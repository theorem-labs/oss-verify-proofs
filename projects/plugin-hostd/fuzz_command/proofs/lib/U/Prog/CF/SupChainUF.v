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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 787 of its 851 lines of code are new or changed and 771 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/sup_pool_config.v, with its module paths, module names, addresses and numbers changed; 558 of its 786 lines of code are new or changed and 623 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0 AllocSlots.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM06 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecAns.
From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecSeq RecStep RecGlue RecAnsB RecTail RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import xmalloc_c record_c arg_s_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require sprintf_c snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SupChainUA sup_chain_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Step.addr_eq_tac ::=
  first [ symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
        | apply wa_of_var; lia ].

Lemma scf_run0 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16e68) (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp t0 t1 t2 a1 a2 (Z_to_bv 64 17)
                     a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 104)
            [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16e1c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 104%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 104%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  carve_frame 24%nat ST.
  clear FR0.
  do 19 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; eassumption.
Qed.

Lemma scf_seg1 :
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (z : Z),
  0 <= z < 2 ^ 32 ->
  evt rsegs (fun ms' => exists b1,
       ms' = MS (mkR (Z_to_bv 64 0x16e80) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 z) (Z_to_bv 64 (12 * z + 1)) b1
                     a2 a3 a4 a5 a6 a7 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15a88) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 z) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16e68) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m z HZ.
  do 6 step.
  match goal with |- context [Z_to_bv 64 (?x - ?y + 1)] =>
    replace (Z_to_bv 64 (x - y + 1)) with (Z_to_bv 64 (12 * z + 1))
      by (f_equal; rewrite (unsigned_lit z) by lia; rewrite !Z.shiftl_mul_pow2 by lia;
          replace (2 ^ 4) with 16 by reflexivity; replace (2 ^ 2) with 4 by reflexivity;
          rewrite !unsigned_lit by lia; lia) end.
  apply evt_done. eexists. reflexivity.
Qed.

Definition scf_mid1 (sp gp tp s0 s1 s2 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo v p : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x16eac) sp gp tp t0 t1 t2 s0 s1 s2 (Z_to_bv 64 (bv_unsigned sp + 8)) a2 a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 p) (Z_to_bv 64 0x10828) (Z_to_bv 64 v) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x161c4) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp + 24)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ length slack = (15 - length (dec v))%nat
    /\ bytes_at rsegs m' (bv_unsigned sp + 8) (dec v ++ Z_to_bv 8 0 :: slack).

Lemma scf_run1 : snprintf_c.snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v p : Z) (canary : word),
  -2^31 <= v < 2^31 ->
  stk rsegs m lo (bv_unsigned sp + 24) -> lo + snprintf_c.SNPRINTF_K <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  bv_unsigned sp + 24 < 2^63 ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> bv_unsigned sp + 24 <= TASK_SIZE ->
  bytes_at rsegs m snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) ->
  bytes_at rsegs m snprintf_c.GUARD (le8 canary) ->
  evt rsegs (scf_mid1 sp gp tp s0 s1 s2 s6 s7 s8 s9 s10 s11 F lo v p m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 v)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16e80) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v p canary HV ST LO IE S63 FRM MI TM HTS GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold snprintf_c.SNPRINTF_K, snprintf_c.IMG_END, snprintf_c.GOT_GUARD, snprintf_c.GUARD in *.
  pose proof (dec_length v HV) as DL.
  pose proof (scu_pf_dec v HV) as PD.
  assert (TL : length (pf_dec v) = length (dec v)) by (rewrite <- PD; unfold pf_bytes; rewrite length_map; reflexivity).
  carve_frame 16%nat ST.
  carve_frame 8%nat ST.
  clear FR0.
  match type of ST with stk _ _ _ ?h => replace h with (bv_unsigned sp) in ST by lia end.
  match type of FR with rw_cells _ _ ?h _ => replace h with (bv_unsigned sp + 8)%Z in FR by lia end.
  do 8 step.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m (bv_unsigned sp + 8)%Z junk).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  assert (JL : length junk = 16%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary SCU_FMT0 SCU_PS0
              [AInt v] (pf_dec v) junk).
    - rewrite unsigned_lit by lia. apply scu_fmt0_at. exact MI.
    - rewrite unsigned_lit by lia. unfold snprintf_c.RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold snprintf_c.RO_END, SCU_FMT0. cbn [length]. lia.
    - reflexivity.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply CF.RecAns.lit_mod32].
    - exact (scu_text0 v).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply CF.RecAns.pf_img_free_hi. lia.
    - exact ST.
    - unfold snprintf_c.SNPRINTF_K. lia.
    - unfold snprintf_c.IMG_END. lia.
    - lia.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GW. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m2
    & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
  rewrite !unsigned_lit in MU2, BT by lia.
  change (Z.to_nat (16 - 1)) with 15%nat in BT, MU2.
  rewrite (firstn_all2 (n := 15%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 0x16ea0)) with (Z_to_bv 64 0x16ea0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (CF.RecAns.bytes_at_firstn_skipn _ _ _ _ (S (length (pf_dec v))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + 8 + Z.of_nat (S (length (pf_dec v))))%Z
                   (skipn (S (length (pf_dec v))) junk)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes (pf_dec v ++ [0%Z]) = dec v ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (pf_dec v)) with (pf_bytes (pf_dec v)).
    rewrite PD. reflexivity. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp + 8)%Z (dec v ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec v))) junk)).
  { replace (dec v ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec v))) junk) with
      ((dec v ++ [Z_to_bv 8 0]) ++ skipn (S (length (pf_dec v))) junk)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, <- TL. cbn [length].
    replace (Z.of_nat (length (pf_dec v) + 1)) with (Z.of_nat (S (length (pf_dec v)))) by lia. exact BJT2. }
  clear BT BJT BJT2 BJ BJL FR.
  do 3 step.
  apply evt_done. unfold scf_mid1.
  do 16 eexists. exists (skipn (S (length (pf_dec v))) junk). split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  split; [eapply wmono_trans; [apply wmono_refl | exact WM2]|].
  split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, TL; lia|].
  exact BUF.
Qed.

Definition scf_mid2 (sp gp tp s0 s2 s3 s6 s7 s8 s9 s10 s11 s5 : word) (F : bvmap 5 word)
    (lo v : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x16ed0) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 v) s2 (Z_to_bv 64 (bv_unsigned sp + 8))
                  a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0x10828) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x161c4) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp + 24)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ length slack = (15 - length (dec v))%nat
    /\ bytes_at rsegs m' (bv_unsigned sp + 8) (dec v ++ Z_to_bv 8 0 :: slack)
    /\ rw_cells rsegs m' (bv_unsigned sp) [C8 s2].

Lemma scf_run2 : snprintf_c.snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v : Z) (canary : word),
  -2^31 <= v < 2^31 ->
  stk rsegs m lo (bv_unsigned sp + 24) -> lo + snprintf_c.SNPRINTF_K <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  bv_unsigned sp + 24 < 2^63 ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> bv_unsigned sp + 24 <= TASK_SIZE ->
  bytes_at rsegs m snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) ->
  bytes_at rsegs m snprintf_c.GUARD (le8 canary) ->
  evt rsegs (scf_mid2 sp gp tp s0 s2 s3 s6 s7 s8 s9 s10 s11 s5 F lo v m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 v) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0x10828) s5
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16eac) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v canary HV ST LO IE S63 FRM MI TM HTS GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold snprintf_c.SNPRINTF_K, snprintf_c.IMG_END, snprintf_c.GOT_GUARD, snprintf_c.GUARD in *.
  pose proof (dec_length v HV) as DL.
  pose proof (scu_pf_dec v HV) as PD.
  assert (TL : length (pf_dec v) = length (dec v)) by (rewrite <- PD; unfold pf_bytes; rewrite length_map; reflexivity).
  carve_frame 16%nat ST.
  carve_frame 8%nat ST.
  match type of ST with stk _ _ _ ?h => replace h with (bv_unsigned sp) in ST by lia end.
  match type of FR with rw_cells _ _ ?h _ => replace h with (bv_unsigned sp + 8)%Z in FR by lia end.
  match type of FR0 with rw_cells _ _ ?h _ => replace h with (bv_unsigned sp) in FR0 by lia end.
  do 5 step.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m (bv_unsigned sp + 8)%Z junk).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  assert (JL : length junk = 16%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary SCU_FMT0 SCU_PS0
              [AInt v] (pf_dec v) junk).
    - rewrite unsigned_lit by lia. apply scu_fmt0_at. exact MI.
    - rewrite unsigned_lit by lia. unfold snprintf_c.RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold snprintf_c.RO_END, SCU_FMT0. cbn [length]. lia.
    - reflexivity.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply CF.RecAns.lit_mod32].
    - exact (scu_text0 v).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply CF.RecAns.pf_img_free_hi. lia.
    - exact ST.
    - unfold snprintf_c.SNPRINTF_K. lia.
    - unfold snprintf_c.IMG_END. lia.
    - lia.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GW. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m2
    & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
  rewrite !unsigned_lit in MU2, BT by lia.
  change (Z.to_nat (16 - 1)) with 15%nat in BT, MU2.
  rewrite (firstn_all2 (n := 15%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 0x16ec0)) with (Z_to_bv 64 0x16ec0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (CF.RecAns.bytes_at_firstn_skipn _ _ _ _ (S (length (pf_dec v))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + 8 + Z.of_nat (S (length (pf_dec v))))%Z
                   (skipn (S (length (pf_dec v))) junk)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes (pf_dec v ++ [0%Z]) = dec v ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (pf_dec v)) with (pf_bytes (pf_dec v)).
    rewrite PD. reflexivity. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp + 8)%Z (dec v ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec v))) junk)).
  { replace (dec v ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec v))) junk) with
      ((dec v ++ [Z_to_bv 8 0]) ++ skipn (S (length (pf_dec v))) junk)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, <- TL. cbn [length].
    replace (Z.of_nat (length (pf_dec v) + 1)) with (Z.of_nat (S (length (pf_dec v)))) by lia. exact BJT2. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp) [CB 8 junk0]).
  { apply (rw_out rsegs _ m m2 _ _ FR0 MU2). intros i Hi. cbn in Hi. split; [lia|]. cbn [outside].
    split; [lia | split; [lia | exact I]]. }
  assert (MU3 : munch [(lo, bv_unsigned sp + 24)] m m2).
  { eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  assert (LS : length (skipn (S (length (pf_dec v))) junk) = (15 - length (dec v))%nat)
    by (rewrite length_skipn, JL, TL; lia).
  clear BT BJT BJT2 BJ BJL FR FR0 MU2 ST2 TM2.
  do 4 step.
  apply evt_done. unfold scf_mid2.
  do 16 eexists. exists (skipn (S (length (pf_dec v))) junk). split; [reflexivity|].
  split; [exact MU3|].
  split; [eapply wmono_trans; [apply wmono_refl | eassumption]|].
  split; [eassumption|]. split; [exact FRM2|]. split; [exact FK|].
  split; [exact LS|].
  split; eassumption.
Qed.

Lemma scf_pw : forall (l : list (Z * Z)) x y, pairwise ranges_disjoint l -> In x l -> In y l -> x <> y ->
  ranges_disjoint x y \/ ranges_disjoint y x.
Proof.
  induction l as [|h t IH]; intros x y HP Hx Hy Hne; [destruct Hx|]. cbn in HP. destruct HP as [H1 H2].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - congruence.
  - left. exact (H1 y Hy).
  - right. exact (H1 x Hx).
  - exact (IH x y H2 Hx Hy Hne).
Qed.

Section Front.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).

Lemma scf_pids : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc lp z pids bs,
  sinvx B API K S L A mem md O Lc Ac mc mdc Rc Oc bc (lp, z) -> 0 < z ->
  ro_agree rsegs mem -> bs <> [] -> bytes_at rsegs mem pids bs ->
  (pids + Z.of_nat (length bs) <= S - K \/ S <= pids) ->
  ((S <= pids /\ pids + Z.of_nat (length bs) <= TASK_SIZE) \/
   (exists q k, In (q, k) (blocks L A) /\ ~ In q (map fst O) /\ q <= pids /\ pids + Z.of_nat (length bs) <= q + k) \/
   (0 <= pids /\ pids + Z.of_nat (length bs) <= 2 ^ 64 /\
    forall i, 0 <= i < Z.of_nat (length bs) -> ro_addr rsegs (Z_to_bv 64 (pids + i)) = true)) ->
  (forall a, pids <= a < pids + Z.of_nat (length bs) -> ~ rec_area a) ->
  bytes_at rsegs mc pids bs /\ (pids + Z.of_nat (length bs) <= lp \/ lp + z <= pids) /\
  pids + Z.of_nat (length bs) <= TASK_SIZE.
Proof using SEGS ERRNO_LOW AX.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc lp z pids bs SI Hz RA0 NE BS HST BH NR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & LIN & LNO & LOC).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & HKS & HK0 & HS63 & HF & HG & HKEEP & _).
  pose proof (bytes_at_bound _ _ _ _ BS) as BB.
  assert (LEN : 0 < Z.of_nat (length bs)) by (destruct bs; [congruence | cbn [length]; lia]).
  destruct (sc_blk B API SEGS AX K S L A mem md O Lc Ac mc mdc Rc Oc bc lp z SI Hz) as (_ & _ & _ & _ & L0 & LC).
  destruct BH as [[HS1 HS2] | [(q & k & HQ & HNQ & Hq1 & Hq2) | (H0 & H1 & HRO)]].
  - split; [|split; [right; lia | exact HS2]].
    apply (bytes_at_transfer rsegs mem mc pids bs BS). intros i Hi.
    assert (FA : free_a B (pids + i)) by (left; unfold TASK_SIZE in *; lia).
    assert (NRA : ~ rec_area (pids + i)) by (apply NR; lia).
    rewrite <- SEGS. exact (proj1 (HF (pids + i) FA ltac:(lia) ltac:(lia) NRA)).
  - assert (QIN : In (q, k) (blocks Lc Ac)).
    { destruct (in_dec pair_dec (q, k) (blocks Lc Ac)) as [IN|NIN]; [exact IN|].
      exfalso. apply HNQ. exact (in_map fst O (q, k) (B2 _ HQ NIN)). }
    assert (NEQ : (q, k) <> (lp, z)).
    { intros Eq. injection Eq as -> ->. apply HNQ. exact (in_map fst O (lp, z) (LNO HQ)). }
    pose proof (block_facts B _ LAWS Lc Ac mc mdc q k 0 HM QIN ltac:(lia)) as (_ & _ & QK & _).
    pose proof HQ as HQ'. unfold blocks in HQ'. apply in_map_iff in HQ' as ([p k'] & Eq & Hp).
    cbn [fst snd] in Eq. injection Eq as Eq1 Eq2. subst k'.
    split; [|split].
    + apply (bytes_at_transfer rsegs mem mc pids bs BS). intros i Hi.
      assert (NO : ~ In (ptr_addr L p, k) O)
        by (intros G; apply HNQ; rewrite <- Eq1; exact (in_map fst O _ G)).
      pose proof (HKEEP p k (pids + i - q) Hp NO) as HK. rewrite Eq1 in HK.
      replace (q + (pids + i - q)) with (pids + i) in HK by ring.
      rewrite <- SEGS. apply HK. lia.
    + destruct (scf_pw _ _ _ (mr_blocks_disjoint B _ LAWS Lc Ac mc mdc HM) QIN LIN NEQ) as [D|D];
        unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
    + unfold TASK_SIZE. lia.
  - assert (TS : pids + Z.of_nat (length bs) <= TASK_SIZE).
    { destruct (Z_lt_le_dec (pids + Z.of_nat (length bs) - 1) (2 ^ 20)) as [Hlt|Hge];
        [unfold TASK_SIZE; lia|].
      exfalso. pose proof (HRO (Z.of_nat (length bs) - 1) ltac:(lia)) as R1.
      rewrite ro_addr_hi in R1 by lia. discriminate. }
    split; [|split; [|exact TS]].
    + apply (bytes_at_transfer rsegs mem mc pids bs BS). intros i Hi.
      pose proof (HRO i Hi) as R.
      pose proof (RA _ R) as E1. pose proof (RA0 _ R) as E2.
      exact (eq_trans E1 (eq_sym E2)).
    + pose proof LIN as LIN'. unfold blocks in LIN'. apply in_map_iff in LIN' as ([q0 z'] & Eq & HQ0).
      cbn [fst snd] in Eq. injection Eq as HLP HZ'. subst z'.
      assert (NI : forall i, 0 <= i < z -> ~ in_img B (lp + i)).
      { intros i Hi. rewrite <- HLP. exact (ax_blocks_img AX Lc Ac mc mdc q0 z i HM HQ0 Hi). }
      destruct (Z_le_gt_dec (pids + Z.of_nat (length bs)) lp) as [G1|G1]; [left; exact G1|].
      destruct (Z_le_gt_dec (lp + z) pids) as [G2|G2]; [right; exact G2|]. exfalso.
      destruct (Z_le_gt_dec pids lp) as [G3|G3].
      * apply (NI 0); [lia|]. replace (lp + 0) with (pids + (lp - pids)) by ring.
        apply (ro_in_img B SEGS); [lia|]. apply HRO. lia.
      * apply (NI (pids - lp)); [lia|]. replace (lp + (pids - lp)) with (pids + 0) by ring.
        apply (ro_in_img B SEGS); [lia|]. apply HRO. lia.
Qed.

Lemma scf_mod8 : forall s0 k, s0 mod 16 = 0 -> 1 <= k <= 11 -> (- (s0 - 128 + 8 + k + 1)) mod 8 <= 15 - k.
Proof. intros s0 k H1 H2. Z.div_mod_to_equations. lia. Qed.

Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis XM : xmalloc_contract B API.
Hypothesis REC : record_contract B API.
Hypothesis SNP : snprintf_c.snprintf_contract.
Hypothesis SPR : sprintf_c.sprintf_contract.
Hypothesis ARGS : forall fx' : YK11.FPState, @arg_s_contract fx' rc B API.

Lemma scu_front : forall L A regs mem md (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z)) b (P : config -> Prop), call_pre_t B API SUP_CHAIN_K L A regs mem md -> getr regs 10 = Z_to_bv 64 id -> -2 ^ 31 <= id < 2 ^ 31 -> getr regs 11 = Z_to_bv 64 pids -> getr regs 12 = Z_to_bv 64 (Z.of_nat (length ids)) -> (1 <= length ids <= 62)%nat -> Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids -> pids <> 0 -> pids mod 4 = 0 -> bytes_at rsegs mem pids (concat (map le32 ids)) -> (pids + 4 * Z.of_nat (length ids) <= spZ regs - SUP_CHAIN_K \/ spZ regs <= pids) -> ((spZ regs <= pids /\ pids + 4 * Z.of_nat (length ids) <= TASK_SIZE) \/ (exists q k, In (q, k) (blocks L A) /\ ~ In q (map fst O) /\ q <= pids /\ pids + 4 * Z.of_nat (length ids) <= q + k) \/ (0 <= pids /\ pids + 4 * Z.of_nat (length ids) <= 2 ^ 64 /\ forall i, 0 <= i < 4 * Z.of_nat (length ids) -> ro_addr rsegs (Z_to_bv 64 (pids + i)) = true)) -> (forall a, pids <= a < pids + 4 * Z.of_nat (length ids) -> ~ rec_area a) -> g_rec_rep rsegs L A mem R O -> ro_agree rsegs mem -> frm_zero fp_csr -> f18_words rsegs mem -> res_ok_slots A b -> room_ag (sb_mallocs b (sup_chain_sizes id ids (snd (sup_chain_m R id ids)))) 745 -> (forall (fx' : YK11.FPState) R' m' mc Lc Ac mdc Oc lp b1, fp_kept fx fx' -> sinvx B API SUP_CHAIN_K (spZ regs) L A mem md O Lc Ac m' mdc (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids))]) Oc b (lp, 12 * Z.of_nat (length ids) + 1) -> bytes_at rsegs m' lp (dec_list ids ++ [Z_to_bv 8 0]) -> bytes_at rsegs m' pids (concat (map le32 ids)) -> munch [(spZ regs - SUP_CHAIN_K, spZ regs - 128); (lp, lp + (12 * Z.of_nat (length ids) + 1))] mc m' -> wmono rsegs mc m' -> ro_agree rsegs m' -> getr R' 2 = Z_to_bv 64 (spZ regs - 128) -> getr R' 3 = getr regs 3 -> getr R' 4 = getr regs 4 -> getr R' 19 = Z_to_bv 64 lp -> st_init_done Ac = true -> sb_le b1 b -> sb_shift b A Ac = sb_malloc (sb_malloc (sb_malloc b1 (12 * Z.of_nat (length ids) + 1)) (Z.of_nat (length (dec id)) + 1)) (Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1) -> rw_cells rsegs m' (spZ regs - 128) [C8 (Z_to_bv 64 (rec_entry G_REC REC_SC R))] -> rw_cells rsegs m' (spZ regs - 104) [C8 (getr regs 27); C8 (getr regs 26); C8 (getr regs 25); C8 (getr regs 24); C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] -> SR rsegs (mkCfg (@mkst fx' R' (Z_to_bv 64 0x16f48) m' (seg_rom rsegs)) mdc) P) -> SR rsegs (mkCfg (mkst regs (Z_to_bv 64 SUP_CHAIN) mem (seg_rom rsegs)) md) P.
Proof using SEGS ERRNO_LOW AX GFACT GOWN GOTG GRD XM REC SNP SPR ARGS.
  intros L A regs mem md id pids ids R O b P PRE GA HID GP GN HN HF HP0 HP4 BS HPS BH NRA GR RA FRM F18 RES ROOM KC.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof ERRNO_LOW as EL.
  pose proof PRE as (PRK & HTS).
  change SUP_CHAIN_K with 12512 in *.
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite SEGS in HWS.
  pose proof (sinv_init B API 12512 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as H16.
  destruct (rec_entry_bounds R H16) as (EB1 & EB2 & EB3).
  pose proof (dec_length id HID) as DL.
  assert (HNZ : 1 <= Z.of_nat (length ids) <= 62) by lia.
  pose proof (dec_length (Z.of_nat (length ids)) ltac:(lia)) as DLN.
  pose proof (bytes_at_bound _ _ _ _ BS) as BSB.
  assert (BL : Z.of_nat (length (concat (map le32 ids))) = 4 * Z.of_nat (length ids)) by (rewrite sc_ids_len; lia).
  set (z := 12 * Z.of_nat (length ids) + 1) in *.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST0 : stk rsegs mem (bv_unsigned sp - 12512) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold SUP_CHAIN.
    eapply scf_run0 with (lo := bv_unsigned sp - 12512); [exact ST0 | lia | lia]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  match type of FR1 with rw_cells _ _ _ ?cs => set (CS := cs) in FR1 end.
  assert (CSZ : Z.of_nat (cells_size CS) = 104) by reflexivity.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16e68) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 128))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_3 : getr R1 3 = getr regs 3) by (rewrite (getr_of_eqv _ _ 3 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 pids) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; exact GP).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 (Z.of_nat (length ids)))
    by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; exact GN).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 17) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_21 : getr R1 21 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 21 X1 eq_refl); simp_regs; exact GA).
  assert (SP1 : spZ R1 = bv_unsigned sp - 128) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12512 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 12512 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 REC_CHAIN _ SI1).
  { rewrite E1_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP1. replace (bv_unsigned sp - 128) with (bv_unsigned sp + (-8) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia. }
  { rewrite SP1. lia. }
  { rewrite E1_4. exact HTP. }
  { exact E1_10. }
  { unfold REC_FN_COUNT, REC_CHAIN. lia. }
  intros L1 A1 regs_r m_r md_r O_r SIr BLEr RPr R10 KSTr.
  rewrite sb_shift_refl in BLEr.
  rewrite E1_1.
  pose proof SIr as (RJr & GRr & ONr & B1r & B2r & RAr & F18r & RESr).
  pose proof RJr as (HMr & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HMr) as (Hhr & Hlr & _).
  assert (Er2 : getr regs_r 2 = Z_to_bv 64 (bv_unsigned sp - 128))
    by exact (eq_trans (RPr 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (Er3 : getr regs_r 3 = getr regs 3) by exact (eq_trans (RPr 3 ltac:(unfold callee_saved; lia)) E1_3).
  assert (Er4 : getr regs_r 4 = getr regs 4) by exact (eq_trans (RPr 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (Er8 : getr regs_r 8 = Z_to_bv 64 pids) by exact (eq_trans (RPr 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (Er9 : getr regs_r 9 = Z_to_bv 64 (Z.of_nat (length ids)))
    by exact (eq_trans (RPr 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (Er21 : getr regs_r 21 = Z_to_bv 64 id) by exact (eq_trans (RPr 21 ltac:(unfold callee_saved; lia)) E1_21).
  assert (FRr : rw_cells rsegs m_r (bv_unsigned sp - 104) CS).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. rewrite CSZ in Hi.
    destruct (KSTr (bv_unsigned sp - 104 + i)) as [Ea Eb]; [rewrite SP1; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  assert (Q9 : reg_get regs_r 9 = Z_to_bv 64 (Z.of_nat (length ids))) by exact Er9.
  eapply evt_SR_canon; [ | exact Hhr | exact Hlr | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q9. eapply scf_seg1. lia. }
  intros ms2 (can2 & (b1x & ->) & EQ2).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x16e80) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 128))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; exact Er2).
  assert (E2_3 : getr R2 3 = getr regs 3) by (rewrite (getr_of_eqv _ _ 3 X2 eq_refl); simp_regs; exact Er3).
  assert (E2_4 : getr R2 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs; exact Er4).
  assert (E2_8 : getr R2 8 = Z_to_bv 64 pids) by (rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; exact Er8).
  assert (E2_9 : getr R2 9 = Z_to_bv 64 (Z.of_nat (length ids)))
    by (rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_10 : getr R2 10 = Z_to_bv 64 z) by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_18 : getr R2 18 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 18 X2 eq_refl); simp_regs; exact R10).
  assert (E2_21 : getr R2 21 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 21 X2 eq_refl); simp_regs; exact Er21).
  assert (SP2 : spZ R2 = bv_unsigned sp - 128) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  apply (sch_xmalloc B API SEGS ERRNO_LOW GFACT GOWN AX GOTG GRD XM 12512 (bv_unsigned sp) L A mem md O L1 A1 m_r md_r
           (rec_record R REC_CHAIN []) O_r b R2 z _ SIr).
  { apply (call_pre_k_of_rjr B _ 12512 (bv_unsigned sp) rec_area _ L A mem md L1 A1 m_r md_r XMALLOC_K R2 RJr).
    - rewrite E2_1. apply bv_eq. vm_compute. reflexivity.
    - rewrite SP2. replace (bv_unsigned sp - 128) with (bv_unsigned sp + (-8) * 16) by ring. rewrite Z.mod_add by lia.
      exact HAL.
    - unfold XMALLOC_K, ALLOC_STACK. lia.
    - rewrite SP2. unfold XMALLOC_K, ALLOC_STACK. lia.
    - rewrite SP2. lia.
    - rewrite E2_4. exact HTP. }
  { rewrite SP2. unfold XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP2. lia. }
  { exact E2_10. }
  { unfold z, LMAX. lia. }
  { refine (room_slots_mono _ _ _ 745 _ _ ROOM); [| unfold z; lia].
    clear - BLEr. unfold sb_mallocs, sup_chain_sizes. cbn [fold_left].
    unfold sb_le, sb_malloc in *. cbn [sb_live sb_bytes sb_cap] in *. lia. }
  intros L2 A2 R3 m3 md3 lp SI3 POST3 E3_10 NZ3 FB3 EQB3.
  rewrite E2_1.
  pose proof SI3 as (RJ3 & GR3 & ON3 & B13 & B23 & RA3 & F183 & RES3 & LIN3 & LNO3 & LOC3).
  pose proof RJ3 as (HM3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC3 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM3) as (Hh3 & Hl3 & _).
  destruct (sc_blk B API SEGS AX 12512 (bv_unsigned sp) L A mem md O L2 A2 m3 md3 (rec_record R REC_CHAIN []) O_r b lp z
              SI3 ltac:(unfold z; lia)) as (_ & _ & _ & _ & LP0 & LPC).
  pose proof POST3 as (PM3 & _ & _ & _ & _ & PR3 & _ & PF3 & _).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 128))
    by exact (eq_trans (PR3 2 ltac:(unfold callee_saved; lia)) E2_2).
  assert (E3_3 : getr R3 3 = getr regs 3) by exact (eq_trans (PR3 3 ltac:(unfold callee_saved; lia)) E2_3).
  assert (E3_4 : getr R3 4 = getr regs 4) by exact (eq_trans (PR3 4 ltac:(unfold callee_saved; lia)) E2_4).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 pids) by exact (eq_trans (PR3 8 ltac:(unfold callee_saved; lia)) E2_8).
  assert (E3_9 : getr R3 9 = Z_to_bv 64 (Z.of_nat (length ids)))
    by exact (eq_trans (PR3 9 ltac:(unfold callee_saved; lia)) E2_9).
  assert (E3_18 : getr R3 18 = Z_to_bv 64 e) by exact (eq_trans (PR3 18 ltac:(unfold callee_saved; lia)) E2_18).
  assert (E3_21 : getr R3 21 = Z_to_bv 64 id) by exact (eq_trans (PR3 21 ltac:(unfold callee_saved; lia)) E2_21).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 104) CS).
  { apply (rw_cells_transfer rsegs m_r); [exact FRr|]. intros i Hi. rewrite CSZ in Hi.
    assert (FA : free_a B (bv_unsigned sp - 104 + i)) by (left; lia).
    assert (NS : ~ scratch_k B XMALLOC_K R2 (bv_unsigned sp - 104 + i))
      by (unfold scratch_k; rewrite SP2; unfold XMALLOC_K, ALLOC_STACK; lia).
    destruct (PF3 (bv_unsigned sp - 104 + i) ltac:(left; lia)
        (free_a_not_owned B _ LAWS AX L1 A1 m_r md_r _ HMr FA) (free_a_not_owned B _ LAWS AX L2 A2 m3 md3 _ PM3 FA)
        NS (fun Hc => Hc)) as [Ea Eb].
    rewrite <- SEGS. split; [exact Ea | exact (proj1 Eb)]. }
  pose proof F183 as (GG3 & canary3 & GW3).
  assert (GGb : bytes_at rsegs m3 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG3 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs m3 snprintf_c.GUARD (Mem.le8 canary3)).
  { destruct GW3 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (STn : stk rsegs (normalize_cj rsegs m3) (bv_unsigned sp - 12512) (bv_unsigned sp - 104)).
  { apply CF.RecAns.stk_normalize_cj; [lia | lia | intros a Ha; rewrite <- SEGS; apply HSC3; left; lia]. }
  pose proof (bytes_at_normalize_cj_low rsegs m3 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA3
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs m3 snprintf_c.GUARD (Mem.le8 canary3) RA3
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  assert (Q2 : reg_get R3 2 = Z_to_bv 64 (bv_unsigned sp - 128)) by exact E3_2.
  assert (Q10 : reg_get R3 10 = Z_to_bv 64 lp) by exact E3_10.
  assert (Q21 : reg_get R3 21 = Z_to_bv 64 id) by exact E3_21.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2, Q10, Q21.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA3 |].
    eapply (scf_run1 SNP) with (lo := bv_unsigned sp - 12512) (canary := canary3).
    - exact HID.
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp - 128 + 24) with (bv_unsigned sp - 104) by ring. exact STn.
    - rewrite unsigned_lit by lia. unfold snprintf_c.SNPRINTF_K. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m3)).
    - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m3)).
    - rewrite unsigned_lit by lia. lia.
    - exact GGn.
    - exact GWn. }
  intros ms4 (can4 & (s4n & Q4' & REL4 & RO4) & EQ4).
  unfold scf_mid1 in Q4'.
  destruct Q4' as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m4n & slack1
    & -> & MU4n & WM4n & MI4n & FRM1 & FK1 & SL1 & BUF4n).
  destruct (CF.RecAns.ms_rel_cj_MS _ _ _ _ _ _ _ _ REL4) as [EC4 MR4r].
  revert EC4 MR4r RO4 EQ4. generalize (ms_mem can4) as m4. intros m4 EC4 MR4r RO4 EQ4. subst can4.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs m3 RA3) MR4r RO4 MU4n) as MU4.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs m3 RA3) MR4r RO4 WM4n) as WM4.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR4r BUF4n) as BUF4.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ4) as (R4 & -> & X4).
  clear MU4n WM4n MI4n BUF4n EQ4 MR4r.
  rewrite unsigned_lit in MU4, BUF4 by lia.
  replace (bv_unsigned sp - 128 + 24) with (bv_unsigned sp - 104) in MU4 by ring.
  assert (E4_1 : getr R4 1 = Z_to_bv 64 0x16eac) by (rewrite (getr_of_eqv _ _ 1 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp - 128))
    by (rewrite (getr_of_eqv _ _ 2 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_3 : getr R4 3 = getr regs 3) by (rewrite (getr_of_eqv _ _ 3 X4 eq_refl); simp_regs; exact E3_3).
  assert (E4_4 : getr R4 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X4 eq_refl); simp_regs; exact E3_4).
  assert (E4_8 : getr R4 8 = Z_to_bv 64 pids) by (rewrite (getr_of_eqv _ _ 8 X4 eq_refl); simp_regs; exact E3_8).
  assert (E4_9 : getr R4 9 = Z_to_bv 64 (Z.of_nat (length ids)))
    by (rewrite (getr_of_eqv _ _ 9 X4 eq_refl); simp_regs; exact E3_9).
  assert (E4_10 : getr R4 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X4 eq_refl); simp_regs; exact E3_18).
  assert (E4_11 : getr R4 11 = Z_to_bv 64 (bv_unsigned sp - 128 + 8))
    by (rewrite (getr_of_eqv _ _ 11 X4 eq_refl); simp_regs; rewrite unsigned_lit by lia; reflexivity).
  assert (E4_18 : getr R4 18 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 18 X4 eq_refl); simp_regs; exact E3_18).
  assert (E4_19 : getr R4 19 = Z_to_bv 64 lp) by (rewrite (getr_of_eqv _ _ 19 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_20 : getr R4 20 = Z_to_bv 64 0x10828) by (rewrite (getr_of_eqv _ _ 20 X4 eq_refl); simp_regs; reflexivity).
  assert (SP4 : spZ R4 = bv_unsigned sp - 128) by (unfold spZ; rewrite E4_2; apply unsigned_lit; lia).
  pose proof (sinvx_heap B API SEGS GOWN AX 12512 (bv_unsigned sp) L A mem md O L2 A2 m3 md3 (rec_record R REC_CHAIN [])
                O_r b lp z m4 _ SI3 MU4 WM4 ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI4.
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 104) CS).
  { apply (rw_out rsegs _ m3 m4 _ _ FR3 MU4). intros i Hi. rewrite CSZ in Hi. split; [lia|]. cbn [outside].
    split; [lia | exact I]. }
  apply (sinvx_arg_sn (fx := mkFP F1 fc1) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS _) 12512 (bv_unsigned sp) L A mem md O
           L2 A2 m4 md3 R REC_CHAIN [] O_r b (lp, z) R4 (bv_unsigned sp - 128 + 8) (Some (dec id)) _ SI4).
  { cbn [length]. lia. }
  { rewrite E4_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP4. replace (bv_unsigned sp - 128) with (bv_unsigned sp + (-8) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP4. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP4. lia. }
  { rewrite E4_4. exact HTP. }
  { exact E4_10. }
  { exact E4_11. }
  { cbn [arg_s_src]. rewrite SP4, SEGS.
    split; [lia|]. split; [apply dec_no0|]. split; [unfold LMAX; lia|].
    exists slack1. split; [exact BUF4|].
    split; [rewrite SL1; pose proof (scf_mod8 (bv_unsigned sp) (Z.of_nat (length (dec id))) HAL ltac:(lia)); lia|].
    split; [right; lia|]. left. split; lia. }
  { cbn [sarg]. rewrite EQB3.
    refine (room_slots_mono _ _ _ 745 _ _ ROOM); [| lia].
    clear - BLEr. unfold sb_mallocs, sup_chain_sizes. cbn [fold_left].
    unfold sb_le, sb_malloc in *. cbn [sb_live sb_bytes sb_cap] in *. lia. }
  intros L5 A5 R5 m5 md5 p5 SI5 EQB5 INIT5 PR5 KST5.
  rewrite E4_1. cbn [app sarg] in SI5, EQB5.
  pose proof SI5 as (RJ5 & _ & _ & _ & _ & RA5 & F185 & _).
  pose proof RJ5 as (HM5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC5 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM5) as (Hh5 & Hl5 & _).
  assert (E5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 128))
    by exact (eq_trans (PR5 2 ltac:(unfold callee_saved; lia)) E4_2).
  assert (E5_3 : getr R5 3 = getr regs 3) by exact (eq_trans (PR5 3 ltac:(unfold callee_saved; lia)) E4_3).
  assert (E5_4 : getr R5 4 = getr regs 4) by exact (eq_trans (PR5 4 ltac:(unfold callee_saved; lia)) E4_4).
  assert (E5_8 : getr R5 8 = Z_to_bv 64 pids) by exact (eq_trans (PR5 8 ltac:(unfold callee_saved; lia)) E4_8).
  assert (E5_9 : getr R5 9 = Z_to_bv 64 (Z.of_nat (length ids)))
    by exact (eq_trans (PR5 9 ltac:(unfold callee_saved; lia)) E4_9).
  assert (E5_18 : getr R5 18 = Z_to_bv 64 e) by exact (eq_trans (PR5 18 ltac:(unfold callee_saved; lia)) E4_18).
  assert (E5_19 : getr R5 19 = Z_to_bv 64 lp) by exact (eq_trans (PR5 19 ltac:(unfold callee_saved; lia)) E4_19).
  assert (E5_20 : getr R5 20 = Z_to_bv 64 0x10828)
    by exact (eq_trans (PR5 20 ltac:(unfold callee_saved; lia)) E4_20).
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 104) CS).
  { apply (rw_cells_transfer rsegs m4); [exact FR4|]. intros i Hi. rewrite CSZ in Hi.
    destruct (KST5 (bv_unsigned sp - 104 + i)) as [Ea Eb]; [rewrite SP4; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  pose proof F185 as (GG5 & canary5 & GW5).
  assert (GGb5 : bytes_at rsegs m5 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG5 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb5 : bytes_at rsegs m5 snprintf_c.GUARD (Mem.le8 canary5)).
  { destruct GW5 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (STn5 : stk rsegs (normalize_cj rsegs m5) (bv_unsigned sp - 12512) (bv_unsigned sp - 104)).
  { apply CF.RecAns.stk_normalize_cj; [lia | lia | intros a Ha; rewrite <- SEGS; apply HSC5; left; lia]. }
  pose proof (bytes_at_normalize_cj_low rsegs m5 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA5
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb5) as GGn5.
  pose proof (bytes_at_normalize_cj_low rsegs m5 snprintf_c.GUARD (Mem.le8 canary5) RA5
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb5) as GWn5.
  assert (Q5_2 : reg_get R5 2 = Z_to_bv 64 (bv_unsigned sp - 128)) by exact E5_2.
  assert (Q5_9 : reg_get R5 9 = Z_to_bv 64 (Z.of_nat (length ids))) by exact E5_9.
  assert (Q5_18 : reg_get R5 18 = Z_to_bv 64 e) by exact E5_18.
  assert (Q5_20 : reg_get R5 20 = Z_to_bv 64 0x10828) by exact E5_20.
  eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of. rewrite Q5_2, Q5_9, Q5_18, Q5_20.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA5 |].
    eapply (scf_run2 SNP) with (lo := bv_unsigned sp - 12512) (canary := canary5).
    - lia.
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp - 128 + 24) with (bv_unsigned sp - 104) by ring. exact STn5.
    - rewrite unsigned_lit by lia. unfold snprintf_c.SNPRINTF_K. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM1.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m5)).
    - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m5)).
    - rewrite unsigned_lit by lia. lia.
    - exact GGn5.
    - exact GWn5. }
  intros ms6 (can6 & (s6n & Q6' & REL6 & RO6) & EQ6).
  unfold scf_mid2 in Q6'.
  destruct Q6' as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & F2 & fc2 & m6n & slack2
    & -> & MU6n & WM6n & MI6n & FRM2 & FK2 & SL2 & BUF6n & FR6n).
  destruct (CF.RecAns.ms_rel_cj_MS _ _ _ _ _ _ _ _ REL6) as [EC6 MR6r].
  revert EC6 MR6r RO6 EQ6. generalize (ms_mem can6) as m6. intros m6 EC6 MR6r RO6 EQ6. subst can6.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs m5 RA5) MR6r RO6 MU6n) as MU6.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs m5 RA5) MR6r RO6 WM6n) as WM6.
  pose proof (CF.RecAns.rw_cells_rel_cj rsegs _ _ _ _ MR6r FR6n) as FR6e.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR6r BUF6n) as BUF6.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ6) as (R6 & -> & X6).
  clear MU6n WM6n MI6n BUF6n FR6n EQ6 MR6r.
  rewrite unsigned_lit in MU6, FR6e, BUF6 by lia.
  replace (bv_unsigned sp - 128 + 24) with (bv_unsigned sp - 104) in MU6 by ring.
  assert (E6_1 : getr R6 1 = Z_to_bv 64 0x16ed0) by (rewrite (getr_of_eqv _ _ 1 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_2 : getr R6 2 = Z_to_bv 64 (bv_unsigned sp - 128))
    by (rewrite (getr_of_eqv _ _ 2 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_3 : getr R6 3 = getr regs 3) by (rewrite (getr_of_eqv _ _ 3 X6 eq_refl); simp_regs; exact E5_3).
  assert (E6_4 : getr R6 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X6 eq_refl); simp_regs; exact E5_4).
  assert (E6_8 : getr R6 8 = Z_to_bv 64 pids) by (rewrite (getr_of_eqv _ _ 8 X6 eq_refl); simp_regs; exact E5_8).
  assert (E6_9 : getr R6 9 = Z_to_bv 64 (Z.of_nat (length ids)))
    by (rewrite (getr_of_eqv _ _ 9 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_10 : getr R6 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_11 : getr R6 11 = Z_to_bv 64 (bv_unsigned sp - 128 + 8))
    by (rewrite (getr_of_eqv _ _ 11 X6 eq_refl); simp_regs; rewrite unsigned_lit by lia; reflexivity).
  assert (E6_19 : getr R6 19 = Z_to_bv 64 lp) by (rewrite (getr_of_eqv _ _ 19 X6 eq_refl); simp_regs; exact E5_19).
  assert (E6_20 : getr R6 20 = Z_to_bv 64 0x10828) by (rewrite (getr_of_eqv _ _ 20 X6 eq_refl); simp_regs; reflexivity).
  assert (SP6 : spZ R6 = bv_unsigned sp - 128) by (unfold spZ; rewrite E6_2; apply unsigned_lit; lia).
  pose proof (sinvx_heap B API SEGS GOWN AX 12512 (bv_unsigned sp) L A mem md O L5 A5 m5 md5
                (rec_record R REC_CHAIN [dec id]) _ b lp z m6 _ SI5 MU6 WM6 ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI6.
  assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp - 104) CS).
  { apply (rw_out rsegs _ m5 m6 _ _ FR5 MU6). intros i Hi. rewrite CSZ in Hi. split; [lia|]. cbn [outside].
    split; [lia | exact I]. }
  apply (sinvx_arg_sn (fx := mkFP F2 fc2) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS _) 12512 (bv_unsigned sp) L A mem md O
           L5 A5 m6 md5 R REC_CHAIN [dec id] _ b (lp, z) R6 (bv_unsigned sp - 128 + 8)
           (Some (dec (Z.of_nat (length ids)))) _ SI6).
  { cbn [length]. lia. }
  { rewrite E6_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP6. replace (bv_unsigned sp - 128) with (bv_unsigned sp + (-8) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP6. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP6. lia. }
  { rewrite E6_4. exact HTP. }
  { exact E6_10. }
  { exact E6_11. }
  { cbn [arg_s_src]. rewrite SP6, SEGS.
    split; [lia|]. split; [apply dec_no0|]. split; [unfold LMAX; lia|].
    exists slack2. split; [exact BUF6|].
    split; [rewrite SL2; pose proof (scf_mod8 (bv_unsigned sp) (Z.of_nat (length (dec (Z.of_nat (length ids)))))
                                       HAL ltac:(lia)); lia|].
    split; [right; lia|]. left. split; lia. }
  { cbn [sarg]. rewrite EQB5, EQB3.
    refine (room_slots_mono _ _ _ 745 _ _ ROOM); [| lia].
    clear - BLEr. unfold sb_mallocs, sup_chain_sizes. cbn [fold_left].
    unfold sb_le, sb_malloc in *. cbn [sb_live sb_bytes sb_cap] in *. lia. }
  intros L7 A7 R7 m7 md7 p7 SI7 EQB7 INIT7 PR7 KST7.
  rewrite E6_1. cbn [app sarg] in SI7, EQB7.
  pose proof SI7 as (RJ7 & _ & _ & _ & _ & RA7 & _).
  pose proof RJ7 as (HM7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC7 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM7) as (Hh7 & Hl7 & _).
  assert (E7_2 : getr R7 2 = Z_to_bv 64 (bv_unsigned sp - 128))
    by exact (eq_trans (PR7 2 ltac:(unfold callee_saved; lia)) E6_2).
  assert (E7_3 : getr R7 3 = getr regs 3) by exact (eq_trans (PR7 3 ltac:(unfold callee_saved; lia)) E6_3).
  assert (E7_4 : getr R7 4 = getr regs 4) by exact (eq_trans (PR7 4 ltac:(unfold callee_saved; lia)) E6_4).
  assert (E7_8 : getr R7 8 = Z_to_bv 64 pids) by exact (eq_trans (PR7 8 ltac:(unfold callee_saved; lia)) E6_8).
  assert (E7_9 : getr R7 9 = Z_to_bv 64 (Z.of_nat (length ids)))
    by exact (eq_trans (PR7 9 ltac:(unfold callee_saved; lia)) E6_9).
  assert (E7_19 : getr R7 19 = Z_to_bv 64 lp) by exact (eq_trans (PR7 19 ltac:(unfold callee_saved; lia)) E6_19).
  assert (E7_20 : getr R7 20 = Z_to_bv 64 0x10828)
    by exact (eq_trans (PR7 20 ltac:(unfold callee_saved; lia)) E6_20).
  assert (SP7 : spZ R7 = bv_unsigned sp - 128) by (unfold spZ; rewrite E7_2; apply unsigned_lit; lia).
  assert (FR7 : rw_cells rsegs m7 (bv_unsigned sp - 104) CS).
  { apply (rw_cells_transfer rsegs m6); [exact FR6|]. intros i Hi. rewrite CSZ in Hi.
    destruct (KST7 (bv_unsigned sp - 104 + i)) as [Ea Eb]; [rewrite SP6; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  assert (FE7 : rw_cells rsegs m7 (bv_unsigned sp - 128) [C8 (Z_to_bv 64 e)]).
  { apply (rw_cells_transfer rsegs m6); [exact FR6e|]. intros i Hi. cbn in Hi.
    destruct (KST7 (bv_unsigned sp - 128 + i)) as [Ea Eb]; [rewrite SP6; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  assert (NE : concat (map le32 ids) <> []).
  { intros E0. apply (f_equal (@length _)) in E0. rewrite sc_ids_len in E0. cbn in E0. lia. }
  destruct (scf_pids 12512 (bv_unsigned sp) L A mem md O L7 A7 m7 md7 _ _ b lp z pids (concat (map le32 ids)) SI7
              ltac:(unfold z; lia) RA NE BS ltac:(rewrite BL; exact HPS) ltac:(rewrite BL; exact BH)
              ltac:(rewrite BL; exact NRA)) as (BP7 & DJ7 & TS7).
  rewrite BL in DJ7, TS7.
  apply (scu_list (fx := mkFP F2 fc2) B API SEGS GOWN AX SPR 12512 (bv_unsigned sp) L A mem md O L7 A7 m7 md7 _ _ b
           lp ids pids R7 P SI7).
  { exact Hh7. }
  { exact Hl7. }
  { exact HN. }
  { exact HF. }
  { lia. }
  { exact HP4. }
  { exact TS7. }
  { rewrite SP7. lia. }
  { unfold z in DJ7. lia. }
  { rewrite SP7. unfold sprintf_c.SPRINTF_K. lia. }
  { rewrite SP7. lia. }
  { rewrite SP7. lia. }
  { intros a Ha. rewrite SP7 in Ha. rewrite <- SEGS. apply HSC7. left. lia. }
  { cbn [fp_csr]. exact FRM2. }
  { exact BP7. }
  { exact E7_8. }
  { exact E7_9. }
  { exact E7_19. }
  { exact E7_20. }
  intros fx' R' m' FK' SI' BX' BP' MU' WM' RA' E2' E3' E4' E19'.
  rewrite SP7 in MU'.
  eapply (KC fx' R' m' m7 L7 A7 md7 _ lp (sb_shift b A A1)).
  - destruct FK' as [FZ' FKr]. split; [exact FZ'|]. intros r Hr.
    assert (NE10 : bv_unsigned (Z_to_bv 5 r) <> 10).
    { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
      unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
    rewrite (FKr r Hr). cbn [fp_regs]. rewrite (FK2 _ NE10). exact (FK1 _ NE10).
  - exact SI'.
  - exact BX'.
  - exact BP'.
  - exact MU'.
  - exact WM'.
  - exact RA'.
  - rewrite E2'. exact E7_2.
  - rewrite E3'. exact E7_3.
  - rewrite E4'. exact E7_4.
  - exact E19'.
  - exact INIT7.
  - exact BLEr.
  - rewrite EQB7, EQB5, EQB3. reflexivity.
  - apply (rw_out rsegs _ m7 m' _ _ FE7 MU'). intros i Hi. cbn in Hi. split; [lia|]. cbn [outside].
    split; [lia | split; [unfold z in LPC; lia | exact I]].
  - apply (rw_out rsegs _ m7 m' _ _ FR7 MU'). intros i Hi. rewrite CSZ in Hi. split; [lia|]. cbn [outside].
    split; [lia | split; [unfold z in LPC; lia | exact I]].
Qed.

End Front.

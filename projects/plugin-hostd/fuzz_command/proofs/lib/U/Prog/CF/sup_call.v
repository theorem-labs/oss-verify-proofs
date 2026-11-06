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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its addresses changed; 872 of its 926 lines of code are new or changed and 781 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecAns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma scu_pf_dec : forall v, (-2^31 <= v < 2^31)%Z -> pf_bytes (pf_dec v) = dec v.
Proof.
  intros c Hc. unfold pf_dec, dec. unfold pf_bytes.
  assert (P : (10 ^ Z.of_nat (S 9) = 10000000000)%Z) by reflexivity.
  destruct (Z.ltb_spec c 0) as [N|N].
  - cbn [map app]. f_equal. replace (Z.abs c) with (- c)%Z by lia.
    exact (pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
  - cbn [app]. replace (Z.abs c) with c by lia.
    exact (pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.

Definition SCU_FMT : list Z := [37%Z; 100%Z].
Definition SCU_PS : list pf_piece := [Pd].

Lemma scu_parse : pf_parse SCU_FMT = Some SCU_PS.
Proof. reflexivity. Qed.

Lemma scu_text : forall v, pf_text SCU_PS [AInt v] = Some (pf_dec v).
Proof. intros v. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma scu_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10828 (pf_bytes (SCU_FMT ++ [0%Z])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma scu_run0 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x165a8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a1 a0
                     (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp + -32)%Z [C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16584) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO IE.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 9 step.
  apply evt_done. eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Definition scu_mid (sp gp tp s0 s1 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo id : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
                    (m' : word -> option byte) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x165d0) sp gp tp t0 t1 t2 s0 s1 a0 sp a2 a3 a4 a5 a6 a7
                  a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (Z_to_bv 64 0x161c4) fc' None m' (seg_rom rsegs) /\
    munch [(lo, bv_unsigned sp + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ frm0 fc' /\
    (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k) /\
    bytes_at rsegs m' (bv_unsigned sp) (dec id ++ Z_to_bv 8 0 :: junk) /\
    length junk = (15 - length (dec id))%nat.

Lemma scu_run1 : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo id : Z) (canary : word) (junk : list byte),
  (-2^31 <= id < 2^31)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> rw_cells rsegs m (bv_unsigned sp) [CB 16%nat junk] ->
  (lo + SNPRINTF_K <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  (bv_unsigned sp + 16 < 2^63)%Z ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (scu_mid sp gp tp s0 (Z_to_bv 64 id) a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo id m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 id) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x165a8) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo id canary junk HV ST FR LO IE S63 FRM MI TM GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (dec_length id HV) as DL.
  pose proof (scu_pf_dec id HV) as PD.
  assert (TL : length (pf_dec id) = length (dec id)) by (rewrite <- PD; unfold pf_bytes; rewrite length_map; reflexivity).
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m (bv_unsigned sp) junk).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  assert (JL : length junk = 16%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  do 7 step.
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary SCU_FMT SCU_PS
              [AInt id] (pf_dec id) junk).
    - rewrite unsigned_lit by lia. apply scu_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, SCU_FMT. cbn [length]. lia.
    - exact scu_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply lit_mod32].
    - exact (scu_text id).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - lia.
    - right. lia.
    - apply pf_img_free_hi. lia.
    - exact ST.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
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
  replace (ret_pc (Z_to_bv 64 0x165c4)) with (Z_to_bv 64 0x165c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (pf_dec id))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + Z.of_nat (S (length (pf_dec id))))%Z
                   (skipn (S (length (pf_dec id))) junk)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes (pf_dec id ++ [0%Z]) = dec id ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (pf_dec id)) with (pf_bytes (pf_dec id)).
    rewrite PD. reflexivity. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp)
                  (dec id ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec id))) junk)).
  { replace (dec id ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec id))) junk) with
      ((dec id ++ [Z_to_bv 8 0]) ++ skipn (S (length (pf_dec id))) junk)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, <- TL. cbn [length].
    replace (Z.of_nat (length (pf_dec id) + 1)) with (Z.of_nat (S (length (pf_dec id)))) by lia. exact BJT2. }
  clear BT BJT BJT2 BJ BJL FR.
  do 3 step.
  apply evt_done. unfold scu_mid.
  do 16 eexists. exists (skipn (S (length (pf_dec id))) junk). split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  split; [exact WM2|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|]. split; [exact BUF|].
  rewrite length_skipn, JL, TL. lia.
Qed.

Lemma scu_run2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x165dc) sp gp tp t0 t1 t2 s0 s1 s2 s0 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x16608) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x165d0) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma scu_run3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x165f0) sp gp tp t0 t1 t2 s0 s1 s2 (Z_to_bv 64 0x10417)
                                      (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x165dc) fc None m (seg_rom rsegs)).
Proof. intros. do 5 step. apply evt_done. reflexivity. Qed.

Lemma scu_run4 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (s2v s1v s0v rav : word),
  rw_cells rsegs m (bv_unsigned sp + 16)%Z [C8 s2v; C8 s1v; C8 s0v; C8 rav] -> (bv_unsigned sp + 48 < 2 ^ 64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5
                                      a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x165f0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    s2v s1v s0v rav FR HB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 6 step. apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecSeq RecStep RecGlue RecTail RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import answer_c record_c arg_s_c arg_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Local Open Scope Z_scope.

Definition scu_kx (xs : list Z) (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> ~ In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma scu_kx_trans : forall xs R1 R2 R3, scu_kx xs R1 R2 -> scu_kx xs R2 R3 -> scu_kx xs R1 R3.
Proof. intros xs R1 R2 R3 H1 H2 r Hr N. rewrite (H2 r Hr N). exact (H1 r Hr N). Qed.

Lemma scu_kx_of_pres : forall xs R R', regs_preserved R R' -> scu_kx xs R R'.
Proof. intros xs R R' H r Hr _. exact (H r Hr). Qed.

Lemma scu_kx_pres : forall xs R R', scu_kx xs R R' ->
  (forall r, In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> regs_preserved R R'.
Proof.
  intros xs R R' K E r Hr. destruct (in_dec Z.eq_dec r xs) as [H|H]; [exact (E r H) | exact (K r Hr H)].
Qed.

Ltac scu_one X :=
  first [ exfalso; match goal with N : ~ In _ _ |- _ => apply N end; cbn [In]; lia
        | match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
          simp_regs; first [reflexivity | unfold getr; reflexivity] ].

Ltac scu_tac X :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Nrr := fresh "Nrr" in
  intros rr Hrr Nrr; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; scu_one X|]);
  subst rr; scu_one X.

Lemma scu_nra_apart : forall s Ln lo hi, (forall a, s <= a < s + Ln -> ~ rec_area a) ->
  REC_SC <= lo -> hi <= G_REC + REC_SIZE -> lo < hi -> 0 < Ln -> s + Ln <= lo \/ hi <= s.
Proof.
  intros s Ln lo hi H H1 H2 H3 H4. destruct (Z_le_gt_dec (s + Ln) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi s) as [D'|D']; [right; exact D'|]. exfalso.
  unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in *.
  destruct (Z_le_gt_dec s lo) as [D1|D1].
  - apply (H lo); [lia|]. destruct (Z_lt_ge_dec lo 213032); [left | right]; lia.
  - apply (H s); [lia|]. destruct (Z_lt_ge_dec s 213032); [left | right]; lia.
Qed.

Lemma scu_shape : forall m, ro_agree rsegs m -> CF.answer_c.ans_shape rsegs m 0x10417 REC_MOD_HOST_SHAPE.
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

Lemma scu_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma scu_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length x) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - pose proof (inst_length x). lia.
  - rewrite scu_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Lemma scu_fp_trans : forall fx0 fx1 fx2 : YK11.FPState, fp_kept fx0 fx1 -> fp_kept fx1 fx2 -> fp_kept fx0 fx2.
Proof.
  intros fx0 fx1 fx2 [_ H1] [Z2 H2]. split; [exact Z2|]. intros r Hr. rewrite (H2 r Hr). exact (H1 r Hr).
Qed.

Lemma scu_fp_snp : forall (fx0 : YK11.FPState) (Ft : bvmap 5 word) (fc' : bv 32), frm0 fc' ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get (@fp_regs fx0) k) -> fp_kept fx0 (mkFP Ft fc').
Proof.
  intros fx0 Ft fc' Z H. split; [exact Z|]. intros r Hr.
  change (reg_get Ft (Z_to_bv 5 r) = reg_get (@fp_regs fx0) (Z_to_bv 5 r)). apply H.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. unfold fs_saved in Hr.
  rewrite Z.mod_small by lia. lia.
Qed.

Section Ans.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ANS : answer_contract B API.
Hypothesis SLACK : block_slack_present B API.

Lemma scu_ans : forall K S L A mem md (O : list (Z * Z)) L1 A1 regs1 mem1 md1 (R1 : rstate)
    (O1 : list (Z * Z)) b bpre b1 c sh e x chg (P : config -> Prop),
  aa_MR API L A mem md ->
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1 ->
  YK0s.ret_ok (getr regs1 1) -> spZ regs1 mod 16 = 0 -> S - K <= spZ regs1 - ANSWER_K -> spZ regs1 <= S ->
  spZ regs1 <= TASK_SIZE -> getr regs1 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs1 10 = Z_to_bv 64 c -> getr regs1 11 = Z_to_bv 64 sh -> chg = negb (bv_unsigned (getr regs1 12) =? 0) ->
  g_rec_rep rsegs L1 A1 mem1 R1 O1 ->
  (r_refuse R1 = 0 -> ans_shape rsegs mem1 sh x) ->
  (r_refuse R1 = 0 -> chg = true -> ans_entry R1 c e) ->
  frm_zero fp_csr -> f18_words rsegs mem1 -> ro_agree rsegs mem1 ->
  res_ok_slots A1 b1 -> b1 = sb_shift b A A1 -> sb_le b1 bpre ->
  room_ag (sb_malloc (sb_malloc b1 (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1))
                (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1))
             (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1) ->
  owns_new L A O O1 ->
  (forall pn, In pn (blocks L1 A1) -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O1) ->
  (forall pn, In pn (blocks L A) -> ~ In pn (blocks L1 A1) -> In pn O) ->
  (forall (fx' : YK11.FPState) L' A' regs' mem' md' O' q,
     fp_kept fx fx' ->
     rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' mem' md' ->
     regs_preserved regs1 regs' ->
     getr regs' 10 = Z_to_bv 64 q ->
     g_rec_rep rsegs L' A' mem' (fst (rec_answer R1 e x chg)) O' -> owns_new L A O O' ->
     (forall pn, In pn (blocks L' A') ->
        (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/
        pn = (q, Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1)) ->
     In (q, Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1) (blocks L' A') ->
     fresh_block B q (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1) ->
     ~ In q (map fst O') ->
     bytes_at rsegs mem' q (snd (rec_answer R1 e x chg) ++ [Z_to_bv 8 0]) ->
     (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
        ptr_addr L p + k <= q \/ q + Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1 <= ptr_addr L p) ->
     ro_agree rsegs mem' -> f18_words rsegs mem' -> st_init_done A' = true ->
     sb_le (sb_shift b A A') (sb_malloc (sb_malloc bpre (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1))
                                (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1)) ->
     res_ok_slots A' (sb_shift b A A') ->
     (forall a, spZ regs1 <= a < S ->
        mbyte rsegs mem' a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem' a)) ->
     SR rsegs (mkCfg (@mkst fx' regs' (getr regs1 1) mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 ANSWER) mem1 (seg_rom rsegs)) md1) P.
Proof using SEGS ERRNO_LOW AX ANS SLACK.
  intros K S L A mem md O L1 A1 regs1 mem1 md1 R1 O1 b bpre b1 c sh e x chg P
    HM R HRA HAL HLO HHI HTS HTP A10 A11 ACH GREP1 SHAPE ENTRY FRM F18 RO1 RES1 EB1 BLE ROOM1 P1 P2 P5 KONT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  assert (AK0 : 0 <= ANSWER_K) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof R as R0.
  destruct R0 as (HM1 & HWA & HW1 & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  assert (PRE1 : call_pre_t B API ANSWER_K L1 A1 regs1 mem1 md1).
  { split; [|exact HTS].
    apply (call_pre_k_of_rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1 ANSWER_K regs1
             R HRA HAL); [exact AK0 | exact HLO | exact HHI | exact HTP]. }
  pose proof (ANS L1 A1 regs1 mem1 md1 R1 O1 c sh e x chg b1 PRE1 A10 A11 ACH) as AN.
  rewrite SEGS in AN.
  eapply SR_bind.
  { apply AN; [exact GREP1 | exact SHAPE | | exact FRM | exact F18 | exact RES1 | exact ROOM1 | exact RO1].
    intros Hr Hc. split; [exact (ENTRY Hr Hc)|]. intros q k a Hq Ha. exact (SLACK L1 A1 mem1 md1 q k a HM1 Hq Ha). }
  intros c' RET. unfold answer_ret in RET.
  destruct RET as (fx' & L' & A' & regs' & mem' & md' & p1 & p2 & old & O' & EC & FPK & OLDB & POST & A0 & NE12 & AL1 & AL2
    & FR1 & FR2 & (c1 & c2 & HB & HIFF & NI1 & NI2) & BK & UBK & GREP' & HO' & HO2 & HBC & BY1 & BY2 & RA' & F18' & GK
    & INIT & REG & GR' & RES').
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  set (n := Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1) in *.
  assert (HB' : exists kold, (old = 0 /\ blocks L1 A1 = c1 ++ c2) \/
                             (old <> 0 /\ In (old, kold) O1 /\ blocks L1 A1 = c1 ++ (old, kold) :: c2)).
  { destruct HB as [H|(k & H)]; [exists 0; left; exact H | exists k; right; exact H]. }
  destruct HB' as [kold HB'].
  assert (STAB : forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
            In (p, k) (user_blocks A1) /\ ptr_addr L1 p = ptr_addr L p).
  { intros p k Hu Hno.
    split; [exact (rjr_in_cur B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1 p k R Hu Hno)|].
    exact (ptr_addr_stable A L L1 p k HWA Hu HL). }
  assert (R2 : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' mem' md').
  { apply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW K S rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1
             ANSWER_K regs1 ans_writes (fun a => a = old) L' A' regs' mem' md' R POST).
    - exact HLO.
    - exact HHI.
    - intros a Ha _.
      unfold ans_writes, rec_area, G_REC, REC_SC, OFF_ANSWER, OFF_STATE, SC_SIZE, REC_SIZE in *.
      split; [lia|]. lia.
    - intros p k Hu Hno Hk E.
      destruct (STAB p k Hu Hno) as [Hu1 Ep].
      pose proof (mr_blocks_range B (aa_MR API) LAWS L A mem md p k HM Hu) as Hr.
      destruct HB' as [(E0 & _)|(NZ & Ho & EB)]; [lia|].
      assert (Hob : In (old, kold) (blocks L1 A1)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
      pose proof (user_in_blocks L1 A1 p k Hu1) as Hb. rewrite Ep, E in Hb.
      pose proof (rec_rep_pos rsegs G_REC REC_SC L1 A1 mem1 R1 O1 (old, kold) GREP1 Ho) as Hk0. cbn [snd] in Hk0.
      assert (Ek : k = kold) by exact (blocks_same_addr B (aa_MR API) LAWS L1 A1 mem1 md1 old k kold HM1 Hb Hob Hk Hk0).
      subst k. rewrite E in Hno.
      destruct (P1 _ Ho) as [H|H]; [exact (Hno H)|]. apply H. rewrite <- E. exact (user_in_blocks L A p kold Hu).
    - intros p k Hu Hu1 Hu'.
      destruct (in_dec pair_dec (ptr_addr L p, k) O) as [H|H]; [exact H|]. exfalso. apply Hu'. apply UBK; [exact Hu1|].
      rewrite (ptr_addr_stable A L L1 p k HWA Hu HL). intros Ho.
      destruct (P1 _ Ho) as [H'|H']; [exact (H H') | exact (H' (user_in_blocks L A p k Hu))].
    - exact REG.
    - rewrite INIT. discriminate. }
  assert (FK : forall a, spZ regs1 <= a < S ->
            mbyte rsegs mem' a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem' a)).
  { intros a Ha. rewrite SEGS in PF. apply PF.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L1 A1 mem1 md1 a HM1 Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L' A' mem' md' a PM Ho). lia.
    - unfold scratch_k. intros [H|H]; lia.
    - intros Hr. unfold ans_writes, G_REC, OFF_ANSWER, OFF_STATE in Hr. lia. }
  pose proof (rjr_others_kept B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' mem' md' O R2
                (fun pn H => H)) as OK.
  destruct (tail_owns_blocks (blocks L A) (blocks L1 A1) (blocks L' A') O O1 O' c1 c2 old kold p1 p2 n
              P1 P2 P5 HB' NI1 HO' HBC) as [OWN BLK].
  assert (Hq : In (p2, n) (blocks L' A')) by (apply HIFF; right; right; reflexivity).
  rewrite EC, SEGS.
  rewrite SEGS in GREP', BY2, RA', F18'.
  apply (KONT fx' L' A' regs' mem' md' O' p2 FPK R2 PR A0 GREP' OWN BLK Hq FR2).
  - intros Hin; apply in_map_iff in Hin as (pn & Epn & Hpn); exact (HO2 pn Hpn Epn).
  - exact BY2.
  - intros p0 k0 Hu0 Hno0.
    enough (D : ptr_addr L p0 + k0 <= p2 \/ p2 + n <= ptr_addr L p0) by (unfold n in D; lia).
    revert p0 k0 Hu0 Hno0.
    apply (q_apart_tail B (aa_MR API) LAWS (ms_segs B) L A mem L' A' mem' md' O p2 n PM OK Hq).
    intros p k Hu Hno. destruct (STAB p k Hu Hno) as [Hu1 Ep].
    apply (tail_q_distinct (blocks L A) (blocks L1 A1) O O1 c1 c2 old kold p2 n (ptr_addr L p, k) P1 HB' NI2).
    + exact (user_in_blocks L A p k Hu).
    + exact Hno.
    + rewrite <- Ep. exact (user_in_blocks L1 A1 p k Hu1).
  - exact RA'.
  - exact F18'.
  - exact INIT.
  - rewrite <- (sb_shift_trans b A A1 A'), <- EB1.
    eapply sb_le_trans; [exact GR' | apply sb_malloc_mono; apply sb_malloc_mono; exact BLE].
  - rewrite <- (sb_shift_trans b A A1 A'), <- EB1. exact RES'.
  - exact FK.
Qed.

End Ans.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis SNP : snprintf_contract.
Hypothesis REC : record_contract B API.
Hypothesis ARGS : forall fx0 : YK11.FPState, arg_s_contract (fx := fx0) B API.
Hypothesis ARGL : forall fx0 : YK11.FPState, arg_line_contract (fx := fx0) B API.
Hypothesis ANS : forall fx0 : YK11.FPState, answer_contract (fx := fx0) B API.

Lemma scu_home_lower : forall L A sp1 sp2 s n, sp2 <= sp1 -> str_home B L A sp1 s n -> str_home B L A sp2 s n.
Proof.
  intros L A sp1 sp2 s n H [H1|[H1|H1]]; [left; lia | right; left; exact H1 | right; right; exact H1].
Qed.

Lemma scu_str : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc p x,
  sinv B API K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  ro_agree rsegs mem ->
  str_arg B L A O S K mem p (Some x) ->
  exists slack, 0 <= p < 2 ^ 64 /\ p <> 0 /\
    bytes_at rsegs mc p (x ++ Z_to_bv 8 0 :: slack) /\ no0 x /\ Z.of_nat (length x) <= LMAX /\
    (- (p + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\
    (p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) <= S - K \/ S <= p) /\
    str_home B Lc Ac S p (Z.of_nat (length x) + 1) /\
    (forall a, p <= a < p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) -> ~ rec_area a).
Proof using SEGS ERRNO_LOW SLACK.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc p x SI RA H.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _ & _ & _ & B2 & RAc & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct H as (Hp0 & N0 & LX & slack & BS & AL & DJ & HOME & NRA).
  rewrite SEGS in BS.
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _ & HK & _).
  rewrite SEGS in HF, HK.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  rewrite length_app in DJ, NRA. cbn [length] in DJ, NRA.
  set (pad := (- (p + Z.of_nat (length x) + 1)) mod 8) in *.
  assert (PADR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (PADA : (p + Z.of_nat (length x) + 1 + pad) mod 8 = 0).
  { unfold pad. rewrite Zplus_mod_idemp_r. replace (p + Z.of_nat (length x) + 1 + - (p + Z.of_nat (length x) + 1)) with 0
      by ring. reflexivity. }
  assert (PR0 : forall j, 0 <= j < pad -> mbyte rsegs mem (p + Z.of_nat (length x) + 1 + j) <> None).
  { intros j Hj E. pose proof BS as (_ & _ & HB).
    assert (Hlt : (Z.to_nat (Z.of_nat (length x) + 1 + j) < length (x ++ Z_to_bv 8 0 :: slack))%nat)
      by (rewrite length_app; cbn [length]; lia).
    specialize (HB (Z.to_nat (Z.of_nat (length x) + 1 + j)) Hlt).
    change (mrd rsegs mem (wa (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))))
      with (mbyte rsegs mem (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))) in HB.
    rewrite Z2Nat.id in HB by lia.
    replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) in HB by ring.
    rewrite E in HB. symmetry in HB. apply nth_error_None in HB. lia. }
  assert (TX0 : bytes_at rsegs mem p (x ++ [Z_to_bv 8 0])).
  { replace (x ++ Z_to_bv 8 0 :: slack) with ((x ++ [Z_to_bv 8 0]) ++ slack) in BS
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS. exact (proj1 BS). }
  assert (LX1 : Z.of_nat (length (x ++ [Z_to_bv 8 0])) = Z.of_nat (length x) + 1)
    by (rewrite length_app; cbn [length]; lia).
  assert (SAME : (forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)) ->
                 bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                 (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None)).
  { intros KE. split.
    - apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi. apply KE. lia.
    - intros j Hj. replace (p + Z.of_nat (length x) + 1 + j) with (p + (Z.of_nat (length x) + 1 + j)) by ring.
      rewrite KE by lia. replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) by ring.
      exact (PR0 j Hj). }
  assert (CASES : bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                  (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None) /\
                  str_home B Lc Ac S p (Z.of_nat (length x) + 1)).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
    - assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi. refine (proj1 (HF (p + i) _ _ _ _)).
        - unfold free_a. left. lia.
        - lia.
        - lia.
        - intros Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Hr. lia. }
      destruct (SAME KE) as [S1 S2]. split; [exact S1 | split; [exact S2 | left; lia]].
    - assert (NG : ~ In (q, k) O).
      { intros Ho. apply Hnq. apply in_map_iff. exists (q, k). split; [reflexivity | exact Ho]. }
      assert (QC : In (q, k) (blocks Lc Ac)).
      { destruct (in_dec pair_dec (q, k) (blocks Lc Ac)) as [Hc|Hc]; [exact Hc|]. exfalso. exact (NG (B2 _ Hq Hc)). }
      pose proof Hq as Hq'. unfold blocks in Hq'. apply in_map_iff in Hq' as ([pp k'] & E & Hp). cbn [fst snd] in E.
      injection E as E1 E2. subst k'.
      split.
      { apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi.
        assert (Hng : ~ (fun pn => In pn O) (ptr_addr L pp, k)) by (intros Hg; apply NG; rewrite <- E1; exact Hg).
        pose proof (HK pp k (p + i - q) Hp Hng ltac:(lia)) as E. rewrite E1 in E.
        replace (q + (p + i - q)) with (p + i) in E by ring. exact E. }
      split.
      { intros j Hj.
        assert (PRc : present mc (p + Z.of_nat (length x) + 1 + j)).
        { destruct (Z_lt_ge_dec (p + Z.of_nat (length x) + 1 + j) (q + k)) as [Hlt|Hge].
          - replace (p + Z.of_nat (length x) + 1 + j) with (q + (p + Z.of_nat (length x) + 1 + j - q)) by ring.
            exact (proj1 (block_facts B _ LAWS Lc Ac mc mdc q k (p + Z.of_nat (length x) + 1 + j - q) HM QC ltac:(lia))).
          - apply (SLACK Lc Ac mc mdc q k _ HM QC). split; [lia|]. Z.div_mod_to_equations. lia. }
        destruct PRc as [bb E]. unfold mbyte. rewrite E. discriminate. }
      right. left. exists q, k. split; [exact QC | lia].
    - pose proof H3 as H3'. rewrite SEGS in H3'.
      assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi.
        assert (RO : ro_addr rsegs (Z_to_bv 64 (p + i)) = true).
        { destruct (Z_lt_ge_dec i (Z.of_nat (length x) + 1)) as [Hl|Hl]; [exact (H3' i ltac:(lia))|].
          pose proof (H3' (Z.of_nat (length x)) ltac:(lia)) as Hlast. apply rs_ro_rsegs in Hlast; [|lia].
          apply rs_ro_rsegs; [lia|]. Z.div_mod_to_equations. lia. }
        rewrite (mbyte_ro_agree _ _ _ RAc RO), (mbyte_ro_agree _ _ _ RA RO). reflexivity. }
      destruct (SAME KE) as [S1 S2].
      split; [exact S1 | split; [exact S2 | right; right; split; [exact H1 | split; [exact H2 | exact H3]]]]. }
  destruct CASES as (TX & PADP & HOMEc).
  destruct (rs_bytes_pad rsegs mc p (x ++ [Z_to_bv 8 0]) (Z.to_nat pad) TX) as (sl & SL & BS').
  { rewrite LX1, Z2Nat.id by lia. lia. }
  { intros j Hj. rewrite LX1. replace (p + (Z.of_nat (length x) + 1) + Z.of_nat j)
      with (p + Z.of_nat (length x) + 1 + Z.of_nat j) by ring. apply PADP. lia. }
  rewrite <- app_assoc in BS'. cbn [app] in BS'.
  exists sl.
  split; [lia|]. split; [exact Hp0|].
  split; [exact BS'|]. split; [exact N0|]. split; [exact LX|].
  split; [change ((- (p + Z.of_nat (length x) + 1)) mod 8) with pad; rewrite SL, Z2Nat.id by lia; lia|].
  split; [rewrite length_app; cbn [length]; rewrite SL; destruct DJ as [D|D]; [left; lia | right; exact D]|].
  split; [exact HOMEc|].
  intros a Ha. apply NRA. rewrite length_app in Ha. cbn [length] in Ha. rewrite SL in Ha. lia.
Qed.

Theorem sup_call_holds : sup_call_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK SNP REC ARGS ARGL ANS.
  unfold sup_call_contract.
  intros L A regs mem md id pl line R O b PRE H10 HID H11 SA GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_CALL_K in PRE, PRK, HCEIL, HWS, SA.
  unfold SUP_CALL.
  rewrite SEGS in GR, RA, F18, HWS |- *.
  assert (RKL : RECORD_K = 8336) by reflexivity.
  assert (ASK : ARG_S_K = 8256) by reflexivity.
  assert (AKL : ARG_LINE_K = 8272) by reflexivity.
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof (sinv_init B API 12432 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as HN.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & _ & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  change (snd (sup_call_m R id line)) with
    (snd (rec_answer (rec_record R REC_CALL [dec id; canon line]) (REC_CALL, [dec id; canon line])
       REC_MOD_HOST_SHAPE true)) in ROOM.
  unfold sup_call_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_CALL [dec id; canon line]) (REC_CALL, [dec id; canon line])
                  REC_MOD_HOST_SHAPE true)) <= 16)%nat).
  { pose proof (scu_len R REC_CALL [dec id; canon line] REC_MOD_HOST_SHAPE true HCODE) as H.
    assert (LX6 : length REC_MOD_HOST_SHAPE = 6%nat) by (vm_compute; reflexivity).
    rewrite LX6 in H. exact H. }
  pose proof (rec_entry_bounds R HN) as ER.
  pose proof (dec_length id HID) as DL.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (U48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (ST : stk rsegs mem (bv_unsigned sp - 12432) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    eapply scu_run0; [exact ST | lia | lia]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x165a8) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 pl) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; exact H11).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; exact H10).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 REC_CALL)
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (K01 : scu_kx [2; 8; 9; 18] regs R1) by scu_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2, U48; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12432 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  change (Z_to_bv 64 0x1612c) with (Z_to_bv 64 RECORD).
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 12432 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 REC_CALL);
    [ exact SI1
    | rewrite E1_1; apply bv_eq; vm_compute; reflexivity
    | rewrite SP1; replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring;
      rewrite Z.mod_add by lia; exact HAL
    | rewrite SP1, RKL; lia
    | rewrite SP1; lia
    | rewrite E1_4; exact HTP
    | exact E1_10
    | unfold REC_CALL, REC_FN_COUNT; lia
    | ].
  intros L1 A1 regs1 m2 md1 O1 SI2 BLE2 RP1 R10 FK1.
  rewrite E1_1.
  rewrite sb_shift_refl in BLE2.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (FK1 (bv_unsigned sp + -32 + i)) as [E W]; [rewrite SP1; lia|]. split; [exact E | apply W]. }
  pose proof SI2 as (RJ2 & GR2 & ON2 & B12 & B22 & RA2 & F182 & RS2).
  pose proof RJ2 as (PM2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC2 & _).
  rewrite SEGS in HSC2.
  destruct (mr_model B _ LAWS L1 A1 m2 md1 PM2) as (Hh2 & Hl2 & _).
  assert (Q1_2 : reg_get regs1 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by exact (eq_trans (RP1 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (Q1_9 : reg_get regs1 9 = Z_to_bv 64 id)
    by exact (eq_trans (RP1 9 ltac:(unfold callee_saved; lia)) E1_9).
  pose proof F182 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs m2 snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs m2 snprintf_c.GUARD (le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_normalize_cj_low rsegs m2 snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) RA2
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs m2 snprintf_c.GUARD (le8 canary) RA2
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  assert (ST2 : stk rsegs (normalize_cj rsegs m2) (bv_unsigned sp - 12432) (bv_unsigned sp + -32)).
  { apply stk_normalize_cj; [lia | lia | intros a Ha; apply HSC2; left; lia]. }
  destruct (stk_carve rsegs _ _ _ 16%nat ST2 ltac:(lia)) as [ST3 [junk FRB]].
  replace (bv_unsigned sp + -32 - Z.of_nat 16) with (bv_unsigned sp + -48) in ST3, FRB by lia.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q1_2, Q1_9.
    eapply (evt_normalize_cj rsegs); [exact wx_apart_rsegs | exact RA2 |].
    eapply (scu_run1 SNP) with (lo := bv_unsigned sp - 12432) (canary := canary) (junk := junk);
      [ exact HID | rewrite U48; exact ST3 | rewrite U48; exact FRB | rewrite U48; unfold SNPRINTF_K; lia | lia
      | rewrite U48; lia | exact FRM | exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m2))
      | exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m2)) | exact GGn | exact GWn ]. }
  intros ms2 (can2 & (s2n & Q2 & REL2 & RO2) & EQ2).
  unfold scu_mid in Q2.
  destruct Q2 as (u0 & u1 & u2 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m3n & junk'
    & -> & MU3n & WM3n & MI3n & FRM3 & FKF & BUF3n & JL3).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL2) as [EC2 MR2r].
  revert EC2 MR2r RO2 EQ2. generalize (ms_mem can2) as m3. intros m3 EC2 MR2r RO2 EQ2. subst can2.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs m2 RA2) MR2r RO2 MU3n) as MU3.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs m2 RA2) MR2r RO2 WM3n) as WM3.
  pose proof (ro_agree_same_cj rsegs _ _ RA2 RO2) as RA3.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR2r BUF3n) as BUF3.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ2) as (R2 & -> & X2).
  clear MU3n WM3n MI3n BUF3n EQ2 MR2r.
  rewrite U48 in MU3, BUF3.
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x165d0) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_4 : getr R2 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs. exact (eq_trans (RP1 4 ltac:(unfold callee_saved; lia)) E1_4). }
  assert (E2_8 : getr R2 8 = Z_to_bv 64 pl).
  { rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs. exact (eq_trans (RP1 8 ltac:(unfold callee_saved; lia)) E1_8). }
  assert (E2_10 : getr R2 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; exact R10).
  assert (E2_11 : getr R2 11 = Z_to_bv 64 (bv_unsigned sp + -48))
    by (rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_18 : getr R2 18 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 18 X2 eq_refl); simp_regs; exact R10).
  assert (K12 : scu_kx [2; 8; 9; 18] R1 regs1) by exact (scu_kx_of_pres _ _ _ RP1).
  assert (K23 : scu_kx [2; 8; 9; 18] regs1 R2) by scu_tac X2.
  assert (SP2 : spZ R2 = bv_unsigned sp - 48) by (unfold spZ; rewrite E2_2, U48; lia).
  assert (FPK1 : fp_kept fx (mkFP Ft fc')) by exact (scu_fp_snp fx Ft fc' FRM3 FKF).
  pose proof (sinv_stack B API SEGS GOWN AX 12432 (bv_unsigned sp) L A mem md O L1 A1 m2 md1 _ O1 b m3 _ SI2 MU3 WM3
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI3.
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_out rsegs _ m2 m3 _ _ FR2 MU3). intros i Hi. cbn in Hi |- *. split; [lia|]. split; [lia | exact I]. }
  change (Z_to_bv 64 0x161c4) with (Z_to_bv 64 ARG_S).
  apply (sinv_arg_s (fx := mkFP Ft fc') B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS (mkFP Ft fc')) 12432 (bv_unsigned sp)
           L A mem md O L1 A1 m3 md1 R REC_CALL O1 b R2 (bv_unsigned sp + -48) (Some (dec id)));
    [ exact SI3
    | rewrite E2_1; apply bv_eq; vm_compute; reflexivity
    | rewrite SP2; replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring;
      rewrite Z.mod_add by lia; exact HAL
    | rewrite SP2, ASK; lia
    | rewrite SP2; lia
    | rewrite E2_4; exact HTP
    | exact E2_10
    | exact E2_11
    |
    |
    | ].
  { cbn [arg_s_src]. rewrite SEGS.
    split; [lia|]. split; [exact (dec_no0 id)|]. split; [unfold LMAX; lia|].
    exists junk'. split; [exact BUF3|].
    split; [rewrite JL3; clear -HAL DL; Z.div_mod_to_equations; lia|].
    split; [right; rewrite SP2; lia|].
    left. rewrite SP2. lia. }
  { cbn [sarg]. eapply room_slots_mono; [| | exact ROOM].
    - eapply sb_le_trans; [apply sb_malloc_mono; exact BLE2|].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      eapply sb_le_trans; [|apply sb_le_malloc; lia].
      apply sb_le_malloc; lia.
    - unfold LMAX. lia. }
  intros L3 A3 regs3 m4 md3 p1 SI4 SBEQ INI3 RP3 FK3.
  change (sarg (Some (dec id))) with (dec id) in SI4, SBEQ.
  rewrite E2_1.
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (FK3 (bv_unsigned sp + -32 + i)) as [E W]; [rewrite SP2; lia|]. split; [exact E | apply W]. }
  assert (R3_2 : getr regs3 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) E2_2).
  assert (R3_4 : getr regs3 4 = getr regs 4) by exact (eq_trans (RP3 4 ltac:(unfold callee_saved; lia)) E2_4).
  assert (R3_8 : getr regs3 8 = Z_to_bv 64 pl) by exact (eq_trans (RP3 8 ltac:(unfold callee_saved; lia)) E2_8).
  assert (R3_18 : getr regs3 18 = Z_to_bv 64 e) by exact (eq_trans (RP3 18 ltac:(unfold callee_saved; lia)) E2_18).
  assert (K34 : scu_kx [2; 8; 9; 18] R2 regs3) by exact (scu_kx_of_pres _ _ _ RP3).
  pose proof SI4 as (RJ4 & GR4 & ON4 & B14 & B24 & RA4 & F184 & RS4).
  pose proof RJ4 as (PM4 & _).
  destruct (mr_model B _ LAWS L3 A3 m4 md3 PM4) as (Hh4 & Hl4 & _).
  eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of. apply scu_run2. }
  intros ms5 (can5 & -> & EQ5).
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ5) as (R4 & -> & X4).
  assert (E4_1 : getr R4 1 = Z_to_bv 64 0x165dc) by (rewrite (getr_of_eqv _ _ 1 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by (rewrite (getr_of_eqv _ _ 2 X4 eq_refl); simp_regs; exact R3_2).
  assert (E4_4 : getr R4 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X4 eq_refl); simp_regs; exact R3_4).
  assert (E4_10 : getr R4 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X4 eq_refl); simp_regs; exact R3_18).
  assert (E4_11 : getr R4 11 = Z_to_bv 64 pl) by (rewrite (getr_of_eqv _ _ 11 X4 eq_refl); simp_regs; exact R3_8).
  assert (E4_18 : getr R4 18 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 18 X4 eq_refl); simp_regs; exact R3_18).
  assert (K45 : scu_kx [2; 8; 9; 18] regs3 R4) by scu_tac X4.
  assert (SP4 : spZ R4 = bv_unsigned sp - 48) by (unfold spZ; rewrite E4_2, U48; lia).
  destruct (scu_str 12432 (bv_unsigned sp) L A mem md O L3 A3 m4 md3 _ _ b pl line SI4 RA SA)
    as (slack & PR & Hp0 & BS & N0 & LX & ALN & DJ & HOME & NRA).
  destruct (rec_entry_at rsegs L3 A3 m4 R REC_CALL [dec id] _ GR4) as (P0 & CA).
  pose proof CA as (_ & _ & _ & _ & NA4 & _). cbn [snd length Z.of_nat] in NA4.
  pose proof (ARGL (mkFP Ft fc')) as AL. unfold arg_line_contract in AL. rewrite SEGS in AL.
  eapply SR_bind.
  { apply (AL L3 A3 R4 m4 md3 e pl 1 line slack (sb_shift b A A3)).
    - apply (call_pre_k_of_rjr B _ 12432 (bv_unsigned sp) rec_area _ L A mem md L3 A3 m4 md3 ARG_LINE_K R4 RJ4).
      + rewrite E4_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP4. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + lia.
      + rewrite SP4. lia.
      + rewrite SP4. lia.
      + rewrite E4_4. exact HTP.
    - exact E4_10.
    - exact E4_11.
    - exact (proj2 (proj2 ER)).
    - exact (proj1 ER).
    - exact (proj1 (proj2 ER)).
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact NA4.
    - lia.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact ALN.
    - rewrite SP4. lia.
    - rewrite SP4. apply (scu_home_lower L3 A3 (bv_unsigned sp)); [lia | exact HOME].
    - unfold iv_apart. apply (scu_nra_apart pl _ e (e + CALL_SIZE)).
      + intros a Ha. apply NRA. rewrite length_app. cbn [length]. lia.
      + exact (proj1 ER).
      + exact (proj1 (proj2 ER)).
      + unfold CALL_SIZE. lia.
      + lia.
    - exact RS4.
    - rewrite SBEQ. eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono, sb_malloc_mono; exact BLE2|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + unfold LMAX in *. lia.
    - exact RA4. }
  intros c5 (L5 & A5 & R5 & m5 & md5 & -> & BK5 & UB5 & _ & RA5 & GK5 & RGN5 & ALT5).
  destruct ALT5 as [(H6 & _)|(_ & p2 & POST5 & Hp2 & _ & FB5 & BLK5 & BN5 & BS5 & BX5 & INI5 & RS5)]; [lia|].
  rewrite SEGS in RA5, BN5, BS5, BX5.
  pose proof POST5 as (PM5 & _ & _ & _ & _ & RP5 & _ & HF5 & _).
  assert (F185 : f18_words rsegs m5).
  { destruct (ax_statics AX L5 A5 m5 md5 PM5) as (_ & (g & Hg & HWg) & _).
    apply (f18_words_after m4 m5 g F184); [| exact Hg | rewrite SEGS, GRD in HWg; exact HWg].
    intros i Hi. unfold snprintf_c.GOT_GUARD. rewrite <- GOTG, <- SEGS. exact (GK5 i Hi). }
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 12432 (bv_unsigned sp) L A mem md O L3 A3 m4 md3 R
                REC_CALL [dec id] _ b ARG_LINE_K R4 _ L5 A5 R5 m5 md5 (canon line) p2 (Z.of_nat (length line) + 1)
                SI4 ltac:(cbn; lia) ltac:(rewrite SP4; lia) ltac:(rewrite SP4; lia) POST5
                ltac:(intros a Ha; cbv beta in Ha; cbn [length Z.of_nat]; lia)
                Hp2 FB5 BLK5 UB5 BK5 RGN5 BN5 BS5 BX5 (canon_no0 line N0)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                INI5 RS5 RA5 F185) as SI5.
  cbn [app] in SI5.
  pose proof FB5 as (FBlo & FBhi & _).
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m4); [exact FR4|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
    destruct (HF5 (bv_unsigned sp + -32 + i)) as [E W].
    - left. lia.
    - intros Ho. destruct (owned_low B _ LAWS _ _ _ _ _ PM4 Ho). lia.
    - intros Ho. destruct (owned_low B _ LAWS _ _ _ _ _ PM5 Ho). lia.
    - unfold scratch_k. rewrite SP4. intros [H|H]; lia.
    - intros Hr. cbv beta in Hr. unfold G_REC, REC_SC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact E | apply W]. }
  assert (R5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by exact (eq_trans (RP5 2 ltac:(unfold callee_saved; lia)) E4_2).
  assert (R5_4 : getr R5 4 = getr regs 4) by exact (eq_trans (RP5 4 ltac:(unfold callee_saved; lia)) E4_4).
  assert (R5_18 : getr R5 18 = Z_to_bv 64 e) by exact (eq_trans (RP5 18 ltac:(unfold callee_saved; lia)) E4_18).
  assert (K56 : scu_kx [2; 8; 9; 18] R4 R5) by exact (scu_kx_of_pres _ _ _ RP5).
  assert (BLE5 : sb_le (sb_shift b A A5)
                   (sb_malloc (sb_malloc b (Z.of_nat (length (dec id)) + 1)) (Z.of_nat (length line) + 1))).
  { destruct BLK5 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A3 A5).
    rewrite <- (sb_shift_add (sb_shift b A A3) L3 A3 L5 A5 bl1 bl2 p2 _ EB1 EB2).
    rewrite SBEQ. apply sb_malloc_mono, sb_malloc_mono. exact BLE2. }
  destruct (mr_model B _ LAWS L5 A5 m5 md5 PM5) as (Hh5 & Hl5 & _).
  rewrite E4_1, SEGS.
  eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of. apply scu_run3. }
  intros ms6 (can6 & -> & EQ6).
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ6) as (R6 & -> & X6).
  assert (E6_1 : getr R6 1 = Z_to_bv 64 0x165f0) by (rewrite (getr_of_eqv _ _ 1 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_2 : getr R6 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by (rewrite (getr_of_eqv _ _ 2 X6 eq_refl); simp_regs; exact R5_2).
  assert (E6_4 : getr R6 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X6 eq_refl); simp_regs; exact R5_4).
  assert (E6_10 : getr R6 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X6 eq_refl); simp_regs; exact R5_18).
  assert (E6_11 : getr R6 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X6 eq_refl); simp_regs; reflexivity).
  assert (E6_12 : getr R6 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X6 eq_refl); simp_regs; reflexivity).
  assert (K67 : scu_kx [2; 8; 9; 18] R5 R6) by scu_tac X6.
  assert (SP6 : spZ R6 = bv_unsigned sp - 48) by (unfold spZ; rewrite E6_2, U48; lia).
  pose proof SI5 as (RJ5 & GR5 & ON5 & B15 & B25 & RA5s & F185s & RS5s).
  pose proof (scu_shape m5 RA5s) as SHP.
  change (Z_to_bv 64 0x16310) with (Z_to_bv 64 ANSWER).
  apply (scu_ans (fx := mkFP Ft fc') B API SEGS ERRNO_LOW AX (ANS (mkFP Ft fc')) SLACK 12432 (bv_unsigned sp)
           L A mem md O L5 A5 R6 m5 md5 (rec_record R REC_CALL [dec id; canon line])
           ((O1 ++ [(p1, Z.of_nat (length (dec id)) + 1)]) ++ [(p2, Z.of_nat (length line) + 1)]) b
           (sb_malloc (sb_malloc b (Z.of_nat (length (dec id)) + 1)) (Z.of_nat (length line) + 1)) (sb_shift b A A5)
           e 0x10417 (REC_CALL, [dec id; canon line]) REC_MOD_HOST_SHAPE true);
    [ exact HMR
    | exact RJ5
    | rewrite E6_1; apply bv_eq; vm_compute; reflexivity
    | rewrite SP6; replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring;
      rewrite Z.mod_add by lia; exact HAL
    | rewrite SP6; lia
    | rewrite SP6; lia
    | rewrite SP6; lia
    | rewrite E6_4; exact HTP
    | exact E6_10
    | exact E6_11
    | rewrite E6_12; reflexivity
    | exact GR5
    | intros _; exact SHP
    | intros _ _; exact (ans_entry_record R REC_CALL [dec id; canon line] HN)
    | exact FRM3
    | exact F185s
    | exact RA5s
    | exact RS5s
    | reflexivity
    | exact BLE5
    | eapply room_slots_mono; [| | exact ROOM];
      [apply sb_malloc_mono, sb_malloc_mono; exact BLE5 | unfold LMAX; lia]
    | exact ON5
    | exact B15
    | exact B25
    | ].
  intros fx' L' A' regs' mem' md' O' q FPK' R7 RP7 A10' GR' ON' BL' IN' FB' NQ' BY' AP' RA' F18' INI' BLE' RES' FK7.
  rewrite E6_1.
  assert (FR7 : rw_cells rsegs mem' (bv_unsigned sp + -32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m5); [exact FR5|]. intros i Hi. cbn in Hi.
    destruct (FK7 (bv_unsigned sp + -32 + i)) as [E W]; [rewrite SP6; lia|]. split; [exact E | apply W]. }
  assert (Q7_2 : reg_get regs' 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by exact (eq_trans (RP7 2 ltac:(unfold callee_saved; lia)) E6_2).
  pose proof R7 as (PM7 & _ & _ & _ & _ & HLen7 & _).
  destruct (mr_model B _ LAWS L' A' mem' md' PM7) as (Hh7 & Hl7 & _).
  assert (SPW : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) + 48) = sp).
  { rewrite U48. replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  eapply evt_SR_canon; [ | exact Hh7 | exact Hl7 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q7_2.
    eapply scu_run4 with (s2v := reg_get regs 18) (s1v := reg_get regs 9) (s0v := reg_get regs 8) (rav := reg_get regs 1);
      [ rewrite U48; replace (bv_unsigned sp + -48 + 16) with (bv_unsigned sp + -32) by lia; exact FR7
      | rewrite U48; lia ]. }
  intros ms8 (can8 & -> & EQ8).
  rewrite SPW in EQ8.
  destruct (eqv_mkst (fx := fx') _ _ _ _ _ _ _ EQ8 eq_refl eq_refl) as (R8 & -> & X8).
  assert (RPC : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RPC.
  apply SR_ret.
  assert (K78 : scu_kx [2; 8; 9; 18] R6 regs') by exact (scu_kx_of_pres _ _ _ RP7).
  assert (K89 : scu_kx [2; 8; 9; 18] regs' R8) by scu_tac X8.
  assert (RP8 : regs_preserved regs R8).
  { apply (scu_kx_pres [2; 8; 9; 18]).
    - apply (scu_kx_trans _ regs R1 R8 K01).
      apply (scu_kx_trans _ R1 regs1 R8 K12).
      apply (scu_kx_trans _ regs1 R2 R8 K23).
      apply (scu_kx_trans _ R2 regs3 R8 K34).
      apply (scu_kx_trans _ regs3 R4 R8 K45).
      apply (scu_kx_trans _ R4 R5 R8 K56).
      apply (scu_kx_trans _ R5 R6 R8 K67).
      exact (scu_kx_trans _ R6 regs' R8 K78 K89).
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X8 eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  exists fx', L', A', R8, mem', md', (fst (sup_call_m R id line)), O', (snd (sup_call_m R id line)), q.
  split; [apply surjective_pairing|].
  split; [first [reflexivity | rewrite SEGS; reflexivity]|].
  split; [exact (scu_fp_trans fx (mkFP Ft fc') fx' FPK1 FPK')|].
  split; [exact (rjr_final B (aa_MR API) CTX 12432 rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs
                   mem md L' A' R8 mem' md' PRK R7 RP8 ltac:(intros a k G; exact (in_map fst O (a, k) G)))|].
  split; [rewrite (getr_of_eqv _ _ 10 X8 eq_refl); simp_regs; exact A10'|].
  split; [first [exact GR' | rewrite SEGS; exact GR']|].
  split; [exact ON'|].
  split; [exact BL'|].
  split; [exact IN'|].
  split; [exact FB'|].
  split; [exact NQ'|].
  split; [first [exact BY' | rewrite SEGS; exact BY']|].
  split; [exact (rjr_others_kept B (aa_MR API) 12432 (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md L' A'
                   mem' md' O R7 (fun pn H => H))|].
  split; [exact AP'|].
  split; [first [exact RA' | rewrite SEGS; exact RA']|].
  split; [first [exact F18' | rewrite SEGS; exact F18']|].
  split; [exact INI'|].
  split; [exact HLen7|].
  split; [exact BLE'|].
  exact RES'.
Qed.

End P.

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
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecAns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma srm_pf_dec : forall v, (-2^31 <= v < 2^31)%Z -> pf_bytes (pf_dec v) = dec v.
Proof.
  intros c Hc. unfold pf_dec, dec. unfold pf_bytes.
  assert (P : (10 ^ Z.of_nat (S 9) = 10000000000)%Z) by reflexivity.
  destruct (Z.ltb_spec c 0) as [N|N].
  - cbn [map app]. f_equal. replace (Z.abs c) with (- c)%Z by lia.
    exact (pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
  - cbn [app]. replace (Z.abs c) with c by lia.
    exact (pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.

Definition SRM_FMT : list Z := [37%Z; 100%Z].
Definition SRM_PS : list pf_piece := [Pd].

Lemma srm_parse : pf_parse SRM_FMT = Some SRM_PS.
Proof. reflexivity. Qed.

Lemma srm_text : forall v, pf_text SRM_PS [AInt v] = Some (pf_dec v).
Proof. intros v. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma srm_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10828 (pf_bytes (SRM_FMT ++ [0%Z])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma srm_run0 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x166b8) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 a0 s1 (Z_to_bv 64 2)
                     a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 24)%Z [C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1669c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 24%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 24%nat junk [] [8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  carve_frame 24%nat ST.
  clear FR0.
  do 7 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; eassumption.
Qed.

Definition srm_mid1 (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo v e : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x166e0) sp gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 e) (Z_to_bv 64 e)
                  (Z_to_bv 64 (bv_unsigned sp + 8)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x161c4) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp + 24)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k)
    /\ length slack = (15 - length (dec v))%nat
    /\ bytes_at rsegs m' (bv_unsigned sp + 8)%Z (dec v ++ Z_to_bv 8 0 :: slack).

Lemma srm_run1 : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v e : Z) (canary : word),
  (-2^31 <= v < 2^31)%Z ->
  stk rsegs m lo (bv_unsigned sp + 24) -> (lo + SNPRINTF_K <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  (bv_unsigned sp + 24 < 2^63)%Z ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> (bv_unsigned sp + 24 <= TASK_SIZE)%Z ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (srm_mid1 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo v e m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v) s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x166b8) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v e canary HV ST LO IE S63 FRM MI TM HTS GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (dec_length v HV) as DL.
  pose proof (srm_pf_dec v HV) as PD.
  assert (TL : length (pf_dec v) = length (dec v)) by (rewrite <- PD; unfold pf_bytes; rewrite length_map; reflexivity).
  carve_frame 16%nat ST.
  carve_frame 8%nat ST.
  clear FR0.
  match type of ST with stk _ _ _ ?h => replace h with (bv_unsigned sp) in ST by lia end.
  match type of FR with rw_cells _ _ ?h _ => replace h with (bv_unsigned sp + 8)%Z in FR by lia end.
  do 7 step.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m (bv_unsigned sp + 8)%Z junk).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  assert (JL : length junk = 16%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary SRM_FMT SRM_PS
              [AInt v] (pf_dec v) junk).
    - rewrite unsigned_lit by lia. apply srm_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, SRM_FMT. cbn [length]. lia.
    - exact srm_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply lit_mod32].
    - exact (srm_text v).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply pf_img_free_hi. lia.
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
  replace (ret_pc (Z_to_bv 64 91860)) with (Z_to_bv 64 91860) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (pf_dec v))) BJ) as [_ BJT].
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
  apply evt_done. unfold srm_mid1.
  do 16 eexists. exists (skipn (S (length (pf_dec v))) junk). split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  split; [eapply wmono_trans; [apply wmono_refl | exact WM2]|].
  split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, TL; lia|].
  exact BUF.
Qed.

Lemma srm_run2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x166f4) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                                      a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x166e0) fc None m (seg_rom rsegs)).
Proof. intros. do 5 step. apply evt_done. reflexivity. Qed.

Lemma srm_run3 :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 : word),
  rw_cells rsegs m (bv_unsigned sp0 + -24)%Z [C8 s01; C8 s00; C8 ra0] -> (48 <= bv_unsigned sp0)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x166f4) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 5 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 + -48 + 48)) with sp0
    by (replace (bv_unsigned sp0 + -48 + 48)%Z with (bv_unsigned sp0) by ring; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB RecSeq RecStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecGlue RecTail RecAnsB RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import xmalloc_c record_c arg_s_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Local Open Scope Z_scope.

Definition srm_kept (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma srm_kept_trans : forall R1 R2 R3, srm_kept R1 R2 -> srm_kept R2 R3 -> srm_kept R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr N2 N8 N9. rewrite (H2 r Hr N2 N8 N9). exact (H1 r Hr N2 N8 N9). Qed.

Lemma srm_kept_of_pres : forall R R', regs_preserved R R' -> srm_kept R R'.
Proof. intros R R' H r Hr _ _ _. exact (H r Hr). Qed.

Ltac srm_kept_tac X :=
  intros rr Hrr Nrr2 Nrr8 Nrr9; unfold callee_saved in Hrr;
  assert (CC : rr = 3 \/ rr = 4 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/
               rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr Nrr2 Nrr8 Nrr9;
  repeat (destruct CC as [CC|CC]; [subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
    simp_regs; first [reflexivity | unfold getr; reflexivity]|]);
  subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
  simp_regs; first [reflexivity | unfold getr; reflexivity].

Lemma srm_pres : forall (regs R : bvmap 5 word), srm_kept regs R ->
  getr R (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) -> getr R (Z_to_bv 5 8) = getr regs (Z_to_bv 5 8) ->
  getr R (Z_to_bv 5 9) = getr regs (Z_to_bv 5 9) -> regs_preserved regs R.
Proof.
  intros regs R KR E2 E8 E9 r Hr.
  destruct (Z.eq_dec r 2) as [->|N2]; [exact E2|].
  destruct (Z.eq_dec r 8) as [->|N8]; [exact E8|].
  destruct (Z.eq_dec r 9) as [->|N9]; [exact E9|].
  exact (KR r Hr N2 N8 N9).
Qed.

Lemma srm_mod8 : forall s0 k, s0 mod 16 = 0 -> 1 <= k <= 11 -> (- (s0 - 40 + k + 1)) mod 8 <= 15 - k.
Proof. intros s0 k H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma srm_malloc_le2 : forall b b' n n', sb_le b b' -> n <= n' -> sb_le (sb_malloc b n) (sb_malloc b' n').
Proof. intros b b' n n' H Hn. unfold sb_le, sb_malloc in *. cbn. lia. Qed.

Lemma srm_host_shape : forall m, ro_agree rsegs m -> ans_shape rsegs m 0x10417 REC_MOD_HOST_SHAPE.
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

Lemma srm_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma srm_stub_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length x) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - pose proof (inst_length x). lia.
  - rewrite srm_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Section AnsCall.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis ANS : answer_contract B API.
Hypothesis SLACK : block_slack_present B API.

Definition ans_mid (K S : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (O : list (Z * Z))
    (regs1 : bvmap 5 word) (mem1 : word -> option byte) (R1 : rstate) (e : rcall) (x : list byte) (chg : bool)
    (b bpre : sbound) (c' : config) : Prop :=
  let t := snd (rec_answer R1 e x chg) in
  let n := Z.of_nat (length t) + 1 in
  exists (fx' : YK11.FPState) L' A' regs' mem' md' O' q,
    c' = mkCfg (@mkst fx' regs' (getr regs1 1) mem' (seg_rom rsegs)) md' /\
    fp_kept fx fx' /\
    rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' mem' md' /\
    regs_preserved regs1 regs' /\
    (forall a, spZ regs1 <= a < S ->
       mbyte rsegs mem' a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem' a)) /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep rsegs L' A' mem' (fst (rec_answer R1 e x chg)) O' /\ owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
    In (q, n) (blocks L' A') /\ fresh_block B q n /\ ~ In q (map fst O') /\
    Mem.bytes_at rsegs mem' q (t ++ [Z_to_bv 8 0]) /\
    others_kept rsegs L A mem L' A' mem' O /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + n <= ptr_addr L p) /\
    ro_agree rsegs mem' /\ f18_words rsegs mem' /\ st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_malloc (sb_malloc bpre n) n) /\ res_ok_slots A' (sb_shift b A A').

Lemma answer_call : forall K S L A mem md (O : list (Z * Z)) L1 A1 regs1 mem1 md1 (R1 : rstate)
    (O1 : list (Z * Z)) bc bpre c sh e x chg,
  sinv B API K S L A mem md O L1 A1 mem1 md1 R1 O1 bc ->
  YK0s.ret_ok (getr regs1 1) -> spZ regs1 mod 16 = 0 -> S - K <= spZ regs1 - ANSWER_K -> spZ regs1 <= S ->
  spZ regs1 <= TASK_SIZE -> getr regs1 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs1 10 = Z_to_bv 64 c -> getr regs1 11 = Z_to_bv 64 sh -> chg = negb (bv_unsigned (getr regs1 12) =? 0) ->
  (r_refuse R1 = 0 -> ans_shape rsegs mem1 sh x) ->
  (r_refuse R1 = 0 -> chg = true -> ans_entry R1 c e) ->
  frm_zero fp_csr ->
  sb_le (sb_shift bc A A1) bpre ->
  room_ag (sb_malloc (sb_malloc (sb_shift bc A A1) (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1))
                (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1))
             (Z.of_nat (length (snd (rec_answer R1 e x chg))) + 1) ->
  SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 ANSWER) mem1 (seg_rom rsegs)) md1)
    (ans_mid K S L A mem md O regs1 mem1 R1 e x chg bc bpre).
Proof using SEGS AX ERRNO_LOW ANS SLACK.
  intros K S L A mem md O L1 A1 regs1 mem1 md1 R1 O1 bc bpre c sh e x chg
    SI RET AL LO HI HTS HTP A10 A11 ACH SHAPE ENTRY FRM BLE ROOM1.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof ERRNO_LOW as EL.
  pose proof SI as (R & GREP1 & P1 & P2 & P5 & RO1 & F18 & RES1).
  pose proof R as R0.
  destruct R0 as (HM1 & HWA & HW1 & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  assert (KA : 0 <= ANSWER_K) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (PRE1 : call_pre_t B API ANSWER_K L1 A1 regs1 mem1 md1).
  { split; [|exact HTS].
    exact (call_pre_k_of_rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L1 A1 mem1 md1 ANSWER_K regs1
             R RET AL KA LO HI HTP). }
  pose proof ANS as ANS0. unfold answer_contract in ANS0. rewrite SEGS in ANS0.
  eapply SR_mono.
  { apply (ANS0 L1 A1 regs1 mem1 md1 R1 O1 c sh e x chg (sb_shift bc A A1) PRE1 A10 A11 ACH GREP1 SHAPE);
      [|exact FRM | exact F18 | exact RES1 | exact ROOM1 | exact RO1].
    intros Hr Hc. split; [exact (ENTRY Hr Hc)|]. intros q k a Hq Ha. exact (SLACK L1 A1 mem1 md1 q k a HM1 Hq Ha). }
  intros c' RETA. unfold answer_ret in RETA.
  destruct RETA as (fx' & L' & A' & regs' & mem' & md' & p1 & p2 & old & O' & EC & FPK & OLDB & POST & A0 & NE12 & AL1
    & AL2 & FR1 & FR2 & (c1 & c2 & HB & HIFF & NI1 & NI2) & BK & UBK & GREP' & HO' & HO2 & HBC & BY1 & BY2 & RA' & F18'
    & GK & INIT & REG & GR' & RES').
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  rewrite SEGS in EC, GREP', BY2, RA', F18'.
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
    - exact LO.
    - exact HI.
    - intros a Ha _.
      unfold ans_writes, rec_area, G_REC, REC_SC, OFF_ANSWER, OFF_STATE, SC_SIZE, REC_SIZE in *.
      split; [lia|]. lia.
    - intros p k Hu Hno Hk E.
      destruct (STAB p k Hu Hno) as [Hu1 Ep].
      pose proof (mr_blocks_range B (aa_MR API) LAWS L1 A1 mem1 md1 p k HM1 Hu1) as Hr. rewrite Ep in Hr.
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
  assert (KST : forall a, spZ regs1 <= a < S ->
            mbyte rsegs mem' a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem' a)).
  { intros a Ha. rewrite <- SEGS. apply PF.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L1 A1 mem1 md1 a HM1 Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L' A' mem' md' a PM Ho). lia.
    - unfold scratch_k. intros [H|H]; lia.
    - unfold ans_writes, G_REC, OFF_ANSWER, OFF_STATE. lia. }
  pose proof (rjr_others_kept B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' mem' md' O R2
                (fun pn H => H)) as OK.
  rewrite SEGS in OK.
  destruct (tail_owns_blocks (blocks L A) (blocks L1 A1) (blocks L' A') O O1 O' c1 c2 old kold p1 p2 n
              P1 P2 P5 HB' NI1 HO' HBC) as [OWN BLK].
  assert (Hq : In (p2, n) (blocks L' A')) by (apply HIFF; right; right; reflexivity).
  unfold ans_mid. exists fx', L', A', regs', mem', md', O', p2.
  split; [exact EC|].
  split; [exact FPK|]. split; [exact R2|]. split; [exact PR|]. split; [exact KST|]. split; [exact A0|].
  split; [exact GREP'|]. split; [exact OWN|]. split; [exact BLK|]. split; [exact Hq|]. split; [exact FR2|].
  split; [intros Hin; apply in_map_iff in Hin as (pn & Epn & Hpn); exact (HO2 pn Hpn Epn)|].
  split; [exact BY2|]. split; [exact OK|].
  split.
  { intros p0 k0 Hu0 Hno0.
    revert p0 k0 Hu0 Hno0.
    apply (q_apart_tail B (aa_MR API) LAWS rsegs L A mem L' A' mem' md' O p2 n PM OK Hq).
    intros p k Hu Hno. destruct (STAB p k Hu Hno) as [Hu1 Ep].
    apply (tail_q_distinct (blocks L A) (blocks L1 A1) O O1 c1 c2 old kold p2 n (ptr_addr L p, k) P1 HB' NI2).
    - exact (user_in_blocks L A p k Hu).
    - exact Hno.
    - rewrite <- Ep. exact (user_in_blocks L1 A1 p k Hu1). }
  split; [exact RA'|]. split; [exact F18'|]. split; [exact INIT|]. split; [lia|].
  rewrite <- (sb_shift_trans bc A A1 A').
  split; [eapply sb_le_trans; [exact GR' | apply sb_malloc_mono; apply sb_malloc_mono; exact BLE] | exact RES'].
Qed.

End AnsCall.

Section Main.
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
Hypothesis SNP : snprintf_contract.
Hypothesis ARGS : forall fx' : YK11.FPState, @arg_s_contract fx' rc B API.
Hypothesis ANS : forall fx' : YK11.FPState, @answer_contract fx' rc B API.

Theorem sup_remove_holds : sup_remove_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN AX CTX SLACK REC SNP ARGS ANS.
  unfold sup_remove_contract.
  intros L A regs mem md id R O b PRE GA HID GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof ERRNO_LOW as EL.
  pose proof PRE as (PRK & HTS).
  change SUP_REMOVE_K with 12432 in PRK |- *.
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite SEGS in GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API 12432 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof GR as (Q0 & (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HCODE & _) & _) & _).
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as H16.
  pose proof (dec_length id HID) as DL.
  assert (LT : (length (snd (sup_remove_m R id)) <= 16)%nat).
  { unfold sup_remove_m, rec_stub. pose proof (srm_stub_len R REC_REMOVE [dec id] REC_MOD_HOST_SHAPE true HCODE) as H.
    assert (LX : length REC_MOD_HOST_SHAPE = 6%nat) by reflexivity. rewrite LX in H. exact H. }
  destruct (rec_entry_bounds R H16) as (EB1 & EB2 & EB3).
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST0 : stk rsegs mem (bv_unsigned sp - 12432) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold SUP_REMOVE.
    eapply srm_run0 with (lo := bv_unsigned sp - 12432); [exact ST0 | lia | lia]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x166b8) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; exact GA).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 2) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (KR1 : srm_kept regs R1) by srm_kept_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12432 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 12432 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 REC_REMOVE _ SI1).
  { rewrite E1_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia. }
  { rewrite SP1. lia. }
  { rewrite E1_4. exact HTP. }
  { exact E1_10. }
  { unfold REC_FN_COUNT, REC_REMOVE. lia. }
  intros L1 A1 regs_r m_r md_r O_r SIr BLEr RPr R10 KSTr.
  rewrite E1_1.
  pose proof SIr as (RJr & GRr & ONr & B1r & B2r & RAr & F18r & RESr).
  pose proof RJr as (HMr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSCr & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HMr) as (Hhr & Hlr & _).
  assert (Er2 : getr regs_r 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (RPr 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (Er4 : getr regs_r 4 = reg_get regs 4) by exact (eq_trans (RPr 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (Er8 : getr regs_r 8 = Z_to_bv 64 id) by exact (eq_trans (RPr 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (KRr : srm_kept regs regs_r) by exact (srm_kept_trans _ _ _ KR1 (srm_kept_of_pres _ _ RPr)).
  assert (FRr : rw_cells rsegs m_r (bv_unsigned sp - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (KSTr (bv_unsigned sp - 24 + i)) as [Ea Eb]; [rewrite SP1; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  pose proof F18r as (GGr & canary & GWr).
  assert (GGb : bytes_at rsegs m_r snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GGr as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs m_r snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GWr as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (STn : stk rsegs (normalize_cj rsegs m_r) (bv_unsigned sp - 12432) (bv_unsigned sp - 24)).
  { apply stk_normalize_cj; [lia | lia | intros a Ha; rewrite <- SEGS; apply HSCr; left; lia]. }
  pose proof (bytes_at_normalize_cj_low rsegs m_r snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RAr
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs m_r snprintf_c.GUARD (Mem.le8 canary) RAr
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  assert (Q8 : reg_get regs_r 8 = Z_to_bv 64 id) by exact Er8.
  assert (Q10 : reg_get regs_r 10 = Z_to_bv 64 e) by exact R10.
  assert (Q2 : reg_get regs_r 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by exact Er2.
  eapply evt_SR_canon; [ | exact Hhr | exact Hlr | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8, Q10, Q2.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RAr |].
    eapply (srm_run1 SNP) with (lo := bv_unsigned sp - 12432) (canary := canary).
    - exact HID.
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp - 48 + 24) with (bv_unsigned sp - 24) by ring. exact STn.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m_r)).
    - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m_r)).
    - rewrite unsigned_lit by lia. lia.
    - exact GGn.
    - exact GWn. }
  intros ms2 (can2 & (s2n & Q2' & REL2 & RO2) & EQ2).
  unfold srm_mid1 in Q2'.
  destruct Q2' as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m2n & slack
    & -> & MU2n & WM2n & MI2n & FRM1 & FK1 & SL & BUF2n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL2) as [EC2 MR2r].
  revert EC2 MR2r RO2 EQ2. generalize (ms_mem can2) as m2. intros m2 EC2 MR2r RO2 EQ2. subst can2.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs m_r RAr) MR2r RO2 MU2n) as MU2.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs m_r RAr) MR2r RO2 WM2n) as WM2.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR2r BUF2n) as BUF2.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ2) as (R2 & -> & X2).
  clear MU2n WM2n MI2n BUF2n EQ2 MR2r.
  rewrite unsigned_lit in MU2, BUF2 by lia.
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x166e0) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_4 : getr R2 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs; exact Er4).
  assert (E2_9 : getr R2 9 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_10 : getr R2 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_11 : getr R2 11 = Z_to_bv 64 (bv_unsigned sp - 40)).
  { rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs. rewrite unsigned_lit by lia. f_equal. lia. }
  assert (KR2 : srm_kept regs_r R2) by srm_kept_tac X2.
  assert (SP2 : spZ R2 = bv_unsigned sp - 48) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 12432 (bv_unsigned sp) L A mem md O L1 A1 m_r md_r
                (rec_record R REC_REMOVE []) O_r b m2 _ SIr MU2 WM2 ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI2.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_out rsegs _ m_r m2 _ _ FRr MU2). intros i Hi. cbn in Hi. split; [lia|]. cbn [outside].
    split; [lia | exact I]. }
  apply (sinv_arg_s (fx := mkFP F1 fc1) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS _) 12432 (bv_unsigned sp) L A mem md O
           L1 A1 m2 md_r R REC_REMOVE O_r b R2 (bv_unsigned sp - 40) (Some (dec id)) _ SI2).
  { rewrite E2_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP2. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP2. lia. }
  { rewrite E2_4. exact HTP. }
  { exact E2_10. }
  { exact E2_11. }
  { cbn [arg_s_src]. rewrite SP2, SEGS.
    split; [lia|]. split; [apply dec_no0|]. split; [unfold LMAX; lia|].
    exists slack. split; [replace (bv_unsigned sp - 40) with (bv_unsigned sp - 48 + 8) by ring; exact BUF2|].
    split; [rewrite SL; pose proof (srm_mod8 (bv_unsigned sp) (Z.of_nat (length (dec id))) HAL ltac:(lia)); lia|].
    split; [right; lia|]. left. split; lia. }
  { cbn [sarg].
    apply (room_slots_mono _ (sb_mallocs b [Z.of_nat (length (dec id)) + 1; 17; 17]) _ 17); [| lia | exact ROOM].
    unfold sb_mallocs. cbn [fold_left].
    rewrite sb_shift_refl in BLEr.
    apply (sb_le_trans _ (sb_malloc b (Z.of_nat (length (dec id)) + 1))); [exact (sb_malloc_mono _ _ _ BLEr)|].
    apply (sb_le_trans _ (sb_malloc (sb_malloc b (Z.of_nat (length (dec id)) + 1)) 17)); apply sb_le_malloc; lia. }
  intros L3 A3 R3 m3 md3 p SI3 EQB3 INIT3 PR3 KST3.
  rewrite E2_1.
  pose proof SI3 as (RJ3 & GR3 & _ & _ & _ & RA3 & F183 & RES3).
  pose proof RJ3 as (HM3 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM3) as (Hh3 & Hl3 & _).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. cbn in Hi.
    destruct (KST3 (bv_unsigned sp - 24 + i)) as [Ea Eb]; [rewrite SP2; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of. eapply srm_run2. }
  intros ms4 (can4 & Q4 & EQ4). subst can4.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ4) as (R4 & -> & X4). clear EQ4.
  assert (E4_1 : getr R4 1 = Z_to_bv 64 0x166f4) by (rewrite (getr_of_eqv _ _ 1 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp - 48)).
  { rewrite (getr_of_eqv _ _ 2 X4 eq_refl); simp_regs. exact (eq_trans (PR3 2 ltac:(unfold callee_saved; lia)) E2_2). }
  assert (E4_4 : getr R4 4 = reg_get regs 4).
  { rewrite (getr_of_eqv _ _ 4 X4 eq_refl); simp_regs. exact (eq_trans (PR3 4 ltac:(unfold callee_saved; lia)) E2_4). }
  assert (E4_10 : getr R4 10 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 10 X4 eq_refl); simp_regs. exact (eq_trans (PR3 9 ltac:(unfold callee_saved; lia)) E2_9). }
  assert (E4_11 : getr R4 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_12 : getr R4 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X4 eq_refl); simp_regs; reflexivity).
  assert (KR4 : srm_kept R3 R4) by srm_kept_tac X4.
  assert (SP4 : spZ R4 = bv_unsigned sp - 48) by (unfold spZ; rewrite E4_2; apply unsigned_lit; lia).
  assert (BLE3 : sb_le (sb_shift b A A3) (sb_malloc b (Z.of_nat (length (dec id)) + 1))).
  { rewrite EQB3. apply sb_malloc_mono. rewrite sb_shift_refl in BLEr. exact BLEr. }
  eapply SR_bind.
  { apply (answer_call (fx := mkFP F1 fc1) B API SEGS AX ERRNO_LOW (ANS _) SLACK 12432 (bv_unsigned sp) L A mem md O
             L3 A3 R4 m3 md3 (rec_record R REC_REMOVE [dec id]) (O_r ++ [(p, Z.of_nat (length (dec id)) + 1)]) b
             (sb_malloc b (Z.of_nat (length (dec id)) + 1)) e 0x10417 (REC_REMOVE, [dec id]) REC_MOD_HOST_SHAPE true SI3).
    - rewrite E4_1. apply bv_eq. vm_compute. reflexivity.
    - rewrite SP4. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
      exact HAL.
    - rewrite SP4. assert (AK : ANSWER_K = 12384) by reflexivity. rewrite AK. lia.
    - rewrite SP4. lia.
    - rewrite SP4. lia.
    - rewrite E4_4. exact HTP.
    - exact E4_10.
    - exact E4_11.
    - rewrite E4_12. reflexivity.
    - intros _. apply srm_host_shape. exact RA3.
    - intros _ _. exact (ans_entry_record R REC_REMOVE [dec id] H16).
    - cbn [fp_csr]. exact FRM1.
    - exact BLE3.
    - unfold sup_remove_m, rec_stub in LT.
      apply (room_slots_mono _ (sb_mallocs b [Z.of_nat (length (dec id)) + 1; 17; 17]) _ 17); [| lia | exact ROOM].
      unfold sb_mallocs. cbn [fold_left].
      apply srm_malloc_le2; [apply srm_malloc_le2; [exact BLE3 | lia] | lia]. }
  intros c5 MID. unfold ans_mid in MID.
  destruct MID as (fx' & L' & A' & R5 & m5 & md5 & O' & q & -> & FPK & RJ5 & PR5 & KST5 & A05 & GR5 & ON5 & BL5 & INq
    & FRq & NIq & BYq & OK5 & AP5 & RA5 & F185 & INIT5 & RG5 & SB5 & RS5).
  pose proof RJ5 as (HM5 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM5) as (Hh5 & Hl5 & _).
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (KST5 (bv_unsigned sp - 24 + i)) as [Ea Eb]; [rewrite SP4; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  assert (Q52 : reg_get R5 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by exact (eq_trans (PR5 2 ltac:(unfold callee_saved; lia)) E4_2).
  rewrite E4_1.
  eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q52.
    eapply srm_run3; [exact FR5 | lia]. }
  intros ms6 (can6 & Q6 & EQ6). subst can6.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ6) as (R6 & -> & X6). clear EQ6.
  assert (KR6 : srm_kept R5 R6) by srm_kept_tac X6.
  assert (RP : regs_preserved regs R6).
  { apply srm_pres.
    - apply (srm_kept_trans _ _ _ KRr). apply (srm_kept_trans _ _ _ KR2).
      apply (srm_kept_trans _ _ _ (srm_kept_of_pres _ _ PR3)). apply (srm_kept_trans _ _ _ KR4).
      exact (srm_kept_trans _ _ _ (srm_kept_of_pres _ _ PR5) KR6).
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 2) X6 eq_refl). simp_regs. first [reflexivity | unfold getr; reflexivity].
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 8) X6 eq_refl). simp_regs. first [reflexivity | unfold getr; reflexivity].
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 9) X6 eq_refl). simp_regs. first [reflexivity | unfold getr; reflexivity]. }
  assert (E6_10 : getr R6 10 = Z_to_bv 64 q) by (rewrite (getr_of_eqv _ _ 10 X6 eq_refl); simp_regs; exact A05).
  assert (RPC : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  apply SR_ret. cbv beta.
  exists (mkFP (@fp_regs fx') (@fp_csr fx')), L', A', R6, m5, md5, (fst (sup_remove_m R id)), O',
    (snd (sup_remove_m R id)), q.
  split; [apply surjective_pairing|].
  split; [rewrite RPC; reflexivity|].
  split.
  { destruct FPK as [FZ' FK']. split; [exact FZ'|]. intros r Hr. cbn [fp_regs]. rewrite (FK' r Hr). cbn [fp_regs].
    apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  split.
  { apply (rjr_final B (aa_MR API) CTX 12432 rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs mem md
             L' A' R6 m5 md5 PRK RJ5 RP).
    intros a0 k0 G. exact (in_map fst O (a0, k0) G). }
  split; [exact E6_10|]. split; [exact GR5|]. split; [exact ON5|]. split; [exact INq|]. split; [exact FRq|].
  split; [exact NIq|]. split; [exact BYq|]. split; [exact OK5|]. split; [exact BL5|].
  split.
  { change (snd (sup_remove_m R id)) with
      (snd (rec_answer (rec_record R REC_REMOVE [dec id]) (REC_REMOVE, [dec id]) REC_MOD_HOST_SHAPE true)).
    intros p0 k0 H1 H2. pose proof (AP5 p0 k0 H1 H2). lia. }
  split; [exact RA5|]. split; [exact F185|]. split; [exact INIT5|]. split; [exact RG5|].
  split; [exact SB5 | exact RS5].
Qed.

End Main.

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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/verbs_receive_br.v; 350 of its 401 lines of code are new or changed and 168 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/verbs_receive_fin_t.v; 222 of its 407 lines of code are new or changed and 216 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require CType.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_tail0 verbs_receive_br2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strcspn_c strncmp_c atoi_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import sup_after_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition tla_cond (v : list byte) : bool := verb_is_m v fmt_preset_load || verb_is_m v fmt_patch_set.

Definition tla_post (sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p0 : word) (v a : list byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' p0 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6')
             F (Z_to_bv 64 (if tla_cond v then SUP_AFTER_REPLY else 0x17b10)) fc None m' (seg_rom rsegs) /\
    (tla_cond v = true -> ra' = Z_to_bv 64 0x17b10 /\ a0' = Z_to_bv 64 (atoi_c.atoi_val a) /\ a1' = p0) /\
    munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono rsegs m m'.

Ltac tla_ret :=
  lazymatch goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (apply bv_eq; vm_compute; reflexivity)
  end.

Lemma tla_swrap : forall z, -2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof. intros z. rewrite bv_swrap32_eq. pose proof (Z.mod_pos_bound (z + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia. Qed.

Lemma tla_acc : forall s n, -2 ^ 31 <= n < 2 ^ 31 -> -2 ^ 31 <= atoi_c.atoi_acc n s < 2 ^ 31.
Proof.
  induction s as [|b s IH]; intros n Hn; cbn [atoi_c.atoi_acc]; [exact Hn|].
  destruct (CType.c_digit b); [apply IH; apply tla_swrap | exact Hn].
Qed.

Lemma tla_atoi : forall s, -2 ^ 31 <= atoi_c.atoi_val s < 2 ^ 31.
Proof.
  intros s. unfold atoi_c.atoi_val. destruct (CType.skip_space s) as [|b r]; [lia|].
  destruct (bv_unsigned b =? 45); [apply tla_acc; lia|].
  destruct (bv_unsigned b =? 43); apply tla_swrap.
Qed.

Section TA.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis SAR : forall f : YK11.FPState, @sup_after_reply_contract f rc B API.
Hypothesis CSPN : strcspn_contract.
Hypothesis NCMP : strncmp_contract.
Hypothesis ATOI : atoi_contract.
Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).
Local Notation TS f := (@tl_state f _ B API S).

Lemma tla_cmp : forall (f : list byte) (A n : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m2 : word -> option byte) (p0 p1 : word) (v a : list byte),
  verbs_receive_disp.img_cstr_b A f = true -> 0 <= A < 2 ^ 64 -> a1 = Z_to_bv 64 A ->
  Z.of_nat (length (vfirst f)) = n -> 0 <= n < 2 ^ 64 -> a2 = Z_to_bv 64 n ->
  length (tfirst v) = length (vfirst f) -> verb_is_m v f = tla_cond v ->
  bytes_at rsegs m2 (bv_unsigned p0) (v ++ [Z_to_bv 8 0]) -> Forall (fun b => bv_unsigned b <> 0) v ->
  bytes_at rsegs m2 (bv_unsigned sp + 16) (le8 p1) -> bytes_at rsegs m2 (bv_unsigned p1) (a ++ [Z_to_bv 8 0]) ->
  mem_inv rsegs m2 -> munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 -> wmono rsegs m m2 ->
  evt rsegs (tla_post sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p0 v a)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 p0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17ae8) fc None m2 (seg_rom rsegs)).
Proof.
  intros f A n ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m m2 p0 p1 v a IMG RA E1 EN RN E2 LR CF HV NZ HP1 HA MI2 MU2 WM2.
  subst a1 a2.
  destruct (verbs_receive_disp.img_cstr m2 verbs_receive_disp.IMG_TOP sp A f MI2 (Z.le_refl _) IMG)
    as (fs & HFs & _).
  destruct (VerbsFacts.strncmp_verb v f fs NZ (proj1 (proj2 HFs)) LR) as (w & HW & RW & QW).
  rewrite EN in HW.
  do 2 zstep.
  eapply evt_cut.
  { eapply NCMP with (ls := v ++ [Z_to_bv 8 0]) (rs := f ++ Z_to_bv 8 0 :: fs) (v := w);
      [ exact HV | rewrite unsigned_lit by lia; exact (proj1 HFs) | rewrite unsigned_lit by lia; exact HW
      | exact MI2 ]. }
  intros ms' PO. unfold strncmp_post in PO.
  destruct PO as (?t0' & ?t1' & ?t2' & ?a1' & ?a2' & ?a3' & ?a4' & ?a5' & ?a6' & ?a7' & ?t3' & ?t4' & ?t5' & ?t6' & m3 &
                  E & MU3 & WM3 & MI3 & _ & _).
  subst ms'. tla_ret.
  zstep. rewrite verbs_receive_disp.eqb_small by exact RW. rewrite QW, CF.
  destruct (tla_cond v) eqn:CND; cbv beta iota delta [negb].
  - assert (T3 : forall X bs, bytes_at rsegs m2 X bs -> bytes_at rsegs m3 X bs).
    { intros X bs Hb. eapply bytes_at_transport; [exact Hb | exact MU3 | exact I]. }
    pose proof (verbs_receive_disp.read_all _ _ _ (T3 _ _ HP1)) as RD. rewrite length_le8 in RD.
    pose proof (bytes_at_bound rsegs _ _ _ HP1) as BP1. rewrite length_le8 in BP1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64) in RSP.
    do 3 zstep. cond_by false.
    zstep. clear RD. zstep.
    assert (EP1 : Z_to_bv 64 (bv_unsigned p1) = p1) by apply Z_to_bv_bv_unsigned.
    rewrite <- EP1.
    eapply evt_cut.
    { eapply ATOI with (str := a); [exact (T3 _ _ HA) | exact MI3]. }
    intros ms' PO. unfold atoi_post in PO.
    destruct PO as (?t0' & ?t1' & ?t2' & ?a1' & ?a2' & ?a3' & ?a4' & ?a5' & ?a6' & ?a7' & ?t3' & ?t4' & ?t5' & ?t6' &
                    m4 & E & MU4 & WM4 & _).
    subst ms'. tla_ret.
    do 2 zstep.
    apply evt_done. unfold tla_post. rewrite CND.
    do 17 eexists. split; [reflexivity|].
    split; [intros _; split; [reflexivity | split; reflexivity]|].
    split.
    + eapply munch_trans; [eapply munch_trans; [exact MU2 | apply verbs_receive_disp.munch_nil; exact MU3]|].
      apply verbs_receive_disp.munch_nil. exact MU4.
    + eapply wmono_trans; [eapply wmono_trans; [exact WM2 | exact WM3] | exact WM4].
  - apply evt_done. unfold tla_post. rewrite CND.
    do 17 eexists. split; [reflexivity|].
    split; [intros Hc; discriminate Hc|].
    split; [eapply munch_trans; [exact MU2 | apply verbs_receive_disp.munch_nil; exact MU3]|].
    eapply wmono_trans; [exact WM2 | exact WM3].
Qed.

Lemma tla_k : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p0 p1 can : word) (v a : list byte) (lo : Z),
  bytes_at rsegs m (bv_unsigned sp + 8) (le8 p0) -> bytes_at rsegs m (bv_unsigned sp + 16) (le8 p1) ->
  VerbsMem.cstr0_at m (bv_unsigned p0) v -> VerbsMem.cstr0_at m (bv_unsigned p1) a ->
  bv_unsigned p0 + Z.of_nat (length v) + 1 <= lo -> bv_unsigned p1 + Z.of_nat (length a) + 1 <= lo ->
  Z.of_nat (length v) <= 8192 -> VerbsMem.ssp_at m can -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> verbs_receive_disp.IMG_TOP <= lo ->
  evt rsegs (tla_post sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p0 v a)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17aa8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p0 p1 can v a lo HP0 HP1 HV HA LV LA VL HSSP HMI ST LO HIT.
  pose proof (verbs_receive_disp.read_all _ _ _ HP0) as RD. rewrite length_le8 in RD.
  zstep. clear RD.
  do 4 zstep.
  eapply evt_cut.
  { eapply CSPN with (str := v) (slack := []) (set := map (Z_to_bv 8) [32; 9]) (lo := lo) (can := can);
    [ exact (proj1 HV)
    | apply verbs_receive_disp.nz_notin; exact (proj2 HV)
    | intros Hs; cbn in Hs; lia
    | rewrite unsigned_lit by lia; apply verbs_receive_disp.img_bytes; [exact HMI | vm_compute; reflexivity]
    | apply verbs_receive_disp.nz_lit; vm_compute; reflexivity
    | exact (proj1 HSSP)
    | exact (proj2 HSSP)
    | exact ST
    | lia
    | left; cbn [length]; lia
    | left; rewrite unsigned_lit by lia; cbn [length map]; unfold verbs_receive_disp.IMG_TOP in HIT; lia
    | left; unfold CSPN_SSP_GOT, verbs_receive_disp.IMG_TOP in *; lia
    | left; unfold CSPN_SSP_GUARD, verbs_receive_disp.IMG_TOP in *; lia
    | exact HMI ]. }
  intros ms' PO. unfold strcspn_post in PO.
  destruct PO as (?t0' & ?t1' & ?t2' & ?a1' & ?a2' & ?a3' & ?a4' & ?a5' & ?a6' & ?a7' & ?t3' & ?t4' & ?t5' & ?t6' & m2 &
                  E & MU2 & WM2 & MI2 & _).
  subst ms'. tla_ret. rewrite VerbsFacts.cspn_tfirst.
  assert (TR : forall X bs, bytes_at rsegs m X bs ->
                 X + Z.of_nat (length bs) <= bv_unsigned sp - 96 \/ bv_unsigned sp <= X -> bytes_at rsegs m2 X bs).
  { intros X bs Hb Hd. eapply bytes_at_transport; [exact Hb | exact MU2 |]. cbn [disjoint_from].
    split; [exact Hd | exact I]. }
  assert (HV2 : bytes_at rsegs m2 (bv_unsigned p0) (v ++ [Z_to_bv 8 0])).
  { apply TR; [exact (proj1 HV)|]. left. rewrite length_app. cbn [length]. lia. }
  assert (HA2 : bytes_at rsegs m2 (bv_unsigned p1) (a ++ [Z_to_bv 8 0])).
  { apply TR; [exact (proj1 HA)|]. left. rewrite length_app. cbn [length]. lia. }
  assert (HP12 : bytes_at rsegs m2 (bv_unsigned sp + 16) (le8 p1)) by (apply TR; [exact HP1 | right; lia]).
  assert (LT : (length (tfirst v) <= length v)%nat) by apply VerbsFacts.upto_length.
  do 2 zstep. rewrite verbs_receive_disp.eqb_lit by lia.
  destruct (Z.of_nat (length (tfirst v)) =? 9) eqn:L9; cbv beta iota delta [negb].
  - apply Z.eqb_eq in L9.
    assert (EP : verb_is_m v fmt_preset_load = false).
    { apply VerbsFacts.verb_is_m_len_ne. vm_compute (length (vfirst fmt_preset_load)). lia. }
    do 3 zstep.
    eapply (tla_cmp fmt_patch_set 0x109bc 9);
      [ vm_compute; reflexivity | lia | reflexivity | vm_compute; reflexivity | lia | reflexivity
      | vm_compute (length (vfirst fmt_patch_set)); lia
      | unfold tla_cond; rewrite EP; reflexivity
      | exact HV2 | exact (proj2 HV) | exact HP12 | exact HA2 | exact MI2 | exact MU2 | exact WM2 ].
  - apply Z.eqb_neq in L9.
    do 2 zstep. rewrite verbs_receive_disp.eqb_lit by lia.
    destruct (Z.of_nat (length (tfirst v)) =? 11) eqn:L11; cbv beta iota delta [negb].
    + apply Z.eqb_eq in L11.
      assert (EP : verb_is_m v fmt_patch_set = false).
      { apply VerbsFacts.verb_is_m_len_ne. vm_compute (length (vfirst fmt_patch_set)). lia. }
      do 4 zstep.
      eapply (tla_cmp fmt_preset_load 0x108e8 11);
        [ vm_compute; reflexivity | lia | reflexivity | vm_compute; reflexivity | lia | reflexivity
        | vm_compute (length (vfirst fmt_preset_load)); lia
        | unfold tla_cond; rewrite EP; destruct (verb_is_m v fmt_preset_load); reflexivity
        | exact HV2 | exact (proj2 HV) | exact HP12 | exact HA2 | exact MI2 | exact MU2 | exact WM2 ].
    + apply Z.eqb_neq in L11.
      assert (CND : tla_cond v = false).
      { unfold tla_cond.
        rewrite (VerbsFacts.verb_is_m_len_ne v fmt_preset_load)
          by (vm_compute (length (vfirst fmt_preset_load)); lia).
        rewrite (VerbsFacts.verb_is_m_len_ne v fmt_patch_set)
          by (vm_compute (length (vfirst fmt_patch_set)); lia).
        reflexivity. }
      apply evt_done. unfold tla_post. rewrite CND.
      do 17 eexists. split; [reflexivity|].
      split; [intros Hc; discriminate Hc|].
      split; [exact MU2 | exact WM2].
Qed.

Lemma tla_vregs : forall rg R' rg', vregs S rg -> Regs6ss.xregs_eqv R' rg' ->
  (forall r, callee_saved r -> r <> 18 -> reg_get R' (Z_to_bv 5 r) = reg_get rg (Z_to_bv 5 r)) -> vregs S rg'.
Proof.
  intros rg R' rg' (V2 & V3 & V4 & V8 & V9 & V25 & V26 & V27) X H.
  assert (P : forall r, callee_saved r -> r <> 18 -> getr rg' (Z_to_bv 5 r) = getr rg (Z_to_bv 5 r)).
  { intros r Hr H18. pose proof (H r Hr H18) as E. cs_cases r Hr;
      first [ exfalso; lia
            | match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv R' rg' k X eq_refl), E; reflexivity end ]. }
  split; [exact (eq_trans (P 2 ltac:(unfold callee_saved; lia) ltac:(lia)) V2)|].
  split; [exact (eq_trans (P 3 ltac:(unfold callee_saved; lia) ltac:(lia)) V3)|].
  split; [exact (eq_trans (P 4 ltac:(unfold callee_saved; lia) ltac:(lia)) V4)|].
  split; [exact (eq_trans (P 8 ltac:(unfold callee_saved; lia) ltac:(lia)) V8)|].
  split; [exact (eq_trans (P 9 ltac:(unfold callee_saved; lia) ltac:(lia)) V9)|].
  split; [exact (eq_trans (P 25 ltac:(unfold callee_saved; lia) ltac:(lia)) V25)|].
  split; [exact (eq_trans (P 26 ltac:(unfold callee_saved; lia) ltac:(lia)) V26)|].
  exact (eq_trans (P 27 ltac:(unfold callee_saved; lia) ltac:(lia)) V27).
Qed.

Lemma tla_call : forall rg mem1 md1 L1 A1 R1 O1 k1 qv jk c id pv verb P,
  VS fx rg SUP_AFTER_REPLY mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  getr rg 1 = Z_to_bv 64 0x17b10 ->
  getr rg 10 = Z_to_bv 64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
  getr rg 11 = Z_to_bv 64 pv ->
  CF.RecKindB.str_arg B L1 A1 O1 (s_spf S) SUP_AFTER_REPLY_K mem1 pv verb ->
  Forall (fun n => 0 <= n <= 8194) (sup_after_reply_sizes id verb) ->
  (k1 + 2 <= 32)%nat ->
  (forall (f' : YK11.FPState) rg' mem' md' L' A' O' c',
     VS f' rg' 0x17b10 mem' md' L' A' (sup_after_reply_m R1 id verb) O' (k1 + 2) qv None jk c' -> SR rsegs c' P) ->
  SR rsegs c P.
Proof using HF HS SAR.
  intros rg mem1 md1 L1 A1 R1 O1 k1 qv jk c id pv verb P HST E1 E10 HID E11 SA HSZ HKS KONT.
  pose proof (vf_segs B API HF) as SEGS.
  assert (KR : 0 <= SUP_AFTER_REPLY_K <= 14336) by (unfold SUP_AFTER_REPLY_K; lia).
  assert (RET : YK0s.ret_ok (Z_to_bv 64 0x17b10)) by (apply bv_eq; vm_compute; reflexivity).
  destruct (vs_pre B API HF S HS rg SUP_AFTER_REPLY mem1 md1 L1 A1 R1 O1 k1 qv None jk c SUP_AFTER_REPLY_K 0x17b10
              HST E1 RET KR) as (PRE & SPR & FZ & F18 & RO & REC & HM1 & _).
  pose proof HST as (EC & FPK0 & VR & H & FR & GQ & GW).
  pose proof (h_res B API S _ _ _ _ _ _ _ _ H) as (RES & _).
  assert (HKS' : (k1 + length (sup_after_reply_sizes id verb) <= 32)%nat)
    by (unfold sup_after_reply_sizes; cbn [length]; lia).
  pose proof (st_room B API S HS k1 _ (LMAX + 1) HKS' HSZ ltac:(unfold LMAX; lia)) as ROOM.
  assert (CAP : sb_live (CF.RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_after_reply_sizes id verb)) <=
                sb_cap (CF.RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_after_reply_sizes id verb))).
  { destruct (sb_mallocs_fields (sup_after_reply_sizes id verb) (sb_n (s_b S) k1)) as (F1 & _ & F3).
    rewrite F1, F3. pose proof (proj1 (ok_room B API S HS)) as (_ & RC & _).
    unfold sb_n. cbn [sb_live sb_cap] in *. unfold sup_after_reply_sizes. cbn [length]. lia. }
  subst c. rewrite <- SEGS.
  eapply SR_bind.
  { exact (SAR fx L1 A1 rg mem1 md1 id pv verb R1 O1 (sb_n (s_b S) k1) PRE E10 HID E11
             ltac:(rewrite SPR; exact SA) REC RO FZ F18 RES ROOM). }
  intros c' (fx' & L' & A' & rg' & mem' & md' & O' & -> & FPK & POST & REC' & OWN & BLK & OK & RO' & F18' & INIT
             & RLEN & LE & RS).
  rewrite SEGS.
  pose proof POST as (HM' & _ & _ & _ & _ & HPR & _ & HFR & _ & _).
  pose proof (frame_keep B API HF S HS SUP_AFTER_REPLY_K rg mem1 mem' L1 A1 L' A' md1 md' CF.RecKindB.rec_area
                HM1 HM' SPR rec_area_low HFR) as KP.
  pose proof (gq_keep B API HF S HS SUP_AFTER_REPLY_K rg mem1 mem' L1 A1 L' A' md1 md' CF.RecKindB.rec_area
                HM1 HM' SPR KR rec_area_gq HFR) as KQ.
  destruct (gq_transfer mem1 mem' qv KQ GQ GW) as [GQ' GW'].
  pose proof (CF.RecKindB.res_ok_slots_le A' _ _ LE CAP RS) as RS2.
  apply (KONT fx' rg' mem' md' L' A' O').
  split; [rewrite E1; reflexivity|].
  split; [exact (fp_kept_trans _ _ _ FPK0 FPK)|].
  split; [exact (vregs_pres S rg rg' VR HPR)|].
  split.
  { apply (heap_step_stub B API HF S HS rg mem1 md1 L1 A1 R1 O1 k1 None SUP_AFTER_REPLY_K L' A' rg' mem' md'
      (sup_after_reply_m R1 id verb) O' [] None (k1 + 2) H SPR KR POST REC' OWN).
    - intros pn Hin. destruct (BLK pn Hin) as [Y|Y]; [left; exact Y | right; left; exact Y].
    - exact OK.
    - exact RO'.
    - exact INIT.
    - exact RLEN.
    - exact (st_res B API S HS A' k1 _ HKS' HSZ RS2).
    - exact HKS.
    - rewrite app_nil_r. reflexivity.
    - intros pn [].
    - constructor.
    - exact I. }
  split; [exact (vfr_keep B API S HS mem1 mem' jk KP FR)|].
  split; [exact GQ' | exact GW'].
Qed.

Lemma tl_after : forall rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  VS fx rg 0x17aa8 mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  (2 <= length (toks D))%nat -> (k1 + 2 <= 32)%nat ->
  (forall (f' : YK11.FPState) rg' mem' md' L' A' O' k' c',
     VS f' rg' 0x17b10 mem' md' L' A'
       (match Verbs.after atoi_c.atoi_val (toks D) with
        | Some (i, v) => sup_after_reply_m R1 i (Some v)
        | None => R1
        end) O' k' qv None jk c' ->
     (k' <= k1 + 2)%nat -> SR rsegs c' P) ->
  SR rsegs c P.
Proof using HF HS SAR CSPN NCMP ATOI.
  intros rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST L2 HK KONT.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof HST as (_ & _ & VR & H & FR & _).
  pose proof (h_tok B API S _ _ _ _ _ _ _ _ H) as TOK.
  pose proof (Forall2_length TOK) as LPT.
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as (HM1 & _ & _ & _ & _ & _ & _ & _ & HS1).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  assert (SP2 : bv_unsigned (reg_get rg 2) = s_spf S).
  { destruct VR as (V2 & _). change (reg_get rg 2) with (getr rg 2). rewrite V2. apply unsigned_lit.
    unfold s_spf, VR_K in *. lia. }
  destruct (h_x B API S _ _ _ _ _ _ _ _ H (s_cb S, s_ncb S) (or_intror (or_introl eq_refl))) as [CBIN _].
  destruct (blk_low B API HF _ _ _ _ (s_cb S) (s_ncb S) 0 HM1 CBIN ltac:(unfold s_ncb; lia)) as (_ & CBC & _ & _).
  destruct (toks D) as [|v [|a rest]] eqn:TK; cbn [length] in L2; [lia | lia |].
  assert (EV0 : nth_error (toks D) 0 = Some v) by (rewrite TK; reflexivity).
  cbn [length] in LPT.
  set (p0 := nth 0 (s_ps S) (Z_to_bv 64 0)).
  set (p1 := nth 1 (s_ps S) (Z_to_bv 64 0)).
  assert (EP0 : nth_error (s_ps S) 0 = Some p0) by (unfold p0; apply nth_error_nth'; lia).
  assert (EP1 : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
  destruct (Forall2_nth _ _ _ _ _ _ TOK EP0 (eq_refl : nth_error (v :: a :: rest) 0 = Some v)) as (CV & _ & BV).
  destruct (Forall2_nth _ _ _ _ _ _ TOK EP1 (eq_refl : nth_error (v :: a :: rest) 1 = Some a)) as (CA & _ & BA).
  assert (LV : Z.of_nat (length v) <= 8192).
  { pose proof (verbs_receive_route.toks_len D v ltac:(rewrite TK; left; reflexivity)).
    pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS). lia. }
  destruct (st_f18 B API HF _ _ _ _ HM1) as (_ & cn & SG1 & SG2).
  assert (SSP : VerbsMem.ssp_at (normalize rsegs mem1) cn).
  { split; apply (bytes_at_normalize rsegs); try exact RO1; rewrite <- SEGS.
    - apply CF.reply.le_at_bytes; [exact SG1 | unfold VerbsMem.SSP_GOT; lia | rewrite length_le8; unfold VerbsMem.SSP_GOT; lia].
    - apply CF.reply.le_at_bytes; [exact SG2 | unfold VerbsMem.SSP_GUARD; lia
                               | rewrite length_le8; unfold VerbsMem.SSP_GUARD; lia]. }
  assert (ST : stk rsegs (normalize rsegs mem1) (s_spf S - 96) (bv_unsigned (reg_get rg 2))).
  { rewrite SP2. split; [unfold s_spf, VR_K in *; lia|]. split; [unfold s_spf in *; lia|]. intros x Hx.
    assert (W : writable_at rsegs mem1 x).
    { rewrite <- SEGS. apply HS1. left. unfold s_spf, VR_K in *. lia. }
    destruct (writable_hi_present mem1 x ltac:(unfold s_spf, VR_K in *; lia) W) as [bb E].
    assert (NE : normalize rsegs mem1 (wa x) = mem1 (wa x)).
    { apply CF.RecKindB.normalize_rw. unfold wa. apply ro_addr_hi. unfold s_spf, VR_K in *. lia. }
    unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity]. }
  assert (AFT : Verbs.after atoi_c.atoi_val (v :: a :: rest) =
                if tla_cond v then Some (atoi_c.atoi_val a, v) else None) by reflexivity.
  eapply (@ka_w fx _ B API HF S HS rg 0x17aa8 mem1 md1 L1 A1 R1 O1 k1 qv None jk c [(s_spf S - 96, s_spf S)] _ P HST).
  - intros x _ Hx. cbn [Frame.outside]. split; [|exact I]. intros Hin. apply Hx. unfold s_spf, VR_K in *. lia.
  - eapply evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply tla_k with (p0 := p0) (p1 := p1) (can := cn) (v := v) (a := a) (lo := s_spf S - 96);
        [ rewrite SP2; apply (bytes_at_normalize rsegs); [exact RO1|];
          replace (s_spf S + 8) with (s_spf S + 8 + 8 * Z.of_nat 0) by lia; exact (frame_tok S mem1 jk 0 p0 FR EP0)
        | rewrite SP2; apply (bytes_at_normalize rsegs); [exact RO1|];
          replace (s_spf S + 16) with (s_spf S + 8 + 8 * Z.of_nat 1) by lia; exact (frame_tok S mem1 jk 1 p1 FR EP1)
        | split; [apply (bytes_at_normalize rsegs); [exact RO1 | exact (proj1 CV)] | exact (proj2 CV)]
        | split; [apply (bytes_at_normalize rsegs); [exact RO1 | exact (proj1 CA)] | exact (proj2 CA)]
        | unfold s_spf, VR_K in *; lia
        | unfold s_spf, VR_K in *; lia
        | exact LV
        | exact SSP
        | apply mem_inv_normalize
        | exact ST
        | rewrite SP2; lia
        | unfold verbs_receive_disp.IMG_TOP, s_spf, VR_K in *; lia ]. }
    intros ms' HQ. split; [exact HQ|].
    unfold tla_post in HQ.
    destruct HQ as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                    E & _ & MU & WM).
    do 3 eexists. split; [exact E|]. split; [rewrite SP2 in MU; exact MU | exact WM].
  - intros R' pc' m' rg' mem2 HQ X MK.
    cbv beta in HQ. unfold tla_post in HQ.
    destruct HQ as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' &
                    E & HC & _ & _).
    injection E as ER EP EM. subst R' pc' m'.
    assert (VR' : vregs S rg').
    { apply (tla_vregs rg _ rg' VR X). intros r Hr H18. cs_cases r Hr; first [exfalso; lia | reflexivity]. }
    pose proof (fun pz Epz => MK pz Epz VR') as MK'. clear MK.
    revert MK' HC. destruct (tla_cond v) eqn:CND; intros MK' HC.
    + destruct (HC eq_refl) as (Era & Ea0 & Ea1). subst ra' a0' a1'.
      pose proof (MK' SUP_AFTER_REPLY eq_refl) as HST1.
      pose proof (tla_atoi a) as HID.
      assert (HSZ : Forall (fun n => 0 <= n <= 8194) (sup_after_reply_sizes (atoi_c.atoi_val a) (Some v))).
      { unfold sup_after_reply_sizes, sarg. pose proof (dec_length _ HID) as DL.
        repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
      apply (tla_call rg' mem2 md1 L1 A1 R1 O1 k1 qv jk _ (atoi_c.atoi_val a) (bv_unsigned p0) (Some v) P HST1).
      * rewrite (getr_of_eqv _ _ 1 X eq_refl). reflexivity.
      * rewrite (getr_of_eqv _ _ 10 X eq_refl). reflexivity.
      * exact HID.
      * rewrite Z_to_bv_bv_unsigned. rewrite (getr_of_eqv _ _ 11 X eq_refl). reflexivity.
      * exact (st_tok_arg B API HF S HS rg' SUP_AFTER_REPLY mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_AFTER_REPLY_K
                 0 p0 v HST1 ltac:(unfold SUP_AFTER_REPLY_K; lia) EP0 EV0).
      * exact HSZ.
      * exact HK.
      * intros f' rg'' mem' md' L' A' O' c' HST2.
        apply (KONT f' rg'' mem' md' L' A' O' (k1 + 2)%nat c'); [|lia].
        rewrite AFT. exact HST2.
    + pose proof (MK' 0x17b10 eq_refl) as HST1.
      apply (KONT fx rg' mem2 md1 L1 A1 O1 k1 _); [|lia].
      rewrite AFT. exact HST1.
Qed.

End TA.

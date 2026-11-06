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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module names, addresses and numbers changed; 511 of its 588 lines of code are new or changed and 758 lines of the source are left out. *)
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

Definition ac_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo code : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x17198) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
                  (Z_to_bv 64 (bv_unsigned sp + -48)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x16284) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k)
    /\ length slack = (31 - length (resp code))%nat
    /\ bytes_at rsegs m' (bv_unsigned sp + -48)%Z (resp code ++ Z_to_bv 8 0 :: slack)
    /\ rw_cells rsegs m' (bv_unsigned sp + -16)%Z [C8 s0; C8 ra].

Lemma ac_run1 : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo code : Z) (canary : word),
  (-2^31 <= code < 2^31)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 + SNPRINTF_K <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  (bv_unsigned sp < 2^63)%Z ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> (bv_unsigned sp <= TASK_SIZE)%Z ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (ac_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo code m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17168) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo code canary HC ST LO IE S63 FRM MI TM HTS GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  rename FR into FRS.
  apply (rw_cells_split_CB rsegs _ _ [] 16%nat junk [] [8; 8]%nat) in FRS; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FRS.
  carve_frame 32%nat ST.
  do 10 step.
  pose proof (resp_len code HC) as RL.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m1 (bv_unsigned sp + -48)%Z junk0).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary RESP_FMT RESP_PS
              [AInt code] (RESP_HEAD ++ pf_dec code) junk0).
    - rewrite unsigned_lit by lia. apply resp_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, RESP_FMT. cbn [length]. lia.
    - exact resp_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HC | apply lit_mod32].
    - exact (resp_text code).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply pf_img_free_hi. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact MI.
    - exact (task_mem_munch1 m m1 lo (bv_unsigned sp) TM MU HTS).
    - exact GG.
    - exact GW. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m2
    & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
  rewrite !unsigned_lit in MU2, BT by lia.
  change (Z.to_nat (32 - 1)) with 31%nat in BT, MU2.
  rewrite (firstn_all2 (n := 31%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 94608)) with (Z_to_bv 64 94608) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (JL : length junk0 = 32%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  assert (FRS2 : rw_cells rsegs m2 (bv_unsigned sp + -16)%Z [C8 s0; C8 ra]).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FRS MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | split; [lia | exact I]]. }
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (RESP_HEAD ++ pf_dec code))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + -48 + Z.of_nat (S (length (RESP_HEAD ++ pf_dec code))))%Z
                   (skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)).
  { apply (bytes_at_transport rsegs _ m1 m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes ((RESP_HEAD ++ pf_dec code) ++ [0%Z]) = resp code ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (RESP_HEAD ++ pf_dec code)) with
      (pf_bytes (RESP_HEAD ++ pf_dec code)). rewrite pf_resp by exact HC. reflexivity. }
  assert (LR : length (resp code) = length (RESP_HEAD ++ pf_dec code)).
  { rewrite <- (pf_resp code HC). unfold pf_bytes. apply length_map. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp + -48)%Z
                  (resp code ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)).
  { replace (resp code ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0) with
      ((resp code ++ [Z_to_bv 8 0]) ++ skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, LR. cbn [length].
    replace (Z.of_nat (length (RESP_HEAD ++ pf_dec code) + 1))
      with (Z.of_nat (S (length (RESP_HEAD ++ pf_dec code)))) by lia. exact BJT2. }
  clear BT BJT BJT2 BJ BJL FR.
  do 2 step.
  apply evt_done. unfold ac_mid.
  do 17 eexists. exists (skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0). split; [reflexivity|].
  split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  split; [eapply wmono_trans; eassumption|].
  split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, LR; lia|].
  split; [exact BUF | exact FRS2].
Qed.

Lemma ac_run2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1719c) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17198) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evt_done. reflexivity. Qed.

Lemma ac_run3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (s0v rav : word),
  rw_cells rsegs m (bv_unsigned sp + 32)%Z [C8 s0v; C8 rav] -> (bv_unsigned sp + 48 < 2 ^ 64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1 s0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1719c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s0v rav FR HB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 5 step. apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB RecAnsB hand_back_c answer_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Local Open Scope Z_scope.

Ltac ac_mid_eq X :=
  match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X eq_refl); simp_regs; reflexivity end.

Ltac ac_pres X5 X1 G4 R1 :=
  match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X5 eq_refl); simp_regs;
    transitivity (getr R1 (Z_to_bv 5 k)); [exact (G4 k ltac:(unfold callee_saved; lia))|];
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X1 eq_refl); simp_regs; reflexivity
  end.

Section AC.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GUARDG : ms_guard B = 0x54730.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis REC_IMG : forall a, rec_area a -> in_img B a /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis REC_NO : forall L A mem md a, aa_MR API L A mem md -> rec_area a -> ~ owned B L A a.
Hypothesis SNP : snprintf_contract.
Hypothesis HB : forall fx' : YK11.FPState, @hand_back_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.

Lemma ac_assoc_nd : forall {T : Type} (l : list (T * Z)) p k n, List.NoDup (map fst l) -> In (p, k) l -> In (p, n) l -> k = n.
Proof.
  intros T. induction l as [|[p0 k0] l IH]; intros p k n ND H1 H2; [destruct H1|].
  cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - injection E1 as E1a E1b. injection E2 as E2a E2b. subst. reflexivity.
  - injection E1 as E1a E1b. subst. exfalso. apply NI. exact (in_map fst l (p, n) H2).
  - injection E2 as E2a E2b. subst. exfalso. apply NI. exact (in_map fst l (p, k) H1).
  - exact (IH p k n ND' H1 H2).
Qed.

Theorem answer_code_holds : answer_code_contract B API.
Proof using SEGS FREE_PC ERRNO_LOW GOTG GUARDG AX CTX REC_IMG REC_NO SNP HB FREE.
  unfold answer_code_contract, answer_code_ret.
  intros L A regs mem md R O code b PRE A0 HC REP FZ F18 RES ROOM RA.
  destruct PRE as [PRE HTS].
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  assert (KV : ANSWER_CODE_K = 8304) by reflexivity.
  assert (HBK : HAND_BACK_K = 8256) by reflexivity.
  rewrite KV in PRE |- *.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (resp_length code HC) as RL.
  rewrite SEGS in RA, HWS, HERR, F18.
  pose proof F18 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs mem snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (ST0 : stk rsegs (normalize_cj rsegs mem) (bv_unsigned sp - 8304) (bv_unsigned sp))
    by (apply stk_normalize_cj; [lia | exact HTS | intros a Ha; apply HWS; lia]).
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GUARD (Mem.le8 canary) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 code) by exact A0. rewrite R10.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA |].
    eapply (ac_run1 SNP) with (lo := bv_unsigned sp - 8304) (canary := canary);
      [exact HC | exact ST0 | unfold SNPRINTF_K; lia | lia | lia | exact FZ
      | exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mem))
      | exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs mem)) | exact HTS
      | exact GGn | exact GWn]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m1n
    & slack & -> & MU1n & WM1n & MI1n & FRM1 & FK1 & SL & BUF1n & FRS1n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same_cj rsegs _ _ RA RO1) as RA1.
  pose proof (rw_cells_rel_cj rsegs _ _ _ _ MR1r FRS1n) as FRS1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r BUF1n) as BUF1.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ1) as (R1 & -> & X1).
  clear MU1n WM1n MI1n FRS1n BUF1n EQ1 MR1r.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x17198) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 code) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (bv_unsigned sp + -48))
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8304 <= a < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 8304, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
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
  assert (BRNG : forall q k, In (q, k) (blocks L A) -> 4096 <= q /\ q + k <= alloc_ceiling).
  { intros q k Hq. unfold blocks in Hq. apply in_map_iff in Hq as ([p k'] & E & Hp). cbn in E. injection E as <- <-.
    exact (mr_blocks_range B _ LAWS L A mem md p k' HMR Hp). }
  rewrite <- SEGS.
  eapply SR_bind.
  { eapply (HB (mkFP F1 fc1) L A R1 m1 md (bv_unsigned sp - 48) (resp code) slack R O b).
    - rewrite HBK. split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP1; replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP1; lia|].
      split; [rewrite SP1; lia|].
      split; [intros a Ha; rewrite SP1 in Ha; rewrite SEGS; apply WM1; apply HWS; lia|].
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
      lia.
    - rewrite E1_10. reflexivity.
    - rewrite SEGS. replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. exact BUF1.
    - exact (resp_no0 code).
    - unfold LMAX. lia.
    - rewrite SL. pose proof (Z.mod_pos_bound (- (bv_unsigned sp - 48 + Z.of_nat (length (resp code)) + 1)) 8
        ltac:(lia)). lia.
    - right. rewrite SP1. lia.
    - left. rewrite SP1. lia.
    - unfold g_rec_rep in REP |- *. eapply (rec_rep_frame _ _ _ L A mem R O L A m1 REP).
      + intros a Ha. assert (Ra : 0 <= a < 2 ^ 21) by (unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia).
        split; [apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]|].
        intros W. rewrite SEGS in W |- *. apply WM1. exact W.
      + intros p n i Hin Hi. pose proof (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin) as Hb.
        pose proof (BRNG p n Hb). apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia].
      + intros pn Hin. exact (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin).
    - intros [q k] Hin. pose proof (BRNG q k (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin)).
      unfold iv_apart. cbn [fst snd]. rewrite length_app. cbn [length]. lia.
    - exact RES.
    - exact ROOM.
    - rewrite SEGS. exact RA1. }
  intros c2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & p1 & p2 & old & O2 & -> & OLD & POST2 & A0' & P12 & AL1 & AL2 & FR1
    & FR2 & BLK & KEPT & UB & REP2 & OREL & ONO & BIND & BP1 & BP2 & BS & RA2 & GK2 & INIT2 & REG2 & GR2 & RES2).
  destruct POST2 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HP2 & HVM2 & HFR2 & HBLKS2 & HSCR2).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
  destruct BLK as (c1 & c2 & COLD & CIFF & NP1 & NP2).
  set (n := Z.of_nat (length (resp code)) + 1) in *.
  assert (NN : 7 <= n <= 17) by (unfold n; lia).
  rewrite E1_1, SEGS.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of. eapply ac_run2. }
  intros ms3 (can3 & Q3 & EQ3). subst can3.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ3) as (R3 & -> & X3). clear EQ3.
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x1719c) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp + -48)).
  { rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs. exact (eq_trans (HP2 2 ltac:(unfold callee_saved; lia)) E1_2). }
  assert (E3_4 : getr R3 4 = reg_get regs 4).
  { rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs. exact (eq_trans (HP2 4 ltac:(unfold callee_saved; lia)) E1_4). }
  assert (E3_10 : getr R3 10 = Z_to_bv 64 p2) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; exact A0').
  assert (SP3 : spZ R3 = bv_unsigned sp - 48) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  assert (IN2 : In (p2, n) (blocks L2 A2)) by (apply CIFF; right; right; reflexivity).
  pose proof IN2 as IN2'. unfold blocks in IN2'. apply in_map_iff in IN2' as ([pf nf] & EPF & UPF).
  cbn [fst snd] in EPF. injection EPF as EPF ENF. subst nf.
  rewrite <- SEGS.
  replace (Z_to_bv 64 0x18ad0) with (Z_to_bv 64 (ms_free B)) by (rewrite FREE_PC; reflexivity).
  eapply SR_bind.
  { eapply (FREE (mkFP F1 fc1) L2 A2 R3 m2 md2 pf n (sb_shift b A A2)).
    - split; [exact HMR2|]. split; [exact HWF2|]. split; [exact HBD2|].
      split; [rewrite E3_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP3; replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP3; change ALLOC_STACK with 8192; lia|].
      split; [rewrite SP3; lia|].
      split; [intros a Ha; rewrite SP3 in Ha; change ALLOC_STACK with 8192 in Ha; apply HSCR2;
              unfold scratch_k; rewrite SP1, HBK; left; lia|].
      split; [rewrite E3_4; exact HTP|].
      split; [intros a Ha; apply HSCR2; right; exact Ha|].
      intros HI. rewrite INIT2 in HI. discriminate.
    - exact RA2.
    - exact UPF.
    - rewrite E3_10, EPF. reflexivity.
    - exact RES2. }
  intros c4 RET4.
  destruct RET4 as (L3 & A3 & R4 & m3 & md3 & -> & CP4 & (d1 & d2 & BL2 & BL3) & KEPT4 & RA4 & GK4 & UB4
    & INIT4 & REG4 & RES4).
  destruct CP4 as (HMR3 & HWF3 & HBD3 & HLE3 & HSTAB3 & HP4 & HVM3 & HFR3 & HBLKS3 & HSCR3).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR3) as (Hh3 & Hl3 & Hmat3).
  assert (BL2' : blocks L2 A2 = d1 ++ (p2, n) :: d2) by (rewrite <- EPF; exact BL2).
  assert (DUP : forall pn, In pn (d1 ++ d2) -> pn <> (p2, n)).
  { intros pn Hin ->. destruct (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 BL2' Hin); lia. }
  assert (INC3 : incl (user_blocks A3) (user_blocks A2)).
  { apply (free_users_incl (user_blocks A2) (user_blocks A3) (ptr_addr L2) (ptr_addr L3) pf n d1 d2).
    - exact (user_block_ptrs_NoDup A2 HWF2).
    - exact UPF.
    - exact BL2.
    - exact BL3.
    - exact UB4. }
  assert (P14 : forall r, callee_saved r -> getr R4 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r)).
  { intros r Hr. rewrite (HP4 r Hr). rewrite <- (HP2 r Hr).
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold callee_saved in Hr; lia).
    repeat (destruct C as [C|C]; [subst r; ac_mid_eq X3|]).
    subst r. ac_mid_eq X3. }
  assert (G4 : forall r, callee_saved r -> reg_get R4 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r)).
  { intros r Hr. rewrite <- (P14 r Hr). unfold getr.
    assert (NZ : bv_eqb (Z_to_bv 5 r) 0 = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 5) with 32. unfold callee_saved in Hr. rewrite Z.mod_small by lia.
      change (bv_unsigned 0) with 0. lia. }
    rewrite NZ. reflexivity. }
  assert (E4_2 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by exact (eq_trans (G4 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E4_8 : reg_get R4 8 = Z_to_bv 64 code)
    by exact (eq_trans (G4 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (DOM : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
     (forall q k, In (q, k) (blocks L A) -> ~ (q <= a < q + k)) /\ ~ (p1 <= a < p1 + n) /\ ~ (p2 <= a < p2 + n)).
  { intros a Ha. split; [|split].
    - intros q k Hq Hin. unfold blocks in Hq. apply in_map_iff in Hq as ([pq kq] & Eq & Uq). cbn [fst snd] in Eq.
      injection Eq as <- <-.
      pose proof (mr_blocks_range B _ LAWS L A mem md pq kq HMR Uq).
      pose proof (ax_blocks_img AX L A mem md pq kq (a - ptr_addr L pq) HMR Uq ltac:(lia)) as NI.
      replace (ptr_addr L pq + (a - ptr_addr L pq)) with a in NI by ring.
      destruct Ha as [Ha|Ha]; [lia | exact (NI Ha)].
    - intros Hin. destruct FR1 as (F1a & F1b & F1c). pose proof (F1c (a - p1) ltac:(lia)) as NI.
      replace (p1 + (a - p1)) with a in NI by ring. destruct Ha as [Ha|Ha]; [lia | exact (NI Ha)].
    - intros Hin. destruct FR2 as (F2a & F2b & F2c). pose proof (F2c (a - p2) ltac:(lia)) as NI.
      replace (p2 + (a - p2)) with a in NI by ring. destruct Ha as [Ha|Ha]; [lia | exact (NI Ha)]. }
  assert (HF12 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8304 <= a < bv_unsigned sp - 48) ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha Hs. destruct (DOM a (or_introl Ha)) as (D1 & D2 & D3).
    apply HFR2; [left; exact Ha | intro Ho; destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho); lia
      | intro Ho; destruct (owned_low B _ LAWS _ _ _ _ _ HMR2 Ho); lia
      | unfold scratch_k; rewrite SP1, HBK; intros [H|H]; lia |].
    intros [H|[(k & Hk & H)|[H|H]]];
      [unfold G_REC, OFF_ANSWER in H; lia | exact (D1 old k Hk H) | apply D2; unfold n; lia | apply D3; unfold n; lia]. }
  assert (HF23 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8240 <= a < bv_unsigned sp - 48) ->
     mbyte (ms_segs B) m3 a = mbyte (ms_segs B) m2 a /\
     (writable_at (ms_segs B) m2 a <-> writable_at (ms_segs B) m3 a)).
  { intros a Ha Hs. destruct (DOM a (or_introl Ha)) as (D1 & D2 & D3).
    apply HFR3; [left; exact Ha | intro Ho; destruct (owned_low B _ LAWS _ _ _ _ _ HMR2 Ho); lia
      | intro Ho; destruct (owned_low B _ LAWS _ _ _ _ _ HMR3 Ho); lia
      | unfold scratch; rewrite SP3; change ALLOC_STACK with 8192; intros [H|H]; lia |].
    cbn beta. rewrite EPF. exact D3. }
  assert (HALL : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a ->
     ~ (bv_unsigned sp - 8304 <= a < bv_unsigned sp) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
     ~ (G_REC + OFF_ANSWER <= a < G_REC + OFF_ANSWER + 8) ->
     mbyte (ms_segs B) m3 a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) m3 a)).
  { intros a Hd N1 NS NE NA.
    assert (AR : 0 <= a < 2 ^ 64) by (destruct Hd as [Hd|Hd]; [lia | pose proof (in_img_low B SEGS a Hd); lia]).
    assert (N2 : ~ owned B L2 A2 a) by exact (not_owned_mid B _ LAWS AX CTX L A mem md L2 A2 m2 md2 a HMR HMR2 Hd N1).
    assert (N3 : ~ owned B L3 A3 a) by exact (not_owned_mid B _ LAWS AX CTX L A mem md L3 A3 m3 md3 a HMR HMR3 Hd N1).
    destruct (DOM a Hd) as (D1 & D2 & D3).
    assert (E01 : mbyte (ms_segs B) m1 a = mbyte (ms_segs B) mem a)
      by (apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]).
    assert (W01 : writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) m1 a)
      by (apply (munch_writable _ _ _ _ _ MU1); [lia | apply OUT1; lia]).
    assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                  (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
    { apply HFR2; [exact Hd | exact N1 | exact N2 | unfold scratch_k; rewrite SP1, HBK; intros [H|H]; [lia | exact (NE H)] |].
      intros [H|[(k & Hk & H)|[H|H]]]; [exact (NA H) | exact (D1 old k Hk H) | apply D2; unfold n; lia | apply D3; unfold n; lia]. }
    assert (H23 : mbyte (ms_segs B) m3 a = mbyte (ms_segs B) m2 a /\
                  (writable_at (ms_segs B) m2 a <-> writable_at (ms_segs B) m3 a)).
    { apply HFR3; [exact Hd | exact N2 | exact N3
        | unfold scratch; rewrite SP3; change ALLOC_STACK with 8192; intros [H|H]; [lia | exact (NE H)] |].
      cbn beta. rewrite EPF. exact D3. }
    destruct H12 as [E12 W12]. destruct H23 as [E23 W23].
    split; [rewrite E23, E12, E01; reflexivity | tauto]. }
  assert (FRS3 : rw_cells rsegs m3 (bv_unsigned sp + -16) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FRS1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
    destruct (HF12 (bv_unsigned sp + -16 + i) ltac:(lia) ltac:(lia)) as [E12 W12].
    destruct (HF23 (bv_unsigned sp + -16 + i) ltac:(lia) ltac:(lia)) as [E23 W23].
    split; [rewrite E23, E12; reflexivity | tauto]. }
  assert (GK : forall i, 0 <= i < 8 ->
     mbyte (ms_segs B) m3 (ms_got_guard B + i) = mbyte (ms_segs B) mem (ms_got_guard B + i)).
  { intros i Hi. rewrite (GK4 i Hi), (GK2 i Hi). rewrite GOTG.
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite E3_1, SEGS.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of. rewrite E4_2.
    eapply ac_run3 with (s0v := reg_get regs 8) (rav := reg_get regs 1).
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp + -48 + 32) with (bv_unsigned sp + -16) by ring. exact FRS3.
    - rewrite unsigned_lit by lia. lia. }
  intros ms5 (can5 & Q5 & EQ5). subst can5.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ5) as (R5 & -> & X5). clear EQ5.
  rewrite <- SEGS.
  apply SR_ret. cbv beta zeta.
  exists (mkFP F1 fc1), L3, A3, R5, m3, md3, p1, old, O2.
  split; [rewrite RP; reflexivity|].
  split.
  { unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
    intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  split.
  { apply (bytes_at_transfer _ m1); [exact OLD|]. intros i Hi. rewrite Mem.length_le8 in Hi.
    symmetry. apply (munch_mbyte _ _ _ _ _ MU1); [unfold G_REC, OFF_ANSWER; lia|].
    apply OUT1; unfold G_REC, OFF_ANSWER; lia. }
  split.
  { unfold call_post_rec.
    split; [exact HMR3|]. split; [exact HWF3|]. split; [exact HBD3|].
    split.
    { destruct HLE2 as (l1 & l2 & l3 & l4). destruct HLE3 as (k1 & k2 & k3 & k4).
      split; [congruence|]. split; [congruence|]. split; [congruence|].
      intros r Hr. rewrite (k4 r (Nat.lt_le_trans _ _ _ Hr REG2)). exact (l4 r Hr). }
    split.
    { intros p k H1 H3. pose proof (INC3 _ H3) as H2. rewrite (HSTAB3 p k H2 H3). exact (HSTAB2 p k H1 H2). }
    split.
    { intros r Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold callee_saved in Hr; lia).
      destruct C as [C|C].
      { subst r. rewrite (getr_of_eqv _ _ (Z_to_bv 5 2) X5 eq_refl). simp_regs.
        rewrite unsigned_lit by lia. replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by ring.
        exact (Z_to_bv_lit_self sp). }
      destruct C as [C|C]; [subst r; ac_pres X5 X1 G4 R1|].
      destruct C as [C|C]; [subst r; ac_pres X5 X1 G4 R1|].
      destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ (Z_to_bv 5 8) X5 eq_refl); simp_regs; reflexivity|].
      repeat (destruct C as [C|C]; [subst r; ac_pres X5 X1 G4 R1|]).
      subst r. ac_pres X5 X1 G4 R1. }
    split.
    { destruct HVM2 as [v2 ->]. destruct HVM3 as [v3 ->]. exists v3. apply with_vmmaps_twice'. }
    split.
    { intros a Hd N1 N3 NS NE. unfold scratch_k, spZ in NS. change (getr regs 2) with sp in NS.
      unfold ac_writes in NE.
      apply HALL; [exact Hd | exact N1 | intro H; apply NS; left; exact H | intro H; apply NS; right; exact H | exact NE]. }
    split.
    { intros p k i H1 H3 Hne Hi. pose proof (INC3 _ H3) as H2.
      pose proof (mr_blocks_range B _ LAWS L A mem md p k HMR H1) as Rg.
      rewrite <- (HSTAB2 p k H1 H2) at 1. rewrite (HBLKS3 p k i H2 H3 Hi). rewrite (HSTAB2 p k H1 H2).
      rewrite (HBLKS2 p k i H1 H2 Hne Hi).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    destruct Ha as [Ha|Ha]; [|apply HSCR3; right; exact Ha].
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 8240)) as [D1|D1].
    - apply (proj2 (HF23 a ltac:(lia) ltac:(lia))). apply HSCR2. unfold scratch_k. rewrite SP1, HBK. left. lia.
    - destruct (Z_lt_ge_dec a (bv_unsigned sp - 48)) as [D2|D2].
      + apply HSCR3. unfold scratch. rewrite SP3. change ALLOC_STACK with 8192. left. lia.
      + apply (proj2 (HF23 a ltac:(lia) ltac:(lia))). apply (proj2 (HF12 a ltac:(lia) ltac:(lia))).
        rewrite SEGS. apply WM1. apply HWS. lia. }
  split.
  { unfold rec_answer_code. cbn [snd]. rewrite (getr_of_eqv _ _ 10 X5 eq_refl). simp_regs. exact E4_8. }
  split; [exact AL1|]. split; [exact FR1|].
  split.
  { exists c1, c2. split; [exact COLD|]. split; [|exact NP1].
    intros pn. rewrite BL3. split.
    - intros Hin. pose proof (in_mid_inv d1 d2 (p2, n) pn Hin) as Hin2. rewrite <- BL2' in Hin2.
      apply CIFF in Hin2 as [H|[H|H]]; [left; exact H | right; exact H | exfalso; exact (DUP pn Hin H)].
    - intros [H|H].
      + assert (Hb : In pn (blocks L2 A2)) by (apply CIFF; left; exact H).
        rewrite BL2' in Hb. apply in_mid_other with (x := (p2, n)); [exact Hb|]. intros ->. exact (NP2 H).
      + subst pn. assert (Hb : In (p1, n) (blocks L2 A2)) by (apply CIFF; right; left; reflexivity).
        rewrite BL2' in Hb. apply in_mid_other with (x := (p2, n)); [exact Hb|]. intros E. injection E as E.
        exact (P12 E). }
  split.
  { intros a k i Hin Hne Hi.
    assert (Hc : In (a, k) (c1 ++ c2)).
    { destruct COLD as [[_ E]|(k' & _ & _ & E)]; rewrite E in Hin; [exact Hin|].
      apply in_mid_other with (x := (old, k')); [exact Hin|]. intros E'. injection E' as E1 E2. exact (Hne E1). }
    assert (Hb2 : In (a, k) (blocks L2 A2)) by (apply CIFF; left; exact Hc).
    assert (Hd : In (a, k) (d1 ++ d2)).
    { rewrite BL2' in Hb2. apply in_mid_other with (x := (p2, n)); [exact Hb2|]. intros E. rewrite E in Hc. exact (NP2 Hc). }
    assert (Hap : a <> p2).
    { intros ->. destruct (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 BL2' Hd); lia. }
    pose proof (BRNG a k Hin) as Rg.
    rewrite (KEPT4 a k i Hb2 ltac:(cbn beta; rewrite EPF; exact Hap) Hi).
    rewrite (KEPT a k i Hin Hne Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split.
  { intros q k Hu Hno.
    pose proof (UB q k Hu Hno) as Hu2.
    apply UB4; [exact Hu2|].
    intros Eq. subst q.
    pose proof (ac_assoc_nd (user_blocks A2) pf k n (user_block_ptrs_NoDup A2 HWF2) Hu2 UPF) as Ek. subst k.
    assert (Ea : ptr_addr L pf = p2) by (rewrite <- (HSTAB2 pf n Hu Hu2); exact EPF).
    assert (Hb : In (p2, n) (blocks L A))
      by (rewrite <- Ea; unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) (user_blocks A) (pf, n) Hu)).
    rewrite Ea in Hno.
    apply NP2.
    destruct COLD as [[_ E]|(k' & _ & Hk' & E)]; rewrite E in Hb; [exact Hb|].
    apply in_mid_other with (x := (old, k')); [exact Hb|]. intros E'. rewrite E' in Hno. exact (Hno Hk'). }
  split.
  { change (fst (rec_answer_code R code)) with (fst (hand_back R (resp code))).
    unfold g_rec_rep in REP2 |- *. eapply (rec_rep_frame _ _ _ L2 A2 m2 _ O2 L3 A3 m3 REP2).
    - intros a Ha. assert (RA' : rec_area a) by (unfold rec_area; tauto).
      destruct (REC_IMG a RA') as [II NEr].
      assert (H23 : mbyte (ms_segs B) m3 a = mbyte (ms_segs B) m2 a /\
                    (writable_at (ms_segs B) m2 a <-> writable_at (ms_segs B) m3 a)).
      { apply HFR3; [right; exact II | exact (REC_NO _ _ _ _ a HMR2 RA') | exact (REC_NO _ _ _ _ a HMR3 RA') | |].
        - unfold scratch. rewrite SP3. change ALLOC_STACK with 8192.
          intros [H|H]; [pose proof (in_img_low B SEGS a II); lia | exact (NEr H)].
        - cbn beta. rewrite EPF. intros H. destruct FR2 as (_ & _ & F2c). apply (F2c (a - p2)); [lia|].
          replace (p2 + (a - p2)) with a by ring. exact II. }
      split; [exact (proj1 H23) | apply (proj2 H23)].
    - intros p k i Hin Hi. pose proof (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP2 Hin) as Hb.
      apply (KEPT4 p k i Hb); [|exact Hi]. cbn beta. rewrite EPF. exact (ONO (p, k) Hin).
    - intros pn Hin. pose proof (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP2 Hin) as Hb. rewrite BL3.
      rewrite BL2' in Hb. apply in_mid_other with (x := (p2, n)); [exact Hb|]. intros ->. exact (ONO _ Hin eq_refl). }
  split; [exact OREL|].
  split.
  { intros pn Hin. rewrite BL3 in Hin. assert (Hb : In pn (blocks L2 A2)) by (rewrite BL2'; apply in_mid_inv; exact Hin).
    destruct (BIND pn Hb) as [H|[H|H]]; [left; exact H | right; exact H | exfalso; exact (DUP pn Hin H)]. }
  split.
  { apply (bytes_at_transfer _ m2); [exact BP1|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    assert (Hb : In (p1, n) (blocks L2 A2)) by (apply CIFF; right; left; reflexivity).
    apply (KEPT4 p1 n i Hb); [cbn beta; rewrite EPF; exact P12 | unfold n; lia]. }
  split; [exact RA4|].
  split.
  { rewrite SEGS. destruct (ax_statics AX L3 A3 m3 md3 HMR3) as (_ & (g & Hg & HGW) & _).
    apply (f18_words_after mem m3 g F18); [| exact Hg | rewrite SEGS, GUARDG in HGW; exact HGW].
    intros i Hi. unfold snprintf_c.GOT_GUARD. rewrite <- GOTG, <- SEGS. exact (GK i Hi). }
  split; [exact GK|].
  split; [exact (INIT4 INIT2)|].
  split; [eapply Nat.le_trans; [exact REG2 | exact REG4]|].
  rewrite <- (sb_shift_trans b A A2 A3), <- (sb_shift_del (sb_shift b A A2) L2 A2 L3 A3 d1 d2 p2 n BL2' BL3).
  split; [apply sb_free_mono; exact GR2 | exact RES4].
Qed.

End AC.

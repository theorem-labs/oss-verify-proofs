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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/verbs_receive_br.v; 224 of its 270 lines of code are new or changed and 173 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require CTypeFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_call.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_br verbs_receive_br2 sup_remove_c sup_remove_all_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma remove_acc_range : forall s n, -2^31 <= n < 2^31 -> -2^31 <= atoi_c.atoi_acc n s < 2^31.
Proof.
  induction s as [|b s IH]; intros n Hn; cbn [atoi_c.atoi_acc]; [exact Hn|].
  match goal with |- context [if ?d then _ else _] => destruct d end; [apply IH, CTypeFacts.swrap32_range | exact Hn].
Qed.

Lemma remove_atoi_range : forall s, -2^31 <= atoi_c.atoi_val s < 2^31.
Proof.
  intros s. unfold atoi_c.atoi_val.
  match goal with |- context [match ?x with [] => _ | _ :: _ => _ end] => destruct x as [|b t] end; [lia|].
  destruct (bv_unsigned b =? 45); [apply remove_acc_range; lia|].
  destruct (bv_unsigned b =? 43); apply CTypeFacts.swrap32_range.
Qed.

Lemma remove_text_len : forall R fn As ch, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_stub R fn As REC_MOD_HOST_SHAPE ch)) <= 28)%nat.
Proof.
  intros R fn As ch HC. unfold rec_stub. rewrite rec_answer_text.
  assert (E : r_code (rec_record R fn As) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
  destruct (r_refuse (rec_record R fn As) =? 0).
  - apply Nat.leb_le. vm_compute. reflexivity.
  - rewrite E. pose proof (resp_length (r_code R) HC). lia.
Qed.

Lemma remove_k1 : atoi_c.atoi_contract -> forall (tk : list (list byte))
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p1 : word) (w : list byte),
  s5 = verbs_receive_disp.ntokw tk -> (length tk <= 64)%nat -> bv_unsigned sp < 2^63 -> mem_inv rsegs m ->
  (length tk = 2%nat -> bytes_at rsegs m (bv_unsigned sp + 16) (le8 p1)) ->
  (length tk = 2%nat -> bytes_at rsegs m (bv_unsigned p1) (w ++ [Z_to_bv 8 0])) ->
  evt rsegs (fun ms' =>
      (length tk = 2%nat /\ atoi_c.atoi_val w = -1 /\ exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
       ms' = MS (mkR (Z_to_bv 64 0x1792c) sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (atoi_c.atoi_val w)) x11 x12 x13 x14 x15 x16 x17
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x16708) fc None m' (seg_rom rsegs) /\ munch [] m m' /\ wmono rsegs m m') \/
      (length tk = 2%nat /\ atoi_c.atoi_val w <> -1 /\ exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
       ms' = MS (mkR (Z_to_bv 64 0x1782c) sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (atoi_c.atoi_val w)) x11 x12 x13 x14 x15 x16 x17
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x1669c) fc None m' (seg_rom rsegs) /\ munch [] m m' /\ wmono rsegs m m') \/
      (length tk <> 2%nat /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17a88) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x177f8) fc None m (seg_rom rsegs)).
Proof.
  intros ATOI tk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p1 w E5 HL HSP MI HB HW. subst s5.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64) in RSP.
  do 2 zstep. rewrite verbs_receive_disp.eqb_ntokw by lia.
  destruct (Z.of_nat (length tk) =? 2) eqn:E; cbv beta iota delta [negb].
  - apply Z.eqb_eq in E. assert (L2 : length tk = 2%nat) by lia.
    pose proof (verbs_receive_disp.read_all _ _ _ (HB L2)) as RD. rewrite length_le8 in RD.
    do 3 zstep. cond_by false.
    do 2 zstep.
    replace p1 with (Z_to_bv 64 (bv_unsigned p1)) by apply Z_to_bv_bv_unsigned.
    eapply evt_cut; [eapply ATOI; [exact (HW L2) | exact MI]|].
    intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & EM & MU & WM & MI'). subst ms'.
    replace (ret_pc (Z_to_bv 64 0x17814)) with (Z_to_bv 64 0x17814) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    pose proof (remove_atoi_range w) as AR.
    do 2 zstep.
    rewrite (rec_shape_of.eqb_lit_signed (atoi_c.atoi_val w) (-1)) by lia.
    destruct (atoi_c.atoi_val w =? -1) eqn:EQ; cbv iota.
    + apply Z.eqb_eq in EQ. zstep. apply evt_done. left. split; [exact L2|]. split; [exact EQ|].
      do 15 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
    + apply Z.eqb_neq in EQ. do 3 zstep. cond_by false. zstep. apply evt_done. right. left. split; [exact L2|]. split; [exact EQ|].
      do 15 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
  - apply Z.eqb_neq in E. apply evt_done. right. right. split; [lia | reflexivity].
Qed.

Lemma k_j17884 : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x178ac) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x1792c) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Lemma k_j177d4 : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x178ac) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x1782c) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis AT : atoi_c.atoi_contract.
Hypothesis DR : forall f : YK11.FPState, @sup_remove_contract f rc B API.
Hypothesis DA : forall f : YK11.FPState, @sup_remove_all_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_remove : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc RRemove) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RRemove -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  join_k B API S 0x178ac 10 rg R1 k1 qv P ->
  rej_k B API S f 0x17a88 rg R1 k1 qv P ->
  SR rsegs c P.
Proof.
  intros f rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST RT N21 HK JOIN REJ.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof HST as (_ & _ & VR & H & FR & _).
  pose proof (h_tok B API S _ _ _ _ _ _ _ _ H) as TOK.
  pose proof (Forall2_length TOK) as LPT.
  pose proof (ok_psl B API S HS) as PSL.
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  assert (SP2 : bv_unsigned (reg_get rg 2) = s_spf S).
  { destruct VR as (V2 & _). change (reg_get rg 2) with (getr rg 2). rewrite V2. apply unsigned_lit.
    unfold s_spf, VR_K in *. lia. }
  assert (SPB : bv_unsigned (reg_get rg 2) < 2^63) by (rewrite SP2; unfold s_spf, VR_K in *; lia).
  assert (R21 : reg_get rg 21 = verbs_receive_disp.ntokw (toks D)) by (rewrite <- N21; reflexivity).
  assert (NL : (length (toks D) <= 64)%nat) by lia.
  set (p1 := nth 1 (s_ps S) (Z_to_bv 64 0)).
  assert (HB : length (toks D) = 2%nat -> bytes_at rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 16) (le8 p1)).
  { intros L2. rewrite SP2. apply bytes_at_normalize; [exact RO1|].
    assert (E : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
    pose proof (frame_tok S mem1 jk 1 p1 FR E) as FT.
    replace (s_spf S + 16) with (s_spf S + 8 + 8 * Z.of_nat 1) by lia. exact FT. }
  assert (HW : length (toks D) = 2%nat ->
    bytes_at rsegs (normalize rsegs mem1) (bv_unsigned p1) (nth 1 (toks D) [] ++ [Z_to_bv 8 0])).
  { intros L2. apply bytes_at_normalize; [exact RO1|].
    assert (E : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
    assert (EW : nth_error (toks D) 1 = Some (nth 1 (toks D) [])) by (apply nth_error_nth'; lia).
    destruct (Forall2_nth _ _ _ _ _ _ TOK E EW) as ((Hb & _) & _). exact Hb. }
  eapply (@ka_w f _ B API HF S HS rg (route_pc RRemove) mem1 md1 L1 A1 R1 O1 k1 qv None jk c [] _ P HST).
  { intros; exact I. }
  { eapply evt_mono.
    { unfold Regs6ss.mkR_of. cbn [route_pc]. apply (remove_k1 AT (toks D)) with (p1 := p1) (w := nth 1 (toks D) []);
      [exact R21 | exact NL | exact SPB | apply mem_inv_normalize | exact HB | exact HW]. }
    intros ms' HQ. split; [exact HQ|]. destruct HQ as [(_ & _ & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & E & MU & WM)|[(_ & _ & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & E & MU & WM)|(_ & E)]]; subst ms'.
    - do 3 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
    - do 3 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
    - do 3 eexists. split; [reflexivity|]. split; [apply munch_refl | apply wmono_refl]. }
  intros R' pc' m' rg' mem2 HQ X MK.
  destruct HQ as [(L2 & AV & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m'' & EQ & _ & _)|[(L2 & AV & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m'' & EQ & _ & _)|(L2 & EQ)]];
    injection EQ as ER EP EM; subst R' pc' m'.
  - destruct (len2 (toks D) L2) as (v & a & TK).
    assert (EAW : nth 1 (toks D) [] = a) by (rewrite TK; reflexivity).
    rewrite EAW in AV.
    assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    pose proof (MK 0x16708 eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
    assert (E1 : getr rg' 1 = Z_to_bv 64 0x1792c) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
    assert (E10 : getr rg' 10 = Z_to_bv 64 (atoi_c.atoi_val a)).
    { rewrite (getr_of_eqv _ _ 10 X eq_refl), <- EAW. reflexivity. }
    pose proof (remove_atoi_range a) as AR.
    pose proof (dec_length _ AR) as DL.
    assert (RET : YK0s.ret_ok (Z_to_bv 64 0x1792c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (KB : 0 <= SUP_REMOVE_ALL_K <= 14336) by (unfold SUP_REMOVE_ALL_K; lia).
    destruct (vs_pre B API HF S HS rg' 0x16708 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_REMOVE_ALL_K 0x1792c
                HST1 E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
    assert (LT : (length (snd (sup_remove_all_m R1)) <= 28)%nat).
    { unfold sup_remove_all_m, sup_remove_m. apply remove_text_len. exact (rep_code _ _ _ _ _ _ REC). }
    assert (HSZ : Forall (fun n => 0 <= n <= 8194) (sup_remove_all_sizes (snd (sup_remove_all_m R1)))).
    { unfold sup_remove_all_sizes. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
    assert (HKS : (k1 + length (sup_remove_all_sizes (snd (sup_remove_all_m R1))) <= 32)%nat).
    { unfold sup_remove_all_sizes. cbn [length]. lia. }
    pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST1))))) as (RES & _).
    assert (CAP : sb_live (CF.RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_remove_all_sizes (snd (sup_remove_all_m R1)))) <=
                  sb_cap (CF.RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_remove_all_sizes (snd (sup_remove_all_m R1))))).
    { destruct (sb_mallocs_fields (sup_remove_all_sizes (snd (sup_remove_all_m R1))) (sb_n (s_b S) k1)) as (F1 & _ & F3).
      rewrite F1, F3. pose proof (proj1 (ok_room B API S HS)) as (_ & RC & _).
      unfold sb_n. cbn [sb_live sb_cap] in *. unfold sup_remove_all_sizes. cbn [length]. lia. }
    apply (call_ans B API HF S HS rg' 0x16708 mem2 md1 L1 A1 R1 O1 k1 qv jk _ SUP_REMOVE_ALL_K 0x1792c
             (sup_remove_all_sizes (snd (sup_remove_all_m R1))) (sup_remove_all_m R1)
             P HST1 E1 KB HKS HSZ).
    + eapply SR_mono.
      { pose proof (st_room B API S HS k1 _ 17 HKS HSZ ltac:(lia)) as ROOM.
        pose proof (DA f L1 A1 rg' mem2 md1 R1 O1 (sb_n (s_b S) k1) PRE REC RO FZ F18 RES ROOM) as C.
        rewrite SEGS in C. unfold SUP_REMOVE_ALL in C. exact C. }
      intros c'' HR.
      exact (ans_of_ns B API HF SUP_REMOVE_ALL_K (sup_remove_all_m R1) sup_remove_all_sizes
               L1 A1 rg' mem2 md1 O1 (sb_n (s_b S) k1) c'' HR CAP).
    + intros f' rg'' mem' md' L' A' O' q c' HST2 E10' HP2.
      apply (join_jump B API HF S HS f' rg R1 k1 qv rg'' 0x1792c 0x178ac mem' md' L' A'
               (fst (sup_remove_all_m R1)) O'
               (k1 + length (sup_remove_all_sizes (snd (sup_remove_all_m R1))))
               q (snd (sup_remove_all_m R1)) jk c' P HST2 k_j17884).
      * exact E10'.
      * exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (PR 18 ltac:(unfold callee_saved; lia))).
      * exact (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (PR 21 ltac:(unfold callee_saved; lia))).
      * rewrite RT, TK. cbn [plan_at]. rewrite AV, Z.eqb_refl. unfold VerbsRun.run_step, VerbsRun.run_call.
        destruct (sup_remove_all_m R1); reflexivity.
      * unfold sup_remove_all_sizes. cbn [length]. lia.
      * exact JOIN.
  - destruct (len2 (toks D) L2) as (v & a & TK).
    assert (EAW : nth 1 (toks D) [] = a) by (rewrite TK; reflexivity).
    rewrite EAW in AV.
    assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    pose proof (MK 0x1669c eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
    assert (E1 : getr rg' 1 = Z_to_bv 64 0x1782c) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
    assert (E10 : getr rg' 10 = Z_to_bv 64 (atoi_c.atoi_val a)).
    { rewrite (getr_of_eqv _ _ 10 X eq_refl), <- EAW. reflexivity. }
    pose proof (remove_atoi_range a) as AR.
    pose proof (dec_length _ AR) as DL.
    assert (RET : YK0s.ret_ok (Z_to_bv 64 0x1782c)) by (apply bv_eq; vm_compute; reflexivity).
    assert (KB : 0 <= SUP_REMOVE_K <= 14336) by (unfold SUP_REMOVE_K; lia).
    destruct (vs_pre B API HF S HS rg' 0x1669c mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_REMOVE_K 0x1782c
                HST1 E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
    assert (LT : (length (snd (sup_remove_m R1 (atoi_c.atoi_val a))) <= 28)%nat).
    { unfold sup_remove_all_m, sup_remove_m. apply remove_text_len. exact (rep_code _ _ _ _ _ _ REC). }
    assert (HSZ : Forall (fun n => 0 <= n <= 8194) ((fun t : list byte => [(Z.of_nat (length (dec (atoi_c.atoi_val a))) + 1)%Z; (Z.of_nat (length t) + 1)%Z; (Z.of_nat (length t) + 1)%Z]) (snd (sup_remove_m R1 (atoi_c.atoi_val a))))).
    { cbv beta. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
    assert (HKS : (k1 + length ((fun t : list byte => [(Z.of_nat (length (dec (atoi_c.atoi_val a))) + 1)%Z; (Z.of_nat (length t) + 1)%Z; (Z.of_nat (length t) + 1)%Z]) (snd (sup_remove_m R1 (atoi_c.atoi_val a)))) <= 32)%nat).
    { cbv beta. cbn [length]. lia. }
    pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST1))))) as (RES & _).
    assert (CAP : sb_live (CF.RecKindB.sb_mallocs (sb_n (s_b S) k1) ((fun t : list byte => [(Z.of_nat (length (dec (atoi_c.atoi_val a))) + 1)%Z; (Z.of_nat (length t) + 1)%Z; (Z.of_nat (length t) + 1)%Z]) (snd (sup_remove_m R1 (atoi_c.atoi_val a))))) <=
                  sb_cap (CF.RecKindB.sb_mallocs (sb_n (s_b S) k1) ((fun t : list byte => [(Z.of_nat (length (dec (atoi_c.atoi_val a))) + 1)%Z; (Z.of_nat (length t) + 1)%Z; (Z.of_nat (length t) + 1)%Z]) (snd (sup_remove_m R1 (atoi_c.atoi_val a)))))).
    { destruct (sb_mallocs_fields ((fun t : list byte => [(Z.of_nat (length (dec (atoi_c.atoi_val a))) + 1)%Z; (Z.of_nat (length t) + 1)%Z; (Z.of_nat (length t) + 1)%Z]) (snd (sup_remove_m R1 (atoi_c.atoi_val a)))) (sb_n (s_b S) k1)) as (F1 & _ & F3).
      rewrite F1, F3. pose proof (proj1 (ok_room B API S HS)) as (_ & RC & _).
      unfold sb_n. cbn [sb_live sb_cap] in *. cbv beta. cbn [length]. lia. }
    apply (call_ans B API HF S HS rg' 0x1669c mem2 md1 L1 A1 R1 O1 k1 qv jk _ SUP_REMOVE_K 0x1782c
             ((fun t : list byte => [(Z.of_nat (length (dec (atoi_c.atoi_val a))) + 1)%Z; (Z.of_nat (length t) + 1)%Z; (Z.of_nat (length t) + 1)%Z]) (snd (sup_remove_m R1 (atoi_c.atoi_val a)))) (sup_remove_m R1 (atoi_c.atoi_val a))
             P HST1 E1 KB HKS HSZ).
    + eapply SR_mono.
      { assert (HSZ' : Forall (fun n => 0 <= n <= 8194) [Z.of_nat (length (dec (atoi_c.atoi_val a))) + 1; 17; 17]).
        { repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
        pose proof (st_room B API S HS k1 [Z.of_nat (length (dec (atoi_c.atoi_val a))) + 1; 17; 17] 17
                      ltac:(cbn [length]; lia) HSZ' ltac:(lia)) as ROOM.
        pose proof (DR f L1 A1 rg' mem2 md1 (atoi_c.atoi_val a) R1 O1 (sb_n (s_b S) k1) PRE E10 AR REC RO FZ F18 RES ROOM) as C.
        rewrite SEGS in C. unfold SUP_REMOVE in C. exact C. }
      intros c'' HR. rewrite <- SEGS in HR.
      exact (ans_of_rm B API HF SUP_REMOVE_K (sup_remove_m R1 (atoi_c.atoi_val a))
               (fun t : list byte => [(Z.of_nat (length (dec (atoi_c.atoi_val a))) + 1)%Z; (Z.of_nat (length t) + 1)%Z; (Z.of_nat (length t) + 1)%Z])
               L1 A1 rg' mem2 md1 O1 (sb_n (s_b S) k1) c'' HR CAP).
    + intros f' rg'' mem' md' L' A' O' q c' HST2 E10' HP2.
      apply (join_jump B API HF S HS f' rg R1 k1 qv rg'' 0x1782c 0x178ac mem' md' L' A'
               (fst (sup_remove_m R1 (atoi_c.atoi_val a))) O'
               (k1 + length ((fun t : list byte => [(Z.of_nat (length (dec (atoi_c.atoi_val a))) + 1)%Z; (Z.of_nat (length t) + 1)%Z; (Z.of_nat (length t) + 1)%Z]) (snd (sup_remove_m R1 (atoi_c.atoi_val a)))))
               q (snd (sup_remove_m R1 (atoi_c.atoi_val a))) jk c' P HST2 k_j177d4).
      * exact E10'.
      * exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (PR 18 ltac:(unfold callee_saved; lia))).
      * exact (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (PR 21 ltac:(unfold callee_saved; lia))).
      * rewrite RT, TK. cbn [plan_at]. apply Z.eqb_neq in AV. rewrite AV. unfold VerbsRun.run_step, VerbsRun.run_call.
        destruct (sup_remove_m R1 (atoi_c.atoi_val a)); reflexivity.
      * cbv beta. cbn [length]. lia.
      * exact JOIN.
  - assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    eapply REJ. split; [exact (MK 0x17a88 eq_refl (vregs_pres S rg rg' VR PR))|].
    split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 21 X eq_refl); reflexivity|].
    split; [|lia].
    rewrite RT. destruct (toks D) as [|v [|a [|b r]]] eqn:TK'; cbn [plan_at]; try reflexivity.
    exfalso. apply L2. rewrite ?TK'. reflexivity.
Qed.

End R.

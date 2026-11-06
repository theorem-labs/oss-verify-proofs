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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/verbs_receive_br.v; 168 of its 208 lines of code are new or changed and 179 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_call.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_br sup_worker_env_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma env_len4 : forall {X : Type} (l : list X), length l = 4%nat -> exists v a b e, l = [v; a; b; e].
Proof. intros X [|v [|a [|b [|e [|w r]]]]] H; cbn [length] in H; try lia. exists v, a, b, e. reflexivity. Qed.

Lemma env_k1 : forall (tk : list (list byte))
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p1 p2 p3 : word),
  s5 = verbs_receive_disp.ntokw tk -> (length tk <= 64)%nat -> bv_unsigned sp < 2^63 ->
  (length tk = 4%nat -> bytes_at rsegs m (bv_unsigned sp + 16) (le8 p1)) ->
  (length tk = 4%nat -> bytes_at rsegs m (bv_unsigned sp + 24) (le8 p2)) ->
  (length tk = 4%nat -> bytes_at rsegs m (bv_unsigned sp + 32) (le8 p3)) ->
  evt rsegs (fun ms' =>
      (length tk = 4%nat /\
       ms' = MS (mkR (Z_to_bv 64 0x179e4) sp gp tp t0 t1 t2 s0 s1 p1 p2 p3 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16d94) fc None m (seg_rom rsegs)) \/
      (length tk <> 4%nat /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17a88) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x179ac) fc None m (seg_rom rsegs)).
Proof.
  intros tk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p1 p2 p3 E5 HL HSP HB1 HB2 HB3. subst s5.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64) in RSP.
  do 2 zstep. rewrite verbs_receive_disp.eqb_ntokw by lia.
  destruct (Z.of_nat (length tk) =? 4) eqn:E; cbv beta iota delta [negb].
  - apply Z.eqb_eq in E. assert (L4 : length tk = 4%nat) by lia.
    pose proof (verbs_receive_disp.read_all _ _ _ (HB1 L4)) as RD1. rewrite length_le8 in RD1.
    pose proof (verbs_receive_disp.read_all _ _ _ (HB2 L4)) as RD2. rewrite length_le8 in RD2.
    pose proof (verbs_receive_disp.read_all _ _ _ (HB3 L4)) as RD3. rewrite length_le8 in RD3.
    do 3 zstep. cond_by false.
    do 2 zstep. cond_by false.
    do 3 zstep.
    replace (bv_unsigned sp + 8 <? 18446744073709551592) with true by (symmetry; apply Z.ltb_lt; lia).
    change (Z.lxor (Z.b2z true) 1) with 0. cond_by false.
    do 4 zstep. apply evt_done. left. split; [exact L4 | reflexivity].
  - apply Z.eqb_neq in E. apply evt_done. right. split; [lia | reflexivity].
Qed.

Lemma k_j178e8 : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x178ac) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x179e4) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis DG : forall f : YK11.FPState, @sup_worker_env_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_env : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc REnv) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = REnv -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
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
  assert (R21 : reg_get rg 21 = verbs_receive_disp.ntokw (toks D)) by (rewrite <- N21; reflexivity).
  assert (SPB : bv_unsigned (reg_get rg 2) < 2^63) by (rewrite SP2; unfold s_spf, VR_K in *; lia).
  assert (NL : (length (toks D) <= 64)%nat) by lia.
  set (p1 := nth 1 (s_ps S) (Z_to_bv 64 0)).
  assert (HB1 : length (toks D) = 4%nat -> bytes_at rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 16) (le8 p1)).
  { intros L4. rewrite SP2. apply bytes_at_normalize; [exact RO1|].
    assert (E : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
    pose proof (frame_tok S mem1 jk 1 p1 FR E) as FT.
    replace (s_spf S + 16) with (s_spf S + 8 + 8 * Z.of_nat 1) by lia. exact FT. }
  set (p2 := nth 2 (s_ps S) (Z_to_bv 64 0)).
  assert (HB2 : length (toks D) = 4%nat -> bytes_at rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 24) (le8 p2)).
  { intros L4. rewrite SP2. apply bytes_at_normalize; [exact RO1|].
    assert (E : nth_error (s_ps S) 2 = Some p2) by (unfold p2; apply nth_error_nth'; lia).
    pose proof (frame_tok S mem1 jk 2 p2 FR E) as FT.
    replace (s_spf S + 24) with (s_spf S + 8 + 8 * Z.of_nat 2) by lia. exact FT. }
  set (p3 := nth 3 (s_ps S) (Z_to_bv 64 0)).
  assert (HB3 : length (toks D) = 4%nat -> bytes_at rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 32) (le8 p3)).
  { intros L4. rewrite SP2. apply bytes_at_normalize; [exact RO1|].
    assert (E : nth_error (s_ps S) 3 = Some p3) by (unfold p3; apply nth_error_nth'; lia).
    pose proof (frame_tok S mem1 jk 3 p3 FR E) as FT.
    replace (s_spf S + 32) with (s_spf S + 8 + 8 * Z.of_nat 3) by lia. exact FT. }
  eapply (@ka_nw f _ B API HF S HS rg (route_pc REnv) mem1 md1 L1 A1 R1 O1 k1 qv None jk c _ P HST).
  { unfold Regs6ss.mkR_of. cbn [route_pc]. apply (env_k1 (toks D)) with (p1 := p1) (p2 := p2) (p3 := p3); [exact R21 | exact NL | exact SPB | exact HB1 | exact HB2 | exact HB3]. }
  { intros ms' [(_ & E)|(_ & E)]; subst ms'; do 2 eexists; reflexivity. }
  intros R' pc' rg' mem2 HQ X MK.
  destruct HQ as [(L4 & EQ)|(L4 & EQ)]; injection EQ as ER EP; subst R' pc'.
  - destruct (env_len4 (toks D) L4) as (v & a & b & e & TK).
    assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    pose proof (MK 0x16d94 eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
    assert (E1 : getr rg' 1 = Z_to_bv 64 0x179e4) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
    assert (E10 : getr rg' 10 = Z_to_bv 64 (bv_unsigned p1)).
    { rewrite Z_to_bv_bv_unsigned. rewrite (getr_of_eqv _ _ 10 X eq_refl). reflexivity. }
    assert (E11 : getr rg' 11 = Z_to_bv 64 (bv_unsigned p2)).
    { rewrite Z_to_bv_bv_unsigned. rewrite (getr_of_eqv _ _ 11 X eq_refl). reflexivity. }
    assert (E12 : getr rg' 12 = Z_to_bv 64 (bv_unsigned p3)).
    { rewrite Z_to_bv_bv_unsigned. rewrite (getr_of_eqv _ _ 12 X eq_refl). reflexivity. }
    assert (RET : YK0s.ret_ok (Z_to_bv 64 0x179e4)) by (apply bv_eq; vm_compute; reflexivity).
    assert (KB : 0 <= SUP_WORKER_ENV_K <= 14336) by (unfold SUP_WORKER_ENV_K; lia).
    destruct (vs_pre B API HF S HS rg' 0x16d94 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_WORKER_ENV_K 0x179e4
                HST1 E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
    assert (EP1 : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
    assert (EA1 : nth_error (toks D) 1 = Some a) by (rewrite TK; reflexivity).
    pose proof (st_tok_arg B API HF S HS rg' 0x16d94 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_WORKER_ENV_K 1 p1 a
                  HST1 KB EP1 EA1) as SA1.
    assert (LA1 : Z.of_nat (length a) <= 8192).
    { assert (IA : In a (toks D)) by (rewrite TK; right; left; reflexivity).
      pose proof (verbs_receive_route.toks_len D a IA) as LW.
      pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS). lia. }
    assert (EP2 : nth_error (s_ps S) 2 = Some p2) by (unfold p2; apply nth_error_nth'; lia).
    assert (EA2 : nth_error (toks D) 2 = Some b) by (rewrite TK; reflexivity).
    pose proof (st_tok_arg B API HF S HS rg' 0x16d94 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_WORKER_ENV_K 2 p2 b
                  HST1 KB EP2 EA2) as SA2.
    assert (LA2 : Z.of_nat (length b) <= 8192).
    { assert (IA : In b (toks D)) by (rewrite TK; right; right; left; reflexivity).
      pose proof (verbs_receive_route.toks_len D b IA) as LW.
      pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS). lia. }
    assert (EP3 : nth_error (s_ps S) 3 = Some p3) by (unfold p3; apply nth_error_nth'; lia).
    assert (EA3 : nth_error (toks D) 3 = Some e) by (rewrite TK; reflexivity).
    pose proof (st_tok_arg B API HF S HS rg' 0x16d94 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_WORKER_ENV_K 3 p3 e
                  HST1 KB EP3 EA3) as SA3.
    assert (LA3 : Z.of_nat (length e) <= 8192).
    { assert (IA : In e (toks D)) by (rewrite TK; right; right; right; left; reflexivity).
      pose proof (verbs_receive_route.toks_len D e IA) as LW.
      pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS). lia. }
    assert (LT : (length (snd (sup_worker_env_m R1 (Some a) (Some b) (Some e))) <= 28)%nat).
    { unfold sup_worker_env_m, daemon_shape. apply stub_text_len. exact (rep_code _ _ _ _ _ _ REC). }
    assert (HSZ : Forall (fun n => 0 <= n <= 8194) (sup_worker_env_sizes (Some a) (Some b) (Some e) (snd (sup_worker_env_m R1 (Some a) (Some b) (Some e))))).
    { unfold sup_worker_env_sizes, sarg. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
    assert (HKS : (k1 + length (sup_worker_env_sizes (Some a) (Some b) (Some e) (snd (sup_worker_env_m R1 (Some a) (Some b) (Some e)))) <= 32)%nat).
    { unfold sup_worker_env_sizes. cbn [length]. lia. }
    pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST1))))) as (RES & _).
    pose proof (st_room B API S HS k1 _ (LMAX + 1) HKS HSZ ltac:(unfold LMAX; lia)) as ROOM.
    assert (CAP : sb_live (CF.RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_worker_env_sizes (Some a) (Some b) (Some e) (snd (sup_worker_env_m R1 (Some a) (Some b) (Some e))))) <=
                  sb_cap (CF.RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_worker_env_sizes (Some a) (Some b) (Some e) (snd (sup_worker_env_m R1 (Some a) (Some b) (Some e)))))).
    { destruct (sb_mallocs_fields (sup_worker_env_sizes (Some a) (Some b) (Some e) (snd (sup_worker_env_m R1 (Some a) (Some b) (Some e)))) (sb_n (s_b S) k1)) as (F1 & _ & F3).
      rewrite F1, F3. pose proof (proj1 (ok_room B API S HS)) as (_ & RC & _).
      unfold sb_n. cbn [sb_live sb_cap] in *. unfold sup_worker_env_sizes. cbn [length]. lia. }
    apply (call_ans B API HF S HS rg' 0x16d94 mem2 md1 L1 A1 R1 O1 k1 qv jk _ SUP_WORKER_ENV_K 0x179e4
             (sup_worker_env_sizes (Some a) (Some b) (Some e) (snd (sup_worker_env_m R1 (Some a) (Some b) (Some e)))) (sup_worker_env_m R1 (Some a) (Some b) (Some e))
             P HST1 E1 KB HKS HSZ).
    + eapply SR_mono.
      { pose proof (DG f L1 A1 rg' mem2 md1 (bv_unsigned p1) (bv_unsigned p2) (bv_unsigned p3) (Some a) (Some b) (Some e) R1 O1 (sb_n (s_b S) k1) PRE E10 E11 E12
                      ltac:(rewrite SPR; exact SA1) ltac:(rewrite SPR; exact SA2) ltac:(rewrite SPR; exact SA3) SH REC RO FZ F18 RES ROOM) as C.
        rewrite SEGS in C. unfold SUP_WORKER_ENV in C. exact C. }
      intros c'' HR.
      exact (ans_of B API HF SUP_WORKER_ENV_K (sup_worker_env_m R1 (Some a) (Some b) (Some e)) (sup_worker_env_sizes (Some a) (Some b) (Some e))
               L1 A1 rg' mem2 md1 O1
               (sb_n (s_b S) k1) c'' HR CAP).
    + intros f' rg'' mem' md' L' A' O' q c' HST2 E10' HP2.
      apply (join_jump B API HF S HS f' rg R1 k1 qv rg'' 0x179e4 0x178ac mem' md' L' A'
               (fst (sup_worker_env_m R1 (Some a) (Some b) (Some e))) O'
               (k1 + length (sup_worker_env_sizes (Some a) (Some b) (Some e) (snd (sup_worker_env_m R1 (Some a) (Some b) (Some e)))))
               q (snd (sup_worker_env_m R1 (Some a) (Some b) (Some e))) jk c' P HST2 k_j178e8).
      * exact E10'.
      * exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (PR 18 ltac:(unfold callee_saved; lia))).
      * exact (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (PR 21 ltac:(unfold callee_saved; lia))).
      * rewrite RT, TK. cbn [plan_at]. unfold VerbsRun.run_step, VerbsRun.run_call.
        destruct (sup_worker_env_m R1 (Some a) (Some b) (Some e)); reflexivity.
      * unfold sup_worker_env_sizes. cbn [length]. lia.
      * exact JOIN.
  - assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    eapply REJ. split; [exact (MK 0x17a88 eq_refl (vregs_pres S rg rg' VR PR))|].
    split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 21 X eq_refl); reflexivity|].
    split; [|lia].
    rewrite RT. destruct (toks D) as [|v [|a [|b [|e [|w r]]]]] eqn:TK'; cbn [plan_at]; try reflexivity.
    exfalso. apply L4. rewrite ?TK'. reflexivity.
Qed.

End R.

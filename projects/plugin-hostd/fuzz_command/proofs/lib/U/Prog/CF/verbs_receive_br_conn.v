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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/verbs_receive_br.v; 144 of its 191 lines of code are new or changed and 172 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_br verbs_receive_br2 sup_connect_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma conn_text_len : forall R fn As ch, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_stub R fn As REC_MOD_HOST_SHAPE ch)) <= 28)%nat.
Proof.
  intros R fn As ch HC. unfold rec_stub. rewrite rec_answer_text.
  assert (E : r_code (rec_record R fn As) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
  destruct (r_refuse (rec_record R fn As) =? 0).
  - apply Nat.leb_le. vm_compute. reflexivity.
  - rewrite E. pose proof (resp_length (r_code R) HC). lia.
Qed.

Lemma conn_toks : forall tk, route tk = RConn -> exists v a b, tk = [v; a; b].
Proof.
  intros [|v args] H; [discriminate H|].
  unfold route, route_mid, route_tail, route_conn, route_cd in H.
  destruct (ledger_of v instance_info_verbs);
    [repeat match type of H with context [if ?b then _ else _] => destruct b end; discriminate H|].
  destruct args as [|a [|b [|e r]]];
    repeat match type of H with context [if ?b then _ else _] => destruct b end; try discriminate H.
  exists v, a, b. reflexivity.
Qed.

Lemma conn_k1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p1 p2 : word),
  bv_unsigned sp < 2^63 -> bytes_at rsegs m (bv_unsigned sp + 16) (le8 p1) ->
  bytes_at rsegs m (bv_unsigned sp + 24) (le8 p2) ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17c24) sp gp tp t0 t1 t2 s0 s1 s4 s0 p1 p2 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16730) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17bf8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 HSP HB1 HB2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64) in RSP.
  pose proof (verbs_receive_disp.read_all _ _ _ HB1) as RD1. rewrite length_le8 in RD1.
  pose proof (verbs_receive_disp.read_all _ _ _ HB2) as RD2. rewrite length_le8 in RD2.
  do 3 zstep. cond_by false. do 3 zstep.
  replace (bv_unsigned sp + 8 <? 18446744073709551600) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [Z.b2z]. change (Z.lxor 1 1) with 0. cond_by false.
  do 5 zstep. apply evt_done. reflexivity.
Qed.

Lemma k_j17ad4 : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x178ac) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x17c24) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis DG : forall f : YK11.FPState, @sup_connect_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_conn : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc RConn) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RConn -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  getr rg 20 = nth 0 (s_ps S) (Z_to_bv 64 0) ->
  join_k B API S 0x178ac 10 rg R1 k1 qv P ->
  SR rsegs c P.
Proof.
  intros f rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST RT N21 HK H20 JOIN.
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
  destruct (conn_toks (toks D) RT) as (v & a & b & TK).
  assert (L3 : length (toks D) = 3%nat) by (rewrite TK; reflexivity).
  set (p0 := nth 0 (s_ps S) (Z_to_bv 64 0)).
  set (p1 := nth 1 (s_ps S) (Z_to_bv 64 0)).
  set (p2 := nth 2 (s_ps S) (Z_to_bv 64 0)).
  assert (EP0 : nth_error (s_ps S) 0 = Some p0) by (unfold p0; apply nth_error_nth'; lia).
  assert (EP1 : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
  assert (EP2 : nth_error (s_ps S) 2 = Some p2) by (unfold p2; apply nth_error_nth'; lia).
  assert (HB1 : bytes_at rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 16) (le8 p1)).
  { rewrite SP2. apply bytes_at_normalize; [exact RO1|].
    pose proof (frame_tok S mem1 jk 1 p1 FR EP1) as FT.
    replace (s_spf S + 16) with (s_spf S + 8 + 8 * Z.of_nat 1) by lia. exact FT. }
  assert (HB2 : bytes_at rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 24) (le8 p2)).
  { rewrite SP2. apply bytes_at_normalize; [exact RO1|].
    pose proof (frame_tok S mem1 jk 2 p2 FR EP2) as FT.
    replace (s_spf S + 24) with (s_spf S + 8 + 8 * Z.of_nat 2) by lia. exact FT. }
  eapply (@ka_nw f _ B API HF S HS rg (route_pc RConn) mem1 md1 L1 A1 R1 O1 k1 qv None jk c _ P HST).
  { unfold Regs6ss.mkR_of. cbn [route_pc]. apply conn_k1 with (p1 := p1) (p2 := p2);
      [exact SPB | exact HB1 | exact HB2]. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 HQ X MK. cbv beta in HQ. injection HQ as ER EP. subst R' pc'.
  - assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    pose proof (MK 0x16730 eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
    assert (E1 : getr rg' 1 = Z_to_bv 64 0x17c24) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
    assert (G10 : getr rg' 10 = getr rg 20) by (rewrite (getr_of_eqv _ _ 10 X eq_refl); reflexivity).
    assert (G11 : getr rg' 11 = getr rg 8) by (rewrite (getr_of_eqv _ _ 11 X eq_refl); reflexivity).
    assert (E10 : getr rg' 10 = Z_to_bv 64 (bv_unsigned p0)) by (rewrite Z_to_bv_bv_unsigned, G10; exact H20).
    assert (E11 : getr rg' 11 = Z_to_bv 64 (s_lb S)).
    { rewrite G11. destruct VR as (_ & _ & _ & V8 & _). exact V8. }
    assert (E12 : getr rg' 12 = Z_to_bv 64 (bv_unsigned p1)).
    { rewrite Z_to_bv_bv_unsigned. rewrite (getr_of_eqv _ _ 12 X eq_refl). reflexivity. }
    assert (E13 : getr rg' 13 = Z_to_bv 64 (bv_unsigned p2)).
    { rewrite Z_to_bv_bv_unsigned. rewrite (getr_of_eqv _ _ 13 X eq_refl). reflexivity. }
    assert (RET : YK0s.ret_ok (Z_to_bv 64 0x17c24)) by (apply bv_eq; vm_compute; reflexivity).
    assert (KB : 0 <= SUP_CONNECT_K <= 14336) by (unfold SUP_CONNECT_K; lia).
    destruct (vs_pre B API HF S HS rg' 0x16730 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_CONNECT_K 0x17c24
                HST1 E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
    assert (EA0 : nth_error (toks D) 0 = Some v) by (rewrite TK; reflexivity).
    assert (EA1 : nth_error (toks D) 1 = Some a) by (rewrite TK; reflexivity).
    assert (EA2 : nth_error (toks D) 2 = Some b) by (rewrite TK; reflexivity).
    pose proof (st_tok_arg B API HF S HS rg' 0x16730 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_CONNECT_K 0 p0 v HST1 KB EP0 EA0) as SA0.
    pose proof (st_tok_arg B API HF S HS rg' 0x16730 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_CONNECT_K 1 p1 a HST1 KB EP1 EA1) as SA1.
    pose proof (st_tok_arg B API HF S HS rg' 0x16730 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_CONNECT_K 2 p2 b HST1 KB EP2 EA2) as SA2.
    pose proof (st_line_arg B API HF S HS rg' 0x16730 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_CONNECT_K HST1 KB) as SL.
    pose proof (ok_nD B API S HS) as OND. pose proof (ok_n8 B API S HS) as ON8.
    assert (LL : Z.of_nat (length (line D)) <= 8192) by (pose proof (verbs_receive_route.line_len D); lia).
    assert (LV : Z.of_nat (length v) <= 8192).
    { pose proof (verbs_receive_route.toks_len D v ltac:(rewrite TK; left; reflexivity)). lia. }
    assert (LA : Z.of_nat (length a) <= 8192).
    { pose proof (verbs_receive_route.toks_len D a ltac:(rewrite TK; right; left; reflexivity)). lia. }
    assert (LB : Z.of_nat (length b) <= 8192).
    { pose proof (verbs_receive_route.toks_len D b ltac:(rewrite TK; right; right; left; reflexivity)). lia. }
    assert (LT : (length (snd (sup_connect_m R1 (Some v) (line D) (Some a) (Some b))) <= 28)%nat).
    { unfold sup_connect_m. apply conn_text_len. exact (rep_code _ _ _ _ _ _ REC). }
    assert (HSZ : Forall (fun n => 0 <= n <= 8194) (sup_connect_sizes (Some v) (line D) (Some a) (Some b) (snd (sup_connect_m R1 (Some v) (line D) (Some a) (Some b))))).
    { unfold sup_connect_sizes, sarg. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
    assert (HKS : (k1 + length (sup_connect_sizes (Some v) (line D) (Some a) (Some b) (snd (sup_connect_m R1 (Some v) (line D) (Some a) (Some b)))) <= 32)%nat).
    { unfold sup_connect_sizes, sarg. cbn [length]. lia. }
    pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST1))))) as (RES & _).
    pose proof (st_room B API S HS k1 _ (LMAX + 1) HKS HSZ ltac:(unfold LMAX; lia)) as ROOM.
    assert (CAP : sb_live (CF.RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_connect_sizes (Some v) (line D) (Some a) (Some b) (snd (sup_connect_m R1 (Some v) (line D) (Some a) (Some b))))) <=
                  sb_cap (CF.RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_connect_sizes (Some v) (line D) (Some a) (Some b) (snd (sup_connect_m R1 (Some v) (line D) (Some a) (Some b)))))).
    { destruct (sb_mallocs_fields (sup_connect_sizes (Some v) (line D) (Some a) (Some b) (snd (sup_connect_m R1 (Some v) (line D) (Some a) (Some b)))) (sb_n (s_b S) k1)) as (F1 & _ & F3).
      rewrite F1, F3. pose proof (proj1 (ok_room B API S HS)) as (_ & RC & _).
      unfold sb_n. cbn [sb_live sb_cap] in *. unfold sup_connect_sizes, sarg. cbn [length]. lia. }
    apply (call_ans B API HF S HS rg' 0x16730 mem2 md1 L1 A1 R1 O1 k1 qv jk _ SUP_CONNECT_K 0x17c24
             (sup_connect_sizes (Some v) (line D) (Some a) (Some b) (snd (sup_connect_m R1 (Some v) (line D) (Some a) (Some b)))) (sup_connect_m R1 (Some v) (line D) (Some a) (Some b))
             P HST1 E1 KB HKS HSZ).
    + eapply SR_mono.
      { pose proof (DG f L1 A1 rg' mem2 md1 (bv_unsigned p0) (s_lb S) (bv_unsigned p1) (bv_unsigned p2)
                      (Some v) (line D) (Some a) (Some b) R1 O1 (sb_n (s_b S) k1) PRE E10 E11 E12 E13
                      ltac:(rewrite SPR; exact SA0) ltac:(rewrite SPR; exact SL) ltac:(rewrite SPR; exact SA1)
                      ltac:(rewrite SPR; exact SA2) REC RO FZ F18 RES ROOM) as C.
        rewrite SEGS in C. unfold SUP_CONNECT in C. exact C. }
      intros c'' HR.
      exact (ans_of_ns B API HF SUP_CONNECT_K (sup_connect_m R1 (Some v) (line D) (Some a) (Some b)) (sup_connect_sizes (Some v) (line D) (Some a) (Some b)) L1 A1 rg' mem2 md1 O1 (sb_n (s_b S) k1) c'' HR CAP).
    + intros f' rg'' mem' md' L' A' O' q c' HST2 E10' HP2.
      apply (join_jump B API HF S HS f' rg R1 k1 qv rg'' 0x17c24 0x178ac mem' md' L' A'
               (fst (sup_connect_m R1 (Some v) (line D) (Some a) (Some b))) O'
               (k1 + length (sup_connect_sizes (Some v) (line D) (Some a) (Some b) (snd (sup_connect_m R1 (Some v) (line D) (Some a) (Some b)))))
               q (snd (sup_connect_m R1 (Some v) (line D) (Some a) (Some b))) jk c' P HST2 k_j17ad4).
      * exact E10'.
      * exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (PR 18 ltac:(unfold callee_saved; lia))).
      * exact (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (PR 21 ltac:(unfold callee_saved; lia))).
      * rewrite RT, TK. cbn [plan_at]. unfold VerbsRun.run_step, VerbsRun.run_call.
        destruct (sup_connect_m R1 (Some v) (line D) (Some a) (Some b)); reflexivity.
      * unfold sup_connect_sizes, sarg. cbn [length]. lia.
      * exact JOIN.
Qed.

End R.

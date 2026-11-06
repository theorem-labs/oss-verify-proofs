(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/verbs_receive_br.v; 103 of its 139 lines of code are new or changed and 179 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br verbs_receive_br2 sup_worker_list_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma wlist_k1 : forall (tk : list (list byte)) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  s5 = verbs_receive_disp.ntokw tk -> (length tk <= 64)%nat ->
  evt rsegs (fun ms' =>
      (length tk = 1%nat /\
       ms' = MS (mkR (Z_to_bv 64 0x17798) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16a64) fc None m (seg_rom rsegs)) \/
      (length tk <> 1%nat /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x178a4) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1778c) fc None m (seg_rom rsegs)).
Proof.
  intros tk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m E5 HL. subst s5.
  do 2 zstep. rewrite verbs_receive_disp.eqb_ntokw by lia.
  destruct (Z.of_nat (length tk) =? 1) eqn:E; cbv beta iota delta [negb].
  - apply Z.eqb_eq in E. assert (L1 : length tk = 1%nat) by lia.
    zstep. apply evt_done. left. split; [exact L1 | reflexivity].
  - apply Z.eqb_neq in E. apply evt_done. right. split; [lia | reflexivity].
Qed.

Lemma k_j17778 : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x176c4) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x17798) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis DG : forall f : YK11.FPState, @sup_worker_list_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_wlist : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc RWlist) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RWlist -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  join_k B API S 0x176c4 10 rg R1 k1 qv P ->
  rej_k B API S f 0x178a4 rg R1 k1 qv P ->
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
  assert (NL : (length (toks D) <= 64)%nat) by lia.
  eapply (@ka_nw f _ B API HF S HS rg (route_pc RWlist) mem1 md1 L1 A1 R1 O1 k1 qv None jk c _ P HST).
  { unfold Regs6ss.mkR_of. cbn [route_pc]. apply (wlist_k1 (toks D)); [exact R21 | exact NL]. }
  { intros ms' [(_ & E)|(_ & E)]; subst ms'; do 2 eexists; reflexivity. }
  intros R' pc' rg' mem2 HQ X MK.
  destruct HQ as [(L1' & EQ)|(L1' & EQ)]; injection EQ as ER EP; subst R' pc'.
  - assert (TK : exists v, toks D = [v]) by (destruct (toks D) as [|v [|w r]]; cbn [length] in L1'; try lia; exists v; reflexivity).
    destruct TK as (v & TK).
    assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    pose proof (MK 0x16a64 eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
    assert (E1 : getr rg' 1 = Z_to_bv 64 0x17798) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
    assert (RET : YK0s.ret_ok (Z_to_bv 64 0x17798)) by (apply bv_eq; vm_compute; reflexivity).
    assert (KB : 0 <= SUP_WORKER_LIST_K <= 14336) by (unfold SUP_WORKER_LIST_K; lia).
    destruct (vs_pre B API HF S HS rg' 0x16a64 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_WORKER_LIST_K 0x17798
                HST1 E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
    assert (LT : (length (snd (sup_worker_list_m R1)) <= 28)%nat).
    { unfold sup_worker_list_m, daemon_shape. apply stub_text_len. exact (rep_code _ _ _ _ _ _ REC). }
    assert (HSZ : Forall (fun n => 0 <= n <= 8194) (sup_worker_list_sizes (snd (sup_worker_list_m R1)))).
    { unfold sup_worker_list_sizes. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
    assert (HKS : (k1 + length (sup_worker_list_sizes (snd (sup_worker_list_m R1))) <= 32)%nat).
    { unfold sup_worker_list_sizes. cbn [length]. lia. }
    pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST1))))) as (RES & _).
    pose proof (st_room B API S HS k1 _ 25 HKS HSZ ltac:(unfold LMAX; lia)) as ROOM.
    assert (CAP : sb_live (RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_worker_list_sizes (snd (sup_worker_list_m R1)))) <=
                  sb_cap (RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_worker_list_sizes (snd (sup_worker_list_m R1))))).
    { destruct (sb_mallocs_fields (sup_worker_list_sizes (snd (sup_worker_list_m R1))) (sb_n (s_b S) k1)) as (F1 & _ & F3).
      rewrite F1, F3. pose proof (ok_room B API S HS) as (_ & RC & _).
      unfold sb_n. cbn [sb_live sb_cap] in *. unfold sup_worker_list_sizes. cbn [length]. lia. }
    apply (call_ans B API HF S HS rg' 0x16a64 mem2 md1 L1 A1 R1 O1 k1 qv jk _ SUP_WORKER_LIST_K 0x17798
             (sup_worker_list_sizes (snd (sup_worker_list_m R1))) (sup_worker_list_m R1)
             P HST1 E1 KB HKS HSZ).
    + eapply SR_mono.
      { pose proof (DG f L1 A1 rg' mem2 md1 R1 O1 (sb_n (s_b S) k1) PRE SH REC RO FZ F18 RES ROOM) as C.
        rewrite SEGS in C. unfold SUP_WORKER_LIST in C. exact C. }
      intros c'' HR.
      exact (ans_of B API HF SUP_WORKER_LIST_K (sup_worker_list_m R1) sup_worker_list_sizes L1 A1 rg' mem2 md1 O1 (sb_n (s_b S) k1) c'' HR CAP).
    + intros f' rg'' mem' md' L' A' O' q c' HST2 E10' HP2.
      apply (join_jump B API HF S HS f' rg R1 k1 qv rg'' 0x17798 0x176c4 mem' md' L' A'
               (fst (sup_worker_list_m R1)) O'
               (k1 + length (sup_worker_list_sizes (snd (sup_worker_list_m R1))))
               q (snd (sup_worker_list_m R1)) jk c' P HST2 k_j17778).
      * exact E10'.
      * exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (PR 18 ltac:(unfold callee_saved; lia))).
      * exact (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (PR 21 ltac:(unfold callee_saved; lia))).
      * rewrite RT, TK. cbn [plan_at]. unfold VerbsRun.run_step, VerbsRun.run_call.
        destruct (sup_worker_list_m R1); reflexivity.
      * unfold sup_worker_list_sizes. cbn [length]. lia.
      * exact JOIN.
  - assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    eapply REJ. split; [exact (MK 0x178a4 eq_refl (vregs_pres S rg rg' VR PR))|].
    split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 21 X eq_refl); reflexivity|].
    split; [|lia].
    rewrite RT. destruct (toks D) as [|v [|a r]] eqn:TK'; cbn [plan_at]; try reflexivity.
    exfalso. apply L1'. rewrite ?TK'. reflexivity.
Qed.

End R.

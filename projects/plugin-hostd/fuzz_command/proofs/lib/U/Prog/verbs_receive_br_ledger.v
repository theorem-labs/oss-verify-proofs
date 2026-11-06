(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/verbs_receive_br.v; 105 of its 143 lines of code are new or changed and 177 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br verbs_receive_br2 sup_instance_verb_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ledger_in : forall v tbl led, ledger_of v tbl = Some led -> In led (map snd tbl).
Proof.
  intros v tbl; induction tbl as [|[nm l] tbl IH]; intros led H; cbn [ledger_of] in H; [discriminate H|].
  cbn [map snd]. destruct (list_eqb v nm); [injection H as <-; left; reflexivity | right; exact (IH led H)].
Qed.

Lemma ledger_route : forall tk led, route tk = RLedger led -> -2^31 <= led < 2^31.
Proof.
  intros [|v args] led H; [discriminate H|].
  unfold route, route_mid, route_tail in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end; try discriminate H.
  destruct (ledger_of v instance_info_verbs) as [l|] eqn:EL.
  - injection H as <-. apply ledger_in in EL. cbv [map snd instance_info_verbs In] in EL.
    repeat (destruct EL as [<-|EL]; [unfold ledger_replace, ledger_none; lia|]). destruct EL.
  - unfold route_conn, route_cd in H. destruct args as [|a [|b [|e r]]];
      repeat match type of H with context [if ?b then _ else _] => destruct b end; discriminate H.
Qed.

Lemma ledger_k1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17bb8) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x169a0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17bb4) fc None m (seg_rom rsegs)).
Proof. intros. zstep. apply evt_done. reflexivity. Qed.

Lemma k_j17a80 : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x17a90) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x17bb8) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis DG : forall f : YK11.FPState, @sup_instance_verb_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_ledger : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P led,
  @vr_state f _ B API S rg (route_pc (RLedger led)) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RLedger led -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  getr rg 10 = getr rg 8 -> getr rg 11 = Z_to_bv 64 led ->
  join_k B API S 0x17a90 10 rg R1 k1 qv P ->
  SR rsegs c P.
Proof.
  intros f rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P led HST RT N21 HK H10 H11 JOIN.
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
  pose proof (ledger_route (toks D) led RT) as LR.
  assert (NE : exists v args, toks D = v :: args)
    by (destruct (toks D) as [|v args]; [discriminate RT | exists v, args; reflexivity]).
  destruct NE as (v & args & TK).
  eapply (@ka_nw f _ B API HF S HS rg (route_pc (RLedger led)) mem1 md1 L1 A1 R1 O1 k1 qv None jk c _ P HST).
  { unfold Regs6ss.mkR_of. cbn [route_pc]. apply ledger_k1. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 HQ X MK. cbv beta in HQ. injection HQ as ER EP. subst R' pc'.
  - assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    pose proof (MK 0x169a0 eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
    assert (E1 : getr rg' 1 = Z_to_bv 64 0x17bb8) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
    assert (G10 : getr rg' 10 = getr rg 10) by (rewrite (getr_of_eqv _ _ 10 X eq_refl); reflexivity).
    assert (G11 : getr rg' 11 = getr rg 11) by (rewrite (getr_of_eqv _ _ 11 X eq_refl); reflexivity).
    assert (E10 : getr rg' 10 = Z_to_bv 64 (s_lb S)).
    { rewrite G10, H10. destruct VR as (_ & _ & _ & V8 & _). exact V8. }
    assert (E11 : getr rg' 11 = Z_to_bv 64 led) by (rewrite G11; exact H11).
    pose proof (dec_length _ LR) as DL.
    assert (RET : YK0s.ret_ok (Z_to_bv 64 0x17bb8)) by (apply bv_eq; vm_compute; reflexivity).
    assert (KB : 0 <= SUP_INSTANCE_VERB_K <= 14336) by (unfold SUP_INSTANCE_VERB_K; lia).
    destruct (vs_pre B API HF S HS rg' 0x169a0 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_INSTANCE_VERB_K 0x17bb8
                HST1 E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
    pose proof (st_line_arg B API HF S HS rg' 0x169a0 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_INSTANCE_VERB_K HST1 KB) as SL.
    assert (LL : Z.of_nat (length (line D)) <= 8192).
    { pose proof (verbs_receive_route.line_len D) as LW.
      pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS). lia. }
    assert (LT : (length (snd (sup_instance_verb_m R1 (line D) led)) <= 28)%nat).
    { unfold sup_instance_verb_m. apply stub_text_len. exact (rep_code _ _ _ _ _ _ REC). }
    assert (HSZ : Forall (fun n => 0 <= n <= 8194) (sup_instance_verb_sizes (line D) led (snd (sup_instance_verb_m R1 (line D) led)))).
    { unfold sup_instance_verb_sizes. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
    assert (HKS : (k1 + length (sup_instance_verb_sizes (line D) led (snd (sup_instance_verb_m R1 (line D) led))) <= 32)%nat).
    { unfold sup_instance_verb_sizes. cbn [length]. lia. }
    pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST1))))) as (RES & _).
    pose proof (st_room B API S HS k1 _ (LMAX + 1) HKS HSZ ltac:(unfold LMAX; lia)) as ROOM.
    assert (CAP : sb_live (RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_instance_verb_sizes (line D) led (snd (sup_instance_verb_m R1 (line D) led)))) <=
                  sb_cap (RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_instance_verb_sizes (line D) led (snd (sup_instance_verb_m R1 (line D) led))))).
    { destruct (sb_mallocs_fields (sup_instance_verb_sizes (line D) led (snd (sup_instance_verb_m R1 (line D) led))) (sb_n (s_b S) k1)) as (F1 & _ & F3).
      rewrite F1, F3. pose proof (ok_room B API S HS) as (_ & RC & _).
      unfold sb_n. cbn [sb_live sb_cap] in *. unfold sup_instance_verb_sizes. cbn [length]. lia. }
    apply (call_ans B API HF S HS rg' 0x169a0 mem2 md1 L1 A1 R1 O1 k1 qv jk _ SUP_INSTANCE_VERB_K 0x17bb8
             (sup_instance_verb_sizes (line D) led (snd (sup_instance_verb_m R1 (line D) led))) (sup_instance_verb_m R1 (line D) led)
             P HST1 E1 KB HKS HSZ).
    + eapply SR_mono.
      { pose proof (DG f L1 A1 rg' mem2 md1 (s_lb S) led (line D) R1 O1 (sb_n (s_b S) k1) PRE E10 E11 LR
                      ltac:(rewrite SPR; exact SL) SH REC RO FZ F18 RES ROOM) as C.
        rewrite SEGS in C. unfold SUP_INSTANCE_VERB in C. exact C. }
      intros c'' HR.
      exact (ans_of B API HF SUP_INSTANCE_VERB_K (sup_instance_verb_m R1 (line D) led) (sup_instance_verb_sizes (line D) led) L1 A1 rg' mem2 md1 O1 (sb_n (s_b S) k1) c'' HR CAP).
    + intros f' rg'' mem' md' L' A' O' q c' HST2 E10' HP2.
      apply (join_jump B API HF S HS f' rg R1 k1 qv rg'' 0x17bb8 0x17a90 mem' md' L' A'
               (fst (sup_instance_verb_m R1 (line D) led)) O'
               (k1 + length (sup_instance_verb_sizes (line D) led (snd (sup_instance_verb_m R1 (line D) led))))
               q (snd (sup_instance_verb_m R1 (line D) led)) jk c' P HST2 k_j17a80).
      * exact E10'.
      * exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (PR 18 ltac:(unfold callee_saved; lia))).
      * exact (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (PR 21 ltac:(unfold callee_saved; lia))).
      * rewrite RT, TK. cbn [plan_at]. unfold VerbsRun.run_step, VerbsRun.run_call.
        destruct (sup_instance_verb_m R1 (line D) led); reflexivity.
      * unfold sup_instance_verb_sizes. cbn [length]. lia.
      * exact JOIN.
Qed.

End R.

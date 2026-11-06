From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_br sup_pin_accept_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pinacc_k1 : forall (tk : list (list byte))
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p1 : word),
  s5 = verbs_receive_disp.ntokw tk -> (length tk <= 64)%nat ->
  (length tk = 2%nat -> bytes_at rsegs m (bv_unsigned sp + 16) (le8 p1)) ->
  evt rsegs (fun ms' =>
      (length tk = 2%nat /\
       ms' = MS (mkR (Z_to_bv 64 0x17944) sp gp tp t0 t1 t2 s0 s1 p1 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16784) fc None m (seg_rom rsegs)) \/
      (length tk <> 2%nat /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17968) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17934) fc None m (seg_rom rsegs)).
Proof.
  intros tk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p1 E5 HL HB. subst s5.
  do 2 zstep. rewrite verbs_receive_disp.eqb_ntokw by lia.
  destruct (Z.of_nat (length tk) =? 2) eqn:E; cbv beta iota delta [negb].
  - apply Z.eqb_eq in E. assert (L2 : length tk = 2%nat) by lia.
    pose proof (verbs_receive_disp.read_all _ _ _ (HB L2)) as RD. rewrite length_le8 in RD.
    do 2 zstep. apply evt_done. left. split; [exact L2 | reflexivity].
  - apply Z.eqb_neq in E. apply evt_done. right. split; [lia | reflexivity].
Qed.

Lemma k_j17944 : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x17830) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x17944) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis DG : forall f : YK11.FPState, @sup_pin_accept_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_pinacc : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc RPinacc) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RPinacc -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  join_k B API S 0x17830 10 rg R1 k1 qv P ->
  rej_k B API S f 0x17968 rg R1 k1 qv P ->
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
  set (p1 := nth 1 (s_ps S) (Z_to_bv 64 0)).
  assert (HB : length (toks D) = 2%nat -> bytes_at rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 16) (le8 p1)).
  { intros L2. rewrite SP2. apply bytes_at_normalize; [exact RO1|].
    assert (E : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
    pose proof (frame_tok S mem1 jk 1 p1 FR E) as FT.
    replace (s_spf S + 16) with (s_spf S + 8 + 8 * Z.of_nat 1) by lia. exact FT. }
  eapply (@ka_nw f _ B API HF S HS rg (route_pc RPinacc) mem1 md1 L1 A1 R1 O1 k1 qv None jk c _ P HST).
  { unfold Regs6ss.mkR_of. cbn [route_pc]. apply (pinacc_k1 (toks D)) with (p1 := p1); [exact R21 | exact NL | exact HB]. }
  { intros ms' [(_ & E)|(_ & E)]; subst ms'; do 2 eexists; reflexivity. }
  intros R' pc' rg' mem2 HQ X MK.
  destruct HQ as [(L2 & EQ)|(L2 & EQ)]; injection EQ as ER EP; subst R' pc'.
  - destruct (len2 (toks D) L2) as (v & a & TK).
    assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    pose proof (MK 0x16784 eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
    assert (E1 : getr rg' 1 = Z_to_bv 64 0x17944) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
    assert (E10 : getr rg' 10 = Z_to_bv 64 (bv_unsigned p1)).
    { rewrite Z_to_bv_bv_unsigned. rewrite (getr_of_eqv _ _ 10 X eq_refl). reflexivity. }
    assert (RET : YK0s.ret_ok (Z_to_bv 64 0x17944)) by (apply bv_eq; vm_compute; reflexivity).
    assert (KB : 0 <= SUP_PIN_ACCEPT_K <= 14336) by (unfold SUP_PIN_ACCEPT_K; lia).
    destruct (vs_pre B API HF S HS rg' 0x16784 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_PIN_ACCEPT_K 0x17944
                HST1 E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
    assert (EP1 : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
    assert (EA : nth_error (toks D) 1 = Some a) by (rewrite TK; reflexivity).
    pose proof (st_tok_arg B API HF S HS rg' 0x16784 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_PIN_ACCEPT_K 1 p1 a
                  HST1 KB EP1 EA) as SA.
    assert (LA : Z.of_nat (length a) <= 8192).
    { assert (IA : In a (toks D)) by (rewrite TK; right; left; reflexivity).
      pose proof (verbs_receive_route.toks_len D a IA) as LW.
      pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS). lia. }
    assert (LT : (length (snd (sup_pin_accept_m R1 (Some a))) <= 28)%nat).
    { unfold sup_pin_accept_m, daemon_shape. apply stub_text_len. exact (rep_code _ _ _ _ _ _ REC). }
    assert (HSZ : Forall (fun n => 0 <= n <= 8194) (sup_pin_accept_sizes (Some a) (snd (sup_pin_accept_m R1 (Some a))))).
    { unfold sup_pin_accept_sizes, sarg. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
    assert (HKS : (k1 + length (sup_pin_accept_sizes (Some a) (snd (sup_pin_accept_m R1 (Some a)))) <= 32)%nat).
    { unfold sup_pin_accept_sizes. cbn [length]. lia. }
    pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST1))))) as (RES & _).
    pose proof (st_room B API S HS k1 _ (LMAX + 1) HKS HSZ ltac:(unfold LMAX; lia)) as ROOM.
    assert (CAP : sb_live (RecKindB.sb_mallocs (sb_n (s_b S) k1)
                    (sup_pin_accept_sizes (Some a) (snd (sup_pin_accept_m R1 (Some a))))) <=
                  sb_cap (RecKindB.sb_mallocs (sb_n (s_b S) k1)
                    (sup_pin_accept_sizes (Some a) (snd (sup_pin_accept_m R1 (Some a)))))).
    { destruct (sb_mallocs_fields (sup_pin_accept_sizes (Some a) (snd (sup_pin_accept_m R1 (Some a))))
                  (sb_n (s_b S) k1)) as (F1 & _ & F3).
      rewrite F1, F3. pose proof (ok_room B API S HS) as (_ & RC & _).
      unfold sb_n. cbn [sb_live sb_cap] in *. unfold sup_pin_accept_sizes. cbn [length]. lia. }
    apply (call_ans B API HF S HS rg' 0x16784 mem2 md1 L1 A1 R1 O1 k1 qv jk _ SUP_PIN_ACCEPT_K 0x17944
             (sup_pin_accept_sizes (Some a) (snd (sup_pin_accept_m R1 (Some a)))) (sup_pin_accept_m R1 (Some a))
             P HST1 E1 KB HKS HSZ).
    + eapply SR_mono.
      { pose proof (DG f L1 A1 rg' mem2 md1 (bv_unsigned p1) (Some a) R1 O1 (sb_n (s_b S) k1) PRE E10
                      ltac:(rewrite SPR; exact SA) SH REC RO FZ F18 RES ROOM) as C.
        rewrite SEGS in C. unfold SUP_PIN_ACCEPT in C. exact C. }
      intros c'' HR.
      exact (ans_of B API HF SUP_PIN_ACCEPT_K (sup_pin_accept_m R1 (Some a)) (sup_pin_accept_sizes (Some a))
               L1 A1 rg' mem2 md1 O1
               (sb_n (s_b S) k1) c'' HR CAP).
    + intros f' rg'' mem' md' L' A' O' q c' HST2 E10' HP2.
      apply (join_jump B API HF S HS f' rg R1 k1 qv rg'' 0x17944 0x17830 mem' md' L' A'
               (fst (sup_pin_accept_m R1 (Some a))) O'
               (k1 + length (sup_pin_accept_sizes (Some a) (snd (sup_pin_accept_m R1 (Some a)))))
               q (snd (sup_pin_accept_m R1 (Some a))) jk c' P HST2 k_j17944).
      * exact E10'.
      * exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (PR 18 ltac:(unfold callee_saved; lia))).
      * exact (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (PR 21 ltac:(unfold callee_saved; lia))).
      * rewrite RT, TK. cbn [plan_at]. unfold VerbsRun.run_step, VerbsRun.run_call.
        destruct (sup_pin_accept_m R1 (Some a)); reflexivity.
      * unfold sup_pin_accept_sizes. cbn [length]. lia.
      * exact JOIN.
  - assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    eapply REJ. split; [exact (MK 0x17968 eq_refl (vregs_pres S rg rg' VR PR))|].
    split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 21 X eq_refl); reflexivity|].
    split; [|lia].
    rewrite RT. destruct (toks D) as [|v [|a [|b r]]] eqn:TK'; cbn [plan_at]; try reflexivity.
    exfalso. apply L2. rewrite ?TK'. reflexivity.
Qed.

End R.

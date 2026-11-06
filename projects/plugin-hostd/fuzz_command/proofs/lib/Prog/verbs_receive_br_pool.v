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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun CTypeFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_br verbs_receive_br2 sup_pool_config_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pool_acc_range : forall s n, -2^31 <= n < 2^31 -> -2^31 <= atoi_c.atoi_acc n s < 2^31.
Proof.
  induction s as [|b s IH]; intros n Hn; cbn [atoi_c.atoi_acc]; [exact Hn|].
  match goal with |- context [if ?d then _ else _] => destruct d end; [apply IH, CTypeFacts.swrap32_range | exact Hn].
Qed.

Lemma pool_atoi_range : forall s, -2^31 <= atoi_c.atoi_val s < 2^31.
Proof.
  intros s. unfold atoi_c.atoi_val.
  match goal with |- context [match ?x with [] => _ | _ :: _ => _ end] => destruct x as [|b t] end; [lia|].
  destruct (bv_unsigned b =? 45); [apply pool_acc_range; lia|].
  destruct (bv_unsigned b =? 43); apply CTypeFacts.swrap32_range.
Qed.

Lemma pool_len3 : forall {X : Type} (l : list X), length l = 3%nat -> exists v a b, l = [v; a; b].
Proof. intros X [|v [|a [|b [|e r]]]] H; cbn [length] in H; try lia. exists v, a, b. reflexivity. Qed.

Lemma pool_k1 : atoi_c.atoi_contract -> forall (tk : list (list byte))
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p1 p2 : word) (w : list byte),
  s5 = verbs_receive_disp.ntokw tk -> (length tk <= 64)%nat -> mem_inv rsegs m ->
  (length tk = 3%nat -> bytes_at rsegs m (bv_unsigned sp + 16) (le8 p1)) ->
  (length tk = 3%nat -> bytes_at rsegs m (bv_unsigned sp + 24) (le8 p2)) ->
  (length tk = 3%nat -> bytes_at rsegs m (bv_unsigned p2) (w ++ [Z_to_bv 8 0])) ->
  evt rsegs (fun ms' =>
      (length tk = 3%nat /\ exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
       ms' = MS (mkR (Z_to_bv 64 0x178cc) sp gp tp x5 x6 x7 s0 s1 p1 (Z_to_bv 64 (atoi_c.atoi_val w)) x12 x13 x14 x15 x16 x17
                     s2 p1 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0x1683c) fc None m' (seg_rom rsegs) /\ munch [] m m' /\ wmono rsegs m m') \/
      (length tk <> 3%nat /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17968) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x178ac) fc None m (seg_rom rsegs)).
Proof.
  intros ATOI tk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p1 p2 w E5 HL MI HB1 HB2 HW. subst s5.
  do 2 zstep. rewrite verbs_receive_disp.eqb_ntokw by lia.
  destruct (Z.of_nat (length tk) =? 3) eqn:E; cbv beta iota delta [negb].
  - apply Z.eqb_eq in E. assert (L3 : length tk = 3%nat) by lia.
    pose proof (verbs_receive_disp.read_all _ _ _ (HB1 L3)) as RD1. rewrite length_le8 in RD1.
    pose proof (verbs_receive_disp.read_all _ _ _ (HB2 L3)) as RD2. rewrite length_le8 in RD2.
    do 3 zstep.
    replace p2 with (Z_to_bv 64 (bv_unsigned p2)) by apply Z_to_bv_bv_unsigned.
    eapply evt_cut; [eapply ATOI; [exact (HW L3) | exact MI]|].
    intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & EM & MU & WM & MI'). subst ms'.
    replace (ret_pc (Z_to_bv 64 0x178c0)) with (Z_to_bv 64 0x178c0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    do 3 zstep. apply evt_done. left. split; [exact L3|].
    exists y5, y6, y7, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m'. split; [reflexivity|]. split; [exact MU | exact WM].
  - apply Z.eqb_neq in E. apply evt_done. right. split; [lia | reflexivity].
Qed.

Lemma k_j178cc : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x17830) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x178cc) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis AT : atoi_c.atoi_contract.
Hypothesis DG : forall f : YK11.FPState, @sup_pool_config_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_pool : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc RPool) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RPool -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
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
  set (p2 := nth 2 (s_ps S) (Z_to_bv 64 0)).
  assert (HB1 : length (toks D) = 3%nat -> bytes_at rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 16) (le8 p1)).
  { intros L3. rewrite SP2. apply bytes_at_normalize; [exact RO1|].
    assert (E : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
    pose proof (frame_tok S mem1 jk 1 p1 FR E) as FT.
    replace (s_spf S + 16) with (s_spf S + 8 + 8 * Z.of_nat 1) by lia. exact FT. }
  assert (HB2 : length (toks D) = 3%nat -> bytes_at rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 24) (le8 p2)).
  { intros L3. rewrite SP2. apply bytes_at_normalize; [exact RO1|].
    assert (E : nth_error (s_ps S) 2 = Some p2) by (unfold p2; apply nth_error_nth'; lia).
    pose proof (frame_tok S mem1 jk 2 p2 FR E) as FT.
    replace (s_spf S + 24) with (s_spf S + 8 + 8 * Z.of_nat 2) by lia. exact FT. }
  assert (HW : length (toks D) = 3%nat ->
    bytes_at rsegs (normalize rsegs mem1) (bv_unsigned p2) (nth 2 (toks D) [] ++ [Z_to_bv 8 0])).
  { intros L3. apply bytes_at_normalize; [exact RO1|].
    assert (E : nth_error (s_ps S) 2 = Some p2) by (unfold p2; apply nth_error_nth'; lia).
    assert (EW : nth_error (toks D) 2 = Some (nth 2 (toks D) [])) by (apply nth_error_nth'; lia).
    destruct (Forall2_nth _ _ _ _ _ _ TOK E EW) as ((Hb & _) & _). exact Hb. }
  eapply (@ka_w f _ B API HF S HS rg (route_pc RPool) mem1 md1 L1 A1 R1 O1 k1 qv None jk c [] _ P HST).
  { intros; exact I. }
  { eapply evt_mono.
    { unfold Regs6ss.mkR_of. cbn [route_pc].
    apply (pool_k1 AT (toks D)) with (p1 := p1) (p2 := p2) (w := nth 2 (toks D) []);
      [exact R21 | exact NL | apply mem_inv_normalize | exact HB1 | exact HB2 | exact HW]. }
    intros ms' HQ. split; [exact HQ|]. destruct HQ as [(_ & y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & E & MU & WM)|(_ & E)]; subst ms'.
    - do 3 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
    - do 3 eexists. split; [reflexivity|]. split; [apply munch_refl | apply wmono_refl]. }
  intros R' pc' m' rg' mem2 HQ X MK.
  destruct HQ as [(L3 & y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m'' & EQ & _ & _)|(L3 & EQ)]; injection EQ as ER EP EM; subst R' pc' m'.
  - destruct (pool_len3 (toks D) L3) as (v & a & b & TK).
    assert (G2 : getr rg' 2 = getr rg 2) by (rewrite (getr_of_eqv _ _ 2 X eq_refl); reflexivity).
    assert (G3 : getr rg' 3 = getr rg 3) by (rewrite (getr_of_eqv _ _ 3 X eq_refl); reflexivity).
    assert (G4 : getr rg' 4 = getr rg 4) by (rewrite (getr_of_eqv _ _ 4 X eq_refl); reflexivity).
    assert (G8 : getr rg' 8 = getr rg 8) by (rewrite (getr_of_eqv _ _ 8 X eq_refl); reflexivity).
    assert (G9 : getr rg' 9 = getr rg 9) by (rewrite (getr_of_eqv _ _ 9 X eq_refl); reflexivity).
    assert (G18 : getr rg' 18 = getr rg 18) by (rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity).
    assert (G21 : getr rg' 21 = getr rg 21) by (rewrite (getr_of_eqv _ _ 21 X eq_refl); reflexivity).
    assert (G25 : getr rg' 25 = getr rg 25) by (rewrite (getr_of_eqv _ _ 25 X eq_refl); reflexivity).
    assert (G26 : getr rg' 26 = getr rg 26) by (rewrite (getr_of_eqv _ _ 26 X eq_refl); reflexivity).
    assert (G27 : getr rg' 27 = getr rg 27) by (rewrite (getr_of_eqv _ _ 27 X eq_refl); reflexivity).
    assert (VR' : vregs S rg').
    { destruct VR as (V2 & V3 & V4 & V8 & V9 & V25 & V26 & V27).
      split; [rewrite G2; exact V2|]. split; [rewrite G3; exact V3|]. split; [rewrite G4; exact V4|].
      split; [rewrite G8; exact V8|]. split; [rewrite G9; exact V9|]. split; [rewrite G25; exact V25|].
      split; [rewrite G26; exact V26|]. rewrite G27; exact V27. }
    pose proof (MK 0x1683c eq_refl VR') as HST1.
    assert (E1 : getr rg' 1 = Z_to_bv 64 0x178cc) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
    assert (EBW : nth 2 (toks D) [] = b) by (rewrite TK; reflexivity).
    assert (E10 : getr rg' 10 = Z_to_bv 64 (bv_unsigned p1)).
    { rewrite Z_to_bv_bv_unsigned. rewrite (getr_of_eqv _ _ 10 X eq_refl). reflexivity. }
    assert (E11 : getr rg' 11 = Z_to_bv 64 (atoi_c.atoi_val b)).
    { rewrite (getr_of_eqv _ _ 11 X eq_refl), <- EBW. reflexivity. }
    pose proof (pool_atoi_range b) as AR.
    pose proof (dec_length _ AR) as DL.
    assert (RET : YK0s.ret_ok (Z_to_bv 64 0x178cc)) by (apply bv_eq; vm_compute; reflexivity).
    assert (KB : 0 <= SUP_POOL_CONFIG_K <= 14336) by (unfold SUP_POOL_CONFIG_K; lia).
    destruct (vs_pre B API HF S HS rg' 0x1683c mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_POOL_CONFIG_K 0x178cc
                HST1 E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
    assert (EP1 : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
    assert (EA : nth_error (toks D) 1 = Some a) by (rewrite TK; reflexivity).
    pose proof (st_tok_arg B API HF S HS rg' 0x1683c mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_POOL_CONFIG_K 1 p1 a
                  HST1 KB EP1 EA) as SA.
    assert (LA : Z.of_nat (length a) <= 8192).
    { assert (IA : In a (toks D)) by (rewrite TK; right; left; reflexivity).
      pose proof (verbs_receive_route.toks_len D a IA) as LW.
      pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS). lia. }
    assert (LT : (length (snd (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b))) <= 28)%nat).
    { unfold sup_pool_config_m, daemon_shape. apply stub_text_len. exact (rep_code _ _ _ _ _ _ REC). }
    assert (HSZ : Forall (fun n => 0 <= n <= 8194) (sup_pool_config_sizes (Some a) (atoi_c.atoi_val b) (snd (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b))))).
    { unfold sup_pool_config_sizes, sarg. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
    assert (HKS : (k1 + length (sup_pool_config_sizes (Some a) (atoi_c.atoi_val b) (snd (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b)))) <= 32)%nat).
    { unfold sup_pool_config_sizes. cbn [length]. lia. }
    pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST1))))) as (RES & _).
    pose proof (st_room B API S HS k1 _ (LMAX + 1) HKS HSZ ltac:(unfold LMAX; lia)) as ROOM.
    assert (CAP : sb_live (RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_pool_config_sizes (Some a) (atoi_c.atoi_val b) (snd (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b))))) <=
                  sb_cap (RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_pool_config_sizes (Some a) (atoi_c.atoi_val b) (snd (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b)))))).
    { destruct (sb_mallocs_fields (sup_pool_config_sizes (Some a) (atoi_c.atoi_val b) (snd (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b)))) (sb_n (s_b S) k1)) as (F1 & _ & F3).
      rewrite F1, F3. pose proof (ok_room B API S HS) as (_ & RC & _).
      unfold sb_n. cbn [sb_live sb_cap] in *. unfold sup_pool_config_sizes. cbn [length]. lia. }
    apply (call_ans B API HF S HS rg' 0x1683c mem2 md1 L1 A1 R1 O1 k1 qv jk _ SUP_POOL_CONFIG_K 0x178cc
             (sup_pool_config_sizes (Some a) (atoi_c.atoi_val b) (snd (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b)))) (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b))
             P HST1 E1 KB HKS HSZ).
    + eapply SR_mono.
      { pose proof (DG f L1 A1 rg' mem2 md1 (bv_unsigned p1) (Some a) (atoi_c.atoi_val b) R1 O1 (sb_n (s_b S) k1)
                      PRE E10 E11 AR ltac:(rewrite SPR; exact SA) SH REC RO FZ F18 RES ROOM) as C.
        rewrite SEGS in C. unfold SUP_POOL_CONFIG in C. exact C. }
      intros c'' HR.
      exact (ans_of B API HF SUP_POOL_CONFIG_K (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b)) (sup_pool_config_sizes (Some a) (atoi_c.atoi_val b))
               L1 A1 rg' mem2 md1 O1
               (sb_n (s_b S) k1) c'' HR CAP).
    + intros f' rg'' mem' md' L' A' O' q c' HST2 E10' HP2.
      apply (join_jump B API HF S HS f' rg R1 k1 qv rg'' 0x178cc 0x17830 mem' md' L' A'
               (fst (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b))) O'
               (k1 + length (sup_pool_config_sizes (Some a) (atoi_c.atoi_val b) (snd (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b)))))
               q (snd (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b))) jk c' P HST2 k_j178cc).
      * exact E10'.
      * exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) G18).
      * exact (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) G21).
      * rewrite RT, TK. cbn [plan_at]. unfold VerbsRun.run_step, VerbsRun.run_call.
        destruct (sup_pool_config_m R1 (Some a) (atoi_c.atoi_val b)); reflexivity.
      * unfold sup_pool_config_sizes. cbn [length]. lia.
      * exact JOIN.
  - assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    eapply REJ. split; [exact (MK 0x17968 eq_refl (vregs_pres S rg rg' VR PR))|].
    split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 21 X eq_refl); reflexivity|].
    split; [|lia].
    rewrite RT. destruct (toks D) as [|v [|a [|b [|e r]]]] eqn:TK'; cbn [plan_at]; try reflexivity.
    exfalso. apply L3. rewrite ?TK'. reflexivity.
Qed.

End R.

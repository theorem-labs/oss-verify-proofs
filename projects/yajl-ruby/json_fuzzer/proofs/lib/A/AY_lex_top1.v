(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Image SFW1_lemmas Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLeaf YajlLex YajlFactsLex YajlFactsBuf YajlFactsDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_lex_top1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_lex_rdck AY_lex_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition topW (K : alexK) : list (Z * Z) := kW K ++ [(k_OLP K, k_OLP K + 4); (k_OBP K, k_OBP K + 8)].
Lemma kW_topW : forall K m m', munch (kW K) m m' -> munch (topW K) m m'.
Proof. aceil.
  intros K m m' MU. eapply munch_weaken; [| exact MU]. unfold sub_fp, topW, kW, lexW. cbn [outside app]. intros x H. tauto.
Qed.

(* [comment removed for export] *)
End RC__1.
Ltac shnow0 U E A n a := let H := fresh "RD" in let U2 := fresh "U2" in
  pose proof U as U2; rewrite E in U2;
  pose proof (rd0_gen _ A n a U2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H; clear U2;
  zstepA; clear H; rewrite ?zxb_small, ?sxb_small by lia.
Ltac shnowOL U E OLP := let H := fresh "RD" in let U2 := fresh "U2" in
  pose proof U as U2; rewrite E in U2;
  pose proof (rdk_gen _ OLP 0 0 (blk_shadow 4) U2 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)) as H; clear U2;
  replace (znth (map bv_unsigned (blk_shadow 4)) 0) with 4 in H by reflexivity;
  zstepA; clear H; rewrite ?zxb_small, ?sxb_small by lia.
(* [comment removed for export] *)
Ltac olp_slow :=
  zstepA; change 7 with (Z.ones 3); rewrite ?Z.land_ones by lia; change (2^3) with 8;
  zstepA; zstepA;
  (let KS := fresh "KS" in if_cases KS; zify_cond KS;
   [ clear KS | exfalso; revert KS; rewrite ?sxb_small, ?zxb_small, ?signed_lit_small by lia; intro KS; Z.div_mod_to_equations; lia ]).
(* [comment removed for export] *)
Ltac zstoreT ENV ENVT :=
  let ST1 := fresh "SEPT" in let ST2 := fresh "SEPT" in
  pose proof (le_OBsep _ _ _ _ _ _ _ _ ENVT) as ST1; pose proof (le_OB _ _ _ _ _ _ _ _ ENVT) as ST2;
  (let X := fresh "SEPX" in destruct ST1 as (ST1 & X); let Y := fresh "SEPY" in destruct X as (X & Y); let W := fresh in destruct Y as (Y & W); clear W;
   zstepA; clear ST1 ST2 X Y).


Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable K : alexK.
Variable m0 : mem.
Hypothesis ENV : kenvA K.
Hypothesis ENVT : kenvT K.
Hypothesis KP : kpolA K.
Hypothesis SH : alexsh K m0.

Ltac pols := polu KP kp_OLs POLS; polu KP kp_OL POL; polu KP kp_OBs POBS; polu KP kp_OB POB; polu KP kp_Ls PLS; polu KP kp_L PL;
             polu KP kp_Hs PHS; polu KP kp_H PH; polu KP kp_stk PSTK.

(* [comment removed for export] *)
Lemma topW_low : forall a n, 2147450880 <= a -> a + n <= 17594333495296 -> disjoint_from (topW K) a n.
Proof. aceil.
  intros a n Ha Hn. pose proof (kOB_facts K ENV ENVT) as OBF. pose proof (le_ceil _ _ _ _ _ _ _ _ _ ENV) as CE.
  pose proof (kH_facts K ENV) as HF. pose proof (kL_facts K ENV) as LF. pose proof (kLB_facts K ENV) as LBF.
  unfold topW, kW, lexW. cbn. clear -Ha Hn OBF CE HF LF LBF CEILB. lia.
Qed.
Ltac nowT F n := intros mx MUx WMx; eapply (u8arr_transport asegs (topW K) m0 mx); [exact F| exact MUx| exact WMx|];
  rewrite (blk_shadow_len_nat n) by lia; apply topW_low;
  [pose proof (kH_facts K ENV); pose proof (kOB_facts K ENV ENVT); Z.div_mod_to_equations; lia
  |pose proof (kH_facts K ENV); pose proof (kOB_facts K ENV ENVT); Z.div_mod_to_equations; lia].
Lemma shH_nowT : forall m, munch (topW K) m0 m -> wmono asegs m0 m -> u8arr asegs m (ASB + k_H K / 8) (blk_shadow 104).
Proof. aceil. nowT (sh_H K m0 SH) 104. Qed.
Lemma shOB_nowT : forall m, munch (topW K) m0 m -> wmono asegs m0 m -> u8arr asegs m (ASB + k_OBP K / 8) (blk_shadow 8).
Proof. aceil. nowT (sh_OB K m0 SH) 8. Qed.
Lemma shOL_nowT : forall m, munch (topW K) m0 m -> wmono asegs m0 m -> u8arr asegs m (ASB + k_OLP K / 8) (blk_shadow 4).
Proof. aceil. nowT (sh_OL K m0 SH) 4. Qed.
(* [comment removed for export] *)
Ltac shpose MU WM :=
  pose proof (shH_nowT _ MU WM) as UH; pose proof (shOB_nowT _ MU WM) as UOB; pose proof (shOL_nowT _ MU WM) as UOL;
  pose proof (blk_shadow_length 104 ltac:(lia)) as UHL; pose proof (blk_shadow_length 8 ltac:(lia)) as UOBL; pose proof (blk_shadow_length 4 ltac:(lia)) as UOLL;
  remember (blk_shadow 104) as shbH eqn:EH in UH; rewrite <- EH in UHL;
  remember (blk_shadow 8) as shbOB eqn:EOB in UOB; rewrite <- EOB in UOBL;
  remember (blk_shadow 4) as shbOL eqn:EOL in UOL; rewrite <- EOL in UOLL.

(* [comment removed for export] *)
Lemma lex_epilogue : forall (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word)
    (k0 : list byte) (start : Z) (m : mem),
  rw_cells asegs m (kSQ K) (kframe K k0 k8 k64 start) ->
  pol (k_P K) (k_lo K) (bv_unsigned (k_sp K)) ->
  evtA asegs (k_P K) (fun ms' => ms' = MS (mkR (k_ra K) (k_sp K) (k_gp K) (k_tp K) t0 t1 t2 (k_s0 K) (k_s1 K) a0 a1 a2 a3 a4 a5 a6 a7
                                     (k_s2 K) (k_s3 K) (k_s4 K) (k_s5 K) (k_s6 K) (k_s7 K) (k_s8 K) (k_s9 K) (k_s10 K) (k_s11 K) t3 t4 t5 t6)
                                (k_F K) (ret_pc (k_ra K)) (k_fc K) None m (seg_rom asegs))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x85974) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until m. intros FR PSTK. pose proof ENV as ENV0. destruct ENV0. clear_seps.
  unfold kSQ, kframe, alex_frame, pol in *. unfold wz.
  do 13 zstepA. zstepA. stepA.
  replace (Z_to_bv 64 (bv_unsigned (k_sp K) - 208 + 208)) with (k_sp K) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  apply evtA_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lex_fin_walk : forall (tok : ytok) (rav s2v s3v s6v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e1 off1 start1 : Z),
  tok <> TK_eof ->
  alexmem K m0 m e1 off1 start1 k0 k8 k64 ->
  rw_cells asegs m (k_OBP K) [C8 (wz 0)] -> rw_cells asegs m (k_OLP K) [C4 (wz 0)] ->
  0 <= start1 <= off1 -> off1 <= zlength (k_txt K) -> (is_string_tok tok = true -> start1 + 2 <= off1) -> 0 <= e1 <= 11 ->
  evtA asegs (k_P K) (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR (k_ra K) (k_sp K) (k_gp K) (k_tp K) t0' t1' t2' (k_s0 K) (k_s1 K) (wz (tok_code tok)) a1' a2' a3' a4' a5' a6' a7'
                    (k_s2 K) (k_s3 K) (k_s4 K) (k_s5 K) (k_s6 K) (k_s7 K) (k_s8 K) (k_s9 K) (k_s10 K) (k_s11 K) t3' t4' t5' t6')
               (k_F K) (ret_pc (k_ra K)) (k_fc K) None m' (seg_rom asegs)
      /\ munch (topW K) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' (k_lo K) (bv_unsigned (k_sp K))
      /\ rw_cells asegs m' (k_H K + 32) [C4 (wz off1)] /\ rw_cells asegs m' (k_L K) (lxcells e1 (k_LB K) (kAF K))
      /\ rw_cells asegs m' (k_LB K) (buf_cells ybuf_zero 0 (kAF K))
      /\ rw_cells asegs m' (k_OBP K) [C8 (wz (outref_addr (k_T K) 0 (fst (fin_ob tok start1 off1))))]
      /\ rw_cells asegs m' (k_OLP K) [C4 (wz (snd (fin_ob tok start1 off1)))])
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v (wz (tok_code tok)) (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz J_TOK) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until start1. intros NE LM OB OL BS BO STR ER.
  pose proof LM as (MU & WM & MI & ST & FR & OFF & LX & BC).
  pose proof (kH_facts K ENV) as HF. pose proof (kOB_facts K ENV ENVT) as OBF.
  pose proof (rd_shL K m0 _ ENV SH MU WM 28 ltac:(lia)) as RDL28.
  lex_prep ENV BC. unfold J_TOK in *. unfold wz in OB, OL. pols.
  try clear le_Tsep; try clear le_OT.   (* [comment removed for export] *)
  apply kW_topW in MU.
  (* [comment removed for export] *)
  shpose MU WM.
  unfold topW, kW, lexW in MU. cbn [app] in MU.
  pose proof (tok_code_range tok) as TR.
  zstepA. zstepA. clear RDL28. rewrite ?zxb_small, ?sxb_small by lia. zstepA. iflit.   (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by lia. zstepA. iflit.                        (* [comment removed for export] *)
  stepA. zstepA. if_cases K1; zify_cond K1.                                  (* [comment removed for export] *)
  - (* [comment removed for export] *)
    assert (TE : tok = TK_error) by (destruct tok; cbn in K1; try lia; reflexivity). subst tok.
    eapply evtA_mono; [eapply lex_epilogue; [exact FR| exact PSTK]|].
    cbv beta. intros ms' ->. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
    split; [reflexivity|].
    release_frame FR ST (bv_unsigned (k_sp K)).
    cbn [fin_ob tok_eqb tok_code Z.eqb Pos.eqb fst snd outref_addr].
    repeat match goal with |- _ /\ _ => split end; assumption.
  - (* [comment removed for export] *)
    zstepA.                                                                  (* [comment removed for export] *)
    shnow0 UOB EOB (k_OBP K) 8 (k_OBP K). zstepA. iflit.                         (* [comment removed for export] *)
    zstepA. zstepA. zstepA. rewrite (land_M32_small start1) by lia.          (* [comment removed for export] *)
    zstepA. zstepA. zstepA.                                                  (* [comment removed for export] *)
    clear UH UOB UOL UHL UOBL UOLL EH EOB EOL shbH shbOB shbOL. zstoreT ENV ENVT. shpose MU WM.             (* [comment removed for export] *)
    shnow0 UH EH (k_H K) 104 (k_H K + 32).                                      (* [comment removed for export] *)
    zstepA. zstepA. zstepA. iflit.                                           (* [comment removed for export] *)
    shnowOL UOL EOL (k_OLP K).                                                             (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by lia. zstepA. iflit.                      (* [comment removed for export] *)
    olp_slow.   (* [comment removed for export] *)
    zstepA. rewrite (swrap32_small (off1 - start1)) by lia || rewrite (swrap32_small (off1 + - start1)) by lia.   (* [comment removed for export] *)
    clear UH UOB UOL UHL UOBL UOLL EH EOB EOL shbH shbOB shbOL. zstoreT ENV ENVT. shpose MU WM. stepA.      (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstepA. stepA. zstepA. if_cases K2; zify_cond K2.                        (* [comment removed for export] *)
    + (* [comment removed for export] *)
      assert (NS : is_string_tok tok = false).
      { rewrite <- land14_string. apply Z.eqb_neq. exact K2. }
      stepA.                                                                 (* [comment removed for export] *)
      eapply evtA_mono; [eapply lex_epilogue; [exact FR| exact PSTK]|].
      cbv beta. intros ms' ->. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
      split; [reflexivity|].
      release_frame FR ST (bv_unsigned (k_sp K)).
      unfold fin_ob. rewrite NS. replace (tok_eqb tok TK_error) with false by (unfold tok_eqb; cbn [tok_code]; symmetry; apply Z.eqb_neq; lia).
      cbn [fst snd outref_addr].
      repeat match goal with |- _ /\ _ => split end; assumption.
    + assert (IS : is_string_tok tok = true).
      { rewrite <- land14_string. apply Z.eqb_eq. exact K2. }
      specialize (STR IS).
      shnowOL UOL EOL (k_OLP K). zstepA. iflit.                                            (* [comment removed for export] *)
      olp_slow.
      zstepA. rewrite ?ysx32_small by lia. stepA. zstepA. if_cases K3; zify_cond K3. 1:{ kill K3. } clear K3.   (* [comment removed for export] *)
      shnow0 UOB EOB (k_OBP K) 8 (k_OBP K). zstepA. iflit.                       (* [comment removed for export] *)
      zstepA. zstepA. clear UH UOB UOL UHL UOBL UOLL EH EOB EOL shbH shbOB shbOL. zstoreT ENV ENVT. shpose MU WM.   (* [comment removed for export] *)
      shnowOL UOL EOL (k_OLP K). zstepA. iflit.                                            (* [comment removed for export] *)
      olp_slow.
      zstepA. clear UH UOB UOL UHL UOBL UOLL EH EOB EOL shbH shbOB shbOL. zstoreT ENV ENVT.                 (* [comment removed for export] *)
      stepA.                                                                 (* [comment removed for export] *)
      eapply evtA_mono; [eapply lex_epilogue; [exact FR| exact PSTK]|].
      cbv beta. intros ms' ->. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
      split; [reflexivity|].
      release_frame FR ST (bv_unsigned (k_sp K)).
      unfold fin_ob. rewrite IS. replace (tok_eqb tok TK_error) with false by (unfold tok_eqb; cbn [tok_code]; symmetry; apply Z.eqb_neq; lia).
      cbn [fst snd outref_addr].
      replace (k_T K + (start1 + 1)) with (k_T K + start1 + 1) by lia.
      replace (off1 - start1 - 2) with (off1 - start1 + -2) by lia.
      repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Hypothesis BCLR : aybuf_clear_stmt.

(* [comment removed for export] *)
Lemma lex_eof_head : forall (rav s2v s3v s6v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e1 off1 start1 : Z),
  alexmem K m0 m e1 off1 start1 k0 k8 k64 -> 0 <= start1 <= off1 -> off1 <= zlength (k_txt K) -> 0 <= e1 <= 11 ->
  evtA asegs (k_P K) (fun ms' => exists (t0' t1' t2' a3' a5' a6' a7' t3' t4' t5' t6' s2' s10' : word) (m' : mem),
      ms' = MS (mkR (wz 0x85880) (wz (kSQ K)) (k_gp K) (k_tp K) t0' t1' t2' (wz (k_H K + 32)) (wz (k_L K + 16))
                    (wz (k_LB K)) (wz (k_T K + start1)) (wz (off1 - start1)) a3' (wz start1) a5' a6' a7'
                    s2' (wz 1) (wz (k_L K + 24)) (wz (k_L K + 28)) (wz ((k_L K + 16) / 8 + ASB)) (wz 3) (wz (zlength (k_txt K))) (wz ASB) s10'
                    (wz ((k_H K + 32) / 8 + ASB)) t3' t4' t5' t6')
               (k_F K) (wz AY_BUF_APPEND) (k_fc K) None m' (seg_rom asegs)
      /\ munch (kW K) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' (k_lo K) (kSQ K)
      /\ rw_cells asegs m' (kSQ K) (kframe K k0 k8 k64 start1) /\ rw_cells asegs m' (k_H K + 32) [C4 (wz off1)]
      /\ rw_cells asegs m' (k_L K) [C4 (wz 0); C4 (wz 0); C4 (wz e1); C4 (wz 0); C8 (wz (k_LB K)); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 1); C8 (wz (kAF K))]
      /\ rw_cells asegs m' (k_LB K) (buf_cells ybuf_zero 0 (kAF K)))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz J_EOF) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until start1. intros LM BS BO ER.
  pose proof LM as (MU & WM & MI & ST & FR & OFF & LX & BC). lex_prep ENV BC. unfold J_EOF, AY_BUF_APPEND in *.
  pols. polu KP kp_img PIMG.
  assert (USQ : bv_unsigned (Z_to_bv 64 (bv_unsigned (k_sp K) - 208)) = bv_unsigned (k_sp K) - 208) by (apply unsigned_lit; lia).
  zstepA. shld (rd_shL K m0 _ ENV SH MU WM 28 ltac:(lia)). zstepA. iflit.   (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by lia. stepA. stepA. zstepA. iflit.          (* [comment removed for export] *)
  zstepA. shadow_addr. zstepA.                                               (* [comment removed for export] *)
  shld (rd_shL K m0 _ ENV SH MU WM 16 ltac:(lia)). zstepA. iflit.            (* [comment removed for export] *)
  zstepA.                                                                    (* [comment removed for export] *)
  stepA.                                                                     (* [comment removed for export] *)
  pose proof (stat_now K m0 _ ENV SH MU WM) as STA1.
  pose proof (shLB_now K m0 _ ENV SH MU WM) as BSH1.
  pose proof (kLB_facts K ENV) as LBF.
  seps ENV.
  pose proof (BCLR (k_P K) (k_LB K) 0 (k_H K + 72) (k_lo K) ybuf_zero) as CLR'. unfold aybuf_clear_rpost in CLR'. cbn [yb_data ybuf_zero app] in CLR'.
  call_spA CLR'; rewrite ?USQ.
  - exact STA1.
  - split; [unfold buf_cells; cbn [buf_state_code yb_state yb_len yb_used ybuf_zero]; exact BC| split; [split; reflexivity| cbn; lia]].
  - exact I.
  - reflexivity.
  - unfold buf_inv; cbn. repeat split; try lia; intros X; first [reflexivity| lia| exfalso; apply X; reflexivity].
  - lia.
  - unfold oshadow, block_shadow, A_SB, SIZEOF_BUF. split; [lia|]. split; [lia|]. exact BSH1.
  - unfold oshw_hi, A_SB, amem. cbn. lia.
  - unfold SIZEOF_BUF; aceil. lia.
  - intros X. exfalso. apply X. reflexivity.
  - exact MI.
  - exact ST.
  - aceil. lia.
  - lia.
  - lia.
  - reflexivity.
  - intros a k Ha Hk. apply PSTK; lia.
  - unfold AY_IMG_LO, AY_IMG_HI. intros a k Ha Hk. apply PIMG; lia.
  - unfold opol, SIZEOF_BUF, oshw_lo, oshw_hi, A_SB, amem. split; intros a k Ha Hk; [apply (kp_LB _ KP)| apply (kp_LBs _ KP)]; cbn in *; lia.
  - intros X. exfalso. apply X. reflexivity.
  - (* [comment removed for export] *)
    clear_seps.
    lazymatch goal with H : stk asegs ?mx (k_lo K) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2; rewrite ?USQ in ST2 end.
    lazymatch goal with H : buf_struct _ _ _ _ _ _ |- _ => destruct H as (BC2 & _ & _ & _); unfold buf_cells, buf_cleared in BC2; cbn [yb_state yb_len yb_used yb_data buf_state_code ybuf_zero] in BC2 end.
    lazymatch goal with H : buf_data _ _ _ _ |- _ => clear H | _ => idtac end.
    try lazymatch goal with H : None <> None -> _ |- _ => clear H end.
    zstepA. shld (rd_shL K m0 _ ENV SH MU WM 28 ltac:(lia)). zstepA. iflit. (* [comment removed for export] *)
    stepA. zstepA. shadow_addr.                                              (* [comment removed for export] *)
    zstoreA ENV.                                                             (* [comment removed for export] *)
    zstepA.                                                                  (* [comment removed for export] *)
    shld (rd_shL K m0 _ ENV SH MU WM 16 ltac:(lia)). zstepA. iflit.          (* [comment removed for export] *)
    pose proof (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)) as RDH. zstepA.    (* [comment removed for export] *)
    zstepA. clear RDH. rewrite ?zxb_small, ?sxb_small by lia. zstepA. iflit. (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by lia.                                     (* [comment removed for export] *)
    zstepA. zstepA. zstepA. rewrite (land_M32_small start1) by lia.          (* [comment removed for export] *)
    zstepA. zstepA.                                                          (* [comment removed for export] *)
    zstepA. rewrite (swrap32_small (off1 - start1)) by lia || rewrite (swrap32_small (off1 + - start1)) by lia.   (* [comment removed for export] *)
    stepA.                                                                   (* [comment removed for export] *)
    apply evtA_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
    unfold kW, lexW, kframe, alex_frame, buf_cells. cbn [buf_state_code yb_state yb_len yb_used ybuf_zero].
    repeat match goal with |- _ /\ _ => split end; first [assumption| eassumption].
Qed.
End S.
End RC__2.

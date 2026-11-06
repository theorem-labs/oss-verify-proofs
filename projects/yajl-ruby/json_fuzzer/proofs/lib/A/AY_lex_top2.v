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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_lex_rdck AY_lex_kit AY_lex_top1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac olp_slow_bge :=
  zstepA; change 7 with (Z.ones 3); rewrite ?Z.land_ones by lia; change (2^3) with 8;
  zstepA; zstepA;
  (let KS := fresh "KS" in if_cases KS; zify_cond KS;
   [ exfalso; revert KS; rewrite ?sxb_small, ?zxb_small, ?signed_lit_small by lia; intro KS; Z.div_mod_to_equations; lia | clear KS ]).

(* [comment removed for export] *)
Ltac yrevealK H MU WM tac :=
  unfold yhide in H;
  lazymatch type of H with
  | rw_cells ?segs _ _ _ =>
      eapply (rw_cells_transport segs) in H; [ | exact MU | exact WM | cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; tac ]
  | Arr.u8arr ?segs _ _ _ =>
      eapply (u8arr_transport segs) in H; [ | exact MU | exact WM | cbv [disjoint_from fst snd]; tac ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section P.
Variables (P : acc -> Prop) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo T : Z) (txt : list Z) (H L LB OBP OLP OT OTn : Z).

Lemma lex_prologue : forall (ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 obw olw : word)
    (m : mem) (e off : Z) (shH shOB shOL : list byte),
  stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
  rw_cells asegs m (H + 32) [C4 (wz off)] -> rw_cells asegs m OBP [C8 obw] -> rw_cells asegs m OLP [C4 olw] ->
  rw_cells asegs m L (lxcells e LB (H + 72)) -> rw_cells asegs m LB (buf_cells ybuf_zero 0 (H + 72)) ->
  ay_statics m ->
  u8arr asegs m (ASB + H / 8) shH -> shH = blk_shadow 104 ->
  u8arr asegs m (ASB + OBP / 8) shOB -> shOB = blk_shadow 8 ->
  u8arr asegs m (ASB + OLP / 8) shOL -> shOL = blk_shadow 4 ->
  lexenvA (bv_unsigned sp) lo T (zlength txt) H L LB OT OTn -> lexenvT lo T (zlength txt) H L LB OBP OLP ->
  0 <= off <= zlength txt -> 0 <= e <= 11 ->
  pol P lo (bv_unsigned sp) -> pol P AY_IMG_LO AY_IMG_HI -> pol P H (H + 104) -> pol P (ASB + H / 8) (ASB + H / 8 + 13) ->
  pol P OBP (OBP + 8) -> pol P (ASB + OBP / 8) (ASB + OBP / 8 + 1) -> pol P OLP (OLP + 4) -> pol P (ASB + OLP / 8) (ASB + OLP / 8 + 1) ->
  evtA asegs P (fun ms' => exists (t1' a1' a2' a3' a4' k8 k16 k24 : word) (k0 : list byte) (m1 : mem),
      ms' = MS (mkR ra (wz (bv_unsigned sp - 208)) gp tp t0 t1' t2 (wz (H + 32)) (wz (L + 16)) (wz off) a1' a2' a3' a4' (wz OLP) a6 a7
                    s2 s3 (wz (L + 24)) (wz (L + 28)) (wz (L + 32)) (wz AY_JT_LEX) (wz (zlength txt)) (wz ASB) s10
                    (wz ((H + 32) / 8 + ASB)) t3 t4 t5 t6)
               F (wz J_HD) fc None m1 (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (OLP, OLP + 4); (OBP, OBP + 8)] m m1
      /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp - 208)
      /\ rw_cells asegs m1 (bv_unsigned sp - 208)
           (alex_frame k0 k8 k16 k24 (wz ((L + 32) / 8 + ASB)) OBP OLP T L off ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      /\ rw_cells asegs m1 (H + 32) [C4 (wz off)] /\ rw_cells asegs m1 OBP [C8 (wz 0)] /\ rw_cells asegs m1 OLP [C4 (wz 0)]
      /\ rw_cells asegs m1 L (lxcells e LB (H + 72)) /\ rw_cells asegs m1 LB (buf_cells ybuf_zero 0 (H + 72)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz L) (wz T) (wz (zlength txt)) (wz (H + 32)) (wz OBP) (wz OLP) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AY_LEX_LEX) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until shOL. intros ST MI OFF OB OL LX BC STA UH EH UOB EOB UOL EOL ENV ENVT OFFB ER PSTK PIMG PH PHS POB POBS POL POLS.
  pose proof ENV as ENV0. destruct ENV0. try clear le_HL; try clear le_HLB; try clear le_LLB; clear_seps.
  pose proof ENVT as ET. destruct ET as [OBF _].
  unfold lxcells, buf_cells, AY_LEX_LEX, AY_JT_LEX, J_HD, pol, AY_IMG_LO, AY_IMG_HI in *. unfold wz.
  cbn [buf_state_code yb_state yb_len yb_used ybuf_zero] in BC. unfold wz in OFF, OB, OL, LX, BC.
  destruct STA as (G1 & G2 & G3 & G4). unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4. clear G3 G4.
  pose proof (blk_shadow_length 104 ltac:(lia)) as UHL. rewrite <- EH in UHL.
  pose proof (blk_shadow_length 8 ltac:(lia)) as UOBL. rewrite <- EOB in UOBL.
  pose proof (blk_shadow_length 4 ltac:(lia)) as UOLL. rewrite <- EOL in UOLL.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (OLP, OLP + 4); (OBP, OBP + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf. pose proof (wmono_refl asegs m) as WMf.
  (* [comment removed for export] *)
  yhide OFF. yhide OB. yhide OL. yhide LX. yhide BC. yhide G1. yhide G2. yhide UH. yhide UOB. yhide UOL.
  (* [comment removed for export] *)
  yhide OBF. yhide le_Tsep. yhide le_OT.
  carve_frame 208%nat ST.
  stepA.                                                                     (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [] 208 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  do 13 stepA.                                                               (* [comment removed for export] *)
  stepA. stepA.                                                              (* [comment removed for export] *)
  zstepA.                                                                    (* [comment removed for export] *)
  yshow OBF. yrevealK G1 MU WM ltac:(clear -CEILB le_ceil OBF; lia). yrevealK G2 MU WM ltac:(clear -CEILB le_ceil OBF; lia). yhide OBF.
  stepA. zstepA. zstepA.                                                     (* [comment removed for export] *)
  clear G1 G2.
  zstepA. shadow_addr. zstepA.                                               (* [comment removed for export] *)
  yshow OBF. yrevealK UH MU WM ltac:(clear -CEILB le_ceil le_H OBF UHL; lia). yhide OBF.
  shnow0 UH EH H 104 (H + 32).                                               (* [comment removed for export] *)
  zstepA.                                                                    (* [comment removed for export] *)
  zstepA. iflit.                                                             (* [comment removed for export] *)
  yshow OBF.
  zstepA. shadow_addr. zstepA. zstepA.                                       (* [comment removed for export] *)
  yreveal UOB MU WM.
  shnow0 UOB EOB OBP 8 OBP. zstepA. iflit.                                   (* [comment removed for export] *)
  yreveal OB MUf WMf. yreveal OL MUf WMf. clear MUf WMf.
  pose proof (le_OBsep _ _ _ _ _ _ _ _ ENVT) as SEPT.
  (* [comment removed for export] *)
  yrevealK OFF MU WM ltac:(clear -CEILB le_ceil le_H SEPT OBF; lia).
  yrevealK LX MU WM ltac:(clear -CEILB le_ceil le_L SEPT OBF; lia).
  yrevealK BC MU WM ltac:(clear -CEILB le_ceil le_LB SEPT OBF; lia).
  yrevealK UOL MU WM ltac:(clear -CEILB le_ceil OBF UOLL; lia).
  clear SEPT.
  zstoreT ENV ENVT.                                                          (* [comment removed for export] *)
  zstepA. shadow_addr. zstepA. zstepA.                                       (* [comment removed for export] *)
  shnowOL UOL EOL OLP.                                                       (* [comment removed for export] *)
  zstepA. rewrite ysx32_small by lia. zstepA.                                (* [comment removed for export] *)
  zstepA. iflit. stepA.                                                      (* [comment removed for export] *)
  olp_slow_bge. stepA.                                                       (* [comment removed for export] *)
  zstepA. zstepA.                                                            (* [comment removed for export] *)
  zstoreT ENV ENVT.                                                          (* [comment removed for export] *)
  zstepA. rewrite ysx32_small by lia. zstepA. if_cases KA; zify_cond KA. 2:{ kill KA. } clear KA.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. zstepA.                                    (* [comment removed for export] *)
  zstepA. stepA. zstepA. shadow_addr. zstepA. zstepA. zstepA.                (* [comment removed for export] *)
  zstepA. zstepA. shadow_addr. zstepA. zstepA. zstepA.                       (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. zstepA. zstepA.                            (* [comment removed for export] *)
  apply evtA_done. eexists _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
  unfold alex_frame. repeat match goal with |- _ /\ _ => split end; first [assumption| eassumption].
Qed.
End P.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable K : alexK.
Hypothesis ENV : kenvA K.
Hypothesis KP : kpolA K.
Hypothesis YBE : aybuf_err_stmt.

Definition eof_err (st e1 : Z) : Z := if st =? 0 then e1 else 11.
Definition eof_ret (st : Z) : Z := if st =? 0 then 3 else 4.

Lemma lex_eof_tail : forall (s2v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte)
    (m : mem) (e1 off1 start1 st LB bl bu bd ba : Z) (shL shLB : list byte),
  let rest := [C4 (wz bl); C4 (wz bu); C4 (wz 0); C8 (wz bd); C8 (wz ba)] in
  rw_cells asegs m (kSQ K) (kframe K k0 k8 k64 start1) ->
  rw_cells asegs m (k_L K) [C4 (wz 0); C4 (wz 0); C4 (wz e1); C4 (wz 0); C8 (wz LB); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 1); C8 (wz (kAF K))] ->
  rw_cells asegs m LB (C4 (wz st) :: rest) -> 0 <= st <= 2 -> 17594333495296 <= LB -> LB mod 16 = 0 -> LB + 32 <= alloc_ceiling ->
  (k_L K + 48 <= LB \/ LB + 32 <= k_L K) ->
  u8arr asegs m (ASB + k_L K / 8) shL -> shL = blk_shadow 48 ->
  u8arr asegs m (ASB + LB / 8) shLB -> shLB = blk_shadow 32 ->
  ay_statics m -> stk asegs m (k_lo K) (kSQ K) -> mem_inv asegs m -> 0 <= e1 <= 11 ->
  pol (k_P K) LB (LB + 32) -> pol (k_P K) (ASB + LB / 8) (ASB + LB / 8 + 4) ->
  evtA asegs (k_P K) (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR (k_ra K) (k_sp K) (k_gp K) (k_tp K) t0' t1' t2' (k_s0 K) (k_s1 K) (wz (eof_ret st)) a1' a2' a3' a4' a5' a6' a7'
                    (k_s2 K) (k_s3 K) (k_s4 K) (k_s5 K) (k_s6 K) (k_s7 K) (k_s8 K) (k_s9 K) (k_s10 K) (k_s11 K) t3' t4' t5' t6')
               (k_F K) (ret_pc (k_ra K)) (k_fc K) None m' (seg_rom asegs)
      /\ munch [(k_lo K, bv_unsigned (k_sp K)); (k_L K, k_L K + 48)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' (k_lo K) (bv_unsigned (k_sp K))
      /\ rw_cells asegs m' (k_L K) [C4 (wz 0); C4 (wz 0); C4 (wz (eof_err st e1)); C4 (wz 0); C8 (wz LB); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 1); C8 (wz (kAF K))]
      /\ rw_cells asegs m' LB (C4 (wz st) :: rest) /\ u8arr asegs m' (ASB + LB / 8) shLB /\ ay_statics m')
    (MS (mkR (wz 0x85880) (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz 1) (wz (k_L K + 24)) (wz (k_L K + 28)) (wz ((k_L K + 16) / 8 + ASB)) (wz 3) (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (ret_pc (wz 0x85880)) (k_fc K) None m (seg_rom asegs)).
Proof. aceil.
  intros until shLB. cbv zeta. intros FR LX BC STR LB1 LB16 LBC SEP UL EL ULB ELB STA ST MI ER PLB PLBS.
  pose proof ENV as ENV0. destruct ENV0. try clear le_HL; try clear le_HLB; try clear le_LLB; clear_seps. unfold kSQ, kAF, kframe, alex_frame in *. unfold wz.
  unfold wz in FR, LX, BC.
  pose proof (blk_shadow_length 48 ltac:(lia)) as ULL. rewrite <- EL in ULL.
  pose proof (blk_shadow_length 32 ltac:(lia)) as ULBL. rewrite <- ELB in ULBL.
  pose proof (kL_facts K ENV) as LF.
  polu KP kp_img PIMG. polu KP kp_Ls PLS. polu KP kp_L PL. polu KP kp_stk PSTK. unfold pol in PLB, PLBS.
  pose proof (munch_refl [(k_lo K, bv_unsigned (k_sp K)); (k_L K, k_L K + 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct STA as (G1 & G2 & G3 & G4). unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.
  ret_pc_lit.
  zstepA. shadow_addr. zstepA.                                               (* [comment removed for export] *)
  shnow0 UL EL (k_L K) 48 (k_L K + 24). zstepA. iflit.                       (* [comment removed for export] *)
  pose proof SEP as SEP'. zstepA. clear SEP'.                                (* [comment removed for export] *)
  shnow0 UL EL (k_L K) 48 (k_L K + 16). zstepA. iflit.                       (* [comment removed for export] *)
  zstepA.                                                                    (* [comment removed for export] *)
  stepA.                                                                     (* [comment removed for export] *)
  assert (USQ : bv_unsigned (Z_to_bv 64 (bv_unsigned (k_sp K) - 208)) = bv_unsigned (k_sp K) - 208) by (apply unsigned_lit; lia).
  pose proof SEP as SEP'.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    destruct (proj1 (ycells_app asegs mx LB [C4 (Z_to_bv 64 st)] [C4 (Z_to_bv 64 bl); C4 (Z_to_bv 64 bu); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 bd); C8 (Z_to_bv 64 ba)]) BC) as [BC1 BCr] end.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BCr. clear BC.
  call_spA (YBE (k_P K) LB st (k_lo K) LB 32); rewrite ?USQ.
  - unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz. split; [exact G1| split; [exact G2| split; [exact G3| exact G4]]].
  - exact BC1.
  - lia.
  - lia.
  - Z.div_mod_to_equations; lia.
  - unfold oshadow, block_shadow, A_SB. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. rewrite <- ELB. exact ULB.
  - lia.
  - lia.
  - lia.
  - aceil. lia.
  - unfold oshw_hi, A_SB, amem. cbn -[Z.add Z.div Z.le]. lia.
  - left. unfold oshw_hi, A_SB, amem. lia.
  - exact MI.
  - exact ST.
  - aceil. lia.
  - lia.
  - lia.
  - reflexivity.
  - intros a k Ha Hk. apply PSTK; lia.
  - unfold AY_IMG_LO, AY_IMG_HI. intros a k Ha Hk. apply PIMG; lia.
  - intros a k Ha Hk. apply PLB; lia.
  - unfold oshw_lo, oshw_hi, A_SB, amem. intros a k Ha Hk. apply PLBS; lia.
  - (* [comment removed for export] *)
    clear SEP'.
    lazymatch goal with H : stk asegs ?mx (k_lo K) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2; rewrite ?USQ in ST2 end.
    lazymatch goal with H : ?x = wz st |- _ => subst x end.
    lazymatch goal with H : rw_cells asegs ?mx LB [C4 _] |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (proj2 (ycells_app asegs mx LB [C4 (Z_to_bv 64 st)] [C4 (Z_to_bv 64 bl); C4 (Z_to_bv 64 bu); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 bd); C8 (Z_to_bv 64 ba)])
                    (conj H ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; exact BCr))) as BC; clear H BCr; cbn [app] in BC end.
    lazymatch goal with H : ay_statics ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => destruct H as (G1' & G2' & G3' & G4'); unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1', G2', G3', G4' end.
    clear G1 G2 G3 G4.
    unfold wz. zstepA. if_cases K5; zify_cond K5.                             (* [comment removed for export] *)
    + (* [comment removed for export] *)
      zstepA. iflit.                                                         (* [comment removed for export] *)
      stepA.                                                                 (* [comment removed for export] *)
      eapply evtA_mono; [eapply (lex_epilogue K ENV); [exact FR| exact (kp_stk _ KP)]|].
      cbv beta. intros ms' ->. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
      unfold eof_ret, eof_err. replace (st =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      split; [reflexivity|].
      release_frame FR ST2 (bv_unsigned (k_sp K)).
      repeat match goal with |- _ /\ _ => split end; try assumption.
      unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz. split; [exact G1'| split; [exact G2'| split; [exact G3'| exact G4']]].
    + (* [comment removed for export] *)
      zstepA. zstepA. zstepA. shadow_addr. zstepA.                           (* [comment removed for export] *)
      shnow0 UL EL (k_L K) 48 (k_L K + 8). zstepA. iflit.                    (* [comment removed for export] *)
      stepA. pose proof SEP as SEP'. zstepA. clear SEP'. stepA. stepA.         (* [comment removed for export] *)
      eapply evtA_mono; [eapply (lex_epilogue K ENV); [exact FR| exact (kp_stk _ KP)]|].
      cbv beta. intros ms' ->. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
      unfold eof_ret, eof_err. replace (st =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      split; [reflexivity|].
      release_frame FR ST2 (bv_unsigned (k_sp K)).
      repeat match goal with |- _ /\ _ => split end; try assumption.
      unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz. split; [exact G1'| split; [exact G2'| split; [exact G3'| exact G4']]].
Qed.
End S.
End RC__1.

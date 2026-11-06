(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2
     RY_lex_kit RY_lex_main.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLeaf YajlLex YajlParser YajlFactsLex YajlFactsBuf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Open Scope yprog_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma land14_string : forall tok, (Z.land (tok_code tok) 14 =? 12) = is_string_tok tok.
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
Definition fin_ob (tok : ytok) (start1 off1 : Z) : outref * Z :=
  if tok_eqb tok TK_error then (OB_null, 0)
  else if is_string_tok tok then (OB_text (start1 + 1), off1 - start1 - 2)
  else (OB_text start1, off1 - start1).

(* [comment removed for export] *)
Definition topW (K : lexK) : list (Z * Z) := kW K ++ [(k_OLP K, k_OLP K + 4); (k_OBP K, k_OBP K + 8)].

Lemma kW_topW : forall K m m', munch (kW K) m m' -> munch (topW K) m m'.
Proof.
  intros K m m' MU. eapply munch_weaken; [| exact MU]. unfold sub_fp, topW, kW, lexW. cbn [outside app]. intros x H. tauto.
Qed.

(* [comment removed for export] *)
Lemma lzbytes_firstn : forall k l, zbytes (firstn k l) = firstn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite firstn_map. reflexivity. Qed.
Lemma lzbytes_skipn : forall k l, zbytes (skipn k l) = skipn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite skipn_map. reflexivity. Qed.
Lemma lbytes_at_sub : forall m A bs i k,
  bytes_at rsegs m A bs -> (i <= length bs)%nat -> bytes_at rsegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
  intros m A bs i k HB Hi.
  rewrite <- (firstn_skipn i bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in HB. apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.
Lemma lbytes_at_zslice : forall m A str i k,
  bytes_at rsegs m A (zbytes str) -> 0 <= i <= zlength str -> bytes_at rsegs m (A + i) (zbytes (zslice str i k)).
Proof.
  intros m A str i k HB Hi. unfold zslice. rewrite lzbytes_firstn, lzbytes_skipn.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. apply lbytes_at_sub; [exact HB|]. rewrite zbytes_length. unfold zlength in Hi. lia.
Qed.
Lemma lForall_zslice : forall (P : Z -> Prop) str i k, Forall P str -> Forall P (zslice str i k).
Proof.
  intros P str i k HF. unfold zslice.
  rewrite <- (firstn_skipn (Z.to_nat i) str) in HF. apply Forall_app in HF. destruct HF as [_ HF].
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) str)) in HF. apply Forall_app in HF. tauto.
Qed.

Lemma tok_post_cases : forall K m0 tok e o st ms, tok_post K m0 tok e o st ms ->
  (tok = TK_eof /\ exists s0v, lex_at K m0 J_EOF s0v e o st ms) \/ (tok <> TK_eof /\ lex_at K m0 J_TOK (wz (tok_code tok)) e o st ms).
Proof. intros K m0 tok e o st ms H. destruct tok; first [left; split; [reflexivity| exact H] | right; split; [discriminate| exact H]]. Qed.

End RC__1.
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable K : lexK.
Hypothesis ENV : kenv K.

(* [comment removed for export] *)
Lemma lex_epilogue : forall (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
  rw_cells rsegs m (kSP K) (kframe K) ->
  evt rsegs (fun ms' => ms' = MS (mkR (k_ra K) (k_sp K) (k_gp K) (k_tp K) t0 t1 t2 (k_s0 K) (k_s1 K) a0 a1 a2 a3 a4 a5 a6 a7
                                     (k_s2 K) (k_s3 K) (k_s4 K) (k_s5 K) (k_s6 K) (k_s7 K) (k_s8 K) (k_s9 K) (k_s10 K) (k_s11 K) t3 t4 t5 t6)
                                (k_F K) (ret_pc (k_ra K)) (k_fc K) None m (seg_rom rsegs))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14e84) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until m. intros FR. pose proof ENV as ENV0. destruct ENV0.
  unfold kSP, kframe, lex_frame in *. unfold wz.
  do 13 zstep. zstep. zstep.
  replace (Z_to_bv 64 (bv_unsigned (k_sp K) - 128 + 128)) with (k_sp K) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lex_fin_walk : forall (tok : ytok) (rav s1v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m1 m : mem) (e1 off1 start1 : Z),
  tok <> TK_eof ->
  lexmem K m1 m e1 off1 ->
  rw_cells rsegs m (k_OBP K) [C8 (wz 0)] -> rw_cells rsegs m (k_OLP K) [C4 (wz 0)] ->
  bv_unsigned (k_sp K) <= k_OLP K -> k_OLP K + 4 <= k_OBP K -> k_OBP K + 8 <= 2^64 ->
  0 <= start1 <= off1 -> off1 <= zlength (k_txt K) -> (is_string_tok tok = true -> start1 + 2 <= off1) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR (k_ra K) (k_sp K) (k_gp K) (k_tp K) t0' t1' t2' (k_s0 K) (k_s1 K) (wz (tok_code tok)) a1' a2' a3' a4' a5' a6' a7'
                    (k_s2 K) (k_s3 K) (k_s4 K) (k_s5 K) (k_s6 K) (k_s7 K) (k_s8 K) (k_s9 K) (k_s10 K) (k_s11 K) t3' t4' t5' t6')
               (k_F K) (ret_pc (k_ra K)) (k_fc K) None m' (seg_rom rsegs)
      /\ munch (topW K) m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m' /\ stk rsegs m' (k_lo K) (bv_unsigned (k_sp K))
      /\ rw_cells rsegs m' (k_H K + 32) [C4 (wz off1)] /\ rw_cells rsegs m' (k_L K) (lxcells e1 (k_LB K) (kAF K))
      /\ rw_cells rsegs m' (k_LB K) (buf_cells ybuf_zero 0 (kAF K))
      /\ rw_cells rsegs m' (k_OBP K) [C8 (wz (outref_addr (k_T K) 0 (fst (fin_ob tok start1 off1))))]
      /\ rw_cells rsegs m' (k_OLP K) [C4 (wz (snd (fin_ob tok start1 off1)))])
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (tok_code tok)) s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start1) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz J_TOK) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until start1. intros NE LM OB OL SPL OLB OBB BS BO STR.
  pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). pose proof ENV as ENV0. lex_prep ENV0 BC. unfold J_TOK. unfold wz in FR, OB, OL.
  apply kW_topW in MU. unfold topW, kW, lexW in MU. cbn [app] in MU.
  pose proof (tok_code_range tok) as TR.
  zstep. rewrite ?ysx32_small by lia.
  zstep. if_cases K0; zify_cond K0. 2:{ kill K0. } clear K0.
  zstep. zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    assert (TE : tok = TK_error) by (destruct tok; cbn in K1; try lia; reflexivity). subst tok.
    eapply evt_mono; [eapply lex_epilogue; exact FR|].
    cbv beta. intros ms' ->. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
    split; [reflexivity|].
    release_frame FR STK (bv_unsigned (k_sp K)).
    cbn [fin_ob tok_eqb tok_code Z.eqb Pos.eqb fst snd outref_addr].
    repeat match goal with |- _ /\ _ => split end; assumption.
  - (* [comment removed for export] *)
    zstep. zstep. rewrite ?ysx32_small by lia. zstep. rewrite (land_M32_small start1) by lia.
    zstep. zstep. zstep.
    zstep. rewrite (swrap32_small (off1 - start1)) by lia || rewrite (swrap32_small (off1 + - start1)) by lia.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      assert (NS : is_string_tok tok = false).
      { rewrite <- land14_string. apply Z.eqb_neq. exact K2. }
      zstep.
      eapply evt_mono; [eapply lex_epilogue; exact FR|].
      cbv beta. intros ms' ->. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
      split; [reflexivity|].
      release_frame FR STK (bv_unsigned (k_sp K)).
      unfold fin_ob. rewrite NS. replace (tok_eqb tok TK_error) with false by (unfold tok_eqb; cbn [tok_code]; symmetry; apply Z.eqb_neq; lia).
      cbn [fst snd outref_addr].
      repeat match goal with |- _ /\ _ => split end; assumption.
    + assert (IS : is_string_tok tok = true).
      { rewrite <- land14_string. apply Z.eqb_eq. exact K2. }
      specialize (STR IS).
      zstep. rewrite ?ysx32_small by lia. zstep. zstep. if_cases K3; zify_cond K3. 1:{ kill K3. } clear K3.
      zstep. zstep. zstep. zstep. zstep. zstep.
      eapply evt_mono; [eapply lex_epilogue; exact FR|].
      cbv beta. intros ms' ->. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
      split; [reflexivity|].
      release_frame FR STK (bv_unsigned (k_sp K)).
      unfold fin_ob. rewrite IS. replace (tok_eqb tok TK_error) with false by (unfold tok_eqb; cbn [tok_code]; symmetry; apply Z.eqb_neq; lia).
      cbn [fst snd outref_addr].
      replace (k_T K + (start1 + 1)) with (k_T K + start1 + 1) by lia.
      replace (off1 - start1 - 2) with (off1 - start1 + -2) by lia.
      repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
Lemma lex_eof_head : forall (rav s0v s1v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m1 m : mem) (e1 off1 start1 : Z),
  lexmem K m1 m e1 off1 -> 0 <= start1 <= off1 -> off1 <= zlength (k_txt K) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR (wz 0x14dfc) (wz (kSP K)) (k_gp K) (k_tp K) t0' t1' t2' (wz 3) s1v
                    (wz (k_LB K)) (wz (k_T K + start1)) (wz (off1 - start1)) a3' a4' a5' a6' a7'
                    (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz 1) (wz start1) s7v s8v s9v s10v s11v t3' t4' t5' t6')
               (k_F K) (wz RY_BUF_APPEND) (k_fc K) None m' (seg_rom rsegs)
      /\ munch (kW K) m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m' /\ stk rsegs m' (k_lo K) (kSP K)
      /\ rw_cells rsegs m' (kSP K) (kframe K) /\ rw_cells rsegs m' (k_H K + 32) [C4 (wz off1)]
      /\ rw_cells rsegs m' (k_L K) [C4 (wz 0); C4 (wz 0); C4 (wz e1); C4 (wz 0); C8 (wz (k_LB K)); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 1); C8 (wz (kAF K))]
      /\ rw_cells rsegs m' (k_LB K) (buf_cells ybuf_zero 0 (kAF K)))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start1) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz J_EOF) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until start1. intros LM BS BO.
  pose proof LM as (MU & WM & MI & STK & FR & OFF & LX & BC). pose proof ENV as ENV0. lex_prep ENV0 BC. unfold J_EOF, RY_BUF_APPEND.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned (k_sp K) - 128)) = bv_unsigned (k_sp K) - 128) by (apply unsigned_lit; lia).
  zstep. rewrite ?ysx32_small by lia. zstep. zstep.
  zstep. if_cases KB; zify_cond KB. 1:{ kill KB. } clear KB.
  zstep.
  zstep. call (buf_clear_null_walk (k_LB K) (k_H K + 72) (k_lo K)).
  { exact BC. }
  { lia. }
  { lia. }
  { rewrite ESP. exact STK. }
  { rewrite ESP. lia. }
  { lia. }
  { lia. }
  { exact MI. }
  { reflexivity. }
  lazymatch goal with H : stk _ _ _ _ |- _ => rewrite ESP in H; rename H into STK' end.
  lazymatch goal with H : rw_cells _ _ (k_LB K) _ |- _ => rename H into BC' end.
  unfold buf_cells in BC'. cbn [yb_len yb_data ybuf_zero buf_state_code yb_state yb_used] in BC'.
  zstep. zstep. zstep. zstep. rewrite ?ysx32_small by lia. zstep. zstep. rewrite (land_M32_small start1) by lia.
  zstep. zstep. rewrite (swrap32_small (off1 - start1)) by lia || rewrite (swrap32_small (off1 + - start1)) by lia.
  zstep.
  apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
  unfold kW, lexW, kframe, lex_frame, buf_cells. cbn [buf_state_code yb_state yb_len yb_used ybuf_zero].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Hypothesis YBE : ybuf_err_stmt.

(* [comment removed for export] *)
Definition eof_err (st e1 : Z) : Z := if st =? 0 then e1 else 11.
Definition eof_ret (st : Z) : Z := if st =? 0 then 3 else 4.

Lemma lex_eof_tail : forall (rav s1v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m : mem) (e1 off1 start1 st LB bl bu bd ba : Z),
  let rest := [C4 (wz bl); C4 (wz bu); C4 (wz 0); C8 (wz bd); C8 (wz ba)] in
  rw_cells rsegs m (kSP K) (kframe K) ->
  rw_cells rsegs m (k_L K) [C4 (wz 0); C4 (wz 0); C4 (wz e1); C4 (wz 0); C8 (wz LB); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 1); C8 (wz (kAF K))] ->
  rw_cells rsegs m LB (C4 (wz st) :: rest) -> 0 <= st <= 2 -> 0 < LB -> LB + 32 <= alloc_ceiling ->
  (k_L K + 48 <= LB \/ LB + 32 <= k_L K) ->
  stk rsegs m (k_lo K) (kSP K) -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR (k_ra K) (k_sp K) (k_gp K) (k_tp K) t0' t1' t2' (k_s0 K) (k_s1 K) (wz (eof_ret st)) a1' a2' a3' a4' a5' a6' a7'
                    (k_s2 K) (k_s3 K) (k_s4 K) (k_s5 K) (k_s6 K) (k_s7 K) (k_s8 K) (k_s9 K) (k_s10 K) (k_s11 K) t3' t4' t5' t6')
               (k_F K) (ret_pc (k_ra K)) (k_fc K) None m' (seg_rom rsegs)
      /\ munch [(k_L K, k_L K + 48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (k_lo K) (bv_unsigned (k_sp K))
      /\ rw_cells rsegs m' (k_L K) [C4 (wz 0); C4 (wz 0); C4 (wz (eof_err st e1)); C4 (wz 0); C8 (wz LB); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 1); C8 (wz (kAF K))]
      /\ rw_cells rsegs m' LB (C4 (wz st) :: rest))
    (MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz 3) s1v a0 a1 a2 a3 a4 a5 a6 a7
          (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz 1) (wz start1) s7v s8v s9v s10v s11v t3 t4 t5 t6)
        (k_F K) (wz 0x14dfc) (k_fc K) None m (seg_rom rsegs)).
Proof.
  intros until ba. cbv zeta. intros FR LX BC STR LBP LBC SEP STK MI.
  pose proof ENV as ENV0. destruct ENV0. unfold kSP, kAF, kframe, lex_frame in *. unfold wz. unfold alloc_ceiling in *.
  unfold wz in FR, LX, BC.
  pose proof (munch_refl [(k_L K, k_L K + 48)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep.
  zstep. call (YBE LB st [C4 (Z_to_bv 64 bl); C4 (Z_to_bv 64 bu); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 bd); C8 (Z_to_bv 64 ba)]).
  { exact BC. }
  { lia. }
  { lia. }
  { assumption. }
  { reflexivity. }
  lazymatch goal with H : ?x = wz st |- _ => subst x end.
  lazymatch goal with H : @eq mem ?x ?y |- _ => first [subst y| subst x] end.
  unfold wz. zstep. if_cases K5; zify_cond K5.
  - (* [comment removed for export] *)
    zstep. if_cases K6; zify_cond K6. 1:{ kill K6. } clear K6.
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. cbn in K7. lia. } clear K7.
    zstep.
    eapply evt_mono; [eapply lex_epilogue; exact FR|].
    cbv beta. intros ms' ->. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
    unfold eof_ret, eof_err. replace (st =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    split; [reflexivity|].
    release_frame FR STK (bv_unsigned (k_sp K)).
    repeat match goal with |- _ /\ _ => split end; assumption.
  - (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    eapply evt_mono; [eapply lex_epilogue; exact FR|].
    cbv beta. intros ms' ->. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
    unfold eof_ret, eof_err. replace (st =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    split; [reflexivity|].
    release_frame FR STK (bv_unsigned (k_sp K)).
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
End S.
End RC__2.

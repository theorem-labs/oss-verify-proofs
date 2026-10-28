(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_arrlA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition arr_W (q out : Z) : list (Z * Z) := [(q + -96, q); (out, out + 24)].

Definition arr_frame (ra s0 s1 s2 s3 s4 s5 s6 : word) (j0 jc : list byte) : list cell :=
  [CB 8 j0; CB 24 jc; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition arr_set_site (ra' : Z) (s1' s2' : word) (out : Z) : Prop :=
  (ra' = 0xb6a94 /\ s1' = Z_to_bv 64 (out + 16))
  \/ (ra' = 0xb6b94 /\ s1' = Z_to_bv 64 (out + 16) /\ exists code, s2' = Z_to_bv 64 code /\ (code = 17 \/ code = 19 \/ code = 22))
  \/ (ra' = 0xb6a40 /\ s1' = Z_to_bv 64 (out + 16))
  \/ (ra' = 0xb6ca4 /\ s2' = Z_to_bv 64 (out + 16)).

Section ArrWalks.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Definition arr_x1 (ptr : list Z) (i e : Z) (q out node P : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte) : machine_state -> Prop :=
    fun ms => exists (m1 : mem) (j0 jc : list byte),
      munch (arr_W q out) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\
      (
        (exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
           ms = entry_st (wz 0xb6a64) (wz (q + -96)) gp (wz TPV) t0' t1' t2' (wz out) s1 (wz out) (wz node) (wz 16) a3' a4' a5' a6' a7'
                         s2 (wz 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc e_asan_memcpy m1
           /\ ptr = [] /\ stk asegs m1 (ae_lo E) (q + -96) /\ rw_cells asegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc)
           /\ rw_cells asegs m1 out [CB 24 jo])
     \/
        (exists (ra' : Z) (t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s4' s5' s6' t3' t4' t5' t6' : word),
           ms = entry_st (wz ra') (wz (q + -96)) gp (wz TPV) t0' t1' t2' (wz out) s1' (wz out) (wz 0) (wz 16) a3' a4' a5' a6' a7'
                         s2' (wz 2147450880) s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc e_asan_memset m1
           /\ arr_set_site ra' s1' s2' out
           /\ stk asegs m1 (ae_lo E) (q + -96) /\ rw_cells asegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc)
           /\ rw_cells asegs m1 out [CB 24 jo])
     \/
        (exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (jo' : list byte),
           ms = MS (mkR ra (wz q) gp (wz TPV) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
           /\ stk asegs m1 (ae_lo E) q /\ rw_cells asegs m1 out [CB 24 jo'])
     \/
        (exists (it j' tok : Z) (r : list Z) (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (od : list byte),
           ms = lvl_entry ATP_ELEM_A (wz 0xb6dcc) (q + -96) gp t0' t1' t2' (wz out) (wz (P + 1)) (q + -88) out (P + 1 + tok) (zlength (47 :: r))
                   a4' a5' a6' a7' (wz (out + 16)) (wz ((out + 16) / 8 + 2147450880)) (wz (zlength ptr - 1)) (wz 47) (wz tok) s7 s8 s9 s10 s11
                   t3' t4' t5' t6' F fc m1
           /\ elem (ae_T E) (ae_S E) (ae_sn E) ck_any d it j' /\ 0 <= it /\ j' <= e /\ ptr_atA E (P + 1 + tok) (47 :: r) /\ 0 <= tok
           /\ zlength (47 :: r) = zlength ptr - 1 - tok
           /\ stk asegs m1 (ae_lo E) (q + -96) /\ rw_cells asegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc)
           /\ rw_cells asegs m1 out [C8 (wz (ae_DOC E)); C8 (wz it); C4 (wz 0); CB 4 od]) ).

  Lemma arr_epi : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q lo : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j0 jc : list byte)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc) -> stk asegs m lo (q + -96) -> mem_inv asegs m -> lo <= q + -96 ->
    (forall (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word), stk asegs m lo q ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz (q + -96)) gp (wz TPV) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz 0xb6ba8) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros FR ST MI LO HK. unfold arr_frame in FR.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 8 step. step.
    release_frame FR ST q.
    step. apply evt_done. apply HK. exact ST.
  Qed.

  Lemma arr_xset : forall (ptr : list Z) (i e q out node P : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (jo j0 jc : list byte) (pc ra' : Z)
      (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    munch (arr_W q out) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 (ae_lo E) (q + -96) ->
    rw_cells asegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc) -> rw_cells asegs m1 out [CB 24 jo] ->
    ((pc = 0xb6b80 /\ ra' = 0xb6b94 /\ exists code, x18 = Z_to_bv 64 code /\ (code = 17 \/ code = 19 \/ code = 22))
     \/ (pc = 0xb6a80 /\ ra' = 0xb6a94) \/ (pc = 0xb6a2c /\ ra' = 0xb6a40) \/ (pc = 0xb6c90 /\ ra' = 0xb6ca4)) ->
    evt asegs (arr_x1 ptr i e q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
      (MS (mkR ra (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 (wz 2147450880) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (wz pc) fc None m1 (seg_rom asegs)).
  Proof.
    intros until x31. intros MU WM MI ST FR OUT CASES.
    destruct CASES as [(-> & -> & CODE)|[(-> & ->)|[(-> & ->)|(-> & ->)]]];
      (do 5 step; apply evt_done; exists m1, j0, jc; split; [exact MU|]; split; [exact WM|]; split; [exact MI|];
       right; left; eexists _; do 17 eexists; split; [unfold entry_st, e_asan_memset; atp_st_eq_goal|];
       split; [| split; [exact ST| split; [exact FR| exact OUT]]]; unfold arr_set_site).
    - right; left. split; [reflexivity|]. split; [reflexivity| exact CODE].
    - left. split; reflexivity.
    - right; right; left. split; reflexivity.
    - right; right; right. split; reflexivity.
  Qed.

  Lemma arr_found : forall (c1 : Z) (ptr1 : list Z) (i e q out node P tok c3 it j' : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (jo j0 jc : list byte) (xa1 xa4 xt2 xt3 xt4 xt5 xt6 : word),
    munch (arr_W q out) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 (ae_lo E) (q + -96) -> ae_lo E <= q + -96 ->
    rw_cells asegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc) -> rw_cells asegs m1 out [CB 24 jo] ->
    q <= out -> out + 24 <= ae_hi E -> 0 <= P -> P + zlength ptr1 + 2 <= ae_lo E ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' out 24) ->
    ptr_atA E P (47 :: c1 :: ptr1) ->
    0 <= tok <= zlength ptr1 + 1 -> (forall j, (j < Z.to_nat tok)%nat -> nth j (c1 :: ptr1) 0 <> 47) ->
    ((c3 = 47 /\ tok < zlength ptr1 + 1 /\ nth (Z.to_nat tok) (c1 :: ptr1) 0 = 47) \/ (c3 <> 47 /\ tok = zlength ptr1 + 1)) -> 0 <= c3 < 256 ->
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any d it j' -> 0 <= it -> j' <= e ->
    evt asegs (arr_x1 (47 :: c1 :: ptr1) i e q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
      (MS (mkR ra (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) xt2
               (Z_to_bv 64 out) (Z_to_bv 64 (P + 1)) (Z_to_bv 64 (ae_DOC E)) xa1 (Z_to_bv 64 it) (Z_to_bv 64 (ae_TAPE E)) xa4 (Z_to_bv 64 e)
               (Z_to_bv 64 32) (Z_to_bv 64 4294967295) (Z_to_bv 64 22) (Z_to_bv 64 2147450880) (Z_to_bv 64 (zlength ptr1 + 1)) (Z_to_bv 64 c3) (Z_to_bv 64 tok)
               s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xb6d50) fc None m1 (seg_rom asegs)).
  Proof.
    intros until xt6. intros MU WM MI ST LO FR OUT QO OB P0 PL SHZO PAT TOK NOSL2 DISJ C3R EL' IT0 JE.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ _ [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (elem_lt _ _ _ _ _ _ _ EL') as IJ'. pose proof (zlength_nonneg ptr1) as ZL1.
    unfold arr_W in MU. unfold arr_frame in FR.
    apply (rw_cells_split_CB asegs _ _ [] 24 jo [] [8; 8; 4; 4]%nat) in OUT; [| reflexivity]. cbn [mk_CB_cells app] in OUT.

    chk0 SHZO out. step. if_false. step.
    astep. chk0 SHZO (out + 8). step. if_false. step.
    astep. chk0 SHZO (out + 16). step. if_false. lstep.
    name_mem mF.

    astep. chk0 SHZO (out + 16). step. if_false. astep. step. if_cases KR; zify_cond KR.
    {
      apply arr_epi with (lo := ae_lo E) (ra := ra) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (j0 := j0) (jc := jc);
        [unfold arr_frame; exact FR| exact ST| exact MI| lia|].
      intros until y31. intros ST'.
      destruct (rw_cells_forget _ _ _ _ OUT) as [jo' OUT']. cbn [cells_size csize Nat.add] in OUT'.
      exists mF, j0, jc. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      right; right; left. do 15 eexists. exists jo'. split; [atp_st_eq_goal|]. split; [exact ST'| exact OUT']. }

    destruct DISJ as [(C47 & TKL & SL)|(X & _)]; [| exfalso; exact (X KR)]. subst c3.
    astep. step. if_false.
    astep. astep. astep. step. step.
    assert (TKN : (Z.to_nat tok < length (c1 :: ptr1))%nat) by (unfold zlength in TKL; cbn [length]; lia).
    assert (PAT2 : ptr_atA E (P + 1 + tok) (47 :: skipn (S (Z.to_nat tok)) (c1 :: ptr1))).
    { pose proof (ptr_atA_skip E P (47 :: c1 :: ptr1) (S (Z.to_nat tok)) PAT ltac:(cbn [length] in *; lia)) as X.
      change (skipn (S (Z.to_nat tok)) (47 :: c1 :: ptr1)) with (skipn (Z.to_nat tok) (c1 :: ptr1)) in X.
      rewrite (skipn_cons_nth _ _ TKN), SL in X. replace (P + Z.of_nat (S (Z.to_nat tok))) with (P + 1 + tok) in X by lia. exact X. }
    assert (ZR : zlength (47 :: skipn (S (Z.to_nat tok)) (c1 :: ptr1)) = zlength ptr1 + 1 - tok).
    { rewrite zlength_cons, zlength_skipn by (cbn [length] in *; lia). rewrite zlength_cons. lia. }
    apply evt_done. exists mF, j0, jc. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    right; right; right. exists it, j', tok, (skipn (S (Z.to_nat tok)) (c1 :: ptr1)). do 11 eexists. eexists.
    split; [unfold lvl_entry; rewrite ZR, !zlength_cons; atp_st_eq_goal|].
    split; [exact EL'|]. split; [exact IT0|]. split; [exact JE|]. split; [exact PAT2|]. split; [lia|]. split; [rewrite ZR, !zlength_cons; lia|].
    split; [exact ST|]. split; [unfold arr_frame; exact FR| exact OUT].
  Qed.

  Lemma arr_tok : forall (c1 : Z) (ptr1 : list Z) (i e c q out node P tok c3 : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (jo j0 jc : list byte) (xa0 xa2 xa4 xt4 xt5 xt6 : word),
    munch (arr_W q out) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 (ae_lo E) (q + -96) -> ae_lo E <= q + -96 ->
    rw_cells asegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc) -> rw_cells asegs m1 out [CB 24 jo] ->
    q <= out -> out + 24 <= ae_hi E -> 0 <= P -> P + zlength ptr1 + 2 <= ae_lo E ->
    rw_cells asegs m1 node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= node -> node + 16 <= ae_hi E ->
    AINV_A E m1 ->
    ty (ae_T E) i = t_arr -> tnext (ae_T E i) = e + 1 -> tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d) (i + 1) e c -> 0 <= i -> e + 1 <= ae_n E - 1 ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' node 16) ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' out 24) ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    ptr_atA E P (47 :: c1 :: ptr1) ->
    0 <= tok <= zlength ptr1 + 1 -> (forall j, (j < Z.to_nat tok)%nat -> nth j (c1 :: ptr1) 0 <> 47) ->
    ((c3 = 47 /\ tok < zlength ptr1 + 1 /\ nth (Z.to_nat tok) (c1 :: ptr1) 0 = 47) \/ (c3 <> 47 /\ tok = zlength ptr1 + 1)) -> 0 <= c3 < 256 ->
    evt asegs (arr_x1 (47 :: c1 :: ptr1) i e q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
      (MS (mkR ra (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) (Z_to_bv 64 10) (Z_to_bv 64 ((P + 1) / 8 + 2147450880)) (Z_to_bv 64 ((P + 1) mod 8))
               (Z_to_bv 64 out) (Z_to_bv 64 (P + 1)) xa0 (Z_to_bv 64 node) xa2 (Z_to_bv 64 (- (zlength ptr1 + 1))) xa4 (Z_to_bv 64 47) (Z_to_bv 64 9)
               (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 22) (Z_to_bv 64 2147450880) (Z_to_bv 64 (zlength ptr1 + 1)) (Z_to_bv 64 c3) (Z_to_bv 64 tok)
               s7 s8 s9 s10 s11 (Z_to_bv 64 48) xt4 xt5 xt6)
          F (Z_to_bv 64 0xb6bd4) fc None m1 (seg_rom asegs)).
  Proof.
    intros until xt6. intros MU WM MI ST LO FR OUT QO OB P0 PL NODE QN NB AI1 TY NXT TILES I0 EN SHZN SHZO SHZD SHZT PAT TOK NOSL2 DISJ C3R.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ [T16 [NT8 [TN [TS TL]]]] _ _ _ [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TILES) as [IE CC].
    pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
    unfold ty in TY. pose proof (ttype_range _ _ TY ltac:(unfold t_arr; lia) ltac:(unfold t_arr; lia)) as TIR.
    unfold arr_W in MU. unfold arr_frame in FR. hide TAPEB.

    chk0 SHZN node. step. if_false.
    astep. chk0 SHZN (node + 8). step. if_false.
    step. chk0 SHZD (ae_DOC E). step. if_false.
    step. step.

    astep. astep. chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.
    step. astep. astep. rewrite TY. unfold t_arr. astep.

    astep. step. step. if_false. astep. astep. astep. astep. step. if_true.

    astep. astep. astep. astep. astep. step. step. if_false. astep. astep. rewrite ?land32_tnext, ?mod32_tnext by lia. rewrite NXT.

    astep. step. if_cases KE; zify_cond KE.
    2: {
         eapply arr_xset; [exact MU| exact WM| exact MI| exact ST| unfold arr_frame; exact FR| exact OUT| right; right; right; split; reflexivity]. }

    do 9 astep.
    lazymatch goal with |- evt _ ?K _ =>
    eapply evt_eq; [| eapply (arr_iter_loopA E OK d K m1 F fc e c (q + -96) ra gp (Z_to_bv 64 out) (Z_to_bv 64 (P + 1)) (Z_to_bv 64 (ae_DOC E))
                               (Z_to_bv 64 22) (Z_to_bv 64 (zlength ptr1 + 1)) (Z_to_bv 64 c3) (Z_to_bv 64 tok) s7 s8 s9 s10 s11 xt4
                               ltac:(unhide TAPEB; exact TAPEB) EN MI (SHZT m1 MU WM) ltac:(lia) ltac:(lia)) with (n := S (Z.to_nat (e - (i + 1)))) (it := i + 1) (c' := c)];
      [atp_st_eq| | | exact TILES| exact KE| lia| lia]
    end.
    -   intros it j' xa1' xa4' xt2' xt3' xt5' xt6' EL' IT0 JE.
      eapply arr_found; eassumption.
    -   intros.
      eapply arr_xset; [exact MU| exact WM| exact MI| exact ST| unfold arr_frame; exact FR| exact OUT| right; right; right; split; reflexivity].
  Qed.

  Lemma arr_scan : forall (c1 : Z) (ptr1 : list Z) (i e c q out node P : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (jo j0 jc : list byte) (x5 x7 xa0 xa2 xa5 xa6 xa7 x20 x21 x22 x28 x29 x30 x31 : word),
    munch (arr_W q out) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 (ae_lo E) (q + -96) -> ae_lo E <= q + -96 ->
    rw_cells asegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc) -> rw_cells asegs m1 out [CB 24 jo] ->
    q <= out -> out + 24 <= ae_hi E -> 0 <= P -> P + zlength ptr1 + 2 <= ae_lo E ->
    rw_cells asegs m1 node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= node -> node + 16 <= ae_hi E ->
    AINV_A E m1 ->
    ty (ae_T E) i = t_arr -> tnext (ae_T E i) = e + 1 -> tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d) (i + 1) e c -> 0 <= i -> e + 1 <= ae_n E - 1 ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' node 16) ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' out 24) ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    acc asegs m1 (ae_PB E) (ae_NPB E) -> ae_PB E <= P -> P + zlength ptr1 + 2 <= ae_PB E + ae_NPB E ->
    ptr_atA E P (47 :: c1 :: ptr1) -> bytes_at asegs m1 (P + 1) (map (Z_to_bv 8) (c1 :: ptr1)) -> Forall (fun c => 0 <= c < 256) (c1 :: ptr1) ->
    evt asegs (arr_x1 (47 :: c1 :: ptr1) i e q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
      (MS (mkR ra (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) x5 (Z_to_bv 64 ((P + 1) / 8)) x7 (Z_to_bv 64 out) (Z_to_bv 64 (P + 1))
               xa0 (Z_to_bv 64 node) xa2 (Z_to_bv 64 (zlength ptr1 + 1 + 1)) (Z_to_bv 64 47) xa5 xa6 xa7
               (Z_to_bv 64 22) (Z_to_bv 64 2147450880) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xb6ab0) fc None m1 (seg_rom asegs)).
  Proof.
    intros until x31. intros MU WM MI ST LO FR OUT QO OB P0 PL NODE QN NB AI1 TY NXT TILES I0 EN SHZN SHZO SHZD SHZT ACC PB1 PB2 PAT RB1 RF1.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (zlength_nonneg ptr1) as ZL1.
    unfold arr_W in MU. unfold arr_frame in FR.

    assert (ROC : ro_cells asegs m1 0x10380 [CB 8 [Z_to_bv 8 205; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204]]).
    { apply (ro_cells_image asegs m1); [exact MI| vm_compute; reflexivity| lia| cbn; lia]. }

    do 6 astep. step. astep. step. astep. astep. astep. astep. step. step.
    lazymatch goal with |- evt _ ?K _ =>
    eapply evt_eq; [| eapply (arr_digit_loopA K m1 F fc (c1 :: ptr1) (P + 1) (zlength ptr1 + 1) (- (zlength ptr1 + 1)) (q + -96) out (ae_PB E) (ae_NPB E)
                               ra gp (Z_to_bv 64 node) (Z_to_bv 64 14757395258967641293) s7 s8 s9 s10 s11
                               RB1 RF1 ltac:(rewrite zlength_cons; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) MI ACC ltac:(lia) ltac:(lia))
                        with (n := S (length (c1 :: ptr1))) (cnt := 0)];
      [atp_st_eq| | | lia| unfold zlength; cbn [length]; lia| intros j Hj; lia]
    end.
    -
      intros code xa0' xa2' xa4' xs5' xs6' xt4' xt5' xt6' CODE.
      eapply arr_xset; [exact MU| exact WM| exact MI| exact ST| unfold arr_frame; exact FR| exact OUT|].
      left. split; [reflexivity|]. split; [reflexivity|]. exists code. split; [reflexivity| exact CODE].
    -
      intros tok c3 xa0' xa2' xa4' xt4' xt5' xt6' TOK NOSL2 DISJ C3R.
      eapply arr_tok; eassumption.
  Qed.

  Lemma arr_walk1 : forall (ptr : list Z) (i e c q out node P : Z)
      (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    ptr_atA E P ptr -> ty (ae_T E) i = t_arr -> tnext (ae_T E i) = e + 1 ->
    tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d) (i + 1) e c -> 0 <= i -> e + 1 <= ae_n E - 1 ->
    AINV_A E m ->
    rw_cells asegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= node -> node + 16 <= ae_hi E ->
    rw_cells asegs m out [CB 24 jo] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> (node + 16 <= out \/ out + 24 <= node) ->
    mem_inv asegs m -> stk asegs m (ae_lo E) q -> ae_lo E + 96 <= q -> q mod 16 = 0 -> shb_cells m ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' node 16) ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' out 24) ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    (ptr <> [] -> forall m', munch (arr_W q out) m m' -> wmono asegs m m' -> acc asegs m' (ae_PB E) (ae_NPB E)) ->
    evt asegs (arr_x1 ptr i e q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
      (lvl_entry ATP_ARR_A ra q gp t0 t1 t2 s0 s1 out node P (zlength ptr) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Proof.
    intros until jo. intros PAT TY NXT TILES I0 EN AI NODE QN NB OUT QO OB O8 NO MI ST LO Q16 [G1 G2] SHZN SHZO SHZD SHZT ACCP.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold lvl_entry, ATP_ARR_A, ATP_ELEM_A in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (PTRB & PTRF & PP0 & PP1 & PL).
    pose proof (zlength_nonneg ptr) as ZL. pose proof (zlength_nonneg (ae_p1 E)) as ZL1.
    assert (PR : ptr <> [] -> 0 < ae_PB E /\ ae_PB E <= P /\ P + zlength ptr <= ae_PB E + ae_NPB E /\ ae_PB E + ae_NPB E <= ae_lo E).
    { intros NE. assert (NE1 : ae_p1 E <> []).
      { destruct PAT as (pre & Ep & _). intros E0. rewrite E0 in Ep. destruct pre; [cbn in Ep; exact (NE (eq_sym Ep))| discriminate Ep]. }
      specialize (PTRR NE1). lia. }
    pose proof (munch_refl (arr_W q out) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold arr_W in MU.
    hide AI. clear PTRB.

    step. carve_frame 96%nat ST.
    apply (rw_cells_split_CB asegs _ _ [] 96 junk [] [8; 24; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    set (j0 := firstn 8 junk) in FR. set (jc := firstn 24 (skipn 8 junk)) in FR. clearbody j0 jc.
    repeat match type of FR with context [CB 8 (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    do 8 step. step. step. step. step.
    name_mem m1.
    assert (AI1 : AINV_A E m1).
    { unhide AI. apply (AINV_A_munch E _ m m1 OK AI MU). constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
    assert (PTRBm : bytes_at asegs m1 P (map (Z_to_bv 8) ptr)).
    { exact (proj1 (ptr_atA_facts E P ptr m1 OK PAT (proj1 (proj2 (proj2 AI1))))). }
    hide AI1.

    step. if_cases K0; zify_cond K0.
    {
      step. step. step.
      apply evt_done. exists m1, j0, jc. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      left. do 12 eexists. split; [unfold entry_st, e_asan_memcpy; atp_st_eq_goal|].
      split; [destruct ptr as [|cx lx]; [reflexivity| exfalso; rewrite zlength_cons in K0; pose proof (zlength_nonneg lx); lia]|].
      split; [exact ST|]. split; [exact FR| exact OUT]. }
    destruct ptr as [|c0 ptr0]; [exfalso; apply K0; reflexivity|].
    assert (NE0 : c0 :: ptr0 <> []) by discriminate. specialize (PR NE0). specialize (ACCP NE0). destruct PR as (PB0 & PB1 & PB2 & PB3).
    assert (C0R : 0 <= c0 < 256) by (inversion PTRF; assumption).
    rewrite zlength_cons in *. pose proof (zlength_nonneg ptr0) as ZL0.
    pose proof (zbytes_read1 m1 P (c0 :: ptr0) 0 PTRBm ltac:(rewrite zlength_cons; lia)) as RD0.
    change (nth (Z.to_nat 0) (c0 :: ptr0) 0) with c0 in RD0. rewrite Z.add_0_r in RD0.

    assert (J64 : forall xa0 xa4 : word,
      evt asegs (arr_x1 (c0 :: ptr0) i e q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
        (MS (mkR ra (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) t0 t1 t2 (Z_to_bv 64 out) s1 xa0 (Z_to_bv 64 node) (Z_to_bv 64 P)
                 (Z_to_bv 64 (zlength ptr0 + 1)) xa4 a5 a6 a7 s2 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xb69ec) fc None m1 (seg_rom asegs))).
    { intros xa0 xa4.

      astep. astep. step. if_cases K1; zify_cond K1.
      {
        eapply arr_xset; [exact MU| exact WM| exact MI| exact ST| unfold arr_frame; exact FR| exact OUT| right; left; split; reflexivity]. }
      subst c0.

      astep. astep. step. if_cases K2; zify_cond K2.
      {
        eapply arr_xset; [exact MU| exact WM| exact MI| exact ST| unfold arr_frame; exact FR| exact OUT|].
        left. split; [reflexivity|]. split; [reflexivity|]. exists 22. split; [reflexivity| lia]. }
      destruct ptr0 as [|c1 ptr1]; [exfalso; rewrite zlength_nil in K2; lia|].
      assert (C1R : 0 <= c1 < 256) by (inversion PTRF as [|? ? _ X]; inversion X; assumption).
      rewrite zlength_cons in *. pose proof (zlength_nonneg ptr1) as ZL1'.
      pose proof (zbytes_read1 m1 P (47 :: c1 :: ptr1) 1 PTRBm ltac:(rewrite !zlength_cons; lia)) as RD1.
      change (nth (Z.to_nat 1) (47 :: c1 :: ptr1) 0) with c1 in RD1.
      assert (RB1 : bytes_at asegs m1 (P + 1) (map (Z_to_bv 8) (c1 :: ptr1))).
      { pose proof (bytes_at_skipn _ _ _ 1 PTRBm ltac:(cbn; lia)) as X. exact X. }
      assert (RF1 : Forall (fun c => 0 <= c < 256) (c1 :: ptr1)) by (inversion PTRF; assumption).
      assert (AT928 : forall xa0' xa2' : word,
        evt asegs (arr_x1 (47 :: c1 :: ptr1) i e q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
          (MS (mkR ra (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) t0 (Z_to_bv 64 ((P + 1) / 8)) t2 (Z_to_bv 64 out) (Z_to_bv 64 (P + 1))
                   xa0' (Z_to_bv 64 node) xa2' (Z_to_bv 64 (zlength ptr1 + 1 + 1)) (Z_to_bv 64 47) a5 a6 a7
                   (Z_to_bv 64 22) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0xb6ab0) fc None m1 (seg_rom asegs))).
      { intros xa0' xa2'. unhide AI1.
        apply (arr_scan c1 ptr1 i e c q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 jo j0 jc
                 t0 t2 xa0' xa2' a5 a6 a7 s4 s5 s6 t3 t4 t5 t6);
          [ exact MU| exact WM| exact MI| exact ST| lia| exact FR| exact OUT| exact QO| lia| lia| lia| exact NODE| lia| lia| exact AI1
          | exact TY| exact NXT| exact TILES| exact I0| exact EN| exact SHZN| exact SHZO| exact SHZD| exact SHZT
          | exact (ACCP m1 MU WM)| lia| lia| exact PAT| exact RB1| exact RF1]. }

      astep. astep. astep. step. if_cases K3; zify_cond K3.
      { eapply evt_eq; [| eapply AT928]; [atp_st_eq]. }

      assert (J98 : forall ya0 ya2 : word,
        evt asegs (arr_x1 (47 :: c1 :: ptr1) i e q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
          (MS (mkR ra (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) t0 (Z_to_bv 64 ((P + 1) / 8)) t2 (Z_to_bv 64 out) (Z_to_bv 64 (P + 1))
                   ya0 (Z_to_bv 64 node) ya2 (Z_to_bv 64 (zlength ptr1 + 1 + 1)) (Z_to_bv 64 47) a5 a6 a7
                   (Z_to_bv 64 22) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0xb6a20) fc None m1 (seg_rom asegs))).
      { intros ya0 ya2.

        astep. astep. step. if_cases K4; zify_cond K4.
        - eapply evt_eq; [| eapply AT928]; [atp_st_eq].
        - eapply arr_xset; [exact MU| exact WM| exact MI| exact ST| unfold arr_frame; exact FR| exact OUT| right; right; left; split; reflexivity]. }
      destruct (acc_read1 m1 (ae_PB E) (ae_NPB E) (P + 1) (ACCP m1 MU WM) ltac:(lia)) as (b1 & RDS1 & OK1).
      destruct (sh_ok_cases b1 (P + 1) OK1) as [-> | (k1 & -> & K1 & KM1)].
      - astep. step. shz_norm. step. if_false. eapply evt_eq; [| eapply J98]; [atp_st_eq].
      - astep. step. rewrite (sxb_small7 k1) by lia. step. if_lia. astep. step. if_lia. eapply evt_eq; [| eapply J98]; [atp_st_eq]. }

    destruct (acc_read1 m1 (ae_PB E) (ae_NPB E) P (ACCP m1 MU WM) ltac:(lia)) as (b0 & RDS0 & OK0).
    destruct (sh_ok_cases b0 P OK0) as [-> | (k0 & -> & K0x & KM0)].
    - astep. astep. step. shz_norm. step. if_false. eapply evt_eq; [| eapply J64]; [atp_st_eq].
    - astep. astep. step. rewrite (sxb_small7 k0) by lia. step. if_lia. astep. step. if_lia. eapply evt_eq; [| eapply J64]; [atp_st_eq].
  Qed.
End ArrWalks.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition elem_W (q out : Z) : list (Z * Z) := [(q + -80, q); (out, out + 24)].
Definition elem_WO (out : Z) : list (Z * Z) := [(out, out + 24)].

Definition elem_frame (ra s0 s1 s2 s3 : word) (j0 jn : list byte) : list cell :=
  [CB 8 j0; CB 16 jn; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition elem_set_site (ra' code : Z) : Prop := (ra' = 0xb37e0 /\ code = 22) \/ (ra' = 0xb378c /\ code = 20).

Lemma tix_shr61 : forall i, 0 <= i < 2^60 -> Z.shiftr (i + 1152921504606846976) 61 = 0.
Proof. intros i Hi. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Lemma frame_join16 : forall (m : mem) A c (ca cb : list byte) rest,
  rw_cells asegs m A (c :: CB 8 ca :: CB 8 cb :: rest) -> rw_cells asegs m A (c :: CB 16 (ca ++ cb) :: rest).
Proof.
  intros m A c ca cb rest H. eapply rw_cells_recastA; [exact H| | cbn [cells_bytes cbytes]; rewrite <- app_assoc; reflexivity].
  destruct H as [[W _] _]. cbn [cells_wf cell_wf] in W |- *. destruct W as (Wc & La & Lb & Wr).
  split; [exact Wc|]. split; [rewrite length_app; rewrite La, Lb; reflexivity| exact Wr].
Qed.

Section ElemWalks.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Definition elem_x1 (ptr : list Z) (i : Z) (q out node P : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte) : machine_state -> Prop :=
    fun ms => exists (m1 : mem) (j0 jn : list byte),
      munch (elem_W q out) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 out [CB 24 jo] /\
      stk asegs m1 (ae_lo E) (q + -64) /\ rw_cells asegs m1 (q + -64) (elem_frame ra s0 s1 s2 s3 j0 jn) /\
      exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      (
        (ms = entry_st (wz 0xb37b0) (wz (q + -64)) gp (wz TPV) t0' t1' t2' (wz out) (wz P) (wz out) (wz node) (wz 16) a3' a4' a5' a6' a7'
                       (wz 0) (wz 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc e_asan_memcpy m1
         /\ ptr = [])
     \/
        (ms = entry_st (wz 0xb37e0) (wz (q + -64)) gp (wz TPV) t0' t1' t2' (wz out) (wz (out + 16)) (wz out) (wz 0) (wz 16) a3' a4' a5' a6' a7'
                       (wz (zlength ptr)) (wz 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc e_asan_memset m1)
     \/
        (exists ptr' : list Z,
           ms = entry_st (wz 0xb3738) (wz (q + -64)) gp (wz TPV) t0' t1' t2' (wz out) (wz P) (wz P) (wz 126) (wz (zlength ptr)) a3' a4' a5' a6' a7'
                         (wz (zlength ptr)) (wz 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc e_memchr m1
           /\ ptr = 47 :: ptr')
     \/
        (exists (ra' : Z) (d' : nat) (e c : Z),
           ms = entry_st (wz ra') (wz (q + -64)) gp (wz TPV) t0' t1' t2' (wz out) (wz P) (wz (q + -56)) (wz node) (wz 16) a3' a4' a5' a6' a7'
                         (wz (zlength ptr)) (wz 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc e_asan_memcpy m1
           /\ d = S d' /\ tnext (ae_T E i) = e + 1 /\ e + 1 <= ae_n E - 1
           /\ ((ra' = 0xb36cc /\ ty (ae_T E) i = t_obj /\ ae_T E e = tword t_obj_end i
                 /\ tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d')) (i + 1) e c)
            \/ (ra' = 0xb36f0 /\ ty (ae_T E) i = t_arr /\ ae_T E e = tword t_arr_end i
                 /\ tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d') (i + 1) e c))) ).

  Lemma elem_epi : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j0 jn : list byte)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -64) (elem_frame ra s0 s1 s2 s3 j0 jn) -> stk asegs m (ae_lo E) (q + -64) -> mem_inv asegs m -> ae_lo E <= q + -64 ->
    (forall (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word), stk asegs m (ae_lo E) q ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz (q + -64)) gp (wz TPV) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz 0xb37f8) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros FR ST MI LO HK. unfold elem_frame in FR.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 5 step. step.
    release_frame FR ST q.
    step. apply evt_done. apply HK. exact ST.
  Qed.

  Lemma elem_walk1 : forall (ptr : list Z) (i j q out node P : Z)
      (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    ptr_atA E P ptr -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j <= ae_n E - 1 ->
    AINV_A E m ->
    rw_cells asegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> 0 < node -> node + 16 <= ae_hi E -> (q <= node \/ node + 16 <= q + -64) ->
    rw_cells asegs m out [CB 24 jo] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> (node + 16 <= out \/ out + 24 <= node) ->
    mem_inv asegs m -> stk asegs m (ae_lo E) q -> ae_lo E + 80 <= q -> q mod 16 = 0 -> shb_cells m ->
    (forall m', munch (elem_W q out) m m' -> wmono asegs m m' -> shz m' node 16) ->
    (forall m', munch (elem_W q out) m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (elem_W q out) m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    (ptr <> [] -> forall m', munch (elem_W q out) m m' -> wmono asegs m m' -> acc asegs m' (ae_PB E) (ae_NPB E)) ->
    evt asegs (elem_x1 ptr i q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
      (lvl_entry ATP_ELEM_A ra q gp t0 t1 t2 s0 s1 out node P (zlength ptr) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Proof using OK.
    intros until jo. intros PAT EL I0 JN AI NODE N0 NB NQ OUT QO OB O8 NO MI ST LO Q16 [G1 G2] SHZN SHZD SHZT ACCP.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold lvl_entry, ATP_ELEM_A in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (PTRB & PTRF & PP0 & PP1 & PL).
    pose proof (zlength_nonneg ptr) as ZL. pose proof (zlength_nonneg (ae_p1 E)) as ZL1.
    assert (PR : ptr <> [] -> 0 < ae_PB E /\ ae_PB E <= P /\ P + zlength ptr <= ae_PB E + ae_NPB E /\ ae_PB E + ae_NPB E <= ae_lo E).
    { intros NE. assert (NE1 : ae_p1 E <> []).
      { destruct PAT as (pre & Ep & _). intros E0. rewrite E0 in Ep. destruct pre; [cbn in Ep; exact (NE (eq_sym Ep))| discriminate Ep]. }
      specialize (PTRR NE1). lia. }
    pose proof (munch_refl (elem_W q out) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold elem_W in MU.
    pose proof (elem_word_range _ _ _ _ _ _ EL I0 ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E i) < 256) by (unfold ttype; lia).
    hide AI. clear PTRB.

    step. carve_frame 64%nat ST.
    apply (rw_cells_split_CB asegs _ _ [] 64 junk [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    set (ja := firstn 8 junk) in FR. set (jb := firstn 8 (skipn 8 junk)) in FR. clearbody ja jb.
    repeat match type of FR with context [CB 8 (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    lazymatch type of FR with context [CB 8 jb :: CB 8 ?x :: _] => rename x into jc end.
    do 5 step.

    step. step. step. step.
    name_mem m1.
    lazymatch goal with H : rw_cells asegs m1 (q + -64) _ |- _ => rename H into FR1 end.
    assert (AI1 : AINV_A E m1).
    { unhide AI. apply (AINV_A_munch E _ m m1 OK AI MU). constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
    pose proof AI1 as (_ & _ & _ & DOCC1 & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i (proj1 AI1) ltac:(lia)) as RDT1.
    assert (PTRB1 : bytes_at asegs m1 P (map (Z_to_bv 8) ptr)) by exact (proj1 (ptr_atA_facts E P ptr m1 OK PAT (proj1 (proj2 (proj2 AI1))))).
    clear AI1.

    chk0 SHZN node. step. if_false.
    step. astep. chk0 SHZN (node + 8). step. if_false.
    step. step.
    chk0 SHZD (ae_DOC E). step. if_false.
    step. step. astep. astep.
    chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.
    step. astep. astep.

    assert (CHILD : forall (pc ra' : Z) (xa0 xa2 xa3 : word) (d' : nat) (e c : Z),
      ((pc = 0xb36c0 /\ ra' = 0xb36cc) \/ (pc = 0xb36e4 /\ ra' = 0xb36f0)) ->
      d = S d' -> tnext (ae_T E i) = e + 1 -> e + 1 <= ae_n E - 1 ->
      ((ra' = 0xb36cc /\ ty (ae_T E) i = t_obj /\ ae_T E e = tword t_obj_end i
          /\ tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d')) (i + 1) e c)
       \/ (ra' = 0xb36f0 /\ ty (ae_T E) i = t_arr /\ ae_T E e = tword t_arr_end i
          /\ tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d') (i + 1) e c)) ->
      evt asegs (elem_x1 ptr i q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
        (MS (mkR ra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV) t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 P)
                 xa0 (Z_to_bv 64 node) xa2 xa3 a4 a5 a6 a7
                 (Z_to_bv 64 (zlength ptr)) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs))).
    { intros pc ra' xa0 xa2 xa3 d' e c PC Ed NXT EN KIND.
      destruct PC as [(-> & ->)|(-> & ->)];
        (astep; step; step; apply evt_done; exists m1, ja, (jb ++ jc);
         split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [assumption|];
         split; [exact ST|]; split; [unfold elem_frame; apply frame_join16; exact FR1|];
         do 12 eexists; right; right; right; eexists _, d', e, c;
         split; [unfold entry_st, e_asan_memcpy; atp_st_eq_goal|]; split; [exact Ed|]; split; [exact NXT|]; split; [exact EN| exact KIND]). }

    lazymatch goal with |- evt asegs ?Q ?S =>
      assert (SCALAR : ttype (ae_T E i) <> 91 -> ttype (ae_T E i) <> 123 -> evt asegs Q S) end.
    { intros S91 S123. step. if_dead1 by S91 TTR. astep. step. if_dead2 by S123 TTR. clear S91 S123.

      step. if_cases K0; zify_cond K0.
      {
        step. step. step.
        apply evt_done. exists m1, ja, (jb ++ jc). split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
        split; [exact ST|]. split; [unfold elem_frame; apply frame_join16; exact FR1|].
        do 12 eexists. left. split; [unfold entry_st, e_asan_memcpy; atp_st_eq_goal|].
        destruct ptr as [|cx lx]; [reflexivity| exfalso; rewrite zlength_cons in K0; pose proof (zlength_nonneg lx); lia]. }
      destruct ptr as [|c0 ptr0]; [exfalso; apply K0; reflexivity|].
      assert (NE0 : c0 :: ptr0 <> []) by discriminate. specialize (PR NE0). specialize (ACCP NE0). destruct PR as (PB0 & PB1 & PB2 & PB3).
      assert (C0R : 0 <= c0 < 256) by (inversion PTRF; assumption).
      rewrite zlength_cons in *. pose proof (zlength_nonneg ptr0) as ZL0.
      pose proof (zbytes_read1 m1 P (c0 :: ptr0) 0 PTRB1 ltac:(rewrite zlength_cons; lia)) as RD0'.
      change (nth (Z.to_nat 0) (c0 :: ptr0) 0) with c0 in RD0'. rewrite Z.add_0_r in RD0'.

      assert (J4c0 : forall xa0 xa1 xa2 xa3 : word,
        evt asegs (elem_x1 (c0 :: ptr0) i q out node P ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
          (MS (mkR ra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV) t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 P) xa0 xa1 xa2 xa3 a4 a5 a6 a7
                   (Z_to_bv 64 (zlength ptr0 + 1)) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0xb371c) fc None m1 (seg_rom asegs))).
      { intros xa0 xa1 xa2 xa3.
        astep. astep. step. if_cases K1; zify_cond K1.
        -
          astep. step. step. step. step.
          apply evt_done. exists m1, ja, (jb ++ jc). split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
          split; [exact ST|]. split; [unfold elem_frame; apply frame_join16; exact FR1|].
          do 12 eexists. right; left. unfold entry_st, e_asan_memset. rewrite ?zlength_cons. atp_st_eq_goal.
        -
          subst c0. astep. step. step. step.
          apply evt_done. exists m1, ja, (jb ++ jc). split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
          split; [exact ST|]. split; [unfold elem_frame; apply frame_join16; exact FR1|].
          do 12 eexists. right; right; left. exists ptr0.
          split; [unfold entry_st, e_memchr; rewrite ?zlength_cons; atp_st_eq_goal| reflexivity]. }

      destruct (acc_read1 m1 (ae_PB E) (ae_NPB E) P (ACCP m1 MU WM) ltac:(lia)) as (b0 & RDS0 & OK0).
      destruct (sh_ok_cases b0 P OK0) as [-> | (k0 & -> & K0' & KM0)].
      - astep. astep. step. shz_norm. step. if_false. eapply evt_eq; [| eapply J4c0]; [atp_st_eq].
      - astep. astep. step. rewrite (sxb_small7 k0) by lia. step. if_dead2 by K0'. astep. step. if_dead2 by K0' KM0 PP0 P0'. eapply evt_eq; [| eapply J4c0]; [atp_st_eq]. }

    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d i j EL I0 ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e c Ed TY Ej NXT CLOSE TILES|d' e c Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    - apply SCALAR; destruct TY as [TY|[TY|TY]]; rewrite TY; discriminate.
    - apply SCALAR; destruct TY as [TY|[TY|TY]]; rewrite TY; discriminate.
    - apply SCALAR; rewrite TY; discriminate.
    -
      clear SCALAR. rewrite TY. unfold t_arr. step. if_true.
      apply (CHILD 0xb36e4 0xb36f0 _ _ _ d' e c (or_intror (conj eq_refl eq_refl)) Ed NXT ltac:(lia)).
      right. split; [reflexivity|]. split; [unfold ty; exact TY|]. split; [exact CLOSE| exact TILES].
    -
      clear SCALAR. rewrite TY. unfold t_obj. step. if_false. astep. step. if_false.
      apply (CHILD 0xb36c0 0xb36cc _ _ _ d' e c (or_introl (conj eq_refl eq_refl)) Ed NXT ltac:(lia)).
      left. split; [reflexivity|]. split; [unfold ty; exact TY|]. split; [exact CLOSE| exact TILES].
  Qed.

End ElemWalks.

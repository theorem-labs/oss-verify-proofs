(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2 Z45 Z5k Z3v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition arr_W (q out : Z) : list (Z * Z) := [(q + -208, q); (out, out + 24)].

Definition arr_frame (ra s0 s1 s2 s3 s4 s5 pw lw : word) (jr : list byte) : list cell :=
  [CB 24 jr; C8 pw; C8 lw; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition arr_set_site (ra' : Z) (s5' : word) (code : Z) : Prop :=
  (ra' = 0x9a234 /\ code = 22) \/ (ra' = 0x9a1d4 /\ code = 19 /\ s5' = Z_to_bv 64 22)
  \/ (ra' = 0x9a3dc /\ s5' = Z_to_bv 64 code /\ (code = 17 \/ code = 19 \/ code = 22)).

Lemma sub_fp_lvl16 : forall q out, sub_fp [(q + -96 + -16, q + -96)] (arr_W q out).
Proof. intros q out x Hx. unfold arr_W in Hx. cbn [outside] in *. lia. Qed.

Section ArrWalks.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Lemma arr_epi : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q lo : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw lw : word) (jr : list byte)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    rw_cells bsegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw lw jr) -> stk bsegs m lo (q + -96) -> mem_inv bsegs m -> lo <= q + -96 ->
    (forall (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word), stk bsegs m lo q ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz (q + -96)) gp (wz TPV) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz 0x9a3f0) fc None m (seg_rom bsegs)).
  Proof.
    intros until x31. intros FR ST MI LO HK. unfold arr_frame in FR.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    do 7 step. step.
    release_frame FR ST q.
    step. apply evt_done. apply HK. exact ST.
  Qed.

  Lemma arr_errb : forall (K : machine_state -> Prop) (m0 m : mem) (F : bvmap 5 word) (fc : bv 32) (q out code : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw lw : word) (jr jo : list byte)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
    munch (arr_W q out) m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) (q + -96) -> ae_lo E + 96 <= q ->
    rw_cells bsegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw lw jr) -> rw_cells bsegs m out [CB 24 jo] -> q <= out -> out + 24 <= ae_hi E ->
    (code = 17 \/ code = 19 \/ code = 22) ->
    (forall (m1 : mem) (ra' code' : Z) (y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys5 y28 y29 y30 y31 : word) (jr' : list byte) (pw' lw' : word),
       arr_set_site ra' ys5 code' ->
       munch (arr_W q out) m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -96) ->
       rw_cells bsegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw' lw' jr') -> rw_cells bsegs m1 out [CB 24 jo] ->
       evt bsegs K (MS (mkR (wz ra') (wz (q + -96)) gp (wz TPV) y5 y6 y7 (wz out) (wz (out + 16)) (wz out) (wz 0) (wz 16) ya3 ya4 ya5 ya6 ya7
                          ys2 ys3 (wz 2147450880) ys5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (wz e_asan_memset) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 (wz 2147450880) (wz code) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0x9a3c4) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros MU WM MI ST LO FR OUT QO OB CODE XSET.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    unfold arr_W in MU.
    step. if_dead1 by QO LO LOW. astep. astep. step. astep. step.
    eapply evt_eq; [| eapply (XSET m 0x9a3dc code)];
      [unfold e_asan_memset; atp_st_eq| right; right; split; [reflexivity| split; [reflexivity| exact CODE]]
      | exact MU| exact WM| exact MI| exact ST| exact FR| exact OUT].
  Qed.

  Lemma arr_scan : forall (K : machine_state -> Prop) (m0 m : mem) (F : bvmap 5 word) (fc : bv 32) (c1 : Z) (ptr1 : list Z) (q out node P : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jr jo : list byte) (x1 x5 x7 xa1 xa2 xa3 xa4 xa5 x19 x28 x29 x30 x31 a6 a7 : word),
    munch (arr_W q out) m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) (q + -96) -> ae_lo E + 96 <= q ->
    rw_cells bsegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 (wz (P + 1)) (wz (zlength ptr1 + 1)) jr) -> rw_cells bsegs m out [CB 24 jo] -> q <= out -> out + 24 <= ae_hi E ->
    acc bsegs m (ae_PB E) (ae_NPB E) -> 0 < ae_PB E -> ae_PB E <= P -> P + zlength ptr1 + 2 <= ae_PB E + ae_NPB E -> ae_PB E + ae_NPB E <= ae_lo E ->
    bytes_at bsegs m (P + 1) (map (Z_to_bv 8) (c1 :: ptr1)) -> Forall (fun c => 0 <= c < 256) (c1 :: ptr1) ->
    (forall (m1 : mem) (ra' code' : Z) (y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys5 y28 y29 y30 y31 : word) (jr' : list byte) (pw' lw' : word),
       arr_set_site ra' ys5 code' ->
       munch (arr_W q out) m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -96) ->
       rw_cells bsegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw' lw' jr') -> rw_cells bsegs m1 out [CB 24 jo] ->
       evt bsegs K (MS (mkR (wz ra') (wz (q + -96)) gp (wz TPV) y5 y6 y7 (wz out) (wz (out + 16)) (wz out) (wz 0) (wz 16) ya3 ya4 ya5 ya6 ya7
                          ys2 ys3 (wz 2147450880) ys5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (wz e_asan_memset) fc None m1 (seg_rom bsegs))) ->
    (forall (m1 : mem) (tok : Z) (y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys3 y28 y29 y30 y31 : word),
       0 <= tok <= zlength ptr1 + 1 ->
       munch (arr_W q out) m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -96) ->
       rw_cells bsegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 (wz (P + 1)) (wz (zlength ptr1 + 1)) jr) -> rw_cells bsegs m1 out [CB 24 jo] ->
       evt bsegs K (MS (mkR (wz 0x9a330) (wz (q + -96)) gp (wz TPV) y5 y6 y7 (wz out) (wz node) (wz (q + -96)) (wz node) (wz 16) ya3 ya4 ya5 ya6 ya7
                          (wz tok) ys3 (wz 2147450880) (wz 22) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (wz e_asan_memcpy) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz (q + -96)) gp (wz TPV) x5 (wz ((P + 1) / 8)) x7 (wz out) (wz node)
                       (wz (P + 1)) xa1 xa2 xa3 xa4 xa5 a6 a7 (wz (zlength ptr1 + 1)) x19 (wz 2147450880) (wz 22) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0x9a250) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until a7. intros MU WM MI ST LO FR OUT QO OB ACC PB0 PB1 PB2 PB3 RB1 RF1 XSET XTOK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (zlength_nonneg ptr1) as ZL1.
    unfold arr_W in MU.

    assert (ROC : ro_cells bsegs m 0x10368 [CB 8 [Z_to_bv 8 205; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204; Z_to_bv 8 204]]).
    { apply (ro_cells_image bsegs m); [exact MI| vm_compute; reflexivity| lia| cbn; lia]. }

    astep. astep. astep. astep.
    replace (0 <? P + 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    astep. astep. step. step. astep. astep. astep. astep. step. step.
    lazymatch goal with |- evt _ ?K' _ =>
    eapply evt_eq; [| eapply (arr_digit_loopB K' m F fc (c1 :: ptr1) (P + 1) (zlength ptr1 + 1) (- (zlength ptr1 + 1)) (q + -96) out node (ae_PB E) (ae_NPB E)
                               x1 gp _ s6 s7 s8 s9 s10 s11
                               RB1 RF1 ltac:(rewrite zlength_cons; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) MI ACC ltac:(lia) ltac:(lia))
                        with (n := S (length (c1 :: ptr1))) (cnt := 0)];
      [atp_st_eq| | | lia| unfold zlength; cbn [length]; lia| intros j Hj; lia]
    end.
    -
      intros code xa0' xa1' xa2' xa4' xs2' xs3' xt4' xt5' xt6' CODE.
      eapply (arr_errb K m0 m); [exact MU| exact WM| exact MI| exact ST| exact LO| exact FR| exact OUT| exact QO| exact OB| exact CODE| exact XSET].
    -
      intros tok c3 xa0' xa1' xa2' xa4' xs3' xt4' xt5' xt6' TOK NOSL2 DISJ C3R.
      step. astep. step. step.
      eapply evt_eq; [| eapply (XTOK m tok)]; [unfold e_asan_memcpy; atp_st_eq| exact TOK| exact MU| exact WM| exact MI| exact ST| exact FR| exact OUT].
  Qed.

  Lemma arr_walk1 : forall (K : machine_state -> Prop) (ptr : list Z) (i e c q out node P : Z)
      (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    ptr_atA E P ptr -> ty (ae_T E) i = t_arr -> 0 <= i -> i < ae_n E ->
    AINV_A E m ->
    rw_cells bsegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= node -> node + 16 <= ae_hi E ->
    rw_cells bsegs m out [CB 24 jo] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> (node + 16 <= out \/ out + 24 <= node) ->
    mem_inv bsegs m -> stk bsegs m (ae_lo E) q -> ae_lo E + 208 <= q -> q mod 16 = 0 -> shb_cells m ->
    (forall m', munch (arr_W q out) m m' -> wmono bsegs m m' -> shz m' node 16) ->
    (forall m', munch (arr_W q out) m m' -> wmono bsegs m m' -> shz m' out 24) ->
    (forall m', munch (arr_W q out) m m' -> wmono bsegs m m' -> shz m' (q + -96) 96) ->
    (ptr <> [] -> forall m', munch (arr_W q out) m m' -> wmono bsegs m m' -> acc bsegs m' (ae_PB E) (ae_NPB E)) ->

    (forall (m1 : mem) (y5 y6 y7 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word) (jr : list byte),
       ptr = [] ->
       munch (arr_W q out) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -96) ->
       rw_cells bsegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 (wz P) (wz 0) jr) -> rw_cells bsegs m1 out [CB 24 jo] ->
       evt bsegs K (MS (mkR (wz 0x9a200) (wz (q + -96)) gp (wz TPV) y5 y6 y7 (wz out) (wz node) (wz out) (wz node) (wz 16) ya3 ya4 ya5 ya6 ya7
                          s2 s3 (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (wz e_asan_memcpy) fc None m1 (seg_rom bsegs))) ->

    (forall (m1 : mem) (ra' code' : Z) (y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys5 y28 y29 y30 y31 : word) (jr' : list byte) (pw' lw' : word),
       arr_set_site ra' ys5 code' ->
       munch (arr_W q out) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -96) ->
       rw_cells bsegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 pw' lw' jr') -> rw_cells bsegs m1 out [CB 24 jo] ->
       evt bsegs K (MS (mkR (wz ra') (wz (q + -96)) gp (wz TPV) y5 y6 y7 (wz out) (wz (out + 16)) (wz out) (wz 0) (wz 16) ya3 ya4 ya5 ya6 ya7
                          ys2 ys3 (wz 2147450880) ys5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (wz e_asan_memset) fc None m1 (seg_rom bsegs))) ->

    (forall (m1 : mem) (c1 : Z) (ptr1 : list Z) (tok : Z) (y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys3 y28 y29 y30 y31 : word) (jr : list byte),
       ptr = 47 :: c1 :: ptr1 -> 0 <= tok <= zlength ptr1 + 1 ->
       munch (arr_W q out) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -96) ->
       rw_cells bsegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 (wz (P + 1)) (wz (zlength ptr1 + 1)) jr) -> rw_cells bsegs m1 out [CB 24 jo] ->
       evt bsegs K (MS (mkR (wz 0x9a330) (wz (q + -96)) gp (wz TPV) y5 y6 y7 (wz out) (wz node) (wz (q + -96)) (wz node) (wz 16) ya3 ya4 ya5 ya6 ya7
                          (wz tok) ys3 (wz 2147450880) (wz 22) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (wz e_asan_memcpy) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (lvl_entry ATP_ARR_A ra q gp t0 t1 t2 s0 s1 out node P (zlength ptr) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Proof using OK.
    intros until jo. intros PAT TY I0 IN AI NODE QN NB OUT QO OB O8 NO MI ST LO Q16 [G1 G2] SHZN SHZO SHZF ACCP XCPY XSET XTOK.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold lvl_entry, ATP_ARR_A in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (PTRB & PTRF & PP0 & PP1 & PL).
    pose proof (zlength_nonneg ptr) as ZL. pose proof (zlength_nonneg (ae_p1 E)) as ZL1.
    assert (PR : ptr <> [] -> 0 < ae_PB E /\ ae_PB E <= P /\ P + zlength ptr <= ae_PB E + ae_NPB E /\ ae_PB E + ae_NPB E <= ae_lo E).
    { intros NE. assert (NE1 : ae_p1 E <> []).
      { destruct PAT as (pre & Ep & _). intros E0. rewrite E0 in Ep. destruct pre; [cbn in Ep; exact (NE (eq_sym Ep))| discriminate Ep]. }
      specialize (PTRR NE1). lia. }
    pose proof (munch_refl (arr_W q out) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold arr_W in MU.
    assert (EU72 : bv_unsigned (Z_to_bv 64 (q + -72)) = q + -72) by (apply unsigned_lit; lia).
    assert (Q16' : (q + -96) mod 16 = 0) by (replace (q + -96) with (q + (-6) * 16) by lia; rewrite Z.mod_add by lia; exact Q16).
    hide AI. clear PTRB.

    step. carve_frame 96%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 96 junk [] [24; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    set (jr := firstn 24 junk) in FR. clearbody jr.
    repeat match type of FR with context [CB 8 (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    do 7 step. step. step. step. step. step. step. step.
    name_mem m1.

    step. if_cases K0; zify_cond K0.
    {
      step. if_dead1 by QO LO LOW. astep. step. step. step.
      assert (E0 : ptr = []) by (destruct ptr as [|cx lx]; [reflexivity| exfalso; rewrite zlength_cons in K0; pose proof (zlength_nonneg lx); lia]).
      lazymatch goal with H : rw_cells bsegs m1 (q + -96) _ |- _ => rename H into FR1 end.
      lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
      lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
      lazymatch goal with H : rw_cells bsegs m1 out _ |- _ => rename H into OUT1 end.
      eapply evt_eq; [| eapply (XCPY m1)]; [unfold e_asan_memcpy; rewrite K0; atp_st_eq| exact E0| exact MU| exact WM| exact MI1| exact ST1| unfold arr_frame; rewrite <- K0; exact FR1| exact OUT1]. }
    destruct ptr as [|c0 ptr0]; [exfalso; apply K0; reflexivity|].
    assert (NE0 : c0 :: ptr0 <> []) by discriminate. specialize (PR NE0). specialize (ACCP NE0). destruct PR as (PB0 & PB1 & PB2 & PB3).
    assert (C0R : 0 <= c0 < 256) by (inversion PTRF; assumption).
    rewrite zlength_cons in *. pose proof (zlength_nonneg ptr0) as ZL0.
    assert (PTRBm : bytes_at bsegs m1 P (map (Z_to_bv 8) (c0 :: ptr0))).
    { unhide AI. exact (proj1 (ptr_atA_facts E P (c0 :: ptr0) m1 OK PAT (proj1 (proj2 (proj2 (AINV_A_munch E _ m m1 OK AI MU ltac:(constructor; [cbn; lia|]; constructor; [cbn; lia| constructor]))))))). }
    pose proof (zbytes_read1 m1 P (c0 :: ptr0) 0 PTRBm ltac:(rewrite zlength_cons; lia)) as RD0.
    change (nth (Z.to_nat 0) (c0 :: ptr0) 0) with c0 in RD0. rewrite Z.add_0_r in RD0.

    step. step. if_dead1 by PB0 PB1.
    lazymatch goal with H : rw_cells bsegs m1 (q + -96) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells bsegs m1 out _ |- _ => rename H into OUT1 end.

    assert (JA8 : forall xa1 xa2 : word,
      evt bsegs K
        (MS (mkR ra (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 P) xa1 xa2
                 (Z_to_bv 64 (zlength ptr0 + 1)) a4 a5 a6 a7 s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9a168) fc None m1 (seg_rom bsegs))).
    { intros xa1 xa2.

      astep. astep. step. if_cases K1; zify_cond K1.
      {
        step. if_dead1 by QO LO LOW. astep. astep. step. astep. step.
        eapply evt_eq; [| eapply (XSET m1 0x9a234 22)];
          [unfold e_asan_memset; atp_st_eq| left; split; reflexivity| exact MU| exact WM| exact MI1| exact ST1| unfold arr_frame; exact FR1| exact OUT1]. }
      subst c0.

      astep. astep. astep. step.
      pose proof FR1 as SV1. unfold arr_frame in SV1.
      apply (proj1 (rw_cells_app bsegs m1 _ [_] _)) in SV1. destruct SV1 as [_ SV1]. cbn [cells_size csize Nat.add] in SV1.
      apply (proj1 (rw_cells_app bsegs m1 _ [_; _] _)) in SV1. destruct SV1 as [SV1 _].
      replace (q + -96 + Z.of_nat 24) with (q + -72) in SV1 by lia.
      hide FR1. hide OUT1.
      eapply evt_eq; [| eapply (substr_cps E OK K m1 F fc (q + -96) (q + -72) P (zlength ptr0 + 1) 1 18446744073709551615 (zlength ptr0 + 1 - 1) 0x9a184);
        [ exact SV1| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| lia| lia| lia| left; split; reflexivity| exact (conj G1 G2)
        | intros m' MU' WM'; apply (shz_sub m' (q + -96) 96); [exact (SHZF m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_lvl16 q out) MU')) (wmono_trans bsegs _ _ _ WM WM'))| lia| lia]
        | exact ST1| lia| lia| exact Q16'| exact MI1| lia| reflexivity| ] ]; [atp_st_eq|].
      clear ST1 MI1. intros m2 xb2 xb3 xb4 xb5 MU12 WM12 MI2 ST2.
      unhide FR1. unhide OUT1. clear SV1 RD0 PTRBm.
      transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12.

      step. step. step. astep.
      name_mem m3.
      lazymatch goal with H : rw_cells bsegs m3 (q + -96) _ |- _ => rename H into FR3 end.
      lazymatch goal with H : stk bsegs m3 _ _ |- _ => rename H into ST3 end.
      lazymatch goal with H : mem_inv bsegs m3 |- _ => rename H into MI3 end.
      lazymatch goal with H : rw_cells bsegs m3 out _ |- _ => rename H into OUT3 end.
      replace (zlength ptr0 + 1 - 1) with (zlength ptr0) in * by lia.
      step. if_cases K2; zify_cond K2.
      {
        eapply (arr_errb K m m3); [exact MU| exact WM| exact MI3| exact ST3| lia| unfold arr_frame; exact FR3| exact OUT3| exact QO| exact OB| lia| exact XSET]. }
      destruct ptr0 as [|c1 ptr1]; [exfalso; rewrite zlength_nil in K2; lia|].
      assert (C1R : 0 <= c1 < 256) by (inversion PTRF as [|? ? _ X]; inversion X; assumption).
      rewrite zlength_cons in *. pose proof (zlength_nonneg ptr1) as ZL1'.
      assert (PTRB3 : bytes_at bsegs m3 P (map (Z_to_bv 8) (47 :: c1 :: ptr1))).
      { unhide AI. exact (proj1 (ptr_atA_facts E P (47 :: c1 :: ptr1) m3 OK PAT (proj1 (proj2 (proj2 (AINV_A_munch E _ m m3 OK AI MU ltac:(constructor; [cbn; lia|]; constructor; [cbn; lia| constructor]))))))). }
      pose proof (zbytes_read1 m3 P (47 :: c1 :: ptr1) 1 PTRB3 ltac:(rewrite !zlength_cons; lia)) as RD1.
      change (nth (Z.to_nat 1) (47 :: c1 :: ptr1) 0) with c1 in RD1.
      assert (RB1 : bytes_at bsegs m3 (P + 1) (map (Z_to_bv 8) (c1 :: ptr1))).
      { pose proof (bytes_at_skipn _ _ _ 1 PTRB3 ltac:(cbn; lia)) as X. exact X. }
      assert (RF1 : Forall (fun c => 0 <= c < 256) (c1 :: ptr1)) by (inversion PTRF; assumption).
      clear PTRB3.
      assert (AT090 : forall xa1' xa2' : word,
        evt bsegs K
          (MS (mkR (Z_to_bv 64 0x9a184) (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) t0 (Z_to_bv 64 ((P + 1) / 8)) t2 (Z_to_bv 64 out) (Z_to_bv 64 node)
                   (Z_to_bv 64 (P + 1)) xa1' xa2' xb3 xb4 xb5 a6 a7
                   (Z_to_bv 64 (zlength ptr1 + 1)) s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 22) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x9a250) fc None m3 (seg_rom bsegs))).
      { intros xa1' xa2'.
        eapply (arr_scan K m m3 F fc c1 ptr1 q out node P); [exact MU| exact WM| exact MI3| exact ST3| lia| unfold arr_frame; exact FR3| exact OUT3| exact QO| exact OB| exact (ACCP m3 MU WM)| lia| lia| lia| lia| exact RB1| exact RF1| exact XSET| ].
        intros m4 tok y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys3 y28 y29 y30 y31 TOK MU4 WM4 MI4 ST4 FR4 OUT4.
        eapply (XTOK m4 c1 ptr1 tok); [reflexivity| exact TOK| exact MU4| exact WM4| exact MI4| exact ST4| exact FR4| exact OUT4]. }

      astep. astep. step. if_cases K3; zify_cond K3.
      { eapply evt_eq; [| eapply AT090]; [atp_st_eq]. }

      assert (JF0 : forall ya1 ya2 : word,
        evt bsegs K
          (MS (mkR (Z_to_bv 64 0x9a184) (Z_to_bv 64 (q + -96)) gp (Z_to_bv 64 TPV) t0 (Z_to_bv 64 ((P + 1) / 8)) t2 (Z_to_bv 64 out) (Z_to_bv 64 node)
                   (Z_to_bv 64 (P + 1)) ya1 ya2 xb3 xb4 xb5 a6 a7
                   (Z_to_bv 64 (zlength ptr1 + 1)) s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 22) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x9a1b0) fc None m3 (seg_rom bsegs))).
      { intros ya1 ya2.

        astep. astep. step. if_cases K4; zify_cond K4.
        - eapply evt_eq; [| eapply AT090]; [atp_st_eq].
        - step. if_dead1 by QO LO LOW. astep. astep. step. astep. step.
          eapply evt_eq; [| eapply (XSET m3 0x9a1d4 19)];
            [unfold e_asan_memset; atp_st_eq| right; left; split; [reflexivity| split; reflexivity]| exact MU| exact WM| exact MI3| exact ST3| unfold arr_frame; exact FR3| exact OUT3]. }
      destruct (acc_read1 m3 (ae_PB E) (ae_NPB E) (P + 1) (ACCP m3 MU WM) ltac:(lia)) as (b1 & RDS1 & OK1).
      destruct (sh_ok_cases b1 (P + 1) OK1) as [-> | (k1 & -> & K1 & KM1)].
      - astep. step. shz_norm. step. if_false. eapply evt_eq; [| eapply JF0]; [atp_st_eq].
      - astep. step. rewrite (sxb_small7 k1) by lia. step. if_dead2 by K1. astep. step. if_dead2 by K1 KM1 PB0 PB1. eapply evt_eq; [| eapply JF0]; [atp_st_eq]. }

    destruct (acc_read1 m1 (ae_PB E) (ae_NPB E) P (ACCP m1 MU WM) ltac:(lia)) as (b0 & RDS0 & OK0).
    destruct (sh_ok_cases b0 P OK0) as [-> | (k0 & -> & K0x & KM0)].
    - astep. astep. step. shz_norm. step. if_false. eapply evt_eq; [| eapply JA8]; [atp_st_eq].
    - astep. astep. step. rewrite (sxb_small7 k0) by lia. step. if_dead2 by K0x. astep. step. if_dead2 by K0x KM0 PB0 PB1. eapply evt_eq; [| eapply JA8]; [atp_st_eq].
  Qed.
End ArrWalks.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_kitA Atp_arrlA Atp_arratA
     El_defsA El_armkitA El_arratA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition w28_W (q : Z) : list (Z * Z) := [(q + -208, q); (q + 128, q + 152)].
Lemma sub_fp_w28_arrat : forall q, sub_fp (arrat_W (q + -96) (q + 128)) (w28_W q).
Proof. intros q x Hx. unfold arrat_W, w28_W in *. cbn [outside] in *. lia. Qed.
Lemma sub_fp_w28_tix : forall q, sub_fp [(q + -96 + -16, q + -96)] (w28_W q).
Proof. intros q x Hx. unfold w28_W in *. cbn [outside] in *. lia. Qed.
Lemma sub_fp_w28_out : forall q, sub_fp [(q + 128, q + 152)] (w28_W q).
Proof. intros q x Hx. unfold w28_W in *. cbn [outside] in *. lia. Qed.

Definition w28_frame (pre : list cell) (s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := pre ++ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section W28.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma w28_walk1 : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q f usp idx : Z) (jr : list byte)
      (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    stk bsegs m (ae_lo E) q -> ae_lo E + 208 <= q -> q + 152 <= ae_hi E -> q mod 32 = 0 -> mem_inv bsegs m -> 0 <= idx < 2^64 ->
    rw_cells bsegs m (q + 16) [C8 (wz EL_C16_A); C8 (wz idx); C8 (wz (f + 240)); C8 (wz 28); C8 (wz f); C8 (wz (f + 208))] ->
    rw_cells bsegs m (f + 208) [C8 (wz (ae_DOC E)); C8 (wz 1)] -> 0 < f -> f + 1024 <= ae_lo E ->
    rw_cells bsegs m (q + 128) [CB 24 jr] ->
    (forall m', munch (w28_W q) m m' -> AINV_A E m') ->
    (forall m', munch (w28_W q) m m' -> wmono bsegs m m' -> shb_cells m') ->
    (forall m', munch (w28_W q) m m' -> wmono bsegs m m' -> shz m' (f + 208) 16) ->
    (forall m', munch (w28_W q) m m' -> wmono bsegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (w28_W q) m m' -> wmono bsegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->

    (forall (m1 : mem) (xa3 xa4 : word) (j0 j8 j16 j24 j28 : list byte),
       munch (w28_W q) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -96) ->
       rw_cells bsegs m1 (q + -96) (w28_frame [CB 8 j0; CB 8 j8; CB 8 j16; CB 4 j24; CB 4 j28] s6 (wz (f + 96)) (wz (f + 32)) (wz (shad f)) (wz f) (wz q) (wz usp) (wz 0xb2690)) ->
       rw_cells bsegs m1 (q + 128) [CB 24 jr] -> ttype (ae_T E 1) <> 91 ->
       evt bsegs K (MS (mkR (wz 0xb5ac0) (wz (q + -96)) gp (wz TPV) t0 t1 t2 (wz (q + 144)) (wz (q + 128)) (wz (q + 128)) (wz 0) (wz 16) xa3 xa4 a5 a6 a7
                          (wz (f + 208)) (wz (f + 216)) (wz SHB) (wz (shad (f + 208))) (wz (shad (f + 216))) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz e_asan_memset) fc None m1 (seg_rom bsegs))) ->

    (forall (m1 : mem) (d' : nat) (e c : Z) (xa3 xa4 : word) (j0 j28 : list byte),
       munch (w28_W q) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -96) ->
       rw_cells bsegs m1 (q + -96) (w28_frame [CB 8 j0; C8 (wz (ae_DOC E)); C8 (wz 1); C4 (wz 0); CB 4 j28] s6 (wz (f + 96)) (wz (f + 32)) (wz (shad f)) (wz f) (wz q) (wz usp) (wz 0xb2690)) ->
       rw_cells bsegs m1 (q + 128) [CB 24 jr] ->
       ty (ae_T E) 1 = t_arr -> tnext (ae_T E 1) = e + 1 -> tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d') 2 e c -> e + 1 <= ae_n E - 1 ->
       evt bsegs K (MS (mkR (wz 0xb5aa4) (wz (q + -96)) gp (wz TPV) t0 t1 t2 (wz idx) (wz (q + 128)) (wz (q + 128)) (wz (q + -88)) (wz idx) xa3 xa4 a5 a6 a7
                          (wz (f + 208)) (wz (f + 216)) (wz SHB) (wz (shad (f + 208))) (wz (shad (f + 216))) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz ATP_ARRAT_A) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR ra (wz q) gp (wz TPV) t0 t1 t2 (wz usp) (wz q) a0 a1 a2 a3 a4 a5 a6 a7
                         (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz 0xb2680) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until t6. intros ST LO HI Q32 MI IDX C16 CE FPOS FLO OUT AIW SHBW SZN SZD SZT XNA XARR.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold ATP_ARRAT_A, SEGTOP_A, USTACK_TOP in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl (w28_W q) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold w28_W in MU.
    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).

    astep. step. step. zstep.

    astep. carve_frame 96%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [8; 8; 8; 4; 4; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    do 8 lstep.

    pose proof (SHBW _ MU WM) as [G1 G2].
    astep. astep. step. step. astep.
    name_mem m1.

    chk0 SZN (f + 208). step. if_false.

    astep. step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.

    astep. chk0 SZN (f + 216). step. if_false. step. zstep.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    eapply (tix_cps E OK _ m1 F fc (q + -96) 1 0xb5a54); [exact (AIW m1 MU)| lia| exact (SHBW m1 MU WM)| | exact ST1| lia| lia| clear - Q32; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_w28_tix q) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST1 MI1. intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12.
    pose proof (AIW m2 MU) as (TAPEB2 & _ & _ & _ & _).
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) 1 TAPEB2 ltac:(lia) TIR) as RDB2.

    chk0 SZT (ae_TAPE E + 8 * 1). step. if_false.
    replace (ae_TAPE E + 8 * 1 + 7) with (ae_TAPE E + 8 * 1 + 7) in RDB2 by lia. step. astep.
    lazymatch goal with H : rw_cells bsegs m2 (q + -96) _ |- _ => rename H into FR2 end.
    lazymatch goal with H : rw_cells bsegs m2 (q + 128) _ |- _ => rename H into OUT2 end.
    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN _ _ _ EL ltac:(lia) ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; pose proof TY as TY0; unfold ty in TY.
    4: {
      unfold t_arr in TY. rewrite TY. step. if_false.
      shz_pose SZN (f + 216). step. shz_norm. step. if_false.
      shz_pose SZN (f + 208). step. shz_norm. step. if_false.
      step. step. lstep. lstep. lstep. astep. astep. astep. zstep.
      name_mem m3.
      lazymatch goal with H : rw_cells bsegs m3 (q + -96) _ |- _ => rename H into FR3 end.
      lazymatch goal with H : rw_cells bsegs m3 (q + 128) _ |- _ => rename H into OUT3 end.
      lazymatch goal with H : stk bsegs m3 _ _ |- _ => rename H into ST3 end.
      lazymatch goal with H : mem_inv bsegs m3 |- _ => rename H into MI3 end.
      lazymatch goal with H : munch _ m m3 |- _ => rename H into MU3 end.
      lazymatch goal with H : wmono bsegs m m3 |- _ => rename H into WM3 end.
      pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ TILES) as [IE CC].
      eapply evt_eq; [| eapply (XARR m3 d' e2 c2)]; [atp_st_eq| exact MU3| exact WM3| exact MI3| exact ST3| unfold w28_frame; cbn [app]; exact FR3| exact OUT3| exact TY0| exact NXT| exact TILES| lia]. }

    all: assert (NA : ttype (ae_T E 1) <> 91) by (unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_obj in TY; lia).
    all: step; if_cases KB; zify_cond KB; [| exfalso; rewrite ?land64_mod, ?Z.mod_small in KB by lia; lia].
    all: step; if_dead1 by LO LOW.
    all: astep; astep; astep; astep; zstep.

    all: lazymatch goal with STx : stk bsegs ?mx _ _, MIx : mem_inv bsegs ?mx, FRx : rw_cells bsegs ?mx (_ + -96) _, OUTx : rw_cells bsegs ?mx (_ + 128) _,
                             MUx : munch _ ?m0 ?mx, WMx : wmono bsegs ?m0 ?mx, NAx : ttype _ <> 91 |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
           eapply evt_eq; [| eapply (XNA mx)]; [unfold e_asan_memset; atp_st_eq| exact MUx| exact WMx| exact MIx| exact STx| unfold w28_frame; cbn [app]; exact FRx| exact OUTx| exact NAx]
         end.
  Qed.

  Lemma w28_epi : forall (viaj : bool) (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q : Z) (j32 : list byte)
      (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 v0 v1 v2 v3 v4 v5 v6 : word) (RA : Z),
    rw_cells bsegs m (q + -96) (w28_frame [CB 32 j32] v6 v5 v4 v3 v2 v1 v0 (wz RA)) ->
    stk bsegs m (ae_lo E) (q + -96) -> ae_lo E + 96 <= q -> q <= ae_hi E -> mem_inv bsegs m -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (stk bsegs m (ae_lo E) q ->
     K (MS (mkR (wz RA) (wz q) gp (wz TPV) t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RA) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR ra (wz (q + -96)) gp (wz TPV) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz (if viaj then 0xb5aa4 else 0xb5ad8)) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until RA. intros FR ST LO HI MI RA0 RA2 HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold w28_frame in FR. cbn [app] in FR.
    assert (J : evt bsegs K (MS (mkR ra (wz (q + -96)) gp (wz TPV) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0xb5ad8) fc None m (seg_rom bsegs))).
    { do 8 step. astep. release_frame FR ST q. step.
      replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
      lazymatch goal with H : stk bsegs m _ q |- _ => apply evt_done; exact (HK H) end. }
    destruct viaj; [zstep; exact J| exact J].
  Qed.

  Lemma w28_after_set : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out : Z) (j32 zb j1 j2 : list byte)
      (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 v0 v1 v2 v3 v4 v5 v6 : word) (RA : Z),
    rw_cells bsegs m (q + -96) (w28_frame [CB 32 j32] v6 v5 v4 v3 v2 v1 v0 (wz RA)) ->
    stk bsegs m (ae_lo E) (q + -96) -> ae_lo E + 96 <= q -> q <= ae_hi E -> mem_inv bsegs m -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    rw_cells bsegs m out [CB 16 zb; CB 4 j1; CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> shz m out 24 ->
    (forall m', munch [(out, out + 24)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
       rw_cells bsegs m' out [CB 16 zb; C4 (wz 17); CB 4 j2] ->
       K (MS (mkR (wz RA) (wz q) gp (wz TPV) t0 t1 t2 v0 v1 (wz 17) a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RA) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb5ac0) (wz (q + -96)) gp (wz TPV) t0 t1 t2 (wz (out + 16)) (wz out) (wz out) a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0xb5ac0) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until RA. intros FR ST LO HI MI RA0 RA2 OUT QO OH SHZO HK. unfold w28_frame in FR. cbn [app] in FR.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP, SHB in *.
    pose proof (munch_refl [(out, out + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    chk0 SHZO (out + 16). step. if_false. astep. lstep.
    name_mem m1.
    lazymatch goal with H : rw_cells bsegs m1 (q + -96) _ |- _ => rename H into FR1 end.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells bsegs m1 out _ |- _ => rename H into OUT1 end.
    eapply (w28_epi false K m1 F fc q j32); [unfold w28_frame; cbn [app]; exact FR1| exact ST1| lia| lia| exact MI1| exact RA0| exact RA2|].
    intros ST1'. exact (HK m1 MU WM MI1 ST1' OUT1).
  Qed.
End W28.

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
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2 Z45 Z5k Z3v Z3t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition atkey_W (spk sret : Z) : list (Z * Z) := [(spk + -160, spk); (sret, sret + 24)].

Definition atkey_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma sub_fp_ktix : forall spk sret, sub_fp [(spk + -144 + -16, spk + -144)] (atkey_W spk sret).
Proof. intros spk sret x Hx. unfold atkey_W in Hx. cbn [outside] in *. lia. Qed.

Section AtKey.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Lemma atkey_pre : forall (K : machine_state -> Prop) (m0 : mem) (F : bvmap 5 word) (fc : bv 32) (i e c spk sret node Kp Lk RA : Z)
      (gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t3 t4 t5 t6 : word) (oa ob oc od : list byte),
    ty (ae_T E) i = t_obj -> tnext (ae_T E i) = e + 1 -> tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (i + 1) e c ->
    0 <= i -> e + 1 <= ae_n E - 1 ->
    rw_cells bsegs m0 node [C8 (wz (ae_DOC E)); C8 (wz i)] -> spk <= node -> node + 16 <= ae_hi E -> node mod 8 = 0 ->
    rw_cells bsegs m0 sret [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] -> spk <= sret -> sret + 24 <= ae_hi E -> sret mod 8 = 0 ->
    0 <= Kp < 2^64 -> 0 <= Lk < 2^64 ->
    (forall m, munch (atkey_W spk sret) m0 m -> wmono bsegs m0 m -> AINV_A E m) ->
    (forall m, munch (atkey_W spk sret) m0 m -> wmono bsegs m0 m -> shb_cells m) ->
    (forall m, munch (atkey_W spk sret) m0 m -> wmono bsegs m0 m -> shz m (ae_DOC E) 16) ->
    (forall m, munch (atkey_W spk sret) m0 m -> wmono bsegs m0 m -> shz m (ae_TAPE E) (8 * ae_n E)) ->
    (forall m, munch (atkey_W spk sret) m0 m -> wmono bsegs m0 m -> shz m node 16) ->
    stk bsegs m0 (ae_lo E) spk -> ae_lo E + 160 <= spk -> spk + 16 <= ae_hi E -> spk mod 16 = 0 -> mem_inv bsegs m0 ->
    0 <= RA < 2^64 -> RA mod 2 = 0 ->

    (forall (m : mem) (x5 x6 x7 xa3 xa4 xa5 xa6 xa7 xs0 xs2 xs3 xs4 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word) (j0 j16 j24 : list byte),
       munch (atkey_W spk sret) m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) (spk + -144) ->
       rw_cells bsegs m (spk + -144) ([CB 8 j0; C8 (wz sret); CB 8 j16; CB 8 j24; C8 (wz Kp)] ++ atkey_saved (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
       rw_cells bsegs m sret [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
       evt bsegs K (MS (mkR (wz 0x9a718) (wz (spk + -144)) gp (wz TPV) x5 x6 x7 xs0 (wz (sret + 16)) (wz sret) (wz 0) (wz 16) xa3 xa4 xa5 xa6 xa7
                          xs2 xs3 xs4 (wz sret) xs6 (wz 2147450880) xs8 xs9 xs10 xs11 x28 x29 x30 x31)
                     F (wz e_asan_memset) fc None m (seg_rom bsegs))) ->

    (forall (m : mem) (x1 x5 x6 x7 xa3 xa4 xa5 xa6 xa7 xs6 x28 x29 x30 x31 : word) (j0 : list byte),
       i + 1 <> e ->
       munch (atkey_W spk sret) m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) (spk + -144) ->
       rw_cells bsegs m (spk + -144) ([CB 8 j0; C8 (wz sret); C8 (wz 4294967295); C8 (wz 4294967297); C8 (wz Kp)] ++ atkey_saved (wz RA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
       rw_cells bsegs m sret [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
       evt bsegs K (MS (mkR x1 (wz (spk + -144)) gp (wz TPV) x5 x6 x7 (wz 67240448) (wz Lk) (wz 1) (wz 1) (wz 4294967297) xa3 xa4 xa5 xa6 xa7
                          (wz 1) (wz (ae_DOC E)) (wz (i + 1)) (wz (ae_DOC E + 8)) xs6 (wz 2147450880) (wz e) (wz 32) (wz 72057594037927935)
                          (wz ((ae_DOC E + 8) / 8 + 2147450880)) x28 x29 x30 x31)
                     F (wz 0x9a7b8) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz RA) (wz spk) gp (wz TPV) t0 t1 t2 s0 s1 (wz sret) (wz node) (wz Kp) (wz Lk) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ATP_ATKEY_A) fc None m0 (seg_rom bsegs)).
  Proof using OK.
    intros until od. intros TY NXT TILES I0 EN NODEC QN NB N8 OUTC QO OB O8 KPR LKR AIW SHBW SHZDW SHZTW SHZNW ST LO HI S16 MI RA0 RA2 XNF XLOOP.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold ATP_ATKEY_A, SEGTOP_A, USTACK_TOP in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TILES) as [IE CC].
    unfold ty in TY. pose proof (ttype_range _ _ TY ltac:(unfold t_obj; lia) ltac:(unfold t_obj; lia)) as TIR.
    pose proof (munch_refl (atkey_W spk sret) m0) as MU. pose proof (wmono_refl bsegs m0) as WM. unfold atkey_W in MU.

    step. carve_frame 144%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 144 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB 8 (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    do 13 step. step.

    pose proof (SHBW _ MU WM) as [G1 G2].
    step. step. step. step.
    name_mem m1.

    chk0 SHZNW node. step. if_false.
    step. step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
    astep. chk0 SHZNW (node + 8). step. if_false.
    step. step. step.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    eapply (tix_cps E OK _ m1 F fc (spk + -144) i 0x9a62c); [exact (AIW m1 MU WM)| lia| exact (SHBW m1 MU WM)| | exact ST1| lia| lia| clear - S16; Z.div_mod_to_equations; lia| exact MI1| lia| reflexivity|].
    { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_ktix spk sret) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST1 MI1. intros m2 ya1 ya3 ya4 MU12 WM12 MI2 ST2.
    transport_after_call bsegs m1 m2 MU12 WM12. clear MU12 WM12.
    pose proof (AIW m2 MU WM) as (TAPEB2 & _ & _ & _ & _).
    pose proof (tape_read_type m2 (ae_TAPE E) (ae_tws E) i TAPEB2 ltac:(lia) TIR) as RDB2. rewrite TY in RDB2. unfold t_obj in RDB2.

    chk0 SHZTW (ae_TAPE E + 8 * i). step. if_false.
    astep. astep. astep. step. if_false. astep. astep. astep. astep. step. if_true.
    astep. astep. astep. astep. astep. step. if_false.

    shz_pose SHZNW node. step. shz_norm. step. if_false.
    step. step. if_dead1 by DF DS. astep. step. if_dead1 by D8 DF DS.
    shz_pose SHZNW (node + 8). step. shz_norm. step. if_false.
    step. step.
    eapply (tix_cps E OK _ m2 F fc (spk + -144) i 0x9a6b4); [exact (AIW m2 MU WM)| lia| exact (SHBW m2 MU WM)| | exact ST2| lia| lia| clear - S16; Z.div_mod_to_equations; lia| exact MI2| lia| reflexivity|].
    { intros m' MU' WM'. exact (SHZDW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_ktix spk sret) MU')) (wmono_trans bsegs _ _ _ WM WM')). }
    clear ST2 MI2 TAPEB2 RDB2. intros m3 za1 za3 za4 MU23 WM23 MI3 ST3.
    transport_after_call bsegs m2 m3 MU23 WM23. clear MU23 WM23.
    pose proof (AIW m3 MU WM) as (TAPEB3 & _ & _ & DOCC3 & _).
    pose proof (tape_read_lo32 E m3 i TAPEB3 ltac:(lia)) as RDL3.

    chk0 SHZTW (ae_TAPE E + 8 * i). step. if_false.
    step. rewrite zx32_tnext by lia. rewrite NXT. step.
    step.
    shz_pose SHZNW node. step. shz_norm. step. if_false.
    shz_pose SHZNW (node + 8). step. shz_norm. step. if_false.
    step. astep. astep. try clear TAPEB3. try clear RDL3. try clear DOCC3.
    name_mem mq.
    lazymatch goal with H : rw_cells bsegs mq (spk + -144) _ |- _ => rename H into FR3 end.
    lazymatch goal with H : rw_cells bsegs mq sret _ |- _ => rename H into OUT3 end.
    lazymatch goal with H : stk bsegs mq _ _ |- _ => rename H into ST3' end.
    lazymatch goal with H : mem_inv bsegs mq |- _ => rename H into MI3' end.
    step. if_cases KE; zify_cond KE.
    2:{
        step. step. if_dead1 by QO LO LOW. astep. astep. astep. step.
        eapply evt_eq; [| eapply (XNF mq)]; [unfold e_asan_memset; atp_st_eq| exact MU| exact WM| exact MI3'| exact ST3'| unfold atkey_saved; cbn [app]; exact FR3| exact OUT3]. }

    step. astep. astep. astep. astep. astep. astep. lstep. astep. astep.
    astep. replace (0 <? ae_DOC E) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    astep. rewrite D8. astep. astep. cbn [Z.ltb Z.eqb Z.compare Pos.compare Z.b2z Z.land]. astep. astep. astep. astep. lstep.
    name_mem m4.
    lazymatch goal with H : rw_cells bsegs m4 (spk + -144) _ |- _ => rename H into FR4 end.
    lazymatch goal with H : rw_cells bsegs m4 sret _ |- _ => rename H into OUT4 end.
    lazymatch goal with H : stk bsegs m4 _ _ |- _ => rename H into ST4 end.
    lazymatch goal with H : mem_inv bsegs m4 |- _ => rename H into MI4 end.
    eapply evt_eq; [| eapply (XLOOP m4)]; [atp_st_eq| exact KE| exact MU| exact WM| exact MI4| exact ST4| unfold atkey_saved; cbn [app]; exact FR4| exact OUT4].
  Qed.
End AtKey.

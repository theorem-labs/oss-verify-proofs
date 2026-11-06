(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/RL/G/G_printf_snsink.v, with its module paths, module names and addresses changed; 110 of its 152 lines of code are new or changed and 129 lines of the source are left out. *)
(* reac-pw/fuzz_link, PLAIN build: the FILE sink lemmas for CJ's printf_core on link's memory FILE.

   The sink is `SINK_mf` of lib/Prog/mf_sink_c.v (the FILE at f, its 1024-byte buffer at f + 280),
   TOPOK is `TOPOK_mf`, OUT is CJ's `OUT_snf OM`. The four lemmas are the four sink premises of
   `printf_core_heap_all` (mf_sink_c.v), in CJ's vocabulary (lib/CJ/RL/GX/G_printf_core_common.v,
   module G_printf_iface: sink_frame_stmt, sink_flags_stmt, topok_stmt, out_stmt).

   Adapted from lib/CJ/RL/GX/G_printf_snfsink.v: snf_sink_frame, snf_sink_flags, snf_topok, and the
   ROOM branch of snf_out (one call of __fwritex through its fit contract `fwritex_contract`,
   lib/CJ/RL/G/G_fwritex.v). A piece that does not fit OM is the model's unreachable arm; a piece
   that fits OM fits the buffer (`mf_fit_room`: k + OM <= 1024), so __fwritex copies it and does
   not call f->write. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require Import G_memcpy G_fwritex G_pad G_fmt_fp_lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import G_printf_snfsink.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.StoreCache.LiaClosure.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import mf_sink_c.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section Img.
  Context {IMG : RImg}.
  Context {RS_35000 : RelSym (sym 0x35000)}.
  Let rp_35000 : (0 <= sym 0x35000 /\ sym 0x35000 < 2^30)%Z := @rel_sym_pf _ RS_35000.
  Context {RS_34288 : RelSym (sym 0x34288)}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {RS_22e18 : RelSym (sym 0x22e18)}.
  Let rp_22e18 : (0 <= sym 0x22e18 /\ sym 0x22e18 < 2^30)%Z := @rel_sym_pf _ RS_22e18.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)%Z}.
  Let rl0_1 : (sym 0x34288 + 8 <= sym 0x35000)%Z := @zfact_pf _ RL0_1.
  Context {RQ_22e18 : ZFact (0x14000 <= sym 0x22e18)%Z}.
  Let rq_22e18 : (0x14000 <= sym 0x22e18)%Z := @zfact_pf _ RQ_22e18.
  Context {SPEC_fwritex : fwritex_contract}.

  Ltac plia := lia0_prune_s; lia.
  Ltac dsolve := first [ plia | match goal with H : _ \/ _ |- _ => destruct H as [H|H]; plia end ].
  Ltac dj := repeat (match goal with |- _ /\ _ => split end); try exact I; dsolve.
  Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.

  (* The fit premise: a piece that fits OM fits the room left in the buffer. *)
  Lemma mf_fit_room : forall f k OM pb fl0 j1 j2 lbfw jx (m : mem) (o bs : list Z),
    SINK_mf f k OM pb fl0 j1 j2 lbfw jx m o -> zlength o + zlength bs <= OM ->
    exists bjunk : list byte,
      wfile m f fl0 j1 j2 lbfw (f + 280) (pb ++ zb o) bjunk
      /\ k + zlength o + zlength bjunk = 1024
      /\ (length (zb bs) <= length bjunk)%nat.
  Proof.
    intros f k OM pb fl0 j1 j2 lbfw jx m o bs HS FIT.
    destruct HS as (bj & WF & _ & Lpb & HL & _ & HOM & _).
    exists bj. split; [exact WF|]. split; [exact HL|].
    rewrite zb_len. unfold zlength in *. lia.
  Qed.

  Lemma mf_sink_frame : forall f k OM pb fl0 j1 j2 lbfw jx RC RCS RE RES,
    sink_frame_stmt f (f + 280) 1024 RC RCS RE RES (SINK_mf f k OM pb fl0 j1 j2 lbfw jx).
  Proof.
    intros f k OM pb fl0 j1 j2 lbfw jx RC RCS RE RES.
    unfold sink_frame_stmt. intros W m m' o HS MU WM DF DB _ _.
    destruct HS as (bj & WF & FX & Lpb & HL & HO & HOM & Fpos & Fhi & Fpl).
    destruct WF as (FC & BUF & FL & LBF & Bpos & Bhi & SEP).
    unfold zlength in *.
    exists bj.
    split; [|split].
    - unfold wfile. split; [|split].
      + eapply rw_cells_transport; [exact FC | exact MU | exact WM | ].
        eapply Forall_disj; [exact DF | | | ]; cbn [cells_size csize Nat.add FILE_cells]; lia.
      + eapply rw_cells_transport; [exact BUF | exact MU | exact WM | ].
        eapply Forall_disj; [exact DB | | | ]; cbn [cells_size csize Nat.add];
          rewrite ?length_app, ?zb_len; lia.
      + repeat (match goal with |- _ /\ _ => split end); assumption.
    - eapply rw_cells_transport; [exact FX | exact MU | exact WM | ].
      eapply Forall_disj; [exact DF | | | ]; cbn [cells_size csize Nat.add]; lia.
    - repeat (match goal with |- _ /\ _ => split end); assumption.
  Qed.

  Lemma mf_sink_flags : forall f k OM pb fl0 j1 j2 lbfw jx,
    sink_flags_stmt f (SINK_mf f k OM pb fl0 j1 j2 lbfw jx).
  Proof.
    intros f k OM pb fl0 j1 j2 lbfw jx. unfold sink_flags_stmt. intros m o HS.
    destruct HS as (bj & WF & _). destruct WF as (FC & _ & FL & _).
    exists fl0. split; [|exact FL].
    unfold FILE_cells in FC. apply (proj1 (rw_cells_app img_segs m f [CB 1 [fl0]] _)) in FC. exact (proj1 FC).
  Qed.

  Lemma mf_topok : topok_stmt TOPOK_mf.
  Proof. unfold topok_stmt, TOPOK_mf. intros. exact I. Qed.

  Lemma mf_out : forall f k OM pb fl0 j1 j2 lbfw jx RC RCS RE RES,
    out_stmt f (f + 280) 1024 RC RCS RE RES (SINK_mf f k OM pb fl0 j1 j2 lbfw jx) TOPOK_mf (OUT_snf OM).
  Proof.
    intros f k OM pb fl0 j1 j2 lbfw jx RC RCS RE RES.
    unfold out_stmt. intros until canary.
    intros HS SRC RNG LB Ha1 Ha2 ST LO GLO SPHI TQ SSP MI D1 D2 D3 D4 E1 E2 E3 E4 E5. rename st into o.
    unfold OUT_snf. apply implM_get_k.
    destruct (Z.leb_spec0 (zlength o + zlength bs) OM) as [FIT|NOFIT]; [ | apply implM_unr ].
    apply implM_put.
    destruct (mf_fit_room f k OM pb fl0 j1 j2 lbfw jx m o bs HS FIT) as (bj & WF & HL & ROOM).
    destruct HS as (bj0 & _ & FX & Lpb & _ & HO & HOM & Fpos & Fhi & Fpl).
    clear TQ RNG D3 D4 E4 E5.
    unfold OUT_DEPTH, GLOBALS_TOP in *.
    pose proof (zb_len bs) as LZb. pose proof (zb_len o) as LZo.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
    assert (EFp : bv_unsigned a2 = f) by (subst a2; apply unsigned_lit; plia).
    destruct SSP as [SS1 SS2]. unfold got_ssp, ssp_guard in SS1, SS2.
    destruct (stk_split _ _ _ (bv_unsigned sp - 64) _ ST ltac:(plia)) as [ST1 ST2].
    assert (LC : Z.of_nat (length (pb ++ zb o)) = k + zlength o)
      by (rewrite length_app, zb_len; unfold zlength; lia).
    unfold zlength in *.
    eapply evt_mono.
    { eapply (SPEC_fwritex ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m fl0 j1 j2 lbfw (f + 280) (pb ++ zb o) bj (zb bs));
        rewrite ?EFp.
      - exact WF.
      - exact SRC.
      - subst a1. rewrite unsigned_lit by plia. rewrite LZb. reflexivity.
      - exact ROOM.
      - exact ST2.
      - exact MI.
      - plia.
      - destruct D1; [left|right]; plia.
      - destruct D2; [left|right]; plia.
      - rewrite LZb. destruct E1; [left|right]; plia.
      - rewrite LZb. destruct E3; [left|right]; plia.
      - rewrite LZb. destruct E2; [left|right]; plia. }
    cbv beta. intros ms' P. unfold fwritex_post in P. rewrite ?EFp in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & WF2 & SRC').
    assert (TR : forall A cs, rw_cells img_segs m A cs ->
              disjoint_from [(bv_unsigned sp - 64, bv_unsigned sp);
                             (f + 280 + Z.of_nat (length (pb ++ zb o)),
                              f + 280 + Z.of_nat (length (pb ++ zb o)) + Z.of_nat (length (zb bs)));
                             (f + 40, f + 48)] A (Z.of_nat (cells_size cs)) -> rw_cells img_segs m' A cs)
      by (intros; eapply rw_cells_transport; eauto).
    unfold out_post, SR. eexists x5, x6, x7, _, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear_disj. lia. }
    split; [exact WM|]. split; [exact MI'|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; dj] | exact ST' | plia ]. }
    split.
    { assert (FX' : rw_cells img_segs m' (f + 148) [CB 84 jx])
        by (apply TR; [exact FX|]; cbn [disjoint_from cells_size csize Nat.add]; dj).
      exists (skipn (length (zb bs)) bj).
      repeat (match goal with |- _ /\ _ => split end).
      - rewrite zb_app2, app_assoc. exact WF2.
      - exact FX'.
      - exact Lpb.
      - unfold zlength. rewrite length_app, length_skipn. plia.
      - unfold zlength. rewrite length_app. plia.
      - exact HOM.
      - exact Fpos.
      - exact Fhi.
      - unfold GLOBALS_TOP. exact Fpl. }
    split.
    { unfold ssp_cells, got_ssp, ssp_guard. split.
      - apply TR; [exact SS1|]. cbn [disjoint_from cells_size csize Nat.add]. dj.
      - apply TR; [exact SS2|]. cbn [disjoint_from cells_size csize Nat.add]. dj. }
    exact SRC'.
  Qed.

End Img.

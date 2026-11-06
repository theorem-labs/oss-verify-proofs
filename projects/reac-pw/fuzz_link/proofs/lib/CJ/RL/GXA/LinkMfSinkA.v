(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/RL/G/G_printf_snsink.v, with its module paths changed; 444 of its 486 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied unchanged from plugin-hostd/fuzz_reply lib/CJ/RL/GXA at 568db058c1d; only the module path prefix is rewritten to this harness. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/CJ/RL/GXA/G_printf_snfsink.v, with its module paths changed; 126 of its 168 lines of code are new or changed and 444 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (fuzz_link.asan, GXA / CJ engine): the FILE sink of printf_core on link's memory
   FILE (fmemopen "w": the FILE at f, its 1024-byte buffer at f + 280).

   - `SINK_mfa`: the sink. St = the text printed so far (o). The FILE is as __fwritex reads it (`wfile`,
     lib/CJ/RL/G/G_fwritex.v: the first 148 bytes, the window active, the buffer holding the k bytes pending
     before the call, then o, then junk); the 84 bytes at f + 148 are kept as they are. It is the plain lane's
     SINK_mf (lib/Prog/mf_sink_c.v) with the FILE placed above GXA's GLOBALS_TOP (sym 0x35000), as GXA's
     printf_core_a_stmt places a heap FILE and buffer (no arm below 64 KiB).
   - `TOPOK_mfa`: True (any stack top).
   - `mf_out_ready copy_ready f`: what the room arm of __fwritex asks of the memcpy wrapper (sym 0x21334): a copy
     into the buffer from S, after any store that changes only the buffer, wpos (f + 40) and the callee window.

   The four lemmas are the four sink premises of GXA's `printf_core_a_all` (lib/CJ/RL/GXA/G_vfprintf_snf.v), in the
   forms of lib/CJ/RL/GXA/G_printf_core_common.v (module G_printf_iface):
   - `mfa_sink_frame`: the sink holds after a store outside the FILE and the buffer;
   - `mfa_sink_flags`: the first flags byte, with F_ERR clear;
   - `mfa_topok`: TOPOK holds below a top where it holds;
   - `mfa_out_a`: OUT = `OUT_snf OM` through __fwritex (sym 0x17d50). A piece that does not fit OM is the model's
     unreachable arm. A piece that fits OM fits the room left in the buffer (k + OM <= 1024), so __fwritex takes
     its room arm and copies it (`fwritex_room_stmt`, G_fwritex_room.v); it never calls f->write. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA Require Import CopyCall G_fwritex_room G_printf_snfsink.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.StoreCache.LiaClosure.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section Img.
  Context {IMG : RImg}.

Section MfSink.
  Variables (f k OM : Z) (pb : list byte) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (jx : list byte).

  Definition SINK_mfa (m : mem) (o : list Z) : Prop :=
    exists bjunk : list byte,
      wfile m f fl0 j1 j2 lbfw (f + 280) (pb ++ zb o) bjunk
      /\ rw_cells img_segs m (f + 148) [CB 84 jx]
      /\ Z.of_nat (length pb) = k /\ k + zlength o + zlength bjunk = 1024
      /\ zlength o <= OM /\ k + OM <= 1024
      /\ 0 < f /\ f + 1304 < 2^63 /\ GLOBALS_TOP <= f.
End MfSink.

Definition TOPOK_mfa (sp : Z) : Prop := True.

  Context {RS_22e18 : RelSym (sym 0x22e18)}.
  Let rp_22e18 : (0 <= sym 0x22e18 /\ sym 0x22e18 < 2^30)%Z := @rel_sym_pf _ RS_22e18.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)%Z}.
  Let rl0_1 : (sym 0x34288 + 8 <= sym 0x35000)%Z := @zfact_pf _ RL0_1.
  Variable copy_ready : mem -> Z -> Z -> Z -> Z -> Prop.
  Context {SPEC_fwritex_room : fwritex_room_stmt copy_ready}.

(* The readiness of the room arm: a copy of N <= L bytes from S into the buffer, after any store that changes
   only the buffer, wpos and the callee window [sp - SN_WRITE_DEPTH, sp). *)
Definition mf_out_ready (f : Z) (m : mem) (sp S L : Z) : Prop :=
  forall m' Dst N,
    munch [(f + 280, f + 1304); (f + 40, f + 48); (sp - SN_WRITE_DEPTH, sp)] m m' -> wmono img_segs m m' ->
    f + 280 <= Dst -> Dst + N <= f + 1304 -> 0 <= N <= L ->
    copy_ready m' (sp - 64) Dst S N.

  Ltac plia := try unfold SN_WRITE_DEPTH, COPY_DEPTH in *; lia0_prune_s; lia.
  Ltac dsolve := first [ plia | match goal with H : _ \/ _ |- _ => destruct H as [H|H]; plia end ].
  Ltac dj := repeat (match goal with |- _ /\ _ => split end); try exact I; dsolve.
  Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
  Ltac mk_tr MU TR :=
    lazymatch type of MU with munch ?W ?m0 ?m1 =>
      assert (TR : forall A cs, rw_cells img_segs m0 A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells img_segs m1 A cs)
        by (intros; eapply rw_cells_transport; eauto)
    end.

Lemma mf_ready_room : forall f m sp S L nc lb,
  mf_out_ready f m sp S L -> 0 <= nc -> 0 <= lb -> nc + lb <= 1024 -> lb <= L ->
  fwritex_room_ready copy_ready m sp f (f + 280 + nc) S lb.
Proof.
  intros f m sp S L nc lb R H1 H2 H3 H4 m' MU WM.
  refine (R m' (f + 280 + nc) lb _ WM _ _ _).
  - eapply munch_weaken; [|exact MU].
    unfold sub_fp, fwritex_room_footprint. cbn [outside]. intros x Hx. lia.
  - lia.
  - lia.
  - lia.
Qed.

Lemma mfa_sink_frame : forall f k OM pb fl0 j1 j2 lbfw jx RC RCS RE RES,
  sink_frame_stmt f (f + 280) 1024 RC RCS RE RES (SINK_mfa f k OM pb fl0 j1 j2 lbfw jx).
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

Lemma mfa_sink_flags : forall f k OM pb fl0 j1 j2 lbfw jx,
  sink_flags_stmt f (SINK_mfa f k OM pb fl0 j1 j2 lbfw jx).
Proof.
  intros f k OM pb fl0 j1 j2 lbfw jx. unfold sink_flags_stmt. intros m o HS.
  destruct HS as (bj & WF & _). destruct WF as (FC & _ & FL & _).
  exists fl0. split; [|exact FL].
  unfold FILE_cells in FC. apply (proj1 (rw_cells_app img_segs m f [CB 1 [fl0]] _)) in FC. exact (proj1 FC).
Qed.

Lemma mfa_topok : topok_stmt TOPOK_mfa.
Proof. unfold topok_stmt, TOPOK_mfa. intros. exact I. Qed.

Lemma mfa_out_a : forall f k OM pb fl0 j1 j2 lbfw jx RC RCS RE RES,
  out_a_stmt f (f + 280) 1024 RC RCS RE RES (SINK_mfa f k OM pb fl0 j1 j2 lbfw jx) TOPOK_mfa (OUT_snf OM)
             (mf_out_ready f).
Proof.
  intros f k OM pb fl0 j1 j2 lbfw jx RC RCS RE RES.
  unfold out_a_stmt. intros until canary.
  intros HS SRC RNG LB Ha1 Ha2 ST LO GLO SPHI TQ SSP MI D1 D2 D3 D4 E1 E2 E3 E4 E5 RDY. rename st into o.
  unfold OUT_snf. apply implM_get_k.
  destruct (Z.leb_spec0 (zlength o + zlength bs) OM) as [FIT|NOFIT]; [ | apply implM_unr ].
  apply implM_put.
  destruct HS as (bj & WF & FX & Lpb & HL & HO & HOM & Fpos & Fhi & Fpl).
  clear TQ RNG D3 D4 E4 E5.
  unfold OUT_DEPTH, GLOBALS_TOP in *.
  pose proof (zb_len bs) as LZb. pose proof (zb_len o) as LZo.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
  assert (EFp : bv_unsigned a2 = f) by (subst a2; apply unsigned_lit; plia).
  destruct SSP as [SS1 SS2]. unfold got_ssp, ssp_guard in SS1, SS2.
  destruct (stk_split _ _ _ (bv_unsigned sp - SN_WRITE_DEPTH) _ ST ltac:(plia)) as [ST1 ST2].
  unfold SN_WRITE_DEPTH, COPY_DEPTH in ST1, ST2.
  assert (LC : Z.of_nat (length (pb ++ zb o)) = k + zlength o)
    by (rewrite length_app, zb_len; unfold zlength; lia).
  unfold zlength in *.
  eapply evt_mono.
  { eapply (SPEC_fwritex_room ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m fl0 j1 j2 lbfw (f + 280) (pb ++ zb o) bj (zb bs));
      rewrite ?EFp, ?LC, ?LZb.
    - exact WF.
    - exact SRC.
    - subst a1. rewrite unsigned_lit by plia. reflexivity.
    - plia.
    - exact ST2.
    - exact MI.
    - plia.
    - eapply mf_ready_room; [ exact RDY | plia | plia | plia | plia ].
    - destruct D1; [left|right]; plia.
    - destruct D2; [left|right]; plia.
    - destruct E1; [left|right]; plia.
    - destruct E3; [left|right]; plia.
    - destruct E2; [left|right]; plia. }
  cbv beta. intros ms' P. unfold fwritex_room_post, fwritex_room_footprint, SN_WRITE_DEPTH, COPY_DEPTH in P.
  rewrite ?EFp, ?LC, ?LZb in P.
  destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & WF2 & SRC').
  mk_tr MU TR.
  unfold out_post, SR. eexists x5, x6, x7, _, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
  split; [reflexivity|].
  split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear_disj. lia. }
  split; [exact WM|]. split; [exact MI'|].
  split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; dj] | exact ST' | plia ]. }
  split.
  { assert (FX' : rw_cells img_segs m' (f + 148) [CB 84 jx])
      by (apply TR; [exact FX|]; cbn [disjoint_from cells_size csize Nat.add]; dj).
    exists (skipn (length bs) bj).
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

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I Require IImgP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_pre.
Module F_fmt_fp_pre.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.P_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad.P_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad.P_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts2.F_frexpl.P_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)
Notation midK := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.midK (only parsing).
Notation MidK := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.MidK (only parsing).
Notation K_pad := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_pad (only parsing).
Notation K_jk40 := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_jk40 (only parsing).
Notation K_jk8 := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_jk8 (only parsing).
Notation K_jk3 := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_jk3 (only parsing).
Notation K_jk12 := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_jk12 (only parsing).
Notation K_jk37 := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_jk37 (only parsing).
Notation K_p1 := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_p1 (only parsing).
Notation K_prefix := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_prefix (only parsing).
Notation K_pl := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_pl (only parsing).
Notation K_plz := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_plz (only parsing).
Notation K_pfx := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_pfx (only parsing).
Notation K_Ft := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.K_Ft (only parsing).

(* [comment removed for export] *)
Lemma wfile_frame_below : forall m Fp fl0 j1 j2 lbfw B c jk (a : Z) bs,
  wfile m Fp fl0 j1 j2 lbfw B c jk -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= Fp)%Z -> (a + Z.of_nat (length bs) <= B)%Z ->
  wfile (write_to_mem m (wa a) bs) Fp fl0 j1 j2 lbfw B c jk.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.wfile_frame_below | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.wfile_frame_below as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.wfile_frame_below | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.wfile_frame_below | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.wfile_frame_below OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.
Lemma wfile_transport_below : forall W m m' Fp fl0 j1 j2 lbfw B c jk,
  wfile m Fp fl0 j1 j2 lbfw B c jk -> munch W m m' -> wmono psegs m m' ->
  (forall iv, In iv W -> (snd iv <= Fp /\ snd iv <= B)%Z) ->
  wfile m' Fp fl0 j1 j2 lbfw B c jk.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.wfile_transport_below | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.wfile_transport_below as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.wfile_transport_below | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.wfile_transport_below | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre.wfile_transport_below OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.

Ltac transport_chunks segs m a bs ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wfile m ?Fp ?fl0 ?j1 ?j2 ?lbfw ?B ?c ?jk |- _ =>
      first [ apply (wfile_frame_below m Fp fl0 j1 j2 lbfw B c jk a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wfile m ?Fp ?fl0 ?j1 ?j2 ?lbfw ?B ?c ?jk |- _ =>
      first [ apply (wfile_transport_below W m m' Fp fl0 j1 j2 lbfw B c jk) in H;
              [ | exact MU | exact WM | let iv := fresh "iv" in let Hiv := fresh "Hiv" in
                                       intros iv Hiv; cbn [In] in Hiv; decompose [or] Hiv; try subst iv; cbn [snd]; first [lia | contradiction] ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
Ltac transport_chunks_extra_wfile m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : wfile m ?Fp ?fl0 ?j1 ?j2 ?lbfw ?B ?c ?jk |- _ =>
      first [ apply (wfile_frame_below m Fp fl0 j1 j2 lbfw B c jk a bs) in H;
              [ | exact Ha | rewrite Hn; tslia | rewrite Hn; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.
Ltac transport_call_extra_wfile segs W m m' MU WM :=
  repeat match goal with
  | H : wfile m ?Fp ?fl0 ?j1 ?j2 ?lbfw ?B ?c ?jk |- _ =>
      first [ apply (wfile_transport_below W m m' Fp fl0 j1 j2 lbfw B c jk) in H;
              [ | exact MU | exact WM | let iv := fresh "iv" in let Hiv := fresh "Hiv" in
                                       intros iv Hiv; cbn [In] in Hiv; decompose [or] Hiv; try subst iv; cbn [snd]; first [lia | contradiction] ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  end.
End F_fmt_fp_pre.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.
Import F_fmt_fp_pre.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Lemma unsigned_lit8 : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre2.unsigned_lit8 | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre2.unsigned_lit8 as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre2.unsigned_lit8 | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre2.unsigned_lit8 | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre2.unsigned_lit8 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.

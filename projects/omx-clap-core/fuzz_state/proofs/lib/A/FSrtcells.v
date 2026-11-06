(* fs.asan's two named runtime-cell premises in the Bz tree's words, and the three string contracts without them.
   rule 24: no function proved (kind: start-up facts - lemmas reading the certified start-up table; no walk).
   The start-up facts themselves are S0-native, in lib/A/FSrtcellsS0.v: fs_shadow_syms_of (FSH_Base.FsShadowSyms from
   ACeg.TfibLib) and fs_rt_vals (the cells of FSstrlen.fs_rt_rest as val_mem facts, from AR's ARm and TfibSyms).
   This file keeps only what needs the Bz view:
   - fs_rt_cells_of: FSstrlen.FsRtCells B (lib/A/FSstrlen.v:587-588) from fs_rt_vals. The C8 bridge is
     FSstrlen.ro_c8_of_val_mem; the C1 bridge (a 1-byte val_mem value) is ro_c1_of_val_mem below. Bz's ImageA.asegs and
     AB1v.tfibsegs are the same segments (FSbz_str.mbyte_mrd holds by reflexivity).
   - The string contracts without the two premises: fs_strlen_realizesU_s, fs_memchr_realizesU_s (ACeg.TfibLib B in
     their place; AR_laws and TfibSyms kept). strcmp is NOT here: a Theorem Labs lane's ruling (2026-10-29T05:50Z) retires fs's Bz
     strcmp walk for the one lifted AStrcmpDefU text (relocated from a Theorem Labs lane's walk); FSstrcmp.v stays on
     a working branch and is cited nowhere. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSbz_str.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSstrlen.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSmemchr.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.ACeg.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSrtcellsS0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YP09 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0m FSupoison FSH_Gen FSH_Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Module BI := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.ImageA.
Module BC := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Cells.
Module BSt := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Step.
Module BR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.R_m2s.
Module FSS := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSbz_str.
Module FSL := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSstrlen.
Module FSM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSmemchr.
Module ACg := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.ACeg.
Module S0c := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSrtcellsS0.

(* ---- the C1 bridge: a 1-byte val_mem value is a C1 cell of the Bz tree ---- *)
Lemma ro_c1_of_val_mem : forall m a b, 0 <= a -> a + 1 <= 2 ^ 64 -> 0 <= b < 256 ->
  val_mem tfibsegs m a 1 b -> BSt.ro_cells BI.asegs m a [BC.C1 (Z_to_bv 8 b)].
Proof.
  intros m a b H0 H1 Hb HV. split; [cbn; tauto|].
  cbn [BC.cells_bytes BC.cbytes app].
  split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct i as [|i]; [|cbn in Hi; exfalso; lia].
  rewrite <- FSS.mbyte_mrd. rewrite (HV 0%nat ltac:(lia)). cbn [nth_error].
  exact (f_equal (fun z => Some (Z_to_bv 8 z)) (S0c.le_byte_1_0 b Hb)).
Qed.

Local Ltac c8 V := apply FSL.ro_c8_of_val_mem; [lia | lia | lia | exact V].
Local Ltac c1 V := apply ro_c1_of_val_mem; [lia | lia | lia | exact V].

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- FsRtCells from the start-up facts (FSrtcellsS0.fs_rt_vals) ---- *)
Lemma fs_rt_cells_of : forall B, AR_laws tfibsegs B -> TfibSyms B -> FSL.FsRtCells B.
Proof.
  intros B LAWS TB ly S W mem md HAR.
  destruct (S0c.fs_rt_vals B LAWS TB ly S W mem md HAR)
    as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
  unfold FSL.fs_rt_rest, BR.kHighMemEnd.
  split; [c8 V1|].
  split; [apply FSL.ro_cons8; [c8 V2 | apply FSL.ro_cons8; [c8 V3 | c8 V4]]|].
  split; [c8 V5|].
  split; [c8 V6|].
  split; [c1 V7|].
  split; [apply FSL.ro_cons8; [c8 V8 | apply FSL.ro_cons8; [c8 V9 | c8 V10]]|].
  split; [c1 V11|].
  split; [c1 V12|].
  c1 V13.
Qed.

(* ---- the three string contracts without the two named premises ---- *)
Corollary fs_strlen_realizesU_s : forall B, AR_laws tfibsegs B -> TfibSyms B -> ACg.TfibLib B ->
  astrlen_realizesU tfibsegs B PC_strlen.
Proof.
  intros B LAWS TB TL.
  exact (FSL.fs_strlen_realizesU B LAWS TB (S0c.fs_shadow_syms_of B TL) (fs_rt_cells_of B LAWS TB)).
Qed.

Corollary fs_memchr_realizesU_s : forall B, AR_laws tfibsegs B -> TfibSyms B -> ACg.TfibLib B ->
  amemchr_realizesU tfibsegs B PC_memchr.
Proof.
  intros B LAWS TB TL.
  exact (FSM.fs_memchr_realizesU B LAWS TB (S0c.fs_shadow_syms_of B TL) (fs_rt_cells_of B LAWS TB)).
Qed.

End core.

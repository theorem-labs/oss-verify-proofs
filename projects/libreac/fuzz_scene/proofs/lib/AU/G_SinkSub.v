(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/G_SinkSub.v. The glue's sink row AIL (AU/G_Top.v Hypothesis
   AIL; AU/G_Close.v passes scene_AIL for it) at the concrete B := YD2l.TfibB, from the donor's YD1u.tfib_AIL over YE2k.tfib_K. Rule 24:
   no function is walked; this file is a monotonicity lemma for the sink's image laws (AU/YE01.v asink_img_laws) and
   its instance. YE2k.tfib_K and AU/G_Sink.scene_K agree in every field the laws read and in the owned list;
   tfib_K's icells has a fourth row (0x103a0, 0xafffff00000fffff) that scene_K's three GOT cells lack. The
   asan-ubsan image holds that value at 0x103a0 (.rodata, an ASan runtime literal-pool word that
   AddrHashMap<CommonInterceptorMetadata>::acquire / release load), so it is a true cell of the image; scene_K does
   not name it, and the laws of the smaller record follow from the larger one's. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
(* Required first, as in AU/G_Top.v, so that the short names below (YK11, YM05, YI16) resolve to lib/Reusable and
   not to their lib/U/Reusable twins: the row's YM05.RunCeil and YK11.FPState are then AU/G_Top.v's. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require SceneAsanBase.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require SceneAsanTop.
(* Gate 6h: no sink-head or sink_syms instance is in scope. YE2k and YD1u are Required, not imported, so YE2k's
   tfib_sink_head instance is not in scope either. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require SinkGuard.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK04 YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YI16 YE00 YM05.
(* Gate 6o: the image-specific YE01 (asink_img_laws) from lib/AU, as AU/G_Top.v takes it. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import
  PaTable PaSym SceneSyms SceneList SceneCode ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import G_Sink G_Top.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YE2k YD1u YD2l.
Import ListNotations.
Open Scope Z_scope.
(* asink_img_laws reads ak_icells in one place only: the premise `In c (ak_icells K)` of ail_icells. The laws are
   therefore antitone in the set of icells, and `incl` (each cell of K' is a cell of K) is the weakest relation
   between the two lists from which ail_icells for K' follows for every B: order, repetition and position (prefix,
   sublist) play no part, and a cell of K' that is not a cell of K gets no as_const fact from the laws of K.
   The laws read seven scalar fields (ak_threaded, ak_need_locks, ak_ofl_lock (through ak_ofl_head), ak_meta_ptr,
   ak_meta_mem, ak_can_got, ak_canary), each equal here, and ak_owned, which they read both as a premise (ail_env,
   ail_env_off and ail_env_static, through aenv_addr) and as a conclusion (ail_owned_core), so it is equal too. They
   do not read ak_read, ak_write, ak_seek, ak_close, ak_path, ak_mode, ak_rwa or ak_trailer, so those carry no
   hypothesis. *)
Lemma asink_img_laws_icells_incl {SK : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head}
  (segs : list Segment) (B : asyms) (K K' : asink_syms) :
  ak_threaded K' = ak_threaded K ->
  ak_need_locks K' = ak_need_locks K ->
  ak_ofl_lock K' = ak_ofl_lock K ->
  ak_meta_ptr K' = ak_meta_ptr K ->
  ak_meta_mem K' = ak_meta_mem K ->
  ak_can_got K' = ak_can_got K ->
  ak_canary K' = ak_canary K ->
  ak_owned K' = ak_owned K ->
  incl (ak_icells K') (ak_icells K) ->
  asink_img_laws (SK:=SK) segs B K -> asink_img_laws (SK:=SK) segs B K'.
Proof.
  intros Eth Enl Eol Emp Emm Ecg Ecn Eow Hinc [Hhead Henv Hoff Hstat Hcore Hcg Hmeta Hmp Herr Hic].
  assert (EH : ak_ofl_head K' = ak_ofl_head K) by (unfold ak_ofl_head; rewrite Eol; reflexivity).
  constructor.
  - rewrite EH. exact Hhead.
  - intros a Ha. apply Henv. unfold aenv_addr in Ha |- *. rewrite Eow, EH in Ha. exact Ha.
  - intros a Ha. apply Hoff. unfold aenv_addr in Ha |- *. rewrite Eow, EH in Ha. exact Ha.
  - intros a Ha. apply Hstat. rewrite Eow in Ha. exact Ha.
  - intros a Ha. rewrite Eow. apply Hcore. unfold aenv_core in Ha |- *. rewrite Eth, Enl, Eol, Ecn in Ha. exact Ha.
  - intros ly. rewrite Ecg, Ecn. apply Hcg.
  - intros a Ha. rewrite Emm in Ha. exact (Hmeta a Ha).
  - intros ly. rewrite Emp, Emm. apply Hmp.
  - exact Herr.
  - intros ly c Hc. exact (Hic ly c (Hinc c Hc)).
Qed.
(* The glue's row, as AU/G_Top.v / AU/G_Close.v state it (SEGS, B and the sink head as there). *)
#[local] Abbreviation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Abbreviation B := YD2l.TfibB.
(* scene_K's three icells are tfib_K's first three. *)
Lemma scene_icells_incl : incl (ak_icells scene_K) (ak_icells YE2k.tfib_K).
Proof.
  cbv [scene_K ak_icells scene_icells YE2k.tfib_K YE2k.tfib_icells].
  intros c Hc. destruct Hc as [<- | [<- | [<- | []]]];
    [left | right; left | right; right; left]; reflexivity.
Qed.
(* YD1u.tfib_AIL at B := TfibB with HB := YD2l.TfibB_syms is the law at tfib_sink_head, tfibsegs and tfib_K;
   asan_ubsan_sink_head and tfib_sink_head are both ofl_head 0x5f7190, and SEGS is YB1v.tfibsegs (both are
   AsanUbsan.M.loaded_segments), so it has the row's type at tfib_K. *)
Lemma scene_AIL : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  asink_img_laws (SK:=asan_ubsan_sink_head) SEGS B scene_K.
Proof.
  intros rc fx.
  apply (@asink_img_laws_icells_incl asan_ubsan_sink_head SEGS B YE2k.tfib_K scene_K
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl scene_icells_incl).
  exact (YD1u.tfib_AIL B YD2l.TfibB_syms).
Qed.

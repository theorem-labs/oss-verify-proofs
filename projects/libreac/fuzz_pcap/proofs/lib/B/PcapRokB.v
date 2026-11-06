From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap; no function walk (a segment lemma). It proves
   the hypothesis ROK of lib/B/Prog/PcapSourceOpen.v's Section e (PcapSourceOpen.v:465-468), which
   pb_pcap_source_openX takes, at the asan-ubsan instance: SEGS := pa_segs of lib/B/Prog/PcapEntryTop.v PI_pcap
   (= AsanUbsan.M.loaded_segments = lib/Reusable/YB1v.v tfibsegs), B := lib/Reusable/YD2l.v PcapB,
   roimg := lib/Reusable/YE3i.v ro_img, and AOFL_HEAD at SK := lib/Reusable/PcapSinkHeads.v asan_ubsan_sink_head
   (0x5f4e88).
   - pcap_rok_B (ROK): ro_img is kept when m' and m read the same through aview at every image byte outside
     PcapB's owned statics, errno and [AOFL_HEAD, +8). ro_img is region_ok over YE3i.img_ro_region, whose chunks
     YE3i.img_ro_chunks lie inside [IMG_RO_LO, IMG_RO_HI) = [0x10000, 0x2efc0) (YE3i.img_ro_chunks_inside). Each chunk
     byte a is an image byte (tfibsegs' segment 0 is [0x10000, 0x2f000), YE3i.img_ro_seg0), is in no row of
     YF0m.Tfib_owned_static (= as_owned_static PcapB; rokB_chunks_avoid_owned below, by computation, the same fact
     YE3i.img_ro_complement_ok states as a complement), and lies below errno (0x5d46ec) and below AOFL_HEAD. So ROK's
     premise gives aview equality at a, lib/Reusable/YCbq.v mbyte_of_aview gives mbyte equality, and the chunk step is
     lib/A/PcapRoBridges.v pcap_roimg_kept's (itself cgif c8557374ad2e lib/A/AE3i.v:72-81 ro_img_kept).
   This file does not Require lib/B/Prog/PcapSourceOpen.v (that file is built by another lane); the Check at the end
   has the kernel compare pcap_rok_B's type with ROK's text, copied token for token from PcapSourceOpen.v:465-468,
   at the instance. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YK04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YA0n YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YE3i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YI16 YCbq YF0m YD2l PcapSinkHeads.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapPa PcapList.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapEntryTop.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Module RokPET := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntryTop.
Module RokCbq := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCbq.
Module RokF0m := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YF0m.
Module RokD2l := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD2l.
Module RokI16 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.
Module RokPSH := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PcapSinkHeads.

(* No chunk of img_ro_chunks meets a row of Tfib_owned_static (as_owned_static PcapB), by computation. *)
Lemma rokB_chunks_avoid_owned :
  forallb (fun c => forallb (fun r => (YP09.c_off c + YP09.c_len c <=? fst r) || (fst r + snd r <=? YP09.c_off c))%bool
    RokF0m.Tfib_owned_static) img_ro_chunks = true.
Proof. vm_compute. reflexivity. Qed.

(* The facts of a chunk byte that ROK's premise asks for. *)
Lemma rokB_chunk_byte : forall c, In c img_ro_chunks -> forall i, 0 <= i < YP09.c_len c ->
  in_img tfibsegs (YP09.c_off c + i) /\ ~ Exists (in_zr (YP09.c_off c + i)) RokF0m.Tfib_owned_static /\
  IMG_RO_LO <= YP09.c_off c + i < IMG_RO_HI.
Proof.
  intros c Hc i Hi.
  pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & _).
  split; [|split; [|lia]].
  - pose proof img_ro_seg0 as H0. rewrite nth_error_map in H0.
    destruct (nth_error tfibsegs 0) as [sg|] eqn:E0; [|discriminate H0].
    cbn [option_map] in H0. injection H0 as E1 E2 _.
    assert (Etop : (IMG_RO_HI + 0xfff) / 0x1000 * 0x1000 = (symaddr ImgPages.AsanUbsan.text_lo)) by reflexivity.
    exists sg. split; [exact (nth_error_In _ _ E0)|].
    rewrite E1. rewrite Etop in E2. unfold IMG_RO_LO, IMG_RO_HI in *. lia.
  - intros Hex. apply Exists_exists in Hex as (r & Hr & Hin). unfold in_zr in Hin.
    pose proof (proj1 (forallb_forall _ _) rokB_chunks_avoid_owned c Hc) as Hc'. cbv beta in Hc'.
    pose proof (proj1 (forallb_forall _ _) Hc' r Hr) as Hb. cbv beta in Hb.
    apply orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

Section rok. Context {rc : YM05.RunCeil}.
(* The instance, under the names PcapSourceOpen.v's Section e gives it (SEGS, B, roimg) and AOFL_HEAD at SK. *)
#[local] Abbreviation SEGS := (@pa_segs rc pcap_listing (@RokPET.PI_pcap rc)).
#[local] Abbreviation B := RokD2l.PcapB.
#[local] Abbreviation roimg := YE3i.ro_img.
#[local] Abbreviation AOFL_HEAD := (@RokCbq.AOFL_HEAD RokPSH.asan_ubsan_sink_head).

(* ROK (PcapSourceOpen.v:465-468), its text at the instance. *)
Lemma pcap_rok_B : forall (W : world SEGS) (m m' : word -> option byte),
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (AOFL_HEAD <= a < AOFL_HEAD + 8) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  roimg (mrestrict (w_H W) m) -> roimg (mrestrict (w_H W) m').
Proof.
  intros W m m' Hag Hro E.
  change (@pa_segs rc pcap_listing (@RokPET.PI_pcap rc)) with tfibsegs in Hag.
  change (as_owned_static B) with RokF0m.Tfib_owned_static in Hag.
  change (as_errno B) with (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x24)%Z) in Hag.
  change AOFL_HEAD with (symaddr Symbols.AsanUbsan.s_ofl_head) in Hag.
  assert (CH : forall c, In c img_ro_chunks -> forall i, 0 <= i < YP09.c_len c ->
    mbyte tfibsegs (mrestrict (w_H W) m') (YP09.c_off c + i) = mbyte tfibsegs (mrestrict (w_H W) m) (YP09.c_off c + i)).
  { intros c Hc i Hi. destruct (rokB_chunk_byte c Hc i Hi) as (Himg & Hno & Hr).
    apply (RokCbq.mbyte_of_aview tfibsegs). apply Hag; [exact Himg | exact Hno | |];
      unfold IMG_RO_LO, IMG_RO_HI in Hr; lia. }
  pose proof (Hro E) as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|].
  split; [intros o Ho; exfalso; clear - Ho; cbn in Ho; lia|].
  apply Forall_forall. intros c Hc i Hi. pose proof (proj1 (Forall_forall _ _) H4 c Hc i Hi) as (b & Hcb & Hmb).
  exists b. split; [exact Hcb|].
  revert Hmb. cbn [YP09.r_base base_val]. rewrite !Z.add_0_l.
  rewrite (CH c Hc i Hi). intros Hmb. exact Hmb.
Qed.
End rok.

(* The type of the hypothesis ROK of lib/B/Prog/PcapSourceOpen.v:465-468, as that file's Section e elaborates it:
   the same Section shape (SK as an implicit Context, so AOFL_HEAD's implicit sink_head is the Section's SK; SEGS,
   B and roimg as Variables), and the text copied token for token. *)
Section rok_stmt.
Context {SK : RokI16.sink_head}.
Variable SEGS : list Segment.
Variable B : asyms.
Variable roimg : (word -> option byte) -> Prop.
#[local] Abbreviation AOFL_HEAD := RokCbq.AOFL_HEAD.
Definition rokB_ROK : Prop :=
forall (W : world SEGS) (m m' : word -> option byte),
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (AOFL_HEAD <= a < AOFL_HEAD + 8) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  roimg (mrestrict (w_H W) m) -> roimg (mrestrict (w_H W) m').
End rok_stmt.
(* At the instance (SK := asan_ubsan_sink_head, SEGS := pa_segs PI_pcap, B := PcapB, roimg := YE3i.ro_img) the kernel
   checks that pcap_rok_B has ROK's type, for every rc. *)
Check (fun rc : YM05.RunCeil => (@pcap_rok_B rc :
  @rokB_ROK RokPSH.asan_ubsan_sink_head (@pa_segs rc pcap_listing (@RokPET.PI_pcap rc)) RokD2l.PcapB YE3i.ro_img)).
Print rokB_ROK.
Print Assumptions pcap_rok_B.

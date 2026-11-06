(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 222 of its 252 lines of code are new or changed and 1050 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_put_grow.v; 84 of its 116 lines of code are new or changed and 220 lines of the source are left out. *)
(* fs WRITER walk, image A (fs.asan): put's CLOSING THEOREM, lib/A/FSH_Fn_writer.v `put_spec B tfibsegs`, from its
   three arms: the FAILED arm and the FAST arm (lib/A/FSW_put.v put_failed_run / put_fast_run) and the GROW arm
   (lib/A/FSW_put_grow_run.v and lib/A/FSW_put_grow_tail.v). The proved arms state their journal count as
   `3 * wcalls st'`, the count put_spec had when they were proved; put_spec now reports `wevk cap st'`
   (FSH_Fn_writer.v wevk), and on both of those arms put1 makes no request, so the two are the same number, 0
   (put_pf_wevk0 below). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSW_K FSW_ret
FSW_writer_tbl FSW_put.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.omx_clap_core.fuzz_state.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* on an arm where put1 records no request, put_spec's count wevk is the proved arms' 3 * wcalls, both 0 *)
Lemma put_pf_wevk0 : forall cap (st : WriterApp.wst), WriterApp.w_calls st = [] -> wevk cap st = 3 * wcalls st.
Proof.
intros cap st H. unfold wevk, wev0, wcalls. rewrite H. cbn [length Z.of_nat]. destruct (cap =? 0); reflexivity.
Qed.
Lemma put_pf_calls_failed : forall failed text cap cnt fail (bs : list Z), failed <> 0 ->
  WriterApp.w_calls (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs) = [].
Proof.
intros failed text cap cnt fail bs Hf. unfold WriterApp.put1. cbn [WriterApp.w_failed].
destruct (Z.eqb_spec failed 0) as [E|_]; [contradiction | reflexivity].
Qed.
Lemma put_pf_calls_fast : forall text cap cnt fail (bs : list Z),
  Z.of_nat (length text) + Z.of_nat (length bs) + 1 <= cap ->
  WriterApp.w_calls (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs) = [].
Proof.
intros text cap cnt fail bs Hle. unfold WriterApp.put1.
cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls negb Z.eqb].
rewrite (proj2 (Z.leb_le _ _) Hle). reflexivity.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis RT_memcpy : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* put_spec's post, as a predicate of the call's data (FSH_Fn_writer.v put_spec, verbatim) *)
Definition put_post ly S U W regs mem md ot o s n buf cap failed (text bs : list Z) live peak cnt fail :
  world tfibsegs -> config -> Prop :=
  fun W' c' => exists (st' : WriterApp.wst) buf' U',
    st' = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs /\
    uswap U U' buf buf' cap /\
    wpost B tfibsegs STK_put ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
      regs ly S U W mem md (wevk cap st') U'
      (fun ly' S' W' regs' mem' md' =>
         wout_ok B tfibsegs ly' S' W' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st') (WriterApp.w_text st') /\
         wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
         bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
         wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
         (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
            fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st' - cap) peak'
              (WriterApp.w_cnt st') (WriterApp.w_fail st')) /\
         (forall i, 0 <= i < n -> mbyte tfibsegs (mrestrict (w_H W') mem') (s + i)
                                = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)))
      W' c'.

(* the FAILED arm in put_spec's count *)
Lemma put_close_failed :
  forall ly S U W regs mem md ch ot o s n buf cap failed (text bs : list Z) live peak cnt fail,
  fpreU tfibsegs B STK_put ly S U W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  0 <= s /\ s + n <= alloc_ceiling ->
  cap <= WMAX ->
  failed <> 0 ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regs mem md)
    (put_post ly S U W regs mem md ot o s n buf cap failed text bs live peak cnt fail).
Proof.
intros ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
  HPRE G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HSRC HCAP HFAIL.
eapply SRr_mono.
{ exact (put_failed_run B HSS ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
           HPRE G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HSRC HCAP HFAIL). }
intros W' c' _ (st' & buf' & U' & Hst & Hu & HP).
exists st', buf', U'. split; [exact Hst|]. split; [exact Hu|].
rewrite (put_pf_wevk0 cap st') by (rewrite Hst; apply put_pf_calls_failed; exact HFAIL). exact HP.
Qed.

(* the FAST arm in put_spec's count *)
Lemma put_close_fast :
  forall ly S U W regs mem md ch ot o s n buf cap failed (text bs : list Z) live peak cnt fail,
  fpreU tfibsegs B STK_put ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> fs_glob tfibsegs W mem live peak cnt fail ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  zbytes_at tfibsegs W mem s bs -> wsrc_kept B tfibsegs ly S U W mem buf s bs -> Z.of_nat (length bs) = n ->
  WriterSpec.bytes_ok bs ->
  0 <= s /\ s + n <= alloc_ceiling -> (s + n <= o \/ ot <= s) ->
  Z.of_nat (length text) + n + 1 <= WMAX ->
  cap <= WMAX ->
  wbudget_pre S cap cnt live (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs) ->
  failed = 0 -> Z.of_nat (length text) + n + 1 <= cap ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regs mem md)
    (put_post ly S U W regs mem md ot o s n buf cap failed text bs live peak cnt fail).
Proof.
intros ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
  HPRE FH G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HZS HSK Hlen Hbok HSRC Hsdisj HWM HCAP HBUD HF0
  HFAST.
eapply SRr_mono.
{ exact (put_fast_run B HSS RT_memcpy IMG ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
           HPRE FH G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HZS HSK Hlen Hbok HSRC Hsdisj HWM HCAP HBUD
           HF0 HFAST). }
intros W' c' _ (st' & buf' & U' & Hst & Hu & HP).
exists st', buf', U'. split; [exact Hst|]. split; [exact Hu|].
rewrite (put_pf_wevk0 cap st') by (rewrite Hst, HF0; apply put_pf_calls_fast; rewrite Hlen; exact HFAST). exact HP.
Qed.

End w.

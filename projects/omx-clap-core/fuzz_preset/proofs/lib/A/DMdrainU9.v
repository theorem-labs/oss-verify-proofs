(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU9.v (commit 67deba317dfb, blob e75aa78f1a30) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainK.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMsegDA DMdeq.
Import ListNotations.
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.

Definition recyc_cut_in (inst : Z) (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (F1 : Z -> Prop) (regs1 : bvmap 5 word) (mem1 : word -> option byte)
(gk : qcache) (P : list batch) (W' : world tfibsegs) (c' : config) : Prop :=
let sp0 := bv_unsigned (getr regs 2) in
let S' := set_qglobal gk (set_qthread qc0 X) in
let m1 := mrestrict (w_H W) mem1 in

drain_pre_cf B ARX L24 QB inst ly X W regs mem md /\
drain_recyc X S' P /\

(forall x : word, ~ F1 (bv_unsigned x) -> mem1 x = mem x) /\
(forall a, F1 a -> dwin_q inst ly sp0 X S' P a) /\

(forall a, 0 <= a < 2 ^ 64 -> ~ qhdr inst ly a -> apresent (w_H W) mem a -> apresent (w_H W) mem1 a) /\

(forall b, In b (P ++ qc_list gk) ->
   ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\
   addrb ly b mod 8192 = 0 /\ 0 <= addrb ly b < ASAN_CEIL) /\
(forall b, In b (P ++ qc_list gk) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat) /\
List.NoDup (map b_self (P ++ qc_list gk)) /\

(forall b, In b (P ++ qc_list gk) -> exists b0, In b0 (all_batches X) /\ b_self b0 = b_self b) /\

(forall b, In b (P ++ qc_list gk) ->
   val_mem tfibsegs m1 (addrb ly b + 8) 8 (b_bytes b) /\
   val_mem tfibsegs m1 (addrb ly b + 16) 8 (zl (b_items b)) /\
   (forall j k, nth_error (b_items b) j = Some k ->
      val_mem tfibsegs m1 (addrb ly b + 24 + 8 * Z.of_nat j) 8 (DMdrainK.iwB B ly k))) /\

val_mem tfibsegs m1 (sp0 - 8) 8 (bv_unsigned (getr regs 1)) /\
val_mem tfibsegs m1 (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem tfibsegs m1 (sp0 - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs m1 (sp0 - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem tfibsegs m1 (sp0 - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs m1 (sp0 - 48) 8 (bv_unsigned (getr regs 20)) /\

val_mem tfibsegs m1 (ly_T ly + t_qc) 8 0 /\ val_mem tfibsegs m1 (ly_T ly + t_qc + 8) 8 0 /\
val_mem tfibsegs m1 (ly_T ly + t_qc + 16) 8 0 /\ val_mem tfibsegs m1 (ly_T ly + t_qc + 24) 8 0 /\

bv_unsigned (getr regs1 2) = sp0 - 80 /\
(forall r : bv 5, In r DMsegDA.SREGS_M -> getr regs1 r = getr regs r) /\

getr regs1 12 = w64 (ly_T ly + t_cache) /\

qc_bytes gk = sum_bytes (qc_list gk) /\

DMdeq.ATDR W ly md regs1 mem1 P (qc_list gk) W' c'.
End g.
End f.

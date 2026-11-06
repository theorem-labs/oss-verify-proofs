(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK0j YQ0b YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03 YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Definition A_Enqueue {imgk : img} : Z := (0x35dd8 + D_150).
Definition QSTACK : Z := 1088.
Section c. Context {imgk : img}.
Variable B : asyms.
Definition enq_pre {imgk : img} (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk) : Prop :=
AR tfxsegs B ly X W mem md /\ A_bytes (w_A W) + EV_A <= abudget X /\
Z.of_nat (length (all_batches X)) + 1 <= st_nev X /\ refill_reg X kBatchClass   /\
In k (st_chunks X) /\ ck_state k = CQuarantined /\ ~ In (ck_beg k) (map ck_beg (q_items X)) /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + QSTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - QSTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (ly_T ly + t_qc) /\ getr regs 11 = w64 (ly_T ly + t_cache) /\
getr regs 13 = w64 (sptr_addr B ly (ck_user k) - kChunkHeaderSize) /\ getr regs 14 = w64 (ck_n k) /\
qloose X.
Definition enq_leaf {imgk : img} (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk)
(r : unit * astate) (W' : world tfxsegs) (c' : config) : Prop :=
exists regs' mem' md' nb,
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
acall_post tfxsegs B QSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
st_qthread (snd r) = qc_push (st_qthread X) k nb /\
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end /\
st_chunks (snd r) = st_chunks X /\ st_qglobal (snd r) = st_qglobal X /\
st_fs (snd r) = st_fs X.
Definition tfx_enqueue_spec {imgk : img} : Prop :=
forall ly X W regs mem md k,
enq_pre ly X W regs mem md k ->
amreal tfxsegs (enqueue k X) W (cfg_at tfxsegs A_Enqueue regs mem md) (enq_leaf ly X W regs mem md k).
Definition tfx_enqueue_spec_nb {imgk : img} (nbq : bool) : Prop :=
forall ly X W regs mem md k,
need_new_batch (st_qthread X) = nbq ->
enq_pre ly X W regs mem md k ->
amreal tfxsegs (enqueue k X) W (cfg_at tfxsegs A_Enqueue regs mem md) (enq_leaf ly X W regs mem md k).

End c.
End b.

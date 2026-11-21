(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFew.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFew.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0s YK0i YP09 YO0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0l YG0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Definition A_Enqueue : Z := 0x35eac.
Definition QSTACK : Z := 1088.
Section c.
Variable B : asyms.
Definition enq_pre (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk) : Prop :=
AR tfibsegs B ly X W mem md /\ A_bytes (w_A W) + EV_A <= abudget X /\
Z.of_nat (length (all_batches X)) + 1 <= st_nev X /\ refill_reg X kBatchClass   /\
In k (st_chunks X) /\ ck_state k = CQuarantined /\ ~ In (ck_beg k) (map ck_beg (q_items X)) /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + QSTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - QSTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (ly_T ly + t_qc) /\ getr regs 11 = w64 (ly_T ly + t_cache) /\
getr regs 13 = w64 (sptr_addr B ly (ck_user k) - kChunkHeaderSize) /\ getr regs 14 = w64 (ck_n k) /\
qloosem X.
Definition enq_leaf (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md' nb,
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
acall_post tfibsegs B QSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
st_qthread (snd r) = qc_push (st_qthread X) k nb /\
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end /\
st_chunks (snd r) = st_chunks X /\ st_qglobal (snd r) = st_qglobal X /\
st_fs (snd r) = st_fs X.
Definition tfib_enqueue_spec_nb (nbq : bool) : Prop :=
forall ly X W regs mem md k,
need_new_batch (st_qthread X) = nbq ->
enq_pre ly X W regs mem md k ->
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (enq_leaf ly X W regs mem md k).
End c.
End b.

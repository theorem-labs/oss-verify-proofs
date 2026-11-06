(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan fake-stack vocabulary of the cgif walks at fuzz_reply's symbol type wsym:
   proofs/cgif/cgif_file_fuzzer/lib/YC44.v (fake-frame and shadow regions, the plain pi runs over the journal and the
   flag store that ends a fake frame), lib/YC1h.v (atoms above A_LIM, after-call with high atoms), lib/YC45.v (the
   plain pi run that stops at a call) and the generic lemmas of lib/A/AC8j.v.  Only the symbol type, the module paths
   and PALibF's two stack_malloc fields (fuzz_reply calls classes 0 and 1) change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_frame.v, with its module paths and module names changed; 46 of its 75 lines of code are new or changed and 1151 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated to libdiginet/fuzz_transport's asan image by this unit's provenance/evidence/class0 run (alreloc with the resolve lines of smcmp.py); CtrlTSyms becomes TransportSyms. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import StackFreeDef StackFreeRaw.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Rt Require Import StackMallocRawDef.
Import ListNotations.
Open Scope Z_scope.
Lemma raw_kept_gen : forall (H : word -> bool) (mem mem' : word -> option byte) (P : Z -> Prop),
(forall z : word, ~ P (bv_unsigned z) -> mem' z = mem z) ->
(forall a, P a -> exists m0, apresent H m0 a) ->
forall x : word, H x = true -> mem' x = mem x.
Proof.
intros H mem mem' P MEQ PRES x Hx. apply MEQ. intros HP.
destruct (PRES _ HP) as (m0 & Hf & _). rewrite Z_to_bv_bv_unsigned, Hx in Hf. discriminate Hf.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Let code := as_code B.
Definition astack_malloc_realizes_hid_plain (cid : Z) : Prop :=
forall ly S W regs mem md pos S',
ecall_pre segs B ly S W regs mem md ->
count_cid cid (frames S) < fs_frames cid ->
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
SRr segs W (cfg_at segs (pc_stack_malloc code cid) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S' W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly cid pos) /\
zero_shadow (aview segs (w_H W) mem') SHADOW_OFF (frame_addr ly cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem') (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall x : word, w_H W x = true -> mem' x = mem x) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
Lemma astack_malloc_realizes_hid_plain_raw : forall cid, astack_malloc_realizes_hid_plain cid -> astack_malloc_realizes_raw segs B cid.
Proof.
intros cid R ly S W regs mem md pos S' H1 H2 H3.
eapply SRr_mono; [exact (R ly S W regs mem md pos S' H1 H2 H3)|].
intros W' c' _ (EW & regs' & mem' & md' & EC & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & PL & P9).
split; [exact EW|]. exists regs', mem', md'.
exact (conj EC (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj (fun x Hx _ => PL x Hx) P9)))))))))).
Qed.
Definition astack_free_realizes_hid_plain (pc cid : Z) : Prop :=
forall ly S W regs mem md pos n,
ecall_pre segs B ly S W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 (frame_addr ly cid pos) -> getr regs 11 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
rdword (aview segs (w_H W) mem) (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly (stack_free_state cid pos S) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < sf_span cid n -> aview segs (w_H W) mem' (shadow_addr (frame_addr ly cid pos) + i) = Some 0xf5) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + sf_span cid n) ->
a <> flag_addr ly cid pos -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall x : word, w_H W x = true -> mem' x = mem x) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
Lemma astack_free_realizes_hid_plain_raw : forall pc cid, astack_free_realizes_hid_plain pc cid -> astack_free_realizes_raw segs B pc cid.
Proof.
intros pc cid R ly S W regs mem md pos n H1 H2 H3 H4 H5 H6 H7.
eapply SRr_mono; [exact (R ly S W regs mem md pos n H1 H2 H3 H4 H5 H6 H7)|].
intros W' c' _ (EW & regs' & mem' & md' & EC & P1 & P2 & P3 & P4 & P5 & PL & P6).
split; [exact EW|]. exists regs', mem', md'.
exact (conj EC (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj (fun x Hx _ => PL x Hx) P6))))))).
Qed.
End c.
End b.

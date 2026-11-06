(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: P'' (the Univ trace carrier) delta of commit 94ab015e127b for cgif/cgif_file_fuzzer/lib/YG0d.v, taken 3-way (its base d94d29d53c8). *)
(* Modified by Theorem Labs, 2026-10-29: from lib/Reusable/YG0d.v, as the new module IcptRealizesX: only amemcmp_realizes and abcmp_realizes, with lib/Rt/MemchrDef.v's amemchr_realizes / amemchr_realizesM and lib/Rt/StrnlenDef.v's astrnlen_whole_realizes / astrnlen_whole_realizesM (their restatements of YG0d.v's amemchr0_realizes / astrnlen_realizes), each restated as <name>_x over a generic allocator invariant ARx at tfibsegs (ecall_pre -> ecall_pre_ix B ARx with the ghost head set Hp, AR -> ARx), with the lemmas <name>_of_x at ARx := AR_x B. *)
(* The runtime contract texts that image A's interceptor walks AE2z / AE2s / Rt/Memchr /
   Rt/Strnlen / Rt/StrnlenMusl / Rt/Bcmp state over a generic allocator invariant ARx (third argument: the ghost head
   set Hp, threaded unchanged), in the vocabulary of AE2y.v's Section ix (ecall_pre_ix, icpt_laws_x, AR_x).
   Each _x text is its original with `ecall_pre segs B ly S W` -> `ecall_pre_ix B ARx ly S Hp W` and
   `AR segs B ly S W mem' md'` -> `ARx ly S Hp W mem' md'`, at segs := tfibsegs:
   amemcmp_realizes_x / abcmp_realizes_x are YG0d.v's amemcmp_realizes / abcmp_realizes; amemchr_realizes_x /
   amemchr_realizesM_x are Rt/MemchrDef.v:23 / :39; astrnlen_whole_realizes_x / astrnlen_whole_realizesM_x are
   Rt/StrnlenDef.v:22 / :38.  Rt/RTx.v (a Theorem Labs lane) states the last four over FCiface.ecall_pre_x for any segs; they
   are restated here, not imported, for AE2y.v:81-88's reason: the walk files must not Require FCiface or YCbqG
   (global Zify / lia redefinitions).  lib/A/RTxIcpt.v shows each text here equal to its RTx.v / W_sites_x.v twin.
   <name>_of_x: at ARx := AR_x B (Hp := []) each _x text gives the original. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AE2y.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section t.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
(* YG0d.v amemcmp_realizes *)
Definition amemcmp_realizes_x (pc : Z) : Prop :=
forall ly S Hp W regs mem md x y n,
ecall_pre_ix B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok tfibsegs W regs mem x n -> src_ok tfibsegs W regs mem y n -> amem_range x n -> amem_range y n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) y n) ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (x + i) = aview tfibsegs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* YG0d.v abcmp_realizes *)
Definition abcmp_realizes_x (pc : Z) : Prop :=
forall ly S Hp W regs mem md x y n,
ecall_pre_ix B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok tfibsegs W regs mem x n -> src_ok tfibsegs W regs mem y n ->
(forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) y n) ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (x + i) = aview tfibsegs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* Rt/MemchrDef.v:23 amemchr_realizes *)
Definition amemchr_realizes_x (pc : Z) : Prop :=
forall ly S Hp W regs mem md x c n,
ecall_pre_ix B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> getr regs 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok tfibsegs W regs mem x n -> amem_range x n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
rom_view tfibsegs W mem ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte tfibsegs W mem x n c k /\ getr regs' 10 = (if k <? n then w64 (x + k) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* Rt/MemchrDef.v:39 amemchr_realizesM *)
Definition amemchr_realizesM_x (lo hi pc : Z) : Prop :=
forall ly S Hp W regs mem md x c n,
ecall_pre_ix B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> getr regs 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok tfibsegs W regs mem x n -> amem_range x n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
consts_view tfibsegs lo hi W mem ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte tfibsegs W mem x n c k /\ getr regs' 10 = (if k <? n then w64 (x + k) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* Rt/StrnlenDef.v:22 astrnlen_whole_realizes *)
Definition astrnlen_whole_realizes_x (pc : Z) : Prop :=
forall ly S Hp W regs mem md x n,
ecall_pre_ix B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok tfibsegs W regs mem x n -> (forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
rom_view tfibsegs W mem ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte tfibsegs W mem x n 0 k /\ getr regs' 10 = w64 k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* Rt/StrnlenDef.v:38 astrnlen_whole_realizesM *)
Definition astrnlen_whole_realizesM_x (lo hi pc : Z) : Prop :=
forall ly S Hp W regs mem md x n,
ecall_pre_ix B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok tfibsegs W regs mem x n -> (forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
consts_view tfibsegs lo hi W mem ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte tfibsegs W mem x n 0 k /\ getr regs' 10 = w64 k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End t.
Section br.
Variable B : asyms.
Lemma amemcmp_realizes_of_x : forall pc, amemcmp_realizes_x B (AR_x B) pc -> amemcmp_realizes tfibsegs B pc.
Proof. intros pc H ly S. exact (H ly S []). Qed.
Lemma abcmp_realizes_of_x : forall pc, abcmp_realizes_x B (AR_x B) pc -> abcmp_realizes tfibsegs B pc.
Proof. intros pc H ly S. exact (H ly S []). Qed.
Lemma amemchr_realizes_of_x : forall pc, amemchr_realizes_x B (AR_x B) pc -> amemchr_realizes tfibsegs B pc.
Proof. intros pc H ly S. exact (H ly S []). Qed.
Lemma amemchr_realizesM_of_x : forall lo hi pc, amemchr_realizesM_x B (AR_x B) lo hi pc -> amemchr_realizesM tfibsegs B lo hi pc.
Proof. intros lo hi pc H ly S. exact (H ly S []). Qed.
Lemma astrnlen_whole_realizes_of_x : forall pc, astrnlen_whole_realizes_x B (AR_x B) pc -> astrnlen_whole_realizes tfibsegs B pc.
Proof. intros pc H ly S. exact (H ly S []). Qed.
Lemma astrnlen_whole_realizesM_of_x : forall lo hi pc,
astrnlen_whole_realizesM_x B (AR_x B) lo hi pc -> astrnlen_whole_realizesM tfibsegs B lo hi pc.
Proof. intros lo hi pc H ly S. exact (H ly S []). Qed.
Lemma amemchr_realizesM_x_of_AR : forall lo hi pc, amemchr_realizesM tfibsegs B lo hi pc -> amemchr_realizesM_x B (AR_x B) lo hi pc.
Proof. intros lo hi pc H ly S Hp. exact (H ly S). Qed.
End br.
End a.

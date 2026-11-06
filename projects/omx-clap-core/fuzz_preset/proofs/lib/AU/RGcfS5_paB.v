(* Modified by Theorem Labs, 2026-10-29: copied from proofs/omx-clap-core/fuzz_preset/lib/A/FSRealloc_S1_pa.v (337e6a94485, blob 1d4809eaec7e) for realloc(NULL, n) (segment S5): PAREGS / PAFRAMES / PACHK / PAST_top / pa_leaf / pachk_ok restated for the end state of A/RGcfS5_r.v's SS_EN (Allocate's entry 0x325b8 reached from asan_realloc's NULL-input `jal Allocate` 0x32fb4: ra = 0x32fb8, sp = entry sp - 2160, no Reallocate frame); frame_chunk, regs_chk, frames_chk and their lemmas are FSRealloc_S1_pa's. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfS5_pa.v (hub 96e1d2182ec6, blob 43703f264b82), stated at fuzz_preset's asan image (ELF sha256 bff8519bbe3e), to its asan-ubsan image (ELF sha256 c90d4fa54d43): module paths to the image-B twins, every image numeral by symbol + offset, image bounds by the image-B start-up facts; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import FSRealloc_S1_paB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition PAREGSN : list (bv 5 * sv) :=
[(1%bv, SLit 0x330a4); (2%bv, SOff 2 (-2160)); (3%bv, SOff 3 0); (4%bv, SLit TFIB_TP); (8%bv, SOff 2 0); (9%bv, SOff 11 0); (10%bv, SLit TFIB_INST); (11%bv, SOff 11 0);
(12%bv, SLit 8); (13%bv, SOff 2 (-2136)); (14%bv, SLit 1); (15%bv, SLit 1); (16%bv, SOff 2 (-2136)); (18%bv, SLit 0); (19%bv, SLit 0x53d60); (20%bv, SLit 1);
(21%bv, SOff 2 (-2136)); (22%bv, SOff 2 (-89)); (23%bv, SOff 23 0); (24%bv, SOff 24 0); (25%bv, SOff 25 0); (26%bv, SOff 26 0); (27%bv, SOff 27 0)].
Definition PAFRAMESN : list (Z * sv) :=
[(-2136, SOff 2 (-2120)); (-2152, SLit 0x53dd0);
(-64, SOff 22 0); (-56, SOff 21 0); (-48, SOff 20 0); (-40, SOff 19 0); (-32, SOff 18 0); (-24, SOff 9 0); (-16, SOff 8 0); (-8, SOff 1 0)].
Definition PACHKN (ss : sstate) : bool :=
regs_chk 32 ss PAREGSN && frames_chk 32 ss PAFRAMESN &&
match frame_chunk (ss_mem ss) (fst MIDLEN) with Some e => sv_eqb e (snd MIDLEN) | None => false end.
Definition PAST_topN (regs0 : bvmap 5 word) (len : Z) (H : word -> bool) (regs' : bvmap 5 word) (m : word -> option byte) : Prop :=
val_mem tfibsegs (mrestrict H m) (bv_unsigned (getr regs0 2) + fst MIDLEN) 8 len /\
Forall (fun p : bv 5 * sv => getr regs' (fst p) = sv_denot (Ereg regs0 []) (snd p)) PAREGSN /\
Forall (fun p : Z * sv => val_mem tfibsegs (mrestrict H m) (bv_unsigned (getr regs0 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg regs0 []) (snd p)))) PAFRAMESN.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition pa_leafN (B : asyms) (R : astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (tr : list Z)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
snd r = set_internal_inited true (set_nev (st_nev S + 1) S) /\ W' = W /\
exists regs' mem' md',
c' = cfg_at tfibsegs 0x326a4 regs' mem' md' /\
(R (snd r) W' mem' md' /\ wle W W' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly (snd r) a -> ~ ascratch B ASTACK regs a ->
aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ ascratch B ASTACK regs (bv_unsigned x) -> mem' x = mem x) /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W') mem' a)) /\
PAST_topN regs (Z.of_nat (length tr)) (w_H W') regs' mem' /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W') mem') (spZ regs - 2120 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
(forall a, spZ regs <= a < ly_top ly -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
qtight (snd r) /\
(forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) /\
(YAkMemnorm.memnorm tfibsegs mem -> YAkMemnorm.memnorm tfibsegs mem').
End b.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pachkN_ok : forall (k : nat) (extra : list word) (regs0 : bvmap 5 word) (E0 E' : env) (H : word -> bool) ss ms,
(37 <= k)%nat -> st_ok tfibsegs E' ss (restrict H ms) -> E0 = Ereg regs0 extra -> (forall n, (n < k)%nat -> ew E' n = ew E0 n) -> ed E' = ed E0 -> PACHKN ss = true ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (getr regs0 2) + fst MIDLEN) 8 (bv_unsigned (ew E0 36)) /\
Forall (fun p : bv 5 * sv => getr (ms_regs ms) (fst p) = sv_denot (Ereg regs0 []) (snd p)) PAREGSN /\
Forall (fun p : Z * sv => val_mem tfibsegs (mrestrict H (ms_mem ms)) (bv_unsigned (getr regs0 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg regs0 []) (snd p)))) PAFRAMESN.
Proof.
intros k extra regs0 E0 E' H ss ms Hk HS -> HA HD HM. unfold PACHKN in HM. apply andb_prop in HM as [HM HMl]. apply andb_prop in HM as [HMr HMf].
assert (HE0 : env_agree 32 (Ereg regs0 []) E').
{ split; [|rewrite HD; reflexivity].
intros n Hn. rewrite (HA n ltac:(lia)). unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia]. }
split; [|split].
- destruct (frame_chunk (ss_mem ss) (fst MIDLEN)) as [e|] eqn:Fc; [|discriminate HMl]. apply sv_eqb_eq in HMl. subst e.
pose proof (frame_chunk_val H E' ss ms (fst MIDLEN) (snd MIDLEN) HS Fc) as V.
rewrite (HA 2%nat ltac:(lia)) in V. unfold MIDLEN in V |- *. cbn [fst snd sv_denot] in V |- *.
rewrite (HA 36%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned in V. exact V.
- exact (regs_chk_ok 32 (Ereg regs0 []) E' H ss ms PAREGSN HS HE0 HMr).
- exact (frames_chk_ok 32 (Ereg regs0 []) E' H ss ms PAFRAMESN HS HE0 ltac:(lia) HMf).
Qed.
End c.

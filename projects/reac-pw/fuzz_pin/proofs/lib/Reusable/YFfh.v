(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFfh.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YFfh.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_pin. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0s YK0i YP09 YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG0f YG0v YG0n YG0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Definition XK_push (c off : Z) (X : astate) : astate :=
let p := cache X c in upd_pc c (mkPC (pc_max p) (pc_chunks p ++ [off - region_off c])) X.
Definition kdrained (c : Z) (X : astate) : list Z :=
let p := cache X c in skipn (length (pc_chunks p) - Z.to_nat (pc_max p / 2)) (pc_chunks p).
Definition kkeep (c : Z) (X : astate) : list Z :=
let p := cache X c in firstn (length (pc_chunks p) - Z.to_nat (pc_max p / 2)) (pc_chunks p).
Definition XK_drain (c : Z) (X : astate) : astate :=
let p := cache X c in let r := reg X c in
upd_pc c (mkPC (pc_max p) (kkeep c X))
(upd_reg c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (fa_push_list (rg_free r) (kdrained c X)) (rg_holes r)) X).
Lemma cache_upd_pc_same : forall c p X, 0 <= c -> (Z.to_nat c < length (st_cache X))%nat -> cache (upd_pc c p X) c = p.
Proof. intros c p X Hc Hl. unfold cache, upd_pc. cbn [st_cache set_cache]. apply znth_zupd_same; assumption. Qed.
Lemma reg_upd_pc' : forall c p X c', reg (upd_pc c p X) c' = reg X c'. Proof. reflexivity. Qed.
Lemma cache_upd_reg' : forall c r X c', cache (upd_reg c r X) c' = cache X c'. Proof. reflexivity. Qed.
Lemma len_cache_upd_reg : forall c r X, length (st_cache (upd_reg c r X)) = length (st_cache X). Proof. reflexivity. Qed.
Lemma cache_dealloc_eq_push : forall c off X,
st_cache_inited X = true -> Z.of_nat (length (pc_chunks (cache X c))) <> pc_max (cache X c) ->
cache_dealloc c off X = IRet (tt, XK_push c off X).
Proof.
intros c off X Hci Hnf. unfold cache_dealloc, init_cache_if_needed, get_pc, set_pc. unfold bind, get, ret, put, modify. cbn [ibind].
rewrite Hci. cbn [ibind]. fold (cache X c).
destruct (Z.eqb_spec (Z.of_nat (length (pc_chunks (cache X c)))) (pc_max (cache X c))); [lia|]. cbn [ibind]. reflexivity.
Qed.
Lemma cache_dealloc_eq_full : forall c off X,
st_cache_inited X = true -> 0 <= c -> (Z.to_nat c < length (st_cache X))%nat ->
Z.of_nat (length (pc_chunks (cache X c))) = pc_max (cache X c) ->
4 * (fa_len (rg_free (reg X c)) + Z.of_nat (length (kdrained c X))) <= rg_mapped_fa (reg X c) ->
cache_dealloc c off X = IRet (tt, XK_push c off (XK_drain c X)).
Proof.
intros c off X Hci Hc Hl Hfull Hroom. unfold cache_dealloc, init_cache_if_needed, get_pc, set_pc, return_to_allocator, ensure_free_array, get_region, set_region.
unfold bind, get, ret, put, modify. cbn [ibind].
rewrite Hci. cbn [ibind]. fold (cache X c). rewrite (proj2 (Z.eqb_eq _ _) Hfull). cbn [ibind]. fold (reg X c).
fold (kdrained c X). destruct (Z.leb_spec (4 * (fa_len (rg_free (reg X c)) + Z.of_nat (length (kdrained c X)))) (rg_mapped_fa (reg X c))); [|lia].
cbn [ibind]. reflexivity.
Qed.

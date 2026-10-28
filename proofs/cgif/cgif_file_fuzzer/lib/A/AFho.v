(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP0l YG00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0x AFhy AFhz.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhp AFhq AFhr AFhs AFht AFhu AFhv AFhw AFhx.
Import ListNotations. Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Definition nd_lo (k : Z) : Z := match k with 3 => 584 | 4 => 4232 | 5 => 16648 | 6 => 33288 | _ => 0 end.
Definition nd_hi (k : Z) : Z := match k with 3 => 4096 | 4 => 16384 | 5 => 32768 | 6 => 65536 | _ => 0 end.
Lemma piece_val : forall lo cnt s,
forallb (fun i => zev (fun _ => lo + 8 * Z.of_nat i) CL_hi =? class_id (lo + 8 * Z.of_nat i)) (seq 0 cnt) = true ->
lo <= s < lo + 8 * Z.of_nat cnt -> (s - lo) mod 8 = 0 -> zev (fun _ => s) CL_hi = class_id s.
Proof.
intros lo cnt s SW Hs Hm.
pose proof (Z.div_mod (s - lo) 8 ltac:(lia)) as DM.
pose proof (forallb_seq_In _ cnt (Z.to_nat ((s - lo) / 8)) SW ltac:(apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_lt_upper_bound; lia)) as Hp.
cbn beta in Hp. rewrite Z2Nat.id in Hp by (apply Z.div_pos; lia).
replace (lo + 8 * ((s - lo) / 8)) with s in Hp by lia. apply Z.eqb_eq in Hp. exact Hp.
Qed.
Lemma CL_hi_val : forall k s, 3 <= k <= 6 -> nd_lo k <= s <= nd_hi k -> s mod 8 = 0 -> zev (fun _ => s) CL_hi = class_id s.
Proof.
intros k s Hk Hs Hm.
assert (M8 : forall lo, lo mod 8 = 0 -> (s - lo) mod 8 = 0) by (intros lo Hlo; rewrite Zminus_mod, Hm, Hlo; reflexivity).
assert (K : k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
destruct K as [->|[->|[->| ->]]]; cbn in Hs.
- apply (piece_val 584 440 s sweep3); [cbn; lia | apply M8; reflexivity].
- destruct (Z_lt_le_dec s 10312).
+ apply (piece_val 4232 760 s sweep4a); [cbn; lia | apply M8; reflexivity].
+ apply (piece_val 10312 760 s sweep4b); [cbn; lia | apply M8; reflexivity].
- destruct (Z_lt_le_dec s 24712).
+ apply (piece_val 16648 1008 s sweep5a); [cbn; lia | apply M8; reflexivity].
+ apply (piece_val 24712 1008 s sweep5b); [cbn; lia | apply M8; reflexivity].
- destruct (Z_lt_le_dec s 41352); [|destruct (Z_lt_le_dec s 49416); [|destruct (Z_lt_le_dec s 57480)]].
+ apply (piece_val 33288 1008 s sweep6a); [cbn; lia | apply M8; reflexivity].
+ apply (piece_val 41352 1008 s sweep6b); [cbn; lia | apply M8; reflexivity].
+ apply (piece_val 49416 1008 s sweep6c); [cbn; lia | apply M8; reflexivity].
+ apply (piece_val 57480 1008 s sweep6d); [cbn; lia | apply M8; reflexivity].
Qed.
Lemma CL_lo_val : forall s, 0 <= s <= 512 -> zev (fun _ => s) CL_lo = class_id s.
Proof.
intros s Hs. pose proof seg1_stops as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ECL & _). rewrite ECL.
cbn [zev zalu_raw]. unfold class_id. replace (s <=? 512) with true by (symmetry; apply Z.leb_le; lia).
rewrite (zcanon_id (s + 31)) by (unfold M64; lia). rewrite (zcanon_id 5) by (unfold M64; lia).
change (Z.land 5 63) with 5. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. apply zcanon_id. unfold M64.
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

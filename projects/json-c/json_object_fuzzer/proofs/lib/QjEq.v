(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition zrange (lo n : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat n)).

Definition mono_f (a : Z) : bool := forallb (fun b => negb (a <? b) || (size_class a <? size_class b)) (zrange 0 48).

Definition stc_k (k : Z) : Z :=
if k <? 10 then k else
let n := k + 1 in
let i := (28 - clz32 n) * 4 + 8 in
let i := if size_class (i + 1) <? n then i + 2 else i in
if size_class i <? n then i + 1 else i.

Definition stc_f (k : Z) : bool := let sc := stc_k k in (0 <=? sc) && (sc <? 48) && (k + 1 <=? size_class sc).

#[local] Fixpoint zrange_bin (x : Z) (k : nat) : list Z := match k with O => [] | S k' => x :: zrange_bin (Z.succ x) k' end.

Lemma lor1_even sc : 0 <= sc -> Z.even sc = true -> Z.lor sc 1 = sc + 1.
Proof.
intros H He. assert (HE : Z.Even sc) by (apply Z.even_spec; exact He). destruct HE as [m ->].
apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
destruct (Z.eq_dec i 0) as [->|NZ].
- rewrite !Z.bit0_odd. replace (2 * m + 1) with (Z.succ (2 * m)) by lia. rewrite Z.odd_succ, He. change (Z.odd 1) with true. apply orb_true_r.
- assert (T1 : forall k, 0 <= k -> Z.testbit 1 (Z.succ k) = false).
{ intros k Hk. change (Z.testbit 1) with (Z.testbit (2 * 0 + 1)). rewrite Z.testbit_odd_succ by exact Hk. apply Z.testbit_0_l. }
replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ, Z.testbit_odd_succ, T1 by lia.
apply orb_false_r.
Qed.

Fixpoint he_list (f : nat) (c : Z) : list Z :=
match f with
| O => [c]
| S f' => c :: (if Z.even c then he_list f' (Z.shiftr c 1) else [])
end.

Definition cnt0_list (sc : Z) : list Z :=
let size := UNIT * size_class sc in
if sc <? 9 then [small_cnt sc 0; small_cnt sc 1; small_cnt sc 2]
else map (fun c => halve_big 8 c size) (he_list 8 (med_cnt (Z.land sc 3))).

Definition cnt0_of (sc u : Z) : Z :=
if sc <? 9 then small_cnt_pick sc u
else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) (UNIT * size_class sc).

Definition bump (size c : Z) : Z := if (c =? 1) && (size * c + UNIT <=? PGSZ / 2) then 2 else c.

Definition adj (sc size cnt : Z) : Z :=
if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
else cnt.

Definition grp_ok (sc cnt needed : Z) : bool :=
let size := UNIT * size_class sc in
let maplen := Z.shiftr needed 12 in
let last := cnt - 1 in
let stride := if (last =? 0) && negb (maplen =? 0) then maplen * 4096 - UNIT else size in
(1 <=? cnt) && (cnt <=? 32) && (needed mod 4096 =? 0) && (4096 <=? needed) && (needed <=? 2 ^ 20)
&& (UNIT + stride * cnt <=? maplen * 4096)
&& ((stride <=? size) || (28 <=? sc))
&& (negb (last =? 0) || (27 <=? sc))
&& (stride * cnt <? 2 ^ 20) && (16 <=? stride) && (stride mod 16 =? 0).

Definition nest_ok (sc cnt : Z) : bool :=
let size := UNIT * size_class sc in
let n' := UNIT + cnt * size - IB in
let j := size_to_class n' in
(2 <=? cnt) && (cnt <=? 32) && (sc <? j) && (j <=? 23) && (UNIT + cnt * size <=? UNIT * size_class j) && (size * cnt <? 2 ^ 20)
&& (0 <=? n') && (n' + IB <=? 2048).

Definition qmax (sc : Z) : Z := (UNIT * size_class sc + UNIT + 4095) / 4096.

Definition ag_check_sc (sc : Z) : bool :=
let size := UNIT * size_class sc in
forallb (fun cnt0 =>
let cnt1 := bump size cnt0 in
if PGSZ / 2 <? size * cnt1 + UNIT then
forallb (fun cnt2 =>
grp_ok sc cnt2 (round_up_pg (size * cnt2 + UNIT))
&& (negb (cnt2 <=? 7)
|| forallb (fun q => negb ((q * 4096 <? size + UNIT) || (4 <=? q)) || (grp_ok sc 1 (q * 4096) && (28 <=? sc))) (zrange 1 (qmax sc))))
[cnt1; adj sc size cnt1]
else nest_ok sc cnt1)
(cnt0_list sc).


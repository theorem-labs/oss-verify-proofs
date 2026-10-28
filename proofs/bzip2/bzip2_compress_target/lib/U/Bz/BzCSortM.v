(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition BZ_N_RADIX : Z := 2.
Definition BZ_N_OVERSHOOT : Z := 34.
Definition SETMASK : Z := 2097152.                 (* [comment removed for export] *)
Definition clearmask (x : Z) : Z := Z.land x 4292870143.   (* [comment removed for export] *)
Definition has_setmask (x : Z) : bool := negb (Z.land x SETMASK =? 0).

Definition qrd (a2 : zarr) (qoff i : Z) : Z := rd16 a2 (qoff + 2 * i).
Definition qwr (a2 : zarr) (qoff i v : Z) : zarr := wr16 a2 (qoff + 2 * i) v.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint gtu_pre (n : nat) (a2 : zarr) (i1 i2 : Z) : option bool * Z * Z :=
  match n with
  | O => (None, i1, i2)
  | S n' => let c1 := rd8 a2 i1 in let c2 := rd8 a2 i2 in
            if negb (c1 =? c2) then (Some (c2 <? c1), i1, i2) else gtu_pre n' a2 (i1 + 1) (i2 + 1)
  end.
(* [comment removed for export] *)
Fixpoint gtu_oct (n : nat) (a2 : zarr) (qoff i1 i2 : Z) : option bool * Z * Z :=
  match n with
  | O => (None, i1, i2)
  | S n' => let c1 := rd8 a2 i1 in let c2 := rd8 a2 i2 in
            if negb (c1 =? c2) then (Some (c2 <? c1), i1, i2) else
            let s1 := qrd a2 qoff i1 in let s2 := qrd a2 qoff i2 in
            if negb (s1 =? s2) then (Some (s2 <? s1), i1, i2) else gtu_oct n' a2 qoff (i1 + 1) (i2 + 1)
  end.
(* [comment removed for export] *)
Fixpoint gtu_loop (fuel : nat) (a2 : zarr) (qoff nblock i1 i2 k budget : Z) : bool * Z :=
  match fuel with
  | O => (false, budget)
  | S f =>
      let '(r, i1, i2) := gtu_oct 8%nat a2 qoff i1 i2 in
      match r with
      | Some b => (b, budget)
      | None =>
          let i1 := if nblock <=? i1 then i1 - nblock else i1 in
          let i2 := if nblock <=? i2 then i2 - nblock else i2 in
          let k := k - 8 in
          let budget := budget - 1 in
          if 0 <=? k then gtu_loop f a2 qoff nblock i1 i2 k budget else (false, budget)
      end
  end.
Definition mainGtU (i1 i2 : Z) (a2 : zarr) (qoff nblock budget : Z) : bool * Z :=
  let '(r, i1, i2) := gtu_pre 12%nat a2 i1 i2 in
  match r with
  | Some b => (b, budget)
  | None => gtu_loop (S (S (Z.to_nat ((nblock + 8) / 8)))) a2 qoff nblock i1 i2 (nblock + 8) budget
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition incs : list Z := [1; 4; 13; 40; 121; 364; 1093; 3280; 9841; 29524; 88573; 265720; 797161; 2391484].
Definition incs_at (hp : Z) : Z := nth (Z.to_nat hp) incs 0.
(* [comment removed for export] *)
Fixpoint mss_hp (fuel : nat) (bigN hp : Z) : Z :=
  match fuel with O => hp | S f => if incs_at hp <? bigN then mss_hp f bigN (hp + 1) else hp end.

(* [comment removed for export] *)
Fixpoint mss_shift (fuel : nat) (a1 a2 : zarr) (qoff nblock d h lo j v budget : Z) : zarr * Z * Z :=
  match fuel with
  | O => (a1, j, budget)
  | S f =>
      let '(gt, budget) := mainGtU (rd32 a1 (j - h) + d) (v + d) a2 qoff nblock budget in
      if gt then
        let a1 := wr32 a1 j (rd32 a1 (j - h)) in
        let j := j - h in
        if j <=? lo + h - 1 then (a1, j, budget) else mss_shift f a1 a2 qoff nblock d h lo j v budget
      else (a1, j, budget)
  end.
(* [comment removed for export] *)
Definition mss_ins (a1 a2 : zarr) (qoff nblock d h lo i budget : Z) : zarr * Z :=
  let v := rd32 a1 i in
  let '(a1, j, budget) := mss_shift (S (Z.to_nat (i - lo))) a1 a2 qoff nblock d h lo i v budget in
  (wr32 a1 j v, budget).
(* [comment removed for export] *)
Fixpoint mss_hloop (fuel : nat) (a1 a2 : zarr) (qoff nblock d h lo hi i budget : Z) : zarr * Z * bool :=
  match fuel with
  | O => (a1, budget, false)
  | S f =>
      if hi <? i then (a1, budget, false) else
      let '(a1, budget) := mss_ins a1 a2 qoff nblock d h lo i budget in let i := i + 1 in
      if hi <? i then (a1, budget, false) else
      let '(a1, budget) := mss_ins a1 a2 qoff nblock d h lo i budget in let i := i + 1 in
      if hi <? i then (a1, budget, false) else
      let '(a1, budget) := mss_ins a1 a2 qoff nblock d h lo i budget in let i := i + 1 in
      if budget <? 0 then (a1, budget, true) else mss_hloop f a1 a2 qoff nblock d h lo hi i budget
  end.
(* [comment removed for export] *)
Fixpoint mss_hps (n : nat) (a1 a2 : zarr) (qoff nblock d lo hi hp budget : Z) : zarr * Z * bool :=
  match n with
  | O => (a1, budget, false)
  | S n' =>
      let h := incs_at hp in
      let '(a1, budget, ex) := mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qoff nblock d h lo hi (lo + h) budget in
      if ex then (a1, budget, true) else mss_hps n' a1 a2 qoff nblock d lo hi (hp - 1) budget
  end.
Definition mainSimpleSort (a1 a2 : zarr) (qoff nblock lo hi d budget : Z) : zarr * Z :=
  let bigN := hi - lo + 1 in
  if bigN <? 2 then (a1, budget) else
  let hp := mss_hp 15%nat bigN 0 - 1 in
  let '(a1, budget, _) := mss_hps (Z.to_nat (hp + 1)) a1 a2 qoff nblock d lo hi hp budget in
  (a1, budget).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mswap (a1 : zarr) (x y : Z) : zarr :=
  let tmp := rd32 a1 x in wr32 (wr32 a1 x (rd32 a1 y)) y tmp.
Fixpoint mvswap (fuel : nat) (a1 : zarr) (p1 p2 n : Z) : zarr :=
  match fuel with
  | O => a1
  | S f => if 0 <? n then mvswap f (mswap a1 p1 p2) (p1 + 1) (p2 + 1) (n - 1) else a1
  end.
Definition mmed3 (a b c : Z) : Z :=
  let '(a, b) := (if b <? a then (b, a) else (a, b)) in
  if c <? b then (if c <? a then a else c) else b.
Definition mmin (a b : Z) : Z := if a <? b then a else b.

Record mpart := MP { mp_a1 : zarr; mp_unLo : Z; mp_unHi : Z; mp_ltLo : Z; mp_gtHi : Z }.
Fixpoint mpart_lo (fuel : nat) (a2 : zarr) (d med : Z) (p : mpart) : mpart :=
  match fuel with
  | O => p
  | S f =>
      if mp_unHi p <? mp_unLo p then p else
      let n := rd8 a2 (rd32 (mp_a1 p) (mp_unLo p) + d) - med in
      if n =? 0 then mpart_lo f a2 d med (MP (mswap (mp_a1 p) (mp_unLo p) (mp_ltLo p)) (mp_unLo p + 1) (mp_unHi p) (mp_ltLo p + 1) (mp_gtHi p))
      else if 0 <? n then p
      else mpart_lo f a2 d med (MP (mp_a1 p) (mp_unLo p + 1) (mp_unHi p) (mp_ltLo p) (mp_gtHi p))
  end.
Fixpoint mpart_hi (fuel : nat) (a2 : zarr) (d med : Z) (p : mpart) : mpart :=
  match fuel with
  | O => p
  | S f =>
      if mp_unHi p <? mp_unLo p then p else
      let n := rd8 a2 (rd32 (mp_a1 p) (mp_unHi p) + d) - med in
      if n =? 0 then mpart_hi f a2 d med (MP (mswap (mp_a1 p) (mp_unHi p) (mp_gtHi p)) (mp_unLo p) (mp_unHi p - 1) (mp_ltLo p) (mp_gtHi p - 1))
      else if n <? 0 then p
      else mpart_hi f a2 d med (MP (mp_a1 p) (mp_unLo p) (mp_unHi p - 1) (mp_ltLo p) (mp_gtHi p))
  end.
Fixpoint mpart_loop (fuel : nat) (sz : nat) (a2 : zarr) (d med : Z) (p : mpart) : mpart :=
  match fuel with
  | O => p
  | S f =>
      let p1 := mpart_lo (S sz) a2 d med p in
      let p2 := mpart_hi (S sz) a2 d med p1 in
      if mp_unHi p2 <? mp_unLo p2 then p2
      else mpart_loop f sz a2 d med (MP (mswap (mp_a1 p2) (mp_unLo p2) (mp_unHi p2)) (mp_unLo p2 + 1) (mp_unHi p2 - 1) (mp_ltLo p2) (mp_gtHi p2))
  end.

(* [comment removed for export] *)
Record mqs := MQS { mq_a1 : zarr; mq_sp : Z; mq_slo : zarr; mq_shi : zarr; mq_sd : zarr;
                    mq_nlo : zarr; mq_nhi : zarr; mq_nd : zarr; mq_budget : Z; mq_exit : bool }.
Definition mpush (q : mqs) (lz hz dz : Z) : mqs :=
  MQS (mq_a1 q) (mq_sp q + 1) (zset (mq_slo q) (mq_sp q) lz) (zset (mq_shi q) (mq_sp q) hz) (zset (mq_sd q) (mq_sp q) dz)
      (mq_nlo q) (mq_nhi q) (mq_nd q) (mq_budget q) (mq_exit q).
Definition mnextsize (q : mqs) (az : Z) : Z := zget (mq_nhi q) az - zget (mq_nlo q) az.
Definition mnextswap (q : mqs) (az bz : Z) : mqs :=
  let nlo := mq_nlo q in let nhi := mq_nhi q in let nd := mq_nd q in
  let tz := zget nlo az in let nlo := zset (zset nlo az (zget nlo bz)) bz tz in
  let tz := zget nhi az in let nhi := zset (zset nhi az (zget nhi bz)) bz tz in
  let tz := zget nd az in let nd := zset (zset nd az (zget nd bz)) bz tz in
  MQS (mq_a1 q) (mq_sp q) (mq_slo q) (mq_shi q) (mq_sd q) nlo nhi nd (mq_budget q) (mq_exit q).

(* [comment removed for export] *)
Definition mqs_iter (a2 : zarr) (qoff nblock : Z) (q : mqs) : mqs :=
  let sp := mq_sp q - 1 in
  let lo := zget (mq_slo q) sp in let hi := zget (mq_shi q) sp in let d := zget (mq_sd q) sp in
  if (hi - lo <? 20) || (14 <? d) then
    let '(a1, budget) := mainSimpleSort (mq_a1 q) a2 qoff nblock lo hi d (mq_budget q) in
    MQS a1 sp (mq_slo q) (mq_shi q) (mq_sd q) (mq_nlo q) (mq_nhi q) (mq_nd q) budget (budget <? 0)
  else
    let a1 := mq_a1 q in
    let med := mmed3 (rd8 a2 (rd32 a1 lo + d)) (rd8 a2 (rd32 a1 hi + d)) (rd8 a2 (rd32 a1 (Z.shiftr (lo + hi) 1) + d)) in
    let sz := Z.to_nat (hi - lo + 1) in
    let p := mpart_loop (S sz) sz a2 d med (MP a1 lo hi lo hi) in
    let unLo := mp_unLo p in let unHi := mp_unHi p in let ltLo := mp_ltLo p in let gtHi := mp_gtHi p in
    let q1 := MQS (mp_a1 p) sp (mq_slo q) (mq_shi q) (mq_sd q) (mq_nlo q) (mq_nhi q) (mq_nd q) (mq_budget q) false in
    if gtHi <? ltLo then mpush q1 lo hi (d + 1)
    else
      let n := mmin (ltLo - lo) (unLo - ltLo) in
      let a1 := mvswap (S (Z.to_nat n)) (mp_a1 p) lo (unLo - n) n in
      let m := mmin (hi - gtHi) (gtHi - unHi) in
      let a1 := mvswap (S (Z.to_nat m)) a1 unLo (hi - m + 1) m in
      let n := lo + unLo - ltLo - 1 in
      let m := hi - (gtHi - unHi) + 1 in
      let nlo := zset (zset (zset (mq_nlo q) 0 lo) 1 m) 2 (n + 1) in
      let nhi := zset (zset (zset (mq_nhi q) 0 n) 1 hi) 2 (m - 1) in
      let nd := zset (zset (zset (mq_nd q) 0 d) 1 d) 2 (d + 1) in
      let q2 := MQS a1 sp (mq_slo q) (mq_shi q) (mq_sd q) nlo nhi nd (mq_budget q) false in
      let q2 := if mnextsize q2 0 <? mnextsize q2 1 then mnextswap q2 0 1 else q2 in
      let q2 := if mnextsize q2 1 <? mnextsize q2 2 then mnextswap q2 1 2 else q2 in
      let q2 := if mnextsize q2 0 <? mnextsize q2 1 then mnextswap q2 0 1 else q2 in
      let q3 := mpush q2 (zget (mq_nlo q2) 0) (zget (mq_nhi q2) 0) (zget (mq_nd q2) 0) in
      let q3 := mpush q3 (zget (mq_nlo q3) 1) (zget (mq_nhi q3) 1) (zget (mq_nd q3) 1) in
      mpush q3 (zget (mq_nlo q3) 2) (zget (mq_nhi q3) 2) (zget (mq_nd q3) 2).

Fixpoint mqs_loop (fuel : nat) (a2 : zarr) (qoff nblock : Z) (q : mqs) : mqs :=
  match fuel with
  | O => q
  | S f => if (0 <? mq_sp q) && negb (mq_exit q) then mqs_loop f a2 qoff nblock (mqs_iter a2 qoff nblock q) else q
  end.

(* [comment removed for export] *)
Record mqloc := MQL { ml_slo : zarr; ml_shi : zarr; ml_sd : zarr; ml_nlo : zarr; ml_nhi : zarr; ml_nd : zarr }.

Definition mqs_fuel (loSt hiSt : Z) : nat := Z.to_nat (64 * (hiSt - loSt) + 64).

(* [comment removed for export] *)
Definition mainQSort3 (a1 a2 : zarr) (qoff nblock loSt hiSt dSt budget : Z) (l : mqloc) : zarr * Z * mqloc :=
  let q := mpush (MQS a1 0 (ml_slo l) (ml_shi l) (ml_sd l) (ml_nlo l) (ml_nhi l) (ml_nd l) budget false) loSt hiSt dSt in
  let q := mqs_loop (mqs_fuel loSt hiSt) a2 qoff nblock q in
  (mq_a1 q, mq_budget q, MQL (mq_slo q) (mq_shi q) (mq_sd q) (mq_nlo q) (mq_nhi q) (mq_nd q)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint ms_ftab_zero (n : nat) (ft : zarr) (i : Z) : zarr :=
  match n with O => ft | S n' => ms_ftab_zero n' (zset ft i 0) (i - 1) end.
(* [comment removed for export] *)
Fixpoint ms_radix1 (n : nat) (a2 ft : zarr) (qoff i j : Z) : zarr * zarr * Z :=
  match n with
  | O => (a2, ft, j)
  | S n' => let a2 := qwr a2 qoff i 0 in
            let j := Z.lor (Z.shiftr j 8) (Z.shiftl (rd8 a2 i) 8) in
            ms_radix1 n' a2 (zincr ft j) qoff (i - 1) j
  end.
(* [comment removed for export] *)
Fixpoint ms_overshoot (n : nat) (a2 : zarr) (qoff nblock i : Z) : zarr :=
  match n with
  | O => a2
  | S n' => ms_overshoot n' (qwr (wr8 a2 (nblock + i) (rd8 a2 i)) qoff (nblock + i) 0) qoff nblock (i + 1)
  end.
(* [comment removed for export] *)
Fixpoint ms_accum (n : nat) (ft : zarr) (i : Z) : zarr :=
  match n with O => ft | S n' => ms_accum n' (zset ft i (zget ft i + zget ft (i - 1))) (i + 1) end.
(* [comment removed for export] *)
Fixpoint ms_radix2 (n : nat) (a1 a2 ft : zarr) (i s : Z) : zarr * zarr * Z :=
  match n with
  | O => (a1, ft, s)
  | S n' => let s := Z.lor (Z.shiftr s 8) (Z.shiftl (rd8 a2 i) 8) in
            let j := zget ft s - 1 in
            ms_radix2 n' (wr32 a1 j i) a2 (zset ft s j) (i - 1) s
  end.
(* [comment removed for export] *)
Fixpoint ms_ro_init (n : nat) (bd ro : zarr) (i : Z) : zarr * zarr :=
  match n with O => (bd, ro) | S n' => ms_ro_init n' (zset bd i 0) (zset ro i i) (i + 1) end.

Definition bigfreq (ft : zarr) (b : Z) : Z := zget ft (Z.shiftl (b + 1) 8) - zget ft (Z.shiftl b 8).
(* [comment removed for export] *)
Fixpoint ms_sh_shift (fuel : nat) (ro ft : zarr) (h j vv : Z) : zarr * Z :=
  match fuel with
  | O => (ro, j)
  | S f => if bigfreq ft vv <? bigfreq ft (zget ro (j - h)) then
             let ro := zset ro j (zget ro (j - h)) in let j := j - h in
             if j <=? h - 1 then (ro, j) else ms_sh_shift f ro ft h j vv
           else (ro, j)
  end.
(* [comment removed for export] *)
Fixpoint ms_sh_pass (n : nat) (ro ft : zarr) (h i : Z) : zarr :=
  match n with
  | O => ro
  | S n' => let vv := zget ro i in
            let '(ro, j) := ms_sh_shift 300%nat ro ft h i vv in
            ms_sh_pass n' (zset ro j vv) ft h (i + 1)
  end.
(* [comment removed for export] *)
Fixpoint ms_shell (fuel : nat) (ro ft : zarr) (h : Z) : zarr :=
  match fuel with
  | O => ro
  | S f => let h := h / 3 in
           let ro := ms_sh_pass (Z.to_nat (256 - h)) ro ft h h in
           if h =? 1 then ro else ms_shell f ro ft h
  end.

(* [comment removed for export] *)
Record mss := MSS { s_a1 : zarr; s_a2 : zarr; s_ft : zarr; s_bd : zarr; s_cs : zarr; s_ce : zarr;
                    s_budget : Z; s_nqs : Z; s_mql : mqloc; s_exit : bool }.

(* [comment removed for export] *)
Fixpoint ms_step1 (n : nat) (qoff nblock ss j : Z) (s : mss) : mss :=
  match n with
  | O => s
  | S n' =>
      if s_exit s then s else
      if j =? ss then ms_step1 n' qoff nblock ss (j + 1) s else
      let sb := Z.shiftl ss 8 + j in
      let ft := s_ft s in
      let '(s1, stop) :=
        (if negb (has_setmask (zget ft sb)) then
           let lo := clearmask (zget ft sb) in
           let hi := clearmask (zget ft (sb + 1)) - 1 in
           if lo <? hi then
             let '(a1, budget, mql) := mainQSort3 (s_a1 s) (s_a2 s) qoff nblock lo hi BZ_N_RADIX (s_budget s) (s_mql s) in
             let s1 := MSS a1 (s_a2 s) ft (s_bd s) (s_cs s) (s_ce s) budget (s_nqs s + (hi - lo + 1)) mql false in
             if budget <? 0 then (MSS a1 (s_a2 s) ft (s_bd s) (s_cs s) (s_ce s) budget (s_nqs s + (hi - lo + 1)) mql true, true)
             else (s1, false)
           else (s, false)
         else (s, false)) in
      if stop then s1 else
      let s2 := MSS (s_a1 s1) (s_a2 s1) (zset (s_ft s1) sb (Z.lor (zget (s_ft s1) sb) SETMASK)) (s_bd s1) (s_cs s1) (s_ce s1)
                    (s_budget s1) (s_nqs s1) (s_mql s1) false in
      ms_step1 n' qoff nblock ss (j + 1) s2
  end.

(* [comment removed for export] *)
Fixpoint ms_copy_init (n : nat) (cs ce ft : zarr) (ss j : Z) : zarr * zarr :=
  match n with
  | O => (cs, ce)
  | S n' => ms_copy_init n' (zset cs j (clearmask (zget ft (Z.shiftl j 8 + ss))))
                            (zset ce j (clearmask (zget ft (Z.shiftl j 8 + ss + 1)) - 1)) ft ss (j + 1)
  end.
(* [comment removed for export] *)
Fixpoint ms_copy_fwd (fuel : nat) (a1 cs a2 bd : zarr) (nblock ss j : Z) : zarr * zarr * Z :=
  match fuel with
  | O => (a1, cs, j)
  | S f =>
      if j <? zget cs ss then
        let k := rd32 a1 j - 1 in let k := if k <? 0 then k + nblock else k in
        let c1 := rd8 a2 k in
        let '(a1, cs) := (if zget bd c1 =? 0 then (wr32 a1 (zget cs c1) k, zset cs c1 (zget cs c1 + 1)) else (a1, cs)) in
        ms_copy_fwd f a1 cs a2 bd nblock ss (j + 1)
      else (a1, cs, j)
  end.
(* [comment removed for export] *)
Fixpoint ms_copy_bwd (fuel : nat) (a1 ce a2 bd : zarr) (nblock ss j : Z) : zarr * zarr * Z :=
  match fuel with
  | O => (a1, ce, j)
  | S f =>
      if zget ce ss <? j then
        let k := rd32 a1 j - 1 in let k := if k <? 0 then k + nblock else k in
        let c1 := rd8 a2 k in
        let '(a1, ce) := (if zget bd c1 =? 0 then (wr32 a1 (zget ce c1) k, zset ce c1 (zget ce c1 - 1)) else (a1, ce)) in
        ms_copy_bwd f a1 ce a2 bd nblock ss (j - 1)
      else (a1, ce, j)
  end.
(* [comment removed for export] *)
Fixpoint ms_mark (n : nat) (ft : zarr) (ss j : Z) : zarr :=
  match n with O => ft | S n' => ms_mark n' (let x := Z.shiftl j 8 + ss in zset ft x (Z.lor (zget ft x) SETMASK)) ss (j + 1) end.
(* [comment removed for export] *)
Fixpoint ms_shifts (fuel : nat) (bbSize shifts : Z) : Z :=
  match fuel with O => shifts | S f => if 65534 <? Z.shiftr bbSize shifts then ms_shifts f bbSize (shifts + 1) else shifts end.
Fixpoint ms_quad (n : nat) (a2 a1 : zarr) (qoff nblock bbStart shifts j : Z) : zarr :=
  match n with
  | O => a2
  | S n' =>
      let a2u := rd32 a1 (bbStart + j) in
      let qVal := Z.shiftr j shifts in
      let a2 := qwr a2 qoff a2u qVal in
      let a2 := if a2u <? BZ_N_OVERSHOOT then qwr a2 qoff (a2u + nblock) qVal else a2 in
      ms_quad n' a2 a1 qoff nblock bbStart shifts (j - 1)
  end.

(* [comment removed for export] *)
Definition ms_big (ro : zarr) (qoff nblock i : Z) (s : mss) : mss :=
  let ss := zget ro i in
  let s1 := ms_step1 256%nat qoff nblock ss 0 s in
  if s_exit s1 then s1 else
  let ft := s_ft s1 in
  let '(cs, ce) := ms_copy_init 256%nat (s_cs s1) (s_ce s1) ft ss 0 in
  let '(a1, cs, _) := ms_copy_fwd (S (Z.to_nat nblock)) (s_a1 s1) cs (s_a2 s1) (s_bd s1) nblock ss (clearmask (zget ft (Z.shiftl ss 8))) in
  let '(a1, ce, _) := ms_copy_bwd (S (Z.to_nat nblock)) a1 ce (s_a2 s1) (s_bd s1) nblock ss (clearmask (zget ft (Z.shiftl (ss + 1) 8)) - 1) in
  let ft := ms_mark 256%nat ft ss 0 in
  let bd := zset (s_bd s1) ss 1 in
  let a2 := (if i <? 255 then
               let bbStart := clearmask (zget ft (Z.shiftl ss 8)) in
               let bbSize := clearmask (zget ft (Z.shiftl (ss + 1) 8)) - bbStart in
               let shifts := ms_shifts 40%nat bbSize 0 in
               ms_quad (Z.to_nat bbSize) (s_a2 s1) a1 qoff nblock bbStart shifts (bbSize - 1)
             else s_a2 s1) in
  MSS a1 a2 ft bd cs ce (s_budget s1) (s_nqs s1) (s_mql s1) false.

Fixpoint ms_bigs (n : nat) (ro : zarr) (qoff nblock i : Z) (s : mss) : mss :=
  match n with
  | O => s
  | S n' => let s1 := ms_big ro qoff nblock i s in
            if s_exit s1 then s1 else ms_bigs n' ro qoff nblock (i + 1) s1
  end.

(* [comment removed for export] *)
Record msres := MSR { mr_ptr : zarr; mr_block : zarr; mr_ftab : zarr; mr_budget : Z;
                      mr_ro : zarr; mr_bd : zarr; mr_cs : zarr; mr_ce : zarr; mr_mql : mqloc; mr_nqs : Z }.

(* [comment removed for export] *)
Definition mainSort (a1 a2 ft ro0 bd0 cs0 ce0 sl0 sh0 sd0 : zarr) (qoff nblock budget : Z) : msres :=
  let ft := ms_ftab_zero 65537%nat ft 65536 in
  let j := Z.shiftl (rd8 a2 0) 8 in
  let '(a2, ft, _) := ms_radix1 (Z.to_nat nblock) a2 ft qoff (nblock - 1) j in
  let a2 := ms_overshoot 34%nat a2 qoff nblock 0 in
  let ft := ms_accum 65536%nat ft 1 in
  let s := Z.shiftl (rd8 a2 0) 8 in
  let '(a1, ft, _) := ms_radix2 (Z.to_nat nblock) a1 a2 ft (nblock - 1) s in
  let '(bd, ro) := ms_ro_init 256%nat bd0 ro0 0 in
  let ro := ms_shell 8%nat ro ft 364 in
  let st := ms_bigs 256%nat ro qoff nblock 0 (MSS a1 a2 ft bd cs0 ce0 budget 0 (MQL sl0 sh0 sd0 sl0 sh0 sd0) false) in
  MSR (s_a1 st) (s_a2 st) (s_ft st) (s_budget st) ro (s_bd st) (s_cs st) (s_ce st) (s_mql st) (s_nqs st).

(** * EnoughDP — computable Gallina transcription of zlib's examples/enough.c
    (Mark Adler, v1.5), the DP that computes the WORST-CASE inflate table
    size over all valid complete prefix codes for (syms, root, max).

    R63 scaffolding, LAYER 1 (g6-bound lane, 2026-08-21).
    SOURCE OF TRUTH: zlib-1.3.1/examples/enough.c,
      md5 (pinned copy: enough.c.pinned
      beside this file).  Every function below carries the enough.c line
      range it transcribes; FIDELITY over elegance -- diff side-by-side.

    The famous outputs (verified from zlib's inftrees.h:49-51):
      enough_run 286 9 15 = Some (_, Some 852)   (ENOUGH_LENS)
      enough_run  30 6 15 = Some (_, Some 592)   (ENOUGH_DISTS)
    The tree consumes these constants at Spec/PngModel/Inftrees.v:60-61
    (ENOUGH_LENS/ENOUGH_DISTS) through the [it_enough] runtime guard.

    FIDELITY DEVIATIONS (complete list):
      D1. C's internal-type overflow aborts (enough.c:531-537: max > bits,
          (syms-2) >= UINTMAX>>(max-1)) are NOT mirrored -- they are
          uintmax_t artifacts, not properties of the function.  Z cannot
          overflow.  (The C's own printed results are overflow-checked by
          its asserts, so C outputs used as oracle cells are sound.)
      D2. A Gallina-side domain guard (max <= 32, syms <= 2^20, root <= 32)
          returns None: it keeps the arithmetic memo-key packing below
          injective without proof burden.  All C-runnable parameter sets
          of interest sit far inside it.
      D3. The num[]/done[] ARRAY INDEX SCHEMES (map(), enough.c:236-241,
          and been_here's triangular (mem,rem) packing, :309-315) are
          replaced by finite maps keyed directly on the semantic tuples
          (syms,left,len) resp. (syms,left,len,mem,rem).  Both C schemes
          are injective on their domains (triangular indexing valid since
          rem' <= (mem'>>3)+rem'), so the SET semantics are identical.
      D4. been_here's normalization (mem -= 1<<root; mem >>= 1; rem >>= 1,
          :310-312) is index compression, a bijection on the reachable
          (even, even) values -- keys here use the raw values.
      D5. All display/string machinery (g.out, g.code[] bookkeeping for
          printing the maximizing sub-codes) is dropped; only the bound
          [g.large] and the code count are computed.
      D6. C's memo hit test is [if (got) ...] (nonzero); mirrored exactly:
          a stored 0 is treated as a miss.  (C never stores 0 -- its
          assert(sum != 0) -- and the recursions are identical, so this
          branch is dead; mirrored anyway.)
      D7. Loops become fuel-indexed fixpoints with fuel PROVABLY above the
          iteration count on live states (see each site); fuel exhaustion
          returns the current accumulator and is dead code on any input
          the C accepts (same pinch arguments as the C's own asserts).

    TRUST NOTE for the harness (Layer 2): validation Examples use
    native_compute; the native compiler is part of the trusted base for
    the ORACLE role only -- the eventual reflection theorem (Layer 3) is
    free to re-check with vm_compute/lazy at its author's discretion. *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Module PM := PositiveMap.

(* ==========================================================================
   Memo keys (replaces map(), enough.c:236-241 -- deviation D3).
   Fields are packed at 2^40 spacing; the D2 domain guard keeps every
   field below 2^40, so packing is injective on the guarded domain.
   ========================================================================== *)

Definition W : Z := 2^40.

Definition key3 (syms left len : Z) : positive :=
  Z.to_pos (1 + len + W * (left + W * syms)).

Definition key5 (syms left len mem rem : Z) : positive :=
  Z.to_pos (1 + rem + W * (mem + W * (len + W * (left + W * syms)))).

(* ==========================================================================
   count (enough.c:257-302): number of prefix codes from the juncture
   (syms symbols left; left bit patterns free at length len; lengths
   len..max usable), memoized in num[] (here: a PM.t Z).

   Fuel: len strictly increases and every live path completes (syms==left)
   at len <= max (the least/most pinch, cf. the C's assert(len < g.max)),
   so fuel = max+1 (in nat) suffices; the O-branch is dead (D7).
   ========================================================================== *)

Fixpoint countF (fuel : nat) (mx syms left len : Z) (memo : PM.t Z)
  : Z * PM.t Z :=
  match fuel with
  | O => (0, memo)                                        (* dead, D7 *)
  | S f =>
      (* :259-260  if (syms == left) return 1; *)
      if syms =? left then (1, memo)
      else
        let k := key3 syms left len in
        (* :266-269  memo hit iff stored value nonzero (D6) *)
        match PM.find k memo with
        | Some v =>
            if v =? 0
            then (0, memo)      (* dead (D6): C never stores 0 *)
            else (v, memo)
        | None =>
            (* :271-275  least = max(0, (left << 1) - syms) *)
            let least := Z.max 0 (2 * left - syms) in
            (* :277-281  most = ((left << (max-len)) - syms)
                                / ((1 << (max-len)) - 1) *)
            let most := (left * 2^(mx - len) - syms) / (2^(mx - len) - 1) in
            (* :283-291  sum over use = least..most of
                         count(syms-use, (left-use)<<1, len+1) *)
            let loop :=
              fix loop (n : nat) (use acc : Z) (m : PM.t Z) : Z * PM.t Z :=
                match n with
                | O => (acc, m)
                | S n' =>
                    let '(got, m1) :=
                      countF f mx (syms - use) (2 * (left - use)) (len + 1) m
                    in loop n' (use + 1) (acc + got) m1
                end in
            let '(sum, memo1) :=
              loop (Z.to_nat (most - least + 1)) least 0 memo in
            (* :297-300  save and return *)
            (sum, PM.add k sum memo1)
        end
  end.

(* ==========================================================================
   The shared table-space drain loop.  Transcribes BOTH
     :368-372  while (rem < left) { left -= rem; rem = 1 << (len-root);
                                    mem += rem; }
     :426-430  while (rem < use)  { use  -= rem; rem = 1 << (len-root);
                                    mem += rem; }
   as  drain fuel subsz x mem rem = (x', mem', rem')  with
   subsz = 2^(len-root).  Fuel: x <= syms <= 2^20 at every call site and
   after the first iteration rem = subsz >= 2, so iterations <= x/2 + 2;
   fuel = Z.to_nat x + 2 covers it (D7).
   ========================================================================== *)

Fixpoint drain (fuel : nat) (subsz x mem rem : Z) : Z * Z * Z :=
  match fuel with
  | O => (x, mem, rem)                                    (* dead, D7 *)
  | S f =>
      if rem <? x
      then drain f subsz (x - rem) (mem + subsz) subsz
      else (x, mem, rem)
  end.

(* ==========================================================================
   examine (enough.c:357-446): walk all sub-codes from the juncture,
   tracking inflate table space (mem = entries allocated so far including
   every opened sub-table at full size; rem = unused entries in the
   current sub-table), pruning re-visited states via done[] (here: a
   PM.t unit on the raw 5-tuple, D3/D4), and maximizing into [large].

   State threaded: (large, done).  Fuel as in countF.
   ========================================================================== *)

Fixpoint examineF (fuel : nat) (mx rt : Z)
                  (syms left len mem rem : Z)
                  (st : Z * PM.t unit) : Z * PM.t unit :=
  match fuel with
  | O => st                                               (* dead, D7 *)
  | S f =>
      let subsz := 2^(len - rt) in
      (* :362-405  complete code *)
      if syms =? left then
        let '(large, done) := st in
        (* :368-372  close out the last sub-table(s) *)
        let '(_, mem1, _) := drain (Z.to_nat left + 2)%nat subsz left mem rem in
        (* :375-405  new maximum?  (display dropped, D5: only the max) *)
        (Z.max large mem1, done)
      else
        let '(large, done) := st in
        (* :408-410  prune if we have been here before *)
        let k := key5 syms left len mem rem in
        match PM.find k done with
        | Some _ => st
        | None =>
            let done1 := PM.add k tt done in
            (* :412-416 / :418-422  least / most, exactly as in count *)
            let least := Z.max 0 (2 * left - syms) in
            let most :=
              (left * 2^(mx - len) - syms) / (2^(mx - len) - 1) in
            (* :424-430  occupy least table spaces *)
            let '(use1, mem1, rem1) :=
              drain (Z.to_nat least + 2)%nat subsz least mem rem in
            let rem2 := rem1 - use1 in
            (* :433-442  the use loop; per-iteration state (mem, rem):
                 recursive call gets (mem + (rem ? subsz : 0), rem << 1);
                 afterwards: if (rem == 0) { rem = subsz; mem += subsz; }
                             rem--;                                      *)
            let loop :=
              fix loop (n : nat) (use mem rem : Z) (st : Z * PM.t unit)
                : Z * PM.t unit :=
                match n with
                | O => st
                | S n' =>
                    let st1 :=
                      examineF f mx rt (syms - use) (2 * (left - use))
                               (len + 1)
                               (mem + (if rem =? 0 then 0 else subsz))
                               (2 * rem) st in
                    let '(mem', rem') :=
                      if rem =? 0 then (mem + subsz, subsz - 1)
                      else (mem, rem - 1) in
                    loop n' (use + 1) mem' rem' st1
                end in
            loop (Z.to_nat (most - least + 1)) least mem1 rem2
                 (large, done1)
        end
  end.

(* ==========================================================================
   enough (enough.c:448-483): seed [large] with the base table 1<<root,
   then, if root < max, walk every reachable (root+1)-bit juncture.
   The reachability test reads the count memo: num[map(n,left,root+1)]
   nonzero (:466-468) for the deep entries, and num[map(n,left,root)]
   nonzero with n <= left<<1 (:470-474) for root-bit codes completing at
   root+1 (the C spells the latter index as [index - 1]; with the D3 keys
   that is key3 n left root -- same cell, root >= 1 keeps it in range).
   ========================================================================== *)

Definition memo_nonzero (numm : PM.t Z) (k : positive) : bool :=
  match PM.find k numm with
  | Some v => negb (v =? 0)
  | None => false
  end.

Definition enough_phase (mx rt syms : Z) (numm : PM.t Z) : Z :=
  let base := 2^rt in
  (* :461  if (root < max) *)
  if rt <? mx then
    let efuel := (Z.to_nat mx + 1)%nat in
    (* :462-463  for (n = 3..syms) for (left = 2; left < n; left += 2) *)
    let outer :=
      fix outer (i : nat) (n : Z) (st : Z * PM.t unit) : Z * PM.t unit :=
        match i with
        | O => st
        | S i' =>
            let inner :=
              fix inner (j : nat) (left : Z) (st : Z * PM.t unit)
                : Z * PM.t unit :=
                match j with
                | O => st
                | S j' =>
                    (* :466-468 *)
                    let st1 :=
                      if (rt + 1 <? mx)
                         && memo_nonzero numm (key3 n left (rt + 1))
                      then examineF efuel mx rt n left (rt + 1)
                                    (2^rt) 0 st
                      else st in
                    (* :470-474 *)
                    let st2 :=
                      if memo_nonzero numm (key3 n left rt)
                         && (n <=? 2 * left)
                      then examineF efuel mx rt
                                    (2 * (n - left)) (2 * (n - left))
                                    (rt + 1) (2^rt) 0 st1
                      else st1 in
                    inner j' (left + 2) st2
                end in
            let st' := inner (Z.to_nat ((n - 1) / 2)) 2 st in
            outer i' (n + 1) st'
        end in
    fst (outer (Z.to_nat (syms - 2)) 3 (base, PM.empty unit))
  else base.

(* ==========================================================================
   enough_run (main, enough.c:498-597): argument munging, refusals, the
   count phase (n = 2..syms sharing one memo), then the table phase.

   Return value mirrors the OBSERVABLE stdout of one C invocation:
     None                    -- hard refusal, no output (exit 1)
     Some (total, None)      -- count line printed, then the
                                "cannot handle minimum code lengths > root"
                                branch (:590-592; note the C still exits 0)
     Some (total, Some large)-- both lines printed
   ========================================================================== *)

Definition enough_run (syms root max : Z) : option (Z * option Z) :=
  (* :517-521  invalid arguments *)
  if (syms <? 2) || (root <? 1) || (max <? 1) then None
  else
    (* :524-525  if not restricting, longest is syms - 1 *)
    let mx := Z.min max (syms - 1) in
    (* :531-537  internal-type aborts NOT mirrored (D1) *)
    (* :540-544  impossible code requests *)
    if syms - 1 >? 2^mx - 1 then None
    else
      (* Gallina domain guard (D2) *)
      if (mx >? 32) || (root >? 32) || (syms >? 2^20) then None
      else
        (* :566-572  count codes for n = 2..syms, one shared memo *)
        let cfuel := (Z.to_nat mx + 1)%nat in
        let cnt :=
          fix cnt (i : nat) (n sum : Z) (memo : PM.t Z) : Z * PM.t Z :=
            match i with
            | O => (sum, memo)
            | S i' =>
                let '(got, memo') := countF cfuel mx n 2 1 memo in
                cnt i' (n + 1) (sum + got) memo'
            end in
        let '(total, numm) := cnt (Z.to_nat (syms - 1)) 2 0 (PM.empty Z) in
        (* :586-587  reduce root to max length *)
        let rt := Z.min root mx in
        (* :588-592  the "cannot handle" refusal *)
        if syms <? 2^(rt + 1)
        then Some (total, Some (enough_phase mx rt syms numm))
        else Some (total, None).

(* The bound alone, when defined. *)
Definition enough_bound (syms root max : Z) : option Z :=
  match enough_run syms root max with
  | Some (_, Some large) => Some large
  | _ => None
  end.

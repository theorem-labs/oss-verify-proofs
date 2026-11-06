(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool String.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VStepMem VCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Inductive contract : Type :=
  C_memcpy | C_memset | C_memcmp | C_bcmp | C_strlen | C_strcmp | C_strncpy | C_tolower | C_strtoul.

(* [comment removed for export] *)
Definition contract_K (c : contract) : Z :=
  match c with C_strncpy => 32 | C_strtoul => 480 | _ => 0 end.

(* [comment removed for export] *)
Record cimg := mkCI {
  ci_errno : Z ;          (* [comment removed for export] *)
  ci_tp : Z ;             (* [comment removed for export] *)
  ci_sentinel : Z         (* [comment removed for export] *)
}.

Inductive cres : Type :=
| CROk (A' : vstate) (a0 : absval)
| CRDead
| CRFail (msg : string).

Definition A0r : Z := 10. Definition A1r : Z := 11. Definition A2r : Z := 12.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lo_of (A : vstate) (e : lin) : option Z := fst (bnd A e).
Definition hi_of (A : vstate) (e : lin) : option Z := snd (bnd A e).
Definition dead_lin (A : vstate) (e : lin) : bool := itv_empty (bnd A e).

Inductive rres : Type :=
| RR_stack (off : lin) (lo hi : Z)     (* [comment removed for export] *)
| RR_data (off : lin)
| RR_img (lo hi : Z)
| RR_dead
| RR_fail (msg : string).

Definition is_sp_rel (e : lin) : bool := Z.eqb (lcoef e SP0) 1 && Z.eqb (lcoef e DATA) 0.
Definition is_data_rel (e : lin) : bool := Z.eqb (lcoef e DATA) 1 && Z.eqb (lcoef e SP0) 0.

(* [comment removed for export] *)
Definition stack_range (P : vparams) (A : vstate) (base n : lin) (store : bool) : rres :=
  if negb (is_sp_rel base) then RR_fail "range: base not stack-relative" else
  let off := lsub base (lsym SP0) in
  let fin := ladd off n in
  if dead_lin A off || dead_lin A fin then RR_dead else
  match lo_of A off, hi_of A fin with
  | Some lo, Some hi =>
      if Z.ltb lo (- vp_frame P) then RR_fail "range: start below the stack window"
      else if Z.ltb 0 hi then RR_fail "range: end above sp0"
      else if store && negb (in_ranges (vp_wstack P) lo (hi - lo)) then RR_fail "range: store range outside the unit write set"
      else RR_stack off lo hi
  | _, _ => RR_fail "range: unbounded stack range"
  end.

Definition readable_range (P : vparams) (A : vstate) (base n : lin) : rres :=
  if is_sp_rel base then stack_range P A base n false
  else if is_data_rel base then
    let off := lsub base (lsym DATA) in
    if dead_lin A off then RR_dead else
    match lo_of A off with
    | Some lo =>
        if Z.ltb lo 0 then RR_fail "range: DATA range with negative start" else
        let e := lsub (ladd off n) (lsym SIZE) in
        match hi_of A e with
        | Some hi => if Z.ltb 0 hi then RR_fail "range: DATA range end not provably <= SIZE" else RR_data off
        | None => RR_fail "range: DATA range end not provably <= SIZE"
        end
    | None => RR_fail "range: DATA range with unbounded start"
    end
  else if negb (Z.eqb (lcoef base SP0) 0 && Z.eqb (lcoef base DATA) 0) then RR_fail "range: mixed base"
  else
    match lo_of A base, hi_of A (ladd base n) with
    | Some lo, Some hi =>
        if in_ranges (vp_segs P) lo (hi - lo) then RR_img lo hi
        else RR_fail "range: absolute range not inside a readable image range"
    | _, _ => RR_fail "range: unbounded absolute range"
    end.

(* [comment removed for export] *)
Inductive nres : Type := NR_ok (lo hi : Z) | NR_dead | NR_fail (msg : string).
Definition nonneg_len (A : vstate) (n : absval) (maxlen : Z) : nres :=
  match n with
  | None => NR_fail "length Top"
  | Some e =>
      if dead_lin A e then NR_dead else
      match bnd A e with
      | (Some lo, Some hi) => if Z.ltb lo 0 || Z.ltb maxlen hi then NR_fail "length range not within [0,maxlen]" else NR_ok lo hi
      | _ => NR_fail "length unbounded"
      end
  end.

Definition MAXLEN : Z := 2 ^ 40.

(* [comment removed for export] *)
Definition disjoint_ranges (A : vstate) (a b n : lin) : bool :=
  qle A (lsub (ladd a n) b) 0 || qle A (lsub (ladd b n) a) 0.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint rom_cstr_len (rom : pmap Z) (a : Z) (fuel : nat) (k : Z) : option Z :=
  match fuel with
  | O => None
  | S f => match (if Z.ltb 0 a then pm_get (Z.to_pos a) rom else None) with
           | Some b => if Z.eqb b 0 then Some k else rom_cstr_len rom (a + 1) f (k + 1)
           | None => None
           end
  end.

Definition CSTR_FUEL : nat := 4096%nat.

Definition rodata_cstr_len (P : vparams) (p : absval) : option Z :=
  match p with
  | Some e => if lin_is_const e then
                (let a := lc e in
                 if in_ranges (vp_pristine P) a 1 then rom_cstr_len (vp_rom P) a CSTR_FUEL 0 else None)
              else None
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint min_opt (l : list Z) : option Z :=
  match l with
  | [] => None
  | x :: t => match min_opt t with Some m => Some (Z.min x m) | None => Some x end
  end.

(* [comment removed for export] *)
Fixpoint const_zero_byte (o : Z) (val : Z) (i : nat) (sz : nat) (phi : Z) : option Z :=
  match sz with
  | O => None
  | S sz' =>
      if Z.leb phi (o + Z.of_nat i) && Z.eqb (Z.land (Z.shiftr val (8 * Z.of_nat i)) 255) 0 then Some (o + Z.of_nat i)
      else const_zero_byte o val (S i) sz' phi
  end.

Definition slot_zero_bytes (slots : cellmap) (phi : Z) : list Z :=
  flat_map (fun oc : Z * cell =>
              match oc with
              | (o, (sz, Some v)) =>
                  if lin_is_const v && Z.leb phi (o + sz - 1) then
                    match const_zero_byte o (Z.land (lc v) (2 ^ (8 * sz) - 1)) 0 (Z.to_nat sz) phi with
                    | Some z => [z] | None => [] end
                  else []
              | _ => []
              end) slots.

(* [comment removed for export] *)
Definition find_nul_bound (A : vstate) (phi : Z) : option Z :=
  let facts := List.filter (fun f : Z * Z => Z.leb phi (fst f)) (vs_nul A) in
  let best := min_opt (map snd facts) in
  let zs := slot_zero_bytes (vs_slots A) phi in
  match best, min_opt zs with
  | Some b, Some z => Some (Z.min b z)
  | Some b, None => Some b
  | None, Some z => Some z
  | None, None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition getA (A : vstate) (r : Z) : absval := get_reg A r.

Definition lin_of (v : absval) : lin := match v with Some e => e | None => lzero end.

Definition c_memcpy (P : vparams) (A : vstate) : cres :=
  let d := getA A A0r in let s := getA A A1r in let n := getA A A2r in
  match nonneg_len A n MAXLEN with
  | NR_dead => CRDead
  | NR_fail m => CRFail ("memcpy n: " ++ m)
  | NR_ok _ _ =>
  match d, s with
  | Some de, Some se =>
      let ne := lin_of n in
      match stack_range P A de ne true with
      | RR_dead => CRDead
      | RR_fail m => CRFail ("memcpy dst: " ++ m)
      | RR_stack _ lo hi =>
          match readable_range P A se ne with
          | RR_dead => CRDead
          | RR_fail m => CRFail ("memcpy src: " ++ m)
          | _ =>
              (* [comment removed for export] *)
              let A1 := set_slots A (cm_kill (vs_slots A) lo hi) in
              let A2 := kill_nul A1 lo (hi - 1) None in
              CROk A2 d
          end
      | _ => CRFail "memcpy dst: unexpected region"
      end
  | None, _ => CRFail "memcpy: dst Top"
  | _, None => CRFail "memcpy: src Top"
  end end.

(* [comment removed for export] *)
Fixpoint zero_slots8 (sl : cellmap) (o : Z) (k : nat) : cellmap :=
  match k with O => sl | S k' => zero_slots8 (cm_set sl o (8, Some (lconst 0))) (o + 8) k' end.
Fixpoint zero_slots1 (sl : cellmap) (o : Z) (k : nat) : cellmap :=
  match k with O => sl | S k' => zero_slots1 (cm_set sl o (1, Some (lconst 0))) (o + 1) k' end.

Definition MEMSET_TRACK_MAX : Z := 256.

Definition c_memset (P : vparams) (A : vstate) : cres :=
  let d := getA A A0r in let c := getA A A1r in let n := getA A A2r in
  match nonneg_len A n MAXLEN with
  | NR_dead => CRDead
  | NR_fail m => CRFail ("memset n: " ++ m)
  | NR_ok _ _ =>
  match d with
  | None => CRFail "memset: dst Top"
  | Some de =>
      let ne := lin_of n in
      match stack_range P A de ne true with
      | RR_dead => CRDead
      | RR_fail m => CRFail ("memset dst: " ++ m)
      | RR_stack off lo hi =>
          if negb (is_zero_val A c) then CRFail "memset: fill value not provably 0 (only memset(d,0,n) is proved)" else
          let A1 := set_slots A (cm_kill (vs_slots A) lo hi) in
          (* [comment removed for export] *)
          if lin_is_const off && lin_is_const ne && Z.leb (lc ne) MEMSET_TRACK_MAX then
            let o := lc off in let k := lc ne in
            let q := Z.to_nat (k / 8) in let r := Z.to_nat (k mod 8) in
            let sl := zero_slots1 (zero_slots8 (vs_slots A1) o q) (o + 8 * Z.of_nat q) r in
            let A2 := set_slots A1 sl in
            let A3 := if Z.ltb 0 k then add_nul (add_nul A2 o o) (o + k - 1) (o + k - 1) else A2 in
            CROk A3 d
          else CROk A1 d
      | _ => CRFail "memset dst: unexpected region"
      end
  end end.

Definition c_memcmp (P : vparams) (A : vstate) : cres :=
  let a := getA A A0r in let b := getA A A1r in let n := getA A A2r in
  match nonneg_len A n MAXLEN with
  | NR_dead => CRDead
  | NR_fail m => CRFail ("memcmp n: " ++ m)
  | NR_ok _ _ =>
  match a, b with
  | Some ae, Some be =>
      let ne := lin_of n in
      match readable_range P A ae ne with
      | RR_dead => CRDead
      | RR_fail m => CRFail ("memcmp a: " ++ m)
      | _ =>
          match readable_range P A be ne with
          | RR_dead => CRDead
          | RR_fail m => CRFail ("memcmp b: " ++ m)
          | _ => let '(v, A1) := afresh A (Some (-255), Some 255) in CROk A1 v
          end
      end
  | _, _ => CRFail "memcmp: pointer Top"
  end end.

(* [comment removed for export] *)
Definition c_strlen (P : vparams) (A : vstate) : cres :=
  let p := getA A A0r in
  match rodata_cstr_len P p with
  | Some k =>
      (* [comment removed for export] *)
      match p with
      | Some e => if in_ranges (vp_segs P) (lc e) (k + 8) then CROk A (Some (lconst k))
                  else CRFail "strlen: rodata string tail not readable"
      | None => CRFail "strlen: impossible"
      end
  | None =>
  match p with
  | None => CRFail "strlen: pointer Top"
  | Some e =>
      if negb (is_sp_rel e) then CRFail "strlen: pointer neither rodata const nor stack" else
      let off := lsub e (lsym SP0) in
      if dead_lin A off then CRDead else
      match bnd A off with
      | (Some plo, Some phi) =>
          match find_nul_bound A phi with
          | None => CRFail "strlen: no known NUL at/after the string"
          | Some H =>
              if Z.ltb 0 (H + 8) then CRFail "strlen: read range may reach sp0 (NUL bound + 8 > 0)"
              else if Z.ltb plo (- vp_frame P) then CRFail "strlen: string start below the stack window"
              else
                let '(s, A1) := fresh_sym A in
                let A2 := asetbox A1 s (Some 0, Some (H - plo)) in
                if lin_is_const off then
                  (* [comment removed for export] *)
                  CROk A2 (Some (lsym s))
                else
                  match aassume A2 (laddc (ladd (lsym s) off) (- H)) with     (* [comment removed for export] *)
                  | (true, A3) => CROk A3 (Some (lsym s))
                  | (false, _) => CRDead
                  end
          end
      | _ => CRFail "strlen: unbounded stack pointer"
      end
  end end.

(* [comment removed for export] *)
Definition c_strcmp (P : vparams) (A : vstate) : cres :=
  let a := getA A A0r in let b := getA A A1r in
  match rodata_cstr_len P b with
  | None => CRFail "strcmp: second argument is not a rodata constant string"
  | Some kb =>
      match a, b with
      | Some ae, Some be =>
          if negb (in_ranges (vp_segs P) (lc be) (kb + 1)) then CRFail "strcmp: rodata string not readable" else
          match readable_range P A ae (lconst (kb + 1)) with
          | RR_dead => CRDead
          | RR_fail m => CRFail ("strcmp arg: " ++ m)
          | _ => let '(v, A1) := afresh A (Some (-255), Some 255) in CROk A1 v
          end
      | _, _ => CRFail "strcmp: pointer Top"
      end
  end.

Definition c_strncpy (P : vparams) (A : vstate) (spoff : Z) : cres :=
  let d := getA A A0r in let s := getA A A1r in let n := getA A A2r in
  match nonneg_len A n MAXLEN with
  | NR_dead => CRDead
  | NR_fail m => CRFail ("strncpy n: " ++ m)
  | NR_ok nlo nhi =>
  match d, s with
  | Some de, Some se =>
      let ne := lin_of n in
      match stack_range P A de ne true with
      | RR_dead => CRDead
      | RR_fail m => CRFail ("strncpy dst: " ++ m)
      | RR_stack doff dlo dhi =>
          (* [comment removed for export] *)
          if Z.ltb dlo spoff then CRFail "strncpy: destination not above sp" else
          let src_chk :=
            match rodata_cstr_len P s with
            | Some k =>
                let ln := Z.min (k + 8) nhi in
                if in_ranges (vp_segs P) (lc se) ln then None else Some "strncpy: rodata source not readable"
            | None =>
                match readable_range P A se ne with
                | RR_dead => Some "dead"
                | RR_fail m => Some ("strncpy src: " ++ m)
                | RR_stack soff slo shi =>
                    if negb (disjoint_ranges A de se ne) then Some "strncpy: stack source not provably disjoint from destination"
                    else if Z.ltb slo spoff then Some "strncpy: stack source not above sp"
                    else None
                | RR_data _ => Some "strncpy: DATA source unsupported (not provably disjoint from the stack)"
                | RR_img _ _ => None
                end
            end in
          match src_chk with
          | Some m => if String.eqb m "dead" then CRDead else CRFail m
          | None =>
              let A1 := set_slots A (cm_kill (vs_slots A) dlo dhi) in
              let A2 := kill_nul A1 dlo (dhi - 1) None in
              CROk A2 d
          end
      | _ => CRFail "strncpy dst: unexpected region"
      end
  | _, _ => CRFail "strncpy: pointer Top"
  end end.

Definition c_tolower (P : vparams) (A : vstate) : cres :=
  let c := getA A A0r in
  match c with
  | None => CRFail "tolower: argument Top"
  | Some e =>
      if dead_lin A e then CRDead else
      match bnd A e with
      | (Some lo, Some hi) =>
          if Z.ltb lo 0 || Z.ltb 255 hi then CRFail "tolower: argument not provably a byte" else
          if lin_is_const e then
            (let v := lc e in CROk A (Some (lconst (if Z.leb 65 v && Z.leb v 90 then v + 32 else v))))
          else
            let rlo := if Z.leb 65 lo then Z.min lo 97 else lo in
            let rhi := if Z.leb 65 hi then Z.max hi (Z.min (hi + 32) 122) else hi in
            let '(v, A1) := afresh A (Some rlo, Some rhi) in CROk A1 v
      | _ => CRFail "tolower: argument unbounded"
      end
  end.

(* [comment removed for export] *)
Definition strtoul_cont (b : Z) : bool :=
  (Z.leb 9 b && Z.leb b 13) || Z.eqb b 32 || Z.eqb b 43 || Z.eqb b 45 || (Z.leb 48 b && Z.leb b 57).

Fixpoint const_stop_byte (o : Z) (val : Z) (i : nat) (sz : nat) (phi : Z) : option Z :=
  match sz with
  | O => None
  | S sz' =>
      if Z.leb phi (o + Z.of_nat i) && negb (strtoul_cont (Z.land (Z.shiftr val (8 * Z.of_nat i)) 255)) then Some (o + Z.of_nat i)
      else const_stop_byte o val (S i) sz' phi
  end.

Definition slot_stop_bytes (slots : cellmap) (phi : Z) : list Z :=
  flat_map (fun oc : Z * cell =>
              match oc with
              | (o, (sz, Some v)) =>
                  if lin_is_const v && Z.leb phi (o + sz - 1) then
                    match const_stop_byte o (Z.land (lc v) (2 ^ (8 * sz) - 1)) 0 (Z.to_nat sz) phi with
                    | Some z => [z] | None => [] end
                  else []
              | _ => []
              end) slots.

Definition STRTOUL_FRAME : Z := 368.

Definition c_strtoul (P : vparams) (CI : cimg) (A : vstate) (spoff : Z) : cres :=
  let p := getA A A0r in let endp := getA A A1r in let base := getA A A2r in
  match endp, base with
  | Some ee, Some be =>
      if negb (lin_is_const ee && Z.eqb (lc ee) 0) then CRFail "strtoul: endptr not NULL" else
      if negb (lin_is_const be && Z.eqb (lc be) 10) then CRFail "strtoul: base not 10" else
      match p with
      | None => CRFail "strtoul: pointer Top"
      | Some pe =>
          if negb (is_sp_rel pe) then CRFail "strtoul: pointer not stack-relative" else
          let off := lsub pe (lsym SP0) in
          if dead_lin A off then CRDead else
          match bnd A off with
          | (Some plo, Some phi) =>
              let stops := (slot_stop_bytes (vs_slots A) phi
                            ++ map fst (List.filter (fun f : Z * Z => Z.leb phi (fst f) && Z.eqb (fst f) (snd f)) (vs_nul A)))%list in
              match min_opt stops with
              | None => CRFail "strtoul: no known stopper byte at/after the string"
              | Some stop =>
                  if Z.ltb 0 (stop + 1) then CRFail "strtoul: scan may reach sp0" else
                  if Z.ltb plo spoff then CRFail "strtoul: string not above sp" else
                  if Z.ltb (spoff - STRTOUL_FRAME) (- vp_frame P) then CRFail "strtoul: callee frame below the stack window" else
                  if negb (in_cells (vp_wcells P) (ci_errno CI) 4) then CRFail "strtoul: errno not in the unit's writable cells" else
                  if negb (match getA A 4 with Some e => lin_eqb e (lconst (ci_tp CI)) | None => false end) then CRFail "strtoul: tp is not the thread-pointer constant" else
                  (* [comment removed for export] *)
                  let A1 := set_globs A (cm_kill (vs_globs A) (ci_errno CI) (ci_errno CI + 4)) in
                  let '(v, A2) := afresh A1 (Some 0, Some (2 ^ 64 - 1)) in
                  CROk A2 v
              end
          | _ => CRFail "strtoul: unbounded pointer"
          end
      end
  | _, _ => CRFail "strtoul: endptr/base Top"
  end.

Definition contract_apply (P : vparams) (CI : cimg) (c : contract) (A : vstate) (spoff : Z) : cres :=
  match c with
  | C_memcpy => c_memcpy P A
  | C_memset => c_memset P A
  | C_memcmp | C_bcmp => c_memcmp P A
  | C_strlen => c_strlen P A
  | C_strcmp => c_strcmp P A
  | C_strncpy => c_strncpy P A spoff
  | C_tolower => c_tolower P A
  | C_strtoul => c_strtoul P CI A spoff
  end.

(* [comment removed for export] *)
Definition CALLER_SAVED : list Z := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

Fixpoint set_tops (A : vstate) (l : list Z) : vstate :=
  match l with [] => A | r :: t => set_tops (set_reg A r None) t end.

(* [comment removed for export] *)
Definition contract_frame (c : contract) (A : vstate) (spoff : Z) (a0 : absval) : vstate :=
  let K := contract_K c in
  let A1 := if Z.eqb K 0 then A
            else kill_nul (set_slots A (cm_kill (vs_slots A) (spoff - K) spoff)) (spoff - K) (spoff - 1) None in
  let A2 := set_tops A1 CALLER_SAVED in
  set_reg A2 A0r a0.

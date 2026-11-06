(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Export LiaTuning.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Inductive brk_phase : Type :=
| BPUntried                 (* [comment removed for export] *)
| BPQueried (cur : Z)       (* [comment removed for export] *)
| BPGuard (cur : Z)         (* [comment removed for export] *)
| BPLive                    (* [comment removed for export] *)
| BPDead.                   (* [comment removed for export] *)

Record mled : Type := mkLed {
  ld_resv : list (Z * Z);          (* [comment removed for export] *)
  ld_groups : list (Z * Z);        (* [comment removed for export] *)
  ld_metas : list (Z * Z * Z);     (* [comment removed for export] *)
  ld_brkreg : option (Z * Z);      (* [comment removed for export] *)
  ld_brk : brk_phase;
  ld_live : list cptr              (* [comment removed for export] *)
}.

Definition led_init (resv : list (Z * Z)) : mled := mkLed resv [] [] None BPUntried [].
Definition set_groups (v : list (Z * Z)) (L : mled) := mkLed (ld_resv L) v (ld_metas L) (ld_brkreg L) (ld_brk L) (ld_live L).
Definition set_metas (v : list (Z * Z * Z)) (L : mled) := mkLed (ld_resv L) (ld_groups L) v (ld_brkreg L) (ld_brk L) (ld_live L).
Definition set_brkreg (v : option (Z * Z)) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) v (ld_brk L) (ld_live L).
Definition set_brkph (v : brk_phase) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) v (ld_live L).
Definition set_live (v : list cptr) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) (ld_brk L) v.

(* [comment removed for export] *)
Definition lranges (L : mled) : list (Z * Z) :=
  ld_resv L
  ++ map (fun g => (fst g, round_up_pg (snd g))) (ld_groups L)
  ++ map (fun m => (fst (fst m), round_up_pg (snd (fst m)))) (ld_metas L)
  ++ match ld_brkreg L with Some (b, l) => [(b + PGSZ, round_up_pg l - PGSZ)] | None => [] end.

(* [comment removed for export] *)
Definition lbrk_pages_ok (L : mled) (lo len : Z) : bool :=
  (0 <? lo) && (lo + len <=? alloc_ceiling) && ranges_free (lranges L) lo len.

Definition MAPF : Z := MAP_PRIVATE + MAP_ANON.
Definition MAPFX : Z := MAP_PRIVATE + MAP_ANON + MAP_FIXED.
Definition LEN_MAX : Z := 2^63.   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint g_remove (a : Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => []
  | y :: l' => if fst y =? a then l' else y :: g_remove a l'
  end.
Definition bump_meta (a : Z) (m : Z * Z * Z) : Z * Z * Z :=
  let '(b, l, k) := m in if b + (1 + k) * PGSZ =? a then (b, l, k + 1) else m.
Fixpoint ap_remove (c : aptr) (l : list aptr) : list aptr :=
  match l with
  | [] => []
  | y :: l' => if aptr_eqb y c then l' else y :: ap_remove c l'
  end.

(* [comment removed for export] *)
Definition brk_quiet (L : mled) : Prop :=
  match ld_brk L with BPQueried _ | BPGuard _ => False | _ => True end.

Definition event_pre (L : mled) (e : ev) : Prop :=
  match e with
  | EBrk req =>
      (req = 0 /\ ld_brk L = BPUntried)
      \/ (exists cur, ld_brk L = BPQueried cur /\ req = round_up_pg cur + 2 * PGSZ)
      \/ (exists b l, ld_brk L = BPLive /\ ld_brkreg L = Some (b, l) /\ req = b + l + PGSZ)
  | EMmap a len prot flags =>
      (brk_quiet L /\ a = 0 /\ flags = MAPF /\ (prot = PROT_NONE \/ prot = PROT_RW) /\ 0 < len < LEN_MAX)
      \/ (exists cur, ld_brk L = BPGuard cur /\ a = round_up_pg cur /\ len = PGSZ /\ prot = PROT_NONE /\ flags = MAPFX)
  | EMunmap a len => brk_quiet L /\ exists l, In (a, l) (ld_groups L) /\ (len = l \/ len = round_up_pg l)
        (* [comment removed for export] *)
  | EMprotect a len prot =>
      brk_quiet L /\ len = PGSZ /\ prot = PROT_RW /\
      exists b l k, In (b, l, k) (ld_metas L) /\ a = b + (1 + k) * PGSZ /\ (2 + k) * PGSZ <= round_up_pg l
  | EPeek _ _ _ => False
  | EUndef _ => False
  end.

Definition answer_ok (L : mled) (e : ev) (z : Z) : bool :=
  match e with
  | EBrk req =>
      if req =? 0 then brk0_answer_ok z
      else match ld_brk L with
           | BPQueried cur => brk_answer_ok cur req z && (negb (z =? req) || lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ))
           | _ => match ld_brkreg L with
                  | Some (b, l) => brk_answer_ok (b + l) req z && (negb (z =? req) || lbrk_pages_ok L (b + l) PGSZ)
                  | None => false
                  end
           end
  | EMmap a len prot flags =>
      if Z.land flags MAP_FIXED =? 0 then mmap_answer_ok (lranges L) len z
      else mmap_fixed_answer_ok a z
  | EMunmap _ _ => munmap_answer_ok z
  | EMprotect _ _ _ => mprotect_answer_ok z
  | _ => false
  end.

Definition event_post (L : mled) (e : ev) (z : Z) : mled :=
  match e with
  | EBrk req =>
      if req =? 0 then set_brkph (BPQueried z) L
      else if z =? req then
             match ld_brk L with
             | BPQueried cur => set_brkph (BPGuard cur) L
             | _ => match ld_brkreg L with
                    | Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L
                    | None => L
                    end
             end
           else set_brkph BPDead L
  | EMmap a len prot flags =>
      if Z.land flags MAP_FIXED =? 0 then
        if is_err z then L
        else if prot =? PROT_NONE then set_metas ((z, len, 0) :: ld_metas L) L
        else set_groups ((z, len) :: ld_groups L) L
      else set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)
  | EMunmap a len => set_groups (g_remove a (ld_groups L)) L
  | EMprotect a len prot =>
      if (z =? 0) || (z =? TWO64 - ENOSYS) then set_metas (map (bump_meta a) (ld_metas L)) L else L
  | _ => L
  end.

(* [comment removed for export] *)
Fixpoint ctree_ok {R} (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
  match t with
  | SRet r => Post L r
  | SVis e k => event_pre L e /\ forall z, answer_ok L e z = true -> ctree_ok (event_post L e z) (k z) Post
  end.

(* [comment removed for export] *)
Inductive cpath {R} : mled -> stree ev Z R -> mled -> R -> Prop :=
| cpath_ret L r : cpath L (SRet r) L r
| cpath_vis L e k z L' r :
    answer_ok L e z = true -> cpath (event_post L e z) (k z) L' r -> cpath L (SVis e k) L' r.

(* [comment removed for export] *)
Inductive creach : mstate -> mled -> Prop :=
| creach_init resv : creach (strip (minit rc_secret resv)) (led_init resv)   (* [comment removed for export] *)
| creach_malloc cs L n L' cs' r :
    creach cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', r) ->
    creach cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end)
| creach_free cs L c L' cs' :
    creach cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
    creach cs' (set_live (ap_remove c (ld_live L')) L').

(* [comment removed for export] *)

End RC__1.

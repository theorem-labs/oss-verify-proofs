(* omx-clap-core/fuzz_preset: S1 of the plain coupling (the internal file COUPLING-A-MEASURE.md section 5).

   req_at sm inp pi : list Z is the multiset of the chunk requests live in the heap at position pi of ONE harness run
   (fuzz/fuzz_preset.c LLVMFuzzerTestOneInput :679-707) on the bytes the driver hands it for input inp. Both builds
   share it: the ASan heap ghost H (lib/A/Prog/ALedger.v:28-36, a ledger entry (a, k) is the chunk (a - 16, k + 16))
   and the plain chunks (lib/Prog/Ledger.v:35-44) hold the same requests, because every pj_parse contract states
   jr_run jr_strtod (zb tb) (lib/A/Prog/pj_parse_c.v:59, lib/Prog/CF/pj_parse_c.v:51). sm is the build's
   jr_strtod (lib/A/Prog/ReaderRes.v:55, lib/Prog/ReaderRes.v:58: the same text).

   WHAT A POSITION IS. hrun sm x is the list of the run's allocator calls that change the heap, in order, as heap
   events (hev). A position (k, F) is the heap after the first k events, and, when event k is a pj_free of the requests
   L (HBulk L), after the frees of F, a sub-multiset of L (pj_free frees L one block at a time). pos_valid says k is in
   range and F is such a sub-multiset. The site ghost at an allocator call's entry is the heap of one position: the
   call's own event is not applied yet (an in-flight realloc's old block is still live).
   S3 (plain_reaches_pos) needs a plain configuration whose live requests CONTAIN req_at sm inp pi; at (k, F) the
   configuration at the entry of pj_free (position (k, [])) contains it.
   THE FREE ORDER. L lists the blocks in the order pj_free (src/preset_file.c:334-350) frees them, post-order: for each
   slot i the subtree of kids[i], then keys[i]; then kids, keys, str. fo t is that list for a tree read back from the
   writer's text (or a pj_set result), pj_frees ok x for the tree (complete, or partial on a refusal) the reader built
   from x. hstep reads L only up to Permutation (rmall_drop); the free history of the run (PresetRun.hfrees) reads
   it in order.

   WHICH CALLS ARE IN. Every call of the run that changes the heap, in three classes:
   - the reader (fuzz/alloc.h forces malloc/realloc/strdup/free of src/preset_file.c to fuzz_*, and fuzz_malloc asks
     malloc for HEAD + n, fuzz/alloc.c:63): its events are jr_run's trace (PjGrammar ev) at request n + 16; a refused
     pj_parse frees what it holds (src/preset_file.c:296-309, pj_free(out)); pj_free (:334-350) of a tree frees what
     the tree holds; pj_string and pj_set (:373-411, the rewrite) through set_trace's shape (lib/A/Prog/pj_set_c.v:16-19);
   - the writer, pj_write (:558-573, put :454-477): its buffer's reallocs are WriterSpec.grow_calls over the writer's
     pieces (WriterValue.wdpieces), at request cap + 16, and one with its k-th call failing (check_reject_clean_starved);
  - the harness's own, straight to the C library (request as asked): padded()'s copies (#102 fuzz_preset.c:510-521,
    malloc (n + FUZZ_PAD); before #102 fuzz_copy, fuzz/fuzz.h:21-37, the same request), expected()'s scratch
    (#102 :360-375, n + 1) and rendered()'s buffer (tx_put #102 :386-406, cap = (n + k + 1) * 2).
  hrun is the run's list when every allocation is granted (in #102 the same events as before #102). A reading of
  check_no_overread that runs out ends the call early (PresetRun.call_evs, ranout); a NULL elsewhere ends the call
  without an abort in #102. The round-trip parses read the writer's text, wdoc t p: by
   PjRoundTrip.G9_trace (lib/Spec/PjRoundTrip.v:923-924) their trace is ttrace t when pj_wf t.

   THE DRIVER. slot_input inp is the harness's input: the file argv[1] names, past its header (YO05/YO06 driver,
   SPECX_args): payload data. The harness is called calls data times on it; every call frees all it took, so the same
   positions serve every call. The driver's own blocks (its read buffer and payload copy) are not in req_at.

   Nothing here is a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO05 YO06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ heap events and the live multiset *)

Inductive hev : Type :=
| HMal (n : Z)          (* malloc n, or realloc (NULL, n) *)
| HRe (m n : Z)         (* realloc of the live request m to n *)
| HFr (n : Z)           (* free of the live request n *)
| HBulk (L : list Z).   (* pj_free of a tree holding the requests L *)

Fixpoint rm1 (z : Z) (s : list Z) : list Z :=
  match s with
  | [] => []
  | y :: r => if y =? z then r else y :: rm1 z r
  end.

Definition rmall (F s : list Z) : list Z := fold_left (fun acc z => rm1 z acc) F s.

Definition hstep (s : list Z) (e : hev) : list Z :=
  match e with
  | HMal n => n :: s
  | HRe m n => n :: rm1 m s
  | HFr n => rm1 n s
  | HBulk L => rmall L s
  end.

Definition hlive_from (s : list Z) (es : list hev) : list Z := fold_left hstep es s.

Definition hlive (es : list hev) : list Z := hlive_from [] es.

(* ================================================================ the reader *)

(* fuzz/alloc.c:28 *)
Definition HEAD : Z := 16.
(* fuzz/fuzz.h:16 *)
Definition FUZZ_PAD : Z := 16.
(* src/preset_file.h:61 *)
Definition MAXB : Z := 3 * 1024 * 1024.

(* One reader event as the heap sees it: request n + HEAD. A grow from capacity 0 is realloc (NULL, n), a malloc. *)
Definition rd_hev (e : ev) : list hev :=
  match e with
  | EAlloc n => [HMal (Z.of_nat n + HEAD)]
  | EGrow O n => [HMal (Z.of_nat n + HEAD)]
  | EGrow m n => [HRe (Z.of_nat m + HEAD) (Z.of_nat n + HEAD)]
  | EFail _ => []
  | EFree n => [HFr (Z.of_nat n + HEAD)]
  end.

Definition rd_hevs (tr : list ev) : list hev := flat_map rd_hev tr.

(* The requests a reader trace leaves live: the blocks of the tree it built (or of the partial tree it refuses). *)
Definition rd_blocks (tr : list ev) : list Z := hlive (rd_hevs tr).

(* ================================================================ realloc chains: the writer and rendered() *)

(* A buffer's successive capacities cs, starting from no buffer; hd is the head the allocator adds. *)
Fixpoint chain (hd old : Z) (cs : list Z) : list hev :=
  match cs with
  | [] => []
  | c :: r => (if old =? 0 then HMal (c + hd) else HRe (old + hd) (c + hd)) :: chain hd c r
  end.

(* pj_write t p, every allocation granted: the capacities of its buffer. *)
Definition wcaps (t : jv) (p : bool) : list Z := grow_calls 0 0 (piece_lens (wdpieces t p)).
Definition wcalls (t : jv) (p : bool) : nat := length (wcaps t p).
Definition w_evs (t : jv) (p : bool) : list hev := chain HEAD 0 (wcaps t p).
(* fuzz_free of the text it returns *)
Definition w_free (t : jv) (p : bool) : list hev := [HFr (last (wcaps t p) 0 + HEAD)].
(* pj_write t p with its k-th allocation (0 the first) failing: the first k reallocs, then free (o.buf) (:567-570). *)
Definition w_starved (t : jv) (p : bool) (k : nat) : list hev :=
  chain HEAD 0 (firstn k (wcaps t p)) ++
  match k with O => [] | S _ => [HFr (last (firstn k (wcaps t p)) 0 + HEAD)] end.

(* rendered (doc, pretty) (fuzz_preset.c:440-449): the length of each tx_put, in order. *)
Definition tx_ch (c : Z) : list Z :=
  if (c =? 34) || (c =? 92) then [1; 1]
  else if 32 <=? c then [1]
  else if (c =? 10) || (c =? 9) || (c =? 13) then [2]
  else [6].

Definition tx_str (s : list Z) : list Z := 1 :: flat_map tx_ch s ++ [1].

Definition tx_line (d : nat) : list Z := 1 :: repeat 2 d.

Fixpoint tx_val (p : bool) (d : nat) (t : jv) {struct t} : list Z :=
  match t with
  | JNull => [4]
  | JFalse => [5]
  | JTrue => [4]
  | JNum txt _ => [Z.of_nat (length txt)]
  | JStr s => tx_str s
  | JArr items =>
      1 ::
      (fix go (i : nat) (l : list jv) {struct l} : list Z :=
         match l with
         | [] => []
         | u :: r => (if Nat.eqb i 0 then [] else [1]) ++ (if p then tx_line (S d) else []) ++
                     tx_val p (S d) u ++ go (S i) r
         end) 0%nat items
      ++ (match items with [] => [] | _ :: _ => if p then tx_line d else [] end) ++ [1]
  | JObj ms =>
      1 ::
      (fix go (i : nat) (l : list (list Z * jv)) {struct l} : list Z :=
         match l with
         | [] => []
         | (k, u) :: r => (if Nat.eqb i 0 then [] else [1]) ++ (if p then tx_line (S d) else []) ++
                          tx_str k ++ [1] ++ (if p then [1] else []) ++ tx_val p (S d) u ++ go (S i) r
         end) 0%nat ms
      ++ (match ms with [] => [] | _ :: _ => if p then tx_line d else [] end) ++ [1]
  end.

(* tx_put's growth: when n + k + 1 > cap, cap := (n + k + 1) * 2 and realloc. *)
Fixpoint tx_caps (n cap : Z) (ls : list Z) : list Z :=
  match ls with
  | [] => []
  | k :: r =>
      if cap <? n + k + 1 then (n + k + 1) * 2 :: tx_caps (n + k) ((n + k + 1) * 2) r
      else tx_caps (n + k) cap r
  end.

Definition rcaps (t : jv) (p : bool) : list Z := tx_caps 0 0 (0 :: tx_val p 0 t ++ (if p then [1] else [])).
Definition r_evs (t : jv) (p : bool) : list hev := chain 0 0 (rcaps t p).
(* free (want) *)
Definition r_free (t : jv) (p : bool) : list hev := [HFr (last (rcaps t p) 0)].

(* ================================================================ the harness's choices *)

(* fuzz_pick (fuzz/fuzz.h:65-72), size_t arithmetic *)
Definition pick_h (x : list Z) : Z := fold_left (fun h b => (h * 33 + b) mod 2 ^ 64) x 5381.
Definition pick (x : list Z) (n : nat) : nat :=
  match n with O => O | S _ => Z.to_nat (pick_h x mod Z.of_nat n) end.

(* fuzz_alloc_fail (k): the k-th allocation from now fails (oks, lib/A/Prog/ReaderRes.v:94-95). *)
Definition okk (k : nat) : list bool := repeat true k ++ [false].

(* "modifiedAt", "2026-10-25T00:00:00Z" (fuzz_preset.c:59, :615) *)
Definition MOD_KEY : list Z := [109; 111; 100; 105; 102; 105; 101; 100; 65; 116].
Definition MOD_VAL : list Z := [50; 48; 50; 54; 45; 49; 48; 45; 50; 53; 84; 48; 48; 58; 48; 48; 58; 48; 48; 90].

Fixpoint zl_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && zl_eqb a' b'
  | _, _ => false
  end.

(* pj_get (copy, MOD_KEY): the first member of that name *)
Fixpoint mfind (ms : list (list Z * jv)) : option jv :=
  match ms with
  | [] => None
  | (k, u) :: r => if zl_eqb k MOD_KEY then Some u else mfind r
  end.

(* the capacity parse_items leaves after n items: PjRoundTrip.gcap from 0 *)
Fixpoint ncap (n : nat) : nat :=
  match n with O => O | S i => gcap i (ncap i) end.

(* the live blocks of a container of capacity cap: its kids array, and an object's keys array *)
Definition arrz (o : bool) (cap : nat) : list Z :=
  match cap with
  | O => []
  | S _ => (Z.of_nat (56 * cap) + HEAD) :: (if o then [Z.of_nat (8 * cap) + HEAD] else [])
  end.

(* pj_free (src/preset_file.c:334-350) of a tree read back from the writer's text, or of a pj_set result: the requests
   it frees, in its order (post-order: for each slot the subtree of kids[i], then keys[i]; then kids, keys). The string
   sizes are the writer's escape, as in PjRoundTrip.ttrace: exact for a parse of wdoc t p, not for any x. *)
Fixpoint fo (t : jv) : list Z :=
  match t with
  | JNum txt _ => [Z.of_nat (S (length txt)) + HEAD]
  | JStr z => [Z.of_nat (S (length (flat_map ech z))) + HEAD]
  | JArr items => concat (map fo items) ++ arrz false (ncap (length items))
  | JObj ms => concat (map (fun m => fo (snd m) ++ [Z.of_nat (S (length (flat_map ech (fst m)))) + HEAD]) ms)
               ++ arrz true (ncap (length ms))
  | _ => []
  end.

(* ================================================================ the run *)

Section Run.

Variable sm : list Z -> Z * Z.

Definition rtr (ok : list bool) (x : list Z) : list ev := snd (jr_run sm x ok).

(* ---- pj_free's order for the tree the reader builds from x: complete, or the partial tree a refusal leaves.
   pj_parse frees out on every refusal (src/preset_file.c:301-308). The partial tree is the path of open containers,
   each with its completed slots, the partial last slot of a value that failed (C :246, v->n++), and its arrays as
   they are then. jfv / jfl follow jrv / jrl (they call grow, jr_name and jrv for control flow and for ok) and give
   the blocks in pj_free's order. *)

(* a leaf's block: the buffer of a number or string the reader kept (a failed strtod keeps str, C :204-205) *)
Definition lf (tr : list ev) : list Z := match tr with [EAlloc n] => [Z.of_nat n + HEAD] | _ => [] end.

(* the arrays after a refused grow (C :42-64): kids realloc'd and keys refused leaves the new kids and the old keys *)
Definition gheld (o : bool) (cap : nat) (tg : list ev) : list Z :=
  match tg with
  | [EGrow _ k; EFail _] => (Z.of_nat k + HEAD) :: match cap with O => [] | S _ => [Z.of_nat (8 * cap) + HEAD] end
  | _ => arrz o cap
  end.

Definition jf_cont (loop : nat -> bool -> nat -> nat -> list Z -> list Z -> list bool -> list Z)
  (d : nat) (o : bool) (x : list Z) (ok : list bool) : list Z :=
  if Nat.ltb MAXD (S d) then []
  else
    let y := skip (tl x) in
    match y with
    | c :: _ => if c =? closer o then [] else loop (S d) o 0%nat 0%nat [] y ok
    | [] => loop (S d) o 0%nat 0%nat [] y ok
    end.

Fixpoint jfv (fuel d : nat) (x : list Z) (ok : list bool) {struct fuel} : list Z :=
  match fuel with
  | O => []
  | S f =>
    match skip x with
    | [] => []
    | b :: y =>
      if b =? 123 then jf_cont (jfl f) d true (b :: y) ok
      else if b =? 91 then jf_cont (jfl f) d false (b :: y) ok
      else lf (snd (fst (jrv sm (S f) d x ok)))                       (* a leaf holds at most one block *)
    end
  end
with jfl (fuel d : nat) (o : bool) (n cap : nat) (af y : list Z) (ok : list bool) {struct fuel} : list Z :=
  match fuel with
  | O => af ++ arrz o cap
  | S f =>
    match grow o n cap ok with
    | (None, tg, _) => af ++ gheld o cap tg                                        (* C :226-227 *)
    | (Some cap1, _, ok1) =>
      match jr_name o y ok1 with
      | (None, _, _) => af ++ arrz o cap1                                           (* C :231-239: key not kept *)
      | (Some (_, y1), tn, ok2) =>
        let af1 := af ++ jfv f d y1 ok2 ++ lf tn in                                 (* value, then key: C :342-344 *)
        match jrv sm f d y1 ok2 with
        | (Some (_, r), _, ok3) =>
          match skip r with
          | c :: r1 => if c =? 44 then jfl f d o (S n) cap1 af1 r1 ok3 else af1 ++ arrz o cap1
          | [] => af1 ++ arrz o cap1
          end
        | (None, _, _) => af1 ++ arrz o cap1                                        (* C :246: partial child counted *)
        end
      end
    end
  end.

(* pj_free (out) of the tree pj_parse builds from x under the grant oracle ok, in pj_free's order *)
Definition pj_frees (ok : list bool) (x : list Z) : list Z := jfv (S (2 * length x)) 0 x ok.

(* one pj_parse of x under the grant oracle ok: the reader's events, then, on a refusal, pj_free (out) *)
Definition parse_evs (x : list Z) (ok : list bool) : list hev :=
  rd_hevs (rtr ok x) ++
  match fst (jr_run sm x ok) with
  | Some _ => []
  | None => [HBulk (pj_frees ok x)]
  end.

(* the reader's trace of the writer's text of t *)
Definition rt_tr (t : jv) (p : bool) : list ev := rtr [] (wdoc t p).

(* round_trip_text (doc, pretty, copy) (:572-603), up to the free of `back`: the writer, rendered(), the parse,
   free (want), fuzz_free (text). `back` is left live. *)
Definition rt_text (t : jv) (p : bool) : list hev :=
  w_evs t p ++ r_evs t p ++ parse_evs (wdoc t p) [] ++ r_free t p ++ w_free t p.

(* round_trip_rewrite's changes to copy (:615): pj_string, then pj_set: pj_free of the old value, or grow and
   strdup (key). *)
Definition set_evs (ms : list (list Z * jv)) : list hev :=
  HMal (Z.of_nat (S (length MOD_VAL)) + HEAD) ::
  match mfind ms with
  | Some u => [HBulk (fo u)]
  | None => rd_hevs (grow_ev true (length ms) (ncap (length ms)) ++ [EAlloc (S (length MOD_KEY))])
  end.

Definition copy_set (ms : list (list Z * jv)) : jv := JObj (pj_set_model ms MOD_KEY (JStr MOD_VAL)).

(* round_trip_rewrite (:606-649) after pj_set: the writer, the parse, fuzz_free (saved), pj_free (&back). *)
Definition rw_evs (ms : list (list Z * jv)) : list hev :=
  set_evs ms ++ w_evs (copy_set ms) true ++ parse_evs (wdoc (copy_set ms) true) [] ++
  w_free (copy_set ms) true ++ [HBulk (fo (copy_set ms))].

(* check_round_trip (:651-660) *)
Definition round_trip (t : jv) : list hev :=
  rt_text t false ++ rt_text t true ++ [HBulk (fo t)] ++
  match t with
  | JObj ms => rw_evs ms ++ [HBulk (fo (copy_set ms))]
  | _ => [HBulk (fo t)]
  end.

(* check_reject_clean_starved's parse (:536-542) *)
Definition starved_parse (x : list Z) (took : nat) : list hev :=
  match took with O => [] | S _ => parse_evs x (okk (pick x took)) end.

(* check_reject_clean_starved's writes (:545-568): each, whole then with one allocation failing *)
Definition starved_write (x : list Z) (t : jv) (p : bool) (rest : list hev) : list hev :=
  w_evs t p ++ w_free t p ++
  match wcalls t p with O => [] | S _ => w_starved t p (pick x (wcalls t p)) ++ rest end.

Definition starved_writes (x : list Z) (t : jv) : list hev := starved_write x t true (starved_write x t false []).

(* LLVMFuzzerTestOneInput (:679-707) on the bytes x *)
Definition hrun (x : list Z) : list hev :=
  let n := Z.of_nat (length x) in
  if MAXB <? n then []
  else
    let P := parse_evs x [] in
    let Lr := pj_frees [] x in
    let tree_free := match fst (jr_run sm x []) with Some _ => [HBulk Lr] | None => [] end in
    (* check_no_overread (:453-477) *)
    [HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD)] ++ P ++ P ++ P ++
    tree_free ++ tree_free ++ tree_free ++
    [HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD)] ++
    (* pj_parse (:692), then check_as_written's expected() (:331, :343) *)
    P ++ [HMal (n + 1); HFr (n + 1)] ++
    match fst (jr_run sm x []) with
    | None => starved_parse x (calls (rtr [] x))
    | Some t => round_trip t ++ starved_parse x (calls (rtr [] x)) ++ starved_writes x t ++ [HBulk Lr]
    end.

(* ================================================================ positions and req_at *)

Definition pos : Type := (nat * list Z)%type.

Definition pos_valid_x (x : list Z) (pi : pos) : Prop :=
  (fst pi <= length (hrun x))%nat /\
  (snd pi = [] \/ exists L G, nth_error (hrun x) (fst pi) = Some (HBulk L) /\ Permutation L (snd pi ++ G)).

Definition req_x (x : list Z) (pi : pos) : list Z := rmall (snd pi) (hlive (firstn (fst pi) (hrun x))).

(* the harness's input in the run of inp: argv [_; p], p a file, its header in range (YO05.driver_m), the payload *)
Definition slot_input (inp : ProcInput) : option (list Z) :=
  match in_argv inp with
  | [_; p] =>
      match YO05.classify_open p (in_fs inp) with
      | YO05.OpenFile data =>
          if (YO05.dlen data <? YO05.MAX_INPUT) && (YO05.HDR_MIN + YO05.config_len data <=? YO05.dlen data)
          then Some (map (fun b : byte => bv_unsigned b) (YO06.payload data))
          else None
      | _ => None
      end
  | _ => None
  end.

Definition pos_valid (inp : ProcInput) (pi : pos) : Prop :=
  match slot_input inp with Some x => pos_valid_x x pi | None => False end.

Definition req_at (inp : ProcInput) (pi : pos) : list Z :=
  match slot_input inp with Some x => req_x x pi | None => [] end.

End Run.

(* ================================================================ sanity, by computation *)

(* "[[]]": one block per tree, a kids array of 8 slots (56 * 8 + 16). At check_no_overread's third-parse peak
   (after the 3 copies and the 3 parses) the three trees and the three copies are live. *)
Example sanity_peak_nested : forall sm, req_x sm [91; 91; 93; 93] (6%nat, []) = [464; 464; 464; 20; 20; 20].
Proof. intros sm. vm_compute. reflexivity. Qed.

(* Every run gives back all it took: the live multiset at the end is empty (refused, array, object without and with
   modifiedAt, a string with escapes). *)
Example sanity_end_refused : forall sm, hlive (hrun sm [91]) = [].
Proof. intros sm. vm_compute. reflexivity. Qed.

Example sanity_end_nested : forall sm, hlive (hrun sm [91; 91; 93; 93]) = [].
Proof. intros sm. vm_compute. reflexivity. Qed.

Example sanity_end_obj : forall sm, hlive (hrun sm [123; 34; 97; 34; 58; 91; 93; 125]) = [].
Proof. intros sm. vm_compute. reflexivity. Qed.

Example sanity_end_obj_mod : forall sm,
  hlive (hrun sm ([123; 34] ++ MOD_KEY ++ [34; 58; 34; 92; 110; 34; 125])) = [].
Proof. intros sm. vm_compute. reflexivity. Qed.

(* pj_free's order against the live list. {"a":"x"}: pj_free frees "x" (18), the key "a" (18), kids (464), keys
   (80); the live list (newest first) has keys before kids, so HBulk of it would assert a free order pj_free does
   not have. {"a":["y","x"] (refused at the end): the partial tree's order, the inner array counted. *)
Example pj_frees_obj : forall sm, pj_frees sm [] [123; 34; 97; 34; 58; 34; 120; 34; 125] = [18; 18; 464; 80].
Proof. intros sm. vm_compute. reflexivity. Qed.

Example rd_blocks_obj : forall sm, rd_blocks (rtr sm [] [123; 34; 97; 34; 58; 34; 120; 34; 125]) = [18; 18; 80; 464].
Proof. intros sm. vm_compute. reflexivity. Qed.

Example pj_frees_obj_order : forall sm,
  pj_frees sm [] [123; 34; 97; 34; 58; 34; 120; 34; 125] <> rd_blocks (rtr sm [] [123; 34; 97; 34; 58; 34; 120; 34; 125]).
Proof. intros sm. vm_compute. discriminate. Qed.

Example pj_frees_partial : forall sm,
  pj_frees sm [] [123; 34; 97; 34; 58; 91; 34; 121; 34; 44; 34; 120; 34; 93] = [18; 18; 464; 18; 464; 80].
Proof. intros sm. vm_compute. reflexivity. Qed.

(* ================================================================ multiset infrastructure

   The facts the consumers of req_at need about hlive / rmall: a count that only Permutation sees, the
   sub-multiset order, and okf: "every removal of this event list finds its block". okf is what makes req_at a
   real multiset difference, and it gives the frame law hlive_from (a ++ s) es = hlive_from a es ++ s. *)

Definition cnt (f : Z -> bool) (L : list Z) : nat := length (List.filter f L).

Lemma perm_cons_cancel : forall (z : Z) a b, Permutation (z :: a) (z :: b) -> Permutation a b.
Proof. intros z a b H. exact (Permutation_cons_inv H). Qed.

Lemma cnt_app : forall f a b, cnt f (a ++ b) = (cnt f a + cnt f b)%nat.
Proof.
  intros f a b. unfold cnt. induction a as [|z a IH]; [reflexivity|].
  simpl. destruct (f z); simpl; lia.
Qed.

Lemma cnt_perm : forall f a b, Permutation a b -> cnt f a = cnt f b.
Proof.
  intros f a b H. unfold cnt. induction H as [|z a b H IH|z y a|a b c H1 IH1 H2 IH2].
  - reflexivity.
  - simpl. destruct (f z); simpl; lia.
  - simpl. destruct (f z); destruct (f y); simpl; lia.
  - lia.
Qed.

Lemma cnt_cons : forall f z L, (cnt f (z :: L) <= S (cnt f L))%nat.
Proof. intros f z L. unfold cnt. simpl. destruct (f z); simpl; lia. Qed.

(* a is a sub-multiset of b *)
Definition subm (a b : list Z) : Prop := exists d, Permutation b (a ++ d).

Lemma subm_refl : forall a, subm a a.
Proof. intros a. exists []. rewrite app_nil_r. apply Permutation_refl. Qed.

Lemma subm_perm : forall a b, Permutation b a -> subm a b.
Proof. intros a b H. exists []. rewrite app_nil_r. exact H. Qed.

Lemma subm_trans : forall a b c, subm a b -> subm b c -> subm a c.
Proof.
  intros a b c [d1 H1] [d2 H2]. exists (d1 ++ d2). rewrite app_assoc.
  apply (Permutation_trans H2). apply Permutation_app_tail. exact H1.
Qed.

Lemma subm_cnt : forall f a b, subm a b -> (cnt f a <= cnt f b)%nat.
Proof. intros f a b [d H]. rewrite (cnt_perm f _ _ H), cnt_app. lia. Qed.

Lemma subm_nil : forall a, subm [] a.
Proof. intros a. exists a. apply Permutation_refl. Qed.

Lemma subm_cons : forall z a b, subm a b -> subm (z :: a) (z :: b).
Proof. intros z a b [d H]. exists d. cbn [app]. apply perm_skip. exact H. Qed.

Lemma subm_app_r : forall a b, subm a (b ++ a).
Proof. intros a b. exists b. apply Permutation_app_comm. Qed.

Lemma subm_app_head : forall u a b, subm a b -> subm (u ++ a) (u ++ b).
Proof.
  intros u a b [d H]. exists d. rewrite <- app_assoc.
  apply Permutation_app_head. exact H.
Qed.

Lemma subm_in : forall z a b, subm a b -> In z a -> In z b.
Proof.
  intros z a b [d H] Hin. apply (Permutation_in z (Permutation_sym H)). apply in_or_app. left. exact Hin.
Qed.

(* ---- rm1 *)

Lemma rm1_cons_eq : forall z s, rm1 z (z :: s) = s.
Proof. intros z s. cbn [rm1]. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma rm1_in : forall z s, In z s -> Permutation s (z :: rm1 z s).
Proof.
  intros z s. induction s as [|y s IH]; intros Hin; [destruct Hin|].
  cbn [rm1]. destruct (y =? z) eqn:E.
  - apply Z.eqb_eq in E. subst y. apply Permutation_refl.
  - apply Z.eqb_neq in E. destruct Hin as [-> | Hin]; [congruence|].
    exact (Permutation_trans (perm_skip y (IH Hin)) (perm_swap z y (rm1 z s))).
Qed.

Lemma rm1_notin : forall z s, ~ In z s -> rm1 z s = s.
Proof.
  intros z s. induction s as [|y s IH]; intros Hin; [reflexivity|].
  cbn [rm1]. destruct (y =? z) eqn:E.
  - apply Z.eqb_eq in E. subst y. exfalso. apply Hin. left. reflexivity.
  - rewrite IH; [reflexivity|]. intros H. apply Hin. right. exact H.
Qed.

Lemma rm1_subm : forall z s, subm (rm1 z s) s.
Proof.
  intros z s. destruct (in_dec Z.eq_dec z s) as [Hin | Hout].
  - exists [z]. apply (Permutation_trans (rm1_in z s Hin)). apply Permutation_cons_append.
  - rewrite (rm1_notin z s Hout). apply subm_refl.
Qed.

Lemma rm1_perm_cons : forall z a u, Permutation a (z :: u) -> Permutation (rm1 z a) u.
Proof.
  intros z a u H.
  assert (Hin : In z a).
  { apply (Permutation_in z (Permutation_sym H)). left. reflexivity. }
  apply (perm_cons_cancel z).
  exact (Permutation_trans (Permutation_sym (rm1_in z a Hin)) H).
Qed.

Lemma rm1_app_l : forall z a s, In z a -> rm1 z (a ++ s) = rm1 z a ++ s.
Proof.
  intros z a s. induction a as [|y a IH]; intros Hin; [destruct Hin|].
  cbn [app rm1]. destruct (y =? z) eqn:E; [reflexivity|].
  apply Z.eqb_neq in E. destruct Hin as [-> | Hin]; [congruence|].
  rewrite (IH Hin). reflexivity.
Qed.

Lemma rm1_app_notin : forall z a s, ~ In z a -> rm1 z (a ++ s) = a ++ rm1 z s.
Proof.
  intros z a s. induction a as [|y a IH]; intros Hin; [reflexivity|].
  cbn [app rm1]. destruct (y =? z) eqn:E.
  - apply Z.eqb_eq in E. subst y. exfalso. apply Hin. left. reflexivity.
  - rewrite IH; [reflexivity|]. intros H. apply Hin. right. exact H.
Qed.

Lemma rm1_perm : forall z a b, Permutation a b -> Permutation (rm1 z a) (rm1 z b).
Proof.
  intros z a b H. destruct (in_dec Z.eq_dec z a) as [Hin | Hout].
  - assert (Hinb : In z b) by (apply (Permutation_in z H); exact Hin).
    apply (perm_cons_cancel z).
    apply (Permutation_trans (Permutation_sym (rm1_in z a Hin))).
    exact (Permutation_trans H (rm1_in z b Hinb)).
  - assert (Houtb : ~ In z b) by (intros Hb; apply Hout; apply (Permutation_in z (Permutation_sym H)); exact Hb).
    rewrite (rm1_notin z a Hout), (rm1_notin z b Houtb). exact H.
Qed.

Lemma rm1_mono : forall z a b, subm a b -> subm (rm1 z a) (rm1 z b).
Proof.
  intros z a b [d Hd].
  pose proof (rm1_perm z b (a ++ d) Hd) as Hp.
  destruct (in_dec Z.eq_dec z a) as [Hin | Hout].
  - exists d. rewrite <- (rm1_app_l z a d Hin). exact Hp.
  - exists (rm1 z d). rewrite (rm1_notin z a Hout), <- (rm1_app_notin z a d Hout). exact Hp.
Qed.

Lemma rm1_le : forall z a s, subm (rm1 z (a ++ s)) (rm1 z a ++ s).
Proof.
  intros z a s. destruct (in_dec Z.eq_dec z a) as [Hin | Hout].
  - rewrite (rm1_app_l z a s Hin). apply subm_refl.
  - rewrite (rm1_app_notin z a s Hout), (rm1_notin z a Hout).
    apply subm_app_head. apply rm1_subm.
Qed.

(* ---- rmall *)

Lemma rmall_cons : forall z L s, rmall (z :: L) s = rmall L (rm1 z s).
Proof. intros z L s. reflexivity. Qed.

Lemma rmall_nil_s : forall L, rmall L [] = [].
Proof. intros L. induction L as [|z L IH]; [reflexivity|]. rewrite rmall_cons. cbn [rm1]. exact IH. Qed.

Lemma rmall_mono : forall L a b, subm a b -> subm (rmall L a) (rmall L b).
Proof.
  induction L as [|z L IH]; intros a b H; [exact H|].
  rewrite !rmall_cons. apply IH. apply rm1_mono. exact H.
Qed.

Lemma rmall_subm : forall L s, subm (rmall L s) s.
Proof.
  induction L as [|z L IH]; intros s; [apply subm_refl|].
  rewrite rmall_cons. apply (subm_trans _ (rm1 z s) s); [apply IH | apply rm1_subm].
Qed.

Lemma rmall_le : forall L a s, subm (rmall L (a ++ s)) (rmall L a ++ s).
Proof.
  induction L as [|z L IH]; intros a s; [apply subm_refl|].
  rewrite !rmall_cons.
  apply (subm_trans _ (rmall L (rm1 z a ++ s))).
  - apply rmall_mono. apply rm1_le.
  - apply IH.
Qed.

Lemma rmall_app_in : forall L a s, subm L a -> rmall L (a ++ s) = rmall L a ++ s.
Proof.
  induction L as [|z L IH]; intros a s H; [reflexivity|].
  destruct H as [d Hd].
  assert (Hin : In z a).
  { apply (Permutation_in z (Permutation_sym Hd)). left. reflexivity. }
  rewrite !rmall_cons, (rm1_app_l z a s Hin). apply IH.
  exists d. apply (rm1_perm_cons z a (L ++ d)). exact Hd.
Qed.

Lemma rmall_drop : forall L A B, Permutation A L -> rmall L (A ++ B) = B.
Proof.
  induction L as [|z L IH]; intros A B H.
  - apply Permutation_sym in H. apply Permutation_nil in H. subst A. reflexivity.
  - assert (Hin : In z A) by (apply (Permutation_in z (Permutation_sym H)); left; reflexivity).
    rewrite rmall_cons, (rm1_app_l z A B Hin). apply IH.
    apply (rm1_perm_cons z A L). exact H.
Qed.

(* ---- hlive_from *)

Lemma hlive_from_nil : forall s, hlive_from s [] = s.
Proof. reflexivity. Qed.

Lemma hlive_from_cons : forall s e r, hlive_from s (e :: r) = hlive_from (hstep s e) r.
Proof. reflexivity. Qed.

Lemma hlive_from_app : forall s a b, hlive_from s (a ++ b) = hlive_from (hlive_from s a) b.
Proof. intros s a b. unfold hlive_from. apply fold_left_app. Qed.

Lemma hstep_mono : forall e a b, subm a b -> subm (hstep a e) (hstep b e).
Proof.
  intros [n | m n | n | L] a b H; cbn [hstep].
  - apply subm_cons. exact H.
  - apply subm_cons. apply rm1_mono. exact H.
  - apply rm1_mono. exact H.
  - apply rmall_mono. exact H.
Qed.

Lemma hlive_from_mono : forall es a b, subm a b -> subm (hlive_from a es) (hlive_from b es).
Proof.
  induction es as [|e r IH]; intros a b H; [exact H|].
  rewrite !hlive_from_cons. apply IH. apply hstep_mono. exact H.
Qed.

Lemma hstep_le : forall e a s, subm (hstep (a ++ s) e) (hstep a e ++ s).
Proof.
  intros [n | m n | n | L] a s; cbn [hstep].
  - apply subm_refl.
  - change (n :: rm1 m a ++ s) with ((n :: rm1 m a) ++ s). cbn [app].
    apply subm_cons. apply rm1_le.
  - apply rm1_le.
  - apply rmall_le.
Qed.

Lemma hlive_from_le : forall es a s, subm (hlive_from (a ++ s) es) (hlive_from a es ++ s).
Proof.
  induction es as [|e r IH]; intros a s; [apply subm_refl|].
  rewrite !hlive_from_cons.
  apply (subm_trans _ (hlive_from (hstep a e ++ s) r)).
  - apply hlive_from_mono. apply hstep_le.
  - apply IH.
Qed.

Lemma hlive_le : forall es s, subm (hlive_from s es) (hlive es ++ s).
Proof. intros es s. unfold hlive. rewrite <- (app_nil_l s) at 1. apply hlive_from_le. Qed.

(* ---- okf: every removal finds its block *)

Definition hits (s : list Z) (e : hev) : Prop :=
  match e with
  | HMal _ => True
  | HRe m _ => In m s
  | HFr n => In n s
  | HBulk L => subm L s
  end.

Fixpoint okf (s : list Z) (es : list hev) : Prop :=
  match es with
  | [] => True
  | e :: r => hits s e /\ okf (hstep s e) r
  end.

Lemma hits_mono : forall e a b, subm a b -> hits a e -> hits b e.
Proof.
  intros [n | m n | n | L] a b H Hh; cbn [hits] in *; try exact I.
  - exact (subm_in m a b H Hh).
  - exact (subm_in n a b H Hh).
  - exact (subm_trans L a b Hh H).
Qed.

Lemma okf_mono : forall es a b, subm a b -> okf a es -> okf b es.
Proof.
  induction es as [|e r IH]; intros a b H Hk; [exact I|].
  destruct Hk as [Hh Hr]. split.
  - exact (hits_mono e a b H Hh).
  - exact (IH _ _ (hstep_mono e a b H) Hr).
Qed.

Lemma okf_app : forall a b s, okf s (a ++ b) <-> okf s a /\ okf (hlive_from s a) b.
Proof.
  induction a as [|e r IH]; intros b s; cbn [app].
  - split; [intros H; split; [exact I | exact H] | intros [_ H]; exact H].
  - cbn [okf]. rewrite hlive_from_cons. split.
    + intros [Hh Hr]. apply IH in Hr as [H1 H2]. split; [split; assumption | exact H2].
    + intros [[Hh H1] H2]. split; [exact Hh|]. apply IH. split; assumption.
Qed.

Lemma hlive_from_okf : forall es a s, okf a es -> hlive_from (a ++ s) es = hlive_from a es ++ s.
Proof.
  induction es as [|e r IH]; intros a s H; [reflexivity|].
  destruct H as [Hh Hr]. rewrite !hlive_from_cons.
  assert (Hst : hstep (a ++ s) e = hstep a e ++ s).
  { destruct e as [n | m n | n | L]; cbn [hstep] in *.
    - reflexivity.
    - rewrite (rm1_app_l m a s Hh). reflexivity.
    - rewrite (rm1_app_l n a s Hh). reflexivity.
    - rewrite (rmall_app_in L a s Hh). reflexivity. }
  rewrite Hst. apply IH. exact Hr.
Qed.

Lemma hlive_okf : forall es s, okf [] es -> hlive_from s es = hlive es ++ s.
Proof. intros es s H. unfold hlive. rewrite <- (app_nil_l s) at 1. apply hlive_from_okf. exact H. Qed.

(* ================================================================ the reader's events are closed *)

Lemma rd_hevs_app : forall a b, rd_hevs (a ++ b) = rd_hevs a ++ rd_hevs b.
Proof. intros a b. unfold rd_hevs. apply flat_map_app. Qed.

Lemma rd_hev_grow_O : forall n, rd_hev (EGrow 0 n) = [HMal (Z.of_nat n + HEAD)].
Proof. reflexivity. Qed.

Lemma rd_hev_grow_S : forall m n, (0 < m)%nat -> rd_hev (EGrow m n) = [HRe (Z.of_nat m + HEAD) (Z.of_nat n + HEAD)].
Proof. intros [|m] n H; [lia | reflexivity]. Qed.

Lemma arrz_hd : forall o c, In (Z.of_nat (56 * S c) + HEAD) (arrz o (S c)).
Proof. intros o c. cbn [arrz]. left. reflexivity. Qed.

Lemma rm1_two : forall a b, rm1 b [a; b] = [a] \/ (a = b /\ rm1 b [a; b] = [b]).
Proof.
  intros a b. cbn [rm1]. destruct (a =? b) eqn:E.
  - apply Z.eqb_eq in E. right. split; [exact E | reflexivity].
  - rewrite Z.eqb_refl. left. reflexivity.
Qed.

Lemma jrealloc_cases : forall m n ok,
  (exists ok1, jrealloc m n ok = (Some tt, [EGrow m n], ok1)) \/
  (exists ok1, jrealloc m n ok = (None, [EFail n], ok1)).
Proof.
  intros m n ok. unfold jrealloc. destruct (take ok) as [b ok1].
  destruct b; [left | right]; exists ok1; reflexivity.
Qed.

Lemma grow_okf : forall o n cap ok,
  okf (arrz o cap) (rd_hevs (snd (fst (grow o n cap ok)))) /\
  (forall c, fst (fst (grow o n cap ok)) = Some c ->
     subm (arrz o c) (hlive_from (arrz o cap) (rd_hevs (snd (fst (grow o n cap ok)))))).
Proof.
  intros o n cap ok. unfold grow.
  destruct (Nat.ltb n cap) eqn:Elt.
  { unfold jret. cbn [fst snd rd_hevs flat_map okf].
    split; [exact I|]. intros c Hc. injection Hc as <-. rewrite hlive_from_nil. apply subm_refl. }
  cbv zeta.
  destruct (jrealloc_cases (56 * cap) (56 * (if Nat.eqb cap 0 then 8 else 2 * cap)) ok) as [[ok1 E1] | [ok1 E1]].
  - unfold jbind. rewrite E1. cbv beta iota.
    destruct o.
    + destruct (jrealloc_cases (8 * cap) (8 * (if Nat.eqb cap 0 then 8 else 2 * cap)) ok1)
        as [[ok2 E2] | [ok2 E2]]; try unfold jbind; rewrite E2; cbv beta iota; unfold jret;
        cbn [fst snd]; rewrite rd_hevs_app; cbn [rd_hevs flat_map app].
      * destruct cap as [|c].
        -- cbn [Nat.eqb arrz]. rewrite !rd_hev_grow_O. cbn [app].
           cbn [okf hits hstep hlive_from fold_left].
           split; [repeat split; exact I|]. intros c0 Hc0. injection Hc0 as <-.
           cbn [arrz]. apply subm_perm. apply perm_swap.
        -- rewrite (rd_hev_grow_S (56 * S c) _ ltac:(lia)), (rd_hev_grow_S (8 * S c) _ ltac:(lia)).
           cbn [app arrz Nat.eqb].
           cbn [okf hits hstep hlive_from fold_left]. rewrite rm1_cons_eq.
           split.
           ++ split; [left; reflexivity|]. split; [right; left; reflexivity | exact I].
           ++ intros c0 Hc0. injection Hc0 as <-. cbn [arrz].
              destruct (rm1_two (Z.of_nat (56 * (2 * S c)) + HEAD) (Z.of_nat (8 * S c) + HEAD))
                as [H2 | [Heq H2]]; rewrite H2.
              ** apply subm_perm. apply perm_swap.
              ** rewrite <- Heq. apply subm_perm. apply perm_swap.
      * destruct cap as [|c].
        -- cbn [Nat.eqb arrz]. rewrite rd_hev_grow_O. cbn [app rd_hev].
           cbn [okf hits hstep hlive_from fold_left].
           split; [repeat split; exact I|]. intros c0 Hc0. discriminate Hc0.
        -- rewrite (rd_hev_grow_S (56 * S c) _ ltac:(lia)). cbn [app arrz Nat.eqb rd_hev].
           cbn [okf hits hstep hlive_from fold_left].
           split; [split; [left; reflexivity | exact I]|]. intros c0 Hc0. discriminate Hc0.
    + unfold jret. cbn [fst snd]. rewrite rd_hevs_app. cbn [rd_hevs flat_map app].
      destruct cap as [|c].
      * cbn [Nat.eqb arrz]. rewrite rd_hev_grow_O. cbn [app].
        cbn [okf hits hstep hlive_from fold_left].
        split; [repeat split; exact I|]. intros c0 Hc0. injection Hc0 as <-.
        cbn [arrz]. apply subm_refl.
      * rewrite (rd_hev_grow_S (56 * S c) _ ltac:(lia)). cbn [app arrz Nat.eqb].
        cbn [okf hits hstep hlive_from fold_left]. rewrite rm1_cons_eq.
        split; [split; [left; reflexivity | exact I]|]. intros c0 Hc0. injection Hc0 as <-.
        cbn [arrz]. apply subm_refl.
  - unfold jbind. rewrite E1. cbv beta iota. cbn [fst snd rd_hevs flat_map rd_hev app].
    cbn [okf]. split; [exact I|]. intros c0 Hc0. discriminate Hc0.
Qed.

(* ================================================================ the reader never removes a foreign block *)

Section Closed.

Variable sm : list Z -> Z * Z.

Definition NB {A : Type} (B : list Z) (m : M A) : Prop :=
  forall ok, okf B (rd_hevs (snd (fst (m ok)))).

Lemma okf_frame : forall es s, okf [] es -> subm s (hlive_from s es).
Proof. intros es s H. rewrite (hlive_okf es s H). apply subm_app_r. Qed.

Lemma NB_bind_gen : forall (A B : Type) (m : M A) (k : A -> M B) (s : list Z),
  (forall ok, okf s (rd_hevs (snd (fst (m ok))))) ->
  (forall ok a t ok1, m ok = (Some a, t, ok1) ->
     okf (hlive_from s (rd_hevs t)) (rd_hevs (snd (fst (k a ok1))))) ->
  forall ok, okf s (rd_hevs (snd (fst (jbind m k ok)))).
Proof.
  intros A B m k s H1 H2 ok. unfold jbind.
  specialize (H1 ok). destruct (m ok) as [[[a|] t] ok1] eqn:E; cbv beta iota.
  - specialize (H2 ok a t ok1 E).
    destruct (k a ok1) as [[r t'] ok2] eqn:Ek. cbn [fst snd] in *.
    rewrite rd_hevs_app. apply okf_app. split; assumption.
  - cbn [fst snd] in *. exact H1.
Qed.

Lemma NB_string : forall z, NB [] (jr_string z).
Proof.
  intros z ok. unfold jr_string. destruct (scan z) as [q|] eqn:Es.
  - unfold jbind, jalloc. destruct (take ok) as [b ok1]. destruct b; cbv beta iota.
    + destruct (decode z) as [[s r]|] eqn:Ed; cbv beta iota.
      * unfold jret. cbn [fst snd rd_hevs flat_map rd_hev app okf hits]. split; exact I.
      * unfold jbind, jfree, jrefuse. cbn [fst snd rd_hevs flat_map rd_hev app].
        cbn [okf hits hstep hlive_from fold_left].
        split; [exact I|]. split; [left; reflexivity | exact I].
    + cbn [fst snd rd_hevs flat_map rd_hev app okf]. exact I.
  - unfold jrefuse. cbn [fst snd rd_hevs flat_map okf]. exact I.
Qed.

Lemma NB_lit : forall w v x, NB [] (lit w v x).
Proof.
  intros w v x ok. unfold lit. destruct (prefixb w x); unfold jret, jrefuse;
    cbn [fst snd rd_hevs flat_map okf]; exact I.
Qed.

Lemma NB_name : forall o y, NB [] (jr_name o y).
Proof.
  intros o y ok. unfold jr_name. destruct o.
  - destruct (skip y) as [|b z] eqn:Ey.
    + unfold jrefuse. cbn [fst snd rd_hevs flat_map okf]. exact I.
    + destruct (b =? 34) eqn:Eb.
      * pose proof (jr_string_spec z ok) as Hs. pose proof (NB_string z ok) as Hn.
        unfold jbind at 1.
        destruct (jr_string z ok) as [[[[nm r]|] t] ok1] eqn:Ej; cbv beta iota.
        -- destruct Hs as (q & Hsc & Hd & Ht & Hl). subst t.
           assert (Hb : sblock z = S q) by (unfold sblock; rewrite Hsc; reflexivity).
           destruct (skip r) as [|c r1] eqn:Er.
           ++ unfold jbind, jfree, jrefuse. rewrite Hb. cbn [fst snd].
              rewrite rd_hevs_app. cbn [rd_hevs flat_map rd_hev app].
              cbn [okf hits hstep hlive_from fold_left].
              split; [exact I|]. split; [left; reflexivity | exact I].
           ++ destruct (c =? 58).
              ** unfold jret. cbn [fst snd]. rewrite rd_hevs_app.
                 cbn [rd_hevs flat_map rd_hev app okf hits]. split; exact I.
              ** unfold jbind, jfree, jrefuse. rewrite Hb. cbn [fst snd].
                 rewrite rd_hevs_app. cbn [rd_hevs flat_map rd_hev app].
                 cbn [okf hits hstep hlive_from fold_left].
                 split; [exact I|]. split; [left; reflexivity | exact I].
        -- cbn [fst snd] in Hn |- *. exact Hn.
      * unfold jrefuse. cbn [fst snd rd_hevs flat_map okf]. exact I.
  - unfold jret. cbn [fst snd rd_hevs flat_map okf]. exact I.
Qed.

Lemma NB_number : forall x, NB [] (jr_number sm x).
Proof.
  intros x ok. unfold jr_number. cbv zeta.
  set (j := match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end).
  destruct (skipn j x) as [|c z] eqn:Ez.
  - unfold jrefuse. cbn [fst snd rd_hevs flat_map okf]. exact I.
  - destruct (negb (digit c)).
    + unfold jrefuse. cbn [fst snd rd_hevs flat_map okf]. exact I.
    + destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end).
      * unfold jrefuse. cbn [fst snd rd_hevs flat_map okf]. exact I.
      * destruct (span numch z) as [a r].
        unfold jbind, jalloc. destruct (take ok) as [b ok1]. destruct b; cbv beta iota.
        -- destruct (whole sm (firstn j x ++ c :: a)); unfold jret, jrefuse; cbn [fst snd];
             rewrite rd_hevs_app; cbn [rd_hevs flat_map rd_hev app okf hits]; split; exact I.
        -- cbn [fst snd rd_hevs flat_map rd_hev app okf]. exact I.
Qed.

Lemma NB_cont : forall loop d o x,
  (forall d' o' n cap acc y, NB (arrz o' cap) (loop d' o' n cap acc y)) ->
  NB [] (jr_cont loop d o x).
Proof.
  intros loop d o x H ok. unfold jr_cont.
  destruct (Nat.ltb MAXD (S d)).
  - unfold jrefuse. cbn [fst snd rd_hevs flat_map okf]. exact I.
  - destruct (skip (tl x)) as [|c r] eqn:Ey.
    + exact (H (S d) o 0%nat 0%nat [] [] ok).
    + destruct (c =? closer o).
      * unfold jret. cbn [fst snd rd_hevs flat_map okf]. exact I.
      * exact (H (S d) o 0%nat 0%nat [] (c :: r) ok).
Qed.

Lemma NB_fuel : forall f,
  (forall d x, NB [] (jrv sm f d x)) /\
  (forall d o n cap acc y, NB (arrz o cap) (jrl sm f d o n cap acc y)).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; intros ok; cbn [jrv jrl]; unfold jrefuse;
      cbn [fst snd rd_hevs flat_map okf]; exact I.
  - split.
    + intros d x ok. cbn [jrv].
      destruct (skip x) as [|b y] eqn:Ex.
      { unfold jrefuse. cbn [fst snd rd_hevs flat_map okf]. exact I. }
      destruct (b =? 123); [exact (NB_cont _ d true (b :: y) IHl ok)|].
      destruct (b =? 91); [exact (NB_cont _ d false (b :: y) IHl ok)|].
      destruct (b =? 34).
      * apply (NB_bind_gen _ _ (jr_string y) _ []).
        -- intros ok0. exact (NB_string y ok0).
        -- intros ok0 a t ok1 Ea. destruct a as [s r]. unfold jret.
           cbn [fst snd rd_hevs flat_map okf]. exact I.
      * destruct (b =? 116); [exact (NB_lit _ _ _ ok)|].
        destruct (b =? 102); [exact (NB_lit _ _ _ ok)|].
        destruct (b =? 110); [exact (NB_lit _ _ _ ok)|].
        exact (NB_number (b :: y) ok).
    + intros d o n cap acc y ok. cbn [jrl].
      apply (NB_bind_gen _ _ (grow o n cap) _ (arrz o cap)).
      { intros ok0. exact (proj1 (grow_okf o n cap ok0)). }
      intros ok0 cap1 tg ok1 Eg.
      assert (Hsub : subm (arrz o cap1) (hlive_from (arrz o cap) (rd_hevs tg))).
      { destruct (grow_okf o n cap ok0) as [_ H2]. rewrite Eg in H2. cbn [fst snd] in H2.
        exact (H2 cap1 eq_refl). }
      apply (okf_mono _ _ _ Hsub).
      apply (NB_bind_gen _ _ (jr_name o y) _ (arrz o cap1)).
      { intros ok2. exact (okf_mono _ [] _ (subm_nil _) (NB_name o y ok2)). }
      intros ok2 a tn ok3 En. destruct a as [nm y1].
      assert (Hn : okf [] (rd_hevs tn)).
      { pose proof (NB_name o y ok2) as HH. rewrite En in HH. cbn [fst snd] in HH. exact HH. }
      set (S1 := hlive_from (arrz o cap1) (rd_hevs tn)).
      assert (Hs1 : subm (arrz o cap1) S1) by (apply okf_frame; exact Hn).
      apply (NB_bind_gen _ _ (jrv sm f d y1) _ S1).
      { intros ok4. exact (okf_mono _ [] _ (subm_nil _) (IHv d y1 ok4)). }
      intros ok4 a2 tv ok5 Ev. destruct a2 as [v r].
      assert (Hv : okf [] (rd_hevs tv)).
      { pose proof (IHv d y1 ok4) as HH. rewrite Ev in HH. cbn [fst snd] in HH. exact HH. }
      assert (Hs2 : subm (arrz o cap1) (hlive_from S1 (rd_hevs tv))).
      { apply (subm_trans _ S1); [exact Hs1 | apply okf_frame; exact Hv]. }
      destruct (skip r) as [|c r1] eqn:Er.
      { unfold jrefuse. cbn [fst snd rd_hevs flat_map okf]. exact I. }
      destruct (c =? 44).
      { apply (okf_mono _ _ _ Hs2). exact (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok5). }
      destruct (c =? closer o).
      { unfold jret. cbn [fst snd rd_hevs flat_map okf]. exact I. }
      { unfold jrefuse. cbn [fst snd rd_hevs flat_map okf]. exact I. }
Qed.

(* THE CLOSEDNESS FACT: every EFree / EGrow of a reader run frees a block the same run made. *)
Theorem rd_okf : forall x ok, okf [] (rd_hevs (snd (jr_run sm x ok))).
Proof.
  intros x ok. unfold jr_run, jr_value.
  destruct (NB_fuel (S (2 * length x))) as [Hv _].
  pose proof (Hv 0%nat x ok) as H.
  destruct (jrv sm (S (2 * length x)) 0 x ok) as [[[[t r]|] tr] ok'] eqn:E;
    cbn [fst snd] in H |- *.
  - destruct (skip r); cbn [snd]; exact H.
  - exact H.
Qed.

(* Closedness in the form the consumers use. *)
Theorem rd_closed : forall x ok s,
  hlive_from s (rd_hevs (snd (jr_run sm x ok))) = rd_blocks (snd (jr_run sm x ok)) ++ s.
Proof. intros x ok s. apply hlive_okf. apply rd_okf. Qed.

Theorem rd_okf_prefix : forall x ok t r, snd (jr_run sm x ok) = t ++ r -> okf [] (rd_hevs t).
Proof.
  intros x ok t r H. pose proof (rd_okf x ok) as Hk. rewrite H, rd_hevs_app in Hk.
  exact (proj1 (proj1 (okf_app _ _ _) Hk)).
Qed.

Theorem rd_closed_prefix : forall x ok t r s, snd (jr_run sm x ok) = t ++ r ->
  hlive_from s (rd_hevs t) = rd_blocks t ++ s.
Proof. intros x ok t r s H. apply hlive_okf. exact (rd_okf_prefix x ok t r H). Qed.

End Closed.

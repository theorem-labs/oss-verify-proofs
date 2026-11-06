(* fuzz_preset, program part (the kit): THE ALLOCATOR CHARGE OF THE READER, CITED FROM THE GRAMMAR. Definitions only.

   A text's room premise is ROOM_cf_k S (n + kr) (the allocator-model owner's YGcfRoomKeep.v), n the allocator steps the function's
   arms make. For the reader the grammar ALREADY records those steps: PjGrammar's reader monad emits one event per
   allocator call (EAlloc for a malloc, EGrow for a realloc, EFail for a refused one, EFree for a free). So the reader
   texts state n as prhPv_rk OF THE GRANTED TRACE (the run with every allocation granted, ok = []) of the very grammar
   function the C function implements - never as a numeral and never as a second, hand-written match:
     parse_value  prhPv_rk (prhPv_gtrace d x)       PjGrammar.jr_value
     parse_items  prhPv_rk (prhPi_gtrace d o x)     PjGrammar.jr_items
     parse_string prhPv_rk (prhPs_gtrace x)         PjGrammar.jr_string
     grow         prhPv_rk (prhPg_gtrace o n cap)   PjGrammar.grow
   A caller's charge then covers its callee's BECAUSE THE CALLEE'S GRANTED RUN IS A SUB-RUN of the caller's, and the
   arm structure (a free only on a bad escape; no realloc when n < cap) comes from the grammar itself.
   WHY (the kit owner's ruling, 2026-10-29): two encodings of one fact is how the room defects happened. The string-arm walk measured
   parse_value's string arm: the grammar charges [EAlloc] (1) when the string decodes, while a constant charge of
   RK_malloc + RK_free (2) cannot be met from 1 + kr (ROOM_cf_k is opaque). Tonight a walk lane reading a text
   against its callers beat review six times, and five times the right answer was to CITE THE MODEL instead of
   re-encoding it.
   WHEN A CONSTANT IS RIGHT: exactly when the charge cannot depend on an arm - one wrapper call per invocation:
   fuzz_malloc, fuzz_strdup, pj_string RK_malloc; fuzz_free RK_free; fuzz_realloc RK_realloc. Do not "fix" those.
   Charges over OTHER models stay over those models (the writer's grows prhWriter_ngrow, tx's prhtx_grows, pj_free's
   frees prhPj_fsteps over the tree's blocks).
   One copy: PRH_FnReader.v, PRH_FnPj.v, PRH_FnCheck.v and the recursive-reader author's PRH_FnParse.v cite these names; prhPv_rk_ev /
   prhPv_rk / prhPv_gtrace / prhPi_gtrace are the image-B parse_value walk's names (PRH_FnPValue.v a34197aa5760), bodies kept. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
Import ListNotations.
Local Open Scope Z_scope.

(* the allocator steps of one event: an allocation RK_malloc, a grow (fuzz_realloc) RK_realloc, a failed allocation at
   most RK_realloc (the chosen failure takes none, a refused malloc one, a refused realloc one), a free RK_free *)
Definition prhPv_rk_ev (e : PjGrammar.ev) : nat :=
  match e with
  | PjGrammar.EAlloc _ => RK_malloc
  | PjGrammar.EGrow _ _ => RK_realloc
  | PjGrammar.EFail _ => RK_realloc
  | PjGrammar.EFree _ => RK_free
  end.
Fixpoint prhPv_rk (tr : list PjGrammar.ev) : nat :=
  match tr with
  | [] => 0%nat
  | e :: r => (prhPv_rk_ev e + prhPv_rk r)%nat
  end.

(* the granted runs (every allocation succeeds, ok = []) of the grammar function each C function implements *)
Definition prhPv_gtrace (d : nat) (tl : list Z) : list PjGrammar.ev :=
  snd (fst (PjGrammar.jr_value prh_jr_strtod d tl [])).
Definition prhPi_gtrace (d : nat) (o : bool) (tl : list Z) : list PjGrammar.ev :=
  snd (fst (PjGrammar.jr_items prh_jr_strtod d o tl [])).
(* parse_string over the text after the opening quote *)
Definition prhPs_gtrace (x : list Z) : list PjGrammar.ev :=
  snd (fst (PjGrammar.jr_string x [])).
(* grow of a container holding n items in cap slots (o: an object, which also grows its keys array) *)
Definition prhPg_gtrace (o : bool) (n cap : Z) : list PjGrammar.ev :=
  snd (fst (PjGrammar.grow o (Z.to_nat n) (Z.to_nat cap) [])).

(* pj_free of blocks holding at most b user bytes: one fuzz_free per pointer it frees, NULL included (str, kids, keys
   of each node and keys[i] of each slot; the slots are at most the kids blocks' 56-byte cells), so at most
   3 + 4 * (b / 56) calls *)
Definition prh_fsteps_bytes (b : Z) : nat := (RK_free * (3 + 4 * Z.to_nat (b / 56)))%nat.

(* THE LARGEST SINGLE REQUEST of a trace: the request bound a reading's text asks, `prh_maxreq tr + cf_head <
   cf_malloc_max` (every one allocator request is one event's size plus the harness head). NOT the trace's peak
   (hpeakR plus heads): that is a HIGH-WATER MARK of live bytes, and charging it as one request is FALSE at full size
   (the B' walker's witness: an accepted 3 MiB input with peak 685,676,770 + heads = 710,842,546 against cf_malloc_max
   535,822,336; `request-premise-defect-witness.md (sha256 478d67bcd9a5; internal record)`, the kit owner's record lines 1366-1383). A refused run is P ++ [EFail (esize E)]
   with E in the granted trace (PjGrammar.agrees), so its largest request is at most the granted run's. *)
Definition prh_maxreq (tr : list PjGrammar.ev) : Z :=
  fold_right Z.max 0 (map (fun e => Z.of_nat (PjGrammar.esize e)) tr).

(* THE BYTES A CALL MAY ADD TO blocks_bytes, over its trace tr (the post conjunct `blocks_bytes S' <= blocks_bytes S +
   prh_held tr` of parse_value, parse_items, parse_string and grow; the items-element walk's finding: after a call nothing else
   re-establishes a reading's live room). blocks_bytes sums the allocator's REQUESTS (YG01.v:223-224), and a harness
   block's request is its user size plus the head (the kit's ablocks entry (res - cf_head, n + cf_head)), while
   PjGrammar.held counts USER bytes (EAlloc n => n, EGrow m n => n - m). So each call is charged cf_head on top: an
   EAlloc, or an EGrow from a NULL base, adds n + cf_head; an EGrow from a live block adds n - m; a free removes
   n + cf_head; a refusal or the chosen failure adds nothing. The plain `held tr` form is FALSE by cf_head at every
   successful allocation (the kit owner's measurement from the definitions, 2026-10-29). *)
Section held. Context {cp : CfParams}.
Definition prh_held (tr : list PjGrammar.ev) : Z :=
  PjGrammar.held tr + cf_head * Z.of_nat (PjGrammar.calls tr).
End held.

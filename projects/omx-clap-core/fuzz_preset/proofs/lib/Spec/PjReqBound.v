(* omx-clap-core/fuzz_preset: the reader-request bound of the #102 harness. Nothing here is a function's proof
   (rule 24); kind: statement text.

   WHAT THE HARNESS COMPARES. Each call of LLVMFuzzerTestOneInput (#102 fuzz/fuzz_preset.c:800-836) sets
   fuzz_alloc_most(PJ_ALLOC_BOUND(size)) (:810), with PJ_ALLOC_BOUND(n) = 256 n + JSON_DEPTH_MAX * 8 * PJ_SLOT + 4096
   (:62-63; PJ_SLOT = sizeof(struct pj) + sizeof(char * ) = 56 + 8, JSON_DEPTH_MAX = 32), so 256 n + 20480. When the C
   library refuses a request, fuzz_malloc / fuzz_realloc call refused(n) (#102 fuzz/alloc.c:70-78, from :89-90,
   :113-116 and :122-124), and refused sets ran_out only if n <= g_most. That n is the caller's request, WITHOUT HEAD:
   fuzz_malloc asks malloc for HEAD + n (:86) but hands refused the n it was asked for.

   WHAT A REQUEST IS IN THE MODEL. A reader event of PjGrammar.jr_run carries that caller's n (PresetReqAt.rd_hev puts
   the heap request at n + HEAD). ev_req is it: EAlloc n, a grow's NEW size n (EGrow m n: fuzz_realloc(p, n)), and a
   failed call's n (EFail n). A free asks for nothing: fuzz_free (alloc.c:140-149) never reaches refused, so EFree
   counts 0.

   THE BOUND. jr_req_bound: every request of the reader's trace on x is at most PJ_ALLOC_BOUND(|x|). It follows from
   PjGrammar.jr_esize_bound, the reader's joint fuel induction over jrv / jrl (PjGrammar.bound_fuel): a string asks
   its scanned length + 1 <= |x| (jr_string_esize), a number its text length + 1 <= |x| + 1 (jr_number_esize), and a
   container's grow asks 56 cap' (8 cap' for an object's keys) with cap' <= 8 + 2 n (PjGrammar.inv, grow_esize),
   where n items each followed by a comma were read, so n + (bytes left) <= |x|. Hence every request is at most
   56 |x| + 448 (jr_req_bound_56), which is below 256 |x| + 20480 for every |x|. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
Import ListNotations.
Local Open Scope Z_scope.

(* #102 fuzz/fuzz_preset.c:62-63, with sizeof(struct pj) = 56 and JSON_DEPTH_MAX = 32 *)
Definition PJ_ALLOC_BOUND (size : Z) : Z := 256 * size + 20480.

(* the n that #102 fuzz/alloc.c refused(n) compares with g_most; frees make no request *)
Definition ev_req (e : ev) : Z :=
  match e with
  | EAlloc n => Z.of_nat n
  | EGrow _ n => Z.of_nat n
  | EFail n => Z.of_nat n
  | EFree _ => 0
  end.

Lemma ev_req_le_esize : forall e, ev_req e <= Z.of_nat (esize e).
Proof. intros [n|m n|n|n]; cbn [ev_req esize]; lia. Qed.

Theorem jr_req_bound_56 : forall sm ok x e, In e (snd (jr_run sm x ok)) ->
  ev_req e <= 56 * Z.of_nat (length x) + 448.
Proof.
  intros sm ok x e Hin.
  pose proof (jr_esize_bound sm x ok e Hin) as H.
  pose proof (ev_req_le_esize e) as He. lia.
Qed.

Theorem jr_req_bound : forall sm ok x e, In e (snd (jr_run sm x ok)) ->
  ev_req e <= 256 * Z.of_nat (length x) + 20480.
Proof.
  intros sm ok x e Hin. pose proof (jr_req_bound_56 sm ok x e Hin) as H. lia.
Qed.

Corollary jr_req_most : forall sm ok x e, In e (snd (jr_run sm x ok)) ->
  ev_req e <= PJ_ALLOC_BOUND (Z.of_nat (length x)).
Proof. exact jr_req_bound. Qed.

(* The largest request of a trace. *)
Definition req_max (t : list ev) : Z := fold_right (fun e m => Z.max (ev_req e) m) 0 t.

(* The worked example of the internal file HARNESS-102-VS-MODEL.md section 6: x = {"a":"x"}, 9 bytes, all granted. The trace is the
   kids array (448 = 56 * 8), the keys array (64 = 8 * 8), the key "a" (2) and the string "x" (2): its largest request
   is 448, against PJ_ALLOC_BOUND(9) = 22784. No number is read, so strtod's model plays no part. *)
Definition ex_obj : list Z := [123; 34; 97; 34; 58; 34; 120; 34; 125].

Example req_max_obj : forall sm,
  (snd (jr_run sm ex_obj []), req_max (snd (jr_run sm ex_obj [])), PJ_ALLOC_BOUND (Z.of_nat (length ex_obj)))
  = ([EGrow 0 448; EGrow 0 64; EAlloc 2; EAlloc 2], 448, 22784).
Proof. intros sm. vm_compute. reflexivity. Qed.

(* reac-pw/fuzz_link, fuzz_link.asan (sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d; names
   from its unstripped twin, sha256 66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f): one membership
   fact per call of the malloc, calloc and free wrappers, over the allocation-trace universe of ACej.v (Tfib_universe)
   and, for the one call whose trace has a tail that the image does not fix (text_of's malloc), over the trace carrier
   of ACejUniv.v (Tfib_univ).
   The wrappers: __wrap_free 0x540c8 (j to ___interceptor_free 0x540d4), __wrap_malloc 0x540cc (j to
   ___interceptor_malloc 0x542a4), __wrap_calloc 0x540d0 (j to ___interceptor_calloc 0x544cc). The trace start (pc0) of
   each is the return address of the call of __sanitizer::StackTrace::GetCurrentPc (0x74b70) on the branch that unwinds
   (GetMallocContextSize() > 2): free 0x5420c (call at 0x54208), malloc 0x5436c (call at 0x54368), calloc 0x545a0 (call
   at 0x5459c).
   The calls: a sweep of every function of .text for a jal to 0x540c8 / 0x540cc / 0x540d0 / 0x540d4 / 0x542a4 / 0x544cc
   finds the three wrappers' jumps to the interceptors and 19 calls (each `jal ra`, so the return address is the call
   address + 4) besides libunwind's DwarfFDECache::add (0x8ad54, 0x8ad78), which ACej.v's header excludes:
     main 0x81d7c, 0x81dd0 (malloc), 0x81df4, 0x81f24 (free); target_run 0x8205c (malloc), 0x820f0 (free);
     LLVMFuzzerTestOneInput 0x82c74, 0x82c84 (calloc), 0x82e6c, 0x82e74, 0x83754, 0x8375c, 0x838d8, 0x83b88, 0x83b90
     (free); text_buf 0x863ec (malloc); text_of 0x87fec (malloc); fmemopen 0x96ab4, 0x96ac4 (malloc).
   A call's trace is unwind_of_chain pc0 ((sp, ra, s0) :: ch) (YG0d call_trace when frame0_ok holds, else [pc0]); ch
   is the frame chain read from s0, empty when s0 fails YG00 bad_next. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import ACej ACejUniv.
Import ListNotations.
Local Open Scope Z_scope.
(* The one-word traces, for the case where the caller's frame is at the stack top (call_trace's frame0_ok = false). *)
Lemma malloc_pc0_in : In [0x5436c] Tfib_universe.
Proof. apply memZL_In. vm_compute. reflexivity. Qed.
Lemma free_pc0_in : In [0x5420c] Tfib_universe.
Proof. apply memZL_In. vm_compute. reflexivity. Qed.
Lemma calloc_pc0_in : In [0x545a0] Tfib_universe.
Proof. apply memZL_In. vm_compute. reflexivity. Qed.
(* main (+0x50, +0xa4 malloc; +0xc8, +0x1f8 free) and target_run (+0x60 malloc, +0xf4 free): s0 holds an integer at
   each call (main: 2 from 0x81d54, and at +0x1f8 also 0xfb or the int result of target_run or target_alloc_count;
   target_run: its fourth argument, a size, from 0x82024), so the chain ends at the call. *)
Lemma drv_site_in : forall pcf ra : Z,
(pcf = 0x5436c /\ ra = 0x81d80) \/ (pcf = 0x5436c /\ ra = 0x81dd4) \/ (pcf = 0x5420c /\ ra = 0x81df8) \/
(pcf = 0x5420c /\ ra = 0x81f28) \/ (pcf = 0x5436c /\ ra = 0x82060) \/ (pcf = 0x5420c /\ ra = 0x820f4) ->
In [pcf; ra] Tfib_universe.
Proof. intros pcf ra H. decompose [or and] H; subst; apply memZL_In; vm_compute; reflexivity. Qed.
(* The trace over the frame chain itself: the record list ch read from s0 (YG00 fpchain) contributes its return
   addresses (YCbo's spine). *)
Lemma unwind_of_chain_spine : forall (pc0 sp ra s0 : Z) (ch : list (Z * Z * Z)),
unwind_of_chain pc0 ((sp, ra, s0) :: ch) =
firstn kUnwindMax (pc0 :: flat_map (fun r => if r =? pc0 then [] else [r]) (ra :: map (fun r => snd (fst r)) ch)).
Proof.
intros pc0 sp ra s0 ch. unfold unwind_of_chain. f_equal. cbn [flat_map]. f_equal. f_equal.
induction ch as [|[[a r] b] ch IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.
(* LLVMFuzzerTestOneInput's nine calls (calloc +0x4a0, +0x4b0, returns 0x82c78, 0x82c88; free +0x698, +0x6a0, +0xf80,
   +0xf88, +0x1104, +0x13b4, +0x13bc, returns 0x82e70, 0x82e78, 0x83758, 0x83760, 0x838dc, 0x83b8c, 0x83b94). s0 is
   its own frame (0x82810 `addi s0, sp, 0x1a0`; s0 is written again only by the epilogue load at 0x83bdc); the chain
   is its frame record, which holds the return into target_run 0x820c8 (the call at 0x820c4, CTX_LLVMFuzzerTestOneInput),
   when s0 passes bad_next (the frame lies below the stack top), else it is empty (b is that test). The record's next
   pointer is target_run's s0, an integer (its fourth argument, a size, from 0x82024), so the chain ends there. *)
Lemma llvmf_ctx : CTX_LLVMFuzzerTestOneInput = [[0x820c8]].
Proof. reflexivity. Qed.
Lemma llvmf_site_in : forall (pcf ra : Z) (b : bool),
(pcf = 0x545a0 /\ ra = 0x82c78) \/ (pcf = 0x545a0 /\ ra = 0x82c88) \/
(pcf = 0x5420c /\ ra = 0x82e70) \/ (pcf = 0x5420c /\ ra = 0x82e78) \/ (pcf = 0x5420c /\ ra = 0x83758) \/
(pcf = 0x5420c /\ ra = 0x83760) \/ (pcf = 0x5420c /\ ra = 0x838dc) \/ (pcf = 0x5420c /\ ra = 0x83b8c) \/
(pcf = 0x5420c /\ ra = 0x83b94) ->
In (firstn kUnwindMax (pcf :: flat_map (fun r => if r =? pcf then [] else [r]) (ra :: (if b then [0x820c8] else []))))
Tfib_universe.
Proof. intros pcf ra b H. decompose [or and] H; subst; destruct b; apply memZL_In; vm_compute; reflexivity. Qed.
(* text_buf's malloc call (+0x1c, return 0x863f0): text_buf saves s0 (0x863d8) and writes it only after the call
   (0x863f4), and its two callers are in LLVMFuzzerTestOneInput (0x835f4, 0x83600), so s0 at the call is
   LLVMFuzzerTestOneInput's frame and the chain is the one of llvmf_site_in (CTX_text_buf is not used). *)
Lemma text_buf_site_in : forall b : bool,
In (firstn kUnwindMax (0x5436c :: flat_map (fun r => if r =? 0x5436c then [] else [r])
(0x863f0 :: (if b then [0x820c8] else [])))) Tfib_universe.
Proof. intros b. destruct b; apply memZL_In; vm_compute; reflexivity. Qed.
(* musl fmemopen's malloc calls (+0x98, return 0x96ab8; +0xa8, return 0x96ac8, made only when the buffer argument is
   NULL, which mark_quietly never passes). fmemopen is reached only from mark_quietly (calls 0x831f8, 0x8347c in
   LLVMFuzzerTestOneInput), through __wrap_fmemopen 0x430a8 and ___interceptor_fmemopen 0x48024, which restores s0
   (0x48060) and jumps (0x48070, `jr t1`) to the address in __interception::real_fmemopen (0xa3780 in .data, 0x96a1c,
   the only aligned data word of the image that holds it). mark_quietly keeps its second argument in s0 (0x883e8
   `mv s0, a1`) and fmemopen writes s0 only after the two calls (0x96acc). That argument (reac-pw fuzz/fuzz_link.c:153,
   726, 759) is NULL, a string literal or an element of the static array g_names (fuzz_link.c:83, 102-110), so s0 is
   0 or an address of the image, below sp: s0 fails bad_next and the chain ends at the call. *)
Lemma mark_quietly_fmemopen_in : forall ra : Z, (ra = 0x96ab8 \/ ra = 0x96ac8) -> In [0x5436c; ra] Tfib_universe.
Proof. intros ra Hra. destruct Hra as [-> | ->]; apply memZL_In; vm_compute; reflexivity. Qed.
Lemma mark_quietly_fmemopen_chain_in : forall (ra sp s0 : Z), (ra = 0x96ab8 \/ ra = 0x96ac8) ->
In (unwind_of_chain 0x5436c [(sp, ra, s0)]) Tfib_universe.
Proof. intros ra sp s0 Hra. destruct Hra as [-> | ->]; apply memZL_In; vm_compute; reflexivity. Qed.
(* text_of's malloc call (+0x22c, return 0x87ff0): s0 holds text_of's second argument (0x87e04 `mv s0, a1`), a slot
   of LLVMFuzzerTestOneInput's frame, so the chain read from it is not fixed by the image (ACejUniv.v's header). Every
   such trace is [0x5436c; 0x87ff0] followed by a tail: it has the wild prefix of Tfib_univ, so it is in the carrier
   (inU), and the depot admits it while the depot has room for one more wild trace. When the chain is empty the trace
   is the fixed row [0x5436c; 0x87ff0], admitted with no room. No fixed row (In) covers the other cases. *)
Lemma text_of_malloc_inU : forall (sp s0 : Z) (ch : list (Z * Z * Z)),
inU Tfib_univ (unwind_of_chain 0x5436c ((sp, 0x87ff0, s0) :: ch)).
Proof.
intros sp s0 ch. split.
- unfold unwind_of_chain. apply firstn_le_length.
- right. rewrite Tfib_univ_wild.
  exists [0x5436c; 0x87ff0], (firstn 28 (flat_map (fun r => match r with (_, ra, _) => if ra =? 0x5436c then [] else [ra] end) ch)).
  split; [left; reflexivity | reflexivity].
Qed.
Lemma text_of_malloc_admits : forall (sp s0 : Z) (ch : list (Z * Z * Z)) (s : astate),
(length (wild_part Tfib_univ (st_depot s)) < u_wmax Tfib_univ)%nat ->
admits Tfib_univ (unwind_of_chain 0x5436c ((sp, 0x87ff0, s0) :: ch)) s.
Proof. intros sp s0 ch s H. split; [apply text_of_malloc_inU | right; right; exact H]. Qed.
Lemma text_of_malloc_admits_nil : forall (sp s0 : Z) (s : astate),
admits Tfib_univ (unwind_of_chain 0x5436c [(sp, 0x87ff0, s0)]) s.
Proof.
intros sp s0 s. change (admits Tfib_univ [0x5436c; 0x87ff0] s).
exact (admits_fix Tfib_univ [0x5436c; 0x87ff0] s Tfib_univ_ok Tfib_univ_wild_fixed).
Qed.
(* Every row of the universe is the trace of one of the calls above. *)
Lemma Tfib_universe_sites : forall t, In t Tfib_universe ->
In t ([[0x5420c]; [0x5436c]; [0x545a0]] ++ TRACES_main ++ TRACES_target_run ++ TRACES_LLVMFuzzerTestOneInput ++
TRACES_text_buf ++ TRACES_text_of ++ TRACES_fmemopen).
Proof.
intros t H. apply memZL_In.
exact (allb_In (fun t => memZL t ([[0x5420c]; [0x5436c]; [0x545a0]] ++ TRACES_main ++ TRACES_target_run ++
TRACES_LLVMFuzzerTestOneInput ++ TRACES_text_buf ++ TRACES_text_of ++ TRACES_fmemopen)) Tfib_universe t
ltac:(vm_compute; reflexivity) H).
Qed.

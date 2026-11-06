From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* libreac/fuzz_pcap v1.9.0, fuzz_pcap.asan: one membership fact per call of the malloc and free wrappers, in the forms the
   per-function specifications of cgif_file_fuzzer take them (lib/A/ACeb.v:39, lib/A/ACf5.v:155-165, lib/YE01.v:201, :217),
   over the allocation-trace universe of ACej.v. The allocator entries' trace start (pc0, the return address of the stack-pc
   read on the interceptors' trace branch): malloc 0x52e74, free 0x52d14. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import ACej.
Import ListNotations.
Local Open Scope Z_scope.
(* The one-word traces, for the case where the caller's frame is at the stack top (call_trace's frame0_ok = false). *)
Lemma malloc_pc0_in : In [(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z)] Tfib_universe.
Proof. apply memZL_In. vm_compute. reflexivity. Qed.
Lemma free_pc0_in : In [(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z)] Tfib_universe.
Proof. apply memZL_In. vm_compute. reflexivity. Qed.
(* main (+0x50, +0xa4 malloc; +0xc8, +0x1f8 free) and target_run (+0x60 malloc, +0xf4 free): s0 holds an integer, so
   the chain ends at the call. *)
Lemma drv_site_in : forall pcf ra : Z,
(pcf = (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z) /\ ra = (symaddr (Symbols.Asan.s_main + 0x54)%Z)) \/ (pcf = (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z) /\ ra = (symaddr (Symbols.Asan.s_main + 0xa8)%Z)) \/ (pcf = (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z) /\ ra = (symaddr (Symbols.Asan.s_main + 0xcc)%Z)) \/
(pcf = (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z) /\ ra = (symaddr (Symbols.Asan.s_main + 0x1fc)%Z)) \/ (pcf = (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z) /\ ra = (symaddr (Symbols.Asan.s_target_run + 0x64)%Z)) \/ (pcf = (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z) /\ ra = (symaddr (Symbols.Asan.s_target_run + 0xf8)%Z)) ->
In [pcf; ra] Tfib_universe.
Proof. intros pcf ra H. decompose [or and] H; subst; apply memZL_In; vm_compute; reflexivity. Qed.
(* LLVMFuzzerTestOneInput's five calls (free +0x2bc, +0x944, +0x94c; malloc +0x178, +0x2f0). s0 is its own frame; its
   record holds the return into target_run 0x80634 when the frame lies below the stack top, else the chain ends there
   (b is that test, spZ + 16 <? ly_top, as in ACf5.v:164). *)
Lemma llvmf_site_in : forall (pcf ra : Z) (b : bool),
(pcf = (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z) /\ ra = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x2c0)%Z)) \/ (pcf = (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z) /\ ra = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x948)%Z)) \/ (pcf = (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z) /\ ra = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x950)%Z)) \/
(pcf = (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z) /\ ra = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x17c)%Z)) \/ (pcf = (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z) /\ ra = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x2f4)%Z)) ->
In (firstn kUnwindMax (pcf :: flat_map (fun r => if r =? pcf then [] else [r]) (ra :: (if b then [(symaddr (Symbols.Asan.s_target_run + 0xcc)%Z)] else []))))
Tfib_universe.
Proof. intros pcf ra b H. decompose [or and] H; subst; destruct b; apply memZL_In; vm_compute; reflexivity. Qed.
(* The contexts LLVMFuzzerTestOneInput hands to its callees (the ACf5.v:133 form): the return address of the call, with
   and without the return into target_run. *)
Lemma llvmf_callee_ctx : forall (site : Z) (L : list (list Z)),
((site = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x1d8)%Z) \/ site = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x900)%Z)) /\ L = CTX_pcap_source_open) \/
((site = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x32c)%Z) \/ site = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x7dc)%Z) \/ site = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x918)%Z) \/ site = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x938)%Z)) /\ L = CTX_pcap_source_next) \/
((site = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x8e4)%Z) \/ site = (symaddr (Symbols.Asan.s_LLVMFuzzerTestOneInput + 0x924)%Z)) /\ L = CTX_pcap_source_close) ->
In [site] L /\ In [site; (symaddr (Symbols.Asan.s_target_run + 0xcc)%Z)] L.
Proof. intros site L H. decompose [or and] H; subst; split; apply memZL_In; vm_compute; reflexivity. Qed.
(* musl fmemopen's malloc calls (+0x98 return 0x8e90c; +0xa8 return 0x8e91c, never made by the harness), in the form of
   ACeb.v:39: s0 at the call is pcap_source_open's frame pointer, so the context is CTX_pcap_source_open. ACeb.v:38's
   HDEEP (2 <= length of the context) is not carried: it serves cgif_raw_newgif's own frame push (ACb8.v:146-149, :347,
   :360-363), fmemopen pushes no frame record before its mallocs, and afmemopen_spec does not ask for it. *)
Lemma fmemopen_malloc_ctx_in : forall (ra : Z) (c : list Z), (ra = (symaddr (Symbols.Asan.s_fmemopen + 0x9c)%Z) \/ ra = (symaddr (Symbols.Asan.s_fmemopen + 0xac)%Z)) -> In c CTX_pcap_source_open ->
In (firstn kUnwindMax ((symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z) :: flat_map (fun r => if r =? (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z) then [] else [r]) (ra :: c))) Tfib_universe.
Proof.
intros ra c Hra Hc. apply memZL_In.
refine (allb_In (fun c => memZL (firstn kUnwindMax ((symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z) :: flat_map (fun r => if r =? (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z) then [] else [r]) (ra :: c)))
Tfib_universe) CTX_pcap_source_open c _ Hc).
destruct Hra as [-> | ->]; vm_compute; reflexivity.
Qed.
(* The same fact over the frame chain itself: the record list ch read from s0 (YG00 fpchain), whose return addresses
   (YCbo's spine) are a context of pcap_source_open. This is the trace amalloc_realizes records when frame0_ok holds. *)
Lemma unwind_of_chain_spine : forall (pc0 sp ra s0 : Z) (ch : list (Z * Z * Z)),
unwind_of_chain pc0 ((sp, ra, s0) :: ch) =
firstn kUnwindMax (pc0 :: flat_map (fun r => if r =? pc0 then [] else [r]) (ra :: map (fun r => snd (fst r)) ch)).
Proof.
intros pc0 sp ra s0 ch. unfold unwind_of_chain. f_equal. cbn [flat_map]. f_equal. f_equal.
induction ch as [|[[a r] b] ch IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma fmemopen_malloc_chain_in : forall (ra sp s0 : Z) (ch : list (Z * Z * Z)), (ra = (symaddr (Symbols.Asan.s_fmemopen + 0x9c)%Z) \/ ra = (symaddr (Symbols.Asan.s_fmemopen + 0xac)%Z)) ->
In (map (fun r => snd (fst r)) ch) CTX_pcap_source_open ->
In (unwind_of_chain (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z) ((sp, ra, s0) :: ch)) Tfib_universe.
Proof. intros ra sp s0 ch Hra Hc. rewrite unwind_of_chain_spine. exact (fmemopen_malloc_ctx_in ra _ Hra Hc). Qed.
(* musl fclose's two frees (+0xa0, +0xa8; s0 is the FILE pointer): the premises of afclose_spec (YE01.v:201). *)
Lemma fclose_free_in : In [(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.Asan.s_fclose + 0xa4)%Z)] Tfib_universe /\ In [(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.Asan.s_fclose + 0xac)%Z)] Tfib_universe.
Proof. split; apply memZL_In; vm_compute; reflexivity. Qed.
(* musl __fdopen's malloc (+0x48, from fopen, never made by the harness; s0 is the mode string): the premise of
   afopen_spec (YE01.v:217). *)
Lemma fdopen_malloc_in : In [(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.Asan.s_fdopen + 0x4c)%Z)] Tfib_universe.
Proof. apply memZL_In. vm_compute. reflexivity. Qed.
(* Every row of the universe is the trace of one of the calls above. *)
Lemma Tfib_universe_sites : forall t, In t Tfib_universe ->
In t ([[(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z)]] ++ TRACES_main ++ TRACES_target_run ++ TRACES_LLVMFuzzerTestOneInput ++
TRACES_fmemopen ++ TRACES_fclose ++ TRACES_fdopen).
Proof.
intros t H. apply memZL_In.
exact (allb_In (fun t => memZL t ([[(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z)]] ++ TRACES_main ++ TRACES_target_run ++ TRACES_LLVMFuzzerTestOneInput ++
TRACES_fmemopen ++ TRACES_fclose ++ TRACES_fdopen)) Tfib_universe t ltac:(vm_compute; reflexivity) H).
Qed.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Export ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Export rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
Import ListNotations.
Open Scope Z_scope.

Module ExF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.

(* Footprint form (D) of the checked fill helper __asan_memset of build B (asan-ubsan) at ASAN_MEMSET = 0x52600.

   FORM (ROUTE1.md (a working note, not in this delivery), which USES
   a working branch 71968bf11a; and a Theorem Labs lane's rewalk-F-policy.md (a working note, not in this delivery)):
   the binders, the premises and the post of asan_memset_contract (lib/B/Prog/asan_memset_c.v) are repeated
   UNCHANGED -- that file is frozen and this one does not touch it -- with
     - the footprint RNG universally quantified, FIRST among the binders;
     - `RngBytes.rng_bytes RNG` FIRST among the footprint premises (a Theorem Labs lane, 16:31Z): an access may straddle two
       adjacent rng ranges, and the owner's proof of this contract needs the footprint byte-wise for the walk;
     - one `rng` premise per region the call reads or writes, LAST, after every original premise;
     - the run an ExecF.evtF on RNG instead of an Exec.evt.
   Apply it with NAMED arguments (`asan_memset_contract_F RNG:=...`), not positionally.

   THE REGIONS, and why each one is in the list:
     - the image [IMG_LO, IMG_HI): the code fetched, the GOT cells and the runtime's own cells. The runtime
       words RT_LO = 0xa08f0 .. RT_HI = 0xaa3b8 (lib/B/AsanRT.v) that asan_cells speaks about (INITED, REPLACE,
       CANPOISON, HIEND, MIDBEG, MIDEND, REAL_MEMSET, ...) lie INSIDE [IMG_LO, IMG_HI), so they need no premise
       of their own (rewalk-F-policy.md asks for "runtime words as one rng RNG RT_LO (RT_HI - RT_LO)" only
       where they fall outside the image; here RT_HI < IMG_HI).
     - the helper's own stack window [sp - ASAN_MEMSET_K, sp): exactly the second range the post's `munch`
       allows the call to write.
     - the destination [D, D + N): the N bytes written. The fill byte arrives in the register a1, so this
       helper has ONE buffer, where the copy helper has two.
     - the shadow of the destination, as an 8-ALIGNED shadow WORD span (see sh_word_rng, rng_asan.v): the one
       range the helper's ASan check reads on the destination.
     - the shadow of the helper's own stack frame [sp - ASAN_MEMSET_K, sp), as an 8-ALIGNED shadow WORD span
       (a Theorem Labs lane, 10:37Z): the helper may READ the shadow bytes of its own frame. The post's `munch`
       [(D, D + N); (sp - K, sp)] rules out shadow WRITES, not shadow reads, so the footprint must hold them.

   PORT.  This file is lib/A/Prog/asan_memset_cF.v with these changes only: the namespace lib.A -> lib.B, and the
   build-B constants in this comment.  The names are exactly lib/A's.  Build B's frozen asan_memset_c.v and build
   A's differ only in ASAN_MEMSET (0x52600 here, 0x524c4 in A); ASAN_MEMSET_K = 2208 in both, so the frozen
   premises and the post are the identical text.  IMG_LO := 0x10000 and IMG_HI := 0x5fe000 (lib/B/Prog/ImgBounds.v)
   hold for build B: the build-B image runs from 0x10000 to 0x5fdf30 (the last PT_LOAD end of fuzz_ctrl.asan-ubsan),
   lib/B/ZImage.v's last region ends at 0x5fe000, and RT_GT = ASAN_GT = 0x5fe000 (lib/B/AsanRT.v,
   lib/B/Prog/asan_stack_malloc_c.v).  This file replaces the inline build-B copy of asan_memset_contract_F that
   lib/B/Prog/Slot/ASegAF.v stated (which lacked the rng_bytes premise).

   DRAFT. rule 24: no function proved. a Theorem Labs lane owns asan_memset_contract_F and proves it; this file only
   STATES it, in new files, with the owner's files untouched (rewalk-F-policy.md (a working note, not in this delivery)). *)

Definition asan_memset_contract_F : Prop :=
  forall (RNG : ExF.footprint)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte) (lo : Z),
  let D := bv_unsigned a0 in let N := bv_unsigned a2 in
  rw_cells rsegs m D [CB (Z.to_nat N) junk] ->
  (N <= 2^40)%Z -> addressable m D N -> end_in_app D N ->
  (N = 0 \/ app_mem (D + 7))%Z -> (D + N <= RT_LO \/ RT_HI <= D)%Z ->
  (D + N <= bv_unsigned sp - ASAN_MEMSET_K \/ bv_unsigned sp <= D)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + ASAN_MEMSET_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
  (* the footprint premises: the footprint is byte-wise, then one per region the call reads or writes *)
  RngBytes.rng_bytes RNG ->
  ExF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  ExF.rng RNG (bv_unsigned sp - ASAN_MEMSET_K) ASAN_MEMSET_K ->
  ExF.rng RNG D N ->
  sh_word_rng RNG D N ->
  sh_word_rng RNG (bv_unsigned sp - ASAN_MEMSET_K) ASAN_MEMSET_K ->
  ExF.evtF rsegs RNG (asan_memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMSET) fc None m (seg_rom rsegs)).

(* ---- the two forms are linked: the frozen contract is the footprint form at RNG_all ---- *)

Lemma asan_memset_contract_of_F : asan_memset_contract_F -> asan_memset_contract.
Proof.
  intros HF. unfold asan_memset_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk lo.
  cbv zeta.
  intros Hrw HN HaD HeD H7 HRT HDsp Hstk HK Hlo Hsp Hac Hshrw Hmi.
  assert (HaD' := HaD).
  unfold addressable in HaD'.
  destruct HaD' as (HD0 & HND & HDN & _).
  eapply ExF.evtF_evt.
  (* eapply: `junk` occurs in no conclusion, so it is an evar that rw_cells closes. *)
  eapply (HF ExF.RNG_all); try eassumption.
  - (* RNG_all is byte-wise; ctrl's lib/Lib/RngBytes.v has no rng_bytes_all lemma, so its one-line proof is here *)
    intros ? ? _ _ _. exact I.
  - pose proof two64 as H64. apply ExF.rng_all; cbv [IMG_LO IMG_HI]; lia.
  - pose proof two64 as H64. apply ExF.rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - pose proof two64 as H64. apply ExF.rng_all; unfold APPMEM_END in *; lia.
  - apply sh_word_rng_all; assumption.
  - apply sh_word_rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG, APPMEM_END in *; lia.
Qed.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Export ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Export rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
Import ListNotations.
Open Scope Z_scope.

Module ExF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.

(* Footprint form (D) of the checked copy helper __asan_memcpy at ASAN_MEMCPY = 0x52028.

   FORM (ROUTE1.md (a working note, not in this delivery), which USES
   a working branch 71968bf11a; and a Theorem Labs lane's rewalk-F-policy.md (a working note, not in this delivery)):
   the binders, the premises and the post of asan_memcpy_contract (asan_memcpy_c.v) are repeated UNCHANGED --
   that file is frozen and this one does not touch it -- with
     - the footprint RNG universally quantified, FIRST among the binders;
     - `RngBytes.rng_bytes RNG` FIRST among the footprint premises (a Theorem Labs lane, 16:31Z): an access may straddle two
       adjacent rng ranges, and the owner's proof of this contract needs the footprint byte-wise for the walk;
     - one `rng` premise per region the call reads or writes, LAST, after every original premise;
     - the run an ExecF.evtF on RNG instead of an Exec.evt.
   Apply it with NAMED arguments (`asan_memcpy_contract_F RNG:=...`), not positionally.

   THE REGIONS, and why each one is in the list:
     - the image [IMG_LO, IMG_HI): the code fetched, the GOT cells and the runtime's own cells. The runtime
       words RT_LO = 0x9fad0 .. RT_HI = 0xa9578 (lib/A/AsanRT.v) that asan_cells speaks about (INITED, REPLACE, CANPOISON,
       HIEND, MIDBEG, MIDEND, REAL_MEMCPY, ...) lie INSIDE [IMG_LO, IMG_HI), so they need no premise of
       their own (rewalk-F-policy.md asks for "runtime words as one rng RNG RT_LO (RT_HI - RT_LO)" only
       where they fall outside the image; here RT_HI < IMG_HI).
     - the helper's own stack window [sp - ASAN_MEMCPY_K, sp): exactly the second range the post's `munch`
       allows the call to write.
     - the destination [D, D + N) and the source [S, S + N): the N bytes written and the N bytes read.
     - the shadow of the destination and the shadow of the source, each as an 8-ALIGNED shadow WORD span
       (see sh_word_rng, rng_asan.v): the two ranges the helper's ASan check reads.
     - the shadow of the helper's own stack frame [sp - ASAN_MEMCPY_K, sp), as an 8-ALIGNED shadow WORD span
       (a Theorem Labs lane, 10:37Z): the helper may READ the shadow bytes of its own frame. The post's `munch`
       [(D, D + N); (sp - K, sp)] rules out shadow WRITES, not shadow reads, so the footprint must hold them.

   DRAFT. rule 24: no function proved. a Theorem Labs lane owns asan_memcpy_contract_F and proves it; this file only
   STATES it, in new files, with the owner's files untouched (rewalk-F-policy.md (a working note, not in this delivery)). *)

Definition asan_memcpy_contract_F : Prop :=
  forall (RNG : ExF.footprint)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte) (lo : Z),
  let D := bv_unsigned a0 in let S := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m S src -> length src = Z.to_nat N ->
  rw_cells rsegs m D [CB (Z.to_nat N) junk] ->
  (D = S \/ (S + N <= D)%Z \/ (D + N <= S)%Z) ->
  (N <= 2^40)%Z ->
  addressable m S N -> addressable m D N -> end_in_app S N -> end_in_app D N ->
  (N = 0 \/ app_mem (S + 7) /\ app_mem (D + 7))%Z -> (D + N <= RT_LO \/ RT_HI <= D)%Z ->
  (D + N <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= D)%Z -> (S + N <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= S)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + ASAN_MEMCPY_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
  (* the footprint premises: the footprint is byte-wise, then one per region the call reads or writes *)
  RngBytes.rng_bytes RNG ->
  ExF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  ExF.rng RNG (bv_unsigned sp - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
  ExF.rng RNG D N -> ExF.rng RNG S N ->
  sh_word_rng RNG D N -> sh_word_rng RNG S N ->
  sh_word_rng RNG (bv_unsigned sp - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
  ExF.evtF rsegs RNG (asan_memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMCPY) fc None m (seg_rom rsegs)).

(* ---- the two forms are linked: the frozen contract is the footprint form at RNG_all ---- *)

Lemma asan_memcpy_contract_of_F : asan_memcpy_contract_F -> asan_memcpy_contract.
Proof.
  intros HF. unfold asan_memcpy_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m src junk lo.
  cbv zeta.
  intros Hsrc Hlen Hrw Hov HN HaS HaD HeS HeD H7 HRT HDsp HSsp Hstk HK Hlo Hsp Hac Hshrw Hmi.
  assert (HaS' := HaS). assert (HaD' := HaD).
  unfold addressable in HaS', HaD'.
  destruct HaS' as (HS0 & HNS & HSN & _).
  destruct HaD' as (HD0 & HND & HDN & _).
  eapply ExF.evtF_evt.
  (* eapply: `junk` occurs in no conclusion, so it is an evar that rw_cells closes. *)
  eapply (HF ExF.RNG_all); try eassumption.
  - (* RNG_all is byte-wise; ctrl's lib/Lib/RngBytes.v has no rng_bytes_all lemma, so its one-line proof is here *)
    intros ? ? _ _ _. exact I.
  - pose proof two64 as H64. apply ExF.rng_all; cbv [IMG_LO IMG_HI]; lia.
  - pose proof two64 as H64. apply ExF.rng_all; unfold ASAN_MEMCPY_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - pose proof two64 as H64. apply ExF.rng_all; unfold APPMEM_END in *; lia.
  - pose proof two64 as H64. apply ExF.rng_all; unfold APPMEM_END in *; lia.
  - apply sh_word_rng_all; assumption.
  - apply sh_word_rng_all; assumption.
  - apply sh_word_rng_all; unfold ASAN_MEMCPY_K, HIGHMEM_BEG, APPMEM_END in *; lia.
Qed.

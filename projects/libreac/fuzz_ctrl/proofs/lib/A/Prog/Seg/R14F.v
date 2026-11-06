(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module names changed; 350 of its 474 lines of code are new or changed and 1378 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R14.v blob 471ba94eddd7 at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: r14_head_of_F re-derives R14.r14_head at ExecF.RNG_all; r14_head_of_F_verbatim checks by constr_eq that
   its type is the type of R14.r14_head. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of R14.v's run lemmas.
   r14_head (R14.v:671) IS re-run here: the first 32-byte sum loop from its head 0x81768 at turn i, plus the
   low-byte test, to 0x81830. Same script over StepF (B3LoopF.b3_loop1_F and B3LoopF.b3_tail1_F in place of
   B3Loop.b3_loop1 / b3_tail1), same post-state predicate.
   Regions (rule (a): the regions the lemma's own premises name): the 32 frame bytes [phi + 18, phi + 50) of its
   `bytes_at rsegs m (phi + 18) xs` / `addressable m (phi + 18) 32` premises, and the shadow bytes of those 32
   bytes, [(phi + 18) / 8 + ASAN_K, (phi + 49) / 8 + ASAN_K], read by the instrumented check of each turn. The run
   writes nothing.

   r14_call (R14.v:712) is re-run in BOTH agreed forms, side by side.
   (A) THE ONE TEXT. r14_call_F cites a Theorem Labs lane's `reac_box_catalogue_match_contract_F` BY NAME in the plain
   contract's premise position (lib/A/Prog/reac_box_catalogue_match_c.v:152 (an earlier version, blob ccd3e1f3c75, not in this delivery) (from a working branch 901563ab46f),
   the text of record; its IMG_HI needs the bcmp_wrap_c.v of record (an earlier version, blob
   270745d3d2e, not in this delivery)), and passes that contract's footprint premises through unchanged,
   instantiated at this call's values (f := phi, len := len, S := S, FS := FS). Two of them are forall-memory
   forms and are passed through as they stand: `rng_bytes RNG` (lib/Lib/RngBytes.v) and
   `rng_fp_cm RNG (normalize rsegs m) (bv_unsigned tp) FS`, the latter at the NORMALIZED memory, because the call
   itself runs there (R14.v's own proof moves every other premise to `normalize rsegs m` the same way, through
   MemNorm; the lift back is MemNormF.evtF_normalize_ro, the evtF form of MemNorm.evt_normalize). r14_call_of_F
   re-derives R14.r14_call at ExecF.RNG_all with the _F contract in the first premise, and
   r14_call_of_F_verbatim pins everything after that premise to R14.r14_call's text (the Seg/F30F.v form).
   (B) THE SPLIT the glue consumes (spec "SPLIT STRETCHES", a Theorem Labs lane 00:45Z; shape fixed by the glue owner
   a Theorem Labs lane 00:48Z and 03:44Z): a Theorem Labs lane does not discharge a footprint contract for
   reac_box_catalogue_match, it cuts at the call and puts a Theorem Labs lane's cgif-form treac_box_catalogue_match_spec
   there, so the same run is ALSO given as two stretches with no callee contract in them:
     r14_call_pre_F  [0x81830, 0x84498): `mv a0,s8 ; mv a1,s2 ; jal 84498`, ending at the callee ENTRY with
                     ra = 0x8183c. Three register instructions, NO memory access, so NO rng premise is appended.
     r14_call_post_F at the RETURN pc 0x8183c: a concrete universally quantified start with the canonical register
                     map `Regs6ss.mkR_of regs` (ra not mentioned), whose premises are exactly the machine-level
                     facts R14.v's own script holds right after it applies the contract (the register map's slots,
                     and munch / wmono / ro_agree / stk / asan_cells / shadow_rw / addressable / fp of the memory
                     it reached), each as the source states it; the callee post's existentials are universally
                     bound variables here. It takes no rng premise either: the stretch is empty (zero steps).
                     Its F and fc are binders, not fp_regs / fp_csr, so that r14_call_of_pre_post below can apply
                     it at R14.r14_call's own F and fc; the glue's fp_regs / fp_csr instance is a special case.
     r14_call_of_pre_post: pre_F and post_F at ExecF.RNG_all, with the PLAIN reac_box_catalogue_match_contract in
                     R14.r14_call's own first-premise position, re-derive R14.r14_call; r14_call_of_pre_post_verbatim
                     pins it to R14.r14_call's type by constr_eq (the no-weakening check). The middle piece is
                     R14.v's own contract application through MemNorm.evt_normalize, cut from its script unchanged.
   R14.v's code is unchanged since release c5e779efe8c (comments edited); it differs from the source blob above: 17 of its code lines changed or removed, 17 added. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcMatch.
(* rt_addressable_bound (the bounds of an `addressable` range) for r14_head_of_F at RNG_all; the callee's contract
   file, a Theorem Labs lane's blob ccd3e1f3c75 at a working branch 901563ab46f (the text of record: the auditor
   a Theorem Labs lane's signed text with the header's catalogue address corrected to CM_T), for BOTH the plain
   reac_box_catalogue_match_contract and reac_box_catalogue_match_contract_F, and for CM_K / CM_T / want /
   rng_fp_cm and the W / D / tls names. That text states its image premise with the LITERALS
   `ExecF.rng RNG 0x10000 0x5ee000`, so r14_call_F passes it through in that spelling; IMG_LO / IMG_HI come
   from bcmp_wrap_c.v (blob 270745d3d2e) and are convertible with the literals (IMG_HI = Contract.GT = 0x5fe000). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_box_catalogue_match_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import B3Loop B3LoopF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R14.
(* Last: StepF's step / if_false / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* R14.v imports lib/A/Reusable/YK11 at the top of its preamble, so the `seg_rom` of R14.r14_head's statement is
   YK11's, not Img0's. Import it last here too (as Seg/F5F.v does), so the twin and the corollary state the same
   rom term; YK11's seg_rom is convertible with Img0's, which is how R14.v's own proof applies B3Loop.b3_loop1. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import ListNotations.
Open Scope Z_scope.

(* The run of R14 from the loop head at index i to 0x81830, with a0 = 0, under a footprint RNG. *)
Lemma r14_head_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) ->
    a2 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a3 = Z_to_bv 64 (32 - Z.of_nat i) ->
    s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> bytes_at rsegs m (phi + 18) xs -> addressable m (phi + 18) 32 ->
    blocksum xs = 0 ->
    ExecF.rng RNG (phi + 18) 32 ->
    ExecF.rng RNG ((phi + 18) / 8 + ASAN_K) ((phi + 49) / 8 - (phi + 18) / 8 + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81768) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi xs i E0 E1 E2 E3 E10 Hi Hlen HB AD HS RB RS.
  assert (RS' : ExecF.rng RNG ((phi + 18) / 8 + ASAN_K) ((phi + 18 + 31) / 8 - (phi + 18) / 8 + 1))
    by (replace (phi + 18 + 31) with (phi + 49) by lia; exact RS).
  pose proof (psum_range xs 32) as PR. change (Z.of_nat 32) with 32 in PR.
  eapply ExecF.evtF_cut.
  { apply (b3_loop1_F RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m (phi + 18) xs i);
      [ rewrite E0; f_equal; lia | exact E1 | rewrite E2; f_equal; lia | exact E3 | exact E10 | exact Hi
      | exact Hlen | exact HB | exact AD | exact RB | exact RS' ]. }
  intros ms' (a4' & a5' & ->).
  replace (phi + 18 + 32) with (phi + 50) by lia.
  eapply ExecF.evtF_cut.
  { apply (b3_tail1_F RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 (psum xs 32))
             (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m (psum xs 32) eq_refl ltac:(lia) (b3_sum_low _ HS)). }
  intros ms' ->. apply ExecF.evtF_done. cbv beta. exists a4', a5'. reflexivity.
Qed.

(* R14.r14_head's statement as a corollary (ExecF.evtF_evt of r14_head_F at RNG_all, each rng premise by
   ExecF.rng_all; the bounds come from the lemma's own `addressable m (phi + 18) 32`). *)
Lemma r14_head_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) ->
    a2 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a3 = Z_to_bv 64 (32 - Z.of_nat i) ->
    s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> bytes_at rsegs m (phi + 18) xs -> addressable m (phi + 18) 32 ->
    blocksum xs = 0 ->
    evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81768) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi xs i E0 E1 E2 E3 E10 Hi Hlen HB AD HS.
  destruct (rt_addressable_bound m (phi + 18) 32 AD) as (Hq & _ & Hq47).
  eapply ExecF.evtF_evt, (r14_head_F ExecF.RNG_all); try eassumption;
    apply ExecF.rng_all; try unfold ASAN_K in *; Z.div_mod_to_equations; lia.
Qed.

(* The pin: r14_head_of_F's statement is R14.r14_head's, term for term (constr_eq: syntactic, not up to
   conversion). *)
Example r14_head_of_F_verbatim : True.
Proof.
  let a := type of R14.r14_head in let b := type of r14_head_of_F in constr_eq a b.
  exact I.
Qed.

Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module CMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match_c.

(* ---- (A) The run of [0x81830, 0x8183c) under a footprint RNG and the callee's footprint contract, cited by name.
   The run itself touches no memory; every rng premise below is the callee's own, instantiated at f := phi,
   len := len, S := S, FS := FS, in the order reac_box_catalogue_match_contract_F states them. ---- *)
Lemma r14_call_F : CMC.reac_box_catalogue_match_contract_F ->
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 50 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat -> bytes_at rsegs m phi fb -> (phi + 50 <= S - CM_K \/ S <= phi) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> 6283264 <= FS -> addressable m (S - CM_K) CM_K ->
    addressable m phi 50 -> app_mem (phi + 50) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    (* the callee's footprint premises, passed through unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (S - CM_K) CM_K ->
    (50 <= len -> ExecF.rng RNG phi 50 /\
                  ExecF.rng RNG (8 * (shadow_addr phi / 8))
                    (8 * (shadow_addr (phi + 49) / 8) + 8 - 8 * (shadow_addr phi / 8))) ->
    ExecF.rng RNG (8 * (shadow_addr CM_T / 8))
      (8 * (shadow_addr (CM_T + 3255) / 8) + 8 - 8 * (shadow_addr CM_T / 8)) ->
    ExecF.rng RNG (8 * (shadow_addr REAC_CTRL_PARSE_BC / 8))
      (8 * (shadow_addr (REAC_CTRL_PARSE_BC + 5) / 8) + 8 - 8 * (shadow_addr REAC_CTRL_PARSE_BC / 8)) ->
    ExecF.rng RNG (shadow_addr (S - CM_K)) (shadow_addr S - shadow_addr (S - CM_K)) ->
    CMC.rng_fp_cm RNG (normalize rsegs m) (bv_unsigned tp) FS ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x8183c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x8183c) fc None m' (seg_rom rsegs) /\
         munch (r14_W S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs)).
Proof.
  intros CMCF RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb -> -> -> Hphi0 Hphi50 Hlen HS Hmod HKS HST HROM Hfb HFB HAPART HROc HROA HAC HSW
    Hhi Hsp HFSgt HADW HADf HAPP50 HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS
    RBYT RIMG RWIN RF50 RCAT RBC RSHW RFPCM.
  assert (HHMB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HK : CM_K = 9136) by reflexivity.
  (* the premises on the normalized memory (R14.v's own transports) *)
  pose proof (mem_rel_normalize rsegs m HROA) as REL.
  assert (HST0 : stk rsegs (normalize rsegs m) (S - CM_K) S)
    by exact (proj1 (R14.r14_rel_stk m _ (S - CM_K) S REL ltac:(lia) ltac:(lia)) HST).
  assert (HFB0 : bytes_at rsegs (normalize rsegs m) phi fb) by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HFB).
  assert (HROc0 : forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs (normalize rsegs m) (wa a) = seg_rom rsegs (wa a))
    by (intros a Ha; rewrite <- (mrd_rel rsegs m _ _ REL); exact (HROc a Ha)).
  assert (HMI0 : mem_inv rsegs (normalize rsegs m)) by apply mem_inv_normalize.
  assert (HAC0 : asan_cells (normalize rsegs m)) by exact (proj1 (R14.r14_rel_cells m _ REL) HAC).
  assert (HSW0 : shadow_rw (normalize rsegs m)) by exact (proj1 (R14.r14_rel_sw m _ REL) HSW).
  assert (HADW0 : addressable (normalize rsegs m) (S - CM_K) CM_K)
    by exact (proj1 (R14.r14_rel_ad m _ _ _ REL) HADW).
  assert (HADf0 : addressable (normalize rsegs m) phi 50) by exact (proj1 (R14.r14_rel_ad m _ _ _ REL) HADf).
  assert (HADT0 : addressable (normalize rsegs m) CM_T 3256) by exact (proj1 (R14.r14_rel_ad m _ _ _ REL) HADT).
  assert (HADB0 : addressable (normalize rsegs m) REAC_CTRL_PARSE_BC 6)
    by exact (proj1 (R14.r14_rel_ad m _ _ _ REL) HADB).
  assert (HRB0 : bytes_at rsegs (normalize rsegs m) REAL_BCMP (le8 (wa BCMP)))
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRB).
  assert (HRM0 : bytes_at rsegs (normalize rsegs m) REAL_MEMCMP (le8 (wa MEMCMP)))
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRM).
  assert (HGC0 : bytes_at rsegs (normalize rsegs m) GOT_CF (le8 (wa CF)))
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HGC).
  assert (HC2540 : bytes_at rsegs (normalize rsegs m) (CF + 254) [Z_to_bv 8 1])
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HC254).
  assert (HC2550 : bytes_at rsegs (normalize rsegs m) (CF + 255) [Z_to_bv 8 1])
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HC255).
  assert (HFP0 : fp [0%nat; 1%nat; 2%nat] (normalize rsegs m) (bv_unsigned tp) FS (S - CM_K) S
                   (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D phi len))
    by exact (proj1 (R14.r14_rel_fp _ m _ _ _ _ _ _ _ REL) HFP).
  assert (HTLS0 : reac_box_catalogue_match_tls (normalize rsegs m) (bv_unsigned tp) FS (S - CM_K) S)
    by exact (R14.r14_rel_tls m _ _ _ _ _ REL HTLS).
  step. (* 81830 mv a0,s8 *)
  step. (* 81834 mv a1,s2 *)
  step. (* 81838 jal 84498 <reac_box_catalogue_match> *)
  pose proof CMCF as HC. unfold CMC.reac_box_catalogue_match_contract_F, REAC_BOX_CATALOGUE_MATCH in HC.
  eapply ExecF.evtF_mono.
  { eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (seg_rom rsegs) HROA).
    eapply HC with (f := phi) (len := len) (S := S) (FS := FS) (fb := fb).
    all: cbv zeta.
    all: first [ exact HST0 | exact HROM | exact Hfb | exact HROc0 | exact HMI0 | exact HAC0 | exact HSW0
               | exact HADW0 | exact HADT0 | exact HADB0 | exact HRB0 | exact HRM0 | exact HGC0 | exact HC2540
               | exact HC2550 | exact HFP0 | exact HTLS0
               | exact RBYT | exact RIMG | exact RWIN | exact RF50 | exact RCAT | exact RBC | exact RSHW
               | exact RFPCM
               | (intros _; split; [lia|]; split; [lia|]; split; [exact HFB0 | exact HAPART])
               | (intros _; split; [exact HADf0 | exact HAPP50])
               | reflexivity | (f_equal; lia) | lia ]. }
  intros ms' (s0' & PO & HREL & HROS).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MU0 & WM0 & MI0 & ST0 & AC0 & SW0 & AD0 & FP0 & TL0).
  subst s0'.
  destruct HREL as (ER & EF & EP & ES & EV & EC & ERo & HMR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ES, EV, EC, ERo,
    HMR.
  assert (Ems : ms' = MS (ms_regs ms') (ms_fregs ms') (ms_pc_val ms') (ms_fcsr ms') (ms_resv ms') (ms_mem ms')
                         (ms_rom ms')) by exact (R14.r14_ms_eta ms' ES).
  rewrite ER, EF, EP, EC, EV, ERo in Ems.
  replace (ret_pc (Z_to_bv 64 0x8183c)) with (Z_to_bv 64 0x8183c) in Ems
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  remember (ms_mem ms') as mf eqn:Emf. clear Emf.
  (* the post on the real memory *)
  assert (MUf : munch (r14_W S FS) m mf) by exact (R14.r14_rel_munch _ m _ mf m0' REL HMR MU0 HROS).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mf.
  split; [exact Ems|].
  split; [exact MUf|].
  split.
  { apply (R14.r14_rel_wmono (r14_W S FS) m _ mf m0' REL HMR MUf WM0).
    intros x E0. exact (R14.r14_W_ro S FS x HFSgt ltac:(lia) E0). }
  split; [exact (R14.r14_ro_agree_same m mf HROA HROS)|].
  split; [exact (proj2 (R14.r14_rel_stk mf m0' (S - CM_K) S HMR ltac:(lia) ltac:(lia)) ST0)|].
  split; [exact (proj2 (R14.r14_rel_cells mf m0' HMR) AC0)|].
  split; [exact (proj2 (R14.r14_rel_sw mf m0' HMR) SW0)|].
  split; [exact (proj2 (R14.r14_rel_ad mf m0' _ _ HMR) AD0)|].
  exact (proj2 (R14.r14_rel_fp _ mf m0' _ _ _ _ _ _ HMR) FP0).
Qed.

(* R14.r14_call's statement as a corollary, with the callee's _F contract in the plain contract's place (the plain
   contract does not give the _F one): r14_call_F at ExecF.RNG_all, every rng premise by ExecF.rng_all from the
   bounds the plain premises already carry, and rng_fp_cm's bound-free ranges outright. *)
Lemma r14_call_of_F : CMC.reac_box_catalogue_match_contract_F ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 50 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat -> bytes_at rsegs m phi fb -> (phi + 50 <= S - CM_K \/ S <= phi) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> 6283264 <= FS -> addressable m (S - CM_K) CM_K ->
    addressable m phi 50 -> app_mem (phi + 50) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x8183c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x8183c) fc None m' (seg_rom rsegs) /\
         munch (r14_W S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs)).
Proof.
  intros CMCF ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb E8 E2 Esp Hphi0 Hphi50 Hlen HS Hmod HKS HST HROM Hfb HFB HAPART HROc HROA HAC HSW
    Hhi Hsp HFSgt HADW HADf HAPP50 HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl. unfold CM_K in *. unfold APPMEM_END, HIGHMEM_BEG in *.
  (* every rng premise at RNG_all: the bounds come from the plain premises (the window, phi, FS through fp's
     fs_place); the bound-free ranges of rng_fp_cm hold at RNG_all outright. The named constants are unfolded in
     the goal as well as in the hypotheses, because the goals come from r14_call_F's statement, which keeps them
     folded. *)
  eapply ExecF.evtF_evt, (r14_call_F CMCF ExecF.RNG_all); try eassumption.
  all: repeat first
    [ exact I
    | apply ExecF.rng_all;
        try unfold IMG_LO in *; try unfold IMG_HI in *; try unfold CM_K in *; try unfold CM_T in *;
        try unfold REAC_CTRL_PARSE_BC in *; try unfold shadow_addr in *; try unfold ASAN_K in *;
        try unfold APPMEM_END in *; try unfold HIGHMEM_BEG in *;
        Z.div_mod_to_equations; lia
    | apply Forall_forall
    | progress intros
    | split ].
Qed.

(* The pin: r14_call_of_F differs from R14.r14_call only in the first premise, which names the callee's _F contract
   in place of the plain one; both first premises are checked by name too (the form of Seg/F30F.v). *)
Example r14_call_of_F_verbatim : True.
Proof.
  lazymatch type of R14.r14_call with ?P -> ?A =>
  lazymatch type of r14_call_of_F with ?Q -> ?B =>
    constr_eq P CMC.reac_box_catalogue_match_contract;
    constr_eq Q CMC.reac_box_catalogue_match_contract_F;
    constr_eq A B
  end end.
  exact I.
Qed.

(* ---- Stretch 1: [0x81830, 0x84498). `mv a0,s8 ; mv a1,s2 ; jal 84498 <reac_box_catalogue_match>`, ending at the
   callee ENTRY with ra = 0x8183c. Three register instructions: no memory access, hence no rng premise. The
   binders and premises are R14.r14_call's, with RNG first and the callee contract removed. ---- *)
Lemma r14_call_pre_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 50 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat -> bytes_at rsegs m phi fb -> (phi + 50 <= S - CM_K \/ S <= phi) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> 6283264 <= FS -> addressable m (S - CM_K) CM_K ->
    addressable m phi 50 -> app_mem (phi + 50) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x8183c) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1
                                (Z_to_bv 64 phi) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
                                (Z_to_bv 64 len) s3 s4 s5 s6 s7 (Z_to_bv 64 phi) s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb -> -> -> Hphi0 Hphi50 Hlen HS Hmod HKS HST HROM Hfb HFB HAPART HROc HROA HAC HSW
    Hhi Hsp HFSgt HADW HADf HAPP50 HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  step. (* 81830 mv a0,s8 *)
  step. (* 81834 mv a1,s2 *)
  step. (* 81838 jal 84498 <reac_box_catalogue_match> *)
  apply ExecF.evtF_done. reflexivity.
Qed.

(* The canonical register map of an explicit register list is that list: Regs6ss.mkR_of reads the 31 slots back out
   of the map mkR builds. Used to put a concrete state into the shape stretch 2 starts from. *)
Lemma r14F_mkR_of : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word,
  Regs6ss.mkR_of (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                      x25 x26 x27 x28 x29 x30 x31)
  = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
        x25 x26 x27 x28 x29 x30 x31.
Proof. intros. reflexivity. Qed.

(* ---- Stretch 2: at the RETURN pc 0x8183c. The stretch is empty; its premises are exactly the machine-level facts
   R14.v's script holds right after it applies the contract and moves the post back across mem_rel, and its
   conclusion is R14.r14_call's post. The callee post's existentials (t0' .. t6', a1' .. a7') are universally
   bound here. ---- *)
Lemma r14_call_post_F :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3' t4' t5' t6' : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    Regs6ss.mkR_of regs =
      mkR (Z_to_bv 64 0x8183c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
          a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' ->
    munch (r14_W S FS) m mem -> wmono rsegs m mem -> ro_agree rsegs mem ->
    stk rsegs mem (S - CM_K) S -> asan_cells mem -> shadow_rw mem ->
    addressable mem (S - CM_K) CM_K ->
    fp [0%nat; 1%nat; 2%nat] mem (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 v3 v4 v5 v6 : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x8183c) sp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6)
                  F (Z_to_bv 64 0x8183c) fc None m' (seg_rom rsegs) /\
         munch (r14_W S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x8183c) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3' t4' t5' t6' F fc m phi len S FS fb ER MU WM RO ST AC SW AD FPm.
  apply ExecF.evtF_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mem.
  split; [rewrite ER; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO|]. split; [exact ST|].
  split; [exact AC|]. split; [exact SW|]. split; [exact AD | exact FPm].
Qed.

(* ---- The two stretches plus the PLAIN contract re-derive R14.r14_call. The middle piece is R14.v's own script
   (MemNorm.evt_normalize, the contract, and the transports of its post back across mem_rel), cut unchanged. ---- *)
Lemma r14_call_of_pre_post : reac_box_catalogue_match_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 50 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat -> bytes_at rsegs m phi fb -> (phi + 50 <= S - CM_K \/ S <= phi) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> 6283264 <= FS -> addressable m (S - CM_K) CM_K ->
    addressable m phi 50 -> app_mem (phi + 50) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x8183c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x8183c) fc None m' (seg_rom rsegs) /\
         munch (r14_W S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs)).
Proof.
  intros CMC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb -> -> -> Hphi0 Hphi50 Hlen HS Hmod HKS HST HROM Hfb HFB HAPART HROc HROA HAC HSW
    Hhi Hsp HFSgt HADW HADf HAPP50 HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  assert (HHMB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HK : CM_K = 9136) by reflexivity.
  (* stretch 1: up to the callee entry *)
  eapply evt_cut.
  { apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    exact (r14_call_pre_F ExecF.RNG_all ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 len) s3 s4 s5 s6 s7 (Z_to_bv 64 phi) s9 s10 s11 t3 t4 t5 t6 F fc m phi len S FS fb
             eq_refl eq_refl eq_refl Hphi0 Hphi50 Hlen HS Hmod HKS HST HROM Hfb
             HFB HAPART HROc HROA HAC HSW Hhi Hsp HFSgt HADW HADf HAPP50 HADT HADB HRB HRM HGC HC254 HC255 HFP
             HTLS). }
  intros ms0 ->.
  (* the premises on the normalized memory (R14.v's own transports) *)
  pose proof (mem_rel_normalize rsegs m HROA) as REL.
  assert (HST0 : stk rsegs (normalize rsegs m) (S - CM_K) S)
    by exact (proj1 (R14.r14_rel_stk m _ (S - CM_K) S REL ltac:(lia) ltac:(lia)) HST).
  assert (HFB0 : bytes_at rsegs (normalize rsegs m) phi fb) by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HFB).
  assert (HROc0 : forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs (normalize rsegs m) (wa a) = seg_rom rsegs (wa a))
    by (intros a Ha; rewrite <- (mrd_rel rsegs m _ _ REL); exact (HROc a Ha)).
  assert (HMI0 : mem_inv rsegs (normalize rsegs m)) by apply mem_inv_normalize.
  assert (HAC0 : asan_cells (normalize rsegs m)) by exact (proj1 (R14.r14_rel_cells m _ REL) HAC).
  assert (HSW0 : shadow_rw (normalize rsegs m)) by exact (proj1 (R14.r14_rel_sw m _ REL) HSW).
  assert (HADW0 : addressable (normalize rsegs m) (S - CM_K) CM_K)
    by exact (proj1 (R14.r14_rel_ad m _ _ _ REL) HADW).
  assert (HADf0 : addressable (normalize rsegs m) phi 50) by exact (proj1 (R14.r14_rel_ad m _ _ _ REL) HADf).
  assert (HADT0 : addressable (normalize rsegs m) CM_T 3256) by exact (proj1 (R14.r14_rel_ad m _ _ _ REL) HADT).
  assert (HADB0 : addressable (normalize rsegs m) REAC_CTRL_PARSE_BC 6)
    by exact (proj1 (R14.r14_rel_ad m _ _ _ REL) HADB).
  assert (HRB0 : bytes_at rsegs (normalize rsegs m) REAL_BCMP (le8 (wa BCMP)))
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRB).
  assert (HRM0 : bytes_at rsegs (normalize rsegs m) REAL_MEMCMP (le8 (wa MEMCMP)))
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRM).
  assert (HGC0 : bytes_at rsegs (normalize rsegs m) GOT_CF (le8 (wa CF)))
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HGC).
  assert (HC2540 : bytes_at rsegs (normalize rsegs m) (CF + 254) [Z_to_bv 8 1])
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HC254).
  assert (HC2550 : bytes_at rsegs (normalize rsegs m) (CF + 255) [Z_to_bv 8 1])
    by exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) HC255).
  assert (HFP0 : fp [0%nat; 1%nat; 2%nat] (normalize rsegs m) (bv_unsigned tp) FS (S - CM_K) S
                   (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D phi len))
    by exact (proj1 (R14.r14_rel_fp _ m _ _ _ _ _ _ _ REL) HFP).
  assert (HTLS0 : reac_box_catalogue_match_tls (normalize rsegs m) (bv_unsigned tp) FS (S - CM_K) S)
    by exact (R14.r14_rel_tls m _ _ _ _ _ REL HTLS).
  (* the call itself, by the plain contract, as R14.v does it *)
  pose proof CMC as HC. unfold reac_box_catalogue_match_contract, REAC_BOX_CATALOGUE_MATCH in HC.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ _ _ _ _ _ _ wx_apart_asan HROA).
    eapply HC with (f := phi) (len := len) (S := S) (FS := FS) (fb := fb).
    all: cbv zeta.
    all: first [ exact HST0 | exact HROM | exact Hfb | exact HROc0 | exact HMI0 | exact HAC0 | exact HSW0
               | exact HADW0 | exact HADT0 | exact HADB0 | exact HRB0 | exact HRM0 | exact HGC0 | exact HC2540
               | exact HC2550 | exact HFP0 | exact HTLS0
               | (intros _; split; [lia|]; split; [lia|]; split; [exact HFB0 | exact HAPART])
               | (intros _; split; [exact HADf0 | exact HAPP50])
               | reflexivity | (f_equal; lia) | lia ]. }
  intros ms' (s0' & PO & HREL & HROS).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MU0 & WM0 & MI0 & ST0 & AC0 & SW0 & AD0 & FP0 & TL0).
  subst s0'.
  destruct HREL as (ER & EF & EP & ES & EV & EC & ERo & HMR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ES, EV, EC, ERo,
    HMR.
  assert (Ems : ms' = MS (ms_regs ms') (ms_fregs ms') (ms_pc_val ms') (ms_fcsr ms') (ms_resv ms') (ms_mem ms')
                         (ms_rom ms')) by exact (R14.r14_ms_eta ms' ES).
  rewrite ER, EF, EP, EC, EV, ERo in Ems.
  replace (ret_pc (Z_to_bv 64 0x8183c)) with (Z_to_bv 64 0x8183c) in Ems
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  remember (ms_mem ms') as mf eqn:Emf. clear Emf.
  (* the post on the real memory; then stretch 2 closes the run *)
  assert (MUf : munch (r14_W S FS) m mf) by exact (R14.r14_rel_munch _ m _ mf m0' REL HMR MU0 HROS).
  assert (WMf : wmono rsegs m mf).
  { apply (R14.r14_rel_wmono (r14_W S FS) m _ mf m0' REL HMR MUf WM0).
    intros x E0. exact (R14.r14_W_ro S FS x HFSgt ltac:(lia) E0). }
  assert (ROf : ro_agree rsegs mf) by exact (R14.r14_ro_agree_same m mf HROA HROS).
  assert (STf : stk rsegs mf (S - CM_K) S)
    by exact (proj2 (R14.r14_rel_stk mf m0' (S - CM_K) S HMR ltac:(lia) ltac:(lia)) ST0).
  assert (ACf : asan_cells mf) by exact (proj2 (R14.r14_rel_cells mf m0' HMR) AC0).
  assert (SWf : shadow_rw mf) by exact (proj2 (R14.r14_rel_sw mf m0' HMR) SW0).
  assert (ADf : addressable mf (S - CM_K) CM_K) by exact (proj2 (R14.r14_rel_ad mf m0' _ _ HMR) AD0).
  assert (FPf : fp [0%nat; 1%nat; 2%nat] mf (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
                   (reac_box_catalogue_match_D phi len))
    by exact (proj2 (R14.r14_rel_fp _ mf m0' _ _ _ _ _ _ HMR) FP0).
  rewrite Ems.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  (* the start state in the canonical register map of stretch 2 *)
  match goal with
  | |- ExecF.evtF _ _ _ (MS ?R _ _ _ _ _ _) => replace R with (Regs6ss.mkR_of R) by apply r14F_mkR_of
  end.
  apply (r14_call_post_F ExecF.RNG_all _ mf (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1
           a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 len) s3 s4 s5 s6 s7 (Z_to_bv 64 phi) s9 s10 s11
           t3' t4' t5' t6' F fc m phi len S FS fb);
    [ apply r14F_mkR_of | exact MUf | exact WMf | exact ROf | exact STf | exact ACf | exact SWf | exact ADf
    | exact FPf ].
Qed.

(* The pin: r14_call_of_pre_post's statement is R14.r14_call's, term for term (constr_eq: syntactic, not up to
   conversion). The two stretches carry no premise the source does not state. *)
Example r14_call_of_pre_post_verbatim : True.
Proof.
  let a := type of R14.r14_call in let b := type of r14_call_of_pre_post in constr_eq a b.
  exact I.
Qed.

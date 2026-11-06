(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Export APS2_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition ASTAGE1 : Z := 0x97628.
Definition APARSE : Z := 0xbffe0.
Definition AS1_STACK : Z := 8192.        (* [comment removed for export] *)
Definition APARSE_STACK : Z := 32 + STAGE2_STACK_A.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition s1_winA (SP THIS ASI len : Z) : list (Z * Z) :=
  [(SP - 2656, SP); (THIS + 8, THIS + 12); (THIS + 24, THIS + 28); (THIS + 72, THIS + 88); (ASI, ASI + 4 * len + 36)].

Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition s1l_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m : amem) (THIS BUF ASI : Z) (d : list Z) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : amem) (rcv : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rcv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ frm0 fc' /\ 0 <= rcv < 2^64
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ wmono asegs m m'
    /\ munch (s1_winA (bv_unsigned sp) THIS ASI (zlength d)) m m'
    /\ AHEAP AI L RNG st LB m'
    /\ (rcv = 0 <-> fst (scan d) = true)
    /\ rw_cells asegs m' (THIS + 72) [C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d))]
    /\ (rcv = 0 -> rw_cells asegs m' (THIS + 8) [C4 (Z_to_bv 64 (zlength (snd (scan d))))]
                 /\ rw_cells asegs m' (THIS + 24) [C4 (Z_to_bv 64 0)]
                 /\ rw_cells asegs m' ASI [CB (4 * (length (snd (scan d)) + 3)) (u32bytes (snd (scan d) ++ [zlength d; zlength d; 0]))]).

Definition s1l_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (pim pcp psi : AsanCtrl.aptr) (THIS BUF ASI ACP nim ncp nsi : Z) (d : list Z) (lo : Z)
         (rstk : region),
    AHEAP AI L RNG st LB m -> mem_inv asegs m ->
    List.NoDup [pim; pcp; psi] ->
    In (HB pim THIS nim) LB -> 96 <= nim ->
    In (HB pcp ACP ncp) LB -> ACP <= BUF -> BUF + zlength d + 64 <= ACP + ncp ->
    In (HB psi ASI nsi) LB -> 4 * zlength d + 36 <= nsi -> 40 <= nsi ->   (* [comment removed for export] *)
    bytes_at asegs m BUF (s1buf d) -> Forall (fun c => 0 <= c < 256) d -> zlength d + 64 <= 2^20 ->
    rw_cells asegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)] ->
    rt_ctab_sh m ->
    stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AS1_STACK ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < al_top L ->
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> rrng RNG rstk ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
    frm0 fc ->
    a0 = Z_to_bv 64 THIS -> a1 = Z_to_bv 64 BUF -> a2 = Z_to_bv 64 (zlength d) -> a3 = Z_to_bv 64 0 ->
    evtF asegs RNG (s1l_postA L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m THIS BUF ASI d lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASTAGE1) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition parse_winA (THIS ASI len TPA ntp SBA nsb AOC AIA : Z) : list (Z * Z) :=
  [(THIS + 8, THIS + 12); (THIS + 24, THIS + 28); (THIS + 72, THIS + 96); (ASI, ASI + 4 * len + 36);
   (TPA, TPA + ntp); (SBA, SBA + nsb); (AOC, AOC + 8192); (AIA, AIA + 1024)].

Variable rng_fs : alayout -> footprint -> Prop.

Definition parse_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (s : APS) (LB : list ablock) (lo : Z) (rstk : region) (data : list Z) (tr0 : list Z)
         (pim psi pcp ptp psb poc pia : AsanCtrl.aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
         (x8 x24 x72 x80 x88 : word) (jtp jsb joc jia : list byte),
    let d := strip_bom data in
    AHEAP AI L RNG (aps_m s) LB m ->
    List.NoDup [pim; psi; pcp; ptp; psb; poc; pia] ->
    In (HB pim THIS nim) LB -> 96 <= nim -> In (HB psi ASI nsi) LB -> 4 * zlength d + 36 <= nsi -> 40 <= nsi ->
    In (HB pcp ACP ncp) LB -> ACP <= BUF -> BUF + zlength d + 64 <= ACP + ncp ->
    In (HB ptp TPA ntp) LB -> In (HB psb SBA nsb) LB -> In (HB poc AOC noc) LB -> 8192 <= noc -> In (HB pia AIA nia) LB -> 1024 <= nia ->
    (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) ->
    (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
    ntp mod 8 = 0 -> 8 * (zlength d + 3) <= ntp <= 2^27 -> 5 * zlength d + 182 <= 3 * nsb -> zlength d + 60 <= nsb <= 2^24 ->
    bytes_at asegs m BUF (s1buf d) -> Forall (fun c => 0 <= c < 256) d -> zlength d + 64 <= 2^20 ->
    rw_cells asegs m (THIS + 8) [C4 x8] -> rw_cells asegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)] ->
    rw_cells asegs m (THIS + 24) [C4 x24] ->
    rw_cells asegs m (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 x72; C8 x80; C8 x88] ->
    rw_cells asegs m DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)] -> DOC mod 8 = 0 ->
    (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= DOC /\ DOC + 16 <= FA + FN /\ ablk FA (FA + FN)) ->
    rw_cells asegs m (Z.shiftr DOC 3 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rng RNG DOC 16 -> rng RNG (Z.shiftr DOC 3 + 2147450880) 2 ->
    rw_cells asegs m TPA [CB (Z.to_nat ntp) jtp] -> rw_cells asegs m SBA [CB (Z.to_nat nsb) jsb] ->
    rw_cells asegs m AOC [CB 8192 joc] -> rw_cells asegs m AIA [CB 1024 jia] ->
    client_img m -> client_sh m -> (forall iv, In iv client_ranges -> In iv CI) ->
    uchain m (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) (Nat.pred UDEPTH) tr0 -> (length tr0 <= 27)%nat ->
    (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned sp + 16 <= bv_unsigned s0) ->
    4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
    In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
    stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - APARSE_STACK ->
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk -> rrng RNG rstk ->
    bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    mem_inv asegs m -> frm0 fc ->
    tp = Z_to_bv 64 ATP ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
    aps_ok L s -> AFRESH (aps_m s) -> dk (aps_m s) < DWMAX ->
    a0 = Z_to_bv 64 THIS -> a1 = Z_to_bv 64 BUF -> a2 = Z_to_bv 64 (zlength d) -> a3 = Z_to_bv 64 DOC ->
    implMA RNG (HarnessP.parse_impl amalloc_M afree_M (new_handlerA AAllocAsan) data) s
           (s2_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo
                     (parse_winA THIS ASI (zlength d) TPA ntp SBA nsb AOC AIA) m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 APARSE) fc None m (seg_rom asegs)).
End S.

(* [comment removed for export] *)
Lemma parse_impl_rnA : forall data idx, scan (strip_bom data) = (true, idx) ->
  HarnessP.parse_impl amalloc_M afree_M (new_handlerA AAllocAsan) data = rn_copyA (strip_bom data) idx.
Proof.
  intros data idx H. unfold HarnessP.parse_impl, HarnessP.root_copy, root_number_alloc, rn_copyA. cbv zeta. rewrite H.
  destruct idx as [|i0 r]; [reflexivity|]. unfold zlength. destruct (is_numstart _); reflexivity.
Qed.
Lemma parse_impl_failA : forall data, fst (scan (strip_bom data)) = false ->
  HarnessP.parse_impl amalloc_M afree_M (new_handlerA AAllocAsan) data = mret tt.
Proof.
  intros data H. unfold HarnessP.parse_impl, HarnessP.root_copy, root_number_alloc. cbv zeta.
  destruct (scan (strip_bom data)) as [[|] [|i0 r]]; cbn in H; try discriminate; reflexivity.
Qed.
End CANSEC1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_consts AU_kit AU_iface AU_parts_iface Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Export PA2_dk.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASTAGE2 : Z := 0x99f60.             (* [comment removed for export] *)
(* [comment removed for export] *)
Definition STAGE2_STACK_A : Z := 416 + 8192.
(* [comment removed for export] *)
Definition ASTAGE2_DEL_RETS : list Z := [0x9a8b0; 0x9fc20; 0xa0228].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition A2_IMGSH : list (Z * Z) :=
  [(2147468960, 32); (2147469000, 443); (2147469552, 23); (2147469580, 1302); (2147471440, 32); (2147471480, 1324); (2147472808, 80)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rn_copyA (d idx : list Z) : MA unit :=
  match idx with
  | i0 :: _ => if is_numstart (byte_at d i0)
               then c <- HarnessP.opnew amalloc_M (new_handlerA AAllocAsan) (zlength d - i0 + 64) ;; HarnessP.opdelete afree_M c
               else mret tt
  | [] => mret tt
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition s2_winA (THIS TPA ntp SBA nsb AOC AIA : Z) : list (Z * Z) :=
  [(THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (TPA, TPA + ntp); (SBA, SBA + nsb); (AOC, AOC + 8192); (AIA, AIA + 1024)].

Section Pres.
  Variable CI : list (Z * Z).
  (* [comment removed for export] *)
  Definition aheap_pres_W (LB : list ablock) (SP : Z) (W : list (Z * Z)) (m m' : amem) : Prop :=
    forall a, 0 <= a < 2^64 -> aclient_addr CI LB SP a -> outside W a ->
      m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
  Lemma aheap_pres_W_of_pres : forall LB SP W m m', aheap_pres CI LB SP m m' -> aheap_pres_W LB SP W m m'.
  Proof. intros LB SP W m m' H a Ha Hc _. exact (H a Ha Hc). Qed.
  Lemma aheap_pres_W_trans : forall LB SP W m1 m2 m3,
    aheap_pres_W LB SP W m1 m2 -> aheap_pres_W LB SP W m2 m3 -> aheap_pres_W LB SP W m1 m3.
  Proof.
    intros LB SP W m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
    split; [congruence| auto].
  Qed.
End Pres.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stmt.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.     (* [comment removed for export] *)

  Definition s2_postA (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : APS) (LB : list ablock) (lo : Z) (W : list (Z * Z)) (m : amem) (r : unit) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ frm0 fc'
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ aheap_pres_W CI LB (bv_unsigned sp) W m m'
      /\ aps_rest s' = aps_rest s
      /\ AHEAP AI L RNG' (aps_m s') LB m'.

  Definition stage2_stmtA : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (lo : Z) (rstk : region) (d idx : list Z) (tr0 : list Z)
           (pim psi pcp ptp psb poc pia : AsanCtrl.aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
           (x24 x88 : word) (jtp jsb joc jia : list byte),
      AHEAP AI L RNG (aps_m s) LB m ->
      (* [comment removed for export] *)
      List.NoDup [pim; psi; pcp; ptp; psb; poc; pia] ->
      In (HB pim THIS nim) LB -> 96 <= nim -> In (HB psi ASI nsi) LB -> 4 * zlength idx + 16 <= nsi ->
      In (HB pcp ACP ncp) LB -> ACP <= BUF -> BUF + zlength d + 64 <= ACP + ncp ->
      In (HB ptp TPA ntp) LB -> In (HB psb SBA nsb) LB -> In (HB poc AOC noc) LB -> 8192 <= noc -> In (HB pia AIA nia) LB -> 1024 <= nia ->
      (* [comment removed for export] *)
      (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) ->
      (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
      (* [comment removed for export] *)
      ntp mod 8 = 0 -> 8 * (zlength idx + 3) <= ntp <= 2^27 -> 5 * zlength d + 182 <= 3 * nsb -> zlength d + 60 <= nsb <= 2^24 ->
      (* [comment removed for export] *)
      bytes_at asegs m BUF (s1buf d) -> Forall (fun c => 0 <= c < 256) d -> zlength d + 64 <= 2^20 ->
      scan d = (true, idx) ->
      rw_cells asegs m ASI [CB (4 * (length idx + 3)) (u32bytes (idx ++ [zlength d; zlength d; 0]))] ->
      (* [comment removed for export] *)
      rw_cells asegs m (THIS + 8) [C4 (Z_to_bv 64 (zlength idx))] -> rw_cells asegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)] ->
      rw_cells asegs m (THIS + 24) [C4 x24] ->
      rw_cells asegs m (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
      rw_cells asegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88] ->
      (* [comment removed for export] *)
      rw_cells asegs m DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)] -> DOC mod 8 = 0 ->
      (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= DOC /\ DOC + 16 <= FA + FN /\ ablk FA (FA + FN)) ->
      rw_cells asegs m (Z.shiftr DOC 3 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
      rng RNG DOC 16 -> rng RNG (Z.shiftr DOC 3 + 2147450880) 2 ->
      (* [comment removed for export] *)
      rw_cells asegs m TPA [CB (Z.to_nat ntp) jtp] -> rw_cells asegs m SBA [CB (Z.to_nat nsb) jsb] ->
      rw_cells asegs m AOC [CB 8192 joc] -> rw_cells asegs m AIA [CB 1024 jia] ->
      (* [comment removed for export] *)
      client_img m -> client_sh m -> (forall iv, In iv client_ranges -> In iv CI) ->
      (* [comment removed for export] *)
      uchain m (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) (Nat.pred UDEPTH) tr0 -> (length tr0 <= 27)%nat ->
      (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned sp + 16 <= bv_unsigned s0) ->
      4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
      In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
      (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - STAGE2_STACK_A ->
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk -> rrng RNG rstk ->
      bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
      mem_inv asegs m -> frm0 fc ->
      tp = Z_to_bv 64 ATP ->
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
      aps_ok L s ->
      (* [comment removed for export] *)
      AFRESH (aps_m s) -> dk (aps_m s) < DWMAX ->
      a0 = Z_to_bv 64 THIS -> a1 = Z_to_bv 64 DOC ->
      implMA RNG (rn_copyA d idx) s
             (s2_postA L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo (s2_winA THIS TPA ntp SBA nsb AOC AIA) m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 ASTAGE2) fc None m (seg_rom asegs)).
End Stmt.

End CANSEC1.

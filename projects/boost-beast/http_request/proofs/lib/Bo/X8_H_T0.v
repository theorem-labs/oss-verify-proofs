(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac MState Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2
     AXRep_fields AXRep_mbuf AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit X8SRKit AXImgKit X8_P_ftab_rep X8_A_kit X8_pst X8_read_stmt X8_sro_stmt AXFuzz_stmt
     X8_stream_stmt3 X8_dss_stmt X8_asio_stmt_ectx X8_H_stmt X8_H_stmt2 X8_H_C X8_H_E X8_H_J X8_H_K X8_H_kit2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable MA : Z.

  (* [comment removed for export] *)
  Definition hz_cost5 (N : Z) : Z := hz_cost4 H MA N + dos_cost H.
  Definition hz_cost6 (N : Z) : Z := hz_cost5 N + as_Cf H NEWSZ_SCH.
  Definition hz_cost7 (N : Z) : Z := hz_cost6 N + as_Cf H NEWSZ_CFG.
  Definition hz_cost8 (N : Z) : Z := hz_cost7 N + as_Cf H NEWSZ_REG.
  Definition hz_cost9 (N : Z) : Z := hz_cost8 N + as_Cf H SZ_ALLOCIMPL.
  Definition hz_cost10 (N : Z) : Z := hz_cost9 N + as_Cf H (CAPMAX N).             (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma hz_cost9_ectx : forall N, hz_cost9 N = hz_cost4 H MA N + ectx_cost H.
  Proof. intros N. unfold hz_cost9, hz_cost8, hz_cost7, hz_cost6, hz_cost5, ectx_cost. lia. Qed.

  (* [comment removed for export] *)
  Definition hzK11 (gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (D N lo B shi : Z) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word)
      (m0 : mem) (mo : Model) : config -> Prop :=
    fun cf => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (errv : word) (s' : as_St H) (spa ff fp : Z) (gap : list cell)
                     (allocb regb schedb : Z) (j24 j4 j16 j40 j32b j40b j392 : list byte) (XS : list (Z * Z)) (stb : Z) (L FBB : list block) (FB : fbv) (fds : list byte),
      as_VIS H s' (cfg_ms cf) = MS (mkR (Z_to_bv 64 P_HZ_RET_ECD) (Z_to_bv 64 spa) gp tp t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                                       (Z_to_bv 64 ff) (Z_to_bv 64 (Z.shiftr ff 3 + 2147450880)) (Z_to_bv 64 (ff + 128)) (Z_to_bv 64 (ff + 208)) (Z_to_bv 64 0)
                                       (Z_to_bv 64 (ff + 272)) (Z_to_bv 64 (ff + 352)) (Z_to_bv 64 ff) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                                  F (ret_pc (Z_to_bv 64 P_HZ_RET_ECD)) fc None m (seg_rom bsegs)
      /\ (spa = bv_unsigned sp + -160 \/ spa = bv_unsigned sp + -176)
      /\ fresh_frame H LF 4 ff fp
      /\ as_AKREL H s' cf
      /\ as_MPRES H mo (cfg_model cf)
      /\ as_RHEAP H s LB m0
      (* [comment removed for export] *)
      /\ as_RHEAP H s' L m
      /\ Permutation L (FBB ++ LB)
      /\ fbb_ok FB FBB
      /\ AFlatBuf L m (ff + 128) FB fds
      /\ fb_cap FB <= CAPMAX N
      /\ (FB <> FB_empty -> blk_fresh H LB spa (fb_begin FB) (fb_cap FB))
      (* [comment removed for export] *)
      /\ hz_frame m spa ff fp (bv_unsigned sp) allocb regb schedb stb j24 j4 j16 j40 j32b j40b j392 gap (hz_saved s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) hz_sh2
      (* [comment removed for export] *)
      /\ AXImg m /\ acanary m /\ AHStat FT m
      /\ rw_cells bsegs m AERRNO [C4 errv] /\ as_rauxv_ok H m B /\ mem_inv bsegs m /\ stk bsegs m lo spa
      /\ as_RFS H ((4, ff, fp) :: LF) m /\ ACONST m /\ stack0 m lo shi
      /\ Forall (fs_scratch H ((4, ff, fp) :: LF)) XS
      /\ xpres H LB (bv_unsigned sp) ((fr4_XS H ff fp ++ [(AERRNO, AERRNO + 4); (AXH_LO, AXH_HI)]%Z) ++ XS) m0 m
      /\ as_AL H s' >= as_AL H s - hz_cost9 N.

  (* [comment removed for export] *)
  Definition hz_final (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (N lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m' /\ Permutation LB' LB
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LB (bv_unsigned sp) ([(AXH_LO, AXH_HI); (AERRNO, AERRNO + 4)]%Z ++ XS) m m'
      /\ AHStat FT m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - hz_cost10 N.

  (* [comment removed for export] *)
  Definition hz_T_stmt : Prop :=
    forall (gp s11 : word) (F : bvmap 5 word) (fc : bv 32) (s : as_St H) (LB : list block) (LF : list fframe) (CH : list (Z * Z))
           (D N lo B shi : Z) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) (m0 : mem) (mo : Model) (msF : machine_state) (mo11 : Model),
      hz_pure H sp ra D N lo B shi LB LF -> hz_cost10 N <= as_AL H s ->
      F = bvmap_empty -> fc = Z_to_bv 32 0 ->
      as_chain H m0 (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      trace_ok (as_TR H) APC0_FREE (P_HZ_RET_DEL :: bv_unsigned ra :: map snd CH) ->
      hzK11 gp (Z_to_bv 64 ATP) s11 F fc s LB LF D N lo B shi sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 mo (mkCfg msF mo11) ->
      as_SR H (hz_final ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF N lo B shi m0 mo) (mkCfg msF mo11).
End HCW.

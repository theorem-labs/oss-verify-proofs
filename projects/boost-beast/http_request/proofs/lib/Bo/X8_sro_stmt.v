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
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsIface7 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2 AXRep_fields AXRep_mbuf AXImgKit X8Kit X8SRKit X8_P_ftab_rep X8_F_insert2 X8_F_insert4 X8_state1_stmt X8_state2_stmt X8_mbuf_stmt X8_pst X8_put_stmt X8_cobj X8_S_place X8_stream_stmt X8_stream_stmt4 X8_read_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ASRO_STACK : Z := 128 + HREAD_STACK.
Definition P_SRO_RET_RS : Z := 0xcf700.   (* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition sro_C (bs fb P E ioc N lo B shi SP stb implb A : Z) (LBin : list block) (LF : list fframe)
      (pad7 pad2 j13 j32a j8a j32b j8b : list byte) (mb : byte) (m0 : mem) (mo0 : Model) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (MX CX : Z) : rsc :=
    mkC bs fb P E ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp F fc MX CX.

  (* [comment removed for export] *)
  Definition sro_phi0 (N : Z) : Z := 17 * 8192 + (3 * N + 1194) + 34 + 2 * CAPMAX N.   (* [comment removed for export] *)
  Definition sro_pot (N : Z) (LBin : list block) (MX CX MA : Z) : Prop :=
       lb_bytes LBin + sro_phi0 N <= MX /\ MX <= as_LIVE_MAX H
    /\ 4 * Z.of_nat (length LBin) + 8192 + 4 * KB + 10 + 8 <= 4 * CX /\ CX <= as_LIVE_CNT_MAX H
    /\ N <= 2^26
    /\ 17 * 8192 + (3 * N + 1194) + 34 + fb_res N 0 <= MA.

  (* [comment removed for export] *)
  Definition sro_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LBin : list block) (LF : list fframe) (bs fb P E ioc N lo B shi stb implb A : Z)
      (pad7 pad2 j13 j32a j8a j32b j8b : list byte) (mb : byte) (MX CX MA MR : Z) (m0 : mem) (mo0 : Model) : config -> Prop :=
    fun cf => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (w : rsw) (s' : as_St H) (errv : word) (E' : ecv) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom bsegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo0 (cfg_model cf)
      /\ RWm H (sro_C bs fb P E ioc N lo B shi (bv_unsigned sp) stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp F fc MX CX) w s' errv E' m
      /\ RWp H (sro_C bs fb P E ioc N lo B shi (bv_unsigned sp) stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp F fc MX CX) MA w
      /\ al_ok H s' (ps_A (w_d w)) MA MR
      /\ stk bsegs m lo (bv_unsigned sp)
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LBin (bv_unsigned sp) (hread_X P E fb stb [] [] ++ XS) m0 m
      /\ ec_ok E' /\ (E' = EC_clear \/ http_fail E')
      /\ (E' = EC_clear -> pc_state (ps_c (w_d w)) = 11).

  (* [comment removed for export] *)
  Definition sro_stmt (MX CX MA MR : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LBin : list block) (LF : list fframe)
           (bs fb P E ioc N lo B shi stb implb A : Z) (Fs : fbv) (ds : list byte) (c0 : pcore) (h0 : hdrv)
           (pad7 pad2 pad4 j13 j32a j8a j32b j8b jE : list byte) (mb : byte) (hb : bool) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz bs) (wz fb) (wz P) (wz E) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 P_A_SYNC_READ_OP) fc None m (seg_rom bsegs) ->
      (* [comment removed for export] *)
      aobj [] LF P 352 -> aobj [] LF E 24 ->
      sobj (bv_unsigned sp) shi bs 32 -> aobj [] LF fb 48 ->                                   (* [comment removed for export] *)
      P mod 8 = 0 -> E mod 8 = 0 -> bs mod 8 = 0 -> fb mod 8 = 0 ->
      (P + 352 <= E \/ E + 24 <= P) -> (P + 352 <= fb \/ fb + 48 <= P) -> (E + 24 <= fb \/ fb + 48 <= E) ->   (* [comment removed for export] *)
      0 <= ioc < 2^64 ->
      (* [comment removed for export] *)
      stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo + ASRO_STACK <= bv_unsigned sp ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= shi -> bv_unsigned sp <= B ->
      tp = Z_to_bv 64 ATP -> bv_unsigned ra mod 2 = 0 ->
      (* [comment removed for export] *)
      rw_cells bsegs m P (ParserCoreCells c0 pad7 pad2) -> pcore_ok c0 -> pc_state c0 = 0 -> pc_hlim c0 <= 8192 -> pc_skip c0 = 0 -> pc_len c0 = 0 ->
      rw_cells bsegs m (P + 80) (NodeCells (init_header_node (P + 80)) pad4) ->
      rw_cells bsegs m (P + 112) (LNodeCells (init_lheader_node (P + 112))) ->
      rw_cells bsegs m (P + O_PR_HDR) (HdrCells h0) -> hdr_empty h0 ->
      rw_cells bsegs m (P + 168) (MBufHdrCells (P + 176) (P + 176) (P + 176) 0 0 0 0) ->
      rw_cells bsegs m (P + 232) [C8 (wz (P + 168))] ->
      rw_cells bsegs m (P + 240) [C1 (b8 0); C1 (b8 0); C1 mb; CB 13 j13] ->
      rw_cells bsegs m (P + 256) [CB 32 j32a; C8 (wz 0); CB 8 j8a] -> rw_cells bsegs m (P + 304) [CB 32 j32b; C8 (wz 0); CB 8 j8b] ->
      (* [comment removed for export] *)
      rw_cells bsegs m fb (FlatBufCells FB_empty) -> rw_cells bsegs m E [CB 24 jE] ->
      (* [comment removed for export] *)
      rw_cells bsegs m bs (BasicStreamCells stb) ->
      AStateBlock LBin m stb ioc implb (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 Fs STREAM_EOF 0 0) ds ->
      zlength ds = N -> 0 <= N < 2^26 ->
      ((N = 0 /\ Fs = FB_empty) \/ (1 <= N /\ Fs = mkFB A A (A + N) (A + N) (A + N) /\ (A + N <= stb \/ stb + SZ_SPCI_STATE <= A))) ->
      (1 <= N -> exists p9, In (p9, A, N) LBin) ->
      (* [comment removed for export] *)
      AXStatics2 m -> APfTab m -> FTInit m -> AMiscVt48 m -> AHttpCat m hb -> (AFieldTabZero m \/ FT m) ->
      (* [comment removed for export] *)
      as_RHEAP H s LBin m -> as_AKREL H s (mkCfg msF mo) -> as_rauxv_ok H m B ->
      sro_pot N LBin MX CX MA -> al_ok H s 0 MA MR ->
      rw_cells bsegs m (errno_addr tp) [C4 errv] ->
      bv_unsigned mb <= 1 ->      (* [comment removed for export] *)
      mem_inv bsegs m ->
      (* [comment removed for export] *)
      as_RFS H LF m -> (length LF + 6 < AFS_MAXLIVE)%nat -> (length LF + 2 < AFS7_MAXLIVE)%nat ->   (* [comment removed for export] *)
      ACONST m -> stack0 m lo shi ->
      accessible m P PARSER_SIZE -> accessible m E 24 -> shvis m E (E + 24) -> accessible m bs 32 -> accessible m fb 48 ->
      (1 <= N -> shvis m A (A + N)) ->
      as_SR H (sro_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBin LF bs fb P E ioc N lo B shi stb implb A
                        pad7 pad2 j13 j32a j8a j32b j8b mb MX CX MA MR m mo)
        (mkCfg msF mo).
End HCW.

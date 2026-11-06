(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface CXXRep XRep XPRep XF_rep XM_rep XP_req_stmt
     XB_flat XS_readsome XP_field XP_ftab_rep XFuzz_stmt XP_pst XP_dtor XP_dtor2.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SRO_STACK : Z := 16384.

(* [comment removed for export] *)
Definition SRO_BYTES (N : Z) : Z := 17 * 8192 + (3 * N + 1194 + 34) + 2 * (2 * N + 65536).
Definition SRO_CNT : Z := 2048 + 22 + 2 + 1 + 2.

(* [comment removed for export] *)
Definition sro_X (P stb : Z) : list (Z * Z) :=
  [(P, P + 242); (P + 416, P + 488); (stb, stb + SZ_SPCI_STATE); (XH_LO, XH_HI)]%Z.

Section HCW.
  Context {HCEIL : HeapCeil}.
Section SR.
  Variable H : hsr.

  (* [comment removed for export] *)
  Definition sro_post (ra gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (P N D lo B stb implb A : Z) (LBin : list block) (pad7 pad2 pad4 j13 j32a j8a j32b j8b : list byte) (mb : byte)
      (m0 : mem) (mo0 : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : PState) (errv' : word)
                    (d : pst) (LBn PB FBB : list block) (FB : fbv) (fds : list byte) (Fs : fbv) (sds : list byte) (nr nb : Z) (E' : ecv),
      cfg_ms c = MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (wz N) (wz D) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo0 (cfg_model c)
      /\ mem_inv usegs m' /\ stk usegs m' lo P
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' (LBn ++ LBin) m'
      (* [comment removed for export] *)
      /\ rw_cells usegs m' P (ParserCoreCells (ps_c d) pad7 pad2) /\ pcore_ok (ps_c d)
      /\ FieldsC m' (P + 80) (ps_S d) (ps_L d) (ps_ns d) (ps_ls d) (ps_em d) /\ FieldsOwn (LBn ++ LBin) (ps_em d)
      /\ rw_cells usegs m' (P + 128) (HdrCells (ps_h d)) /\ HdrOwn (LBn ++ LBin) (ps_h d) /\ HdrDisj (ps_em d) (ps_h d)
      /\ MBuf m' (P + 168) (ps_es d) (ps_insz d) /\ MBufOwn (LBn ++ LBin) (ps_es d) /\ BodyDisj (ps_em d) (ps_h d) (ps_es d)
      /\ rw_cells usegs m' (P + 232) [C8 (wz (P + 168))]
      /\ rw_cells usegs m' (P + 240) [C1 (ps_rdi d)] /\ rw_cells usegs m' (P + 241) [C1 (b8 (ps_u d))] /\ rw_cells usegs m' (P + 242) [C1 mb]
      /\ rw_cells usegs m' (P + 243) [CB 13 j13]
      /\ rw_cells usegs m' (P + 256) [CB 32 j32a; C8 (wz 0); CB 8 j8a] /\ rw_cells usegs m' (P + 304) [CB 32 j32b; C8 (wz 0); CB 8 j8b]
      (* [comment removed for export] *)
      /\ Permutation LBn (PB ++ FBB)
      /\ (forall b, In b PB -> powned (ps_em d) (ps_h d) (ps_es d) b)
      /\ (forall b, In b (FBB ++ LBin) -> ~ powned (ps_em d) (ps_h d) (ps_es d) b)
      /\ ((FB = FB_empty /\ FBB = [])
          \/ (exists pf, FBB = [(pf, fb_begin FB, fb_cap FB)] /\ 0 < fb_begin FB /\ fb_begin FB <= fb_end FB /\ fb_end FB <= hceil))
      (* [comment removed for export] *)
      /\ FlatBuf (LBn ++ LBin) m' (P + 416) FB fds
      /\ rw_cells usegs m' (P + 464) (ErrCodeCells E')
      (* [comment removed for export] *)
      /\ rw_cells usegs m' (P + 360) (BasicStreamCells stb)
      /\ StateBlock (LBn ++ LBin) m' stb (P + 392) implb (mkST (mkSPC VP_SPCI_STATE 1 1 1) 0 Fs STREAM_EOF nr nb) sds
      /\ ((N = 0 /\ Fs = FB_empty) \/ (1 <= N /\ fb_begin Fs = A /\ fb_end Fs = A + N))
      (* [comment removed for export] *)
      /\ (exists hb, HttpCat m' hb) /\ (FieldTabZero m' \/ FT m') /\ XStatics m' /\ PfTab m' /\ FTInit m' /\ MiscVt48 m'
      (* [comment removed for export] *)
      /\ xpres LBin P (sro_X P stb) m0 m'.

  (* [comment removed for export] *)
  Definition sro_stmt : Prop :=
    forall (ra gp tp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (mo : Model) (s : PState) (LBin : list block)
           (P N D lo B stb implb A : Z) (c0 : pcore) (h0 : hdrv) (Fs : fbv) (sds : list byte)
           (pad7 pad2 pad4 j13 j32a j8a j32b j8b : list byte) (mb : byte) (hb : bool) (errv : word),
      (* [comment removed for export] *)
      0 <= P -> P + 512 <= B -> B <= 2^64 -> P mod 16 = 0 -> bv_unsigned ra mod 2 = 0 -> tp = Z_to_bv 64 RATP ->
      stk usegs m lo P -> hceil <= lo -> 0xb8000 <= lo -> lo + SRO_STACK <= P ->
      (* [comment removed for export] *)
      rw_cells usegs m P (ParserCoreCells c0 pad7 pad2) -> pcore_ok c0 -> pc_state c0 = 0 -> pc_hlim c0 <= 8192 -> pc_skip c0 = 0 ->
      rw_cells usegs m (P + 80) (NodeCells (init_header_node (P + 80)) pad4) ->
      rw_cells usegs m (P + 112) (LNodeCells (init_lheader_node (P + 112))) ->
      rw_cells usegs m (P + 128) (HdrCells h0) -> hdr_empty h0 ->
      rw_cells usegs m (P + 168) (MBufHdrCells (P + 176) (P + 176) (P + 176) 0 0 0 0) ->
      rw_cells usegs m (P + 232) [C8 (wz (P + 168))] ->
      rw_cells usegs m (P + 240) [CB 3 [b8 0; b8 0; mb]; CB 13 j13] ->
      rw_cells usegs m (P + 256) [CB 32 j32a; C8 (wz 0); CB 8 j8a] -> rw_cells usegs m (P + 304) [CB 32 j32b; C8 (wz 0); CB 8 j8b] ->
      (* [comment removed for export] *)
      rw_cells usegs m (P + 416) (FlatBufCells FB_empty) -> rw_cells usegs m (P + 464) (ErrCodeCells EC_clear) ->
      (* [comment removed for export] *)
      rw_cells usegs m (P + 360) (BasicStreamCells stb) ->
      StateBlock LBin m stb (P + 392) implb (mkST (mkSPC VP_SPCI_STATE 1 1 1) 0 Fs STREAM_EOF 0 0) sds ->
      zlength sds = N -> 0 <= N <= 2^26 ->
      ((N = 0 /\ Fs = FB_empty) \/ (1 <= N /\ Fs = mkFB A A (A + N) (A + N) (A + N) /\ (A + N <= stb \/ stb + SZ_SPCI_STATE <= A))) ->
      (* [comment removed for export] *)
      XStatics m -> PfTab m -> FTInit m -> MiscVt48 m -> HttpCat m hb -> (FieldTabZero m \/ FT m) ->
      (* [comment removed for export] *)
      hs_RHEAP H s LBin m -> hs_KREL H s mo -> hs_rauxv_ok H m B ->
      lb_bytes LBin + SRO_BYTES N <= hs_LIVE_MAX H -> Z.of_nat (length LBin) + SRO_CNT <= hs_LIVE_CNT_MAX H ->
      rw_cells usegs m (errno_addr tp) [C4 errv] ->
      bv_unsigned mb <= 1 ->      (* [comment removed for export] *)
      mem_inv usegs m ->
      hs_SR H (sro_post ra gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P N D lo B stb implb A LBin pad7 pad2 pad4 j13 j32a j8a j32b j8b mb m mo)
        (mkCfg (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (wz N) (wz D)
                         (wz (P + 360)) (wz (P + 416)) (wz P) (wz (P + 464)) a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 P_SYNC_READ_OP) fc None m (seg_rom usegs)) mo).
End SR.
End HCW.

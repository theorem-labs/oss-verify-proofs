(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList X8Kit X8SRKit X8_cobj X8_S_place X8_stream_stmt X8_stream_stmt3.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition P_BSD_RET1 : Z := 0xa5f44.    (* [comment removed for export] *)
Definition P_BSD_RET_AR : Z := 0xa5f4c.  (* [comment removed for export] *)
Definition P_BSD_RET2 : Z := 0xa5f5c.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASTREAM_DTOR_STACK : Z := 32 + ASHCOUNT_DTOR_STATE_STACK.

(* [comment removed for export] *)
Definition bsd_X (bs stb implb vb vcap : Z) (Fb : fbv) : list (Z * Z) :=
  (bs + 16, bs + 32) :: blkX stb SZ_SPCI_STATE ++ (implb, implb + SZ_SPCI_IMPL) :: (vb, vb + 8 * vcap) :: (sh vb, sh vb + vcap)
  :: (if fb_begin Fb =? 0 then [] else blkX (fb_begin Fb) (fb_cap Fb)).

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition stream_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (bs stb implb vb i vcap lo B shi : Z) (S : statev) (errv : word) (m : mem) (mo : Model)
      : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (pf p : bptr) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
      /\ In (p, stb, SZ_SPCI_STATE) LB
      /\ (st_fb S <> FB_empty -> In (pf, fb_begin (st_fb S), fb_cap (st_fb S)) LB)
      /\ as_RHEAP H s' (as_lb_remove H p (sd_LB H (st_fb S) pf LB)) m'
      /\ rw_cells bsegs m' bs (BasicStreamCells stb)
      /\ AImplBlockC (as_lb_remove H p (sd_LB H (st_fb S) pf LB)) m' implb (mkIMPL (mkSPC AVP_SPCI_IMPL 1 1 i) 0 vb [] vcap)
      /\ AXStatics2 m'
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LB (bv_unsigned sp) (bsd_X bs stb implb vb vcap (st_fb S) ++ XS) m m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi /\ accessible m' bs SZ_BS
      /\ as_AL H s' >= as_AL H s - scs_cost H (st_fb S).

  Definition stream_dtor_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (bs stb ioc implb vb i vcap lo B shi : Z) (S : statev) (ds : list byte)
           (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 P_A_STREAM_DTOR) fc None m (seg_rom bsegs) ->
      a0 = Z_to_bv 64 bs ->
      (* [comment removed for export] *)
      rw_cells bsegs m bs (BasicStreamCells stb) -> sobj (bv_unsigned sp) shi bs SZ_BS -> bs mod 8 = 0 ->
      (* [comment removed for export] *)
      AStateBlock LB m stb ioc implb S ds -> st_hdr S = mkSPC AVP_SPCI_STATE 1 1 1 -> st_lk S = 0 ->
      (* [comment removed for export] *)
      AImplBlockC LB m implb (impl_one 2 i vb (stb + 32) vcap) -> 0 < vcap -> 8 * vcap <= 2^16 ->
      (stb + SZ_SPCI_STATE <= implb \/ implb + SZ_SPCI_IMPL <= stb) ->
      (stb + SZ_SPCI_STATE <= vb \/ vb + 8 * vcap <= stb) ->
      (vb + 8 * vcap <= implb \/ implb + SZ_SPCI_IMPL <= vb) ->
      (st_fb S <> FB_empty -> fb_off (st_fb S) stb SZ_SPCI_STATE /\ fb_off (st_fb S) implb SZ_SPCI_IMPL /\ fb_off (st_fb S) vb (8 * vcap)
                              /\ fb_off (st_fb S) bs SZ_BS) ->
      AXStatics2 m ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->
      stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ASTREAM_DTOR_STACK ->
      rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      (* [comment removed for export] *)
      athr_cells m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
      stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
      accessible m bs SZ_BS -> shvis m bs (bs + SZ_BS) ->
      as_chain H m (bv_unsigned s0) CH -> trace_ok (as_TR H) APC0_FREE (bv_unsigned ra :: map snd CH) ->
      (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp' /\ bs + SZ_BS + 16 <= fp') ->
      scs_cost H (st_fb S) <= as_AL H s ->
      as_SR H (stream_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF bs stb implb vb i vcap lo B shi S errv m mo)
        (mkCfg msF mo).
End HCW.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit X8SRKit X8_A_leaves2 XL_mutex XL_cond X8_asio_stmt_alloc X8_asio_stmt_sp X8_cobj X8_S_place X8_stream_stmt.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASTREAM_CLOSE_STACK : Z := 144 + AINTRIN_STACK.
(* [comment removed for export] *)
Definition ASSVC_SHUTDOWN_STACK : Z := 176 + AINTRIN_STACK.
(* [comment removed for export] *)
Definition ASTATE_DTOR_STACK : Z := 144 + AFREE_STACK.
(* [comment removed for export] *)
Definition ASHCOUNT_DTOR_STATE_STACK : Z := 64 + ASTATE_DTOR_STACK.
(* [comment removed for export] *)
Definition ASHCOUNT_DTOR_IMPL_STACK : Z := 112 + AFREE_STACK.
(* [comment removed for export] *)
Definition ASSVC_DTOR_STACK : Z := ASHCOUNT_DTOR_IMPL_STACK.
(* [comment removed for export] *)
Definition ADOBJ_SSVC_STACK : Z := 32 + ASHCOUNT_DTOR_IMPL_STACK.

(* [comment removed for export] *)
Definition blkX (b n : Z) : list (Z * Z) := [(b, b + n); (sh b, sh b + nsh n)]%Z.
(* [comment removed for export] *)
Definition sd_X (implb : Z) (Fb : fbv) : list (Z * Z) :=
  (implb + 12, implb + 16) :: (if fb_begin Fb =? 0 then [] else blkX (fb_begin Fb) (fb_cap Fb)).
(* [comment removed for export] *)
Definition scs_X (stb implb : Z) (Fb : fbv) : list (Z * Z) := blkX stb SZ_SPCI_STATE ++ sd_X implb Fb.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W1.
  Variable H : asr.

Definition cl_W (lo : Z) (sp : word) (bs stb ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (bs + 16, bs + 32); (stb + 104, stb + 144); (stb + 240, stb + 252);
   (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (sh ff, sh ff + 32)]%Z.

Definition stream_close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list block) (LF : list fframe) (bs stb ioc implb lo shi : Z) (S : statev) (ds : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (cl_W lo sp bs stb ff fp) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' bs (BasicStreamCells stb)
    /\ AStateBlock LB m' stb ioc implb (st_closed S) ds
    /\ accessible m' bs SZ_BS
    /\ fresh_frame H LF 2 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

Definition stream_close_stmt : Prop :=
  forall (bs stb ioc implb lo shi : Z) (LB : list block) (LF : list fframe) (S : statev) (ds : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells bsegs m bs (BasicStreamCells stb) -> bs mod 8 = 0 ->
  AStateBlock LB m stb ioc implb S ds -> st_lk S = 0 ->
  (st_fb S <> FB_empty -> fb_end (st_fb S) <= stb \/ stb + SZ_SPCI_STATE <= fb_begin (st_fb S)) ->
  (* [comment removed for export] *)
  (st_fb S <> FB_empty -> fb_end (st_fb S) <= bs \/ bs + SZ_BS <= fb_begin (st_fb S)) ->
  stk bsegs m lo (bv_unsigned sp) -> lo + ASTREAM_CLOSE_STACK <= bv_unsigned sp -> aceil <= lo ->
  (bs + SZ_BS <= stb \/ stb + SZ_SPCI_STATE <= bs) ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
  stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
  aplace bs SZ_BS -> (bs + SZ_BS <= lo \/ bv_unsigned sp <= bs) -> fsobj H LF bs SZ_BS -> accessible m bs SZ_BS -> shvis m bs (bs + SZ_BS) ->
  fsobj H LF stb SZ_SPCI_STATE ->
  (st_fb S <> FB_empty -> fsobj H LF (fb_begin (st_fb S)) (fb_cap (st_fb S))) ->
  evt bsegs (stream_close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF bs stb ioc implb lo shi S ds m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz bs) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_STREAM_CLOSE) fc None m (seg_rom bsegs)).
End W1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W2.
  Variable H : asr.

Definition sh_W (lo : Z) (sp : word) (implb ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (implb + 32, implb + 72);
   (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16)]%Z.

Definition ssvc_shutdown_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list block) (LF : list fframe) (v implb lo shi : Z) (S : svch) (I : implv) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sh_W lo sp implb ff fp) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ AStreamSvc LB m' v S implb
    /\ AImplBlockC LB m' implb I
    /\ fresh_frame H LF 1 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

Definition ssvc_shutdown_stmt : Prop :=
  forall (v implb lo shi : Z) (LB : list block) (LF : list fframe) (S : svch) (I : implv)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  AStreamSvc LB m v S implb ->
  AImplBlockC LB m implb I -> im_lk I = 0 -> im_states I = [] ->
  (v + NEWSZ_SSVC <= implb \/ implb + SZ_SPCI_IMPL <= v) ->
  (0 < im_vcap I -> im_vb I + 8 * im_vcap I <= implb \/ implb + SZ_SPCI_IMPL <= im_vb I) ->
  stk bsegs m lo (bv_unsigned sp) -> lo + ASSVC_SHUTDOWN_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
  stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
  fsobj H LF v NEWSZ_SSVC -> fsobj H LF implb SZ_SPCI_IMPL -> (0 < im_vcap I -> fsobj H LF (im_vb I) (8 * im_vcap I)) ->
  evt bsegs (ssvc_shutdown_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF v implb lo shi S I m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_SSVC_SHUTDOWN) fc None m (seg_rom bsegs)).
End W2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W3.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition sd_LB (Fb : fbv) (pf : bptr) (LB : list block) : list block :=
    if fb_begin Fb =? 0 then LB else as_lb_remove H pf LB.
  Definition sd_cost (Fb : fbv) : Z := if fb_begin Fb =? 0 then 0 else as_Cf H (fb_cap Fb).

Definition state_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (stb implb lo B shi : Z) (S : statev) (I : implv) (errv : word) (m : mem) (mo : Model)
    : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (pf p : bptr) (j7 : list byte) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ (st_fb S <> FB_empty -> In (pf, fb_begin (st_fb S), fb_cap (st_fb S)) LB)
    /\ as_RHEAP H s' (sd_LB (st_fb S) pf LB) m'
    /\ In (p, stb, SZ_SPCI_STATE) (sd_LB (st_fb S) pf LB)
    /\ rw_cells bsegs m' stb (SpcHdrCells (st_hdr S) j7)
    /\ (exists rest, rw_cells bsegs m' (stb + 32) rest /\ Z.of_nat (cells_size rest) = SZ_SPCI_STATE - 32)
    /\ addressable m' stb SZ_SPCI_STATE
    /\ AImplBlockC (sd_LB (st_fb S) pf LB) m' implb (impl_weak I 1)
    /\ AXStatics2 m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) (sd_X implb (st_fb S) ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - sd_cost (st_fb S).

Definition state_dtor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (stb ioc implb lo B shi : Z) (S : statev) (ds : list byte) (I : implv)
         (errv : word) (CH : list (Z * Z)),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_STATE_DTOR) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 (stb + 32) ->
    AStateBlock LB m stb ioc implb S ds ->
    AImplBlockC LB m implb I -> spc_weak (im_hdr I) = 2 ->
    (stb + SZ_SPCI_STATE <= implb \/ implb + SZ_SPCI_IMPL <= stb) ->
    (0 < im_vcap I -> stb + SZ_SPCI_STATE <= im_vb I \/ im_vb I + 8 * im_vcap I <= stb) ->
    (0 < im_vcap I -> im_vb I + 8 * im_vcap I <= implb \/ implb + SZ_SPCI_IMPL <= im_vb I) ->
    (st_fb S <> FB_empty -> fb_off (st_fb S) stb SZ_SPCI_STATE /\ fb_off (st_fb S) implb SZ_SPCI_IMPL
                            /\ (0 < im_vcap I -> fb_off (st_fb S) (im_vb I) (8 * im_vcap I))) ->
    AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ASTATE_DTOR_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 -> athr_cells m ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    as_chain H m (bv_unsigned s0) CH -> pf_ok (as_TR H) APF_c7bf0 (bv_unsigned ra) CH ->
    (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> 0 <= bv_unsigned s0 < 2^64 ->
    sd_cost (st_fb S) <= as_AL H s ->
    as_SR H (state_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF stb implb lo B shi S I errv m mo)
      (mkCfg msF mo).
End W3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W4.
  Variable H : asr.

Definition scs_cost (Fb : fbv) : Z := sd_cost H Fb + as_Cf H SZ_SPCI_STATE.

Definition shcount_dtor_state_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (stb implb lo B shi : Z) (S : statev) (I : implv) (errv : word) (m : mem) (mo : Model)
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
    /\ AImplBlockC (as_lb_remove H p (sd_LB H (st_fb S) pf LB)) m' implb (impl_weak I 1)
    /\ AXStatics2 m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) (scs_X stb implb (st_fb S) ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - scs_cost (st_fb S).

Definition shcount_dtor_state_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (PC stb ioc implb lo B shi : Z) (S : statev) (ds : list byte) (I : implv)
         (errv : word) (CH : list (Z * Z)),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_SHCOUNT_DTOR) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 PC ->
    (* [comment removed for export] *)
    ro_cells bsegs m PC [C8 (wz stb)] -> cobj LB LF (bv_unsigned sp) shi PC 8 -> PC mod 8 = 0 -> accessible m PC 8 ->
    (* [comment removed for export] *)
    AStateBlock LB m stb ioc implb S ds -> st_hdr S = mkSPC AVP_SPCI_STATE 1 1 1 ->
    (* [comment removed for export] *)
    AImplBlockC LB m implb I -> spc_weak (im_hdr I) = 2 ->
    (stb + SZ_SPCI_STATE <= implb \/ implb + SZ_SPCI_IMPL <= stb) ->
    (0 < im_vcap I -> stb + SZ_SPCI_STATE <= im_vb I \/ im_vb I + 8 * im_vcap I <= stb) ->
    (0 < im_vcap I -> im_vb I + 8 * im_vcap I <= implb \/ implb + SZ_SPCI_IMPL <= im_vb I) ->
    (st_fb S <> FB_empty -> fb_off (st_fb S) stb SZ_SPCI_STATE /\ fb_off (st_fb S) implb SZ_SPCI_IMPL
                            /\ (0 < im_vcap I -> fb_off (st_fb S) (im_vb I) (8 * im_vcap I))) ->
    (PC + 8 <= stb \/ stb + SZ_SPCI_STATE <= PC) ->
    AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ASHCOUNT_DTOR_STATE_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 -> athr_cells m ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    as_chain H m (bv_unsigned s0) CH -> trace_ok (as_TR H) APC0_FREE (bv_unsigned ra :: map snd CH) ->
    (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
    scs_cost (st_fb S) <= as_AL H s ->
    as_SR H (shcount_dtor_state_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF stb implb lo B shi S I errv m mo)
      (mkCfg msF mo).
End W4.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W5.
  Variable H : asr.

Definition sci_cost (vcap : Z) : Z := as_Cf H (8 * vcap) + as_Cf H SZ_SPCI_IMPL.

Definition shcount_dtor_impl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (implb vb vcap lo B shi : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (pi q : bptr),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ In (pi, implb, SZ_SPCI_IMPL) LB /\ In (q, vb, 8 * vcap) LB
    /\ as_RHEAP H s' (as_lb_remove H pi (as_lb_remove H q LB)) m'
    /\ AXStatics2 m'
    /\ xpres H LB (bv_unsigned sp) (blkX implb SZ_SPCI_IMPL ++ blkX vb (8 * vcap)) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - sci_cost vcap.

Definition shcount_dtor_impl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (PC implb lk vb vcap lo B shi : Z) (errv : word) (CH : list (Z * Z)),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_SHCOUNT_DTOR) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 PC ->
    ro_cells bsegs m PC [C8 (wz implb)] -> aobj LB LF PC 8 -> PC mod 8 = 0 -> accessible m PC 8 ->
    (PC + 8 <= implb \/ implb + SZ_SPCI_IMPL <= PC) -> (PC + 8 <= vb \/ vb + 8 * vcap <= PC) ->
    AImplBlockC LB m implb (mkIMPL (mkSPC AVP_SPCI_IMPL 1 1 1) lk vb [] vcap) -> 0 < vcap -> 8 * vcap <= 2^16 ->
    (vb + 8 * vcap <= implb \/ implb + SZ_SPCI_IMPL <= vb) ->
    AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ASHCOUNT_DTOR_IMPL_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
    as_chain H m (bv_unsigned s0) CH -> trace_ok (as_TR H) APC0_FREE (bv_unsigned ra :: map snd CH) ->
    (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
    sci_cost vcap <= as_AL H s ->
    as_SR H (shcount_dtor_impl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF implb vb vcap lo B shi errv m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
Definition ssvc_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (v implb vb vcap lo B shi : Z) (S : svch) (errv : word) (m : mem) (mo : Model)
    : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (pi q : bptr),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ In (pi, implb, SZ_SPCI_IMPL) LB /\ In (q, vb, 8 * vcap) LB
    /\ as_RHEAP H s' (as_lb_remove H pi (as_lb_remove H q LB)) m'
    /\ AStreamSvc (as_lb_remove H pi (as_lb_remove H q LB)) m' v S implb
    /\ AXStatics2 m'
    /\ xpres H LB (bv_unsigned sp) ((v, v + 8) :: blkX implb SZ_SPCI_IMPL ++ blkX vb (8 * vcap)) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - sci_cost vcap.

Definition ssvc_dtor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (v implb lk vb vcap lo B shi : Z) (S : svch) (errv : word) (CH : list (Z * Z)),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_SSVC_DTOR) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 v ->
    AStreamSvc LB m v S implb ->
    AImplBlockC LB m implb (mkIMPL (mkSPC AVP_SPCI_IMPL 1 1 1) lk vb [] vcap) -> 0 < vcap -> 8 * vcap <= 2^16 ->
    (vb + 8 * vcap <= implb \/ implb + SZ_SPCI_IMPL <= vb) ->
    AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ASSVC_DTOR_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
    as_chain H m (bv_unsigned s0) CH -> trace_ok (as_TR H) APC0_FREE (bv_unsigned ra :: map snd CH) ->
    (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
    sci_cost vcap <= as_AL H s ->
    as_SR H (ssvc_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v implb vb vcap lo B shi S errv m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
Definition dos_cost : Z := sci_cost 1 + as_Cf H NEWSZ_SSVC.

Definition dealloc_obj_ssvc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (v implb allocb vb lo B shi : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
  fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (pv pi q : bptr),
    as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ In (pv, v, NEWSZ_SSVC) LB /\ In (pi, implb, SZ_SPCI_IMPL) LB /\ In (q, vb, 8) LB
    /\ as_RHEAP H s' (as_lb_remove H pv (as_lb_remove H pi (as_lb_remove H q LB))) m'
    /\ AAllocImpl (as_lb_remove H pv (as_lb_remove H pi (as_lb_remove H q LB))) m' allocb
    /\ AXStatics2 m'
    /\ xpres H LB (bv_unsigned sp) (blkX v NEWSZ_SSVC ++ blkX implb SZ_SPCI_IMPL ++ blkX vb 8) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - dos_cost.

Definition dealloc_obj_ssvc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (AT v implb allocb vb lo B shi : Z) (S : svch) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_DEALLOC_OBJ_SSVC) fc None m (seg_rom bsegs) ->
    a0 = Z_to_bv 64 AT -> a1 = Z_to_bv 64 v ->
    ro_cells bsegs m AT [C8 (wz allocb)] -> bv_unsigned sp <= AT -> AT + 8 <= shi -> AT mod 8 = 0 ->
    AStreamSvc LB m v S implb -> AImplBlockC LB m implb (mkIMPL (mkSPC AVP_SPCI_IMPL 1 1 1) 0 vb [] 1) ->
    AAllocImpl LB m allocb -> AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADOBJ_SSVC_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    dos_cost <= as_AL H s ->
    as_SR H (dealloc_obj_ssvc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v implb allocb vb lo B shi errv m mo)
      (mkCfg msF mo).
End W5.

End HCW.

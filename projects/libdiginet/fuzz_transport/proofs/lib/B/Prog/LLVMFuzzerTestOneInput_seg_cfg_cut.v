(* LLVMFuzzerTestOneInput_seg_cfg_cut: proves no function (kind: the cut inside the CFG segment of
   LLVMFuzzerTestOneInput's image-B walk, and the statement of the stage that reaches it).

   The CFG segment of fuzz_transport.asan-ubsan's LLVMFuzzerTestOneInput runs from the return of
   diginet_session_config_default (+0x358, lc_st_cfgd of lib/B/Prog/LLVMFuzzerTestOneInput_segs.v) to the point
   before the memset of M (+0x4b0, lc_st_scal). It is proved in two files, which meet at +0x3a0, the return of the
   second __asan_memcpy:

     stage  +0x358 .. +0x39c  the arguments and the two __asan_memcpy calls (g_cfg [0, 6) := HOST at 0x81608 and
                              g_cfg [6, 12) := DESK at 0x8163c) and the three flag bits the code stores between
                              them (desk_mac_set, auto_wake, sum_mode, into g_cfg [12, 24));
     run C  +0x3a0 .. +0x4ac  the fourteen config bytes at the cursor and the stores they feed.

   lc_st_cfgc below is that meeting point: lc_st_cfgd's own facts at +0x3a0, plus s6 (the desk_mac_set bit the
   stage computes at +0x37c) and the world after the five model updates the stage makes (lc_cfg_b1: host_mac,
   auto_wake, sum_mode, desk_mac_set, desk_mac, the first five of lc_pro_scal). It is absolute, like the walk's
   other cuts: it names no memory of an earlier point. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TSess0 TOps.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.

(* +0x3a0, the return of the second __asan_memcpy. *)
Definition CF_RC2 : Z := 0x3a0.

(* The five updates the stage makes to config_default's world: lc_pro_scal's first five. *)
Definition lc_cfg_b1 (D : list byte) (B1 : list byte) : list byte :=
  let flags := lc_flags D in
  TW.set_Cfg_desk_mac
    (TW.set_Cfg_desk_mac_set
       (TW.set_Cfg_sum_mode
          (TW.set_Cfg_auto_wake (TW.set_Cfg_host_mac B1 TC.HOST) (Z.land flags 1))
          (if Z.land flags 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO))
       (Z.land (Z.shiftr flags 2) 1))
    TC.DESK.

Section cut. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* The cut: lc_st_cfgd's facts at +0x3a0, with s6 the desk_mac_set bit and the world after the stage's five
   updates. The cursor, s5 = g_cfg, s4 = io, s2 / s10 the shadow addresses and the two frame spill slots are the
   cut's own, unchanged by the stage. *)
Definition lc_st_cfgc (cx : lcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' Bw0 B1,
    c' = lc_cfg cx CF_RC2 regs' mem' md' /\
    @lc_core rc B cx ly' S' W' regs' mem' md' 0 /\ lc_fr cx regs' /\
    lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W') mem') /\
    lc_fsh cx (aview segs (w_H W') mem') false false /\ lc_io cx W' mem' /\
    lc_meter MT cx S' 0 /\
    lc_cur cx regs' 19 23 (lc_c1 (l_pl cx)) /\ YK11.getr regs' 24 = w64 (lc_flags (l_pl cx)) /\
    YK11.getr regs' 21 = w64 TB_g_cfg /\ YK11.getr regs' 20 = w64 (lc_F cx + 176) /\
    YK11.getr regs' 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) /\
    lc_w0 cx Bw0 /\ TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) /\
    lc_tw W' mem' (lc_cfg_b1 (l_pl cx) B1).

(* The stage: from the segment's entry to the cut. K1 reads the image's HOST and DESK bytes, K2 gives the two
   __asan_memcpy calls their sources' read-only facts (trans_src_ok of TRANS_HOST and TRANS_DESK). *)
Definition lc_cfg_stage_stmt : Prop :=
  @lc_rom_view_stmt rc B MT XL RLO RHI -> @lc_src_ro_stmt rc B MT XL RLO RHI ->
  @lp_prem rc B MT XL RLO RHI ->
  forall (cx : lcx) (W' : world segs) (c' : config),
    @lc_base rc B MT XL RLO RHI cx -> @lc_st_cfgd rc B MT cx W' c' -> SRr segs W' c' (lc_st_cfgc cx).

End cut.

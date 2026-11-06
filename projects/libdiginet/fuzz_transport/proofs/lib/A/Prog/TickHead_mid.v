(* TickHead_mid: the head piece's own cut at its call of __asan_set_shadow_f8 (+0x1ac, return address +0x1b0), as
   STATEMENTS only. The head of the walk of diginet_session_tick (lib/A/Prog/TickCut.v tick_head_stmt) is proved in three
   parts: lib/A/Prog/TickHead_entry.v walks from the entry to the call (tkh_call_at -> the holds statement),
   lib/A/Prog/TickHead_disp.v walks from the return to the cuts wake, online, step and epi (tkh_ret_at), and
   lib/A/Prog/TickHead.v joins them by the call (TransportGRt.v gx_set_shadow_at). tkh_mid is what holds at both the
   call and the return: the caller's G journal with the class-5 frame owned, the frame on top of the call's frames, the
   call's blocks, the meter, what the call keeps (acall_kept_g with no written byte outside the window and the own
   frame), every byte of G the call's, the 13 saved words, the frame's flag word, now at s1 + 56, and the registers the
   code after the call reads or hands on. *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg TickCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The call `jal __asan_set_shadow_f8` (+0x1ac) and its return address (+0x1b0), as offsets from the listing's base. *)
Definition TKH_SS : Z := AF_diginet_session_tick + 0x1ac.
Definition TKH_RET : Z := AF_diginet_session_tick + 0x1b0.

(* The registers at the call and at the return: tick_regs_base (sp = s1 = sp1, gp, tp, s0 = the entry sp,
   s2 = s11 = the frame), s3 = the frame's shadow address, s4 = s, s6 = the body's shadow address (frame + 384), s8 =
   the shadow base. *)
Definition tkh_regs (regs rg : bvmap 5 word) (sp1 F : Z) : Prop :=
  tick_regs_base regs rg sp1 F /\
  YK11.getr rg 19 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr rg 20 = w64 TICK_S /\
  YK11.getr rg 22 = w64 (SHADOW_OFF + F / 8 + 48) /\ YK11.getr rg 24 = w64 SHADOW_OFF.

Section mid. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The state at the call and at the return, at memory M and model MD with registers rg. *)
Definition tkh_mid (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (now : Z) (pos sp1 F : Z)
    (S2 : astate) (M : word -> option byte) (MD : Model) (rg : bvmap 5 word) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) lyc S2 W M MD k /\
  frames S2 = (TICK_CID, pos) :: frames Sc /\
  ablocks B lyc S2 = ablocks B lyc Sc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W M (spZ regs - TICK_STK) (spZ regs) (fun _ => False) /\
  gx_kept segs TG.G_HARNESS W memc W M /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) M) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) TICK_SAVED /\
  rdword (aview segs (w_H W) M) (F + TICK_FBYTES - 8) = Some (flag_addr lyc TICK_CID pos) /\
  rdword (aview segs (w_H W) M) (sp1 + 56) = Some now /\
  tkh_regs regs rg sp1 F.

(* The call cut: at the callee's entry with a0 = the body's shadow address, a1 = 186 and ra = the return address. *)
Definition tkh_call_at : Prop :=
  tick_laws B MT -> tick_callees B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate)
         (M : word -> option byte) (MD : Model) (rg : bvmap 5 word),
    tick_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tkh_mid STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now pos sp1 F S2 M MD rg ->
    YK11.getr rg 10 = w64 (SHADOW_OFF + F / 8 + 48) -> YK11.getr rg 11 = w64 186 ->
    YK11.getr rg 1 = Z_to_bv 64 (BASE + TKH_RET) ->
    SRr segs W (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_set_shadow_f8)) M (YK11.seg_rom segs)) MD)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The return cut: at the return address. *)
Definition tkh_ret_at : Prop :=
  tick_laws B MT -> tick_callees B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (S2 : astate)
         (M : word -> option byte) (MD : Model) (rg : bvmap 5 word),
    tick_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tkh_mid STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now pos sp1 F S2 M MD rg ->
    SRr segs W (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TKH_RET)) M (YK11.seg_rom segs)) MD)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).
End mid.

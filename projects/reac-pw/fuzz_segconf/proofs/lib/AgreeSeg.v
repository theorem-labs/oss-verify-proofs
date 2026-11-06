From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YN2b.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import
  ZTraceSpec ZAllocator Contract FrameAPI AllocSlots AllocRoom SlotAgree AgreeCap AgreeShape AgreeFrame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require SlotTopG CallocBigC CallocHolds.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require SegSlot SegEnd SegSlotAG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Tac_slot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require FrameProof SlotTopG ZAllocator AllocCf AgreeZlib
  FrameAPI SlotAgree CallocBigC CallocHolds.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require SlotFR SlotInv SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Tac_slot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.SegCF Require SlotTopCF.
Import ListNotations.
Open Scope Z_scope.

(* reac-pw/fuzz_segconf's ubsan_agrees (Statements.v: agrees_in Env.alloc_forced_only lim_source lim_target
   Images.plain Images.ubsan) by the frame's AgreeFrame.ubsan_agrees_of_slots at the agreement shape
   ag_shape checksum_shape (sb_cap = CAP_AG), in the form of reac-pw/fuzz_pin's AgreePin.v (commit
   a2a7540da98), with segconf's G and GI in both builds (G = frame_G = longl, plain 0x32ac0 / UBSan 0x33460, 121
   bytes; GI = GI_SLOT: longl[120] = 0):
   - the plain slot in its halts (realizes) form at the agreement shape (Prog/SegSlotAG.slot_of_lemmas_ag over the
     plain segment lemmas, Prog/SegEnd.segs_holds, taken at the halts shape checksum_shape);
   - the UBSan slot in cut-free form (U/Prog/SegCF/SlotTopCF.segconf_ubsan_slot_cg over the cut-free copies of the
     UBSan walks and the cut-free lifts of the UBSan evt statements), from its cut-free frame facts at the zlib
     instance and the agreement shape (ubsan_frame_facts);
   - the allocator steps in the cut-free slot's form: the frame's cut-free malloc (AllocCf.zlib_malloc_contract_cf)
     and the cut-free calloc (CallocHolds.calloc_cf_holds) give malloc_contract_cfg and
     calloc_contract_cfg (room_ag: room_slots, sb_cap <= CAP_AG, sb_bytes + n <= 2^29) under the zlib run-limit law
     2^34 <= vm_limit (AgreeZlib.zlib_limit): malloc_cfg_of_cf (pin's) and calloc_cfg_of_cf (libreac/fuzz_decode's
     U/Prog/LLVMFuzzerTestOneInput_cfb.v calloc_ag_of_cf, commit 25e3d17bdb50, at the big cap);
   - the room of the driver's calls at SBD_AG for every payload: AgreeShape.ag_room_calls.
   ubsan_agrees_of_callees is the agreement modulo the segment statements of both builds (the plain walks' SegEnd
   statements, the UBSan cut-free statements of E01, L01, L03, M02, X01 and the UBSan evt statements of M01, L02,
   V01), the evt-callee contracts K_<seg> of both builds and the two cut records.
   Proves no function (kind: agreement composition of LLVMFuzzerTestOneInput's two slots). *)

Local Abbreviation AGS := (ag_shape checksum_shape).
Local Abbreviation U_B := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable.YH02.src0_msyms.
Local Abbreviation U_API := (@OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.ZAllocator.zlib_API).
Local Abbreviation U_SH := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable.YI5b.src0_sink_head.
Local Abbreviation U_SK := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable.YI5c.src0_sink.
Local Abbreviation U_RA := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable.YL0s.RA_LIB.
Local Abbreviation U_EMPTY := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable.YL0s.EMPTY.

(* The plain slot at the agreement shape, from the plain segment lemmas at the concrete instance. *)
Lemma plain_slot_ag : forall CP : cut_preds,
  (forall (fx : FPState) (rc : RunCeil),
     OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.LLVMFuzzerTestOneInput_c.seg_lemmas
       src0_msyms (@zlib_API) RA_LIB EMPTY CP) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_g fx rc AGS src0_msyms (@zlib_API rc) src0_sink_head src0_sink frame_G frame_RELRO
    (GI_SLOT (ms_segs src0_msyms)) j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros CP SEGS rc fx j Hj.
  exact (lib.Prog.SegSlotAG.slot_of_lemmas_ag (fx := fx) (rc := rc) (LS := AGS) (SH := src0_sink_head) (SK := src0_sink)
           src0_msyms (@zlib_API) RA_LIB EMPTY CP checksum_shape lib.Prog.SegSlot.frame_facts_concrete
           (fun pl fs K => eq_refl) (fun n b => eq_refl) (fun b n H => ag_room_g checksum_shape b n H)
           (SEGS fx rc) j Hj).
Qed.

(* The frame's cut-free malloc contract (room_cf) gives the slot's form (malloc_contract_cfg, room_ag) under the
   run-limit law (AgreeZlib.zlib_limit at the zlib instance): pin's AgreePin.malloc_cfg_of_cf. *)
Lemma malloc_cfg_of_cf : forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B),
  (forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md)) ->
  U.SlotAgree.malloc_contract_cf (fx := fx) (rc := rc) B API ->
  U.Prog.SlotInvCF.malloc_contract_cfg (rc := rc) (fx := fx) B API.
Proof.
  intros rc fx B API HLIM HM L A regs mem md n b CP RO H10 RES (HR & Hc & Hb).
  apply (HM L A regs mem md n b CP RO H10 RES).
  destruct CP as (HMR & _).
  exact (room_cf_of_limit md b n (HLIM L A mem md HMR) HR Hc Hb).
Qed.

(* The cut-free calloc contract (room_cf, m * n <= CALLOC_BIG_CAP) gives the slot's form
   (calloc_contract_cfg, room_ag) the same way: libreac/fuzz_decode's calloc_ag_of_cf at the big cap. *)
Lemma calloc_cfg_of_cf : forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B) (pc : Z),
  (forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md)) ->
  U.CallocBigC.calloc_contract_big_cf (fx := fx) (rc := rc) B API pc ->
  U.Prog.SlotInvCF.calloc_contract_cfg (rc := rc) (fx := fx) B API pc.
Proof.
  intros rc fx B API pc HLIM HC L A regs mem md m n b CP RO Hm Hn Hm0 Hn0 Hcap RES (HR & Hc & Hb).
  apply (HC L A regs mem md m n b CP RO Hm Hn Hm0 Hn0 Hcap RES).
  destruct CP as (HMR & _).
  exact (room_cf_of_limit md b (m * n) (HLIM L A mem md HMR) HR Hc Hb).
Qed.

(* calloc in the cut-free slot's form at the UBSan concrete instance. *)
Lemma calloc_cf_concrete_holds : U.Prog.SegCF.SlotTopCF.calloc_cf_concrete.
Proof.
  intros fx rc.
  exact (calloc_cfg_of_cf rc fx _ _ _ (U.AgreeZlib.zlib_limit rc) (@U.CallocHolds.calloc_cf_holds fx rc)).
Qed.

(* calloc at the plain concrete instance (Prog/SegEnd.calloc_concrete): CallocHolds.calloc_holds. *)
Lemma plain_calloc_concrete : lib.Prog.SegEnd.calloc_concrete.
Proof. intros fx rc. exact (@lib.CallocHolds.calloc_holds fx rc). Qed.

(* The cut-free frame facts at the UBSan zlib instance and the agreement shape. *)
Lemma ubsan_frame_facts : U.Prog.SlotInvCF.frame_facts_cf U_B U_API AGS U_SH U_SK U_RA U_EMPTY.
Proof.
  unfold U.Prog.SlotInvCF.frame_facts_cf.
  split; [exact U.SlotTopG.ms_segs_rsegs|].
  split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact U.FrameProof.errno_below_ceiling|].
  do 14 (split; [reflexivity|]).
  do 3 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [split; vm_compute; reflexivity|].
  split; [exact U.FrameProof.ctx_not_ro|].
  split; [exact U.FrameProof.frame_G_facts|].
  split; [exact U.FrameProof.frame_RELRO_facts|].
  split; [intros pl fs K; reflexivity|].
  split; [intros n b; reflexivity|].
  split; [exact (ag_room_cg checksum_shape)|].
  intros rc fx.
  destruct (U.FrameProof.zlib_frame_allocator rc fx) as (_ & _ & _ & R).
  exact (conj (malloc_cfg_of_cf rc fx _ _ (U.AgreeZlib.zlib_limit rc) (@U.AllocCf.zlib_malloc_contract_cf fx rc))
          (conj (@U.AllocCf.zlib_free_contract_cf fx rc) (conj (@U.AllocCf.src0_free_null_cf fx) R))).
Qed.

Theorem ubsan_agrees_of_callees :
  forall (CPp : cut_preds) (KpM01 KpL01 KpL02 KpM02 KpV01 : Prop)
         (CPu : U.Prog.SlotInv.cut_preds) (KuM01 KuL01 KuL02 KuM02 KuV01 : Prop),
  (* the plain walks (Prog/SegEnd.v's statements) and their evt-callee contracts *)
  lib.Prog.SegEnd.seg_E01_stmt CPp -> lib.Prog.SegEnd.seg_M01_stmt CPp KpM01 -> lib.Prog.SegEnd.seg_L01_stmt CPp KpL01 ->
  lib.Prog.SegEnd.seg_L02_stmt CPp KpL02 -> lib.Prog.SegEnd.seg_L03_stmt CPp -> lib.Prog.SegEnd.seg_M02_stmt CPp KpM02 ->
  lib.Prog.SegEnd.seg_V01_stmt CPp KpV01 -> lib.Prog.SegEnd.seg_X01_stmt CPp ->
  KpM01 -> KpL01 -> KpL02 -> KpM02 -> KpV01 ->
  (* the UBSan cut-free walks, the UBSan evt statements and their evt-callee contracts *)
  U.Prog.SegCF.SlotTopCF.seg_E01_cf_stmt CPu -> U.Prog.SegCF.SlotTopCF.evt_M01_stmt CPu KuM01 ->
  U.Prog.SegCF.SlotTopCF.seg_L01_cf_stmt CPu KuL01 -> U.Prog.SegCF.SlotTopCF.evt_L02_stmt CPu KuL02 ->
  U.Prog.SegCF.SlotTopCF.seg_L03_cf_stmt CPu -> U.Prog.SegCF.SlotTopCF.seg_M02_cf_stmt CPu KuM02 ->
  U.Prog.SegCF.SlotTopCF.evt_V01_stmt CPu KuV01 -> U.Prog.SegCF.SlotTopCF.seg_X01_cf_stmt CPu ->
  KuM01 -> KuL01 -> KuL02 -> KuM02 -> KuV01 ->
  Statements.ubsan_agrees.
Proof.
  intros CPp KpM01 KpL01 KpL02 KpM02 KpV01 CPu KuM01 KuL01 KuL02 KuM02 KuV01
    PE01 PM01 PL01 PL02 PL03 PM02 PV01 PX01 KPM01 KPL01 KPL02 KPM02 KPV01
    UE01 UM01 UL01 UL02 UL03 UM02 UV01 UX01 KUM01 KUL01 KUL02 KUM02 KUV01.
  pose proof (lib.Prog.SegEnd.segs_holds CPp KpM01 KpL01 KpL02 KpM02 KpV01 PE01 PM01 PL01 PL02 PL03 PM02 PV01 PX01
                KPM01 KPL01 KPL02 KPM02 KPV01 plain_calloc_concrete) as SEGS.
  apply (ubsan_agrees_of_slots AGS frame_G (GI_SLOT (ms_segs src0_msyms))
           U.FrameAPI.frame_G (U.Prog.SlotFR.GI_SLOT (ms_segs U_B))).
  - intros a Ha. exact Ha.
  - intros j m m' Hm HG. unfold GI_SLOT, GIb in *. rewrite (Hm _ lib.Prog.Seg.Tac_slot.sl_longl_nul_in). exact HG.
  - intros mem Himg. unfold GI_SLOT, GIb. rewrite (Himg _ lib.Prog.Seg.Tac_slot.sl_longl_nul_in).
    rewrite lib.SlotTopG.ms_segs_rsegs. exact lib.Prog.Seg.Tac_slot.sl_longl_nul.
  - exact (plain_slot_ag CPp SEGS).
  - intros data. apply ag_room_calls.
  - intros a Ha. exact Ha.
  - intros j m m' Hm HG. unfold U.Prog.SlotFR.GI_SLOT, U.Prog.SlotFR.GIb in *.
    rewrite (Hm _ U.Prog.Seg.Tac_slot.sl_longl_nul_in). exact HG.
  - intros mem Himg. unfold U.Prog.SlotFR.GI_SLOT, U.Prog.SlotFR.GIb.
    rewrite (Himg _ U.Prog.Seg.Tac_slot.sl_longl_nul_in).
    rewrite U.SlotTopG.ms_segs_rsegs. exact U.Prog.Seg.Tac_slot.sl_longl_nul.
  - intros rc fx j Hj.
    exact (U.Prog.SegCF.SlotTopCF.segconf_ubsan_slot_cg CPu KuM01 KuL01 KuL02 KuM02 KuV01
             UE01 UM01 UL01 UL02 UL03 UM02 UV01 UX01 KUM01 KUL01 KUL02 KUM02 KUV01 calloc_cf_concrete_holds
             fx rc AGS ubsan_frame_facts j Hj).
Qed.

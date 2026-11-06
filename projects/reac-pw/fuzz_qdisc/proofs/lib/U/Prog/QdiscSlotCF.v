(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v; 94 of its 156 lines of code are new or changed and 400 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocPackCf.v, with its module paths and module names changed; 167 of its 193 lines of code are new or changed and 130 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/CF/SRCF.v, with its module paths changed; 8 of its 32 lines of code are new or changed and 169 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/KindBGlueCf.v, with its module paths and module names changed; 184 of its 207 lines of code are new or changed and 9 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
  YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U Require Import Contract KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U Require Import FrameAPI SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Prog Require QdiscSlot.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Reusable Require YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U Require ZAllocator FrameProof ZTraceSpec.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U Require Img0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Lib Require MState Mem Frame Exec.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Prog Require reac_qdisc_etf_catchup_slots_c reac_qdisc_etf_catchup_slots check_slots_c
  check_slots LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput.
Import ListNotations.
Local Open Scope Z_scope.


(* The qdisc ubsan slot in the cut-free form of the agreement frame (SlotAgree.lib_contract_cg): the same run as
   QdiscSlot.qdisc_slot, lifted by evt_SRcf instead of evt_SR. *)

Section RunCf.
Variable B : malloc_syms.
Let segs := ms_segs B.

Lemma kb_run_cf : forall {fx : FPState} regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop)
    (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt segs (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom segs) /\ K R pc' mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom segs)) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     SRcf B (mkCfg (mkst regs' pc' mem' (seg_rom segs)) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom segs)) md) P.
Proof.
  intros fx regs pc mem md K P Hh Hl HE HK.
  eapply (evt_SRcf_canon B (mkst regs pc mem (seg_rom segs)) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & pc' & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' HKR). apply kb_getr_eqv. exact HR.
Qed.

End RunCf.

Section QdiscSlotCF.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis HSEGS : ms_segs B = Img0.rsegs.
Hypothesis HLIBK : forall pl fs K, LIBK pl fs K = K (LL 0 fs []).
Hypothesis HDELTA : forall n b, lib_delta n b = b.
Hypothesis HEMPTY : empty = 0x2d3f0.
Hypothesis HHEAD : @sk_ofl_head SH = 0x4dba0.
Hypothesis HLOCK : @sk_ofl_lock SK = 0x4db98.
Hypothesis HTHR : @sk_threaded SK = 0x4d770 + 1.
Hypothesis HRA : ra mod 2 = 0.

Lemma qdisc_slot_cg : forall j, lib_contract_cg B API [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.
Proof.
  intros j L A regs mem md p n pl b K HP _ _ HRO _ Hfrm HK.
  rewrite HLIBK.
  destruct HP as [HP0 [HLEN [HD [Hres [Hroom [HSink [Hfd [Hsorted Hsp47]]]]]]]].
  destruct HP0 as [HM [HW [HB [Hid [Hra [Hal [Hsp [HspHi [HWstack [Htp [HWerrno
    [Hptr [Hsize [Hlive Hro]]]]]]]]]]]]]].
  pose proof alloc_ceiling_val as Hceil.
  pose proof (img_low_of_check B 4294967296 (QdiscSlot.qdisc_img_check B HSEGS)) as IMG0.
  assert (IMG : img_low B) by (apply IMG0; lia). clear IMG0.
  assert (PR : 0 <= p /\ p + n <= alloc_ceiling).
  { destruct Hlive as [[-> ->] | [Hpos [q [Hq <-]]]]; [rewrite HEMPTY; lia |].
    pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq). lia. }
  assert (Hptr' : bv_unsigned (getr regs 10) = p) by (rewrite Hptr; apply MState.unsigned_lit; lia).
  assert (Hsz' : bv_unsigned (getr regs 11) = Z.of_nat (length pl)) by (rewrite Hsize, <- HLEN; apply MState.unsigned_lit; lia).
  unfold SLOT_STACK in *.
  assert (HDB : Mem.bytes_at Img0.rsegs mem p pl).
  { rewrite <- HSEGS. split; [lia|]. split; [lia|].
    intros i Hi. change (Mem.mrd (ms_segs B) mem (Mem.wa (p + Z.of_nat i)) = nth_error pl i).
    change (Mem.mrd (ms_segs B) mem (Mem.wa (p + Z.of_nat i))) with (mbyte (ms_segs B) mem (p + Z.of_nat i)).
    rewrite (HD (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity. }
  rewrite HSEGS in HRO, HWstack, HWerrno.
  assert (STN : Frame.stk Img0.rsegs (MemNorm.normalize Img0.rsegs mem) (spZ regs - 16384) (spZ regs)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (FS : find_segment Img0.rsegs a 1 = None).
    { destruct (find_segment Img0.rsegs a 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
      destruct IMG as [_ IMG2]. rewrite HSEGS in IMG2. pose proof (IMG2 a seg E). lia. }
    assert (RO : Mem.ro_addr Img0.rsegs (Z_to_bv 64 a) = false).
    { unfold Mem.ro_addr. rewrite MState.unsigned_lit by lia. rewrite FS. reflexivity. }
    pose proof (HWstack a ltac:(lia)) as Hw.
    unfold writable_at, wview in Hw.
    destruct (mem (Z_to_bv 64 a)) as [bb|] eqn:E.
    - split.
      + unfold wview, MemNorm.normalize, Mem.wa. rewrite RO, E. discriminate.
      + exists bb. unfold Mem.mrd, MemNorm.normalize, Mem.wa. rewrite RO, E. reflexivity.
    - exfalso. rewrite MState.unsigned_lit in Hw by lia. rewrite FS in Hw. apply Hw. reflexivity. }
  pose proof (LLVMFuzzerTestOneInput.qdisc_main_holds reac_qdisc_etf_catchup_slots.qdisc_slots_holds
    check_slots.qdisc_check_holds) as MAIN.
  unfold LLVMFuzzerTestOneInput_c.qdisc_main_contract, LLVMFuzzerTestOneInput_c.LLVM_QDISC,
    LLVMFuzzerTestOneInput_c.LLVM_QDISC_STACK in MAIN.
  specialize (MAIN (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
    (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
    (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
    (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr (MemNorm.normalize Img0.rsegs mem)
    (spZ regs - 16384) pl).
  rewrite Hptr', Hsz' in MAIN.
  specialize (MAIN (MemNorm.bytes_at_normalize Img0.rsegs mem p pl HRO HDB) eq_refl (MemNorm.mem_inv_normalize Img0.rsegs mem)).
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MAIN.
  assert (PNZ : 0 < Z.of_nat (length pl) -> 0 < p).
  { intros Hl. destruct Hlive as [[Hn0 _] | [Hpos [q [Hq <-]]]]; [lia |].
    pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq). lia. }
  specialize (MAIN STN ltac:(lia) Hal ltac:(left; lia) ltac:(pose proof alloc_ceiling_lt; lia) PNZ).
  pose proof (MemNorm.evt_normalize Img0.rsegs _ _ _ _ _ _ _ _ wx_apart_rsegs HRO MAIN) as RUN.
  clear MAIN.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as [Hhalt [Hlazy _]].
  specialize (HK (LL 0 (m_fs md) [])).
  set (SP := spZ regs) in *.
  assert (HSPr : 0 <= SP < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R; unfold bv_modulus in R; exact R).
  apply (kb_run_cf B regs (Z_to_bv 64 ENTRY) mem md
    (fun R pc' mem' => pc' = MState.ret_pc (getr regs 1) /\ getr R 10 = Z_to_bv 64 0 /\
       (forall r, callee_saved r -> getr R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
       Frame.munch [(SP - 96, SP)] mem mem' /\ Frame.wmono Img0.rsegs mem mem' /\ MemNorm.ro_same Img0.rsegs mem mem')
    (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
        c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom (ms_segs B))) md' /\
        frm_zero (@fp_csr fx') /\
        lib_post_g B API [] SLOT_STACK L A regs mem md p n b (LL 0 (m_fs md) []) L' A' regs' mem' md' /\ True));
    [exact Hhalt | exact Hlazy | | | exact HK].
  - rewrite HSEGS. eapply Exec.evt_mono; [exact RUN|].
    intros s (s0 & HQ & Hrel & Hsame).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' & Es0 & MU0 & WM0 & _ & _).
    subst s0.
    destruct Hrel as (Er & Ef & Epc & Esv & Ers & Efc & Erom & Emem).
    destruct s as [sr sf spc ssv srs sfc smem srom]. cbn in Er, Ef, Epc, Esv, Ers, Efc, Erom, Emem, Hsame.
    exists sr, spc, smem. split; [subst sf ssv srs sfc srom; reflexivity|].
    split; [exact Epc|].
    split; [rewrite Er; reflexivity|].
    split; [rewrite Er; kb_saved|].
    pose proof (MemNorm.mem_rel_normalize Img0.rsegs mem HRO) as Rn.
    split; [exact (MemNorm.munch_rel Img0.rsegs _ _ _ _ _ Rn Emem Hsame MU0)|].
    split; [exact (MemNorm.wmono_rel Img0.rsegs _ _ _ _ Rn Emem Hsame WM0)|].
    exact Hsame.
  - intros R pc' mem' regs' (Epc & E10 & Esv & MU & WM & Hsame) Hreg.
    unfold SLOT_STACK in *.
    apply (SRcf_ret B).
    exists fx, L, A, regs', mem', md.
    split; [rewrite Epc, Hra, (QdiscSlot.ret_pc_even_Z ra HRA); reflexivity|].
    split; [exact Hfrm|].
    split; [|exact I].
    assert (OUT : forall x, 0 <= x < alloc_ceiling -> Frame.outside [(SP - 96, SP)] x)
      by (intros x Hx; apply outside_one; lia).
    assert (MB : forall x, 0 <= x < alloc_ceiling -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x)
      by (intros x Hx; unfold mbyte; rewrite (MU (Z_to_bv 64 x)); [reflexivity|];
          rewrite MState.unsigned_lit by lia; apply OUT; exact Hx).
    unfold lib_post_g. cbn [ll_ret ll_fs ll_out].
    split. { eapply (kb_MR_A B API L A mem mem' md); [exact HM | exact MU |]. intros x Hx _. apply OUT. exact Hx. }
    split; [exact HW|]. split; [exact HB|]. split; [exact Hid|].
    split; [rewrite Hreg; exact E10|].
    split; [intros r Hr; rewrite Hreg; apply Esv; exact Hr|].
    split. { exists (m_vmmaps md), (m_fds md), (m_statpins md). split; [apply os_upd_self | reflexivity]. }
    split. { intros q k0 Hin. exists q. split; [exact Hin | reflexivity]. }
    split.
    { intros a Ha Hns.
      assert (Ho : Frame.outside [(SP - 96, SP)] a).
      { apply outside_one. destruct (Z_lt_le_dec a (SP - 96)) as [|H1]; [left; lia|]. right.
        destruct (Z_le_gt_dec SP a) as [|H2]; [lia|]. exfalso. apply Hns. left. unfold SP in *. lia. }
      unfold mbyte, writable_at, wview. rewrite (MU (Z_to_bv 64 a)); [split; reflexivity|].
      rewrite MState.unsigned_lit by lia. exact Ho. }
    split.
    { intros a Himg _ _ _ _. destruct IMG as [IMG1 _]. pose proof (IMG1 a Himg) as Ha.
      unfold mbyte, writable_at, wview. rewrite (MU (Z_to_bv 64 a)); [split; reflexivity|].
      rewrite MState.unsigned_lit by lia. apply OUT. exact Ha. }
    split. { intros a (lo & len & Hin & _). destruct Hin. }
    split.
    { intros q k0 i Hin Hneq Hi. pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k0 HM Hin). apply MB. lia. }
    split.
    { intros a Hs. rewrite HSEGS. unfold writable_at. apply WM.
      destruct Hs as [Hs|Hs]; [exact (HWstack a Hs) | exact (HWerrno a Hs)]. }
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsorted|].
    split.
    { destruct HSink as [[T1 T2] [W1 F1]]. split; [split|split; [|exact F1]].
      - intros k0 Hk. rewrite MB; [apply T1; exact Hk|]. rewrite HTHR. lia.
      - intros k0 Hk. rewrite MB; [apply T2; exact Hk|]. rewrite HLOCK. lia.
      - intros k0 Hk. rewrite MB; [apply W1; exact Hk|]. rewrite HHEAD. lia. }
    split. { rewrite HSEGS. exact (MemNorm.ro_agree_same Img0.rsegs mem mem' HRO Hsame). }
    split. { rewrite HDELTA. exact Hres. }
    intros i Hi. apply MB. lia.
Qed.

End QdiscSlotCF.


(* The instance of the frame (U.FrameProof.frame_ubsan_holds): the form ubsan_agrees_of_slots takes. *)
Section Inst.
Import OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Reusable.YH02 OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Reusable.YI5b
  OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Reusable.YI5c OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.Reusable.YL0s
  OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.ZAllocator OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.FrameProof
  OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.U.ZTraceSpec.

Theorem qdisc_slot_cg_frame : forall (LS : lib_shape),
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) -> (forall n b, @lib_delta LS n b = b) ->
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_cg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    [] frame_RELRO (fun _ _ => True) j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros LS HL HD rc fx j _.
  apply qdisc_slot_cg.
  - reflexivity.
  - exact HL.
  - exact HD.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
Qed.

End Inst.

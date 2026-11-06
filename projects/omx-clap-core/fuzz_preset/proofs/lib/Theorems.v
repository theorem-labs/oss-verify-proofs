From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require FrameProof.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require EntrySR Statement PackSlot LinkPlain.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements.

Theorem omx_clap_core_fuzz_preset_plain_halts : Statements.plain_halts.
Proof.
  apply (Statement.plain_halts_of_frame FrameProof.frame_plain_holds).
  apply PackSlot.slot_contract_of_entry.
  intros rc fx B API SH SK ra empty stk FA.
  unfold EntrySR.entry_sr_contract. intros HS HG.
  pose proof (LinkPlain.lp_entry_sr (rc := rc) (fx := fx) (SH := SH) (SK := SK) B API HS HG FA ra empty stk) as H.
  unfold EntrySR.entry_sr_contract in H.
  exact (H HS HG).
Qed.

(* Second build (ubsan). These Requires come after the first-build theorem: the U modules share short names
   (FrameProof, Statement, PackSlot, EntrySR) with the first build's. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require FrameProof.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require EntrySR Statement PackSlot LinkUEntry.

Theorem omx_clap_core_fuzz_preset_ubsan_halts : Statements.ubsan_halts.
Proof.
  apply (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.Statement.ubsan_halts_of_frame OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.FrameProof.frame_ubsan_holds).
  apply OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.PackSlot.slot_contract_of_entry.
  intros rc fx B API SH SK ra empty stk FA.
  unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.EntrySR.entry_sr_contract. intros HS HG.
  pose proof (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.LinkUEntry.lu_entry_sr (rc := rc) (fx := fx) (SH := SH) (SK := SK) B API HS HG FA ra empty stk) as H.
  unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.EntrySR.entry_sr_contract in H.
  exact (H HS HG).
Qed.

(* ubsan_agrees, from AgreePresetH.ubsan_agrees_of_halts_pg34 at LS := ZTraceSpec.checksum_shape (the fuzz_state route):
   the plain run from the proved plain HALTS slot (AgreePresetH.preset_plain_halts_slot) and the statement's plain
   budget; the ubsan run from the ubsan cut-free slot at the 2^34 law (U zlib_limit):
   U.Prog.CF.SlotCgpg34.ubsan_slot_cgpg34 (h-hpreset-2's SlotCgpg at pack_ag34_form, rooms from PackRoomsAg34). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require AgreePresetH SlotTopG ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require SlotGI Ledger LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require SlotTopG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require SlotGI Ledger LLVMFuzzerTestOneInput_c PackSlot.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require SlotCgpg34.

Section UbsanAgrees.
Local Notation LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape.

Theorem omx_clap_core_fuzz_preset_ubsan_agrees : Statements.ubsan_agrees.
Proof.
  destruct OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AgreePresetH.preset_plain_halts_slot as (CS & HCS & HP).
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AgreePresetH.ubsan_agrees_of_halts_pg34 LS CS
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.PackSlot.CS_pre
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.LLVMFuzzerTestOneInput_c.slot_G
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.Ledger.omx_GI
       OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YH02.src0_msyms)
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.LLVMFuzzerTestOneInput_c.slot_G
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.Ledger.omx_GI
       OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.YH02.src0_msyms)
    HCS
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.Statement.slot_G_frame
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.SlotGI.slot_G_local
       OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YH02.src0_msyms)
    (fun mem H => OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.SlotGI.slot_GI_init
       OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YH02.src0_msyms mem
       OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.SlotTopG.ms_segs_rsegs H)
    HP
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.PackSlot.CS_pre_ok
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.Statement.slot_G_frame
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.SlotGI.slot_G_local
       OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.YH02.src0_msyms)
    (fun mem H => OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.SlotGI.slot_GI_init
       OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.YH02.src0_msyms mem
       OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.SlotTopG.ms_segs_rsegs H)
    (fun rc HL => @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF.SlotCgpg34.ubsan_slot_cgpg34 rc LS
       (fun pl fs K => eq_refl) HL)).
Qed.

End UbsanAgrees.

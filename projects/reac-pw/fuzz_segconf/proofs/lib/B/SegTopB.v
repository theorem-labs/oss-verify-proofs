(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the closing file of the ASan+UBSan
   build, the two statements `Statements.asan_ubsan_halts` and `Statements.asan_ubsan_agrees` from named parts only.
   The image-B twin of image A's lib/A/SegTop.v (commit 6f7a1561a103), in the place and under the name of
   plugin-hostd/fuzz_command's lib/B/CmdTopB.v (origin/ossv/recipes 501c0d516c69).

   The chain as fuzz_command's CmdTopB.v proves it, each link proved in its file and composed here:
     SegLibX.seg_lib_x_closed (lib/B/Prog/SegLibX.v, fuzz_command's lib/B/Prog/CmdLibX.v) -- the program contract C3
       (lib/B/YCfn.v tfib_lib_contract_x_all at the core's record, the trivial meter, every run ceiling and call
       index) from the contract of the program's entry function LLVMFuzzerTestOneInput;
     SegTFIBBLib.seg_TFIB_T_B_of_lib (lib/B/SegTFIBBLib.v, fuzz_command's lib/B/CmdTFIBBLib.v) -- C2: the driver and
       the start-up over the program contract, through the core's de-classed lib/B/YD1q.v (the generated start-up of
       lib/B/YB01.v / YB1n.v), with the malloc chain lib/B/YF0w.v, the free closer lib/B/YF0q.v and the module
       destructor's contract lib/B/Rt/RtDtorExit.v;
     SegAsanUbsanTop.seg_asan_ubsan_halts_of_tfib / seg_asan_ubsan_agrees_of_tfib (lib/B/SegAsanUbsanTop.v, the twin
       of fuzz_command's lib/A/AsanUbsanTop.v; the agreement's plain side is image A's lib/A/SegAsanTop.v
       seg_plain_rz at the released plain tree's lib/AgreeSeg.v plain_slot_ag and lib/Prog/SegEnd.v segs_holds) --
       the two statements from TFIB_T_B (lib/B/SegTFIBB.v).
   seg_B_tfib below composes C3 and C2: from the entry function's contract at every run ceiling and FP state
   (seg_hltoi_B, at the core's record), TFIB_T_B; it is CmdTopB.v's cmd_TFIB_T_B_of_parts.

   HLTOI -- the contract of LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput_c.v) at image B's sink head,
     the segments tfibsegs, the allocator record SegB and the trivial meter, at SegInstB's image-B terms, at every run
     ceiling and FP state: lib/B/Prog/SegProgClosed.v's seg_ltoi_all (all 36 walks composed) at the core's record.
   No Section hypothesis is left: the two statements are closed (Print Assumptions below).
   The allocator record is image B's core record lib/B/YD2l.v SegB with its symbol record SegB_syms (the image-B twin of
   image A's lib/A/AD2l.v, fuzz_command's lib/B/YD2l.v CmdB / CmdB_syms).

   THE SINK INSTANCE IS EXPLICIT. The plain build's lib/Reusable/YI5b.v (`#[global] Instance src0_sink_head`) and
   lib/Reusable/YI5c.v (`src0_sink`) are loaded below and both hints removed, so no sink argument here can be filled
   with the plain build's head; `sk_probe_is_asan_ubsan` shows what a bare `sink_head` resolves to.
   proves no function (kind: merge; the closing file of image B). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YE2k YCbp YF0m YD2l SegTFIBB SegTFIBBLib SegAsanUbsanTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require LLVMFuzzerTestOneInput_c SegProgClosed SegLibX.
Open Scope Z_scope.

(* The guard: the plain build's sink hints are out of the way (paths in full: lib/U/Reusable has modules of the same
   short names, YI16, YI5b and YI5c), and image B's head is the instance. *)
#[local] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI5c.src0_sink : typeclass_instances.
#[local] Existing Instance YE2k.tfib_sink_head.

(* What a bare `sink_head` resolves to in this file: the ASan+UBSan image's own head. *)
Definition sk_probe : OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI16.sink_head := _.
Lemma sk_probe_is_asan_ubsan : sk_probe = YE2k.tfib_sink_head.
Proof. reflexivity. Qed.

(* The contract of the program's entry function at image B's terms, at every run ceiling and FP state: the
   conclusion of lib/B/Prog/SegProgClosed.v's seg_ltoi_all, and fuzz_command's CmdTopB.v HLTOI. *)
Definition seg_hltoi_B (B : asyms) : Prop := forall (rc : YM05.RunCeil) (fx0 : YK11.FPState),
  @LLVMFuzzerTestOneInput_c.LLVMFuzzerTestOneInput_contract fx0 rc YE2k.tfib_sink_head tfibsegs B YCbp.ameter_triv
    A_LLVMFuzzerTestOneInput_A STK_LLVMFuzzerTestOneInput emptyA RLO_A RHI_A longlA mod40A catA wordsA rolesA gotwA
    guardA seg_litA_fz seg_litA_rc.

(* HLTOI's text is seg_ltoi_all's, at every run ceiling (the type of this term checks it) *)
Lemma seg_hltoi_of_closed : forall (B : asyms) (P : YM05.RunCeil -> Prop),
  (forall rc, P rc -> forall fx0 : YK11.FPState,
    @LLVMFuzzerTestOneInput_c.LLVMFuzzerTestOneInput_contract fx0 rc YE2k.tfib_sink_head tfibsegs B
      YCbp.ameter_triv A_LLVMFuzzerTestOneInput_A STK_LLVMFuzzerTestOneInput emptyA RLO_A RHI_A longlA mod40A catA
      wordsA rolesA gotwA guardA seg_litA_fz seg_litA_rc) ->
  (forall rc, P rc) -> seg_hltoi_B B.
Proof. intros B P H HP rc fx0. exact (H rc (HP rc) fx0). Qed.

(* seg_ltoi_all at the core's record: its record premises HB / HD are lib/B/YD2l.v's SegB_syms and eq_refl (SegB's
   as_dhash is tfib_dhash) *)
Definition seg_ltoi_SegB (rc : YM05.RunCeil) :=
  @SegProgClosed.seg_ltoi_all rc YD2l.SegB YD2l.SegB_syms (fun t => eq_refl).

(* C3 then C2 at the core's record: TFIB_T_B from the entry function's contract (fuzz_command's CmdTopB.v
   cmd_TFIB_T_B_of_parts) *)
Lemma seg_B_tfib : seg_hltoi_B YD2l.SegB -> SegTFIBB.TFIB_T_B.
Proof.
intros H. apply SegTFIBBLib.seg_TFIB_T_B_of_lib. intros rc j.
exact (@SegLibX.seg_lib_x_closed rc (H rc) j).
Qed.

Section asan_ubsan.

(* ---- the parts ----------------------------------------------------------------------------------------------- *)

(* the allocator record: the core's record (lib/B/YD2l.v SegB, with SegB_syms : YF0m.SegBSyms SegB) *)
#[local] Notation B := YD2l.SegB.

(* HLTOI: the contract of the program's entry function, at every run ceiling and FP state: seg_ltoi_all at the core's
   record (lib/B/Prog/SegProgClosed.v, all 36 walks composed) *)
Lemma HLTOI : seg_hltoi_B B.
Proof. intros rc fx0. exact (seg_ltoi_SegB rc fx0). Qed.


(* ---- the two statements, through lib/B/SegAsanUbsanTop.v ------------------------------------------------------ *)
Theorem seg_asan_ubsan_halts_of_parts : Statements.asan_ubsan_halts.
Proof. exact (SegAsanUbsanTop.seg_asan_ubsan_halts_of_tfib (seg_B_tfib HLTOI)). Qed.
Theorem seg_asan_ubsan_agrees_of_parts : Statements.asan_ubsan_agrees.
Proof. exact (SegAsanUbsanTop.seg_asan_ubsan_agrees_of_tfib (seg_B_tfib HLTOI)). Qed.
End asan_ubsan.

Print Assumptions seg_asan_ubsan_halts_of_parts.
Print Assumptions seg_asan_ubsan_agrees_of_parts.
About seg_asan_ubsan_halts_of_parts.
About seg_asan_ubsan_agrees_of_parts.
About seg_ltoi_SegB.
Print Assumptions seg_B_tfib.

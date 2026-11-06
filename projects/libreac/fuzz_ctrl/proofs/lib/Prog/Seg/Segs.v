(* The 75 segment lemmas of fuzz_ctrl's plain slot (Slot.v seg_lemmas) from frame_facts, the callee contracts
   (SlotLink.callee_contracts) and reac_ctrl_identity_fragment's contract: SlotLink's premise SEGS. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Slot SlotLink.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require A02 A03 R01 R02 R03 R04 R05 R06 R07 R08 R09 R10.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require R23 R24 P01 P02 P03 P04 P05 P06 P07 P08 P09 F01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require F02 F03 F04 F05 F06 F07 F08 F09 F10 I01 I02 G01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require G02 G03 G04 G05 G06 E01 E02 E03 E04 Q01 Q02 Q03.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Q04 Q05 Q06 C01 C02 C03 W01 W02 W03 W04 C04 C05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require C06 X01 X02.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require FrameProof.
From OSSVerify.libreac.fuzz_ctrl Require Statements.

(* A segment lemma as its file states it once its Section closes: the S_<SEG> form after its premises
   (frame_facts, the callee contracts and the allocator contracts it names), each found among the hypotheses. *)
Ltac seg L := red; intros; eapply L; eassumption.

Section Segs.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CC : callee_contracts.
Hypothesis FRAG : reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_contract.

(* malloc's and free's contracts: the first two parts of frame_facts' frame_allocator. *)
Lemma segs_alloc : malloc_contract B (APIf rc) /\ free_contract B (APIf rc).
Proof. pose proof FF as H. repeat apply proj2 in H. destruct (H rc fx) as (MAL & FRE & _). exact (conj MAL FRE). Qed.

Lemma segs : seg_lemmas B APIf ra empty.
Proof.
  destruct CC as (CATC & INIT & MSET & MSETRO & MCPY & MCPYRO & MSAME & MSAMERO & BC & BCRO & MCMP & MCMPRO & MCHR & MCHRRO & SCMP & BAS & PARSE & REPLY & ING & INGOK & MATCH & PP & DECL & DROWS & PU & KN & CKV & HRV & CLS).
  destruct segs_alloc as (MAL & FRE).
  unfold seg_lemmas.
  split; [seg A02.seg_A02|].
  split; [seg A03.seg_A03|].
  split; [seg R01.seg_R01|].
  split; [seg R02.seg_R02|].
  split; [seg R03.seg_R03|].
  split; [seg R04.seg_R04|].
  split; [seg R05.seg_R05|].
  split; [seg R06.seg_R06|].
  split; [seg R07.seg_R07|].
  split; [seg R08.seg_R08|].
  split; [seg R09.seg_R09|].
  split; [seg R10.seg_R10|].
  split; [seg R11.seg_R11|].
  split; [seg R12.seg_R12|].
  split; [seg R13.seg_R13|].
  split; [seg R14.seg_R14|].
  split; [seg R15.seg_R15|].
  split; [seg R16.seg_R16|].
  split; [seg R17.seg_R17|].
  split; [seg R18.seg_R18|].
  split; [seg R19.seg_R19|].
  split; [seg R20.seg_R20|].
  split; [seg R21.seg_R21|].
  split; [seg R22.seg_R22|].
  split; [seg R23.seg_R23|].
  split; [seg R24.seg_R24|].
  split; [seg P01.seg_P01|].
  split; [seg P02.seg_P02|].
  split; [seg P03.seg_P03|].
  split; [seg P04.seg_P04|].
  split; [seg P05.seg_P05|].
  split; [seg P06.seg_P06|].
  split; [seg P07.seg_P07|].
  split; [seg P08.seg_P08|].
  split; [seg P09.seg_P09|].
  split; [seg F01.seg_F01|].
  split; [seg F02.seg_F02|].
  split; [seg F03.seg_F03|].
  split; [seg F04.seg_F04|].
  split; [seg F05.seg_F05|].
  split; [seg F06.seg_F06|].
  split; [seg F07.seg_F07|].
  split; [seg F08.seg_F08|].
  split; [seg F09.seg_F09|].
  split; [seg F10.seg_F10|].
  split; [seg I01.seg_I01|].
  split; [seg I02.seg_I02|].
  split; [seg G01.seg_G01|].
  split; [seg G02.seg_G02|].
  split; [seg G03.seg_G03|].
  split; [seg G04.seg_G04|].
  split; [seg G05.seg_G05|].
  split; [seg G06.seg_G06|].
  split; [seg E01.seg_E01|].
  split; [seg E02.seg_E02|].
  split; [seg E03.seg_E03|].
  split; [seg E04.seg_E04|].
  split; [seg Q01.seg_Q01|].
  split; [seg Q02.seg_Q02|].
  split; [seg Q03.seg_Q03|].
  split; [seg Q04.seg_Q04|].
  split; [seg Q05.seg_Q05|].
  split; [seg Q06.seg_Q06|].
  split; [seg C01.seg_C01|].
  split; [seg C02.seg_C02|].
  split; [seg C03.seg_C03|].
  split; [seg W01.seg_W01|].
  split; [seg W02.seg_W02|].
  split; [seg W03.seg_W03|].
  split; [seg W04.seg_W04|].
  split; [seg C04.seg_C04|].
  split; [seg C05.seg_C05|].
  split; [seg C06.seg_C06|].
  split; [seg X01.seg_X01|].
  seg X02.seg_X02.
Qed.

End Segs.

(* SlotLink's premise SEGS, closed. *)
Theorem segs_holds : forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts B APIf LS SH SK ra empty -> callee_contracts ->
  reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_contract ->
  seg_lemmas B APIf ra empty.
Proof. intros fx rc B APIf LS SH SK ra empty FF CC FRAG. exact (segs B APIf ra empty FF CC FRAG). Qed.

Theorem plain_halts_holds : OSSVerify.libreac.fuzz_ctrl.Statements.plain_halts.
Proof. exact (plain_halts_of_frame segs_holds FrameProof.frame_plain_holds). Qed.

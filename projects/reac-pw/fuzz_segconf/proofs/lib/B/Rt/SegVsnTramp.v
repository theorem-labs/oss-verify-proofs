(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/SegVsnTramp.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The vsnprintf entry of reac-pw/fuzz_segconf's ASan+UBSan image B at its trampoline: __interceptor_trampoline_vsnprintf
   (SegRtPC.PC_vsnprintf) is one forward jump `j` to ___interceptor_vsnprintf (FMsnprintfImg.A_VSNI), which changes no
   register and no byte (pin fuzz_segconf.asan sha256 48c5355bdacb; the run vt_r1 below computes the one step).
   vsni_tramp carries the GXA-route vsnprintf-interceptor contract (RtPFSx.v sh_avsnprintf_icpt_realizesUa) from the
   interceptor to the trampoline, for any family and window: the one step is a symbolic run over the route's code
   table (FMsnprintfGk0.v tbl_g, which holds the trampoline block), as RtDMallocTramp.v does for malloc's trampoline;
   the model materializes (ARU kept by RtPFupoison.ARU_frame, as FMsnprintfSnp.v keeps it). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0d YP0i YP0j YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI16 YK06.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG07 YG0k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YFfk.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YB1q YE34 YF0l YF0m YF0x YE20 YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFupoison RtPFH.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import FMsnprintfImg FMsnprintfK.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import FMsnprintfGk0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFSx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require SegRtPC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the jump, symbolically: from the trampoline to the interceptor, every register an atom, no memory ---- *)
Definition vt_ss0 : sstate := mkSS SegRtPC.PC_vsnprintf sr_atoms [] None (mkFacts [] [] []).
Definition vt_e1 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_g FUEL A_VSNI vt_ss0).
Lemma vt_r1 : sym_run_toN tfibsegs tbl_g FUEL A_VSNI vt_ss0 = (vt_e1, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma vt_e1_pc : ss_pc vt_e1 = A_VSNI.
Proof. vm_compute. reflexivity. Qed.
Lemma vt_atoms : forallb (fun i : nat => sv_eqb (sr_get (ss_regs vt_e1) (Z_to_bv 5 (Z.of_nat i))) (SOff i 0)) (seq 1 31) = true.
Proof. vm_compute. reflexivity. Qed.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem vsni_tramp : forall FF K gc gv img_lo img_hi cr,
  sh_avsnprintf_icpt_realizesUa tfibsegs B FF K gc gv img_lo img_hi cr A_VSNI ->
  sh_avsnprintf_icpt_realizesUa tfibsegs B FF K gc gv img_lo img_hi cr SegRtPC.PC_vsnprintf.
Proof.
intros FF K gc gv img_lo img_hi cr HV.
intros ly S U W regs mem md d n f ap ws T cval HPRE HKlo HWIN G10 G11 G12 G13 HCV HCB HCD Hgc Hgv Hgc0 Hgc1 Hgv0 Hgv1
  Dgc Dgv HWS Hap0 Hap1 Dap HFF Hn HT Hd0 Hdn Hpw Hdst Ham Hra Hhull Hdog Hfrm Hord Hdsl H47 Hd8.
pose proof HPRE as ((HAR & Hret & H16 & Hes & Hhi & Hpe & Hgp & Htp) & Hok & Hpo).
assert (HARU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
set (EE := YE2y.Env regs []).
(* the entry state *)
assert (HS0 : st_ok tfibsegs EE vt_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 SegRtPC.PC_vsnprintf) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold vt_ss0, EE, YE2y.Env. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 SegRtPC.PC_vsnprintf) with (Z_to_bv 64 SegRtPC.PC_vsnprintf).
(* the jump *)
eapply SRr_bind; [exact (g_phase_to W EE A_VSNI vt_ss0 vt_e1 RS_running _ md HS0 vt_r1)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (Emem : ms_mem ms1 = mem).
{ apply functional_extensionality. intros x. exact (frame_of_nil EE mem (ms_mem ms1) x HF1). }
assert (GA : forall x : bv 5, 1 <= bv_unsigned x -> getr (ms_regs ms1) x = getr regs x).
{ intros x Hx. rewrite (st_ok_reg_denot (w_H W) EE vt_e1 ms1 x HS1).
  pose proof (bv_unsigned_in_range 5 x) as Rx. change (bv_modulus 5) with 32 in Rx.
  assert (Hi : In (Z.to_nat (bv_unsigned x)) (seq 1 31)) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) vt_atoms _ Hi) as Hb. apply sv_eqb_eq in Hb.
  rewrite Z2Nat.id in Hb by lia. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. cbn [sv_denot]. unfold EE.
  rewrite (YE2y.Env_reg regs [] (Z.to_nat (bv_unsigned x)) x ltac:(rewrite Z2Nat.id by lia; reflexivity)).
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
set (regs1 := ms_regs ms1) in *.
assert (G1 : getr regs1 1 = getr regs 1) by (apply GA; vm_compute; discriminate).
assert (G2 : getr regs1 2 = getr regs 2) by (apply GA; vm_compute; discriminate).
assert (G3 : getr regs1 3 = getr regs 3) by (apply GA; vm_compute; discriminate).
assert (G4 : getr regs1 4 = getr regs 4) by (apply GA; vm_compute; discriminate).
assert (Q10 : getr regs1 10 = getr regs 10) by (apply GA; vm_compute; discriminate).
assert (Q11 : getr regs1 11 = getr regs 11) by (apply GA; vm_compute; discriminate).
assert (Q12 : getr regs1 12 = getr regs 12) by (apply GA; vm_compute; discriminate).
assert (Q13 : getr regs1 13 = getr regs 13) by (apply GA; vm_compute; discriminate).
assert (SP : YG0d.spZ regs1 = YG0d.spZ regs) by (unfold YG0d.spZ; rewrite G2; reflexivity).
assert (RA : YG0d.raZ regs1 = YG0d.raZ regs) by (unfold YG0d.raZ; rewrite G1; reflexivity).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EE vt_e1 ms1 HS1 eq_refl) as Hshape.
rewrite Hshape, vt_e1_pc. fold regs1. rewrite Emem.
change (mkCfg (mkst regs1 (Z_to_bv 64 A_VSNI) mem (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs A_VSNI regs1 mem md1).
(* the interceptor's premises at the same state, the model materialized *)
assert (HA1 : ARU tfibsegs B ly S U W mem md1).
{ pose proof (same_but_materialized_frame md md1 (with_vm_backing_same md mat1)) as MF.
  apply (ARU_frame tfibsegs B LAWS ly S U W mem md mem md1 HARU);
    [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | intros; reflexivity]. }
assert (HPRE1 : ecall_preU tfibsegs B ly S U W regs1 mem md1).
{ destruct HA1 as (AR1 & OK1 & PO1). split; [|exact (conj OK1 PO1)].
  unfold YG0d.ecall_pre. rewrite SP, G1, G3, G4.
  exact (conj AR1 (conj Hret (conj H16 (conj Hes (conj Hhi (conj Hpe (conj Hgp Htp))))))). }
assert (Hdst1 : YG0d.dest_ok tfibsegs B ly S W regs1 mem d (sn_len (n - 1) T))
  by (unfold YG0d.dest_ok; rewrite SP; exact Hdst).
eapply SRr_mono.
- apply (HV ly S U W regs1 mem md1 d n f ap ws T cval HPRE1); rewrite ?SP, ?Q10, ?Q11, ?Q12, ?Q13; assumption.
- intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & FP1 & FP2 & HA' & HP' & HSB' & R10 & HB & HFR & HPM).
  split; [reflexivity|]. exists fx', regs', mem', md'.
  split; [rewrite RA; reflexivity|].
  split; [exact FP1|]. split; [exact FP2|]. split; [exact HA'|].
  split.
  { intros r Hr. rewrite (HP' r Hr).
    assert (Hr5 : bv_unsigned (Z_to_bv 5 r) = r).
    { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small.
      unfold acallee_saved in Hr. lia. }
    apply GA. rewrite Hr5. unfold acallee_saved in Hr. lia. }
  split; [eapply same_but_materialized_trans; [apply with_vm_backing_same | exact HSB']|].
  split; [exact R10|]. split; [exact HB|].
  split; [intros a Ha H1 H2; apply HFR; [exact Ha | exact H1 | rewrite SP; exact H2]|].
  exact HPM.
Qed.
End t.

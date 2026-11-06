(* Segment C02 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x13fb8, 0x13fe8]. classify != 0: to U14008.
   classify = 0: #87-#89 not taken (C31 C1.8: q.src[0 .. 3) = 00 40 ab, read from sp+1692 .. 1694), then
   bcmp(q.src = sp+1692, our = sp+114, 6) (BCMP). U13fb8 -> U13fec; U14008. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF bcmp_c bcmp_ro_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

Ltac c02_if b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b by (vm_compute; reflexivity); cbv iota
  end.

(* classify != 0 (a0 = -1): 0x13fb8 `bnez a0` to 0x14008. *)
Lemma c02_none :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 (-1) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) F (Z_to_bv 64 0x14008) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13fb8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ->.
  step. c02_if true. apply evt_done. reflexivity.
Qed.

(* classify = 0: the three oui bytes, then bcmp. *)
Lemma c02_some : bcmp_ro_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv v : Z) (ls rs : list byte),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 -> a0 = Z_to_bv 64 0 ->
    ov_read_bytes rsegs m (wa (spv + 1692)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (spv + 1693)) 1 = Some [Z_to_bv 8 64] ->
    ov_read_bytes rsegs m (wa (spv + 1694)) 1 = Some [Z_to_bv 8 171] ->
    bytes_at rsegs m (spv + 1692) ls -> bytes_at rsegs m (spv + 114) rs -> memcmp_model ls rs 6 = Some v ->
    MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13fec) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13fec) fc None m' (seg_rom rsegs) /\
         munch [] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13fb8) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv v ls rs -> Hs0 Hs1 -> R6 R7 R8 HL HR Hm MI.
  step. c02_if false.
  step. step. c02_if false.
  step. step. step. c02_if false.
  step. step. step. c02_if false.
  step. step. step. step.
  eapply evt_cut.
  { eapply BC with (ls := ls) (rs := rs) (v := v); rewrite ?MState.unsigned_lit by lia;
      first [exact HL | exact HR | exact Hm | exact MI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13fec)) with (Z_to_bv 64 0x13fec)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MU | exact WM].
Qed.

Section C02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BCMP : bcmp_ro_contract.

Lemma c02_byte : forall fr i z, cp_v fr i = z -> 0 <= z < 256 -> cp_b fr i = Z_to_bv 8 z.
Proof.
  intros fr i z H Hz. apply bv_eq. unfold cp_v in H. rewrite H. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma seg_C02 : forall j : nat, Hat B APIf ra (Inv_U13fec_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U14008_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13fb8_at B APIf ra empty) j.
Proof.
  intros j H1 H2 g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HCC & HCLS & H10)).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  destruct (t_cls (g_in g) j) as [e|] eqn:Ec.
  - pose proof HCLS as (HB & HV).
    pose proof HCC as ((HFT & HVC & HIFS) & _ & _).
    pose proof HFT as ((_ & _ & HOUR & _) & _).
    pose proof (u8_cls_B _ _ _ Ec) as EB.
    destruct (u8_cls_oui _ _ _ Ec) as (O6 & O7 & O8).
    assert (L6 : length (firstn 6 (skipn 4 (t_B (g_in g) j))) = 6%nat)
      by (rewrite length_firstn, length_skipn, u8_B_length; reflexivity).
    destruct (u8_mcmp_total _ (OUR (g_in g)) 6 L6 (OUR_length _)) as (v & Hm).
    pose proof (u8_mcmp_rng _ _ _ _ Hm) as Hv.
    pose proof (bytes_at_normalize rsegs mem _ _ HMI HB) as HBn.
    pose proof (u8_at_slice _ _ _ 4 6 HBn ltac:(rewrite u8_B_length; lia)) as HLS.
    pose proof HLS as HLS'. rewrite EB, u8_struct_src in HLS'.
    rewrite (c02_byte _ _ _ O6 ltac:(lia)), (c02_byte _ _ _ O7 ltac:(lia)), (c02_byte _ _ _ O8 ltac:(lia)) in HLS'.
    pose proof (u8_ovr _ _ _ (u8_at_slice _ _ _ 0 1 HLS' ltac:(cbn; lia))) as R6.
    pose proof (u8_ovr _ _ _ (u8_at_slice _ _ _ 1 1 HLS' ltac:(cbn; lia))) as R7.
    pose proof (u8_ovr _ _ _ (u8_at_slice _ _ _ 2 1 HLS' ltac:(cbn; lia))) as R8.
    cbn [firstn skipn length] in R6, R7, R8.
    unfold spk in *. unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    replace (g_S g - 1936 + 1688 + Z.of_nat 4 + Z.of_nat 0) with (g_S g - 1936 + 1692) in R6 by lia.
    replace (g_S g - 1936 + 1688 + Z.of_nat 4 + Z.of_nat 1) with (g_S g - 1936 + 1693) in R7 by lia.
    replace (g_S g - 1936 + 1688 + Z.of_nat 4 + Z.of_nat 2) with (g_S g - 1936 + 1694) in R8 by lia.
    replace (g_S g - 1936 + 1688 + Z.of_nat 4) with (g_S g - 1936 + 1692) in HLS by lia.
    eapply (u8_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | u8_fp_tac | | |].
    + rewrite sl_mkR_of.
      apply (c02_some BCMP) with (spv := g_S g - 1936) (v := v) (ls := firstn 6 (skipn 4 (t_B (g_in g) j)))
        (rs := OUR (g_in g)); [exact Hsp | lia | lia | | exact R6 | exact R7 | exact R8 | exact HLS | | exact Hm
        | exact (u8_ro_norm mem)].
      * unfold rg in H10. rewrite H10; try rewrite Ec; reflexivity.
      * unfold OURb in HOUR. exact (bytes_at_normalize rsegs mem _ _ HMI HOUR).
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      pose proof (fun r => sl_getr_eqv _ _ r Hx) as HG.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _).
      injection HE; intros; subst.
      apply (H1 g). exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (HK : CK regs regs') by (repeat split; rewrite HG; reflexivity).
      split; [|split; [|split]].
      * apply (u8_CC_keep g j phi regs regs' mem m' _ HCC HK (eq_trans (HG _) eq_refl) (eq_trans (HG _) eq_refl)
                 MU'); u8_dj.
      * split; [apply (u8_ba _ mem m' _ _ HB MU'); exact I | apply (u8_ba _ mem m' _ _ HV MU'); exact I].
      * rewrite Ec. discriminate.
      * assert (E10 : YK11.getr regs' 10 = Z_to_bv 64 v) by (rewrite HG; reflexivity).
        rewrite E10, (u8_bv0 v Hv).
        exact (u8_mcmp 6 _ _ v L6 (OUR_length _) Hm).
  - eapply (u8_run_to B APIf ra empty FF g _ L A regs mem md);
      [exact HFR | unfold rmk; apply c02_none; unfold rg in H10; rewrite H10; try rewrite Ec; reflexivity |].
    intros regs' HG.
    assert (HKg : forall r, YK11.getr regs' r = YK11.getr regs r) by (intros r; rewrite HG; apply kb_rmk_getr).
    apply (H2 g). exists phi. apply (u8_cut_close B APIf ra empty _ _ _ _ L A).
    + apply (u8_FR_regs B APIf ra empty _ _ _ _ regs); [exact HFR | apply HKg ..].
    + exact HP.
    + assert (HK : CK regs regs') by (repeat split; apply HKg).
      exact (u8_CC_keep g j phi regs regs' mem mem [] HCC HK (HKg _) (HKg _) (munch_refl [] mem) I I I).
Qed.

End C02.

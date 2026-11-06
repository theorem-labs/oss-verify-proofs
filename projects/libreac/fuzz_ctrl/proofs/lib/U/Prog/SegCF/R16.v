(* Segment R16 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x135b0, 0x135c0], U135b0 -> U135c4 (b = 0:
   #18 not taken (declaration_of = 1), bcmp(Φ + 18, sp+1752, 32) = 0: X(0) is the declaration of row m). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import bcmp_c bcmp_ro_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u2 Tac_u2m.
Import ListNotations.
Open Scope Z_scope.

Lemma r16_ro_norm : forall m, MemNorm.ro_agree rsegs (MemNorm.normalize rsegs m).
Proof. intros m a Ha. unfold Mem.mrd, MemNorm.normalize. rewrite Ha. reflexivity. Qed.

Lemma r16_evt : bcmp_ro_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi : Z) (l : list byte),
    sp = Z_to_bv 64 spv -> s5 = Z_to_bv 64 (phi + 18) -> a0 = Z_to_bv 64 1 ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> 0 < phi -> phi + 50 <= spv ->
    length l = 32%nat -> bytes_at rsegs m (phi + 18) l -> bytes_at rsegs m (spv + 1752) l ->
    MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x135c4) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x135c4) fc None m' (seg_rom rsegs) /\
         munch [] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x135b0) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi l -> -> -> Hsp0 Hsp Hph0 Hph Ll HL HR MI.
  step. if_false_by (u2_eqb0 1 ltac:(lia)).
  step. step. step. step.
  eapply evt_cut.
  { eapply BC with (ls := l) (rs := l) (v := 0).
    all: rewrite ?unsigned_lit by lia.
    all: first [ exact HL | exact HR | exact MI | apply u2_memcmp_refl; rewrite Ll; lia ]. }
  intros ms' PO. unfold memcmp_post_ro in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & _).
  subst ms'.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
Qed.

Section R16.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BC : bcmp_ro_contract.

Lemma seg_R16 : Hcut B APIf ra (Inv_U135c4 B APIf ra empty) -> Hcut B APIf ra (Inv_U135b0 B APIf ra empty).
Proof.
  intros H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF & H21 & H10 & HD).
  pose proof HRF as (HRB & Hnz & H20 & HF).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  destruct (u2_RS_len (g_in g) 0) as (LI & LF).
  destruct (u2_hb B APIf ra empty FF g phi (rnb g 0) L A regs mem md HFR HP) as (_ & Hphi & Hphin).
  unfold rnb, rFb, rgb in *.
  destruct (u2_rtn (g_in g) (Z.of_nat 0) Hnz) as (_ & Hnb & HL).
  change (Z.of_nat 0) with 0 in *.
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  unfold spk, SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (HG : bytes_at rsegs (normalize rsegs mem) phi (rt_g (g_in g) 0)).
  { apply u2_fr50_at; [exact (bytes_at_normalize rsegs mem phi _ HMI HF) | lia]. }
  assert (L50 : length (rt_g (g_in g) 0) = 50%nat) by apply fr50_length.
  assert (HX : bytes_at rsegs (normalize rsegs mem) (phi + 18) (RcDecl.decl (rt_mb (g_in g)))).
  { rewrite <- (u2_rtm_X0 (g_in g)). apply u2_bsl_at; [exact HG | lia | lia | rewrite L50; lia]. }
  assert (LX : length (RcDecl.decl (rt_mb (g_in g))) = 32%nat).
  { rewrite <- (u2_rtm_X0 (g_in g)). rewrite u2_bsl_len; [reflexivity | lia | lia | rewrite L50; lia]. }
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (r16_evt BC) with (spv := g_S g - 1936) (phi := phi) (l := RcDecl.decl (rt_mb (g_in g)));
      [exact Hsp | exact H21 | exact H10 | lia | lia | lia | lia | exact LX | exact HX
      | exact (bytes_at_normalize rsegs mem _ _ HMI HD) | apply r16_ro_norm].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists []. split; [exact MU|]. split; [exact WM|].
    intros z _ O. exfalso. apply O. exact I.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _).
    injection HE; intros; subst.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (KR : u2_kr regs' regs).
    { unfold u2_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
    split.
    { apply (u2_RFb_keep g 0 _ _ phi regs regs' mem m'' m' [] HMI MU Hrel LI LF I I KR); [|exact HRF].
      rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    unfold rg, spk, fsp, SLOT_FRAME in *. rewrite !(sl_getr_eqv _ _ _ Hx).
    split; [exact H21|]. split; [reflexivity|].
    apply (u2_keep [] mem m'' m' _ _ HMI MU Hrel); [exact I | exact HD].
Qed.

End R16.

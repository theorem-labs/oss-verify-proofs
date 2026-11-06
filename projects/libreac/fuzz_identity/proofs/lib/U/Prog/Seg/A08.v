From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import reac_box_family_of_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma a08_evt : reac_box_family_of_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv lo : Z),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 0 -> stk rsegs m lo spv -> mem_inv rsegs m ->
    0 <= lo -> lo + 32 <= spv -> spv + 384 <= 2 ^ 64 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x12ff0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x12ff0) fc None m' (seg_rom rsegs) /\
         munch [(spv - 32, spv)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12fe4) fc None m (seg_rom rsegs)).
Proof.
  intros FO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo -> -> ST MI Hlo Hlo32 Hsp.
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply unsigned_lit; lia).
  step. if_true.
  step.
  eapply evt_cut.
  { eapply FO with (lo := lo) (idb := []);
      first [ rewrite Esp; exact ST | unfold REAC_BOX_FAMILY_OF_FRAME; rewrite Esp; lia | exact MI
            | left; reflexivity ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & _).
  subst ms'. rewrite Esp in MUc. unfold REAC_BOX_FAMILY_OF_FRAME in MUc.
  replace (ret_pc (Z_to_bv 64 77808)) with (Z_to_bv 64 77808) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MUc | exact WMc].
Qed.

Section A08.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis FAMOF : reac_box_family_of_contract.

Lemma seg_A08 : Hcut B APIf ra (Inv_U12ff0 B APIf ra empty) -> Hcut B APIf ra (Inv_U12fe4 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & (Hn & Hp) & HID & H10).
  destruct (sa_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sa_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK, SA_TOP, fsp, SLOT_FRAME in *.
  destruct (stk_split rsegs _ _ (g_S g - 384) _ ST ltac:(lia)) as [ST1 _].
  eapply (sa_mid B APIf ra empty FF g 0 [] L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sa_mkR_of.
    apply (a08_evt FAMOF) with (spv := g_S g - 384) (lo := g_S g - 65536);
      [exact Hsp | exact H10 | exact ST1 | exact (mem_inv_normalize rsegs mem) | lia | lia | lia].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 384 - 32, g_S g - 384)]. split; [exact MU|]. split; [exact WM|].
    intros y Hy O. apply (sa_fp1 g (g_S g - 384 - 32) (g_S g - 384) y);
      [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hy | exact O].
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; rewrite (sa_getr_eqv _ _ _ Hx); [exact Hn | exact Hp]|].
    split; [|rewrite (sa_getr_eqv _ _ _ Hx); reflexivity].
    apply (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel)).
    eapply bytes_at_transport; [exact (bytes_at_normalize rsegs mem _ _ HMI HID) | exact MU |].
    unfold IDb, spk, fsp, SLOT_FRAME. rewrite rec_id_length. cbn [disjoint_from].
    unfold RcIdentModel.ID_SIZE. split; [lia | exact I].
Qed.

End A08.

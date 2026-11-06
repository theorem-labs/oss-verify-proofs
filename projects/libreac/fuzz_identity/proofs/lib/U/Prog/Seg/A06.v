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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import reac_identity_reac_ver_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma a06_evt : reac_identity_reac_ver_str_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv lo : Z),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 (-1) -> stk rsegs m lo spv -> 0 <= lo -> lo + 64 <= spv ->
    spv + 384 <= 2 ^ 64 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x12fc4) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
                  F (Z_to_bv 64 0x12fc4) fc None m' (seg_rom rsegs) /\
         munch [(spv - 64, spv)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12fa4) fc None m (seg_rom rsegs)).
Proof.
  intros VS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo -> -> ST Hlo Hlo64 Hsp.
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply unsigned_lit; lia).
  step. if_true.
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply VS with (ma := 0) (mi := 0) (pa := 0) (o := 0) (c := 20) (lo := lo);
      first [ reflexivity | apply bv_eq; reflexivity | rewrite Esp; exact ST | rewrite Esp; lia | lia
            | intros C; exfalso; apply C; reflexivity ]. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & m' & E & WMc & _ & Hz).
  subst ms'. cbn [Z.eqb orb] in Hz. destruct Hz as [-> MUc]. rewrite Esp in MUc.
  replace (ret_pc (Z_to_bv 64 77764)) with (Z_to_bv 64 77764) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', m'.
  split; [reflexivity|]. split; [exact MUc | exact WMc].
Qed.

Section A06.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis VERSTR : reac_identity_reac_ver_str_contract.

Lemma seg_A06 : Hcut B APIf ra (Inv_U12fc4 B APIf ra empty) -> Hcut B APIf ra (Inv_U12fa4 B APIf ra empty).
Proof.
  intros H g c (L & A & regs & mem & md & -> & HFR & HP & (Hn & Hp) & HID & H10).
  destruct (sa_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sa_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK, SA_TOP, fsp, SLOT_FRAME in *.
  destruct (stk_split rsegs _ _ (g_S g - 384) _ ST ltac:(lia)) as [ST1 _].
  eapply (sa_mid B APIf ra empty FF g 0 [] L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sa_mkR_of.
    apply (a06_evt VERSTR) with (spv := g_S g - 384) (lo := g_S g - 65536);
      [exact Hsp | exact H10 | exact ST1 | lia | lia | lia].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 384 - 64, g_S g - 384)]. split; [exact MU|]. split; [exact WM|].
    intros y Hy O. apply (sa_fp1 g (g_S g - 384 - 64) (g_S g - 384) y); [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hy | exact O].
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; rewrite (sa_getr_eqv _ _ _ Hx); [exact Hn | exact Hp]|].
    split; [|rewrite (sa_getr_eqv _ _ _ Hx); reflexivity].
    apply (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel)).
    eapply bytes_at_transport; [exact (bytes_at_normalize rsegs mem _ _ HMI HID) | exact MU |].
    unfold IDb, spk, fsp, SLOT_FRAME. rewrite rec_id_length. cbn [disjoint_from]. unfold RcIdentModel.ID_SIZE. split; [lia | exact I].
Qed.

End A06.

(* Segment G03 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13a94, 0x13aac], U13a94 -> U13ab4
   (sum_ok (s11; v1.8 s10); s10 = rf (v1.8 s9)), U13ab0 (not sum_ok: bcmp (0x1e1fc) (before = sp+192, frag = sp+120
   (v1.8 sp+82), 72) = 0, as not FR(Φ, len) keeps the frag: FGf = FG_j). #57's first half (rf = -1) is not taken:
   rf is 0 or 1. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv bcmp_c bcmp_ro_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u4 Tac_u5.
Import ListNotations.
Open Scope Z_scope.

(* 0x13aa0-0x13aac (not sum_ok): bcmp(before = sp+192, frag = sp+120, 72) of equal bytes returns 0. *)
Lemma g03_call : bcmp_ro_contract ->
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (st : list byte),
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> length st = 72%nat ->
    bytes_at rsegs m (spv + 192) st -> bytes_at rsegs m (spv + 120) st -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13ab0) (Z_to_bv 64 spv) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13ab0) fc None m' (seg_rom rsegs) /\
         munch [] m m' /\ wmono rsegs m m')
      (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13aa0) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv st Hlo Hhi Lst H192 H120 MI.
  step. step. step. step.
  eapply evt_cut.
  { eapply BC with (ls := st) (rs := st) (v := 0).
    all: u5_ul.
    all: first [ exact H192 | exact H120 | exact MI | apply u5_mcmp_refl; rewrite Lst; lia ]. }
  intros ms' PO. unfold memcmp_post_ro in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13ab0)) with (Z_to_bv 64 0x13ab0)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MU | exact WM].
Qed.

Lemma g03_evt : bcmp_ro_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv rf sok : Z) (st : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 rf -> s11 = Z_to_bv 64 sok ->
    (rf = 0 \/ rf = 1) -> (sok = 0 \/ sok = 1) -> 0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    (sok = 0 -> length st = 72%nat /\ bytes_at rsegs m (spv + 192) st /\ bytes_at rsegs m (spv + 120) st) ->
    MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' =>
         (sok = 1 /\
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 rf) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13ab4) fc None m (seg_rom rsegs)) \/
         (sok = 0 /\ exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                            (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x13ab0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                          a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 rf) s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x13ab0) fc None m' (seg_rom rsegs) /\
            munch [] m m' /\ wmono rsegs m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13a94) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv rf sok st Hsp Ha0 Hs11 Hrf Hsok Hlo Hhi Hst MI.
  subst sp a0 s11.
  destruct Hsok as [-> | ->].
  - destruct (Hst eq_refl) as (Lst & H192 & H120).
    destruct Hrf as [-> | ->].
    + step. u5_br false. step. step. u5_br false.
      eapply evt_cut.
      { apply (g03_call BC) with (st := st); [lia | lia | exact Lst | exact H192 | exact H120 | exact MI]. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  -> & MU & WM).
      apply evt_done. right. split; [reflexivity|].
      exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [exact MU | exact WM].
    + step. u5_br false. step. step. u5_br false.
      eapply evt_cut.
      { apply (g03_call BC) with (st := st); [lia | lia | exact Lst | exact H192 | exact H120 | exact MI]. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  -> & MU & WM).
      apply evt_done. right. split; [reflexivity|].
      exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [exact MU | exact WM].
  - destruct Hrf as [-> | ->];
      step; u5_br false; step; step; u5_br true;
      apply evt_done; left; split; reflexivity.
Qed.

Section G03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BC : bcmp_ro_contract.

Lemma seg_G03 : forall j : nat, Hat B APIf ra (Inv_U13ab0_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13ab4_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13a94_at B APIf ra empty) j.
Proof.
  intros j H0 H4 g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGF & H10).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof HGF as (HFB & HI & HG & HS & H192 & _).
  pose proof HFB as (_ & (_ & _ & H27 & _)).
  pose proof (u5_rf01 (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j)) as Hrf.
  unfold FGb, FGB in HG.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME, spk in *.
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ []);
    [exact HFR | exact HP | intros x Hx O; exfalso; apply O; exact I | | |].
  - rewrite sl_mkR_of.
    apply (g03_evt BC) with (spv := g_S g - 1936) (rf := t_rf (g_in g) j) (sok := b2z (t_sum_ok (g_in g) j))
      (st := t_FG (g_in g) j);
      [exact Hsp | exact H10 | exact H27 | exact Hrf
      | unfold b2z; destruct (t_sum_ok _ _); [right | left]; reflexivity | lia | lia | | apply u5_ro_norm].
    intros Hs0.
    assert (Hsf : t_sum_ok (g_in g) j = false).
    { unfold b2z in Hs0. destruct (t_sum_ok _ _); [discriminate | reflexivity]. }
    split; [apply u4_tFG_len|]. split.
    + exact (u5_norm mem _ _ HMI H192).
    + rewrite <- (u5_nosum _ _ Hsf). exact (u5_norm mem _ _ HMI (proj1 HG)).
  - intros ms [(? & ->) | (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM)].
    + do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
    + do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    assert (HGF' : GF g j phi regs m').
    { apply (u5_GF_keep g j phi regs regs mem m' _ HGF (u5_SKP_refl regs) MU'); u4_dj. }
    destruct HQ as [(Hs1 & HE) | (Hs0 & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _)];
      injection HE; intros; subst;
      (assert (K10 : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity)).
    + apply H4. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [exact (u5_GF_regs g j phi regs regs' m' HGF' K10)|].
      unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + apply H0. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [exact (u5_GF_regs g j phi regs regs' m' HGF' K10)|].
      split; [unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
      split; [unfold b2z in Hs0; destruct (t_sum_ok _ _); [discriminate | reflexivity]|].
      unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End G03.

(* Segment R07 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13374, 0x13384], K13374 -> K13388
   (fuzz_dup's null test #6, then memcpy(Φ, out = sp+192, n_b)). libreac v1.9.0: out sp+176 -> sp+192,
   frame 1936. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

Lemma r07_evt : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi n : Z) (src junk : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 phi -> s6 = Z_to_bv 64 n ->
    0 < phi -> phi + n <= spv -> spv + 1936 <= 2 ^ 64 -> 0 <= n ->
    bytes_at rsegs m (spv + 192) src -> length src = Z.to_nat n ->
    rw_cells rsegs m phi [Cells.CB (Z.to_nat n) junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13388) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 phi) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 (Z_to_bv 64 phi) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13388) fc None m' (seg_rom rsegs) /\
         munch [(phi, phi + n)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' phi src)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13374) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi n src junk -> -> -> Hph0 Hph Hsp Hn HB HL HC MI.
  step. if_false_by (b1_beq0 phi ltac:(lia)).
  step. step. step. step.
  eapply evt_cut.
  { eapply MCPY with (src := src) (junk := junk); rewrite ?MState.unsigned_lit by lia.
    - exact HB.
    - exact HL.
    - exact HC.
    - lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & HZ & _).
  subst ms'. rewrite !MState.unsigned_lit in MUc, HZ by lia.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MUc|]. split; [exact WMc|]. exact (sl_rw_bytes _ _ _ _ HZ).
Qed.

Section R07.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MCPY : memcpy_contract.

Lemma seg_R07 : forall b, Hat B APIf ra (Inv_K13388_at B APIf ra empty) b ->
  Hat B APIf ra (Inv_K13374_at B APIf ra empty) b.
Proof.
  intros b H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HRS & Hnz & H22 & H10 & Hphi0 & HO)).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  destruct (b1_hb B APIf ra empty FF g phi (rnb g b) L A regs mem md HFR HP) as (STb & Hphi & Hphin).
  unfold rnb, rFb in *.
  set (N := rt_n (g_in g) (Z.of_nat b)) in *.
  destruct (b1_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & HL).
  fold N in Hnb, HL.
  destruct (b1_RS_len (g_in g) b) as (LI & LF).
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ phi (Z.to_nat N) STb ltac:(lia) ltac:(lia)) as (junk & HC).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run regs (Z_to_bv 64 0x13374) mem md _ _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    apply (r07_evt MCPY) with (spv := g_S g - 1936) (phi := phi) (n := N) (src := rt_F (g_in g) (Z.of_nat b))
      (junk := junk); [exact Hsp | exact H10 | exact H22 | lia | lia | lia | lia | | exact HL | exact HC
      | exact (mem_inv_normalize rsegs mem)].
    exact (bytes_at_normalize rsegs mem _ _ HMI HO).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & _). do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & WM & HZ).
    injection HE; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    assert (MU' : Frame.munch [(phi, phi + N)] mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m'' HR0 Hrel Hsame MU).
    assert (WM' : Frame.wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m'' HR0 Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' HMI Hsame).
    pose proof (b1_out _ _ _ _ Hrel HZ) as HZ'.
    rewrite <- SEGS. apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split.
    { apply (b1_fr_hb B APIf ra empty FF g phi N L A regs mem md regs' m' HFR HP).
      - intros a Ha _ Hn. apply MU'. rewrite MState.unsigned_lit by lia. cbn [outside]. split; [exact Hn | exact I].
      - intros a Ha. destruct HZ' as (_ & _ & H3).
        assert (Hk : (Z.to_nat (a - phi) < length (rt_F (g_in g) (Z.of_nat b)))%nat) by lia.
        destruct (nth_error (rt_F (g_in g) (Z.of_nat b)) (Z.to_nat (a - phi))) as [bb|] eqn:En;
          [|apply nth_error_None in En; lia].
        exists bb. rewrite <- En, <- (H3 _ Hk). f_equal. unfold wa. f_equal. lia.
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    split; [exact HP|].
    assert (KR : b1_kr regs' regs).
    { unfold b1_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
    unfold RF, RFx, RFb, rnb, rFb, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
    split; [split; [|split; [exact Hnz | split; [reflexivity | exact HZ']]] | exact H22].
    apply (b1_RB_keep g b _ _ regs regs' mem m'' m' _ HMI MU Hrel LI LF); [|exact KR | exact HRS].
    cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
Qed.

End R07.

(* Segment R08 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13464, 0x13470], U13464 -> U13474
   (turn b) (reac_ctrl_parse(Φ, n_b, &p = sp+76)). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u1.
Import ListNotations.
Open Scope Z_scope.

Lemma r08_evt : reac_ctrl_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi n : Z) (fr junk : list byte),
    sp = Z_to_bv 64 spv -> s4 = Z_to_bv 64 phi -> s5 = Z_to_bv 64 n ->
    65536 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    0 < phi -> phi + 50 <= spv - 80 -> 50 <= n < 2 ^ 64 ->
    stk rsegs m (spv - 80) spv -> mem_inv rsegs m -> length fr = 50%nat ->
    (forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (phi + Z.of_nat i)) = nth_error fr i) ->
    rw_cells rsegs m (spv + 76) [Cells.CB 36 junk] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13474) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13474) fc None m' (seg_rom rsegs) /\
         munch [(spv + 76, spv + 112); (spv - 80, spv)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 76) (snd (ctrlparse n fr)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13464) fc None m (seg_rom rsegs)).
Proof.
  intros PARSE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi n fr junk -> -> -> Hsp0 Hsp H16 Hph0 Hph Hn Hst MI Hlen Hrd HC.
  step. step. step. step.
  eapply evt_cut.
  { eapply PARSE with (f := phi) (n := n) (o := spv + 76) (S := spv) (fr := fr) (junk := junk).
    all: try unfold REAC_CTRL_PARSE_K.
    all: first [ reflexivity | lia | exact Hst | exact MI | exact Hlen | exact Hrd
               | intros _; split; [lia|]; split; [lia|]; split; [exact HC|]; split; [lia | intros _; lia] ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & _ & HZ).
  subst ms'.
  unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc.
  rewrite (proj2 (Z.eqb_neq (spv + 76) 0) ltac:(lia)) in MUc. cbn [app] in MUc.
  replace (spv + 76 + 36) with (spv + 112) in MUc by lia.
  specialize (HZ ltac:(lia)).
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MUc|]. split; [exact WMc|]. exact (sl_rw_bytes _ _ _ _ HZ).
Qed.

Section R08.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PARSE : reac_ctrl_parse_contract.

Lemma seg_R08 : forall b, Hat B APIf ra (Inv_U13474_at B APIf ra empty) b ->
  Hat B APIf ra (Inv_U13464_at B APIf ra empty) b.
Proof.
  intros b H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF).
  pose proof HRF as ((HRB & Hnz & H20 & HF) & H21).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (u1_hb B APIf ra empty FF g phi (rnb g b) L A regs mem md HFR HP) as (_ & Hphi & Hphin).
  unfold rnb, rFb, rgb in *.
  destruct (u1_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & HL).
  destruct (u1_RS_len (g_in g) b) as (LI & LF).
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 76) 36 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  assert (ST80 : stk rsegs (normalize rsegs mem) (g_S g - 1936 - 80) (g_S g - 1936)).
  { destruct ST as (S1 & S2 & S3). split; [lia|]. split; [lia|]. intros a Ha. apply S3. lia. }
  pose proof (bytes_at_normalize rsegs mem phi _ HMI HF) as (_ & _ & HF3).
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (r08_evt PARSE) with (spv := g_S g - 1936) (phi := phi) (n := rt_n (g_in g) (Z.of_nat b))
      (fr := rt_g (g_in g) (Z.of_nat b)) (junk := junk);
      [exact Hsp | exact H20 | exact H21 | lia | lia | lia | lia | lia | lia | exact ST80
      | exact (mem_inv_normalize rsegs mem) | apply fr50_length | | exact HC].
    intros i Hi. pose proof (cp_rd_lt39 _ _ _ Hi) as Hi39.
    rewrite (HF3 i ltac:(lia)). symmetry. unfold rt_g. apply u1_fr50_nth; lia.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 1936 + 76, g_S g - 1936 + 112); (g_S g - 1936 - 80, g_S g - 1936)].
    split; [exact MU|]. split; [exact WM|].
    intros z Hz O. cbn [outside] in O. unfold SLOT_K, SLOT_STACK. lia.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HZ).
    injection HE; intros; subst.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (KR : u1_kr regs' regs).
    { unfold u1_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
    unfold RF, RFx, RFb, rnb, rFb, rg in *. rewrite !(sl_getr_eqv _ _ _ Hx).
    split; [split; [split|]|].
    + apply (u1_RB_keep g b _ _ regs regs' mem m'' m' _ HMI MU Hrel LI LF); [|exact KR | exact HRB].
      cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
    + split; [exact Hnz|]. split; [exact H20|].
      apply (u1_keep _ mem m'' m' _ _ HMI MU Hrel); [|exact HF].
      rewrite HL. cbn [disjoint_from]. lia.
    + exact H21.
    + split; [reflexivity|]. exact (u1_out _ _ _ _ Hrel HZ).
Qed.

End R08.

(* Segment Q01 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13b64, 0x13b7c], K13b64 -> K13b80 (call
   reac_ports_parse at 0x13b7c). Branch #74 (HRV C1.2, C1.3: a0 = want_v = s0) is not taken; M7 and s2 = -7 store
   ports = (-7, -7, -7) at sp+1688, which reac_ports_parse overwrites exactly when decl(blk) (PP C1.2, C1.3). *)
(* libreac v1.9.0 (IDENTICAL-RENUMBER, segment table 5a S_Q01): v1.8 [0x13b34, 0x13b4c] K13b34 -> K13b50; the
   ports slots sp+1672 / 1676 / 1680 -> sp+1688 / 1692 / 1696, the frame 1920 -> 1936; VC -> VCm in EQ (SlotInv.v).
   Statement kept on the renamed cuts. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b7.
Import ListNotations.
Open Scope Z_scope.

(* The 12 bytes M7 ++ le4 (-7) are three s32 -7. *)
Lemma q01_m7 : forall m a, bytes_at rsegs m a (le8 (Z_to_bv 64 0xfffffff9fffffff9) ++ le4 (Z_to_bv 64 (-7))) ->
  u32 m a (-7) /\ u32 m (a + 4) (-7) /\ u32 m (a + 8) (-7).
Proof.
  intros m a H.
  assert (E : le8 (Z_to_bv 64 0xfffffff9fffffff9) = le4 (Z_to_bv 64 (-7)) ++ le4 (Z_to_bv 64 (-7))).
  { apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [vm_compute; reflexivity|].
    intros i Hi. vm_compute in Hi.
    do 8 (destruct i as [|i]; [apply bv_eq; vm_compute; reflexivity|]). lia. }
  rewrite E, <- app_assoc in H.
  apply (proj1 (bytes_at_app rsegs m _ _ _)) in H as [H0 H]. rewrite length_le4 in H.
  apply (proj1 (bytes_at_app rsegs m _ _ _)) in H as [H4 H8]. rewrite length_le4 in H8.
  unfold u32. split; [exact H0|]. split.
  - replace (a + 4) with (a + Z.of_nat 4) by lia. exact H4.
  - replace (a + 8) with (a + Z.of_nat 4 + Z.of_nat 4) by lia. exact H8.
Qed.

(* 0x13b64 -> 0x13b80 with sp = spv, s0 = a0 = want_v, s2 = -7, s6 = blk = Φ + 18, bs = blk's 20 bytes. *)
Lemma q01_evt : reac_ports_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi wv : Z) (bs junk : list byte),
    sp = Z_to_bv 64 spv -> s0 = Z_to_bv 64 wv -> a0 = Z_to_bv 64 wv -> s2 = Z_to_bv 64 (-7) ->
    s6 = Z_to_bv 64 (phi + 18) ->
    0 <= spv -> spv + 1936 < 2 ^ 64 -> spv mod 16 = 0 -> 0 < phi -> phi + 50 <= spv ->
    q64 m (spv + 8) 0xfffffff9fffffff9 ->
    Step.rw_cells rsegs m (spv + 1688) [Cells.CB 12 junk] ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    evt rsegs
      (fun ms' => exists (ra' t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if RcLeaf.decl bs then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13b80) fc None m' (seg_rom rsegs) /\
         munch [(spv + 1688, spv + 1700)] m m' /\ wmono rsegs m m' /\
         (RcLeaf.decl bs = true ->
            u32 m' (spv + 1688) (4 * RcLeaf.n_in bs) /\ u32 m' (spv + 1692) (4 * RcLeaf.n_out bs) /\
            u32 m' (spv + 1696) (16 * RcLeaf.bt bs 7)) /\
         (RcLeaf.decl bs = false -> u32 m' (spv + 1688) (-7) /\ u32 m' (spv + 1692) (-7) /\ u32 m' (spv + 1696) (-7)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b64) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi wv bs junk -> -> -> -> -> Hs0 Hs1 H16 Hp1 Hp2 HM7 HC Hl HB.
  pose proof (b7_rdn m _ _ HM7) as R8. rewrite length_le8 in R8.
  pose proof (munch_refl [(spv + 1688, spv + 1700)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. b7_br false ltac:(rewrite bv_eqb_refl; reflexivity).
  step. step. step. step. step. step.
  pose proof (sl_cells_bytes _ _ _ HC) as HCB. cbn [Cells.cells_bytes Cells.cbytes] in HCB.
  rewrite app_nil_r in HCB.
  destruct HC as [_ HW]. cbn [Cells.cells_size Cells.csize Nat.add] in HW.
  eapply evt_cut.
  { eapply PP with (p := phi + 18) (q := spv + 1688) (bs := bs).
    - first [reflexivity | f_equal; lia].
    - first [reflexivity | f_equal; lia].
    - lia.
    - lia.
    - intros _ _. split; [exact Hl | exact HB].
    - intros _ _. split; [lia | split; [exact HW | lia]]. }
  intros ms' (t0' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & Hpost).
  rewrite (MState.ret_pc_even 0x13b80) by (first [reflexivity | lia]).
  assert (Eok : RcLeaf.ports_ok (phi + 18) (spv + 1688) bs = RcLeaf.decl bs).
  { unfold RcLeaf.ports_ok. replace (phi + 18 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (spv + 1688 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  rewrite Eok in Hpost |- *.
  apply evt_done.
  revert Hpost. destruct (RcLeaf.decl bs) eqn:Ed; intros Hpost.
  - destruct Hpost as (Q0 & Q4 & Q8 & MUc & WMc & _).
    eexists _, _, _, _, _, _, _, _, _, m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUc]]|].
    { unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
    split; [exact (wmono_trans _ _ _ _ WM WMc)|].
    split; [|intros E; discriminate E].
    intros _. unfold u32. split; [exact Q0|]. split.
    + replace (spv + 1692) with (spv + 1688 + 4) by lia. exact Q4.
    + replace (spv + 1696) with (spv + 1688 + 8) by lia. exact Q8.
  - subst m'.
    eexists _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [intros E; discriminate E|].
    intros _. destruct (q01_m7 _ _ HCB) as (Q0 & Q4 & Q8).
    split; [exact Q0|]. split.
    + replace (spv + 1692) with (spv + 1688 + 4) by lia. exact Q4.
    + replace (spv + 1696) with (spv + 1688 + 8) by lia. exact Q8.
Qed.

Section Q01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PP : reac_ports_parse_contract.

Lemma seg_Q01 : forall j, Hat B APIf ra (Inv_K13b80_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13b64_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HEQ & H9 & H8 & H10)).
  pose proof HEQ as (HFT & H7 & H2 & HVC & HIFS & H88).
  pose proof HFT as (Hj & H26 & HFC & H21 & Hphi & HOUR & HM7).
  pose proof HVC as (H22 & H24 & HB).
  pose proof (b7_big_8819 _ _ H88) as Hbig.
  destruct (b7_phi_bnd B APIf ra empty g _ L A regs mem md phi _ HFR HP ltac:(lia)) as (Hp1 & Hp2).
  destruct (b7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  pose proof alloc_ceiling_value as Hac.
  assert (H22' : rg regs 22 (phi + 18)).
  { unfold t_big in H22. rewrite (proj2 (Z.leb_le _ _) Hbig) in H22. exact H22. }
  pose proof (sl_fr_stk B APIf ra empty FF g _ L A regs mem md HFR) as ST.
  unfold SLOT_K, SLOT_STACK, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1688) 12 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (q01_evt PP) with (spv := g_S g - 1936) (phi := phi) (wv := t_want_v (g_in g) j)
      (bs := t_pbs (g_in g) j) (junk := junk).
    + exact Hsp.
    + exact H8.
    + exact H10.
    + exact H2.
    + exact H22'.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + apply b7_norm; [exact HMI|]. exact HM7.
    + exact HC.
    + apply b7_pbs_length.
    + apply b7_pbs_bytes. apply b7_norm; [exact HMI|]. apply b7_g_bytes; [exact Hphi | exact Hbig].
  - intros ms (ra' & t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 1936 + 1688, g_S g - 1936 + 1700)]. split; [exact MU|]. split; [exact WM|].
    intros x Hx O. apply (sl_fp1 g (g_S g - 1936 + 1688) (g_S g - 1936 + 1700) x);
      [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hx | exact O].
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (ra' & t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m'' & HE & MU & WM & Hok & Hno).
    injection HE; intros; subst.
    apply H. unfold Inv_K13b80_at, FCUT, CUTST. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    set (W := [(g_S g - 1936 + 1688, g_S g - 1936 + 1700)]) in *.
    assert (MTW : MT W mem m') by exact (b7_mt W mem _ m' HMI MU Hrel).
    split; [|split].
    + apply (b7_EQ g j phi regs mem regs' m' W); [exact HEQ | exact MTW | |].
      * intros a n Hn Ha. unfold W. cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME in Ha. split; [lia | exact I].
      * unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold PORTS, t_rp, spk, fsp, SLOT_FRAME.
      destruct (RcLeaf.decl (t_pbs (g_in g) j)) eqn:Ed; split; intros E; try lia.
      * destruct (Hok eq_refl) as (Q0 & Q4 & Q8).
        split; [exact (b7_back _ _ _ _ Hrel Q0)|].
        split; [exact (b7_back _ _ _ _ Hrel Q4) | exact (b7_back _ _ _ _ Hrel Q8)].
      * destruct (Hno eq_refl) as (Q0 & Q4 & Q8).
        split; [exact (b7_back _ _ _ _ Hrel Q0)|].
        split; [exact (b7_back _ _ _ _ Hrel Q4) | exact (b7_back _ _ _ _ Hrel Q8)].
Qed.

End Q01.

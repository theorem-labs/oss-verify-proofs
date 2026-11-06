(* Segment Q01 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13da0, 0x13dbc], U13dac (v1.9 pc
   0x13da0) -> U13dcc (v1.9 pc 0x13dc0). Branch #74 (a0 = s3 = want_v) is not taken; ports = {-7, -7, -7} (the -7
   pair of M7 at sp+8 and `li -7`) at sp+1688, then reac_ports_parse(blk, sp+1688) with blk = s8 (C24 C1.2, C1.3):
   a0 = r_p, the slots are the ports when r_p = 0. v1.8: want_v s1, M7 sp+16, blk s7. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u7.
Import ListNotations.
Open Scope Z_scope.

Lemma q01_m7 : le8 (Z_to_bv 64 0xfffffff9fffffff9) = le4 (Z_to_bv 64 (-7)) ++ le4 (Z_to_bv 64 (-7)).
Proof. vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. Qed.

(* The 12 bytes at a after `sd M7; sw -7`: three ints -7. *)
Lemma q01_split : forall m a X Y, bytes_at rsegs m a (le8 X ++ le4 Y) ->
  X = Z_to_bv 64 0xfffffff9fffffff9 -> Y = Z_to_bv 64 (-7) ->
  u32 m a (-7) /\ u32 m (a + 4) (-7) /\ u32 m (a + 8) (-7).
Proof.
  intros m a X Y H -> ->. rewrite q01_m7, <- app_assoc in H.
  apply (proj1 (bytes_at_app rsegs m a _ _)) in H as [H1 H2].
  apply (proj1 (bytes_at_app rsegs m _ _ _)) in H2 as [H2 H3].
  rewrite length_le4 in H2, H3.
  replace (a + Z.of_nat 4) with (a + 4) in H2, H3 by lia.
  replace (a + 4 + Z.of_nat 4) with (a + 8) in H3 by lia.
  unfold u32. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* 0x13da0 -> 0x13dc0: bne a0,s3; ld a0,8(sp); sd a0,1688(sp); li a0,-7; sw a0,1696(sp); addi a1,sp,1688;
   mv a0,s8; jal reac_ports_parse. *)
Lemma q01_evt : reac_ports_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv blk wv : Z) (bs jk : list byte),
    sp = Z_to_bv 64 spv -> s8 = Z_to_bv 64 blk -> a0 = Z_to_bv 64 wv -> s3 = Z_to_bv 64 wv ->
    0 < blk -> blk + 20 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    length bs = 20%nat -> bytes_at rsegs m blk bs ->
    ov_read_bytes rsegs m (Z_to_bv 64 (spv + 8)) 8 = Some (le8 (Z_to_bv 64 0xfffffff9fffffff9)) ->
    rw_cells rsegs m (spv + 1688) [Cells.CB 12 jk] ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13dc0) fc None m' (seg_rom rsegs) /\
         a0' = Z_to_bv 64 (if RcLeaf.decl bs then 0 else -1) /\
         munch [(spv + 1688, spv + 1700)] m m' /\ wmono rsegs m m' /\
         (RcLeaf.decl bs = true ->
            u32 m' (spv + 1688) (4 * RcLeaf.n_in bs) /\ u32 m' (spv + 1692) (4 * RcLeaf.n_out bs) /\
            u32 m' (spv + 1696) (16 * RcLeaf.bt bs 7)) /\
         (RcLeaf.decl bs = false ->
            u32 m' (spv + 1688) (-7) /\ u32 m' (spv + 1692) (-7) /\ u32 m' (spv + 1696) (-7)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13da0) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv blk wv bs jk -> -> -> -> Hb0 Hbs Hsp H16 Hl HB HM7 HC.
  pose proof (proj2 HC) as HW. change (Z.of_nat (Cells.cells_size [Cells.CB 12 jk])) with 12 in HW.
  pose proof (munch_refl [(spv + 1688, spv + 1700)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. u7_br false ltac:(u7_bool).
  step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply PP with (p := blk) (q := spv + 1688) (bs := bs).
    - u7_weq.
    - u7_weq.
    - lia.
    - lia.
    - intros _ _. split; [exact Hl | exact HB].
    - intros _ _. split; [Z.div_mod_to_equations; lia|]. split; [exact HW | lia]. }
  intros ms' (t0' & t1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & HPOST).
  rewrite (MState.ret_pc_even 0x13dc0) by (first [reflexivity | lia]).
  unfold RcLeaf.ports_ok in HPOST |- *.
  replace (blk =? 0) with false in HPOST |- * by (symmetry; apply Z.eqb_neq; lia).
  replace (spv + 1688 =? 0) with false in HPOST |- * by (symmetry; apply Z.eqb_neq; lia).
  cbn [negb andb] in HPOST |- *.
  pose proof (sl_cells_bytes _ _ _ HC) as HCB. cbn [Cells.cells_bytes Cells.cbytes] in HCB.
  rewrite ?app_nil_r in HCB.
  apply evt_done. do 12 eexists. split; [reflexivity|]. split; [reflexivity|].
  destruct (RcLeaf.decl bs) eqn:Ed.
  - destruct HPOST as (P0 & P1 & P2 & MUc & WMc & _).
    split.
    { apply (u7_munch_join _ _ _ _ _ MU MUc). intros x Hx. cbn [Frame.outside] in *. destruct Hx as [Hx _].
      split; [lia | exact I]. }
    split; [exact (wmono_trans rsegs _ _ _ WM WMc)|].
    split; [intros _ | intros E; discriminate E].
    replace (spv + 1688 + 4) with (spv + 1692) in P1 by lia.
    replace (spv + 1688 + 8) with (spv + 1696) in P2 by lia.
    split; [exact P0|]. split; [exact P1 | exact P2].
  - subst m'.
    split; [exact MU|]. split; [exact WM|].
    split; [intros E; discriminate E | intros _].
    destruct (q01_split _ _ _ _ HCB ltac:(u7_weq) ltac:(u7_weq)) as (U0 & U1 & U2).
    replace (spv + 1688 + 4) with (spv + 1692) in U1 by lia.
    replace (spv + 1688 + 8) with (spv + 1696) in U2 by lia.
    split; [exact U0|]. split; [exact U1 | exact U2].
Qed.

Section Q01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PP : reac_ports_parse_contract.

Lemma seg_Q01 : forall j, Hat B APIf ra (Inv_U13dc0_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13da0_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HEQ & H19 & H10)).
  pose proof HEQ as (HFT & H7 & H2 & HVC & HIFS & H88).
  pose proof HFT as ((Hj & H9 & HOUR & HM7 & HOVF & HS2) & HFC & H23 & Hphi & H18).
  pose proof HVC as (H24 & H16 & HB).
  pose proof (u7_big_8819 _ _ H88) as Hbig.
  rewrite (u7_big_true _ _ H88) in H24.
  destruct (u7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HSa & HSb & HSc & Hsp & HMI).
  destruct (u7_phi_bnd B APIf ra empty g _ L A regs mem md phi _ HFR HP ltac:(lia)) as (Hp1 & Hp2).
  pose proof alloc_ceiling_value as Hac.
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  unfold SLOT_K, SLOT_STACK in ST.
  destruct (sl_rw_of_stk _ _ _ (fsp g + 1688) 12 ST ltac:(unfold fsp, SLOT_FRAME; lia)
              ltac:(unfold fsp, SLOT_FRAME; lia)) as (jk & HC).
  eapply (u7_mid B APIf ra empty FF g _ L A regs mem md _ [(fsp g + 1688, fsp g + 1700)]);
    [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (u7_fp g _ x _ Hx O).
    repeat (apply Forall_cons; [cbn [fst snd]; unfold SLOT_K, SLOT_STACK, fsp, SLOT_FRAME; lia|]). apply Forall_nil.
  - rewrite sl_mkR_of.
    apply (q01_evt PP) with (spv := fsp g) (blk := phi + 18) (wv := t_want_v (g_in g) j) (bs := t_pbs (g_in g) j)
      (jk := jk).
    + exact Hsp.
    + exact H24.
    + exact H10.
    + exact H19.
    + lia.
    + unfold fsp, SLOT_FRAME. lia.
    + unfold fsp, SLOT_FRAME. lia.
    + unfold fsp, SLOT_FRAME. Z.div_mod_to_equations. lia.
    + apply u7_pbs_length.
    + apply u7_norm; [exact HMI|]. apply u7_pbs_bytes. apply u7_g_bytes; [exact Hphi | exact Hbig].
    + pose proof (u7_rdn _ _ _ (u7_norm mem _ _ HMI HM7)) as R. rewrite length_le8 in R. exact R.
    + exact HC.
  - intros ms (ra' & t0' & t1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & _ & MU & WM & _ & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (ra' & t0' & t1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m'' & HE & E10 & _ & _ & HT & HF).
    destruct (u7_MS_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE) as (ER & Epc & Em). subst R pc' m0'.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (DJ : DJE g j phi [(fsp g + 1688, fsp g + 1700)]).
    { intros a n Hn Ha. cbn [disjoint_from]. split; [|exact I]. unfold spk, fsp, SLOT_FRAME in *. lia. }
    split; [|split].
    + apply (u7_EQ g j phi regs mem regs' m' _ HEQ (u7_mt _ _ _ MU') DJ).
      unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). transitivity a0'; [reflexivity|]. rewrite E10. unfold t_rp.
      reflexivity.
    + unfold PORTS. split.
      * intros E. unfold t_rp in E. destruct (RcLeaf.decl (t_pbs (g_in g) j)) eqn:Ed; [|discriminate E].
        destruct (HT eq_refl) as (U0 & U1 & U2).
        split; [exact (u7_back _ _ _ _ Hrel U0)|].
        split; [exact (u7_back _ _ _ _ Hrel U1) | exact (u7_back _ _ _ _ Hrel U2)].
      * intros E. unfold t_rp in E. destruct (RcLeaf.decl (t_pbs (g_in g) j)) eqn:Ed; [exfalso; exact (E eq_refl)|].
        destruct (HF eq_refl) as (U0 & U1 & U2).
        split; [exact (u7_back _ _ _ _ Hrel U0)|].
        split; [exact (u7_back _ _ _ _ Hrel U1) | exact (u7_back _ _ _ _ Hrel U2)].
Qed.

End Q01.

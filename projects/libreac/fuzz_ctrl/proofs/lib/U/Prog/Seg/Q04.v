(* Segment Q04 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x13df4, 0x13e30], U13df4 -> U13e34 (r_p = 0) or U13fa4
   (r_p != 0). t2 = 12 (T2); #75 (a0 = s9 = unk), #76 (r_p = 0 exactly when unk >= 0, C5.3) and, when r_p != 0, #77-#79
   (the three slots hold -7) are not taken. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u7.
Import ListNotations.
Open Scope Z_scope.

(* 0x13de8 -> 0x13e28 / 0x13f98 (v1.8 0x13df4 -> 0x13e34 / 0x13fa4); unk is s10, r_p is s11 (v1.8 s9, s10). *)
Lemma q04_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv rp unk : Z),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 unk -> s10 = Z_to_bv 64 unk -> s11 = Z_to_bv 64 rp ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    (rp = 0 \/ rp = -1) -> (rp = 0 <-> 0 <= unk) -> (unk = -1 \/ 0 <= unk <= 48) ->
    (rp <> 0 -> ov_read_bytes rsegs m (Z_to_bv 64 (spv + 1688)) 4 = Some (le4 (Z_to_bv 64 (-7))) /\
                ov_read_bytes rsegs m (Z_to_bv 64 (spv + 1692)) 4 = Some (le4 (Z_to_bv 64 (-7))) /\
                ov_read_bytes rsegs m (Z_to_bv 64 (spv + 1696)) 4 = Some (le4 (Z_to_bv 64 (-7)))) ->
    evt rsegs
      (fun ms' => exists (a0' a1' t2' : word),
         (rp = 0 /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2' s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                        t3 t4 t5 t6) F (Z_to_bv 64 0x13e28) fc None m (seg_rom rsegs) /\
          t2' = Z_to_bv 64 12) \/
         (rp <> 0 /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2' s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                        t3 t4 t5 t6) F (Z_to_bv 64 0x13f98) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13de8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv rp unk -> -> -> -> Hs0 Hs1 Hrp Hiff Hunk HL.
  step. step. u7_br false ltac:(u7_bool).
  step. step. step.
  destruct Hrp as [Erp | Erp]; subst rp.
  - assert (Hu : 0 <= unk <= 48) by (destruct Hunk; lia).
    u7_br false ltac:(u7_bool).
    step. u7_br true ltac:(u7_bool).
    apply evt_done. do 3 eexists. left. split; [reflexivity|]. split; [reflexivity|]. u7_weq.
  - assert (Hu : unk = -1).
    { destruct Hunk as [Hu|Hu]; [exact Hu|]. exfalso. assert (E : -1 = 0) by (apply Hiff; lia). lia. }
    subst unk.
    destruct (HL ltac:(lia)) as (R0 & R1 & R2).
    u7_br false ltac:(u7_bool).
    step. u7_br false ltac:(u7_bool).
    step. step. step. u7_br false ltac:(u7_bool).
    step. step. step. u7_br false ltac:(u7_bool).
    step. step. step. u7_br false ltac:(u7_bool).
    step.
    apply evt_done. do 3 eexists. right. split; [lia|]. reflexivity.
Qed.

Section Q04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_Q04 : forall j, Hat B APIf ra (Inv_U13e28_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13f98_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13de8_at B APIf ra empty) j.
Proof.
  intros j H34 Hfa4 g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HQB & H26 & H10)).
  pose proof HQB as (HEQ & H27 & HPO & H1792).
  destruct (u7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  pose proof alloc_ceiling_value as Hac.
  eapply (u7_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x _ O. exfalso. apply O. exact I.
  - rewrite sl_mkR_of.
    apply q04_evt with (spv := fsp g) (rp := t_rp (g_in g) j) (unk := t_unk (g_in g) j).
    + exact Hsp.
    + exact H10.
    + exact H26.
    + exact H27.
    + unfold fsp, SLOT_FRAME. lia.
    + unfold fsp, SLOT_FRAME. lia.
    + apply u7_rp_cases.
    + apply u7_rp_unk.
    + destruct (u7_unk_range (g_in g) j) as [E|E]; [left; exact E | right; lia].
    + intros E. destruct HPO as (_ & HP1). destruct (HP1 E) as (U0 & U1 & U2).
      pose proof (u7_rdn _ _ _ (u7_norm mem _ _ HMI U0)) as R0.
      pose proof (u7_rdn _ _ _ (u7_norm mem _ _ HMI U1)) as R1.
      pose proof (u7_rdn _ _ _ (u7_norm mem _ _ HMI U2)) as R2.
      rewrite length_le4 in R0, R1, R2. split; [exact R0|]. split; [exact R1 | exact R2].
  - intros ms (a0' & a1' & t2' & [(_ & -> & _) | (_ & ->)]);
      do 3 eexists; (split; [reflexivity|]); (split; [apply munch_refl|]); (split; [apply wmono_refl|]);
      (split; [reflexivity|]); split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    assert (MT : MT [] mem m') by exact (u7_mt _ _ _ MU').
    destruct HQ as (a0' & a1' & t2' & [(Erp & HE & E7) | (Erp & HE)]);
      destruct (u7_MS_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE) as (ER & Epc & Em); subst R pc' m0'.
    + subst t2'. apply H34. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [|split; [|split; [|split]]].
      * apply (u7_QB g j phi regs mem regs' m' [] HQB MT (u7_DJE_nil g j phi) (u7_DJQ_nil g)).
        -- unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
        -- rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). exact H26.
      * exact Erp.
      * apply u7_rp_unk. exact Erp.
      * unfold T2, rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + apply Hfa4. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      apply u7_EQ_CC. apply (u7_EQ g j phi regs mem regs' m' [] (proj1 HQB) MT (u7_DJE_nil g j phi)).
      unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
Qed.

End Q04.

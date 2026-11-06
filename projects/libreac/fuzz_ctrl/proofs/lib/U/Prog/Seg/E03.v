(* Segment E03 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13c88, 0x13cf0], U13c94 (v1.9 pc
   0x13c88) -> U13d00 (v1.9 pc 0x13cf4) (#68 not taken: a0 = 0; #69: p.counter = B[20 .. 22) = Φ[14] + 256 Φ[15],
   struct P5.2; #70: k = 1 exactly when Φ[16] = Φ[17] = 0, P5.3; the UBSan checks T44-T48 not taken by Φ's heap
   range; call reac_ctrl_checksum_verify(Φ) at 0x13cf0: a0 = sum_ok ? 0 : -1, C28 C1.2, C1.3). Φ is s7 and k is s9
   (v1.8 s6, s8). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv reac_ctrl_checksum_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u6.
Import ListNotations.
Open Scope Z_scope.

(* The register file, pc and memory of two equal machine states, by projection (injection on the concrete states
   of this segment does not finish). *)
Lemma e03_MS_inj : forall R F pc fc rv m ro R' F' pc' fc' rv' m' ro',
  MState.MS R F pc fc rv m ro = MState.MS R' F' pc' fc' rv' m' ro' -> R = R' /\ pc = pc' /\ m = m'.
Proof.
  intros R F pc fc rv m ro R' F' pc' fc' rv' m' ro' H.
  exact (conj (f_equal ms_regs H) (conj (f_equal ms_pc_val H) (f_equal ms_mem H))).
Qed.

Lemma e03_evt : reac_ctrl_checksum_verify_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi k : Z) (b14 b15 b16 b17 : byte)
         (bs : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 phi -> s9 = Z_to_bv 64 k -> a0 = Z_to_bv 64 0 ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> 4096 <= phi -> phi + 50 <= 2 ^ 63 -> 0 <= k <= 13 ->
    ov_read_bytes rsegs m (wa (phi + 14)) 1 = Some [b14] -> ov_read_bytes rsegs m (wa (phi + 15)) 1 = Some [b15] ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] -> ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] ->
    ov_read_bytes rsegs m (wa (spv + 1772)) 2 = Some (le2 (Z_to_bv 64 (256 * bv_unsigned b15 + bv_unsigned b14))) ->
    (k = 1 <-> bv_unsigned b16 = 0 /\ bv_unsigned b17 = 0) ->
    length bs = 32%nat -> bytes_at rsegs m (phi + 18) bs ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' : word),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if blocksum bs =? 0 then 0 else -1))
                       a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13cf4) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13c88) fc None m (seg_rom rsegs)).
Proof.
  intros CSV ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi k b14 b15 b16 b17 bs -> -> -> -> Hs Hsp Hp0 Hp1 Hk R14 R15 R16 R17 RC HF Hl HB.
  pose proof (RcLib.byte_range b14). pose proof (RcLib.byte_range b15).
  pose proof (RcLib.byte_range b16). pose proof (RcLib.byte_range b17).
  step. if_false.
  step. u6_nt false.
  step. step. u6_nt false.
  step. step. u6_nt false.
  step. step. step. step. step. step.
  (* #69: (Φ[15] << 8) | Φ[14] is the counter *)
  u6_br false ltac:(rewrite ?u6_orshl; rewrite ?u6_zx16 by lia; rewrite u6_eqb by lia; rewrite Z.eqb_refl; reflexivity).
  step. step. u6_nt false.
  step. step.
  destruct (Z.eq_dec (bv_unsigned b16) 0) as [E16|E16].
  - u6_br true ltac:(rewrite u6_eqz by lia; apply Z.eqb_eq; exact E16).
    step. step. u6_nt false.
    step. step.
    step. step. step.
    (* #70: [Φ[17] = 0] = [k = 1] *)
    u6_br false ltac:(rewrite u6_sltb, u6_sltk by lia;
                      replace (k =? 1) with (bv_unsigned b17 =? 0)
                        by (destruct (Z.eqb_spec (bv_unsigned b17) 0), (Z.eqb_spec k 1); first [reflexivity | exfalso; tauto]);
                      rewrite u6_eqb by (destruct (bv_unsigned b17 =? 0); cbn [b2z]; lia);
                      rewrite Z.eqb_refl; reflexivity).
    step. step.
    eapply evt_cut.
    { eapply CSV with (p := phi) (bs := bs); [lia | lia | first [reflexivity | f_equal; lia] | exact Hl | exact HB]. }
    intros ms' (a1' & a2' & a3' & a4' & a5' & ->).
    rewrite (MState.ret_pc_even 0x13cf4) by (first [reflexivity | lia]).
    apply evt_done. do 6 eexists. reflexivity.
  - u6_br false ltac:(rewrite u6_eqz by lia; apply Z.eqb_neq; exact E16).
    step. step.
    step. step. step.
    (* #70: 0 = [k = 1] since Φ[16] <> 0 *)
    u6_br false ltac:(rewrite u6_sltk by lia;
                      replace (k =? 1) with false
                        by (symmetry; apply Z.eqb_neq; intros X; apply E16; exact (proj1 (proj1 HF X)));
                      reflexivity).
    step. step.
    eapply evt_cut.
    { eapply CSV with (p := phi) (bs := bs); [lia | lia | first [reflexivity | f_equal; lia] | exact Hl | exact HB]. }
    intros ms' (a1' & a2' & a3' & a4' & a5' & ->).
    rewrite (MState.ret_pc_even 0x13cf4) by (first [reflexivity | lia]).
    apply evt_done. do 6 eexists. reflexivity.
Qed.

Section E03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CSV : reac_ctrl_checksum_verify_contract.

Lemma seg_E03 : forall j,
  Hat B APIf ra (Inv_U13cf4_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13c88_at B APIf ra empty) j.
Proof.
  intros j H00 g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HEA & H88) & H10).
  destruct (u6_S_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  destruct (u6_phi_rng B APIf ra empty _ _ _ _ _ _ _ _ HFR HP) as (Hph & Hph2).
  pose proof alloc_ceiling_lt as Hac.
  pose proof HEA as ((HT & H7 & H1 & H0 & H2 & HC) & HIFS).
  pose proof HT as (HLK & HFC & H23 & HPhi & H18).
  pose proof HC as (H24 & H16 & HB).
  unfold SLOT_K, SLOT_STACK in *.
  assert (Hf : fsp g = g_S g - 1936) by (unfold fsp, SLOT_FRAME; reflexivity).
  pose proof (u6_big_8819 _ _ H88) as Hl.
  pose proof (u6_norm mem _ _ HMI (u6_ba_g mem phi (g_in g) j HPhi Hl)) as HG50.
  pose proof (u6_g_len (g_in g) j) as LG.
  (* p.counter = B[20 .. 22) at sp+1772 = [Φ[14]; Φ[15]] (struct P5.2) *)
  pose proof (u6_ba_sub mem (spk g 1752) (t_B (g_in g) j) 20 2 HB
                ltac:(unfold t_B; rewrite RcParse.ctrlparse_length; lia)) as XC.
  rewrite (u6_cnt (g_in g) j H88) in XC.
  rewrite <- u6_le2 in XC.
  replace (spk g 1752 + Z.of_nat 20) with (fsp g + 1772) in XC by (unfold spk; lia).
  pose proof (u6_ovr _ _ _ (u6_norm mem _ _ HMI XC)) as RC. rewrite length_le2 in RC.
  (* the 32 block bytes Φ[18 .. 50) *)
  pose proof (u6_ba_sub _ phi (t_g (g_in g) j) 18 32 HG50 ltac:(lia)) as XS.
  replace (phi + Z.of_nat 18) with (phi + 18) in XS by lia.
  eapply (u6_mid B APIf ra empty FF g _ L A regs mem md _ [(0, 0)]); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. cbn [Frame.outside]. split; [lia | exact I].
  - rewrite sl_mkR_of.
    apply (e03_evt CSV) with (spv := fsp g) (phi := phi) (k := t_k (g_in g) j)
      (b14 := nth 14 (t_g (g_in g) j) (Z_to_bv 8 0)) (b15 := nth 15 (t_g (g_in g) j) (Z_to_bv 8 0))
      (b16 := nth 16 (t_g (g_in g) j) (Z_to_bv 8 0)) (b17 := nth 17 (t_g (g_in g) j) (Z_to_bv 8 0))
      (bs := firstn 32 (skipn 18 (t_g (g_in g) j))).
    + exact Hsp.
    + exact H23.
    + exact H7.
    + exact H10.
    + lia.
    + lia.
    + lia.
    + lia.
    + apply u6_k_range.
    + exact (RcLib.rd_byte rsegs _ phi _ 14 HG50 ltac:(lia)).
    + exact (RcLib.rd_byte rsegs _ phi _ 15 HG50 ltac:(lia)).
    + exact (RcLib.rd_byte rsegs _ phi _ 16 HG50 ltac:(lia)).
    + exact (RcLib.rd_byte rsegs _ phi _ 17 HG50 ltac:(lia)).
    + exact RC.
    + exact (u6_filler (g_in g) j H88).
    + rewrite length_firstn, length_skipn, LG. reflexivity.
    + exact XS.
  - intros ms (ra' & a1' & a2' & a3' & a4' & a5' & ->).
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity | split; reflexivity].
  - intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
    destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & HE).
    destruct (e03_MS_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE) as (ER & EP & EM).
    subst R pc' m0'.
    assert (AV : u6_av g phi (t_len (g_in g) j) 0 0) by (apply u6_av0; unfold fsp, SLOT_FRAME; lia).
    assert (AI : u6_ai g 0 0) by (apply u6_ai0; unfold fsp, SLOT_FRAME; lia).
    assert (K : u6_kT regs regs') by (unfold u6_kT; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split).
    assert (E19 : YK11.getr regs' 19 = YK11.getr regs 19) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E27 : YK11.getr regs' 27 = YK11.getr regs 27) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    pose proof (u6_EA_keep g j phi regs regs' mem m' 0 0 HEA K E19 E27 MU AV AI) as HEA'.
    apply H00. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; [exact HEA' | exact H88]|].
    unfold rg. rewrite (sl_getr_eqv _ _ _ Hx).
    transitivity (Z_to_bv 64 (if blocksum (firstn 32 (skipn 18 (t_g (g_in g) j))) =? 0 then 0 else -1));
      [reflexivity|].
    rewrite (u6_sum8819 (g_in g) j H88). reflexivity.
Qed.

End E03.

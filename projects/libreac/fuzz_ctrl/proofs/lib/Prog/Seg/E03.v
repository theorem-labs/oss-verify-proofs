(* Segment E03 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13aa8, 0x13aec], K13aa8 -> K13af0 (#68 not taken: the
   p.src bcmp returned 0; #69 p.counter = Φ[14] | Φ[15] << 8 (struct P5.2); #70 (k == 1) = (Φ[16] = Φ[17] = 0)
   (P5.3); reac_ctrl_checksum_verify on Φ[18 .. 50) returns sum_ok - 1).
   libreac v1.9.0 (table 5a S_E03, IDENTICAL-RENUMBER): pcs + 0x30, p = sp+1752 so p.counter = sp+1772 (v1.8 1756),
   the frame 1936 bytes. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel SlotModel SlotInv reac_ctrl_checksum_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b6.
Import ListNotations.
Open Scope Z_scope.

(* 0x13ae8-0x13aec: reac_ctrl_checksum_verify (Φ) and the return to 0x13af0. *)
Ltac e03_call CSV phi bs Lbs Hbs :=
  step; step;
  eapply evt_cut;
  [ eapply CSV with (p := phi) (bs := bs); [lia | lia | first [reflexivity | f_equal; lia] | exact Lbs | exact Hbs]
  | ];
  let a1' := fresh "a1'" in let a2' := fresh "a2'" in let a3' := fresh "a3'" in let E := fresh "E" in
  intros ?ms' (a1' & a2' & a3' & E); subst;
  replace (ret_pc (Z_to_bv 64 0x13af0)) with (Z_to_bv 64 0x13af0)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]);
  apply evt_done; exists a1', a2', a3'; reflexivity.

Lemma e03_evt : reac_ctrl_checksum_verify_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi k : Z) (b14 b15 b16 b17 : byte)
         (bs : list byte),
    sp = Z_to_bv 64 spv -> s5 = Z_to_bv 64 phi -> s7 = Z_to_bv 64 k -> a0 = Z_to_bv 64 0 ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> 0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= k <= 13 ->
    (k = 1 <-> bv_unsigned b16 = 0 /\ bv_unsigned b17 = 0) ->
    ov_read_bytes rsegs m (wa (phi + 14)) 1 = Some [b14] -> ov_read_bytes rsegs m (wa (phi + 15)) 1 = Some [b15] ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] -> ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] ->
    ov_read_bytes rsegs m (wa (spv + 1772)) 2 = Some [b14; b15] ->
    length bs = 32%nat -> bytes_at rsegs m (phi + 18) bs ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR (Z_to_bv 64 0x13af0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if blocksum bs =? 0 then 0 else -1))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13af0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13aa8) fc None m (seg_rom rsegs)).
Proof.
  intros CSV ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi k b14 b15 b16 b17 bs -> -> -> -> Hs Hsp Hp0 Hp1 Hk Hf R14 R15 R16 R17 RC Lbs Hbs.
  pose proof (RcLib.byte_range b14). pose proof (RcLib.byte_range b15).
  rewrite <- (b6_le2 b15 b14) in RC.
  step. if_false. step. step. step. step. step.
  rewrite b6_orshl. rewrite b6_zx16 by lia.
  step. if_false.
  step. step.
  rewrite (b6_eqz b16 0) by lia.
  destruct (Z.eqb_spec (bv_unsigned b16) 0) as [E16 | E16]; cbv iota.
  - (* Φ[16] = 0: a0 = (Φ[17] == 0) *)
    step. step. step. step. step.
    rewrite b6_sltb, b6_sltk by lia.
    replace (bv_unsigned b17 =? 0) with (k =? 1)
      by (destruct (Z.eqb_spec k 1), (Z.eqb_spec (bv_unsigned b17) 0); try reflexivity; exfalso; tauto).
    if_false.
    e03_call CSV phi bs Lbs Hbs.
  - (* Φ[16] != 0: a0 = 0, and k != 1 *)
    step. step. step. step. step.
    rewrite b6_sltk by lia.
    replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; intros X; apply E16; exact (proj1 (proj1 Hf X))).
    cbn [b2z]. if_false.
    e03_call CSV phi bs Lbs Hbs.
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
  Hat B APIf ra (Inv_K13af0_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13aa8_at B APIf ra empty) j.
Proof.
  intros j Hac0 g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HEA & H8) & H10).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  destruct (b6_phi_rng B APIf ra empty _ _ _ _ _ _ _ _ HFR HP) as (Hph & Hph2).
  pose proof HEA as (HT & H7 & H9 & H0 & H2 & HC & HIFS).
  pose proof HT as (Hj & H26 & HFC & H21 & HPhi & HOUR & HM7).
  pose proof HC as (H8r & H22 & HTF & HB).
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Hf : fsp g = g_S g - 1936) by (unfold fsp, SLOT_FRAME; reflexivity).
  destruct (b6_8819 (g_in g) j H8) as (Hl & _ & _).
  pose proof (RcParse.ctrlparse_kind_range (t_len (g_in g) j) (t_g (g_in g) j)) as Hk. fold (t_k (g_in g) j) in Hk.
  pose proof (b6_g_len (g_in g) j) as LG.
  pose proof (b6_norm mem _ _ HMI (b6_ba_g mem phi (g_in g) j HPhi Hl)) as HG50.
  (* p.counter = B[20 .. 22) at sp+1772 = Φ[14], Φ[15] *)
  pose proof (b6_ba_sub mem (spk g 1752) (t_B (g_in g) j) 20 2 HB
                ltac:(unfold t_B; rewrite RcParse.ctrlparse_length; lia)) as XC.
  rewrite (b6_cnt (g_in g) j H8) in XC.
  replace (spk g 1752 + Z.of_nat 20) with (fsp g + 1772) in XC by (unfold spk; lia).
  pose proof (b6_ovr _ _ _ (b6_norm mem _ _ HMI XC)) as RC. cbn [length] in RC.
  (* the 32 block bytes Φ[18 .. 50) *)
  pose proof (b6_ba_sub _ phi (t_g (g_in g) j) 18 32 HG50 ltac:(lia)) as XB.
  replace (phi + Z.of_nat 18) with (phi + 18) in XB by lia.
  assert (LB : length (firstn 32 (skipn 18 (t_g (g_in g) j))) = 32%nat)
    by (rewrite length_firstn, length_skipn; lia).
  pose proof (b6_sum8819 (g_in g) j H8) as Hsum.
  revert XB LB Hsum. generalize (firstn 32 (skipn 18 (t_g (g_in g) j))) as bs. intros bs XB LB Hsum.
  eapply (b6_mid B APIf ra empty FF g _ L A regs mem md _ [(0, 0)]); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. cbn [Frame.outside]. split; [lia | exact I].
  - rewrite sl_mkR_of.
    apply (e03_evt CSV) with (spv := fsp g) (phi := phi) (k := t_k (g_in g) j)
      (b14 := nth 14 (t_g (g_in g) j) (Z_to_bv 8 0)) (b15 := nth 15 (t_g (g_in g) j) (Z_to_bv 8 0))
      (b16 := nth 16 (t_g (g_in g) j) (Z_to_bv 8 0)) (b17 := nth 17 (t_g (g_in g) j) (Z_to_bv 8 0))
      (bs := bs).
    + exact Hsp.
    + exact H21.
    + exact H7.
    + exact H10.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact (b6_filler (g_in g) j H8).
    + exact (RcLib.rd_byte rsegs _ phi _ 14 HG50 ltac:(lia)).
    + exact (RcLib.rd_byte rsegs _ phi _ 15 HG50 ltac:(lia)).
    + exact (RcLib.rd_byte rsegs _ phi _ 16 HG50 ltac:(lia)).
    + exact (RcLib.rd_byte rsegs _ phi _ 17 HG50 ltac:(lia)).
    + exact RC.
    + exact LB.
    + exact XB.
  - intros ms (? & ? & ? & ->). do 3 eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [reflexivity | split; reflexivity].
  - intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
    destruct HQ as (a1' & a2' & a3' & HE).
    (* the registers and pc by projection: injection would compare the two seg_rom constants by evaluation *)
    pose proof (f_equal ms_regs HE) as ER. pose proof (f_equal ms_pc_val HE) as EP. clear HE.
    unfold MS in ER, EP. cbn [ms_regs ms_pc_val] in ER, EP. subst R pc'.
    assert (AV : b6_av g phi (t_len (g_in g) j) 0 0) by (apply b6_av0; unfold fsp, SLOT_FRAME; lia).
    assert (O154 : b6_out 0 0 (spk g 154) 38) by (apply b6_out0; unfold spk, fsp, SLOT_FRAME; lia).
    assert (O16 : b6_out 0 0 (spk g 16) 60) by (apply b6_out0; unfold spk, fsp, SLOT_FRAME; lia).
    assert (K : b6_kS regs regs') by (unfold b6_kS; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split).
    assert (E18 : YK11.getr regs' 18 = YK11.getr regs 18) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    pose proof (b6_EA_keep g j phi regs regs' mem m' 0 0 HEA K E18 MU AV O154 O16) as HEA'.
    apply Hac0. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; [exact HEA' | exact H8]|].
    unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). rewrite Hsum; reflexivity.
Qed.

End E03.

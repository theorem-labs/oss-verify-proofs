(* Segment Q06 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13c40, 0x13c9c], K13c40 -> K13ca0. Branches #80, #81
   (C5.6: 4 n_in, 4 n_out and unk = 4 n_unk are multiples of 4), #82 (C5.7: the byte first = want_first), #83 (C5.6:
   4 (n_in + n_out + n_empty + n_unk) = 48), #84, #85 (C5.6: in_ch = 4 n_in, out_ch = 4 n_out) and #86 (C5.8:
   headamp_base = 16 blk[7]) are not taken. *)
(* libreac v1.9.0 (IDENTICAL-RENUMBER, segment table 5a S_Q06): v1.8 [0x13c10, 0x13c6c] K13c10 -> K13c70; the ports
   slots sp+1672 / 1676 / 1680 -> sp+1688 / 1692 / 1696, check_ports `first` sp+1776 -> sp+1792; VC -> VCm in EQ and
   CC7 (SlotInv.v). Statement kept on the renamed cuts. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b7.
Import ListNotations.
Open Scope Z_scope.

(* #80: in_ch & 3 = 0. *)
Lemma q06_c80 : forall nin, 0 <= nin <= 12 ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (sx32 (Z_to_bv 64 (4 * nin)))) 3)) (Z_to_bv 64 0)) = false.
Proof.
  intros nin H. rewrite b7_sx32 by lia. rewrite MState.unsigned_lit by lia. rewrite b7_land4 by lia.
  rewrite bv_eqb_refl. reflexivity.
Qed.

(* #81: (out_ch | unk) & 3 = 0. *)
Lemma q06_c81 : forall nout nu, 0 <= nout <= 12 -> 0 <= nu <= 12 ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 (Z_to_bv 64 (4 * nout))))
                                                                    (bv_unsigned (Z_to_bv 64 (4 * nu)))))) 3))
               (Z_to_bv 64 0)) = false.
Proof.
  intros nout nu H1 H2. rewrite b7_sx32 by lia.
  rewrite (MState.unsigned_lit (4 * nout)) by lia. rewrite (MState.unsigned_lit (4 * nu)) by lia.
  rewrite (MState.unsigned_lit (Z.lor (4 * nout) (4 * nu))) by (apply ZBridge.zr_lor; unfold ZBridge.inr64; lia).
  rewrite Z.land_lor_distr_l, !b7_land4 by lia. rewrite bv_eqb_refl. reflexivity.
Qed.

(* #82: the byte first read back equals zext.b of want_first. *)
Lemma q06_c82 : forall pf, 0 <= pf < 256 ->
  negb (bv_eqb (zxb (Z_to_bv 8 pf)) (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 pf)) 255))) = false.
Proof.
  intros pf H.
  pose proof (b7_all (fun pf => Bool.eqb (negb (bv_eqb (zxb (Z_to_bv 8 pf))
                                     (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 pf)) 255)))) false)
                ltac:(vm_compute; reflexivity) pf H) as E.
  cbv beta in E. apply Bool.eqb_prop in E. exact E.
Qed.

(* #83: 4 n_empty + unk + in_ch + out_ch = 48. *)
Lemma q06_c83 : forall nin nout nemp nu, 0 <= nin <= 12 -> 0 <= nout <= 12 -> 0 <= nemp <= 12 -> 0 <= nu <= 12 ->
  nin + nout + nemp + nu = 12 ->
  negb (bv_eqb
          (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 nemp)) 2)) +
                                    bv_unsigned (Z_to_bv 64 (4 * nu + bv_unsigned (sx32 (Z_to_bv 64 (4 * nin))) +
                                                              bv_unsigned (sx32 (Z_to_bv 64 (4 * nout))))))))
          (Z_to_bv 64 48)) = false.
Proof.
  intros nin nout nemp nu H1 H2 H3 H4 H5. rewrite !b7_sx32 by lia.
  rewrite (MState.unsigned_lit nemp) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  rewrite (MState.unsigned_lit (4 * nin)) by lia. rewrite (MState.unsigned_lit (4 * nout)) by lia.
  rewrite (MState.unsigned_lit (nemp * 4)) by lia.
  rewrite (MState.unsigned_lit (4 * nu + 4 * nin + 4 * nout)) by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  replace (nemp * 4 + (4 * nu + 4 * nin + 4 * nout)) with 48 by lia.
  rewrite bv_eqb_refl. reflexivity.
Qed.

(* #84, #85: a port width against 4 times its count. *)
Lemma q06_c84 : forall n, 0 <= n <= 12 ->
  negb (bv_eqb (sx32 (Z_to_bv 64 (4 * n))) (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 2)))) =
  false.
Proof.
  intros n H. rewrite b7_sx32 by lia. rewrite MState.unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 2) with 4. rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  replace (n * 4) with (4 * n) by lia. rewrite bv_eqb_refl. reflexivity.
Qed.

(* #86: headamp_base = 16 blk[7]. *)
Lemma q06_c86 : forall b : byte,
  negb (bv_eqb (sx32 (Z_to_bv 64 (16 * bv_unsigned b))) (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 4))) = false.
Proof.
  intros b. pose proof (b7_byte_range b) as R. rewrite b7_sx32 by lia. rewrite b7_uzxb.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. replace (bv_unsigned b * 16) with (16 * bv_unsigned b) by lia.
  rewrite bv_eqb_refl. reflexivity.
Qed.

(* 0x13c40 -> 0x13ca0 with the counts of the slot loop in a1, a0, a2, want_first in a5, unk = 4 n_unk in s8. *)
Lemma q06_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi nu nin nout nemp pf : Z) (b7 : byte),
    sp = Z_to_bv 64 spv -> s6 = Z_to_bv 64 (phi + 18) -> s8 = Z_to_bv 64 (4 * nu) ->
    a1 = Z_to_bv 64 nin -> a0 = Z_to_bv 64 nout -> a2 = Z_to_bv 64 nemp -> a5 = Z_to_bv 64 pf ->
    0 <= nin <= 12 -> 0 <= nout <= 12 -> 0 <= nemp <= 12 -> 0 <= nu <= 12 -> nin + nout + nemp + nu = 12 ->
    0 <= pf < 256 ->
    u32 m (spv + 1688) (4 * nin) -> u32 m (spv + 1692) (4 * nout) -> u32 m (spv + 1696) (16 * bv_unsigned b7) ->
    b8 m (spv + 1792) pf -> bytes_at rsegs m (phi + 25) [b7] ->
    evt rsegs
      (fun ms' => exists a0' a1' a2' a3' a4' a5' a6' s8' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8' s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13ca0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13c40) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi nu nin nout nemp pf b7 -> -> -> -> -> -> -> Hin Hout Hemp Hnu Hsum Hpf P0 P4 P8 P16 P25.
  pose proof (b7_rdn m _ _ P0) as R0. pose proof (b7_rdn m _ _ P4) as R4. pose proof (b7_rdn m _ _ P8) as R8.
  rewrite length_le4 in R0, R4, R8.
  pose proof (b7_rdn m _ _ P16) as R16. pose proof (b7_rdn m _ _ P25) as R25. cbn [length] in R16, R25.
  step. step. step. b7_br false ltac:(exact (q06_c80 nin Hin)).
  step. step. step. step. b7_br false ltac:(exact (q06_c81 nout nu Hout Hnu)).
  step. step. step. b7_br false ltac:(exact (q06_c82 pf Hpf)).
  step. step. step. step. step. step. b7_br false ltac:(exact (q06_c83 nin nout nemp nu Hin Hout Hemp Hnu Hsum)).
  step. step. b7_br false ltac:(exact (q06_c84 nin Hin)).
  step. step. b7_br false ltac:(exact (q06_c84 nout Hout)).
  step. step. step. step. b7_br false ltac:(exact (q06_c86 b7)).
  apply evt_done. do 8 eexists. reflexivity.
Qed.

Section Q06.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_Q06 : forall j, Hat B APIf ra (Inv_K13ca0_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13c40_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP &
                  (HQB & H24 & Er & Hu & H11 & H10 & H12 & H15)).
  pose proof HQB as (HEQ & H25 & HPO & H1792).
  pose proof HEQ as (HFT & H7 & H2 & HVC & HIFS & H88).
  pose proof HFT as (Hj & H26 & HFC & H21 & Hphi & HOUR & HM7).
  pose proof HVC as (H22 & HTF & HB).
  pose proof (b7_big_8819 _ _ H88) as Hbig.
  destruct (b7_phi_bnd B APIf ra empty g _ L A regs mem md phi _ HFR HP ltac:(lia)) as (Hp1 & Hp2).
  destruct (b7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  pose proof alloc_ceiling_value as Hac.
  assert (H22' : rg regs 22 (phi + 18)).
  { unfold t_big in H22. rewrite (proj2 (Z.leb_le _ _) Hbig) in H22. exact H22. }
  destruct (b7_unk_rp0 _ _ Er) as (_ & Ed).
  set (bs := t_pbs (g_in g) j) in *.
  assert (H24' : rg regs 24 (4 * RcPorts.pu_nunk bs 12)).
  { unfold t_unk in H24. fold bs in H24. rewrite Ed in H24. exact H24. }
  assert (H1792' : b8 mem (spk g 1792) (RcPorts.pu_first bs 12)).
  { unfold t_first in H1792. fold bs in H1792. rewrite Ed in H1792. exact H1792. }
  destruct (proj1 HPO Er) as (P0 & P4 & P8). fold bs in P0, P4, P8.
  pose proof (b7_codes_sum bs 12) as Hsum. change (Z.of_nat 12) with 12 in Hsum.
  pose proof (b7_cnt_range RcLeaf.is_in bs 12) as Rin. pose proof (b7_cnt_range RcLeaf.is_out bs 12) as Rout.
  pose proof (b7_cnt_range is_empty bs 12) as Remp.
  pose proof (b7_nunk_nonneg bs 12) as Rnu0. pose proof (b7_nunk_le bs 12) as Rnu1.
  pose proof (b7_first_spec bs 12) as (_ & Rpf).
  change (Z.of_nat 12) with 12 in Rin, Rout, Remp, Rnu1.
  assert (HG : bytes_at rsegs (normalize rsegs mem) phi (t_g (g_in g) j))
    by (apply b7_norm; [exact HMI | apply b7_g_bytes; [exact Hphi | exact Hbig]]).
  pose proof (b7_bytes_nths _ _ _ 25 1 HG ltac:(rewrite b7_g_length; lia)) as H25b. cbn [b7_nths] in H25b.
  change (Z.of_nat 25) with 25 in H25b.
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply q06_evt with (spv := fsp g) (phi := phi) (nu := RcPorts.pu_nunk bs 12) (nin := RcLeaf.n_in bs)
      (nout := RcLeaf.n_out bs) (nemp := RcLeaf.cnt is_empty bs 12) (pf := RcPorts.pu_first bs 12)
      (b7 := nth 7 bs (Z_to_bv 8 0)).
    + exact Hsp.
    + exact H22'.
    + exact H24'.
    + exact H11.
    + exact H10.
    + exact H12.
    + exact H15.
    + exact Rin.
    + exact Rout.
    + exact Remp.
    + lia.
    + unfold RcLeaf.n_in, RcLeaf.n_out. lia.
    + exact Rpf.
    + exact (b7_norm _ _ _ HMI P0).
    + exact (b7_norm _ _ _ HMI P4).
    + exact (b7_norm _ _ _ HMI P8).
    + exact (b7_norm _ _ _ HMI H1792').
    + unfold bs. rewrite (b7_pbs_bt (g_in g) j 7 ltac:(lia)). exact H25b.
  - intros ms (a0' & a1' & a2' & a3' & a4' & a5' & a6' & s8' & ->). do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists []. split; [apply munch_refl|]. split; [apply wmono_refl|]. intros x _ O. exfalso. apply O. exact I.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (a0' & a1' & a2' & a3' & a4' & a5' & a6' & s8' & HE).
    apply b7_MS_inj in HE as (ER & EPC & EM). subst R pc' m0'.
    apply H. unfold Inv_K13ca0_at, FCUT, CUTST. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (MT0 : MT [] mem m') by exact (b7_mt [] mem _ m' HMI (munch_refl _ _) Hrel).
    assert (HEQ' : EQ g j phi regs' m').
    { apply (b7_EQ g j phi regs mem regs' m' []); [exact HEQ | exact MT0 | apply b7_DJE_nil |].
      unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity. }
    destruct HEQ' as (HFT' & H7' & H2' & HVC' & HIFS' & _).
    split; [|exact H7']. split; [exact HFT'|]. split; [exact H2'|]. split; [exact HVC' | exact HIFS'].
Qed.

End Q06.

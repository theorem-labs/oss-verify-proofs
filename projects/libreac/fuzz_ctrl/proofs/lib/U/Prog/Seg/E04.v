(* Segment E04 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13cf4, 0x13d9c], U13d00 (v1.9 pc
   0x13cf4) -> U13dac (v1.9 pc 0x13da0) (call reac_ctrl_headamp_record_verify at 0x13d9c). s11 becomes sum_ok - 1 and
   #71 (CSV: a0 = sum_ok - 1) is not taken; #72 and #73 (struct P5.4: k = 6 gives Φ[18] = 4, Φ[19] = 3) are not
   taken; the UBSan checks T49-T54 are not taken by Φ's heap range (T54 by AF11); the inline record sum (head
   0x13d74, 6 turns) gives s3 = want_v. Φ is s7, k is s9 (v1.8: sum_ok s10, Φ s6, k s8, want_v s1). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv
  reac_ctrl_headamp_record_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcParse RcLeaf RcFrag RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u6.
Import ListNotations.
Open Scope Z_scope.

Lemma e04_hv0 : forall b0 b1 rec, bv_unsigned b0 <> 4 -> RcLeaf.hv b0 b1 rec = false.
Proof. intros b0 b1 rec H. unfold RcLeaf.hv. destruct (Z.eqb_spec (bv_unsigned b0) 4); [lia | reflexivity]. Qed.

Lemma e04_hv1 : forall b0 b1 rec, bv_unsigned b1 <> 3 -> RcLeaf.hv b0 b1 rec = false.
Proof.
  intros b0 b1 rec H. unfold RcLeaf.hv. destruct (Z.eqb_spec (bv_unsigned b1) 3); [lia|].
  rewrite andb_false_r. reflexivity.
Qed.

Lemma e04_hv : forall b0 b1 rec, bv_unsigned b0 = 4 -> bv_unsigned b1 = 3 ->
  RcLeaf.hv b0 b1 rec = (RcLeaf.rsum rec =? 0).
Proof. intros b0 b1 rec H0 H1. unfold RcLeaf.hv. rewrite H0, H1. reflexivity. Qed.

(* want_v of a frame's first 50 bytes G. *)
Definition e04_wv (G : list byte) : Z :=
  if RcLeaf.hv (RcParse.cp_b G 18) (RcParse.cp_b G 19) (RcFrag.bsl G 34 6) then 0 else -1.

(* 0x13d60 -> 0x13d98: the inline record_sum_closes over Φ[34 .. 40) with the AF11 check each turn. *)
Lemma e04_sum :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (r0 r1 r2 r3 r4 r5 : byte),
    s7 = Z_to_bv 64 phi -> 0 <= phi -> phi + 104 <= 2 ^ 64 ->
    bytes_at rsegs m (phi + 34) [r0; r1; r2; r3; r4; r5] ->
    evt rsegs
      (fun ms' => exists a0' a1' a2' a3' a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s2
                       (Z_to_bv 64 (if RcLeaf.rsum [r0; r1; r2; r3; r4; r5] =? 0 then 0 else -1))
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13d98) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13d60) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi r0 r1 r2 r3 r4 r5 -> H0 H40 HR.
  pose proof (u6_rd1 m _ _ 0 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R0.
  pose proof (u6_rd1 m _ _ 1 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R1.
  pose proof (u6_rd1 m _ _ 2 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R2.
  pose proof (u6_rd1 m _ _ 3 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R3.
  pose proof (u6_rd1 m _ _ 4 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R4.
  pose proof (u6_rd1 m _ _ 5 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R5.
  cbn [nth Z.of_nat] in R0, R1, R2, R3, R4, R5.
  pose proof (RcLib.byte_range r0). pose proof (RcLib.byte_range r1). pose proof (RcLib.byte_range r2).
  pose proof (RcLib.byte_range r3). pose proof (RcLib.byte_range r4). pose proof (RcLib.byte_range r5).
  step. step. step. step. step.
  step. u6_br false ltac:(apply u6_af11; [reflexivity | lia | lia | lia]).
  step. step. step. step. step. u6_br true ltac:(rewrite u6_eqb by lia; u6_zdec).
  step. u6_br false ltac:(apply u6_af11; [reflexivity | lia | lia | lia]).
  step. step. step. step. step. u6_br true ltac:(rewrite u6_eqb by lia; u6_zdec).
  step. u6_br false ltac:(apply u6_af11; [reflexivity | lia | lia | lia]).
  step. step. step. step. step. u6_br true ltac:(rewrite u6_eqb by lia; u6_zdec).
  step. u6_br false ltac:(apply u6_af11; [reflexivity | lia | lia | lia]).
  step. step. step. step. step. u6_br true ltac:(rewrite u6_eqb by lia; u6_zdec).
  step. u6_br false ltac:(apply u6_af11; [reflexivity | lia | lia | lia]).
  step. step. step. step. step. u6_br true ltac:(rewrite u6_eqb by lia; u6_zdec).
  step. u6_br false ltac:(apply u6_af11; [reflexivity | lia | lia | lia]).
  step. step. step. step. step. u6_br false ltac:(rewrite u6_eqb by lia; u6_zdec).
  step. step. step.
  apply evt_done. rewrite !u6_uzxb. rewrite u6_wv by lia. do 6 eexists. reflexivity.
Qed.

(* 0x13d98 -> 0x13da0: mv a0,s7; jal reac_ctrl_headamp_record_verify (HRV C1.2, C1.3). *)
Lemma e04_tail : reac_ctrl_headamp_record_verify_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (b0 b1 : byte) (rec : list byte),
    s7 = Z_to_bv 64 phi -> 0 < phi -> phi + 40 <= 2 ^ 64 ->
    bytes_at rsegs m (phi + 18) [b0; b1] -> bytes_at rsegs m (phi + 34) rec -> length rec = 6%nat ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' a4' a5' : word,
         ms' = MS (mkR (Z_to_bv 64 0x13da0) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (if RcLeaf.hv b0 b1 rec then 0 else -1))
                       a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13da0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13d98) fc None m (seg_rom rsegs)).
Proof.
  intros HRV ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi b0 b1 rec -> Hp Hp40 HB HR Hl.
  step. step.
  eapply evt_cut.
  { eapply HRV with (p := phi) (b0 := b0) (b1 := b1) (rec := rec); [| lia | lia | exact HB | exact Hl | exact HR].
    first [reflexivity | f_equal; lia]. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & ->).
  rewrite (MState.ret_pc_even 0x13da0) by (first [reflexivity | lia]).
  apply evt_done. exists a1', a2', a3', a4', a5'. reflexivity.
Qed.

(* 0x13d2c -> 0x13da0: T51; s3 = -1; Φ[18] = 4 and Φ[19] = 3 (T52) lead to T53 and the record sum; the call. *)
Lemma e04_rest : reac_ctrl_headamp_record_verify_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (b0 b1 r0 r1 r2 r3 r4 r5 : byte),
    s7 = Z_to_bv 64 phi -> 4096 <= phi -> phi + 50 <= 2 ^ 63 ->
    bytes_at rsegs m (phi + 18) [b0; b1] -> bytes_at rsegs m (phi + 34) [r0; r1; r2; r3; r4; r5] ->
    evt rsegs
      (fun ms' => exists ra' a1' a2' a3' a4' a5' : word,
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (if RcLeaf.hv b0 b1 [r0; r1; r2; r3; r4; r5] then 0 else -1))
                       a1' a2' a3' a4' a5' a6 a7 s2
                       (Z_to_bv 64 (if RcLeaf.hv b0 b1 [r0; r1; r2; r3; r4; r5] then 0 else -1))
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13da0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13d2c) fc None m (seg_rom rsegs)).
Proof.
  intros HRV ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi b0 b1 r0 r1 r2 r3 r4 r5 Hs7 Hp0 Hp1 HB HR.
  pose proof (u6_rd1 m _ _ 0 (Z_to_bv 8 0) HB ltac:(cbn; lia)) as L18.
  pose proof (u6_rd1 m _ _ 1 (Z_to_bv 8 0) HB ltac:(cbn; lia)) as L19.
  cbn [nth Z.of_nat] in L18, L19.
  pose proof (RcLib.byte_range b0) as R18. pose proof (RcLib.byte_range b1) as R19.
  subst s7.
  step. step. u6_nt false.
  step. step. step. step.
  destruct (Z.eq_dec (bv_unsigned b0) 4) as [E18|E18].
  - u6_br false ltac:(rewrite u6_eqz by lia; u6_zdec).
    step. step. u6_nt false.
    step. step. step.
    destruct (Z.eq_dec (bv_unsigned b1) 3) as [E19|E19].
    + u6_br false ltac:(rewrite u6_eqz by lia; u6_zdec).
      step. step. u6_nt false.
      eapply evt_cut; [eapply e04_sum; [reflexivity | lia | lia | exact HR]|].
      intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & ->).
      eapply evt_mono; [eapply (e04_tail HRV); [reflexivity | lia | lia | exact HB | exact HR | reflexivity]|].
      intros ms' (a1'' & a2'' & a3'' & a4'' & a5'' & ->).
      exists (Z_to_bv 64 0x13da0), a1'', a2'', a3'', a4'', a5''. rewrite (e04_hv _ _ _ E18 E19). reflexivity.
    + u6_br true ltac:(rewrite u6_eqz by lia; u6_zdec).
      eapply evt_mono; [eapply (e04_tail HRV); [reflexivity | lia | lia | exact HB | exact HR | reflexivity]|].
      intros ms' (a1'' & a2'' & a3'' & a4'' & a5'' & ->).
      exists (Z_to_bv 64 0x13da0), a1'', a2'', a3'', a4'', a5''. rewrite (e04_hv1 _ _ _ E19). reflexivity.
  - u6_br true ltac:(rewrite u6_eqz by lia; u6_zdec).
    eapply evt_mono; [eapply (e04_tail HRV); [reflexivity | lia | lia | exact HB | exact HR | reflexivity]|].
    intros ms' (a1'' & a2'' & a3'' & a4'' & a5'' & ->).
    exists (Z_to_bv 64 0x13da0), a1'', a2'', a3'', a4'', a5''. rewrite (e04_hv0 _ _ _ E18). reflexivity.
Qed.

(* 0x13cf4 -> 0x13da0 for a frame whose first 50 bytes G are at Φ, kind k, sum_ok so. *)
Lemma e04_evt : reac_ctrl_headamp_record_verify_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi k : Z) (so : bool) (G : list byte),
    s11 = Z_to_bv 64 (b2z so) -> a0 = Z_to_bv 64 (if so then 0 else -1) ->
    s7 = Z_to_bv 64 phi -> s9 = Z_to_bv 64 k -> 0 <= k <= 13 ->
    4096 <= phi -> phi + 50 <= 2 ^ 63 -> length G = 50%nat -> bytes_at rsegs m phi G ->
    (k = 6 -> RcParse.cp_v G 18 = 4 /\ RcParse.cp_v G 19 = 3) ->
    evt rsegs
      (fun ms' => exists ra' a1' a2' a3' a4' a5' s11' : word,
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (e04_wv G))
                       a1' a2' a3' a4' a5' a6 a7 s2 (Z_to_bv 64 (e04_wv G)) s4 s5 s6 s7 s8 s9 s10 s11' t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13da0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13cf4) fc None m (seg_rom rsegs)).
Proof.
  intros HRV ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi k so G -> -> -> -> Hk Hp Hp50 HL HG H6.
  pose proof (u6_bytes_nths m phi G 18 2 HG ltac:(lia)) as HB18. cbn [u6_nths] in HB18.
  pose proof (u6_bytes_nths m phi G 34 6 HG ltac:(lia)) as HB34. cbn [u6_nths] in HB34.
  change (Z.of_nat 18) with 18 in HB18. change (Z.of_nat 34) with 34 in HB34.
  pose proof (u6_rd1 m _ _ 0 (Z_to_bv 8 0) HB18 ltac:(cbn; lia)) as L18.
  pose proof (u6_rd1 m _ _ 1 (Z_to_bv 8 0) HB18 ltac:(cbn; lia)) as L19.
  cbn [nth Z.of_nat] in L18, L19.
  assert (Ersl : RcFrag.bsl G 34 6 = u6_nths G 34 6) by (apply u6_bsl_nths; lia).
  unfold e04_wv. rewrite Ersl. cbn [u6_nths]. unfold RcParse.cp_b, RcParse.cp_z.
  unfold RcParse.cp_v, RcParse.cp_b, RcParse.cp_z in H6.
  pose proof (RcLib.byte_range (nth 18 G (Z_to_bv 8 0))) as R18.
  pose proof (RcLib.byte_range (nth 19 G (Z_to_bv 8 0))) as R19.
  step. step. u6_br false ltac:(destruct so; vm_compute; reflexivity).
  step. step.
  destruct (Z.eq_dec k 6) as [Ek|Ek].
  - subst k. destruct (H6 eq_refl) as [E18 E19].
    u6_br false ltac:(rewrite u6_eqb by lia; u6_zdec).
    step. step. u6_nt false.
    step. step. step. u6_br false ltac:(rewrite u6_eqz by lia; u6_zdec).
    step. step. u6_nt false.
    step. step. step. u6_br false ltac:(rewrite u6_eqz by lia; u6_zdec).
    eapply evt_mono; [eapply (e04_rest HRV); [reflexivity | lia | lia | exact HB18 | exact HB34]|].
    intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & ->). do 7 eexists. reflexivity.
  - u6_br true ltac:(rewrite u6_eqb by lia; u6_zdec).
    eapply evt_mono; [eapply (e04_rest HRV); [reflexivity | lia | lia | exact HB18 | exact HB34]|].
    intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & ->). do 7 eexists. reflexivity.
Qed.

Section E04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HRV : reac_ctrl_headamp_record_verify_contract.

Lemma seg_E04 : forall j, Hat B APIf ra (Inv_U13da0_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13cf4_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HEA & H88) & H10).
  destruct (u6_S_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  destruct (u6_phi_rng B APIf ra empty _ _ _ _ _ _ _ _ HFR HP) as (Hph & Hph2).
  pose proof alloc_ceiling_lt as Hac.
  pose proof HEA as ((HT & H7 & H1 & H0 & H2 & HC) & HIFS).
  pose proof HT as (HLK & HFC & H23 & HPhi & H18).
  pose proof (u6_big_8819 _ _ H88) as Hbig.
  unfold SLOT_K, SLOT_STACK in *.
  assert (Hf : fsp g = g_S g - 1936) by (unfold fsp, SLOT_FRAME; reflexivity).
  eapply (u6_mid B APIf ra empty FF g _ L A regs mem md _ [(0, 0)]); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. cbn [Frame.outside]. split; [lia | exact I].
  - rewrite sl_mkR_of.
    apply (e04_evt HRV) with (phi := phi) (k := t_k (g_in g) j) (so := t_sum_ok (g_in g) j) (G := t_g (g_in g) j).
    + exact H0.
    + exact H10.
    + exact H23.
    + exact H7.
    + apply u6_k_range.
    + lia.
    + lia.
    + apply u6_g_len.
    + apply u6_norm; [exact HMI | apply u6_ba_g; [exact HPhi | exact Hbig]].
    + apply u6_k6.
  - intros ms (ra' & a1' & a2' & a3' & a4' & a5' & s11' & ->).
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity | split; reflexivity].
  - intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
    destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & s11' & HE).
    injection HE; intros; subst.
    assert (AV : u6_av g phi (t_len (g_in g) j) 0 0) by (apply u6_av0; unfold fsp, SLOT_FRAME; lia).
    assert (AI : u6_ai g 0 0) by (apply u6_ai0; unfold fsp, SLOT_FRAME; lia).
    assert (K : u6_kT regs regs') by (unfold u6_kT; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [exact (u6_EQ_keep g j phi regs regs' mem m' 0 0 HEA H88 K MU AV AI)|].
    split; unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity.
Qed.

End E04.

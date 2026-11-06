(* Segment E04 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13af0, 0x13b60], K13af0 -> K13b64 (call
   reac_ctrl_headamp_record_verify at 0x13b60). Branch #71 (CSV: a0 = sum_ok - 1), #72 and #73 (struct P5.4: k = 6
   gives Φ[18] = 4, Φ[19] = 3) are not taken; the record sum loop (head 0x13b40, 6 turns) gives s0 = want_v.
   libreac v1.9.0 (table 5a S_E04, CHANGED: register): sum_ok is s1 (0x13af0 `addi s1,s1,-1`, 0x13af4 `bne a0,s1`;
   v1.8 s0), so e04_evt's premise is s1 = b2z sum_ok and its exit state leaves s1 (= sum_ok - 1) open; want_v is
   still s0 (0x13b1c `li s0,-1`, 0x13b54-0x13b58); pcs + 0x30; K13b64's EQ keeps VCm (SlotInv.v). rule 24: no
   function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv
  reac_ctrl_headamp_record_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcParse RcLeaf RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b7.
Import ListNotations.
Open Scope Z_scope.

(* andi 127; seqz; addi -1 of the record sum S. *)
Lemma e04_s0 : forall S, 0 <= S < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 S)) 127)) 1) + -1) =
  Z_to_bv 64 (if S mod 128 =? 0 then 0 else -1).
Proof.
  intros S HS. rewrite (MState.unsigned_lit S) by lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
  pose proof (Z.mod_pos_bound S 128 ltac:(lia)) as HM.
  unfold v_sltiu. rewrite (MState.unsigned_lit (S mod 128)) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec (S mod 128) 1); destruct (Z.eqb_spec (S mod 128) 0); try lia;
    rewrite MState.unsigned_lit by lia; f_equal; lia.
Qed.

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

(* 0x13b34 -> 0x13b5c: the inline record_sum_closes over Φ[34 .. 40). *)
Lemma e04_sum :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (r0 r1 r2 r3 r4 r5 : byte),
    s5 = Z_to_bv 64 phi -> 0 <= phi -> phi + 40 < 2 ^ 64 ->
    bytes_at rsegs m (phi + 34) [r0; r1; r2; r3; r4; r5] ->
    evt rsegs
      (fun ms' => exists a0' a1' a2' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2
                       (Z_to_bv 64 (if RcLeaf.rsum [r0; r1; r2; r3; r4; r5] =? 0 then 0 else -1)) s1
                       a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13b5c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b34) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi r0 r1 r2 r3 r4 r5 -> H0 H40 HR.
  pose proof (b7_rd1 m _ _ 0 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R0.
  pose proof (b7_rd1 m _ _ 1 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R1.
  pose proof (b7_rd1 m _ _ 2 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R2.
  pose proof (b7_rd1 m _ _ 3 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R3.
  pose proof (b7_rd1 m _ _ 4 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R4.
  pose proof (b7_rd1 m _ _ 5 (Z_to_bv 8 0) HR ltac:(cbn; lia)) as R5.
  cbn [nth Z.of_nat] in R0, R1, R2, R3, R4, R5.
  pose proof (b7_byte_range r0). pose proof (b7_byte_range r1). pose proof (b7_byte_range r2).
  pose proof (b7_byte_range r3). pose proof (b7_byte_range r4). pose proof (b7_byte_range r5).
  step. step. step.
  step. step. step. step. b7_br true ltac:(rewrite b7_eqb_small by lia; b7_zdec).
  step. step. step. step. b7_br true ltac:(rewrite b7_eqb_small by lia; b7_zdec).
  step. step. step. step. b7_br true ltac:(rewrite b7_eqb_small by lia; b7_zdec).
  step. step. step. step. b7_br true ltac:(rewrite b7_eqb_small by lia; b7_zdec).
  step. step. step. step. b7_br true ltac:(rewrite b7_eqb_small by lia; b7_zdec).
  step. step. step. step. b7_br false ltac:(rewrite b7_eqb_small by lia; b7_zdec).
  step. step. step.
  apply evt_done. rewrite !b7_uzxb. rewrite e04_s0 by lia. do 4 eexists. reflexivity.
Qed.

(* 0x13b5c -> 0x13b64: mv a0,s5; jal reac_ctrl_headamp_record_verify (HRV C1.2, C1.3). *)
Lemma e04_tail : reac_ctrl_headamp_record_verify_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (b0 b1 : byte) (rec : list byte),
    s5 = Z_to_bv 64 phi -> 0 < phi -> phi + 40 <= 2 ^ 64 ->
    bytes_at rsegs m (phi + 18) [b0; b1] -> bytes_at rsegs m (phi + 34) rec -> length rec = 6%nat ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR (Z_to_bv 64 0x13b64) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (if RcLeaf.hv b0 b1 rec then 0 else -1))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13b64) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b5c) fc None m (seg_rom rsegs)).
Proof.
  intros HRV ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi b0 b1 rec -> Hp Hp40 HB HR Hl.
  step. step.
  eapply evt_cut.
  { eapply HRV with (p := phi) (b0 := b0) (b1 := b1) (rec := rec); [| lia | lia | exact HB | exact Hl | exact HR].
    first [reflexivity | f_equal; lia]. }
  intros ms' (a1' & a2' & a3' & ->).
  rewrite (MState.ret_pc_even 0x13b64) by (first [reflexivity | lia]).
  apply evt_done. exists a1', a2', a3'. reflexivity.
Qed.

(* 0x13af0 -> 0x13b64 for a frame whose first 50 bytes G are at Φ, kind k, sum_ok so (in s1). *)
Lemma e04_evt : reac_ctrl_headamp_record_verify_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi k : Z) (so : bool) (G : list byte),
    s1 = Z_to_bv 64 (b2z so) -> a0 = Z_to_bv 64 (if so then 0 else -1) ->
    s9 = Z_to_bv 64 (phi + 18) -> s5 = Z_to_bv 64 phi -> s7 = Z_to_bv 64 k -> 0 <= k <= 13 ->
    0 < phi -> phi + 50 < 2 ^ 64 -> length G = 50%nat -> bytes_at rsegs m phi G ->
    (k = 6 -> RcParse.cp_v G 18 = 4 /\ RcParse.cp_v G 19 = 3) ->
    evt rsegs
      (fun ms' => exists ra' s1' a1' a2' a3' : word,
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 (Z_to_bv 64 (e04_wv G)) s1' (Z_to_bv 64 (e04_wv G))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13b64) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13af0) fc None m (seg_rom rsegs)).
Proof.
  intros HRV ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi k so G -> -> -> -> -> Hk Hp Hp50 HL HG H6.
  pose proof (b7_bytes_nths m phi G 18 2 HG ltac:(lia)) as HB18. cbn [b7_nths] in HB18.
  pose proof (b7_bytes_nths m phi G 34 6 HG ltac:(lia)) as HB34. cbn [b7_nths] in HB34.
  change (Z.of_nat 18) with 18 in HB18. change (Z.of_nat 34) with 34 in HB34.
  pose proof (b7_rd1 m _ _ 0 (Z_to_bv 8 0) HB18 ltac:(cbn; lia)) as L18.
  pose proof (b7_rd1 m _ _ 1 (Z_to_bv 8 0) HB18 ltac:(cbn; lia)) as L19.
  cbn [nth Z.of_nat] in L18, L19.
  assert (Ersl : RcFrag.bsl G 34 6 = b7_nths G 34 6) by (apply b7_bsl_nths; lia).
  unfold e04_wv. rewrite Ersl. cbn [b7_nths]. unfold RcParse.cp_b, RcParse.cp_z.
  unfold RcParse.cp_v, RcParse.cp_b, RcParse.cp_z in H6.
  pose proof (b7_byte_range (nth 18 G (Z_to_bv 8 0))) as R18.
  pose proof (b7_byte_range (nth 19 G (Z_to_bv 8 0))) as R19.
  step. step. b7_br false ltac:(destruct so; vm_compute; reflexivity).
  step. step. step.
  destruct (Z.eq_dec k 6) as [Ek|Ek].
  - subst k. destruct (H6 eq_refl) as [E18 E19].
    b7_br false ltac:(rewrite b7_eqb_small by lia; b7_zdec).
    step. step. b7_br false ltac:(unfold zxb; rewrite b7_eqb_small by lia; b7_zdec).
    step. step. step. b7_br false ltac:(unfold zxb; rewrite b7_eqb_small by lia; b7_zdec).
    step.
    eapply evt_cut; [eapply e04_sum; [reflexivity | lia | lia | exact HB34]|].
    intros ms' (a0' & a1' & a2' & a3' & ->).
    eapply evt_mono; [eapply (e04_tail HRV); [reflexivity | lia | lia | exact HB18 | exact HB34 | reflexivity]|].
    intros ms' (a1'' & a2'' & a3'' & ->).
    exists (Z_to_bv 64 0x13b64). eexists. exists a1'', a2'', a3''. rewrite (e04_hv _ _ _ E18 E19). reflexivity.
  - b7_br true ltac:(rewrite b7_eqb_small by lia; b7_zdec).
    step. step. step.
    destruct (Z.eq_dec (bv_unsigned (nth 18 G (Z_to_bv 8 0))) 4) as [E18|E18].
    + b7_br false ltac:(unfold zxb; rewrite b7_eqb_small by lia; b7_zdec).
      step. step. step.
      destruct (Z.eq_dec (bv_unsigned (nth 19 G (Z_to_bv 8 0))) 3) as [E19|E19].
      * b7_br false ltac:(unfold zxb; rewrite b7_eqb_small by lia; b7_zdec).
        eapply evt_cut; [eapply e04_sum; [reflexivity | lia | lia | exact HB34]|].
        intros ms' (a0' & a1' & a2' & a3' & ->).
        eapply evt_mono; [eapply (e04_tail HRV); [reflexivity | lia | lia | exact HB18 | exact HB34 | reflexivity]|].
        intros ms' (a1'' & a2'' & a3'' & ->).
        exists (Z_to_bv 64 0x13b64). eexists. exists a1'', a2'', a3''. rewrite (e04_hv _ _ _ E18 E19). reflexivity.
      * b7_br true ltac:(unfold zxb; rewrite b7_eqb_small by lia; b7_zdec).
        eapply evt_mono; [eapply (e04_tail HRV); [reflexivity | lia | lia | exact HB18 | exact HB34 | reflexivity]|].
        intros ms' (a1'' & a2'' & a3'' & ->).
        exists (Z_to_bv 64 0x13b64). eexists. exists a1'', a2'', a3''. rewrite (e04_hv1 _ _ _ E19). reflexivity.
    + b7_br true ltac:(unfold zxb; rewrite b7_eqb_small by lia; b7_zdec).
      eapply evt_mono; [eapply (e04_tail HRV); [reflexivity | lia | lia | exact HB18 | exact HB34 | reflexivity]|].
      intros ms' (a1'' & a2'' & a3'' & ->).
      exists (Z_to_bv 64 0x13b64). eexists. exists a1'', a2'', a3''. rewrite (e04_hv0 _ _ _ E18). reflexivity.
Qed.

Section E04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HRV : reac_ctrl_headamp_record_verify_contract.

Lemma seg_E04 : forall j, Hat B APIf ra (Inv_K13b64_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13af0_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HEB & H10)).
  pose proof HEB as ((HFT & H7 & H9 & H0 & H2 & HVC & HIFS) & H88).
  pose proof HFT as (Hj & H26 & HFC & H21 & Hphi & HOUR & HM7).
  pose proof (b7_big_8819 _ _ H88) as Hbig.
  destruct (b7_phi_bnd B APIf ra empty g _ L A regs mem md phi _ HFR HP ltac:(lia)) as (Hp1 & Hp2).
  destruct (b7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  pose proof alloc_ceiling_value as Hac.
  assert (HEQ : EQ g j phi regs mem).
  { split; [exact HFT|]. split; [exact H7|]. split; [exact H2|]. split; [exact (proj2 HVC)|].
    split; [exact HIFS | exact H88]. }
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (e04_evt HRV) with (phi := phi) (k := t_k (g_in g) j) (so := t_sum_ok (g_in g) j) (G := t_g (g_in g) j).
    + exact H0.
    + exact H10.
    + exact H9.
    + exact H21.
    + exact H7.
    + apply b7_k_range.
    + lia.
    + lia.
    + apply b7_g_length.
    + apply b7_norm; [exact HMI | apply b7_g_bytes; [exact Hphi | exact Hbig]].
    + apply b7_k6.
  - intros ms (ra' & s1' & a1' & a2' & a3' & ->). do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists []. split; [apply munch_refl|]. split; [apply wmono_refl|]. intros x _ O. exfalso. apply O. exact I.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (ra' & s1' & a1' & a2' & a3' & HE). injection HE; intros; subst.
    apply H. unfold Inv_K13b64_at, FCUT, CUTST. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (MT0 : MT [] mem m') by exact (b7_mt [] mem (normalize rsegs mem) m' HMI (munch_refl _ _) Hrel).
    split; [|split; [|split]].
    + apply (b7_EQ g j phi regs mem regs' m' []); [exact HEQ | exact MT0 | apply b7_DJE_nil |].
      unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
    + apply (b7_rg regs); [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity | exact H9].
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End E04.

(* Segment Q05 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13e28, 0x13ed0], U13e34 (v1.9 pc
   0x13e28) -> U13ee0 (v1.9 pc 0x13ed4) (r_p = 0). T55 (blk = Φ + 18 = s8 is not 0; v1.8 s7), then the port-slot
   loop (head 0x13e58, a6 = 12 - i, 12 turns, C5.5) over blk[8 .. 20): it counts the codes {00, 02}, {01}, {03} and
   keeps the first code >= 4 (known_slot(c) is c <u 4, AF4). In each turn T56 (blk + 8 + i does not wrap: AF9,
   t2 = 12) and T57-T59 (no count overflows int: CNT) are not taken. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u7 Tac_u7q.
Import ListNotations.
Open Scope Z_scope.

(* ---- One code c of the loop (AF4): the three count increments and the first unknown code ---- *)

Lemma q05_in : forall c : byte,
  bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (zxb c)) 253)) 1) =
  if RcLeaf.is_in (bv_unsigned c) then 1 else 0.
Proof.
  intros c. rewrite u7q_uzxb. pose proof (u7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (u7q_all (fun u => Z.eqb (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land u 253)) 1))
                                       (if RcLeaf.is_in u then 1 else 0)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma q05_out : forall c : byte,
  bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + -1)) 1) = if RcLeaf.is_out (bv_unsigned c) then 1 else 0.
Proof.
  intros c. rewrite u7q_uzxb. pose proof (u7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (u7q_all (fun u => Z.eqb (bv_unsigned (v_sltiu (Z_to_bv 64 (u + -1)) 1))
                                       (if RcLeaf.is_out u then 1 else 0)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma q05_emp : forall c : byte,
  bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + -3)) 1) = if is_empty (bv_unsigned c) then 1 else 0.
Proof.
  intros c. rewrite u7q_uzxb. pose proof (u7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (u7q_all (fun u => Z.eqb (bv_unsigned (v_sltiu (Z_to_bv 64 (u + -3)) 1))
                                       (if is_empty u then 1 else 0)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma q05_snez : forall f, 0 <= f < 256 ->
  bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 f)) 255))) =
  if f =? 0 then 0 else 1.
Proof.
  intros f R.
  pose proof (u7q_all (fun f => Z.eqb (bv_unsigned (v_sltu (Z_to_bv 64 0)
                                   (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 f)) 255))))
                                       (if f =? 0 then 0 else 1)) ltac:(vm_compute; reflexivity) f R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma q05_known : forall c : byte,
  bv_unsigned (v_sltiu (zxb c) 4) = if 4 <=? bv_unsigned c then 0 else 1.
Proof.
  intros c. unfold zxb. pose proof (u7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (u7q_all (fun u => Z.eqb (bv_unsigned (v_sltiu (Z_to_bv 64 u) 4))
                                       (if 4 <=? u then 0 else 1)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

(* beqz t0 at 0x13ebc with t0 = (zext.b first != 0) | (c <u 4). *)
Lemma q05_br : forall f (c : byte), 0 <= f < 256 ->
  bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 f)) 255))))
                             (bv_unsigned (v_sltiu (zxb c) 4))))
         (Z_to_bv 64 0) = (f =? 0) && (4 <=? bv_unsigned c).
Proof.
  intros f c Hf. rewrite (q05_snez f Hf), q05_known.
  destruct (f =? 0), (4 <=? bv_unsigned c); vm_compute; reflexivity.
Qed.

Definition q05_f (f u : Z) : Z := if (f =? 0) && (4 <=? u) then u else f.

Lemma q05_first_step : forall bs i,
  q05_f (RcPorts.pu_first bs i) (bv_unsigned (nth (8 + i) bs (Z_to_bv 8 0))) = RcPorts.pu_first bs (S i).
Proof.
  intros bs i. cbn [RcPorts.pu_first]. unfold q05_f, RcPorts.rc_u8.
  destruct (u7_first_spec bs i) as ((E1 & E2) & _).
  destruct (Z.eqb_spec (RcPorts.pu_first bs i) 0) as [F0|F0];
    destruct (Z.eqb_spec (RcPorts.pu_nunk bs i) 0) as [N0|N0]; cbn [andb]; try reflexivity; exfalso; tauto.
Qed.

Ltac q05_flag := match goal with |- context [if ?b then _ else _] => destruct b end; lia.

(* 0x13e58 -> 0x13ed0: one turn on the code c at A4 (a5 = A5 the room, a6 = A6 the turns left), with the increments
   BI, BO, BE of the counts NI, NO, NE and the first unknown code PF. *)
Lemma q05_body :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A4 A5 A6 NI NO NE PF BI BO BE : Z) (c : byte),
    t2 = Z_to_bv 64 12 -> a4 = Z_to_bv 64 A4 -> a5 = Z_to_bv 64 A5 -> a6 = Z_to_bv 64 A6 ->
    a1 = Z_to_bv 64 NI -> a0 = Z_to_bv 64 NO -> a2 = Z_to_bv 64 NE -> a3 = Z_to_bv 64 PF ->
    ov_read_bytes rsegs m (Z_to_bv 64 A4) 1 = Some [c] ->
    0 <= A5 < 2 ^ 64 -> 0 <= A6 < 2 ^ 64 -> 12 < A5 + A6 < 2 ^ 64 ->
    0 <= NI <= 12 -> 0 <= NO <= 12 -> 0 <= NE <= 12 -> 0 <= PF < 256 ->
    bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (zxb c)) 253)) 1) = BI -> 0 <= BI <= 1 ->
    bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + -1)) 1) = BO -> 0 <= BO <= 1 ->
    bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + -3)) 1) = BE -> 0 <= BE <= 1 ->
    evt rsegs
      (fun ms' => exists t0' t1' : word,
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (Z_to_bv 64 (NO + BO)) (Z_to_bv 64 (NI + BI))
                       (Z_to_bv 64 (NE + BE)) (Z_to_bv 64 (q05_f PF (bv_unsigned c))) (Z_to_bv 64 (A4 + 1)) a5
                       (Z_to_bv 64 (A6 + -1)) (Z_to_bv 64 (q05_f PF (bv_unsigned c)))
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13ed0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13e58) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A4 A5 A6 NI NO NE PF BI BO BE c -> -> -> -> -> -> -> -> R H5 H6 H56 HI HO HE HF EI RI EO RO EE RE.
  (* T56 *)
  step. step. u7_br false ltac:(u7_bool).
  (* T57: {00, 02} *)
  step. step. step. step. step. step.
  rewrite EI, (u7q_sx NI) by lia. rewrite (u7q_addw NI BI) by lia.
  step. u7_br false ltac:(u7_bool).
  (* T58: {01} *)
  step. step. step. step. step.
  rewrite EO, (u7q_sx NO) by lia. rewrite (u7q_addw NO BO) by lia.
  step. u7_br false ltac:(u7_bool).
  (* T59: {03} *)
  step. step. step. step. step.
  rewrite EE, (u7q_sx NE) by lia. rewrite (u7q_addw NE BE) by lia.
  step. u7_br false ltac:(u7_bool).
  (* the first code >= 4 *)
  step. step. step. step. step.
  destruct ((PF =? 0) && (4 <=? bv_unsigned c)) eqn:EB.
  - u7_br true ltac:(rewrite (q05_br PF c HF); exact EB).
    step. step. step.
    apply evt_done. do 2 eexists. unfold q05_f. rewrite EB. reflexivity.
  - u7_br false ltac:(rewrite (q05_br PF c HF); exact EB).
    step. step. step. step.
    apply evt_done. do 2 eexists. unfold q05_f. rewrite EB. reflexivity.
Qed.

(* The loop from turn i (head 0x13e58, k = 12 - i turns left) to its exit 0x13ed4, for the 20 block bytes bs at blk:
   a1 / a0 / a2 = the counts of {00, 02} / {01} / {03} among blk[8 .. 8 + i), a3 = the first code >= 4 among them
   (or 0), a4 = blk + 8 + i, a5 = 2^64 - 8 - blk (AF9), a6 = k, t2 = 12. *)
Lemma q05_loop : forall (bs : list byte) (blk : Z) (k i : nat)
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (1 <= k)%nat -> (i + k = 12)%nat -> 4096 <= blk -> blk + 20 < 2 ^ 63 ->
  t2 = Z_to_bv 64 12 -> a4 = Z_to_bv 64 (blk + 8 + Z.of_nat i) ->
  a5 = Z_to_bv 64 (18446744073709551608 - blk) -> a6 = Z_to_bv 64 (Z.of_nat k) ->
  a1 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in bs i) -> a0 = Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out bs i) ->
  a2 = Z_to_bv 64 (RcLeaf.cnt is_empty bs i) -> a3 = Z_to_bv 64 (RcPorts.pu_first bs i) ->
  (forall j, (j < 12)%nat ->
     ov_read_bytes rsegs m (Z_to_bv 64 (blk + 8 + Z.of_nat j)) 1 = Some [nth (8 + j) bs (Z_to_bv 8 0)]) ->
  evt rsegs
    (fun ms' => exists t0' t1' a3' a4' a6' : word,
       ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out bs 12))
                     (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in bs 12)) (Z_to_bv 64 (RcLeaf.cnt is_empty bs 12)) a3' a4' a5
                     a6' (Z_to_bv 64 (RcPorts.pu_first bs 12)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13ed4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e58) fc None m (seg_rom rsegs)).
Proof.
  intros bs blk k. induction k as [|k IH];
    intros i ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      Hk Hik Hb0 Hb1 E7 E14 E15 E16 E11 E10 E12 E13 Hrd; [lia|].
  subst t2 a4 a5 a6 a1 a0 a2 a3.
  pose proof (u7_cnt_range RcLeaf.is_in bs i) as RI.
  pose proof (u7_cnt_range RcLeaf.is_out bs i) as RO.
  pose proof (u7_cnt_range is_empty bs i) as RE.
  destruct (u7_first_spec bs i) as (_ & RF).
  eapply evt_cut.
  { eapply q05_body with (c := nth (8 + i) bs (Z_to_bv 8 0));
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |
       exact (Hrd i ltac:(lia)) | lia | lia | lia | lia | lia | lia | exact RF |
       apply q05_in | q05_flag | apply q05_out | q05_flag | apply q05_emp | q05_flag]. }
  intros ms' (t0' & t1' & ->).
  rewrite q05_first_step.
  rewrite <- (u7q_cnt_S RcLeaf.is_in bs i), <- (u7q_cnt_S RcLeaf.is_out bs i), <- (u7q_cnt_S is_empty bs i).
  step.
  destruct (Nat.eq_dec k 0) as [-> | Hk0].
  - u7_br false ltac:(u7_bool).
    assert (Ei : i = 11%nat) by lia. subst i.
    apply evt_done. do 5 eexists. reflexivity.
  - u7_br true ltac:(u7_bool).
    apply (IH (S i)); [lia | lia | lia | lia | reflexivity | f_equal; lia | reflexivity | f_equal; lia |
                       reflexivity | reflexivity | reflexivity | reflexivity | exact Hrd].
Qed.

(* 0x13e28 -> 0x13ed4 with s8 = blk and bs blk's 20 bytes. *)
Lemma q05_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (blk : Z) (bs : list byte),
    s8 = Z_to_bv 64 blk -> t2 = Z_to_bv 64 12 -> 4096 <= blk -> blk + 20 < 2 ^ 63 ->
    (forall j, (j < 12)%nat ->
       ov_read_bytes rsegs m (Z_to_bv 64 (blk + 8 + Z.of_nat j)) 1 = Some [nth (8 + j) bs (Z_to_bv 8 0)]) ->
    evt rsegs
      (fun ms' => exists t0' t1' a3' a4' a5' a6' : word,
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (Z_to_bv 64 (RcLeaf.n_out bs)) (Z_to_bv 64 (RcLeaf.n_in bs))
                       (Z_to_bv 64 (RcLeaf.cnt is_empty bs 12)) a3' a4' a5' a6' (Z_to_bv 64 (RcPorts.pu_first bs 12))
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13ed4) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13e28) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m blk bs -> -> Hb0 Hb1 Hrd.
  (* T55 *)
  step. u7_br false ltac:(u7_bool).
  step. step. step. step. step. step. step. step. step. step. step.
  rewrite (u7q_room blk) by lia.
  eapply evt_mono.
  { eapply (q05_loop bs blk 12 0);
      [lia | lia | lia | lia | reflexivity | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity |
       reflexivity | reflexivity | exact Hrd]. }
  intros ms' (t0' & t1' & a3' & a4' & a6' & ->). unfold RcLeaf.n_out, RcLeaf.n_in. do 6 eexists. reflexivity.
Qed.

Section Q05.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_Q05 : forall j : nat, Hat B APIf ra (Inv_U13ed4_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13e28_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HQB & H26 & Hrp & Hunk & HT2)).
  pose proof HQB as (HEQ & H27 & HPO & H1792).
  pose proof HEQ as (HFT & H7 & H2 & HVC & HIFS & H88).
  pose proof HFT as (HLK & HFC & H23 & Hphi & H18).
  pose proof HVC as (H24 & H16 & HB).
  pose proof (u7_big_8819 _ _ H88) as Hbig.
  rewrite (u7_big_true _ _ H88) in H24.
  destruct (u7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HSa & HSb & HSc & Hsp & HMI).
  destruct (u7_phi_bnd B APIf ra empty g _ L A regs mem md phi _ HFR HP ltac:(lia)) as (Hp1 & Hp2).
  set (pbs := t_pbs (g_in g) j) in *.
  assert (Hpbs : bytes_at rsegs (normalize rsegs mem) (phi + 18) pbs).
  { apply u7_norm; [exact HMI|]. apply u7_pbs_bytes. apply u7_g_bytes; [exact Hphi | exact Hbig]. }
  assert (HR : forall k, (k < 12)%nat ->
            ov_read_bytes rsegs (normalize rsegs mem) (Z_to_bv 64 (phi + 18 + 8 + Z.of_nat k)) 1 =
            Some [nth (8 + k) pbs (Z_to_bv 8 0)]).
  { intros k Hk.
    pose proof (u7_rd1 _ _ _ (8 + k) (Z_to_bv 8 0) Hpbs ltac:(unfold pbs; rewrite u7_pbs_length; lia)) as E.
    replace (phi + 18 + Z.of_nat (8 + k)) with (phi + 18 + 8 + Z.of_nat k) in E by lia. exact E. }
  eapply (u7_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x _ O. exfalso. apply O. exact I.
  - rewrite sl_mkR_of.
    apply q05_evt with (blk := phi + 18) (bs := pbs).
    + exact H24.
    + exact HT2.
    + lia.
    + lia.
    + exact HR.
  - intros ms (t0' & t1' & a3' & a4' & a5' & a6' & ->).
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (t0' & t1' & a3' & a4' & a5' & a6' & HE).
    destruct (u7_MS_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE) as (ER & Epc & Em). subst R pc' m0'.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + apply (u7_QB g j phi regs mem regs' m' [] HQB (u7_mt _ _ _ MU') (u7_DJE_nil g j phi) (u7_DJQ_nil g)).
      * unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). exact H26.
    + exact Hrp.
    + exact Hunk.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End Q05.

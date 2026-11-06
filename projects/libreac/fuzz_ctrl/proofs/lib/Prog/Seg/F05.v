(* Segment F05 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x1370c, 0x13730] and [0x13768, 0x137c4],
   K1370c -> K1374c (1 <= len <= 49) and K137c8 (len >= 50: is_8819 from Φ[12], Φ[13]; the block sum of Φ[18 .. 50)
   in a 32-turn loop; TF from sum_ok, Φ[16], Φ[17]; #42 not taken by struct P5.1). *)
(* libreac v1.9.0 (CHANGED register, segment table 5a S_F05): v1.8 [0x13700, 0x13724] and [0x1375c, 0x137b8],
   K13700 -> K13740 / K137bc, every pc + 12 (loop head 0x13778 -> 0x13784). Registers: is_8819 in s0 (0x1372c
   `seqz s0,a0`, 0x13768 `li s0,0`; v1.8 s11), sum_ok in s1 (0x1379c `seqz s1,a0`; v1.8 s0); type_filler stored at
   sp+24 (0x137c0; v1.8 sp+48); the parse result p at sp+1752. Same instructions otherwise. Statement kept on the
   renamed cuts. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b4.
Import ListNotations.
Open Scope Z_scope.

(* ---- Values the code computes ---- *)

Lemma f05_seqz0 : forall x, 0 <= x < 2 ^ 64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 (b2z (x =? 0)).
Proof.
  intros x Hx. unfold v_sltiu. rewrite MState.unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec x 0) as [E|E]; [subst; reflexivity|].
  rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity.
Qed.

(* seqz (Φ[13] - 25) *)
Lemma f05_seqz25 : forall b : byte,
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + -25)) 1 = Z_to_bv 64 (b2z (bv_unsigned b =? 25)).
Proof.
  intros b. unfold v_sltiu. rewrite RcIdentLib.zxb_u. pose proof (b4_byte_nn b) as Hb.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite (Z.mod_small 1) by lia.
  destruct (Z.ltb_spec ((bv_unsigned b + -25) mod 18446744073709551616) 1) as [H|H];
    destruct (Z.eqb_spec (bv_unsigned b) 25) as [E|E]; try reflexivity; exfalso.
  - apply E. lia.
  - rewrite E in H. cbn in H. lia.
Qed.

(* and s6, (len < 50) - 1, s9 with len >= 50 *)
Lemma f05_and : forall len x, 50 <= len < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 len) 50) + -1)))
                     (bv_unsigned (Z_to_bv 64 x))) = Z_to_bv 64 x.
Proof.
  intros len x Hl Hx. unfold v_sltiu. rewrite (MState.unsigned_lit len) by lia.
  change (bv_wrap 64 50) with 50. rewrite (proj2 (Z.ltb_ge len 50)) by lia.
  rewrite (MState.unsigned_lit x) by lia.
  change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1))) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* seqz (zext.b sum) *)
Lemma f05_s0 : forall S, 0 <= S < 2 ^ 64 ->
  v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 S)) 255)) 1 = Z_to_bv 64 (b2z (S mod 256 =? 0)).
Proof.
  intros S HS. rewrite MState.unsigned_lit by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  change (2 ^ 8) with 256. apply f05_seqz0. pose proof (Z.mod_pos_bound S 256 ltac:(lia)). lia.
Qed.

Lemma f05_s1 : forall b : byte, v_sltiu (zxb b) 1 = Z_to_bv 64 (b2z (bv_unsigned b =? 0)).
Proof. intros b. unfold zxb. apply f05_seqz0. pose proof (b4_byte_nn b). lia. Qed.

Lemma f05_lor : forall c1 c2 : bool,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (b2z c1))) (bv_unsigned (Z_to_bv 64 (b2z c2)))) =
  Z_to_bv 64 (b2z (c1 || c2)).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma f05_snez : forall k, 0 <= k < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 k) = Z_to_bv 64 (b2z (negb (k =? 0))).
Proof.
  intros k Hk. unfold v_sltu, c_ltu. rewrite b4_ltu by lia.
  destruct (Z.eqb_spec k 0) as [E|E]; [subst; reflexivity|].
  rewrite (proj2 (Z.ltb_lt 0 k)) by lia. reflexivity.
Qed.

Lemma f05_bne_same : forall x : word, negb (bv_eqb x x) = false.
Proof. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

(* One unfolding of psum, by rewriting (no conversion unfolds psum at a numeral). *)
Lemma f05_psum_S : forall bs i,
  RcModel.psum bs (S i) = RcModel.psum bs i + bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof. reflexivity. Qed.

Lemma f05_blocksum : forall bs, RcModel.psum bs 32 mod 256 = RcModel.blocksum bs.
Proof. intros bs. unfold RcModel.blocksum. reflexivity. Qed.

Lemma f05_psum_rng : forall bs i, 0 <= RcModel.psum bs i <= 255 * Z.of_nat i.
Proof.
  intros bs i. induction i as [|i IH]; cbn [RcModel.psum]; [lia|].
  pose proof (b4_byte_nn (nth i bs (Z_to_bv 8 0))). lia.
Qed.

Lemma f05_nth_skipn : forall m (l : list byte) n d, nth n (skipn m l) d = nth (m + n) l d.
Proof. induction m as [|m IH]; intros [|x l] n d; cbn; try reflexivity; [destruct n; reflexivity | apply IH]. Qed.

(* ---- The run ---- *)

(* len <= 49: s7 = k, to K1374c. *)
Lemma f05a_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k len : Z),
    a0 = Z_to_bv 64 k -> s4 = Z_to_bv 64 len -> 0 <= len <= 49 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                                (Z_to_bv 64 k) s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x1374c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1370c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m k len E0 E4 Hl.
  subst a0 s4.
  step. step. step.
  if_true_by (f_equal negb (eq_trans (b4_ltu 49 len ltac:(lia) ltac:(lia)) (proj2 (Z.ltb_ge 49 len) ltac:(lia)))).
  apply evt_done. reflexivity.
Qed.

(* len >= 50: 0x1370c -> loop head 0x13784 with a0 = 0, a1 = Φ + 18, a2 = Φ + 50, s6 = Φ + 18, s7 = k,
   s0 = is_8819 (Φ[12] = 0x88 and Φ[13] = 0x19). *)
Lemma f05h_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k len phi : Z) (bs : list byte) (b12 b13 : byte),
    a0 = Z_to_bv 64 k -> s4 = Z_to_bv 64 len -> s5 = Z_to_bv 64 phi -> s9 = Z_to_bv 64 (phi + 18) ->
    50 <= len < 2 ^ 20 -> 0 < phi -> phi + 50 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (phi + 12)) 1 = Some [b12] ->
    ov_read_bytes rsegs m (wa (phi + 13)) 1 = Some [b13] ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2
                                (Z_to_bv 64 (b2z ((bv_unsigned b12 =? 136) && (bv_unsigned b13 =? 25)))) s1
                                (Z_to_bv 64 (RcModel.psum bs 0))
                                (Z_to_bv 64 (phi + 18 + Z.of_nat 0)) (Z_to_bv 64 (phi + 50)) a3 a4 a5 a6 a7
                                s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 k) s8 s9 s10 s11
                                t3 t4 t5 t6)
                           F (Z_to_bv 64 0x13784) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1370c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m k len phi bs b12 b13 E0 E4 E5 E9 Hl Hp Hpl HR12 HR13.
  subst a0 s4 s5 s9.
  pose proof (b4_byte_nn b12) as Hb12. pose proof (b4_byte_nn b13) as Hb13.
  replace (phi + 18 + Z.of_nat 0) with (phi + 18) by lia.
  step. step. step.
  if_false_by (f_equal negb (eq_trans (b4_ltu 49 len ltac:(lia) ltac:(lia)) (proj2 (Z.ltb_lt 49 len) ltac:(lia)))).
  step. step. step.
  destruct (Z.eqb_spec (bv_unsigned b12) 136) as [E12|E12].
  - if_false_by (f_equal negb (eq_trans (b4_eqb (bv_unsigned b12) 136 ltac:(lia) ltac:(lia))
                                        (proj2 (Z.eqb_eq _ _) E12))).
    step. step. step. step. step. step. step. step. step. step.
    rewrite f05_seqz25. rewrite (f05_and len (phi + 18)) by lia.
    replace (bv_unsigned b12 =? 136) with true by (symmetry; apply Z.eqb_eq; exact E12). cbn [andb].
    apply evt_done. reflexivity.
  - if_true_by (f_equal negb (eq_trans (b4_eqb (bv_unsigned b12) 136 ltac:(lia) ltac:(lia))
                                       (proj2 (Z.eqb_neq _ _) E12))).
    step. step. step. step. step. step. step.
    rewrite (f05_and len (phi + 18)) by lia.
    replace (bv_unsigned b12 =? 136) with false by (symmetry; apply Z.eqb_neq; exact E12). cbn [andb].
    apply evt_done. reflexivity.
Qed.

(* The block sum loop: from turn i (a0 = psum bs i, a1 = Φ + 18 + i) to the exit 0x13794 (a0 = psum bs 32). *)
Lemma f05_loop : forall (bs : list byte) (phi : Z) (k i : nat)
  (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (1 <= k)%nat -> (i + k = 32)%nat -> 0 <= phi -> phi + 50 < 2 ^ 64 ->
  (forall j, (j < 32)%nat -> ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
  evt rsegs
    (fun ms' => exists a3', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (RcModel.psum bs 32))
                   (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 (phi + 50)) a3' a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x13794) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (RcModel.psum bs i)) (Z_to_bv 64 (phi + 18 + Z.of_nat i))
             (Z_to_bv 64 (phi + 50)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13784) fc None m (seg_rom rsegs)).
Proof.
  intros bs phi k. induction k as [|k IH];
    intros i ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      Hk Hik Hphi Hhi Hrd; [lia|].
  pose proof (Hrd i ltac:(lia)) as HR.
  pose proof (f05_psum_rng bs i) as Hps.
  step. step. step. step.
  rewrite RcIdentLib.zxb_u. rewrite b4_eqb by lia.
  destruct (Nat.eq_dec k 0) as [-> | Hk0].
  - assert (Ei : i = 31%nat) by lia. subst i.
    replace (phi + 18 + Z.of_nat 31 + 1 =? phi + 50) with true by (symmetry; apply Z.eqb_eq; lia).
    cbv beta iota delta [negb].
    replace (phi + 18 + Z.of_nat 31 + 1) with (phi + 50) by lia.
    rewrite <- (f05_psum_S bs 31).
    apply evt_done. eexists. reflexivity.
  - replace (phi + 18 + Z.of_nat i + 1 =? phi + 50) with false by (symmetry; apply Z.eqb_neq; lia).
    cbv beta iota delta [negb].
    replace (phi + 18 + Z.of_nat i + 1) with (phi + 18 + Z.of_nat (S i)) by lia.
    rewrite <- (f05_psum_S bs i).
    apply (IH (S i)); [lia | lia | lia | lia | exact Hrd].
Qed.

(* 0x13794 -> 0x137c8: s1 = sum_ok, a2 = TF stored at sp+24, #42 not taken (s0 = is_8819), s2 = 1. *)
Lemma f05t_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi k S : Z) (e : bool)
         (b16 b17 : byte) (junk : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 S -> s5 = Z_to_bv 64 phi -> s7 = Z_to_bv 64 k ->
    s0 = Z_to_bv 64 (b2z e) ->
    0 <= S < 2 ^ 64 -> 0 <= k <= 13 -> negb (k =? 0) = e -> 0 < phi -> phi + 50 < 2 ^ 64 ->
    0 <= spv -> spv + 1936 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] ->
    ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] ->
    Step.rw_cells rsegs m (spv + 24) [Cells.CB 8 junk] ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (b2z (S mod 256 =? 0))) a0' a1' a2' a3 a4 a5 a6 a7
                       (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x137c8) fc None m' (seg_rom rsegs) /\
         munch [(spv + 24, spv + 32)] m m' /\ wmono rsegs m m' /\
         q64 m' (spv + 24) (b2z ((S mod 256 =? 0) || ((bv_unsigned b16 =? 0) && (bv_unsigned b17 =? 0)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13794) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi k S e b16 b17 junk Esp E0 E5 E7 E8 HS Hk He Hp Hpl Hs0 Hs1 HR16 HR17 HC.
  subst sp a0 s5 s7 s0.
  pose proof (b4_byte_nn b16) as Hb16. pose proof (b4_byte_nn b17) as Hb17.
  pose proof (Step.rw_cells_store_ok rsegs m (spv + 24) [Cells.CB 8 junk] 0 (Cells.CB 8 junk) 8 HC
                eq_refl eq_refl) as HSt.
  pose proof (munch_refl [(spv + 24, spv + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step.
  rewrite (f05_s0 S HS).
  destruct (Z.eqb_spec (bv_unsigned b16) 0) as [E16|E16].
  - if_false_by (f_equal negb (eq_trans (b4_eqb (bv_unsigned b16) 0 ltac:(lia) ltac:(lia))
                                        (proj2 (Z.eqb_eq _ _) E16))).
    step. step. step. step.
    rewrite f05_s1. rewrite (f05_s0 S HS). rewrite f05_lor.
    step. step.
    rewrite (f05_snez k) by lia. rewrite He. if_false_by (f05_bne_same (Z_to_bv 64 (b2z e))).
    step. step.
    apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    pose proof (sl_cells_bytes _ _ _ HC) as HB. cbn [Cells.cells_bytes Cells.cbytes] in HB.
    rewrite app_nil_r in HB. unfold q64.
    replace (bv_unsigned b16 =? 0) with true by (symmetry; apply Z.eqb_eq; exact E16).
    cbn [andb]. rewrite orb_comm. exact HB.
  - if_true_by (f_equal negb (eq_trans (b4_eqb (bv_unsigned b16) 0 ltac:(lia) ltac:(lia))
                                       (proj2 (Z.eqb_neq _ _) E16))).
    step. step.
    rewrite (f05_snez k) by lia. rewrite He. if_false_by (f05_bne_same (Z_to_bv 64 (b2z e))).
    step. step.
    apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    pose proof (sl_cells_bytes _ _ _ HC) as HB. cbn [Cells.cells_bytes Cells.cbytes] in HB.
    rewrite app_nil_r in HB. unfold q64.
    replace (bv_unsigned b16 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E16).
    cbn [andb]. rewrite orb_false_r. exact HB.
Qed.

Lemma f05_nth_firstn : forall m n (l : list byte) d, (n < m)%nat -> nth n (firstn m l) d = nth n l d.
Proof.
  induction m as [|m IH]; intros n [|x l] d Hn; [lia | lia | destruct n; reflexivity |].
  destruct n as [|n]; [reflexivity|]. cbn. apply IH. lia.
Qed.

(* len >= 50: head, loop and tail. *)
Lemma f05b_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi k len : Z) (g junk : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 k -> s4 = Z_to_bv 64 len -> s5 = Z_to_bv 64 phi ->
    s9 = Z_to_bv 64 (phi + 18) ->
    50 <= len < 2 ^ 20 -> 0 <= k <= 13 -> 0 < phi -> phi + 50 < 2 ^ 64 -> 0 <= spv -> spv + 1936 < 2 ^ 64 ->
    (forall i, (i < 50)%nat -> ov_read_bytes rsegs m (wa (phi + Z.of_nat i)) 1 = Some [nth i g cp_z]) ->
    negb (k =? 0) = (cp_v g 12 =? 0x88) && (cp_v g 13 =? 0x19) ->
    Step.rw_cells rsegs m (spv + 24) [Cells.CB 8 junk] ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (b2z ((cp_v g 12 =? 0x88) && (cp_v g 13 =? 0x19))))
                       (Z_to_bv 64 (b2z (RcModel.blocksum (skipn 18 g) =? 0)))
                       a0' a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 k)
                       s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x137c8) fc None m' (seg_rom rsegs) /\
         munch [(spv + 24, spv + 32)] m m' /\ wmono rsegs m m' /\
         q64 m' (spv + 24)
           (b2z ((RcModel.blocksum (skipn 18 g) =? 0) || ((cp_v g 16 =? 0) && (cp_v g 17 =? 0)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1370c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi k len g junk Esp E0 E4 E5 E9 Hl Hk Hp Hpl Hs0 Hs1 Hrd He HC.
  pose proof (Hrd 12%nat ltac:(lia)) as HR12. pose proof (Hrd 13%nat ltac:(lia)) as HR13.
  pose proof (Hrd 16%nat ltac:(lia)) as HR16. pose proof (Hrd 17%nat ltac:(lia)) as HR17.
  change (Z.of_nat 12) with 12 in HR12. change (Z.of_nat 13) with 13 in HR13.
  change (Z.of_nat 16) with 16 in HR16. change (Z.of_nat 17) with 17 in HR17.
  rewrite <- !f05_blocksum.
  eapply evt_cut.
  { exact (f05h_evt ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m k len phi (skipn 18 g) (nth 12 g cp_z) (nth 13 g cp_z) E0 E4 E5 E9 Hl Hp Hpl HR12 HR13). }
  intros ms1 ->.
  eapply evt_cut.
  { apply (f05_loop (skipn 18 g) phi 32 0); [lia | lia | lia | lia |].
    intros j Hj. rewrite f05_nth_skipn. replace (phi + 18 + Z.of_nat j) with (phi + Z.of_nat (18 + j)) by lia.
    apply Hrd. lia. }
  intros ms2 (a3' & ->).
  pose proof (f05_psum_rng (skipn 18 g) 32) as Hps.
  eapply evt_cut.
  { apply (f05t_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ spv phi k
             (RcModel.psum (skipn 18 g) 32) ((bv_unsigned (nth 12 g cp_z) =? 136) && (bv_unsigned (nth 13 g cp_z) =? 25))
             (nth 16 g cp_z) (nth 17 g cp_z) junk);
      [exact Esp | reflexivity | exact E5 | reflexivity | reflexivity | lia | lia | exact He | lia | lia | lia | lia
      | exact HR16 | exact HR17 | exact HC]. }
  intros ms3 (a0' & a1' & a2' & m' & -> & MU & WM & HQ).
  apply evt_done. exists a0', a1', a2', a3', m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. exact HQ.
Qed.

(* The register file, pc and memory of a state equation, without injection on the model terms. *)
Lemma f05_ms_inj : forall R1 F1 pc1 fc1 rv1 m1 ro1 R2 F2 pc2 fc2 rv2 m2 ro2,
  MS R1 F1 pc1 fc1 rv1 m1 ro1 = MS R2 F2 pc2 fc2 rv2 m2 ro2 -> R1 = R2 /\ pc1 = pc2 /\ m1 = m2.
Proof.
  intros R1 F1 pc1 fc1 rv1 m1 ro1 R2 F2 pc2 fc2 rv2 m2 ro2 E.
  split; [exact (f_equal ms_regs E)|]. split; [exact (f_equal ms_pc_val E) | exact (f_equal ms_mem E)].
Qed.

Section F05.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_F05 : forall j : nat, Hat B APIf ra (Inv_K1374c_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K137c8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K1370c_at B APIf ra empty) j.
Proof.
  intros j H40 Hbc g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HFT & Hnz & HIFS & H25 & H10 & HB)).
  pose proof HFT as (Hj & H26 & (H27 & H32 & H20) & H21 & Hphi & HOUR & HM7).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HS1 & HS2 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (b1_hb B APIf ra empty FF g phi (t_len (g_in g) j) L A regs mem md HFR HP) as (_ & Hphi0 & Hphin).
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  pose proof (b4_len_range (g_in g) j) as (Hl0 & _).
  pose proof (b4_len_le (g_in g) j) as Hle.
  pose proof (b4_phi_len (g_in g) j) as HL.
  assert (Hk : 0 <= t_k (g_in g) j <= 13) by apply RcParse.ctrlparse_kind_range.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (Z_le_dec 50 (t_len (g_in g) j)) as [Hb|Hs].
  - (* len >= 50: to K137c8 *)
    assert (Hbig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; lia).
    pose proof (b4_tg_eq (g_in g) j Hb) as Eg.
    pose proof (bytes_at_normalize rsegs mem phi _ HMI Hphi) as HphiN.
    assert (Hrd : forall i, (i < 50)%nat ->
      ov_read_bytes rsegs (normalize rsegs mem) (wa (phi + Z.of_nat i)) 1 = Some [nth i (t_g (g_in g) j) cp_z]).
    { intros i Hi. rewrite (bytes_at_read rsegs _ phi _ (Z.of_nat i) 1 HphiN) by lia.
      rewrite Nat2Z.id. rewrite (b4_firstn1 _ i) by lia.
      rewrite Eg. unfold RcIdentModel.nthb. rewrite f05_nth_firstn by lia. reflexivity. }
    assert (HP51 : negb (t_k (g_in g) j =? 0) =
                   (cp_v (t_g (g_in g) j) 12 =? 0x88) && (cp_v (t_g (g_in g) j) 13 =? 0x19)).
    { pose proof (b4_P51 (g_in g) j) as P. unfold t_8819 in P. rewrite Hbig in P. cbn [andb] in P.
      destruct (Z.eqb_spec (t_k (g_in g) j) 0) as [E|E];
        destruct ((cp_v (t_g (g_in g) j) 12 =? 0x88) && (cp_v (t_g (g_in g) j) 13 =? 0x19)) eqn:X;
        cbn [negb]; try reflexivity; exfalso; [apply P in E; congruence | apply E, P; first [exact X | reflexivity]]. }
    destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 24) 8 ST ltac:(lia) ltac:(lia)) as (junk & HC).
    set (W := [(g_S g - 1936 + 24, g_S g - 1936 + 32)]).
    eapply (b4_mid B APIf ra empty FF g _ L A regs mem md _ W); [exact HFR | exact HP | | | |].
    + intros x Hx O. refine (b4_fp g W x _ Hx O). unfold W, SLOT_K, SLOT_STACK.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
    + rewrite sl_mkR_of.
      apply f05b_evt with (spv := g_S g - 1936) (phi := phi) (k := t_k (g_in g) j) (len := t_len (g_in g) j)
        (g := t_g (g_in g) j) (junk := junk);
        [exact Hsp | exact H10 | exact H20 | exact H21 | exact H25 | lia | lia | lia | lia | lia | lia
        | exact Hrd | exact HP51 | exact HC].
    + intros ms (? & ? & ? & ? & m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + (* the state equation by projections: injection on the model terms of the registers does not end *)
      intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (? & ? & ? & ? & m'' & HE & _ & _ & H24).
      destruct (f05_ms_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE) as (ER & Epc & Em).
      subst m0' pc' R.
      apply Hbc. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (K1 : b4_keep mem m' (spk g 8) (spk g 24)).
      { apply (b4_keep_munch _ mem m' _ _ MU'); unfold W, spk, fsp, SLOT_FRAME in *; cbn [disjoint_from];
          repeat split; lia. }
      assert (K2 : b4_keep mem m' (spk g 32) (spk g 1788)).
      { apply (b4_keep_munch _ mem m' _ _ MU'); unfold W, spk, fsp, SLOT_FRAME in *; cbn [disjoint_from];
          repeat split; lia. }
      assert (KH : b4_keep mem m' phi (phi + t_len (g_in g) j)).
      { apply (b4_keep_munch _ mem m' _ _ MU'); unfold W, spk, fsp, SLOT_FRAME in *; cbn [disjoint_from];
          repeat split; lia. }
      split; [split|].
      * apply (b4_FT_keep2 g j phi regs regs' mem m' KH);
          [exact K1
          | eapply b4_keep_sub; [exact K2 | unfold spk; lia | unfold spk; lia]
          | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity .. | exact HFT].
      * unfold FV, V7, V9, V0, V2, VC, rg. rewrite !(sl_getr_eqv _ _ _ Hx).
        unfold t_TF, t_tfill, t_sum_ok, t_8819. rewrite !Hbig. cbn [andb].
        split; [reflexivity|]. split; [exact H25|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [exact (b1_out _ _ _ _ Hrel H24)|].
        eapply b4_ba_keep; [exact HB | exact K2 | unfold spk; lia
                           | unfold t_B; rewrite (RcParse.ctrlparse_length (t_len (g_in g) j) (t_g (g_in g) j)); unfold spk; lia].
      * apply (b4_IFS_keep2 g j regs regs' mem m');
          [eapply b4_keep_sub; [exact K1 | unfold spk; lia | lia]
          | eapply b4_keep_sub; [exact K2 | unfold spk; lia | unfold spk; lia]
          | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity | exact HIFS].
  - (* 1 <= len <= 49: to K1374c *)
    eapply (b4_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | | | |].
    + intros x Hx O. exfalso. apply O. exact I.
    + rewrite sl_mkR_of. apply f05a_evt with (k := t_k (g_in g) j) (len := t_len (g_in g) j);
        [exact H10 | exact H20 | lia].
    + intros ms ->. do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct (f05_ms_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ HQ) as (ER & Epc & Em).
      subst m0' pc' R.
      apply H40. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (K : b4_keep mem m' (spk g 8) (spk g 1788))
        by (apply (b4_keep_munch [] mem m' _ _ MU' I); unfold spk, fsp, SLOT_FRAME; lia).
      assert (KH : b4_keep mem m' phi (phi + t_len (g_in g) j))
        by (apply (b4_keep_munch [] mem m' _ _ MU' I); lia).
      split; [|split; [lia|split; [|split; [|split]]]].
      * apply (b4_FT_keep g j phi regs regs' mem m' KH);
          [eapply b4_keep_sub; [exact K | lia | unfold spk; lia]
          | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity .. | exact HFT].
      * apply (b4_IFS_keep g j regs regs' mem m'); [eapply b4_keep_sub; [exact K | unfold spk; lia | unfold spk; lia]
          | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity | exact HIFS].
      * unfold V9, rg. rewrite (sl_getr_eqv _ _ _ Hx). exact H25.
      * unfold V7, rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * eapply b4_ba_keep; [exact HB | exact K | unfold spk; lia
                           | unfold t_B; rewrite (RcParse.ctrlparse_length (t_len (g_in g) j) (t_g (g_in g) j)); unfold spk; lia].
Qed.

End F05.

From Stdlib Require Import SpecFloat.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rate_snap_c reac_master_only_cadence_ns_c.
Import ListNotations.
Open Scope Z_scope.

Lemma digits2_size : forall p, digits2_pos p = Pos.size p.
Proof. induction p as [p IH|p IH|]; cbn [digits2_pos Pos.size]; try rewrite IH; reflexivity. Qed.

Lemma log2_size : forall p, Z.log2 (Zpos p) = Zpos (Pos.size p) - 1.
Proof. intros p. destruct p; cbn [Z.log2 Pos.size]; rewrite ?Pos2Z.inj_succ; lia. Qed.

Lemma size_bounds : forall p, 2 ^ (Zpos (Pos.size p) - 1) <= Zpos p < 2 ^ Zpos (Pos.size p).
Proof.
  intros p. pose proof (Z.log2_spec (Zpos p) ltac:(lia)) as [H1 H2]. rewrite log2_size in H1, H2.
  split; [exact H1|]. replace (Zpos (Pos.size p)) with (Z.succ (Zpos (Pos.size p) - 1)) by lia. exact H2.
Qed.

Lemma digits2_shift : forall k p, digits2_pos (shift_pos k p) = (digits2_pos p + k)%positive.
Proof.
  intros k p. unfold shift_pos. induction k as [|k IH] using Pos.peano_ind.
  - cbn [Pos.iter digits2_pos]. rewrite Pos.add_1_r. reflexivity.
  - rewrite Pos.iter_succ. cbn [digits2_pos]. rewrite IH, Pos.add_succ_r. reflexivity.
Qed.

Lemma round_aux_exact : forall md s mz ez,
  Zpos (digits2_pos mz) = 53 -> -1074 <= ez <= 971 ->
  round_aux fmt_double md s (Zpos mz) ez loc_Exact = (S754_finite s mz ez, no_flags).
Proof.
  intros md s mz ez Hd He.
  assert (E1 : SpecFloat.shr_fexp 53 1024 (Zpos mz) ez loc_Exact = (Build_shr_record (Zpos mz) false false, ez)).
  { unfold SpecFloat.shr_fexp. cbn [Zdigits2]. rewrite Hd.
    replace (SpecFloat.fexp 53 1024 (53 + ez) - ez) with 0 by (unfold SpecFloat.fexp, SpecFloat.emin; lia).
    reflexivity. }
  unfold round_aux. cbn [fp_prec fp_emax fmt_double]. rewrite E1. cbn [loc_of_shr_record shr_m].
  replace (BinarySingleNaN.choice_mode (flocq_mode md) s (Zpos mz) loc_Exact) with (Zpos mz) by (destruct md; reflexivity).
  rewrite E1. cbn [shr_m].
  replace (ez <=? 1024 - 53) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma round_exact_small : forall md s p, Zpos (digits2_pos p) <= 31 ->
  exists mz, round_exact fmt_double md s p 0 = (S754_finite s mz (Zpos (digits2_pos p) - 53), no_flags) /\
             Zpos (digits2_pos mz) = 53.
Proof.
  intros md s p Hd. unfold round_exact. cbn [fp_prec fp_emax fmt_double].
  replace (SpecFloat.fexp 53 1024 (Zpos (digits2_pos p) + 0)) with (Zpos (digits2_pos p) - 53)
    by (unfold SpecFloat.fexp, SpecFloat.emin; lia).
  unfold SpecFloat.shl_align.
  match goal with |- context [match ?t with Z0 => _ | Zpos _ => _ | Zneg _ => _ end] => destruct t as [|k|k] eqn:E end;
    try (exfalso; lia).
  exists (shift_pos k p).
  assert (D : Zpos (digits2_pos (shift_pos k p)) = 53) by (rewrite digits2_shift, Pos2Z.inj_add; lia).
  split; [|exact D].
  apply round_aux_exact; [exact D | lia].
Qed.

Lemma cvt_ok : forall z, 1 <= z < 2^31 ->
  snd (fp_of_int fmt_double RNE false 32 z) = no_flags /\
  0 <= fst (fp_of_int fmt_double RNE false 32 z) < 2^64 /\
  fp_is_nan fmt_double (fst (fp_of_int fmt_double RNE false 32 z)) = false.
Proof.
  intros z Hz.
  assert (W : int_wrap 32 z = z) by (unfold int_wrap; rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  unfold fp_of_int. rewrite W. cbn [andb].
  destruct z as [|p|p]; try (exfalso; lia).
  assert (Hd : Zpos (digits2_pos p) <= 31).
  { rewrite digits2_size. pose proof (size_bounds p) as [H1 H2].
    destruct (Z_le_gt_dec (Zpos (Pos.size p)) 31) as [G|G]; [exact G|].
    exfalso. assert (2^31 <= 2^(Zpos (Pos.size p) - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
  destruct (round_exact_small RNE false p Hd) as (mz & E & D).
  unfold round_scaled. rewrite E. unfold enc. cbn [fst snd].
  pose proof (size_bounds mz) as [M1 M2]. rewrite <- digits2_size, D in M1, M2.
  assert (EV : fp_encode fmt_double (S754_finite false mz (Zpos (digits2_pos p) - 53))
               = (Zpos (digits2_pos p) + 1021) * 2^52 + Zpos mz).
  { unfold fp_encode. change (fp_prec fmt_double) with 53. rewrite <- digits2_size, D.
    change (fp_mw fmt_double) with 52. change (fp_ew fmt_double) with 11. change (fp_emin fmt_double) with (-1074).
    cbv zeta. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont].
    rewrite !Z.shiftl_mul_pow2 by lia. lia. }
  rewrite EV.
  split; [reflexivity|]. split; [lia|].
  unfold fp_is_nan, fp_exp_field.
  change (fp_mw fmt_double) with 52. change (fp_ew fmt_double) with 11.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (((Zpos (digits2_pos p) + 1021) * 2^52 + Zpos mz) / 2^52) with (Zpos (digits2_pos p) + 1022)
    by (apply (Z.div_unique_pos _ _ _ (Zpos mz - 2^52)); lia).
  rewrite Z.land_ones, Z.mod_small by lia.
  replace (Zpos (digits2_pos p) + 1022 =? Z.ones 11) with false by (symmetry; apply Z.eqb_neq; change (Z.ones 11) with 2047; lia).
  reflexivity.
Qed.

Lemma fcsr_keep : forall fc : bv 32, Z_to_bv 32 (Z.lor (bv_unsigned fc) 0) = fc.
Proof.
  intros fc. rewrite Z.lor_0_r. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma cvt_fcsr : forall (fc : bv 32) z, 1 <= z < 2^31 ->
  Z_to_bv 32 (Z.lor (bv_unsigned fc) (fflags_bits (fp_of_int fmt_double RNE false 32 z).2)) = fc.
Proof. intros fc z Hz. destruct (cvt_ok z Hz) as (H & _ & _). rewrite H. apply fcsr_keep. Qed.

Lemma cvt_nan : forall z, 1 <= z < 2^31 -> fp_is_nan fmt_double (bv_unsigned (fcvt_d_wu RNE (Z_to_bv 64 z))) = false.
Proof.
  intros z Hz. unfold fcvt_d_wu. rewrite (unsigned_lit z) by lia.
  destruct (cvt_ok z Hz) as (_ & R & N). rewrite (unsigned_lit _ R). exact N.
Qed.

Lemma snap_fcsr_keep : forall x fc, fp_is_nan fmt_double (bv_unsigned x) = false -> reac_rate_snap_fcsr x fc = fc.
Proof. intros x fc H. unfold reac_rate_snap_fcsr. rewrite H. apply fcsr_keep. Qed.

Lemma snap_cases : forall x,
  reac_rate_snap_model x = 44100 \/ reac_rate_snap_model x = 48000 \/ reac_rate_snap_model x = 96 * 1000.
Proof. intros x. unfold reac_rate_snap_model. destruct (flt_d _ _); [|destruct (flt_d _ _)]; auto. Qed.

Lemma fget_other_n : forall (F : bvmap 5 word) (k r : bv 5) v,
  bv_unsigned k <> bv_unsigned r -> reg_get (bvmap_set k v F) r = reg_get F r.
Proof. intros F k r v H. apply reg_get_set_other. intros E. apply H. rewrite E. reflexivity. Qed.

Ltac fsimp := repeat first [ rewrite freg_get_other by reflexivity | rewrite freg_get_same by reflexivity ].

Ltac run_to n :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 n) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [if_true | if_false]
  | _ => step
  end.

Ltac norm_lits :=
  repeat lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with
      | context [Some ?v] =>
          lazymatch v with Z_to_bv 64 ?z => tryif is_Zlit z then fail else idtac | _ => idtac end;
          tryif (match v with context [?x] => is_var x end) then fail else idtac;
          let z := eval vm_compute in (bv_unsigned v) in
          is_Zlit z;
          replace v with (Z_to_bv 64 z) by (apply bv_eq; vm_compute; reflexivity)
      end
  end.

Ltac run_lit n :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 n) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [if_true | if_false]
  | _ => step; norm_lits
  end.

Ltac fix_cvt_fcsr :=
  try match goal with |- context [fp_of_int fmt_double RNE false 32 (bv_unsigned (Z_to_bv 64 ?z))] =>
    rewrite (unsigned_lit z) by lia
  end;
  match goal with |- context [Z_to_bv 32 (Z.lor (bv_unsigned ?f) (fflags_bits (fp_of_int fmt_double RNE false 32 ?z).2))] =>
    rewrite (cvt_fcsr f z) by lia
  end.

Ltac step_keep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with
    | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i ]
      end
    end
  end.

Ltac snap_call RS :=
  eapply evt_cut; [eapply RS; eassumption | ];
  let ms' := fresh "ms'" in let a1x := fresh "a1x" in let E := fresh "E" in
  intros ms' [a1x E]; subst ms';
  rewrite ret_pc_even by (first [lia | reflexivity]);
  fsimp.

Ltac fix_snap :=
  match goal with |- context [reac_rate_snap_fcsr (fcvt_d_wu RNE (Z_to_bv 64 ?z)) ?f] =>
    rewrite (snap_fcsr_keep _ f (cvt_nan z ltac:(lia)))
  end;
  match goal with |- context [reac_rate_snap_model ?x] =>
    let v := eval vm_compute in (reac_rate_snap_model x) in
    replace (reac_rate_snap_model x) with v by (vm_compute; reflexivity)
  end.

Ltac snap_turn RS pc :=
  run_lit pc; step_keep; fix_cvt_fcsr; step; snap_call RS; fix_snap.

Ltac kept_tac :=
  let k := fresh "k" in let K8 := fresh "K8" in let K10 := fresh "K10" in
  let K14 := fresh "K14" in let K15 := fresh "K15" in
  intros k K8 K10 K14 K15;
  repeat (rewrite fget_other_n; [| let HE := fresh "HE" in intro HE;
            first [ apply K8; rewrite <- HE; reflexivity | apply K10; rewrite <- HE; reflexivity
                  | apply K14; rewrite <- HE; reflexivity | apply K15; rewrite <- HE; reflexivity ] ]);
  reflexivity.

Ltac fix_div :=
  match goal with |- context [mul_div M_DIVU ?x ?y] =>
    replace (mul_div M_DIVU x y) with (Z_to_bv 64 (10^9)) by (apply bv_eq; vm_compute; reflexivity)
  end.

Lemma cad_epilogue : forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                         g1 g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 a1 a2 a3 a4 a5 a6 a7 : word)
    (F F' : bvmap 5 word) (fc : bv 32) (lo : Z) (m0 m : word -> option byte),
  rw_cells rsegs m (bv_unsigned sp + -96)
    [C8 (reg_get F (Z_to_bv 5 8)); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -96) -> lo + 96 <= bv_unsigned sp ->
  munch [(bv_unsigned sp + -96, bv_unsigned sp)] m0 m -> wmono rsegs m0 m ->
  (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 ->
     reg_get F' k = reg_get F k) ->
  evt rsegs
    (fun ms' => exists (a1' a2' a3' a4' a5' : word) (F'' : bvmap 5 word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (10^9)) a1' a2' a3' a4' a5' a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F'' (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned sp + -96, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\
       stk rsegs m' lo (bv_unsigned sp) /\ freg_kept F F'')
    (MS (mkR g1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 g8 g9 (Z_to_bv 64 (10^9)) a1 a2 a3 a4 a5 a6 a7
             g18 g19 g20 g21 g22 g23 g24 g25 s10 s11 t3 t4 t5 t6)
        F' (Z_to_bv 64 0x16634) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    g1 g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 a1 a2 a3 a4 a5 a6 a7 F F' fc lo m0 m FR ST LO MU WM KF.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Hlo & _ & _).
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  step.
  apply evt_done. do 7 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|].
  intros k K10 K14 K15.
  destruct (Z.eq_dec (bv_unsigned k) 8) as [K8|K8].
  - replace k with (Z_to_bv 5 8) by (apply bv_eq; rewrite K8; reflexivity).
    rewrite freg_get_same by reflexivity. reflexivity.
  - rewrite fget_other_n by (intro HE; apply K8; rewrite <- HE; reflexivity).
    apply KF; assumption.
Qed.

Lemma rates_read : forall m,
  bytes_at rsegs m 0x10598 (le4 (Z_to_bv 64 44100) ++ le4 (Z_to_bv 64 48000) ++ le4 (Z_to_bv 64 (96 * 1000))) ->
  ov_read_bytes rsegs m (wa 0x10598) 4 = Some (le4 (Z_to_bv 64 44100)) /\
  ov_read_bytes rsegs m (wa (0x10598 + 4)) 4 = Some (le4 (Z_to_bv 64 48000)) /\
  ov_read_bytes rsegs m (wa (0x10598 + 8)) 4 = Some (le4 (Z_to_bv 64 (96 * 1000))).
Proof.
  intros m H. split; [|split].
  - replace (wa 0x10598) with (wa (0x10598 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m _ _ 0 4 H) by (cbn; lia). reflexivity.
  - rewrite (bytes_at_read rsegs m _ _ 4 4 H) by (cbn; lia). reflexivity.
  - rewrite (bytes_at_read rsegs m _ _ 8 4 H) by (cbn; lia). reflexivity.
Qed.

Theorem reac_master_only_cadence_ns_holds : reac_rate_snap_contract -> reac_master_only_cadence_ns_contract.
Proof.
  intros RS. unfold reac_master_only_cadence_ns_contract, REAC_MASTER_ONLY_CADENCE_NS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fps lo
    E0 Hfps ST HLO HRT HR H6 H3.
  subst a0.
  unfold RT, A_P6000, A_P3837, RATES in *.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Hlo & Hhi & _).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 96%nat ST.
  step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  destruct (Z_lt_le_dec 0 fps) as [Hp | Hp].
  - replace (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 fps)) with true
      by (rewrite bv_lts_zero_l, unsigned_lit by lia; symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
    cbv iota beta. cbn [negb].
    step_keep.
    rewrite (unsigned_lit fps) by lia. rewrite (cvt_fcsr fc fps) by lia.
    pose proof (cvt_nan fps ltac:(lia)) as NX.
    set (X := fcvt_d_wu RNE (Z_to_bv 64 fps)) in *.
    step. step.
    snap_call RS.
    rewrite (snap_fcsr_keep X fc NX).
    step. step. step.
    snap_call RS.
    rewrite (snap_fcsr_keep X fc NX).
    destruct (snap_cases X) as [HM|[HM|HM]]; rewrite HM; run_to 0x16634; fix_div;
      (eapply cad_epilogue; [eassumption | eassumption | lia | eassumption | eassumption | kept_tac]).
  - replace (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 fps)) with false.
    2:{ rewrite bv_lts_zero_l, unsigned_lit_wrap. destruct (Z.eq_dec fps 0) as [Z0|Z0].
        - subst fps. reflexivity.
        - replace (fps mod 2^64) with (fps + 2^64) by (apply Z.mod_unique with (q := -1); lia).
          symmetry. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
    cbv iota beta. cbn [negb].
    match goal with HRR : bytes_at _ _ _ (le4 _ ++ _) |- _ => destruct (rates_read _ HRR) as (R0 & R1 & R2) end.
    snap_turn RS 0x165d4. snap_turn RS 0x165d4. snap_turn RS 0x165d4.
    run_lit 0x16634.
    eapply cad_epilogue; [eassumption | eassumption | lia | eassumption | eassumption | kept_tac].
Qed.

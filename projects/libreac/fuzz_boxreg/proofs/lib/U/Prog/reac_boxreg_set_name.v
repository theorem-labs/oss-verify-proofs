From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd printf_facts_c snprintf_c reac_boxreg_set_name_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sn_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; lia).
  first [ reflexivity | f_equal; apply firstn_all2; rewrite length_le4; lia ].
Qed.

Lemma sn_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Ltac sn_cl := repeat first [ rewrite sn_sx32 by lia | rewrite lts_lit by lia ].

Lemma sn_fmt : forall m, mem_inv rsegs m -> bytes_at rsegs m FMT_S (pf_bytes ([37; 115] ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [ exact MI | unfold FMT_S; lia | cbn; unfold FMT_S; lia | ].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma sn_empty : forall m, mem_inv rsegs m ->
  bytes_at rsegs m EMPTY_S (pf_bytes ([] ++ [0]) ++ [Z_to_bv 8 46; Z_to_bv 8 0]).
Proof.
  intros m MI. apply ro_bytes_at; [ exact MI | unfold EMPTY_S; lia | cbn; unfold EMPTY_S; lia | ].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma sn_img_shift : forall D n D' n', pf_img_free D n -> D <= D' -> D' + n' <= D + n -> pf_img_free D' n'.
Proof.
  intros D n D' n' H H1 H2. unfold pf_img_free in *. intros i Hi s Hs C.
  apply (H (D' - D + i) ltac:(lia) s Hs). lia.
Qed.

Lemma sn_img_disj : forall D n a k, pf_img_free D n -> 0 < n -> 0 < k ->
  (exists s, In s (segments_reserved rsegs) /\ bv_unsigned (fst s) <= a /\
             a + k <= bv_unsigned (fst s) + bv_unsigned (snd s)) ->
  a + k <= D \/ D + n <= a.
Proof.
  intros D n a k H Hn Hk (s & Hs & H1 & H2). unfold pf_img_free in H.
  destruct (Z_le_gt_dec (a + k) D) as [L1 | L1]; [ left; exact L1 | ].
  destruct (Z_le_gt_dec (D + n) a) as [L2 | L2]; [ right; exact L2 | ].
  exfalso. destruct (Z_le_gt_dec D a) as [L3 | L3].
  - apply (H (a - D) ltac:(lia) s Hs). lia.
  - apply (H 0 ltac:(lia) s Hs). lia.
Qed.

Lemma sn_res_empty : exists s, In s (segments_reserved rsegs) /\ bv_unsigned (fst s) <= EMPTY_S /\
  EMPTY_S + 3 <= bv_unsigned (fst s) + bv_unsigned (snd s).
Proof.
  assert (E : existsb (fun s : word * word => (bv_unsigned (fst s) <=? EMPTY_S) &&
                (EMPTY_S + 3 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in E. destruct E as (s & Hs & Hb). apply andb_true_iff in Hb. destruct Hb as [B1 B2].
  apply Z.leb_le in B1, B2. exists s. split; [ exact Hs | split; assumption ].
Qed.

Lemma sn_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
         (lo D p : Z) (canary : word) (s : list Z) (junk slack : list byte),
    snprintf_contract ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 32 -> a2 = Z_to_bv 64 FMT_S -> a3 = Z_to_bv 64 p ->
    rw_cells rsegs m D [CB 32 junk] -> 0 < D -> pf_img_free D 32 -> (D + 32 <= lo \/ bv_unsigned sp <= D) ->
    Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) < 2^31 - 1 ->
    bytes_at rsegs m p (pf_bytes (s ++ [0]) ++ slack) ->
    (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) -> 0 < p ->
    (p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= p) ->
    (p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= D \/ D + 32 <= p) ->
    stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - SNPRINTF_K -> IMG_END <= lo ->
    bv_unsigned sp < 2^63 -> frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    (forall ms', printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D (Z.of_nat (length s))
                   (firstn 31 s) m ms' -> Q ms') ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 SNPRINTF) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q
    lo D p canary s junk slack SC E0 E1 E2 E3 HJ HD0 HD1 HD2 SF SL SB SM SP SD1 SD2 ST LOK LOI SPB FR MI TM GG GD K.
  subst a0 a1 a2 a3.
  pose proof (rw_cells_bound rsegs m D [CB 32 junk] HJ) as RD.
  change (Z.of_nat (cells_size [CB 32 junk])) with 32 in RD.
  pose proof (bytes_at_bound rsegs m p _ SB) as PB.
  unfold pf_bytes in PB. rewrite !length_app, length_map, length_app in PB. cbn [length] in PB.
  pose proof (SC ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 32) (Z_to_bv 64 FMT_S) (Z_to_bv 64 p)
                 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
                 [37; 115] [Ps] [APtr s] s junk) as H.
  cbv zeta in H.
  rewrite (unsigned_lit D), (unsigned_lit 32), (unsigned_lit FMT_S) in H by (unfold FMT_S; lia).
  assert (PA : pf_args_ok m (bv_unsigned sp) lo D 32 [Z_to_bv 64 p; a4; a5; a6; a7] [APtr s]).
  { cbn [pf_args_ok pf_arg_ok]. rewrite (unsigned_lit p) by lia. split; [ | exact I ].
    split; [ exact SF | ]. exists slack.
    split; [ exact SB | split; [ exact SM | split; [ exact SP | split; [ exact SD1 | exact SD2 ] ] ] ]. }
  assert (PT : pf_text [Ps] [APtr s] = Some s).
  { cbn. rewrite app_nil_r. reflexivity. }
  eapply evt_mono; [ | exact K ].
  exact (H (sn_fmt m MI) ltac:(unfold RO_LO, FMT_S; lia) ltac:(unfold FMT_S, RO_END; cbn [length]; lia)
           eq_refl PA PT HJ ltac:(lia) SL HD0 HD2 HD1 ST LOK LOI SPB FR MI TM GG GD).
Qed.

Ltac sn_weq :=
  first [ reflexivity
        | repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
            rewrite (unsigned_lit e) by (rewrite ?Z.shiftl_mul_pow2 by lia; lia) end;
          rewrite ?Z.shiftl_mul_pow2 by lia; f_equal; lia
        | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; rewrite ?Z.shiftl_mul_pow2 by lia;
          Z.div_mod_to_equations; lia ].

Ltac sn_lia := unfold IMG_END, EMPTY_S in *; cbn [length] in *; lia.

Ltac sn_tests :=
  repeat match goal with
  | |- context [Z.ltb ?x ?y] =>
      first [ rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia ]
  | |- context [Z.leb ?x ?y] =>
      first [ rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia ]
  end; cbn [orb].

Ltac sn_ret :=
  apply evt_done; cbv beta delta [mkR]; do 18 eexists; split; [ reflexivity | ];
  split; [ apply munch_refl | ]; split; [ apply wmono_refl | ]; split; [ assumption | ]; split; [ assumption | ];
  split; [ assumption | ]; split; [ intros ? _; reflexivity | ]; split; [ assumption | ];
  sn_tests; split; [ reflexivity | split; reflexivity ].

Ltac sn_post :=
  let ms := fresh "ms" in let PP := fresh "PP" in
  intros ms PP; unfold printf_post in PP; cbv beta;
  destruct PP as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                  snEQ & snMU & snWM & snMI & snTM & snFR & snFK & snST & snBY);
  do 18 eexists; split; [ exact snEQ | ];
  split;
  [ eapply munch_weaken; [ | exact snMU ];
    let x := fresh "x" in let Hx := fresh "Hx" in
    intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (snX1 & snX2 & _);
    split; [ exact snX1 | split; [ | exact I ] ]; rewrite length_firstn; lia
  | ];
  split; [ exact snWM | ]; split; [ exact snMI | ]; split; [ exact snTM | ]; split; [ exact snFR | ];
  split; [ exact snFK | ];
  split; [ exact snST | ]; sn_tests; exact snBY.

Lemma sn_land3 : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.

Lemma sn_hi : forall x i, 0 <= x < 2^64 -> 64 <= i -> Z.testbit x i = false.
Proof. intros x i Hx Hi. rewrite <- (Z.mod_small x (2^64)) by lia. apply Z.mod_pow2_bits_high. lia. Qed.

Lemma sn_lxor : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  assert (L : Z.ldiff x (Z.ones 64) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 64).
    - rewrite Z.ones_spec_low by lia. cbn [negb]. apply andb_false_r.
    - rewrite (sn_hi x i Hx) by lia. reflexivity. }
  rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x L).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite (sn_hi x i Hx) by lia. reflexivity.
Qed.

Lemma sn_sh6 : forall x, Z.shiftl x 6 = x * 64.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma sn_sh3 : forall x, Z.shiftl x 3 = x * 8.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Ltac sn_fin H := first [ lia | Z.div_mod_to_equations; lia ].

Theorem reac_boxreg_set_name_holds : snprintf_contract -> reac_boxreg_set_name_contract.
Proof.
  intros SC. unfold reac_boxreg_set_name_contract, REAC_BOXREG_SET_NAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo r idx q bs canary s E0 E1 E2 Hidx HR HB1 HRI Hr0 Hr4 HN ST LOK LOI SPB DR FR MI TM GG GD.
  destruct HR as [[HWF HBY] HWR].
  cbn [cells_wf cell_wf] in HWF. destruct HWF as [HL _].
  cbn [cells_bytes cbytes] in HBY. rewrite app_nil_r in HBY.
  change (Z.of_nat (cells_size [CB 288 bs])) with 288 in HWR.
  pose proof (bytes_at_bound rsegs m r bs HBY) as RB. rewrite HL in RB. change (Z.of_nat 288) with 288 in RB.
  pose proof (rd4_bytes_at m r bs 280 HBY ltac:(lia) ltac:(rewrite HL; lia)) as BN.
  change (rd4 bs 280) with (bx_n bs) in BN.
  pose proof (sn_rd4 _ _ _ BN) as RN.
  unfold boxreg_B1 in HB1.
  subst a0 a1 a2.
  step. sn_cl.
  if_cases HC1; zify_bool HC1.
  - step. sn_ret.
  - step. if_cases HT0; [ exfalso; zify_cond HT0; rewrite ?(Z.mod_small r) in HT0 by lia; sn_fin HT0 | ].
    step. step. step.
    if_cases HT1;
      [ exfalso; zify_cond HT1; rewrite ?(Z.mod_small r) in HT1 by lia; rewrite (sn_land3 r Hr4) in HT1;
        sn_fin HT1 | ].
    step. sn_cl. step. sn_cl.
    if_cases HC2; zify_bool HC2.
    + step. sn_ret.
    + step. step.
      if_cases HT2; [ exfalso; zify_cond HT2; rewrite ?(Z.mod_small idx) in HT2 by lia; sn_fin HT2 | ].
      step. step. step. step. step.
      if_cases HT3;
        [ exfalso; zify_cond HT3; rewrite ?(Z.mod_small r) in HT3 by lia; rewrite ?(Z.mod_small idx) in HT3 by lia;
          rewrite ?sn_sh6, ?sn_sh3 in HT3; rewrite ?(sn_lxor r) in HT3 by lia; sn_fin HT3 | ].
      assert (JK : rw_cells rsegs m (r + 56 * idx + 24) [CB 32 (bsub bs (56 * idx + 24) 32)]).
      { unfold rw_cells, cells_at. split; [ split | ].
        - cbn [cells_wf cell_wf]. split; [ | exact I ]. rewrite bsub_length by (rewrite ?HL; lia). reflexivity.
        - cbn [cells_bytes cbytes]. rewrite app_nil_r.
          replace (r + 56 * idx + 24) with (r + (56 * idx + 24)) by lia.
          apply bytes_at_bsub; [ exact HBY | lia | lia | rewrite HL; lia ].
        - change (Z.of_nat (cells_size [CB 32 (bsub bs (56 * idx + 24) 32)])) with 32.
          destruct HWR as (W1 & W2 & W3). split; [ lia | split; [ lia | ] ].
          intros i Hi. replace (r + 56 * idx + 24 + i) with (r + (56 * idx + 24 + i)) by lia. apply W3. lia. }
      assert (HDF : pf_img_free (r + 56 * idx + 24) 32) by (apply (sn_img_shift r 288); [ exact HRI | lia | lia ]).
      do 6 step.
      destruct HN as [[Q0 S0] | [QN (SF & SL & slack & SB & SM & SD1 & SD2)]].
      * subst q s. if_cases HC3; [ exfalso; vm_compute in HC3; discriminate HC3 | ].
        do 6 step.
        eapply sn_tail with (lo := lo) (D := r + 56 * idx + 24) (p := EMPTY_S) (canary := canary) (s := [])
          (junk := bsub bs (56 * idx + 24) 32) (slack := [Z_to_bv 8 46; Z_to_bv 8 0]);
          [ exact SC | sn_weq | sn_weq | sn_weq | sn_weq | exact JK | sn_lia | exact HDF | sn_lia | constructor | sn_lia
          | exact (sn_empty m MI) | apply Z.leb_le; vm_compute; reflexivity | sn_lia | sn_lia
          | cbn [length]; pose proof (sn_img_disj _ 32 EMPTY_S 3 HDF ltac:(lia) ltac:(lia) sn_res_empty); lia
          | exact ST | exact LOK | exact LOI | exact SPB | exact FR | exact MI | exact TM | exact GG | exact GD
          | sn_post ].
      * pose proof (bytes_at_bound _ _ _ _ SB) as QB. unfold pf_bytes in QB.
        rewrite !length_app, length_map, length_app in QB. cbn [length] in QB.
        if_cases HC3; [ | exfalso; rewrite eqb_lit in HC3 by lia; zify_bool HC3; lia ].
        do 4 step.
        eapply sn_tail with (lo := lo) (D := r + 56 * idx + 24) (p := q) (canary := canary) (s := s)
          (junk := bsub bs (56 * idx + 24) 32) (slack := slack);
          [ exact SC | sn_weq | sn_weq | sn_weq | sn_weq | exact JK | sn_lia | exact HDF | sn_lia | exact SF | exact SL
          | exact SB | exact SM | lia | exact SD1 | lia
          | exact ST | exact LOK | exact LOI | exact SPB | exact FR | exact MI | exact TM | exact GG | exact GD
          | sn_post ].
Qed.

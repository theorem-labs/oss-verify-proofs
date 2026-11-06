(** The value and refusal segments of reac_headamp_prop_parse_result's walk (plain image, 0x1487c): [pv_refuse]
    proves Prog/Seg/ParseCut.v's [S_REFUSE] (0x14c5c-0x14c70: the first refusal is kept, s8 reloaded, then the
    advance [K_ADV]) and [pv_value] proves [S_VALUE] (0x14b5c-0x14c58: value_pod_to_byte on the child at cc, with
    spa_pod_get_bool / _int / _float and reac_float_nearest inlined, value_in_range, the n >= max break to [S_EXIT], or
    out[n] = (ch, p, value) and n++, then the advance; or the refusal OUT_OF_RANGE through [S_REFUSE]). Adapted from
    fuzz_role's parse walk (proofs/reac-pw/fuzz_role/lib/Prog/reac_role_prop_parse.v: the value words pc_*, the Float
    core pc_flt). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Cells Step Image FP ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Accessors Spa SpaBool Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import reac_headamp_prop_parse_result_c ParseSites ParseFP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Import ParseCut.
Import ListNotations.
Open Scope Z_scope.

(** * The call's facts *)
Lemma pv_facts : forall c, pc_ok c ->
  0 < c_P c /\ c_P c + Z.of_nat (length (c_bs c)) <= c_lo c /\ 8 <= Z.of_nat (length (c_bs c)) /\
  0 <= c_cap c <= 9 /\ 0 < c_O c /\ c_O c + 3 * (c_cap c + 1) <= c_lo c /\
  0 <= c_lo c /\ c_lo c + 528 <= bv_unsigned (c_sp c) /\ bv_unsigned (c_sp c) < 2^64 /\
  c_spf c = bv_unsigned (c_sp c) - 160 /\ 0 <= c_E c /\ c_E c + 4 <= 2^64 /\
  (c_E c + 4 <= c_lo c \/ bv_unsigned (c_sp c) <= c_E c) /\
  (c_E c + 4 <= c_O c \/ c_O c + 3 * (c_cap c + 1) <= c_E c) /\
  (c_O c + 3 * (c_cap c + 1) <= c_P c \/ c_P c + Z.of_nat (length (c_bs c)) <= c_O c).
Proof.
  intros c (HA & HS & HL & _ & _).
  destruct HA as (_ & HP0 & _ & HLEN & _ & HPL & HCAP & HO0 & _ & HOL & HOP & _ & HEV & HED & _).
  pose proof (rw_cells_bound rsegs _ _ _ HEV) as HEB. cbn [cells_size csize] in HEB.
  destruct HS as (HLO & _ & _). cbn [disjoint_from] in HED.
  pose proof (bv_unsigned_in_range 64 (c_sp c)) as R. change (bv_modulus 64) with (2^64) in R.
  unfold PARSE_STACK in HL. unfold c_spf, c_E.
  repeat split; lia.
Qed.

(** * Words and branch tests *)
Lemma pv_slit : forall e, -2^63 <= e < 2^63 -> bv_signed (Z_to_bv 64 e) = e.
Proof.
  intros e H. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.ltb_spec (e mod 2^64) (2^63)); Z.div_mod_to_equations; lia.
Qed.

Ltac pv_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu;
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
         | |- context [bv_signed (Z_to_bv 64 ?e)] => rewrite (pv_slit e) by lia
         end;
  solve_cond_rec.
Ltac pv_go := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true; [cbv iota | symmetry; pv_cond]
            | replace c with false; [cbv iota | symmetry; pv_cond] ]
  end.

(** * [S_REFUSE]: 0x14c5c `beqz s4` (rf = 0 keeps bad), 0x14c60 `mv s8,s4`, 0x14c64 `mv s6,zero`, 0x14c68
    `mv s4,s8`, 0x14c6c `ld s8,0x18(sp)` (the prefix pointer), 0x14c70 `j 0x14a94`: the advance. *)
Lemma pv_refuse : forall c, pc_ok c -> S_REFUSE c.
Proof.
  intros c HC. unfold S_REFUSE.
  intros r cc rest cl keys rf bad m F fc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 ja jb
    HK Hn Hk Hkc Hrf Hbad HR HPM HFP.
  pose proof (proj1 HPM) as HRW. unfold wframe, saves in HRW.
  step.
  destruct (Z.eq_dec rf 0) as [E0|E0].
  - subst rf. pv_go.
    step. step. step. step.
    eapply HK; [exact Hn | lia | lia | lia | | exact HPM | exact HFP].
    unfold REFUSE_NONE in HR. rewrite Z.eqb_refl in HR. exact HR.
  - pv_go.
    step. step. step. step. step.
    eapply HK; [exact Hn | lia | lia | lia | | exact HPM | exact HFP].
    unfold REFUSE_NONE in HR. rewrite (proj2 (Z.eqb_neq rf 0) E0) in HR. exact HR.
Qed.

(** * The memory at a cut: the pod's bytes, out writable, the frame's shapes *)
Lemma pv_pod : forall c fr cl m, pc_ok c -> Z.of_nat (length cl) <= c_cap c -> PMem c fr cl m ->
  bytes_at rsegs m (c_P c) (c_bs c).
Proof.
  intros c fr cl m (HA & _ & HL & _ & _) Hn (_ & _ & HMU & _).
  apply (pod_kept _ _ _ _ _ _ _ _ _ _ _ _ (Z.of_nat (length cl)) (c_P c) (c_bs c) HA HL);
    [lia | exact HMU | lia | lia | exact (proj1 HA)].
Qed.

Lemma pv_wro : forall c fr cl m, pc_ok c -> PMem c fr cl m -> wr_at rsegs m (c_O c) (3 * (c_cap c + 1)).
Proof.
  intros c fr cl m (HA & _) (_ & _ & _ & _ & _ & HWM & _).
  destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & HW & _).
  exact (wr_at_transport rsegs (c_m c) m _ _ HW HWM).
Qed.

Lemma pv_v2w : forall c ja bd ch jb cl m, PMem c (vframe c ja bd ch jb) cl m ->
  exists ja', PMem c (wframe c ja' jb) cl m.
Proof.
  intros c ja bd ch jb cl m (HRW & HR). exists (cells_bytes [CB 8 ja; C8 bd; C8 ch]). split; [|exact HR].
  unfold vframe, wframe in *.
  exact (rw_cells_merge rsegs m (c_spf c) [] [CB 8 ja; C8 bd; C8 ch] _ HRW).
Qed.

Lemma pv_v2e : forall c ja bd ch jb cl m, PMem c (vframe c ja bd ch jb) cl m ->
  exists j, PMem c (CB 56 j :: saves c) cl m.
Proof.
  intros c ja bd ch jb cl m (HRW & HR).
  exists (cells_bytes [CB 8 ja; C8 bd; C8 ch; C8 (Z_to_bv 64 LIT_PREFIX); CB 24 jb]). split; [|exact HR].
  unfold vframe in *.
  exact (rw_cells_merge rsegs m (c_spf c) [] [CB 8 ja; C8 bd; C8 ch; C8 (Z_to_bv 64 LIT_PREFIX); CB 24 jb] _ HRW).
Qed.

(** * The words of the tail, the bound and the cell bytes *)
Lemma pv_land255 : forall v, 0 <= v <= 255 -> Z.land (bv_unsigned (Z_to_bv 64 v)) 255 = v.
Proof.
  intros v Hv. rewrite unsigned_lit by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2^8) with 256. lia.
Qed.

Lemma pv_addiw : forall n, 0 <= n < 2^31 - 1 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 n) + 1)) = Z_to_bv 64 (n + 1).
Proof.
  intros n H. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  assert (HM : bv_half_modulus 32 = 2^31) by reflexivity. rewrite HM. lia.
Qed.

Lemma pv_le1 : forall x, 0 <= x < 2^64 -> le1 (Z_to_bv 64 x) = [Z_to_bv 8 x].
Proof.
  intros x H. change (le1 (Z_to_bv 64 x)) with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 x))].
  rewrite unsigned_lit by lia. reflexivity.
Qed.

(** value_in_range (reac_headamp_prop.c:89-100) is the code's test value < bound (0x14b04 / 0x14b3c). *)
Lemma pv_range : forall p v, 0 <= p <= HA_SENS ->
  value_in_range p v = (v <? (if p =? HA_SENS then 0x38 else 2)).
Proof.
  intros p v Hp. unfold HA_SENS in Hp.
  assert (E : p = 0 \/ p = 1 \/ p = 2) by lia.
  destruct E as [-> | [-> | ->]];
    unfold value_in_range, HA_PHANTOM, HA_PAD, HA_SENS, REAC_HEADAMP_SENS_MAX; cbv [Z.eqb Pos.eqb orb];
    apply eq_true_iff_eq; rewrite Z.leb_le, Z.ltb_lt; lia.
Qed.

Lemma pv_out3 : forall m O cl ch p v,
  bytes_at rsegs m O (ha_cells_bytes cl) ->
  bytes_at rsegs m (O + 3 * Z.of_nat (length cl)) [Z_to_bv 8 ch] ->
  bytes_at rsegs m (O + (3 * Z.of_nat (length cl) + 1)) [Z_to_bv 8 p] ->
  bytes_at rsegs m (O + (3 * Z.of_nat (length cl) + 2)) [Z_to_bv 8 v] ->
  bytes_at rsegs m O (ha_cells_bytes (cl ++ [(ch, p, v)])).
Proof.
  intros m O cl ch p v H H0 H1 H2.
  assert (E : ha_cells_bytes (cl ++ [(ch, p, v)]) =
              ha_cells_bytes cl ++ [Z_to_bv 8 ch] ++ [Z_to_bv 8 p] ++ [Z_to_bv 8 v]).
  { unfold ha_cells_bytes. rewrite flat_map_app. reflexivity. }
  rewrite E. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact H|].
  rewrite length_ha_cells_bytes. apply (proj2 (bytes_at_app _ _ _ _ _)). split.
  { replace (O + Z.of_nat (3 * length cl)) with (O + 3 * Z.of_nat (length cl)) by lia. exact H0. }
  apply (proj2 (bytes_at_app _ _ _ _ _)). split.
  { replace (O + Z.of_nat (3 * length cl) + Z.of_nat (length [Z_to_bv 8 ch]))
      with (O + (3 * Z.of_nat (length cl) + 1)) by (cbn [length]; lia). exact H1. }
  replace (O + Z.of_nat (3 * length cl) + Z.of_nat (length [Z_to_bv 8 ch]) + Z.of_nat (length [Z_to_bv 8 p]))
    with (O + (3 * Z.of_nat (length cl) + 2)) by (cbn [length]; lia). exact H2.
Qed.

(** One `sb` into out at O + k: store_ok from out's writable bytes, the step, the stored byte, the transport. *)
Ltac pv_ost k :=
  lazymatch goal with
  | HWO : wr_at rsegs ?mm ?O ?n |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HSo" in
      pose proof (wr_at_store_ok rsegs mm O n k 1 HWO ltac:(lia) ltac:(lia)) as HS
  end;
  step;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
      let E := addr_expr a in
      let HB := fresh "HBc" in
      assert (HB : bytes_at rsegs (write_to_mem mm (wa E) bs) E bs)
        by (apply bytes_at_write_same; simpl_sizes; lia)
  end;
  store_done.

(** * The value's tail at 0x14b88 with a1 = v, 0 <= v <= 255: `andi a2,a1,0xff`, the bound at 0x08, `bgeu a2,a3`
    (value_in_range fails: the refusal OUT_OF_RANGE with s8 = 5), `bge s1,s2` (n >= max: [S_EXIT]), then
    out[n] = (ch, p, v) by three `sb`, n++, s8 reloaded (0x14c6c) and the advance. *)
Lemma pv_tail : forall c, pc_ok c -> S_EXIT c -> S_REFUSE c ->
  forall (r cc ch p v : Z) (rest : list (list byte * ent)) (cl : list Headamp.cell) (keys rf : Z)
         (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) (ja jb : list byte),
    K_ADV c r cc rest ->
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc - (r + 16) -> 0 <= rf <= 5 ->
    0 <= ch < REAC_HEADAMP_MAX_CH -> 0 <= p <= HA_SENS -> 0 <= v <= 255 -> x11 = Z_to_bv 64 v ->
    ha_result (fold_after (c_cap c) (if value_in_range p v then inr (ch, p, v) else inl REFUSE_OUT_OF_RANGE)
                 rest cl keys rf) = RESM c ->
    PMem c (vframe c ja (Z_to_bv 64 (if p =? HA_SENS then 0x38 else 2)) (Z_to_bv 64 ch) jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 rf) (Z_to_bv 64 (c_P c + r + 16))
               x22 (Z_to_bv 64 (keys + 1)) (Z_to_bv 64 5) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14b88) fc None m (seg_rom rsegs)).
Proof.
  intros c HC HEX HRF r cc ch p v rest cl keys rf m F fc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30
    x31 ja jb HK Hn Hk Hkc Hrf Hch Hp Hv E11 HFOLD HPM HFP.
  subst x11.
  pose proof (pv_facts c HC)
    as (HP0 & HPL & HLEN & HCAP & HO0 & HOL & HLO0 & HLOSP & HSP & HSPF & HE0 & HE64 & HEL & HEO & HOP).
  pose proof (length_ha_cells_bytes cl) as HLC.
  rewrite (pv_range p v Hp) in HFOLD.
  set (B := if p =? HA_SENS then 0x38 else 2) in *.
  assert (HB : 2 <= B <= 56) by (subst B; destruct (p =? HA_SENS); lia).
  clearbody B.
  pose proof HPM as HPM0.
  pose proof (pv_pod c _ _ _ HC Hn HPM) as HPOD. pose proof (pv_wro c _ _ _ HC HPM) as HWO.
  destruct HPM as (HRW & HST & HMU & HBO & (ev' & HEV) & HWM & HMI).
  unfold vframe, saves in HRW.
  step. rewrite (pv_land255 v Hv).
  step. step.
  destruct (Z.lt_ge_cases v B) as [HvB|HvB].
  2: { (* value_in_range fails: the refusal OUT_OF_RANGE *)
    pv_go.
    destruct (pv_v2w c _ _ _ _ _ _ HPM0) as (ja' & HPW).
    rewrite (proj2 (Z.ltb_ge v B) HvB) in HFOLD. cbn [fold_after] in HFOLD.
    eapply HRF; [exact HK | exact Hn | exact Hk | exact Hkc | exact Hrf | lia | exact HFOLD | exact HPW | exact HFP]. }
  pv_go.
  rewrite (proj2 (Z.ltb_lt v B) HvB) in HFOLD. cbn [fold_after] in HFOLD.
  step.
  destruct (Z.le_gt_cases (c_cap c) (Z.of_nat (length cl))) as [HF|HF].
  { (* n >= max: the walk's end *)
    pv_go.
    rewrite (proj2 (Z.leb_le _ _) HF) in HFOLD.
    destruct (pv_v2e c _ _ _ _ _ _ HPM0) as (j & HPE).
    eapply HEX; [exact HFOLD | exact HPE | exact (proj2 HFP)]. }
  pv_go.
  rewrite (proj2 (Z.leb_gt _ _) HF) in HFOLD.
  clear HPM0.
  (* out[n] = (ch, p, v): the footprint grows to (O, O + 3 (n + 1)) *)
  assert (HMU1 : munch ((bv_unsigned (c_sp c) - PARSE_STACK, bv_unsigned (c_sp c))
                        :: (c_O c, c_O c + 3 * (Z.of_nat (length cl) + 1)) :: (c_E c, c_E c + 4)
                        :: (if c_R c =? 0 then [] else [(c_R c, c_R c + 12)])) (c_m c) m).
  { refine (munch_weaken _ _ _ _ _ HMU). unfold sub_fp, parse_writes. cbn [app outside].
    intros x (H1 & H2 & H3 & H4). split; [exact H1|]. split; [lia|]. split; [exact H3 | exact H4]. }
  clear HMU. unfold PARSE_STACK in HMU1.
  step. step.
  rewrite (unsigned_lit (Z.of_nat (length cl))) by lia. rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
  step. step. step.
  pv_ost (3 * Z.of_nat (length cl)).
  pv_ost (3 * Z.of_nat (length cl) + 1).
  pv_ost (3 * Z.of_nat (length cl) + 2).
  step.
  rewrite (pv_addiw (Z.of_nat (length cl))) by lia.
  step. step. step.
  assert (HL1 : Z.of_nat (length (cl ++ [(ch, p, v)])) = Z.of_nat (length cl) + 1)
    by (rewrite length_app; cbn [length]; lia).
  rewrite <- HL1.
  eapply (HK (cl ++ [(ch, p, v)]) (keys + 1) rf); [lia | lia | lia | lia | exact HFOLD | | exact HFP].
  unfold PMem, wframe, saves.
  refine (conj _ (conj HST (conj _ (conj _ (conj (ex_intro _ ev' HEV) (conj HWM HMI)))))).
  - exact (rw_cells_merge rsegs _ (c_spf c) [] [CB 8 ja; C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 ch)] _ HRW).
  - rewrite HL1. exact HMU1.
  - unfold REAC_HEADAMP_MAX_CH, HA_SENS in *.
    rewrite (pv_le1 ch) in HBc by lia. rewrite (pv_le1 p) in HBc0 by lia. rewrite (pv_le1 v) in HBc1 by lia.
    apply pv_out3; assumption.
Qed.

(** * The refusal OUT_OF_RANGE of a value pod value_pod_to_byte refuses: 0x14c5c with s8 = 5, the frame at the value
    cut. *)
Lemma pv_ref5 : forall c, S_REFUSE c ->
  forall (r cc ch p : Z) (e : ent) (rest : list (list byte * ent)) (cl : list Headamp.cell) (keys rf : Z)
         (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 bd chw : word) (ja jb : list byte),
    K_ADV c r cc rest ->
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc - (r + 16) -> 0 <= rf <= 5 ->
    parse_value e = None ->
    ha_result (fold_after (c_cap c) (vcell ch p e) rest cl keys rf) = RESM c ->
    PMem c (vframe c ja bd chw jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 rf) (Z_to_bv 64 (c_P c + r + 16))
               x22 (Z_to_bv 64 (keys + 1)) (Z_to_bv 64 5) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14c5c) fc None m (seg_rom rsegs)).
Proof.
  intros c HRF r cc ch p e rest cl keys rf m F fc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
    bd chw ja jb HK Hn Hk Hkc Hrf HV HFOLD HPM HFP.
  destruct (pv_v2w c _ _ _ _ _ _ HPM) as (ja' & HPW).
  unfold vcell in HFOLD. rewrite HV in HFOLD. cbn [fold_after] in HFOLD.
  eapply HRF; [exact HK | exact Hn | exact Hk | exact Hkc | exact Hrf | lia | exact HFOLD | exact HPW | exact HFP].
Qed.

(** * The Float core *)
(** flw of the 4 bytes of a u32 b stored by sw (role's pc_flw). *)
Lemma pv_flw : forall b, 0 <= b < 2^32 -> bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 b))) = Z_to_bv 32 b.
Proof.
  intros b Hb. apply bv_eq. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
  rewrite unsigned_lit by lia. rewrite Z_to_bv_unsigned. change (Z.of_N 32) with 32.
  change (bv_wrap 32 b) with (b mod 2^32). rewrite !Z.mod_small by lia. reflexivity.
Qed.

(** The two double constants of reac_float_nearest(f, 0, 255) (reac_float_near.h:27): fs0 = +0.0 (0x14a18
    `fmv.d.x fs0,zero`) and 256.0 at 0x104b0. *)
Lemma pv_consts : f64_is_int (Z_to_bv 64 0) 0 = true /\ f64_is_int (Z_to_bv 64 0x4070000000000000) 256 = true.
Proof. split; vm_compute; reflexivity. Qed.

(** 0x14c54 `sub a1,a1,a2` with a2 = [d < fcvt.d.l t] (reac_float_near.h:30): t - that bit, t read signed. *)
Lemma pv_subw : forall (t : word) (B : bool),
  Z_to_bv 64 (bv_unsigned t - bv_unsigned (bword B)) = Z_to_bv 64 (bv_signed t - (if B then 1 else 0)).
Proof.
  intros t B. apply Z_to_bv_eqm. rewrite zb_signed.
  pose proof (bv_unsigned_in_range 64 t) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
  destruct B; cbn [bword]; rewrite unsigned_lit by lia;
    destruct (Z.ltb_spec (bv_unsigned t) (2^63)); Z.div_mod_to_equations; lia.
Qed.

(** From 0x14c18 with a1 = b, the Float body's u32 (body.h:202): the store to the float temp at 0x20, flw, and
    reac_float_nearest(f, 0, 255) inlined (reac_float_near.h:24-34: fcvt.d.s, fadd.d 0.5, fle.d against fs0 = +0.0,
    flt.d against 256.0, fcvt.l.d rtz, fcvt.d.l, flt.d, sub) with ParseFP's double steps; then the tail at 0x14b88
    or the refusal OUT_OF_RANGE. *)
Lemma pv_flt : forall c, pc_ok c -> S_EXIT c -> S_REFUSE c ->
  forall (r cc ch p b : Z) (e : ent) (rest : list (list byte * ent)) (cl : list Headamp.cell) (keys rf : Z)
         (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) (ja jb : list byte),
    K_ADV c r cc rest ->
    Z.of_nat (length cl) <= c_cap c -> 0 <= keys -> keys * 8 <= cc - (r + 16) -> 0 <= rf <= 5 ->
    0 <= ch < REAC_HEADAMP_MAX_CH -> 0 <= p <= HA_SENS -> 0 <= b < 2^32 -> x11 = Z_to_bv 64 b ->
    parse_value e = nearest b 0 255 ->
    ha_result (fold_after (c_cap c) (vcell ch p e) rest cl keys rf) = RESM c ->
    PMem c (vframe c ja (Z_to_bv 64 (if p =? HA_SENS then 0x38 else 2)) (Z_to_bv 64 ch) jb) cl m -> fp_ok F fc ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 rf) (Z_to_bv 64 (c_P c + r + 16))
               x22 (Z_to_bv 64 (keys + 1)) (Z_to_bv 64 5) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14c18) fc None m (seg_rom rsegs)).
Proof.
  intros c HC HEX HRF r cc ch p b e rest cl keys rf m F fc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30
    x31 ja jb HK Hn Hk Hkc Hrf Hch Hp Hb E11 HV HFOLD HPM HFP.
  subst x11.
  pose proof (pv_facts c HC)
    as (HP0 & HPL & HLEN & HCAP & HO0 & HOL & HLO0 & HLOSP & HSP & HSPF & HE0 & HE64 & HEL & HEO & HOP).
  pose proof (length_ha_cells_bytes cl) as HLC.
  pose proof pv_consts as (C0 & C256).
  assert (HN : nearest b 0 255 =
    if rfn_in b (Z_to_bv 64 0) (Z_to_bv 64 0x4070000000000000) then Some (rfn_r b) else None).
  { apply rfn_hw_nearest; [exact Hb | lia | lia | exact C0 | exact C256]. }
  clear C0 C256. unfold rfn_in in HN. rewrite HN in HV. clear HN.
  destruct HFP as (HF8 & FRM).
  pose proof (pv_pod c _ _ _ HC Hn HPM) as HPOD. pose proof (pv_wro c _ _ _ HC HPM) as HWO.
  destruct HPM as (HRW & HST & HMU & HBO & (ev' & HEV) & HWM & HMI).
  unfold vframe, saves in HRW. unfold parse_writes, PARSE_STACK in HMU. cbn [app] in HMU.
  (* 0x14c18 `sw a1,0x20(sp)`, 0x14c1c `flw fa5,0x20(sp)`: the float temp *)
  step. step.
  rewrite (pv_flw b Hb).
  lazymatch type of HRW with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
    apply (rw_cells_merge rsegs _ _ [c1; c2; c3; c4] [c5; c6] rest) in HRW end.
  cbn [app cells_size csize Nat.add] in HRW.
  lazymatch type of HRW with rw_cells _ ?mm _ (_ :: _ :: _ :: _ :: CB 24 ?jb' :: _) =>
    assert (HPV : PMem c (vframe c ja (Z_to_bv 64 (if p =? HA_SENS then 0x38 else 2)) (Z_to_bv 64 ch) jb') cl mm)
      by (split; [exact HRW | split; [exact HST | split; [exact HMU | split; [exact HBO | split;
            [exists ev'; exact HEV | split; [exact HWM | exact HMI]]]]]])
  end.
  clear HRW HST HMU HBO HEV HPOD HWO HWM.
  (* 0x14c20-0x14c2c: d = (double) f + 0.5 *)
  step. step. step. step.
  change (fadd_d RNE (fcvt_d_s RNE (Sem.nan_box (Z_to_bv 32 b))) (Z_to_bv 64 0x3FE0000000000000)) with (rfn_d b).
  (* 0x14c30 `fle.d a1,fs0,fa5`, 0x14c34 `beqz a1` *)
  step.
  lazymatch goal with |- context [Sem.reg_get F ?r] =>
    replace (Sem.reg_get F r) with (Z_to_bv 64 0) by (rewrite <- HF8; f_equal; apply bv_eq; reflexivity) end.
  step.
  destruct (fle_d (Z_to_bv 64 0) (rfn_d b)) eqn:E1; try rewrite E1 in HV; cbn [andb] in HV.
  2: { change (bword false) with (Z_to_bv 64 0). pv_go.
       eapply pv_ref5; [exact HRF | exact HK | exact Hn | exact Hk | exact Hkc | exact Hrf | exact HV | exact HFOLD
                       | exact HPV | ].
       split; [rewrite !freg_get_other by reflexivity; exact HF8 | assumption]. }
  change (bword true) with (Z_to_bv 64 1). pv_go.
  (* 0x14c38-0x14c44: d < 256.0 *)
  step. step. step. step.
  destruct (flt_d (rfn_d b) (Z_to_bv 64 0x4070000000000000)) eqn:E2; try rewrite E2 in HV.
  2: { change (bword false) with (Z_to_bv 64 0). pv_go.
       eapply pv_ref5; [exact HRF | exact HK | exact Hn | exact Hk | exact Hkc | exact Hrf | exact HV | exact HFOLD
                       | exact HPV | ].
       split; [rewrite !freg_get_other by reflexivity; exact HF8 | assumption]. }
  change (bword true) with (Z_to_bv 64 1). pv_go.
  pose proof (parse_value_range e (rfn_r b) HV) as HR.
  (* 0x14c48-0x14c58: t = fcvt.l.d rtz d, t - (d < fcvt.d.l t), then the tail *)
  step. step. step. step. step.
  eapply (pv_tail c HC HEX HRF r cc ch p (rfn_r b));
    [exact HK | exact Hn | exact Hk | exact Hkc | exact Hrf | exact Hch | exact Hp | exact HR | | | exact HPV | ].
  - rewrite pv_subw. reflexivity.
  - unfold vcell in HFOLD. rewrite HV in HFOLD. exact HFOLD.
  - split; [rewrite !freg_get_other by reflexivity; exact HF8 | assumption].
Qed.

(** * The value pod: its words, read from the pod, and the model's answer *)
Lemma pv_le_rt : forall l : list byte, Z_to_le_bytes (length l) (bytes_le_to_Z l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb. pose proof (le_bytes_nonneg l) as Hl.
  rewrite lor_low_shiftl by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8). change (2^8) with 256.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite Z.div_add by lia.
    rewrite Z.div_small, Z.add_0_l by lia. exact IH.
Qed.

Lemma pv_rd4 : forall bs o, 0 <= o -> (Z.to_nat o + 4 <= length bs)%nat ->
  firstn 4 (skipn (Z.to_nat o) bs) = le4 (Z_to_bv 64 (u32_at bs o)).
Proof.
  intros bs o H0 H1. unfold le4, u32_at, rd32.
  pose proof (rd32_range (skipn (Z.to_nat o) bs)) as R. unfold rd32 in R.
  rewrite unsigned_lit by lia.
  assert (L : length (firstn 4 (skipn (Z.to_nat o) bs)) = 4%nat) by (rewrite length_firstn, length_skipn; lia).
  pose proof (pv_le_rt (firstn 4 (skipn (Z.to_nat o) bs))) as E. rewrite L in E. symmetry. exact E.
Qed.

Lemma pv_ld4 : forall m P bs o, bytes_at rsegs m P bs -> 0 <= o -> o + 4 <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (P + o)) 4 = Some (le4 (Z_to_bv 64 (u32_at bs o))).
Proof.
  intros m P bs o HB H0 H1. rewrite (bytes_at_read rsegs m P bs o 4 HB H0 ltac:(lia)).
  rewrite pv_rd4 by lia. reflexivity.
Qed.

Lemma pv_rd1 : forall m P bs o b, bytes_at rsegs m P bs -> 0 <= o -> nth_error bs (Z.to_nat o) = Some b ->
  ov_read_bytes rsegs m (wa (P + o)) 1 = Some [b].
Proof.
  intros m P bs o b HB Ho E.
  assert (L : (Z.to_nat o < length bs)%nat) by (apply nth_error_Some; congruence).
  rewrite (bytes_at_read rsegs m P bs o 1 HB Ho) by lia.
  rewrite <- (firstn_skipn_step bs (Z.to_nat o) 0 b E). reflexivity.
Qed.

Lemma pv_bytes4 : forall bs o, 0 <= o -> o + 4 <= Z.of_nat (length bs) ->
  exists b8 b9 b10 b11, nth_error bs (Z.to_nat o) = Some b8 /\ nth_error bs (Z.to_nat (o + 1)) = Some b9 /\
    nth_error bs (Z.to_nat (o + 2)) = Some b10 /\ nth_error bs (Z.to_nat (o + 3)) = Some b11 /\
    u32_at bs o = bytes_le_to_Z [b8; b9; b10; b11].
Proof.
  intros bs o H0 H4.
  exists (nth (Z.to_nat o) bs NUL), (nth (Z.to_nat (o + 1)) bs NUL), (nth (Z.to_nat (o + 2)) bs NUL),
    (nth (Z.to_nat (o + 3)) bs NUL).
  split; [apply nth_error_nth'; lia|]. split; [apply nth_error_nth'; lia|].
  split; [apply nth_error_nth'; lia|]. split; [apply nth_error_nth'; lia|].
  unfold u32_at, rd32.
  rewrite <- (firstn_skipn_step bs (Z.to_nat o) 3 (nth (Z.to_nat o) bs NUL)) by (apply nth_error_nth'; lia).
  rewrite <- (firstn_skipn_step bs (S (Z.to_nat o)) 2 (nth (Z.to_nat (o + 1)) bs NUL))
    by (replace (S (Z.to_nat o)) with (Z.to_nat (o + 1)) by lia; apply nth_error_nth'; lia).
  rewrite <- (firstn_skipn_step bs (S (S (Z.to_nat o))) 1 (nth (Z.to_nat (o + 2)) bs NUL))
    by (replace (S (S (Z.to_nat o))) with (Z.to_nat (o + 2)) by lia; apply nth_error_nth'; lia).
  rewrite <- (firstn_skipn_step bs (S (S (S (Z.to_nat o)))) 0 (nth (Z.to_nat (o + 3)) bs NUL))
    by (replace (S (S (S (Z.to_nat o)))) with (Z.to_nat (o + 3)) by lia; apply nth_error_nth'; lia).
  reflexivity.
Qed.

(** The register forms of the reads and the branch tests (role's pa, pb and pc words). *)
Lemma pv_zx32 : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma pv_sx32 : forall v, 0 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  assert (HM : bv_half_modulus 32 = 2^31) by reflexivity. rewrite HM. lia.
Qed.

Lemma pv_eqb_sx : forall v k, 0 <= v < 2^32 -> 0 <= k < 2^31 ->
  bv_eqb (sx32 (Z_to_bv 64 v)) (Z_to_bv 64 k) = (v =? k).
Proof.
  intros v k Hv Hk. unfold bv_eqb, sx32. rewrite !Z_to_bv_unsigned.
  assert (HM : bv_half_modulus 32 = 2^31) by reflexivity.
  unfold bv_swrap, bv_wrap. rewrite HM.
  replace (bv_modulus 32) with (2^32) by reflexivity. replace (bv_modulus 64) with (2^64) by reflexivity.
  rewrite (Z.mod_small v (2^64)), (Z.mod_small k (2^64)) by lia.
  apply eq_true_iff_eq. rewrite !Z.eqb_eq. split; intros E; Z.div_mod_to_equations; lia.
Qed.

Lemma pv_c_shr : forall u, 0 <= u < 2^32 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 u)) 20)) (Z_to_bv 64 0) = (u <? 2^20).
Proof.
  intros u Hu. unfold bv_eqb. rewrite (unsigned_lit u) by lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (D : 0 <= u / 2^20 < 2^12) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (unsigned_lit (u / 2^20)) by lia. rewrite (unsigned_lit 0) by lia.
  destruct (Z.ltb_spec u (2^20)).
  - apply Z.eqb_eq. apply Z.div_small. lia.
  - apply Z.eqb_neq. assert (0 < u / 2^20) by (apply Z.div_str_pos; lia). lia.
Qed.

(** 0x14b84 `snez a1,a1` of the Bool body read by `lw`. *)
Lemma pv_snez : forall V, 0 <= V < 2^32 ->
  v_sltu (Z_to_bv 64 0) (sx32 (Z_to_bv 64 V)) = Z_to_bv 64 (if V =? 0 then 0 else 1).
Proof.
  intros V H. unfold v_sltu, c_ltu, bv_ltu, sx32. rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit_wrap.
  rewrite (unsigned_lit V) by lia.
  assert (E : bv_swrap 32 V = (V + 2^31) mod 2^32 - 2^31) by reflexivity. rewrite E.
  destruct (Z.eqb_spec V 0) as [->|NZ]; [reflexivity|].
  replace (0 <? ((V + 2^31) mod 2^32 - 2^31) mod 2^64) with true; [reflexivity|].
  symmetry. apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

(** 0x14bd8 `bgeu a2,a1` with a2 = 0xff and a1 the Int body read by `lw`. *)
Lemma pv_c_int : forall V, 0 <= V < 2^32 -> bv_ltu (Z_to_bv 64 255) (sx32 (Z_to_bv 64 V)) = (255 <? V).
Proof.
  intros V H. unfold bv_ltu, sx32. rewrite (unsigned_lit 255) by lia. rewrite unsigned_lit_wrap.
  rewrite (unsigned_lit V) by lia.
  assert (E : bv_swrap 32 V = (V + 2^31) mod 2^32 - 2^31) by reflexivity. rewrite E.
  apply eq_true_iff_eq. rewrite !Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

(** The four lbu, slli and or of the Float body (body.h:202): the u32 of the 4 bytes (role's pc_asm_word). *)
Lemma pv_lor_shl : forall x y k, 0 <= k -> 0 <= x -> 0 <= y < 2^k -> Z.lor (Z.shiftl x k) y = x * 2^k + y.
Proof.
  intros x y k Hk Hx Hy. rewrite Z.shiftl_mul_pow2 by lia.
  assert (L : Z.land (x * 2^k) y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [Hik|Hik].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite <- (Z.mod_small y (2^k)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- (Z.lxor_lor _ _ L), <- (Z.add_nocarry_lxor _ _ L). reflexivity.
Qed.

Lemma pv_asm : forall b8 b9 b10 b11 : byte,
  Z.lor (Z.lor (Z.shiftl (bv_unsigned b11) 24) (Z.shiftl (bv_unsigned b10) 16))
        (Z.lor (Z.shiftl (bv_unsigned b9) 8) (bv_unsigned b8)) = bytes_le_to_Z [b8; b9; b10; b11].
Proof.
  intros b8 b9 b10 b11.
  pose proof (byte_range b8) as R8. pose proof (byte_range b9) as R9.
  pose proof (byte_range b10) as R10. pose proof (byte_range b11) as R11.
  assert (E1 : Z.lor (Z.shiftl (bv_unsigned b9) 8) (bv_unsigned b8) = bv_unsigned b9 * 2^8 + bv_unsigned b8)
    by (apply pv_lor_shl; lia).
  assert (E2 : Z.lor (Z.shiftl (bv_unsigned b11) 24) (Z.shiftl (bv_unsigned b10) 16) =
               Z.shiftl (bv_unsigned b11 * 2^8 + bv_unsigned b10) 16).
  { rewrite (Z.shiftl_mul_pow2 (bv_unsigned b10) 16) by lia.
    rewrite (Z.shiftl_mul_pow2 (bv_unsigned b11 * 2^8 + bv_unsigned b10) 16) by lia.
    rewrite pv_lor_shl by lia. lia. }
  rewrite E1, E2. rewrite pv_lor_shl by lia.
  cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  rewrite (lor_low_shiftl (bv_unsigned b10) (bv_unsigned b11)) by lia.
  rewrite (lor_low_shiftl (bv_unsigned b9) (bv_unsigned b10 + bv_unsigned b11 * 256)) by lia.
  rewrite (lor_low_shiftl (bv_unsigned b8) (bv_unsigned b9 + (bv_unsigned b10 + bv_unsigned b11 * 256) * 256)) by lia.
  lia.
Qed.

Lemma pv_shl_rng : forall (b : byte) k, 0 <= k <= 24 -> 0 <= Z.shiftl (bv_unsigned b) k < 2^32.
Proof.
  intros b k Hk. pose proof (byte_range b) as R. rewrite Z.shiftl_mul_pow2 by lia.
  assert (2^k <= 2^24) by (apply Z.pow_le_mono_r; lia). assert (0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.

Lemma pv_ub : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. apply unsigned_lit. pose proof (byte_range b). lia. Qed.

Lemma pv_us : forall (b : byte) k, 0 <= k <= 24 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned b) k)) = Z.shiftl (bv_unsigned b) k.
Proof. intros b k Hk. apply unsigned_lit. pose proof (pv_shl_rng b k Hk). lia. Qed.

Lemma pv_ul : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> bv_unsigned (Z_to_bv 64 (Z.lor x y)) = Z.lor x y.
Proof. intros x y Hx Hy. apply unsigned_lit. pose proof (Z_lor_lt_pow2 x y 32 Hx Hy). lia. Qed.

Ltac pv_rng32 :=
  lazymatch goal with
  | |- 0 <= Z.lor _ _ < 2^32 => apply Z_lor_lt_pow2; pv_rng32
  | |- 0 <= Z.shiftl (bv_unsigned _) _ < 2^32 => apply pv_shl_rng; lia
  | |- 0 <= bv_unsigned ?b < 2^32 => pose proof (byte_range b); lia
  end.

Lemma pv_asm_word : forall b8 b9 b10 b11 : byte,
  v_or (v_or (v_slli (zxb b11) 24) (v_slli (zxb b10) 16)) (v_or (v_slli (zxb b9) 8) (zxb b8)) =
  Z_to_bv 64 (bytes_le_to_Z [b8; b9; b10; b11]).
Proof.
  intros b8 b9 b10 b11. rewrite <- pv_asm. unfold v_or, v_slli, zxb. f_equal.
  rewrite !pv_ub. rewrite !pv_us by lia. rewrite !pv_ul by pv_rng32. reflexivity.
Qed.

(** value_pod_to_byte (reac_headamp_prop.c:24-47) on the child at o: spa_pod_get_bool, spa_pod_get_int with the
    0..255 test, spa_pod_get_float with reac_float_nearest(f, 0, 255) (role's pc_res_* pattern). *)
Lemma pv_body : forall bs o, 4 <= u32_at bs o -> rd32 (e_body (child_at bs o)) = u32_at bs (o + 8).
Proof.
  intros bs o H. unfold child_at. cbn [e_body]. unfold rd32 at 1. rewrite firstn_firstn.
  replace (Nat.min 4 (Z.to_nat (u32_at bs o))) with 4%nat by lia. reflexivity.
Qed.

Lemma pv_res_big : forall bs o, 2^20 <= u32_at bs o -> parse_value (child_at bs o) = None.
Proof.
  intros bs o H. unfold parse_value, spa_get_bool, spa_get_int, spa_get_float.
  replace (e_size (child_at bs o)) with (u32_at bs o) by reflexivity.
  unfold SPA_POD_MAX_SIZE. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
Qed.

Lemma pv_res_bad : forall bs o, u32_at bs o < 2^20 ->
  (u32_at bs o < 4 \/ (u32_at bs (o + 4) <> 2 /\ u32_at bs (o + 4) <> 4 /\ u32_at bs (o + 4) <> 6)) ->
  parse_value (child_at bs o) = None.
Proof.
  intros bs o H1 H2. unfold parse_value, spa_get_bool, spa_get_int, spa_get_float.
  replace (e_size (child_at bs o)) with (u32_at bs o) by reflexivity.
  replace (e_type (child_at bs o)) with (u32_at bs (o + 4)) by reflexivity.
  unfold SPA_POD_MAX_SIZE, POD_BOOL, POD_INT, POD_FLOAT. rewrite (proj2 (Z.ltb_lt _ _) H1).
  destruct H2 as [H2|(H3 & H4 & H5)].
  - rewrite (proj2 (Z.leb_gt _ _) H2). rewrite !andb_false_r. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) H3), (proj2 (Z.eqb_neq _ _) H4), (proj2 (Z.eqb_neq _ _) H5). reflexivity.
Qed.

Lemma pv_res_bool : forall bs o, u32_at bs o < 2^20 -> 4 <= u32_at bs o -> u32_at bs (o + 4) = 2 ->
  parse_value (child_at bs o) = Some (if u32_at bs (o + 8) =? 0 then 0 else 1).
Proof.
  intros bs o H1 H2 H3. unfold parse_value, spa_get_bool.
  replace (e_size (child_at bs o)) with (u32_at bs o) by reflexivity.
  replace (e_type (child_at bs o)) with (u32_at bs (o + 4)) by reflexivity.
  unfold SPA_POD_MAX_SIZE, POD_BOOL. rewrite H3, (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2).
  rewrite (pv_body bs o H2). destruct (u32_at bs (o + 8) =? 0); reflexivity.
Qed.

Lemma pv_res_int : forall bs o, u32_at bs o < 2^20 -> 4 <= u32_at bs o -> u32_at bs (o + 4) = 4 ->
  parse_value (child_at bs o) =
  if (s32 (u32_at bs (o + 8)) <? 0) || (255 <? s32 (u32_at bs (o + 8))) then None else Some (s32 (u32_at bs (o + 8))).
Proof.
  intros bs o H1 H2 H3. unfold parse_value, spa_get_bool, spa_get_int.
  replace (e_size (child_at bs o)) with (u32_at bs o) by reflexivity.
  replace (e_type (child_at bs o)) with (u32_at bs (o + 4)) by reflexivity.
  unfold SPA_POD_MAX_SIZE, POD_BOOL, POD_INT. rewrite H3, (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2).
  rewrite (pv_body bs o H2). reflexivity.
Qed.

Lemma pv_res_flt : forall bs o, u32_at bs o < 2^20 -> 4 <= u32_at bs o -> u32_at bs (o + 4) = 6 ->
  parse_value (child_at bs o) = nearest (u32_at bs (o + 8)) 0 255.
Proof.
  intros bs o H1 H2 H3. unfold parse_value, spa_get_bool, spa_get_int, spa_get_float.
  replace (e_size (child_at bs o)) with (u32_at bs o) by reflexivity.
  replace (e_type (child_at bs o)) with (u32_at bs (o + 4)) by reflexivity.
  unfold SPA_POD_MAX_SIZE, POD_BOOL, POD_INT, POD_FLOAT.
  rewrite H3, (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2).
  rewrite (pv_body bs o H2). reflexivity.
Qed.

(** * [S_VALUE]: 0x14b5c-0x14c14, value_pod_to_byte's dispatch on the child at cc (s10 = P + cc): its size (`lwu`,
    SPA_POD_IS_VALID), its type (`lw`), then Bool (`snez` of the body), Int (the body when 0 <= it <= 255) or Float
    (the body's 4 bytes, then [pv_flt]); the value goes to the tail [pv_tail], any other pod to the refusal
    OUT_OF_RANGE. *)
Lemma pv_value : forall c, pc_ok c -> S_EXIT c -> S_REFUSE c -> S_VALUE c.
Proof.
  intros c HC HEX HRF. unfold S_VALUE.
  intros r cc ch p rest cl keys rf m F fc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x24 x28 x29 x30 x31 ja jb
    HK HSTO Hcc Hcc8 HCI Hn Hk Hkc Hrf Hch Hp HFOLD HPM HFP.
  pose proof (pv_facts c HC)
    as (HP0 & HPL & HLEN & HCAP & HO0 & HOL & HLO0 & HLOSP & HSP & HSPF & HE0 & HE64 & HEL & HEO & HOP).
  destruct HSTO as (Hr16 & Hr8 & Hvs & Hrl). unfold child_in in HCI.
  pose proof (pv_pod c _ _ _ HC Hn HPM) as HPOD.
  assert (RCS : 0 <= u32_at (c_bs c) cc < 2^32) by (unfold u32_at; apply rd32_range).
  assert (RT : 0 <= u32_at (c_bs c) (cc + 4) < 2^32) by (unfold u32_at; apply rd32_range).
  assert (RV : 0 <= u32_at (c_bs c) (cc + 8) < 2^32) by (unfold u32_at; apply rd32_range).
  assert (RVS : 0 <= u32_at (c_bs c) (r + 8)) by (unfold u32_at; apply rd32_range).
  (* the refusal OUT_OF_RANGE of a pod value_pod_to_byte refuses *)
  assert (REF : parse_value (child_at (c_bs c) cc) = None -> forall (y11 y12 y13 y14 y15 y16 y17 : word),
    evt rsegs (PPost c (RESM c))
      (MS (mkR x1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) x5 x6 x7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 rf) (Z_to_bv 64 (c_P c + r + 16))
               x22 (Z_to_bv 64 (keys + 1)) (Z_to_bv 64 5) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) x28 x29 x30 x31)
          F (Z_to_bv 64 0x14c5c) fc None m (seg_rom rsegs))).
  { intros EV y11 y12 y13 y14 y15 y16 y17.
    eapply pv_ref5; [exact HRF | exact HK | exact Hn | exact Hk | exact Hkc | exact Hrf | exact EV | exact HFOLD
                    | exact HPM | exact HFP]. }
  (* 0x14b5c `lwu a1,0(s10)`, `srli a2,a1,0x14`, `li s8,5`, `bnez a2`: SPA_POD_IS_VALID *)
  pose proof (pv_ld4 m (c_P c) (c_bs c) cc HPOD ltac:(lia) ltac:(lia)) as HR. unfold wa in HR.
  step. clear HR. rewrite (pv_zx32 _ RCS).
  step. step. step.
  rewrite (pv_c_shr _ RCS).
  destruct (Z.lt_ge_cases (u32_at (c_bs c) cc) (2^20)) as [H20|H20].
  2: { pv_go. apply REF. apply pv_res_big. exact H20. }
  pv_go.
  (* 0x14b6c `lw a2,4(s10)`: the type; `bltu a1,a3` on size < 4 *)
  pose proof (pv_ld4 m (c_P c) (c_bs c) (cc + 4) HPOD ltac:(lia) ltac:(lia)) as HR. unfold wa in HR.
  replace (c_P c + (cc + 4)) with (c_P c + cc + 4) in HR by lia.
  step. clear HR.
  step. step.
  destruct (Z.lt_ge_cases (u32_at (c_bs c) cc) 4) as [H4|H4].
  { pv_go. step. step. pv_go. step. step. pv_go.
    apply REF. apply pv_res_bad; [exact H20 | left; exact H4]. }
  pv_go.
  (* 0x14b78 `bne a2,a3` (a3 = 2): Bool (body.h:134-147) *)
  step. step.
  rewrite (pv_eqb_sx _ 2 RT) by lia.
  destruct (Z.eq_dec (u32_at (c_bs c) (cc + 4)) 2) as [T2|T2].
  { pv_go.
    pose proof (pv_ld4 m (c_P c) (c_bs c) (cc + 8) HPOD ltac:(lia) ltac:(lia)) as HR. unfold wa in HR.
    replace (c_P c + (cc + 8)) with (c_P c + cc + 8) in HR by lia.
    step. clear HR. step.
    assert (EV : parse_value (child_at (c_bs c) cc) = Some (if u32_at (c_bs c) (cc + 8) =? 0 then 0 else 1))
      by (apply pv_res_bool; assumption).
    unfold vcell in HFOLD. rewrite EV in HFOLD.
    eapply (pv_tail c HC HEX HRF r cc ch p (if u32_at (c_bs c) (cc + 8) =? 0 then 0 else 1));
      [exact HK | exact Hn | exact Hk | exact Hkc | exact Hrf | exact Hch | exact Hp | | | exact HFOLD | exact HPM
      | exact HFP].
    - destruct (u32_at (c_bs c) (cc + 8) =? 0); lia.
    - apply pv_snez. exact RV. }
  pv_go.
  (* 0x14bc0: Int (body.h:165-173) *)
  step. step. pv_go.
  step. step.
  rewrite (pv_eqb_sx _ 4 RT) by lia.
  destruct (Z.eq_dec (u32_at (c_bs c) (cc + 4)) 4) as [T4|T4].
  { pv_go.
    pose proof (pv_ld4 m (c_P c) (c_bs c) (cc + 8) HPOD ltac:(lia) ltac:(lia)) as HR. unfold wa in HR.
    replace (c_P c + (cc + 8)) with (c_P c + cc + 8) in HR by lia.
    step. clear HR.
    step. step.
    rewrite (pv_c_int _ RV).
    pose proof (pv_res_int (c_bs c) cc H20 H4 T4) as EV. unfold s32 in EV.
    destruct (Z.le_gt_cases (u32_at (c_bs c) (cc + 8)) 255) as [V255|V255].
    - pv_go.
      rewrite (proj2 (Z.ltb_lt (u32_at (c_bs c) (cc + 8)) (2^31))) in EV by lia.
      rewrite (proj2 (Z.ltb_ge (u32_at (c_bs c) (cc + 8)) 0)) in EV by lia.
      rewrite (proj2 (Z.ltb_ge 255 (u32_at (c_bs c) (cc + 8)))) in EV by lia. cbn [orb] in EV.
      unfold vcell in HFOLD. rewrite EV in HFOLD.
      eapply (pv_tail c HC HEX HRF r cc ch p (u32_at (c_bs c) (cc + 8)));
        [exact HK | exact Hn | exact Hk | exact Hkc | exact Hrf | exact Hch | exact Hp | lia | | exact HFOLD
        | exact HPM | exact HFP].
      apply pv_sx32. lia.
    - pv_go. step.
      apply REF. rewrite EV.
      destruct (Z.ltb_spec (u32_at (c_bs c) (cc + 8)) (2^31)).
      + rewrite (proj2 (Z.ltb_lt 255 (u32_at (c_bs c) (cc + 8)))) by lia. rewrite orb_true_r. reflexivity.
      + rewrite (proj2 (Z.ltb_lt (u32_at (c_bs c) (cc + 8) - 2^32) 0)) by lia. reflexivity. }
  pv_go.
  (* 0x14be0: Float (body.h:194-202) *)
  step. step. pv_go.
  step. step.
  rewrite (pv_eqb_sx _ 6 RT) by lia.
  destruct (Z.eq_dec (u32_at (c_bs c) (cc + 4)) 6) as [T6|T6].
  2: { pv_go. apply REF. apply pv_res_bad; [exact H20 | right; split; [exact T2 | split; [exact T4 | exact T6]]]. }
  pv_go.
  destruct (pv_bytes4 (c_bs c) (cc + 8) ltac:(lia) ltac:(lia)) as (b8 & b9 & b10 & b11 & B8 & B9 & B10 & B11 & EB).
  pose proof (pv_rd1 m (c_P c) (c_bs c) (cc + 8 + 1) b9 HPOD ltac:(lia) B9) as HR.
  replace (c_P c + (cc + 8 + 1)) with (c_P c + cc + 9) in HR by lia.
  step. clear HR.
  pose proof (pv_rd1 m (c_P c) (c_bs c) (cc + 8) b8 HPOD ltac:(lia) B8) as HR.
  replace (c_P c + (cc + 8)) with (c_P c + cc + 8) in HR by lia.
  step. clear HR.
  pose proof (pv_rd1 m (c_P c) (c_bs c) (cc + 8 + 2) b10 HPOD ltac:(lia) B10) as HR.
  replace (c_P c + (cc + 8 + 2)) with (c_P c + cc + 10) in HR by lia.
  step. clear HR.
  pose proof (pv_rd1 m (c_P c) (c_bs c) (cc + 8 + 3) b11 HPOD ltac:(lia) B11) as HR.
  replace (c_P c + (cc + 8 + 3)) with (c_P c + cc + 11) in HR by lia.
  step. clear HR.
  step. step. step. step. step. step.
  eapply (pv_flt c HC HEX HRF r cc ch p (u32_at (c_bs c) (cc + 8)) (child_at (c_bs c) cc));
    [exact HK | exact Hn | exact Hk | exact Hkc | exact Hrf | exact Hch | exact Hp | exact RV | | | exact HFOLD
    | exact HPM | exact HFP].
  - rewrite EB. exact (pv_asm_word b8 b9 b10 b11).
  - apply pv_res_flt; assumption.
Qed.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_tr_kit Z_tr_rod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees FillWinModel SendModel BitsModel BitsModel2 TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Definition eA_cells (L : dlay) (s : deflate_state) (PD : Z) (h1 h2 h3 h4 h5 : list byte) : list cell :=
  [C8 (wz (dl_S L)); C4 (wz (ds_status s)); CB 4 h1; C8 (wz (dl_Ab L)); C8 (wz (ds_pending_buf_size s));
   C8 (wz (dl_Ab L + ds_pending_out s)); C8 (wz PD);
   C4 (wz (ds_wrap s)); CB 4 h2; C8 (wz (ds_gzhead s)); C8 (wz (ds_gzindex s)); C1 (Z_to_bv 8 (ds_method s)); CB 3 h3;
   C4 (wz (ds_last_flush s)); C4 (wz (ds_w_size s)); C4 (wz (ds_w_bits s)); C4 (wz (ds_w_mask s)); CB 4 h4;
   C8 (wz (dl_Aw L)); C8 (wz (ds_window_size s)); C8 (wz (dl_Ap L)); C8 (wz (dl_Ah L));
   C4 (wz (ds_ins_h s)); C4 (wz (ds_hash_size s)); C4 (wz (ds_hash_bits s)); C4 (wz (ds_hash_mask s)); C4 (wz (ds_hash_shift s)); CB 4 h5;
   C8 (wz (ds_block_start s)); C4 (wz (ds_match_length s)); C4 (wz (ds_prev_match s)); C4 (wz (ds_match_available s));
   C4 (wz (ds_strstart s)); C4 (wz (ds_match_start s)); C4 (wz (ds_lookahead s)); C4 (wz (ds_prev_length s));
   C4 (wz (ds_max_chain_length s)); C4 (wz (ds_max_lazy_match s)); C4 (wz (ds_level s)); C4 (wz (ds_strategy s));
   C4 (wz (ds_good_match s)); C4 (wz (ds_nice_match s))].
Definition eD_cells (L : dlay) (s : deflate_state) (wbb wbv : word) (h0 h1 h2 h3 h4 : list byte) : list cell :=
  [CB 7 h0; C8 (wz (dl_Ab L + ds_lit_bufsize s)); C4 (wz (ds_lit_bufsize s)); C4 (wz (ds_sym_next s)); C4 (wz (ds_sym_end s)); CB 4 h1;
   C8 (wz (ds_opt_len s)); C8 (wz (ds_static_len s)); C4 (wz (ds_matches s)); C4 (wz (ds_insert s));
   C2 wbb; CB 2 h2; C4 wbv; CB 4 h3; C4 (wz 0); C8 (wz (ds_high_water s)); CB 4 h4; C4 (wz 0)].
Definition EM (m : mem) (L : dlay) (s : deflate_state) (PB : arr) (PD : Z) (wbb wbv : word) : Prop :=
  (exists h1 h2 h3 h4 h5, rw_cells usegs m (dl_As L) (eA_cells L s PD h1 h2 h3 h4 h5))
  /\ (exists h0 h1 h2 h3 h4, rw_cells usegs m (dl_As L + 5881) (eD_cells L s wbb wbv h0 h1 h2 h3 h4))
  /\ u8arr usegs m (dl_Ab L) (av8 PB 65536) /\ arr_len PB = 65536.
Lemma EM_of_groups : forall m L s, dsA m L s -> dsD m L s -> dpend m L s -> arr_len (ds_pending_buf s) = 65536 ->
  EM m L s (ds_pending_buf s) (ds_pending s) (wz (ds_bi_buf s)) (wz (ds_bi_valid s)).
Proof.
  intros m L s (h1 & h2 & h3 & h4 & h5 & HA) (h0 & g1 & g2 & g3 & g4 & HD) HP LN. unfold EM.
  split; [exists h1, h2, h3, h4, h5; exact HA|]. split; [exists h0, g1, g2, g3, g4; exact HD|]. split; [exact HP| exact LN].
Qed.
Lemma EM_to_groups : forall m L s PB PD (wbb wbv : word) BB BV,
  EM m L s PB PD wbb wbv -> le2 wbb = le2 (wz BB) -> le4 wbv = le4 (wz BV) ->
  dsA m L (upd4 s PB PD BB BV) /\ dsD m L (upd4 s PB PD BB BV) /\ dpend m L (upd4 s PB PD BB BV).
Proof.
  intros m L s PB PD wbb wbv BB BV ((h1 & h2 & h3 & h4 & h5 & HA) & (h0 & g1 & g2 & g3 & g4 & HD) & HP & LN) E2 E4.
  split; [|split].
  - exists h1, h2, h3, h4, h5. exact HA.
  - exists h0, g1, g2, g3, g4. unfold dsD_cells, upd4. dsred. eapply rw_cells_sim; [exact HD|].
    unfold eD_cells. cbn [cells_sim cell_sim]. repeat split; try reflexivity; assumption.
  - exact HP.
Qed.
Ltac open_EM H :=
  let hA1 := fresh "hA1" in let hA2 := fresh "hA2" in let hA3 := fresh "hA3" in let hA4 := fresh "hA4" in let hA5 := fresh "hA5" in
  let hD0 := fresh "hD0" in let hD1 := fresh "hD1" in let hD2 := fresh "hD2" in let hD3 := fresh "hD3" in let hD4 := fresh "hD4" in
  let GA := fresh "GA" in let GD := fresh "GD" in let Gp := fresh "Gpend" in let LN := fresh "LNP" in
  destruct H as ((hA1 & hA2 & hA3 & hA4 & hA5 & GA) & (hD0 & hD1 & hD2 & hD3 & hD4 & GD) & Gp & LN);
  unfold eA_cells in GA; unfold eD_cells in GD;
  lazymatch type of Gp with u8arr _ _ _ (av8 ?a ?n) => let LW := fresh "LPB" in pose proof (av8_zlength a n ltac:(lia)) as LW end.
Ltac close_EM GA GD Gp :=
  unfold EM; split; [eexists _, _, _, _, _; unfold eA_cells; close_cells GA|];
  split; [eexists _, _, _, _, _; unfold eD_cells; close_cells GD|];
  split; [exact Gp| rewrite ?arr_len_blit, ?arr_len_set, ?arr_len_fill; first [assumption | lia]].
Lemma swrap_mod : forall (n : N) x k, 0 <= k <= Z.of_N n -> (bv_swrap n x) mod 2^k = x mod 2^k.
Proof.
  intros n x k Hk. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  set (M := 2 ^ Z.of_N n). set (h := M / 2).
  assert (HM : M = 2^(Z.of_N n - k) * 2^k) by (unfold M; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hk2 : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hr : 0 < 2^(Z.of_N n - k)) by (apply Z.pow_pos_nonneg; lia).
  assert (HMp : 0 < M) by (rewrite HM; apply Z.mul_pos_pos; assumption).
  pose proof (Z.div_mod (x + h) M ltac:(lia)) as D.
  replace ((x + h) mod M - h) with (x + (- ((x + h) / M) * 2^(Z.of_N n - k)) * 2^k).
  - apply Z.mod_add. lia.
  - rewrite HM in D at 1. set (q := (x + h) / M) in *. set (r := 2^(Z.of_N n - k)) in *. set (t := 2^k) in *. clearbody q r t. lia.
Qed.
Lemma lo16_unsigned_wz : forall E, bv_unsigned (wz E) mod 2^16 = E mod 2^16.
Proof. intros. rewrite unsigned_lit_wrap. apply mod_pow2_mod_pow2. lia. Qed.
Lemma lo16_sx16 : forall w : word, bv_unsigned (sx16 w) mod 2^16 = bv_unsigned w mod 2^16.
Proof. intros. unfold sx16. rewrite lo16_unsigned_wz. apply (swrap_mod 16). cbn. lia. Qed.
Lemma lo16_zx16 : forall w : word, bv_unsigned (zx16 w) mod 2^16 = bv_unsigned w mod 2^16.
Proof. intros. unfold zx16. rewrite lo16_unsigned_wz. apply Z.mod_mod. lia. Qed.
Lemma lo16_swrap32 : forall x, (bv_swrap 32 x) mod 2^16 = x mod 2^16.
Proof. intros. apply (swrap_mod 32). cbn. lia. Qed.
Lemma lo16_mod64 : forall x, (x mod 18446744073709551616) mod 2^16 = x mod 2^16.
Proof. intros. change 18446744073709551616 with (2^64). apply mod_pow2_mod_pow2. lia. Qed.
Lemma lo16_lor : forall a b, (Z.lor a b) mod 2^16 = Z.lor (a mod 2^16) (b mod 2^16).
Proof. intros. apply lor_mod_pow2. lia. Qed.
Lemma lo16_shl : forall x k, 0 <= k -> (Z.shiftl x k) mod 2^16 = (Z.shiftl (x mod 2^16) k) mod 2^16.
Proof.
  intros x k Hk. rewrite !Z.shiftl_mul_pow2 by lia. rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.
Lemma lo16_idem : forall x, (x mod 2^16) mod 2^16 = x mod 2^16.
Proof. intros. apply Z.mod_mod. lia. Qed.
Lemma lo8_of_lo16 : forall x y, x mod 2^16 = y mod 2^16 -> x mod 2^8 = y mod 2^8.
Proof.
  intros x y H. rewrite <- (mod_pow2_mod_pow2 x 16 8), <- (mod_pow2_mod_pow2 y 16 8) by lia. rewrite H. reflexivity.
Qed.
Lemma lo8_wrap8 : forall x y, x mod 2^16 = y mod 2^16 -> x mod 2^8 = wrap8 y mod 2^8.
Proof. intros x y H. rewrite wrap8_mod, Z.mod_mod by lia. apply lo8_of_lo16. exact H. Qed.
Lemma lo8_wrap8_land : forall x y, x mod 2^16 = y mod 2^16 -> x mod 2^8 = wrap8 (Z.land y 255) mod 2^8.
Proof.
  intros x y H. rewrite wrap8_mod. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite !Z.mod_mod by lia.
  apply lo8_of_lo16. exact H.
Qed.
Lemma hi8_lo16 : forall (w : word) y, bv_unsigned w mod 2^16 = y mod 2^16 ->
  bv_unsigned (wz (bv_unsigned (Z_to_bv 8 (Z.shiftr (bv_unsigned w) 8)))) mod 2^8 = wrap8 (Z.shiftr (wrap16 y) 8) mod 2^8.
Proof.
  intros w y H.
  assert (E : bv_unsigned (Z_to_bv 8 (Z.shiftr (bv_unsigned w) 8)) = (Z.shiftr (bv_unsigned w) 8) mod 2^8) by (rewrite Z_to_bv_unsigned; reflexivity).
  rewrite E. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (Z.shiftr (bv_unsigned w) 8) (2^8) ltac:(lia)); lia).
  rewrite Z.mod_mod by lia. rewrite wrap8_mod, wrap16_mod, Z.mod_mod by lia. rewrite <- H.
  rewrite !Z.shiftr_div_pow2 by lia.
  set (X := bv_unsigned w). change (2^16) with (2^8 * 2^8). rewrite Z.rem_mul_r by lia.
  replace (X mod 2^8 + 2^8 * ((X / 2^8) mod 2^8)) with ((X / 2^8) mod 2^8 * 2^8 + X mod 2^8) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small (X mod 2^8)) by (apply Z.mod_pos_bound; lia).
  rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.
Lemma srlw_val : forall V k, 0 <= k < 32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.land V 65535)) (k mod 32)) = Z.shiftr (wrap16 V) k.
Proof.
  intros V k Hk. rewrite (Z.mod_small k 32) by lia. unfold wrap16.
  assert (R : 0 <= Z.land V 65535 < 2^16) by (change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (E : bv_wrap 32 (Z.land V 65535) = Z.land V 65535) by (apply bv_wrap_small; unfold bv_modulus; cbn; lia).
  rewrite E. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 `div` 2) with 2147483648. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as P.
  split; [pose proof (Z.div_pos (Z.land V 65535) (2^k) ltac:(lia) P); lia|].
  apply Z.div_lt_upper_bound; [exact P|]. nia.
Qed.
Lemma lo8_wz_wrap8 : forall X, 0 <= X < 2^64 -> bv_unsigned (wz X) mod 2^8 = wrap8 X mod 2^8.
Proof. intros X HX. rewrite unsigned_lit by lia. rewrite wrap8_mod, Z.mod_mod by lia. reflexivity. Qed.
Ltac bits8 :=
  unfold wrap8, wrap16; change 255 with (Z.ones 8); change 65535 with (Z.ones 16);
  rewrite <- ?Z.land_ones by lia;
  apply Z.bits_inj'; intros n Hn;
  repeat first [ rewrite Z.land_spec | rewrite Z.lxor_spec | rewrite Z.shiftr_spec by lia | rewrite Z.lnot_spec by lia
               | rewrite Z.testbit_ones_nonneg by lia ];
  destruct (Z.ltb_spec n 8); cbn [andb]; rewrite ?andb_false_r; try reflexivity;
  repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b); try lia end;
  cbn [andb xorb negb]; rewrite ?andb_true_r, ?xorb_true_r, ?xorb_false_r; try reflexivity.
Lemma lo8_unsigned_wz : forall E, bv_unsigned (wz E) mod 2^8 = E mod 2^8.
Proof. intros. rewrite unsigned_lit_wrap. apply mod_pow2_mod_pow2. lia. Qed.
Lemma lenb0 : forall len, bv_unsigned (wz len) mod 2^8 = wrap8 (Z.land (wrap16 len) 255) mod 2^8.
Proof. intros len. rewrite lo8_unsigned_wz. bits8. Qed.
Lemma lenb1 : forall len, bv_unsigned (wz (Z.shiftr len 8)) mod 2^8 = wrap8 (Z.shiftr (wrap16 (wrap16 len)) 8) mod 2^8.
Proof. intros len. rewrite lo8_unsigned_wz. bits8. Qed.
Lemma lenb2 : forall len, bv_unsigned (wz (Z.lxor len 65535)) mod 2^8 = wrap8 (Z.land (wrap16 (Z.lnot len)) 255) mod 2^8.
Proof. intros len. rewrite lo8_unsigned_wz. bits8. Qed.
Definition nbv (BB BV V : Z) : Z := wrap16 (Z.lor BB (Z.shiftl (wrap16 V) BV)).
Definition sbF_PB (PB : arr) (PD BB BV V l : Z) : arr :=
  if 16 - l <? BV then arr_set (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) else PB.
Definition sbF_PD (PD BV l : Z) : Z := if 16 - l <? BV then PD + 1 + 1 else PD.
Definition sbF_BB (BB BV V l : Z) : Z := if 16 - l <? BV then Z.shiftr (wrap16 V) (16 - BV) else nbv BB BV V.
Definition sbF_BV (BV l : Z) : Z := if 16 - l <? BV then BV + l - 16 else BV + l.
Lemma send_bits_sbF : forall s PB PD BB BV V l,
  send_bits (upd4 s PB PD BB BV) V l = upd4 s (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l).
Proof.
  intros. unfold sbF_PB, sbF_PD, sbF_BB, sbF_BV, nbv.
  destruct (Z.ltb_spec (16 - l) BV) as [C|C].
  - rewrite send_bits_flush_eq by (unfold Buf_size; rewrite TrSmallModel.upd4_bi_valid; exact C).
    unfold sb_nb, Buf_size. rewrite !TrSmallModel.upd4_pending_buf, !TrSmallModel.upd4_pending, !TrSmallModel.upd4_bi_buf, !TrSmallModel.upd4_bi_valid.
    apply TrSmallModel.upd4_upd4.
  - rewrite send_bits_keep_eq by (unfold Buf_size; rewrite TrSmallModel.upd4_bi_valid; lia).
    unfold sb_nb. rewrite !TrSmallModel.upd4_pending_buf, !TrSmallModel.upd4_pending, !TrSmallModel.upd4_bi_buf, !TrSmallModel.upd4_bi_valid.
    apply TrSmallModel.upd4_upd4.
Qed.
Lemma nbv_canon : forall BB BV V, 0 <= BV -> nbv BB BV V mod 2^16 = Z.lor (BB mod 2^16) ((Z.shiftl (V mod 2^16) BV) mod 2^16).
Proof. intros. unfold nbv. rewrite !wrap16_mod, lo16_idem, lo16_lor. reflexivity. Qed.
Lemma or_sllw_lo16 : forall A V k BB, A mod 2^16 = BB mod 2^16 -> 0 <= k < 32 ->
  bv_unsigned (wz (Z.lor A (bv_swrap 32 (Z.shiftl V (k mod 32)) mod 18446744073709551616))) mod 2^16 = nbv BB k V mod 2^16.
Proof.
  intros A V k BB HA Hk. rewrite nbv_canon by lia. rewrite lo16_unsigned_wz, lo16_lor, HA, lo16_mod64, lo16_swrap32.
  rewrite (Z.mod_small k 32) by lia. rewrite lo16_shl by lia. reflexivity.
Qed.
Notation Wem L := [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + 65536)] (only parsing).
Definition ct_readable (W : list ivl) (m0 : mem) (T : Z) (fc dl : arr) (n : Z) : Prop :=
  forall m', munch W m0 m' -> wmono usegs m0 m' -> mem_inv usegs m' -> forall i, 0 <= i < n ->
     ov_read_bytes usegs m' (wa (T + 4 * i)) 2 = Some (le2 (wz (arr_get fc i)))
  /\ ov_read_bytes usegs m' (wa (T + 4 * i + 2)) 2 = Some (le2 (wz (arr_get dl i))).
Lemma ct_readable_rebase : forall W W' m0 m T fc dl n,
  ct_readable W m0 T fc dl n -> munch W m0 m -> wmono usegs m0 m -> sub_fp W' W -> ct_readable W' m T fc dl n.
Proof.
  intros W W' m0 m T fc dl n H MU WM SUB m' MU' WM' MI i Hi. apply H; [|eapply wmono_trans; eassumption| exact MI| exact Hi].
  eapply munch_trans; [exact MU|]. eapply munch_weaken; [exact SUB| exact MU'].
Qed.
Lemma ct_readable_ro : forall W m0 T fc dl N n, (forall m, mem_inv usegs m -> bytes_at usegs m T (u16s (avct fc dl N))) -> n <= N ->
  ct_readable W m0 T fc dl n.
Proof.
  intros W m0 T fc dl N n HB HN m' _ _ MI i Hi. specialize (HB m' MI). split.
  - apply (Z_tr_rod.u16ro_read m' T (avct fc dl N) (2 * i)); [exact HB| apply avct_nth_fc; lia| lia| f_equal; lia].
  - apply (Z_tr_rod.u16ro_read m' T (avct fc dl N) (2 * i + 1)); [exact HB| apply avct_nth_dl; lia| lia| f_equal; lia].
Qed.
Lemma ct_readable_rw : forall W m0 T fc dl N n, u16arr usegs m0 T (avct fc dl N) -> 0 <= N -> n <= N ->
  disjoint_from W T (4 * N) -> ct_readable W m0 T fc dl n.
Proof.
  intros W m0 T fc dl N n ARR H0 HN D m' MU WM _ i Hi.
  assert (ARR' : u16arr usegs m' T (avct fc dl N)).
  { eapply u16arr_transport; [exact ARR| exact MU| exact WM|]. rewrite avct_length. replace (2 * Z.of_nat (Z.to_nat (2 * N))) with (4 * N) by lia. exact D. }
  split.
  - apply (u16arr_read usegs m' T (avct fc dl N) (2 * i)); [exact ARR'| apply avct_nth_fc; lia| lia| f_equal; lia].
  - apply (u16arr_read usegs m' T (avct fc dl N) (2 * i + 1)); [exact ARR'| apply avct_nth_dl; lia| lia| f_equal; lia].
Qed.
Tactic Notation "sb_or" ident(w) ident(LO) constr(BB) tactic3(HA) :=
  match goal with
  | |- context [wz (Z.lor ?a (bv_swrap 32 (Z.shiftl ?V (?k mod 32)) mod 18446744073709551616))] =>
      let Ew := fresh "Ew" in
      remember (wz (Z.lor a (bv_swrap 32 (Z.shiftl V (k mod 32)) mod 18446744073709551616))) as w eqn:Ew;
      assert (LO : bv_unsigned w mod 2^16 = nbv BB k V mod 2^16) by (rewrite Ew; apply or_sllw_lo16; [HA | lia]);
      clear Ew
  end.
Ltac sbf_b0 L Gp PB PD nb LO :=
  repeat zs;
  pb_store Gp PB 65536 (dl_Ab L) PD (wrap8 (Z.land nb 255)) ltac:(apply lo8_wrap8_land; exact LO).
Ltac sbf_b1 L Gp GD PB PD nb LO :=
  repeat zs; rd_c2 GD 55%nat 1; zs; repeat zs;
  pb_store Gp (arr_set PB PD (wrap8 (Z.land nb 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 nb) 8)) ltac:(apply hi8_lo16; exact LO).
Lemma srlw_val16 : forall V k, 0 <= V < 2^16 -> 0 <= k < 32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 V) (k mod 32)) = Z.shiftr (wrap16 V) k.
Proof.
  intros V k HV Hk. rewrite <- (srlw_val V k Hk). unfold wrap16.
  replace (Z.land V 65535) with V; [reflexivity|].
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. exact HV.
Qed.
Lemma srliw7 : forall x, 0 <= x < 2^31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 7) = Z.shiftr x 7.
Proof.
  intros x Hx. assert (E : bv_wrap 32 x = x) by (apply bv_wrap_small; unfold bv_modulus; cbn; lia). rewrite E.
  apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 `div` 2) with 2147483648. rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128.
  pose proof (Z.div_pos x 128 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 128 x ltac:(lia) ltac:(lia)). lia.
Qed.
Ltac state_eq tac := f_equal; unfold mkR; repeat f_equal; tac.

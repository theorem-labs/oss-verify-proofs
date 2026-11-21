(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem Z_kit Z_defl_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_defl_kit Z_defl_path
     F_memset Z_fw_model Z_fw_kit Z_fw_slide Zg_adler32_iface Zg_defl_path Zg_defl_iface Z_ukit Zl_defl_iface Zl_dparams_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateParams FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition ZL_DP_EPI : Z := 0x17030.
Definition ZL_DP_LV : Z := 0x170e4.      (* [comment removed for export] *)
Definition ZL_DP_LVNE : Z := 0x170e8.    (* [comment removed for export] *)
Definition ZL_DP_SAME : Z := 0x1722c.    (* [comment removed for export] *)
Definition ZL_DP_FLUSH : Z := 0x17130.
Definition ZL_DP_TBL : Z := 0x171fc.
Definition ZL_DP_TRAP : Z := 0x17238.
Definition ZL_DEFLATE : Z := 0x1723c.
Definition ZL_CFG_NOT : Z := 18446744073709370791.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma slx_val : forall v, - 2^63 <= v < 2^63 -> Z.lxor (v mod 18446744073709551616) 9223372036854775808 = v + 9223372036854775808.
Proof.
  intros v Hv. change 9223372036854775808 with (2^63). change 18446744073709551616 with (2^64).
  rewrite zb_lxor_sign by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.
Lemma slx_pos : forall v, 0 <= v < 2^63 -> Z.lxor v 9223372036854775808 = v + 9223372036854775808.
Proof. intros v Hv. change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sgn_guard0 : forall b, - 2^63 <= b < 2^63 ->
  (9223372036854775808 <? Z.lxor (b mod 18446744073709551616) 9223372036854775808) = (0 <? b).
Proof. intros b Hb. rewrite slx_val by lia. destruct (Z.ltb_spec 0 b); [apply Z.ltb_lt; lia| apply Z.ltb_ge; lia]. Qed.
(* [comment removed for export] *)
Lemma sub_guard : forall ss b, 0 <= ss < 2^32 -> - 2^62 <= b < 2^62 ->
  (Z.lxor ((ss - b mod 18446744073709551616) mod 18446744073709551616) 9223372036854775808 <? Z.lxor ss 9223372036854775808) = (0 <? b).
Proof.
  intros ss b Hs Hb.
  replace ((ss - b mod 18446744073709551616) mod 18446744073709551616) with ((ss - b) mod 18446744073709551616) by (Z.div_mod_to_equations; lia).
  rewrite slx_val by lia. rewrite slx_pos by lia.
  destruct (Z.ltb_spec 0 b); [apply Z.ltb_lt; lia| apply Z.ltb_ge; lia].
Qed.
(* [comment removed for export] *)
Lemma add_guard : forall ss b la, 0 <= ss < 2^32 -> - 2^62 <= b < 2^62 -> 0 <= la < 2^32 ->
  (Z.lxor ((ss - b mod 18446744073709551616 + la) mod 18446744073709551616) 9223372036854775808
     <? Z.lxor ((ss - b mod 18446744073709551616) mod 18446744073709551616) 9223372036854775808) = false.
Proof.
  intros ss b la Hs Hb Hl.
  replace ((ss - b mod 18446744073709551616 + la) mod 18446744073709551616) with ((ss - b + la) mod 18446744073709551616) by (Z.div_mod_to_equations; lia).
  replace ((ss - b mod 18446744073709551616) mod 18446744073709551616) with ((ss - b) mod 18446744073709551616) by (Z.div_mod_to_equations; lia).
  rewrite (slx_val (ss - b + la)) by lia. rewrite (slx_val (ss - b)) by lia. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Definition dp_tbl_st (X : deflate_state) (level strategy : Z) : deflate_state :=
  let '(good, lazy, nice, chain) := configuration_table level in
  set_strategy (set_max_chain_length (set_nice_match (set_good_match (set_max_lazy_match (set_level X level) lazy) good) nice) chain) strategy.

(* [comment removed for export] *)
Definition dp_pre (X : deflate_state) : deflate_state :=
  if (ds_level X =? 0) && negb (ds_matches X =? 0) then set_matches (if ds_matches X =? 1 then slide_hash X else clear_hash X) 0 else X.

Lemma dp_set_level_eq : forall X level strategy,
  set_strategy (dparams_set_level X level) strategy = dp_tbl_st (dp_pre X) level strategy.
Proof.
  intros X level strategy. unfold dparams_set_level, dp_tbl_st, dp_pre.
  destruct ((ds_level X =? 0) && negb (ds_matches X =? 0)); [destruct (ds_matches X =? 1)|]; destruct (configuration_table level) as [[[g l] n] c]; reflexivity.
Qed.

Lemma u16s_zero : forall ws, Forall (fun w => w = wz 0) ws -> u16s ws = repeat (Z_to_bv 8 0) (2 * length ws).
Proof.
  induction ws as [|w ws IH]; intros H; [reflexivity|].
  inversion H; subst. cbn [u16s length]. rewrite IH by assumption.
  replace (2 * S (length ws))%nat with (S (S (2 * length ws))) by lia. reflexivity.
Qed.

Lemma av16_zero : forall a n, 0 <= n -> (forall i, 0 <= i < n -> arr_get a i = 0) -> Forall (fun w => w = wz 0) (av16 a n).
Proof.
  intros a n Hn H. apply Forall_forall. intros w Hw. apply In_nth_error in Hw. destruct Hw as [k Hk].
  assert (Hkl : (k < length (av16 a n))%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
  rewrite av16_length in Hkl.
  pose proof (av16_nth a n (Z.of_nat k) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite E in Hk. injection Hk as <-. rewrite H by lia. reflexivity.
Qed.

Lemma clear_hash_head : forall X, ds_hash_size X = 32768 -> arr_len (ds_head X) = 32768 ->
  u16s (av16 (ds_head (clear_hash X)) 32768) = repeat (Z_to_bv 8 0) (Z.to_nat 65536).
Proof.
  intros X HS HL. unfold clear_hash. dsred. rewrite HS.
  rewrite u16s_zero; [rewrite av16_length; f_equal; lia|].
  apply av16_zero; [lia|]. intros i Hi. rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_set, HL.
  destruct (Z_lt_le_dec i 32767).
  - replace ((0 <=? i) && (i <? 0 + Z.max 0 (32768 - 1)) && ((0 <=? i) && (i <? 32768))) with true by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
  - replace ((0 <=? i) && (i <? 0 + Z.max 0 (32768 - 1)) && ((0 <=? i) && (i <? 32768))) with false by (symmetry; rewrite !andb_false_iff, ?Z.ltb_ge; lia).
    rewrite arr_get_set. replace (32768 - 1 =? i) with true by (symmetry; apply Z.eqb_eq; lia).
    unfold arr_inb. rewrite HL. replace ((0 <=? 32768 - 1) && (32768 - 1 <? 32768)) with true by reflexivity. reflexivity.
Qed.

Lemma u16s_skipn : forall k ws, skipn (2 * k) (u16s ws) = u16s (skipn k ws).
Proof.
  induction k as [|k IH]; intros ws; [reflexivity|].
  destruct ws as [|w ws]; [rewrite skipn_nil; reflexivity|].
  replace (2 * S k)%nat with (S (S (2 * k))) by lia. cbn [u16s skipn app]. unfold le2, Z_to_le_bytes. cbn. apply IH.
Qed.

Lemma av16_last0 : forall a, arr_len a = 32768 ->
  skipn (Z.to_nat 65534) (u16s (av16 (arr_set a (32768 - 1) 0) 32768)) = [Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros a HL. replace (Z.to_nat 65534) with (2 * Z.to_nat 32767)%nat by lia. rewrite u16s_skipn.
  pose proof (av16_length (arr_set a (32768 - 1) 0) 32768) as LN.
  pose proof (av16_nth (arr_set a (32768 - 1) 0) 32768 32767 ltac:(lia)) as NT.
  rewrite arr_get_set in NT. replace (32768 - 1 =? 32767) with true in NT by reflexivity. unfold arr_inb in NT. rewrite HL in NT.
  replace ((0 <=? 32768 - 1) && (32768 - 1 <? 32768)) with true in NT by reflexivity. cbn [andb] in NT.
  remember (av16 (arr_set a (32768 - 1) 0) 32768) as ws eqn:Ews. clear Ews.
  rewrite <- (firstn_skipn (Z.to_nat 32767) ws) in NT. rewrite nth_error_app2 in NT by (rewrite length_firstn; lia).
  rewrite length_firstn in NT. replace (Z.to_nat 32767 - Nat.min (Z.to_nat 32767) (length ws))%nat with 0%nat in NT by lia.
  pose proof (length_skipn (Z.to_nat 32767) ws) as LS. rewrite LN in LS.
  destruct (skipn (Z.to_nat 32767) ws) as [|w [|w' l]]; cbn in LS; try lia.
  cbn in NT. injection NT as ->. reflexivity.
Qed.

Section DP.
Variables (L : dlay) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis HDEFL : deflate_in_stmtg.
Hypothesis HSLH : slide_hash_stmt.
Hypothesis CTX_lo : lo <= bv_unsigned (r_sp r) - (64 + Z_DEFLATE_IN_STACK).
Hypothesis CTX_sp16 : bv_unsigned (r_sp r) mod 16 = 0.
Hypothesis CTX_lay : dlay_ok L.
Hypothesis CTX_bel : dlay_below L lo (bv_unsigned (r_sp r)).
Hypothesis CTX_io : dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo.
Hypothesis CTX_relro : relro_clean me.
Hypothesis CTX_din : din me L inp.

(* [comment removed for export] *)
Definition DPI (fj : list byte) (X : deflate_state) (m : mem) : Prop :=
  DREP m L X /\ dout m L rest0 (ds_strm X) /\ Box (length (cs_out_rev (ds_strm X)) <= length rest0)%nat
  /\ rw_cells usegs m (bv_unsigned (r_sp r) + -64) [CB 8 fj; C8 (r_s5 r); C8 (r_s4 r); C8 (r_s3 r); C8 (r_s2 r); C8 (r_s1 r); C8 (r_s0 r); C8 (r_ra r)]
  /\ stk usegs m lo (bv_unsigned (r_sp r) + -64)
  /\ munch (defl_W L rest0 lo r) me m /\ wmono usegs me m /\ mem_inv usegs m.

(* [comment removed for export] *)
Definition KAT (Q : machine_state -> Prop) (pc : Z) (level strategy : Z) (X : deflate_state) : Prop :=
  forall (fj : list byte) (y1 y5 y6 y7 y9 y10 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 : word) (m' : mem),
    DPI fj X m' ->
    evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 y10 (wz level) (wz strategy) y13 y14 y15 y16 y17
                         (wz ZL_CFG_TABLE) (wz ZL_CFG_NOT) y20 y21 (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz pc) fc None m' (seg_rom usegs)).

Definition KATL (Q : machine_state -> Prop) (pc : Z) (level strategy : Z) (X : deflate_state) : Prop :=
  forall (fj : list byte) (y1 y5 y6 y7 y9 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 : word) (m' : mem),
    DPI fj X m' ->
    evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 (wz (ds_level X)) (wz level) (wz strategy) y13 y14 y15 y16 y17
                         (wz ZL_CFG_TABLE) (wz ZL_CFG_NOT) y20 y21 (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz pc) fc None m' (seg_rom usegs)).

(* [comment removed for export] *)
Definition KEP (Q : machine_state -> Prop) (rc : Z) (X : deflate_state) : Prop :=
  forall (fj : list byte) (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 : word) (m' : mem),
    DPI fj X m' ->
    evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 (wz rc) y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21
                     (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz ZL_DP_EPI) fc None m' (seg_rom usegs)).

Lemma DCTX_of : defl_ctx L inp rest0 lo r me.
Proof.
  unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in CTX_lo.
  constructor; [unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK; lia| exact CTX_sp16| exact CTX_lay| exact CTX_bel| exact CTX_io| exact CTX_relro| exact CTX_din].
Qed.

(* [comment removed for export] *)
Lemma dp_epi : forall rc X, - 2^31 <= rc < 2^31 ->
  KEP (deflate_in_post (r_ra r) (r_sp r) (r_gp r) (r_tp r) (r_s0 r) (r_s1 r) (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r)
                 F fc L X rc inp rest0 lo me) rc X.
Proof.
  intros rc X Rrc. unfold KEP. intros until m'. intros (DR & DOUT & _ & FR & STK & MU & WM & MI). unfold ZL_DP_EPI. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in CTX_lo.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (defl_din L inp rest0 lo r me DCTX_of m' MU) as DIN. unfold defl_W in MU.
  do 7 zs. release_frame FR STK (bv_unsigned (r_sp r)). zs. zs.
  apply evt_done. unfold deflate_in_post. do 14 eexists. exists m'.
  split; [rewrite Z_to_bv_mod64; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
  split; [exact DR|]. split; [exact DIN| exact DOUT].
Qed.

(* [comment removed for export] *)
Lemma dp_same : forall (Q : machine_state -> Prop) (strategy : Z) (X : deflate_state),
  0 <= strategy <= 1 ->
  KEP Q 0 (set_strategy X strategy) ->
  forall (fj : list byte) (y1 y5 y6 y7 y9 y10 y11 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 : word) (m' : mem),
    DPI fj X m' ->
    evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 y10 y11 (wz strategy) y13 y14 y15 y16 y17
                         y18 y19 y20 y21 (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz ZL_DP_SAME) fc None m' (seg_rom usegs)).
Proof.
  intros Q strategy X RS1 KE. unfold ZL_DP_SAME. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in CTX_lo.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1]. open_A GA.
  pose proof CTX_lay as LAY. lay_open LAY. pose proof CTX_bel as BEL. below_open BEL. pose proof CTX_io as I0. io_open I0. unfold defl_W in MU.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] m') as MUf. pose proof (wmono_refl usegs m') as WMf.
  zs. zs. name_mem mB. zs.
  tr_groups MUf WMf.
  unfold KEP, ZL_DP_EPI in KE. apply (KE fj).
  split; [split|].
  - exact ZS.
  - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  - split; [dsred; apply (dout_munch _ m' mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
    split; [dsred; exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

(* [comment removed for export] *)
Lemma dp_tbl : forall (Q : machine_state -> Prop) (level strategy : Z) (X : deflate_state),
  0 <= level <= 9 -> 0 <= strategy <= 1 ->
  KEP Q 0 (dp_tbl_st X level strategy) ->
  KAT Q ZL_DP_TBL level strategy X.
Proof.
  intros Q level strategy X RL9 RS1 KE. unfold KAT, ZL_DP_TBL. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in CTX_lo.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1]. open_A GA.
  pose proof CTX_lay as LAY. lay_open LAY. pose proof CTX_bel as BEL. below_open BEL. pose proof CTX_io as I0. io_open I0. unfold defl_W in MU.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] m') as MUf. pose proof (wmono_refl usegs m') as WMf.
  unfold ZL_CFG_TABLE, ZL_CFG_NOT.
  zstep. rewrite (Z.shiftl_mul_pow2 level 4) by lia. change (2^4) with 16.
  (* [comment removed for export] *)
  zs. name_mem m1.
  assert (RLP1 : relro_clean m1) by (apply (defl_relro L inp rest0 lo r me DCTX_of); exact MU).
  pose proof (cfgL_row m1 level RLP1 RL9) as ROW. unfold ZL_CFG_TABLE, cfg_row_cells in ROW.
  destruct (configuration_table level) as [[[good lazy] nice] chain] eqn:ECT.
  assert (RT : 0 <= good < 65536 /\ 0 <= lazy < 65536 /\ 0 <= nice < 65536 /\ 0 <= chain < 65536).
  { assert (C : level = 0 \/ level = 1 \/ level = 2 \/ level = 3 \/ level = 4 \/ level = 5 \/ level = 6 \/ level = 7 \/ level = 8 \/ level = 9) by lia.
    destruct C as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]; rewrite E in ECT; cbn in ECT; injection ECT as <- <- <- <-; lia. }
  zstep. if_cases KG; zify_cond KG; rewrite ?unsigned_lit in KG by lia; try (exfalso; lia).
  zstep.
  replace (180824 + 16 * level) with (180824 + level * 16) in ROW by lia.
  pose proof (rw_cells_read_at usegs m1 (180824 + level * 16) [C2 (wz good); C2 (wz lazy); C2 (wz nice); C2 (wz chain)] 0%nat (C2 (wz good)) 2 (wz (180824 + level * 16))
                ROW eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as HR0.
  zs. zs. zs. clear HR0. zs.
  rewrite ?(zx16_small good), ?(zx16_small lazy), ?(zx16_small nice), ?(zx16_small chain) by lia.
  zs. zs. zs. zs. name_mem mB.
  tr_groups MUf WMf.
  unfold dp_tbl_st in KE. rewrite ECT in KE.
  eapply (dp_same Q strategy _ RS1 KE).
  split; [split; [exact ZS|]|].
  - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  - split; [dsred; apply (dout_munch _ m' mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
    split; [dsred; exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

(* [comment removed for export] *)
Lemma dp_flush : forall (Q : machine_state -> Prop) (level strategy : Z) (d : deflate_state),
  0 <= level <= 9 -> 0 <= strategy <= 1 ->
  defl_pathg inp 5 (deflate_core d 5) d ->
  (let X1 := fst (deflate_core d 5) in
   0 <= cs_avail_in (ds_strm X1) < 2^31 /\ 0 <= ds_strstart X1 < 2^32 /\ 0 <= ds_lookahead X1 < 2^32 /\ - 2^62 <= ds_block_start X1 < 2^62
   /\ Box (length (cs_out_rev (ds_strm X1)) <= length rest0)%nat /\ - 5 <= snd (deflate_core d 5) <= 1) ->
  (snd (deflate_core d 5) <> -2 -> cs_avail_in (ds_strm (fst (deflate_core d 5))) = 0 ->
     (ds_strstart (fst (deflate_core d 5)) - ds_block_start (fst (deflate_core d 5))) + ds_lookahead (fst (deflate_core d 5)) = 0 ->
     0 <= ds_level (fst (deflate_core d 5)) <= 9) ->
  (snd (deflate_core d 5) = -2 -> KEP Q (-2) (fst (deflate_core d 5))) ->
  (snd (deflate_core d 5) <> -2 ->
     (cs_avail_in (ds_strm (fst (deflate_core d 5))) <> 0 \/ (ds_strstart (fst (deflate_core d 5)) - ds_block_start (fst (deflate_core d 5))) + ds_lookahead (fst (deflate_core d 5)) <> 0) ->
     KEP Q (-5) (fst (deflate_core d 5))) ->
  (snd (deflate_core d 5) <> -2 -> cs_avail_in (ds_strm (fst (deflate_core d 5))) = 0 ->
     (ds_strstart (fst (deflate_core d 5)) - ds_block_start (fst (deflate_core d 5))) + ds_lookahead (fst (deflate_core d 5)) = 0 ->
     ds_level (fst (deflate_core d 5)) <> level ->
     KATL Q ZL_DP_LVNE level strategy (fst (deflate_core d 5))) ->
  (snd (deflate_core d 5) <> -2 -> cs_avail_in (ds_strm (fst (deflate_core d 5))) = 0 ->
     (ds_strstart (fst (deflate_core d 5)) - ds_block_start (fst (deflate_core d 5))) + ds_lookahead (fst (deflate_core d 5)) = 0 ->
     ds_level (fst (deflate_core d 5)) = level ->
     forall (fj : list byte) (y1 y5 y6 y7 y9 y10 y11 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 : word) (m' : mem),
       DPI fj (fst (deflate_core d 5)) m' ->
       evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 y10 y11 (wz strategy) y13 y14 y15 y16 y17
                         y18 y19 y20 y21 (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz ZL_DP_SAME) fc None m' (seg_rom usegs))) ->
  forall (fj : list byte) (y1 y5 y6 y7 y10 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 : word) (m' : mem),
    DPI fj d m' ->
    evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz (dl_S L)) y10 (wz level) (wz strategy) y13 y14 y15 y16 y17
                         (wz ZL_CFG_TABLE) (wz ZL_CFG_NOT) y20 y21 (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz ZL_DP_FLUSH) fc None m' (seg_rom usegs)).
Proof.
  intros Q level strategy d RL9 RS1 PATH FACTS RLX1 KM2 KM5 KOKne KOKeq. cbv zeta in FACTS. destruct FACTS as (RAI1 & RSS1 & RLA1 & RBS1 & ROOM1 & RRC).
  unfold ZL_DP_FLUSH. intros until m'. intros DI. pose proof DI as (DR & DOUT & ROOM & FR & STK & MU & WM & MI). unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in CTX_lo.
  assert (RLP : relro_clean m') by (apply (defl_relro L inp rest0 lo r me DCTX_of); exact MU).
  pose proof (defl_din L inp rest0 lo r me DCTX_of m' MU) as DIN.
  pose proof CTX_lay as LAY. lay_open LAY. pose proof CTX_bel as BEL. below_open BEL. pose proof CTX_io as I0. io_open I0. unfold defl_W in MU.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
  zstep. zstep. zs. zstep.
  zstep. call (HDEFL L d 5 inp rest0 lo).
  1:{ exact DR. } 1:{ exact DIN. } 1:{ exact DOUT. } 1:{ exact MI. } 1:{ exact RLP. } 1:{ rewrite ESP. exact STK. }
  1:{ rewrite ESP. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact CTX_io. } 1:{ right. right. reflexivity. } 1:{ exact PATH. } 1:{ exact (unbox _ ROOM1). } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem mA.
  lazymatch goal with H : stk usegs mA _ _ |- _ => rewrite ?ESP in H; rename H into STKA end.
  lazymatch goal with H : DREP mA L _ |- _ => rename H into DRA end.
  lazymatch goal with H : dout mA L _ _ |- _ => rename H into DOA end.
  revert RAI1 RSS1 RLA1 RBS1 ROOM1 RRC RLX1 KM2 KM5 KOKne KOKeq DRA DOA. generalize (snd (deflate_core d 5)) as rc. generalize (fst (deflate_core d 5)) as X1.
  intros X1 rc RAI1 RSS1 RLA1 RBS1 ROOM1 RRC RLX1 KM2 KM5 KOKne KOKeq DRA DOA.
  assert (DIA : DPI fj X1 mA).
  { split; [exact DRA|]. split; [exact DOA|]. split; [exact ROOM1|]. split; [exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  pose proof DRA as [ZSA STA]. destruct STA as [GAA GBA GCA GDA GltA GdtA GbtA GblcA GheapA GdepA GwinA GprevA GheadA GpendA LENSA LAYA]. open_zs ZSA. open_A GAA.
  rewrite Z_to_bv_mod64.
  zstep. zstep. zstep. if_cases KRC; zify_cond KRC; rewrite ?signed_wz, ?unsigned_lit in KRC by lia.
  - (* [comment removed for export] *)
    unfold KEP, ZL_DP_EPI in KM2. eapply (KM2 ltac:(lia)). exact DIA.
  - zs. zstep. zstep. if_cases KAI; zify_cond KAI; rewrite ?signed_wz, ?unsigned_lit in KAI by lia.
    + unfold KEP, ZL_DP_EPI in KM5. eapply (KM5 ltac:(lia) ltac:(left; lia)). exact DIA.
    + zs. zs. zstep. zstep. zstep.
      rewrite (sgn_guard0 (ds_block_start X1)) by lia. rewrite (sub_guard (ds_strstart X1) (ds_block_start X1)) by lia.
      zstep. rewrite bv_eqb_refl. change (negb true) with false. cbv iota.
      zs. zstep. zstep. rewrite (add_guard (ds_strstart X1) (ds_block_start X1) (ds_lookahead X1)) by lia.
      zstep. change (0 + 9223372036854775808) with 9223372036854775808. rewrite (slti0_false (ds_lookahead X1)) by lia.
      zstep. rewrite bv_eqb_refl. change (negb true) with false. cbv iota.
      zstep. if_cases KSUM; zify_cond KSUM; rewrite ?unsigned_lit in KSUM by lia.
      * unfold KEP, ZL_DP_EPI in KM5. eapply (KM5 ltac:(lia) ltac:(right; clear - KSUM RSS1 RLA1 RBS1; Z.div_mod_to_equations; lia)). exact DIA.
      * assert (HSUM : ds_strstart X1 - ds_block_start X1 + ds_lookahead X1 = 0) by (clear - KSUM RSS1 RLA1 RBS1; Z.div_mod_to_equations; lia).
        assert (AI0 : cs_avail_in (ds_strm X1) = 0) by lia. assert (NRC : rc <> -2) by lia.
        pose proof (RLX1 NRC AI0 HSUM) as RLX. assert (RLX' : - 2^31 <= ds_level X1 < 2^31) by lia.
        zstep. zstep. zs. zstep. if_cases KLV; zify_cond KLV; rewrite ?signed_wz, ?unsigned_lit in KLV by lia.
        -- unfold KATL, ZL_DP_LVNE in KOKne. eapply (KOKne NRC AI0 HSUM ltac:(lia)). exact DIA.
        -- zstep. unfold ZL_DP_SAME in KOKeq. eapply (KOKeq NRC AI0 HSUM ltac:(lia)). exact DIA.
Qed.

(* [comment removed for export] *)
Lemma dp_lvne : forall (Q : machine_state -> Prop) (level strategy : Z) (X : deflate_state),
  0 <= level <= 9 -> 0 <= strategy <= 1 -> 0 <= ds_level X <= 9 -> 0 <= ds_matches X < 2^31 -> ds_level X <> level ->
  (ds_level X = 0 -> ds_matches X <> 0 ->
     ds_w_size X = 32768 /\ ds_hash_size X = 32768
     /\ (forall i, 0 <= i < 32768 -> 0 <= arr_get (ds_head X) i < 65536)
     /\ (forall i, 0 <= i < 32768 -> 0 <= arr_get (ds_prev X) i < 65536)) ->
  KEP Q 0 (set_strategy (dparams_set_level X level) strategy) ->
  KATL Q ZL_DP_LVNE level strategy X.
Proof.
  intros Q level strategy X RL9 RS1 RLX RMX NE HF KNE. unfold KATL, ZL_DP_LVNE. intros until m'. intros DI.
  pose proof DI as (DR & DOUT & ROOM & FR & STK & MU & WM & MI). unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in CTX_lo.
  pose proof DR as DR0. destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1]. open_A GA. open_D GD.
  pose proof CTX_lay as LAY. lay_open LAY. pose proof CTX_bel as BEL. below_open BEL. pose proof CTX_io as I0. io_open I0. unfold defl_W in MU.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (RLX' : - 2^31 <= ds_level X < 2^31) by lia. assert (RMX' : - 2^31 <= ds_matches X < 2^31) by lia.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] m') as MUf. pose proof (wmono_refl usegs m') as WMf.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ah L, dl_Ah L + 65536)] m') as MUh. pose proof (wmono_refl usegs m') as WMh.
  rewrite dp_set_level_eq in KNE.
  (* [comment removed for export] *)
  pose proof (dp_tbl Q level strategy (dp_pre X) RL9 RS1 KNE) as TBL. unfold KAT, ZL_DP_TBL in TBL.
  zstep. if_cases KL0; zify_cond KL0; rewrite ?signed_wz, ?unsigned_lit in KL0 by lia.
  - (* [comment removed for export] *)
    eapply TBL. unfold dp_pre. replace (ds_level X =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. exact DI.
  - (* [comment removed for export] *)
    zstep. zstep. zstep. zs. zstep. if_cases KM0; zify_cond KM0; rewrite ?signed_wz, ?unsigned_lit in KM0 by lia.
    + eapply TBL. unfold dp_pre. replace (ds_matches X =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite Bool.andb_false_r. exact DI.
    + destruct (HF ltac:(lia) ltac:(lia)) as (WS & HS & RH & RP).
      assert (EPRE : dp_pre X = set_matches (if ds_matches X =? 1 then slide_hash X else clear_hash X) 0).
      { unfold dp_pre. replace (ds_level X =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        replace (ds_matches X =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      zstep. zstep. if_cases KM1; zify_cond KM1; rewrite ?signed_wz, ?unsigned_lit in KM1 by lia.
      * (* [comment removed for export] *)
        replace (ds_matches X =? 1) with false in EPRE by (symmetry; apply Z.eqb_neq; lia).
        pose proof (ln_head _ LENS) as Lhead. open_u16 Ghead.
        assert (AH2 : 2 <= dl_Ah L /\ dl_Ah L mod 2 = 0) by (pose proof (lo_h _ LAY) as BH; unfold blk_ok in BH; clear - BH; Z.div_mod_to_equations; lia).
        zs. rewrite HS. zs. zs. zs. zs. zstep. gF. zstep. zstep. zstep. gX. gF.
        zstep. zstep. al2 (dl_Ah L + 65534). gF. zstep.
        st16u Ghead (ds_head X) 32768 (dl_Ah L) (32768 - 1) 0 ltac:(reflexivity).
        name_mem m1.
        assert (LHB : Z.of_nat (length (u16s (av16 (arr_set (ds_head X) (32768 - 1) 0) 32768))) = 65536) by (rewrite u16s_length, av16_length; lia).
        destruct (u8arr_split3 _ (dl_Ah L) _ (Z.to_nat 0) (Z.to_nat 65534) Ghead ltac:(lia)) as (_ & O2 & O3). clear Ghead.
        rewrite !Z2Nat.id in O2 by lia. rewrite !Z2Nat.id in O3 by lia. rewrite Z.add_0_r in O2.
        assert (LO3 : Z.of_nat (length (skipn (Z.to_nat 0 + Z.to_nat 65534) (u16s (av16 (arr_set (ds_head X) (32768 - 1) 0) 32768)))) = 2) by (rewrite length_skipn; lia).
        clear MUf WMf.
        zstep. zstep.
        lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
          eapply evt_cut; [eapply memset_callZ with (D := dl_Ah L) (C := 0) (N := 65534); [exact O2| eassumption| lia| lia| lia| lia] | post_call segs mm] end.
        name_mem m2.
        replace (Z.to_nat 0 + Z.to_nat 65534)%nat with (Z.to_nat 65534) in O3 by lia. rewrite (av16_last0 (ds_head X) Lhead) in O3.
        change (Z_to_bv 8 (0 mod 256)) with (Z_to_bv 8 0) in POST.
        replace (dl_Ah L + 0 + 65534) with (dl_Ah L + 65534) in O3 by lia.
        pose proof (u8arr_join2z m2 (dl_Ah L) (repeat (Z_to_bv 8 0) (Z.to_nat 65534)) [Z_to_bv 8 0; Z_to_bv 8 0] 65534 ltac:(rewrite repeat_length; lia) POST O3) as HD. clear POST O3.
        replace (repeat (Z_to_bv 8 0) (Z.to_nat 65534) ++ [Z_to_bv 8 0; Z_to_bv 8 0]) with (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) in HD
          by (replace (Z.to_nat 65536) with (Z.to_nat 65534 + 2)%nat by lia; rewrite repeat_app; reflexivity).
        rewrite <- (clear_hash_head X HS Lhead) in HD.
        assert (L16H : Z.of_nat (length (u16s (av16 (ds_head (clear_hash X)) 32768))) = 2 * 32768) by (rewrite u16s_length, av16_length; lia).
        zs. zs. zstep. zstep. name_mem m3.
        tr_groups MUh WMh.
        eapply TBL. rewrite EPRE.
        split; [split; [exact ZS|]|].
        -- constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                        | exact Gwin| exact Gprev| unfold dhead, u16arr; dsred; exact HD| exact Gpend| | exact LAY1].
           destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
           constructor; dsred; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9|exact l10|exact l11| unfold clear_hash; dsred; rewrite arr_len_fill, arr_len_set; exact l12|exact l13].
        -- split; [dsred; rewrite strm_clear_hash; apply (dout_munch _ m' m3 L rest0 _ DOUT ROOM MUh WMh); cbn [disjoint_from]; slia|].
           split; [dsred; rewrite strm_clear_hash; exact ROOM|]. split; [exact FR|]. split; [eassumption|]. split; [exact MU|]. split; [exact WM| eassumption].
      * (* [comment removed for export] *)
        replace (ds_matches X =? 1) with true in EPRE by (symmetry; apply Z.eqb_eq; lia).
        pose proof DR0 as [_ ST0]. clear MUh WMh.
        zstep. zstep. zs. zstep. eapply evt_cut; [eapply HSLH; [exact ST0| eassumption| exact WS| exact HS| exact RH| exact RP| reflexivity] | ].
        intros ms' PSH. unfold slide_hash_post in PSH. destruct PSH as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & EQ & MUc & WMc & MIc & ST2). subst ms'. replace (ret_pc (wz 94488)) with (wz 94488) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968)] m2) as MUg. pose proof (wmono_refl usegs m2) as WMg.
        destruct ST2 as [GA2 GB2 GC2 GD2 Glt2 Gdt2 Gbt2 Gblc2 Gheap2 Gdep2 Gwin2 Gprev2 Ghead2 Gpend2 LENS2 LAY2].
        zstep.
        pose proof GD2 as GD2c. unfold dsD in GD2c. destruct GD2c as (h0 & h1 & h2 & h3 & h4 & GD2r).
        pose proof (rw_cells_store_ok_at usegs m2 (dl_As L + 5881) _ 47%nat _ 4%nat (wz (dl_As L + 5928)) GD2r ltac:(cbn; reflexivity) ltac:(cbn; reflexivity) ltac:(f_equal; cbn; lia)) as SOK5928.
        zs.
        pose proof (rw_cells_write usegs m2 (dl_As L + 5881) _ 47%nat _ (C4 (wz 0)) GD2r ltac:(cbn; reflexivity) ltac:(cbn; reflexivity) ltac:(cbn [cell_wf]; repeat split; try lia; try exact I)) as RW3X.
        replace (dl_As L + 5881 + Z.of_nat 47) with (dl_As L + 5928) in RW3X by (cbn; lia).
        change (rw_cells usegs (write_to_mem m2 (wz (dl_As L + 5928)) (le4 (wz 0))) (dl_As L + 5881) (cell_upd (dsD_cells L (slide_hash X) h0 h1 h2 h3 h4) 47 (C4 (wz 0)))) in RW3X.
        zstep. zstep. remember (write_to_mem m2 (wz (dl_As L + 5928)) (le4 (wz 0))) as m3 eqn:HM3.
        pose proof RW3X as RW3.
        pose proof (lo_Ss L CTX_lay) as APS. unfold apart in APS.
        clear MUg WMg.
        assert (MUg : munch [(dl_As L + 5881, dl_As L + 5968)] m2 m3) by (pose proof (dlay_ranges L CTX_lay) as DRG; destruct DRG as [[P1 P2] _]; rewrite HM3; apply munch_write; [apply munch_refl | lia | simpl; lia | cbn [inside]; left; split; [lia | simpl; lia]]).
        assert (WMg : wmono usegs m2 m3) by (rewrite HM3; apply wmono_write; apply wmono_refl).
        tr_groups MUg WMg. tr_groups MUf WMf.
        pose proof (dzs_munch m' m2 L _ (ds_strm X) ZS MUc WMc ltac:(cbn [disjoint_from]; slia)) as ZS2.
        pose proof (dzs_munch m2 m3 L _ (ds_strm X) ZS2 MUg WMg ltac:(cbn [disjoint_from]; slia)) as ZS3.
        assert (SUB1 : sub_fp [(dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_As L + 5960, dl_As L + 5964)] [(dl_As L + 5881, dl_As L + 5968); (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_As L + 5960, dl_As L + 5964)]) by (unfold sub_fp; intros x Hx; cbn [outside] in *; tauto).
        assert (SUB2 : sub_fp [(dl_As L + 5881, dl_As L + 5968)] [(dl_As L + 5881, dl_As L + 5968); (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_As L + 5960, dl_As L + 5964)]) by (unfold sub_fp; intros x Hx; cbn [outside] in *; tauto).
        pose proof (munch_trans _ _ _ _ (munch_weaken _ _ _ _ SUB1 MUc) (munch_weaken _ _ _ _ SUB2 MUg)) as MUF3.
        pose proof (wmono_trans usegs m' m2 m3 WMc WMg) as WMF3.
        pose proof (stk_transport_disjoint usegs [(dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_As L + 5960, dl_As L + 5964)] m' m2 lo (bv_unsigned (r_sp r) + -64) STK MUc WMc ltac:(cbn [disjoint_from]; slia)) as STK2.
        assert (STK3 : stk usegs m3 lo (bv_unsigned (r_sp r) + -64)) by (pose proof (dlay_ranges L CTX_lay) as DRG; destruct DRG as [[P1 P2] _]; rewrite HM3; apply stk_write; [exact STK2 | lia | simpl; lia]).
        assert (MI3 : mem_inv usegs m3) by (rewrite HM3; apply mem_inv_store; [exact MIc | first [exact SOK5928 | (cbn; exact SOK5928)]]).
        assert (SUB3 : sub_fp [(dl_As L + 5881, dl_As L + 5968); (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_As L + 5960, dl_As L + 5964)] (defl_W L rest0 lo r)).
        { unfold sub_fp, defl_W. intros x Hx. cbn [outside] in *. intuition lia. }
        pose proof (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB3 MUF3)) as MU3.
        pose proof (wmono_trans usegs _ _ _ WM WMF3) as WM3.
        pose proof (rw_cells_agree m' m3 (bv_unsigned (r_sp r) + -64) _ FR ltac:(apply (agree_on_of_munch [(dl_As L + 5881, dl_As L + 5968); (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_As L + 5960, dl_As L + 5964)]); [exact MUF3| exact WMF3| lia| cbn [cells_size csize]; lia| cbn [disjoint_from]; slia])) as FR3.
        eapply TBL. rewrite EPRE.
        split; [split; [first [exact ZS | (dsred; exact ZS3)]|]|].
        -- constructor; [exact GA2| exact GB2| exact GC2| exists h0, h1, h2, h3, h4; unfold dsD_cells; dsred; eapply rw_cells_sim; [exact RW3| unfold dsD_cells; simpl cell_upd; simpl; cells_sim_tac]| exact Glt2| exact Gdt2| exact Gbt2| exact Gblc2| exact Gheap2| exact Gdep2
                        | exact Gwin2| exact Gprev2| exact Ghead2| exact Gpend2| close_lens LENS2 | exact LAY2].
        -- split; [dsred; rewrite strm_slide_hash; apply (dout_munch _ m' m3 L rest0 _ DOUT ROOM MUF3 WMF3); cbn [disjoint_from]; slia|].
           split; [dsred; rewrite strm_slide_hash; exact ROOM|]. split; [exact FR3|]. split; [exact STK3|]. split; [exact MU3|]. split; [exact WM3| exact MI3].
Qed.

(* [comment removed for export] *)
Lemma dp_lv : forall (Q : machine_state -> Prop) (level strategy : Z) (X : deflate_state),
  0 <= level <= 9 -> 0 <= strategy <= 1 -> 0 <= ds_level X <= 9 ->
  (ds_level X = level -> KEP Q 0 (set_strategy X strategy)) ->
  (ds_level X <> level -> KATL Q ZL_DP_LVNE level strategy X) ->
  KATL Q ZL_DP_LV level strategy X.
Proof.
  intros Q level strategy X RL9 RS1 RLX KEQ KNE. unfold KATL, ZL_DP_LV. intros until m'. intros DI.
  assert (RLX' : - 2^31 <= ds_level X < 2^31) by lia.
  zstep. if_cases KE; zify_cond KE; rewrite ?signed_wz, ?unsigned_lit in KE by lia.
  - eapply (dp_same Q strategy X RS1 (KEQ ltac:(lia))). exact DI.
  - unfold KATL, ZL_DP_LVNE in KNE. eapply (KNE ltac:(lia)). exact DI.
Qed.

(* [comment removed for export] *)
Definition KFL (Q : machine_state -> Prop) (level strategy : Z) (X : deflate_state) : Prop :=
  forall (fj : list byte) (y1 y5 y6 y7 y10 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 : word) (m' : mem),
    DPI fj X m' ->
    evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz (dl_S L)) y10 (wz level) (wz strategy) y13 y14 y15 y16 y17
                         (wz ZL_CFG_TABLE) (wz ZL_CFG_NOT) y20 y21 (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz ZL_DP_FLUSH) fc None m' (seg_rom usegs)).

Lemma dp_front : forall Q level strategy d t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  DREP me L d -> dout me L rest0 (ds_strm d) -> Box (length (cs_out_rev (ds_strm d)) <= length rest0)%nat ->
  stk usegs me lo (bv_unsigned (r_sp r)) -> mem_inv usegs me ->
  (ds_status d = 42 \/ ds_status d = 113 \/ ds_status d = 666) -> 0 <= level <= 9 -> 0 <= strategy <= 1 ->
  0 <= ds_level d <= 9 -> 0 <= ds_strategy d < 2^31 -> - 2 <= ds_last_flush d <= 5 ->
  (dparams_flushes d level strategy = false -> KATL Q ZL_DP_LV level strategy d) ->
  (dparams_flushes d level strategy = true -> KFL Q level strategy d) ->
  evt usegs Q (MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) (wz (dl_S L)) (wz level) (wz strategy) a3 a4 a5 a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
                  F (wz ZL_DEFLATEPARAMS) fc None me (seg_rom usegs)).
Proof.
  intros until t6. intros DR DOUT ROOM STK MI HST RL9 RS1 RLV RSG RLF KLV KFLH. unfold ZL_DEFLATEPARAMS. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in CTX_lo.
  pose proof DR as DR0. destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA. pose proof CTX_lay as LAY. lay_open LAY. pose proof CTX_bel as BEL. below_open BEL. pose proof CTX_io as I0. io_open I0.
  pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs. pose proof (lo_S _ LAY) as BKS.
  unfold Z_ZCALLOC, Z_ZCFREE in ZS.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl (defl_W L rest0 lo r) me) as MU. unfold defl_W in MU. pose proof (wmono_refl usegs me) as WM.
  pose proof (munch_refl [(lo, bv_unsigned (r_sp r))] me) as MUf. pose proof (wmono_refl usegs me) as WMf.
  assert (RST : - 2^31 <= ds_status d < 2^31) by lia.
  assert (RLV' : - 2^31 <= ds_level d < 2^31) by lia. assert (RSG' : - 2^31 <= ds_strategy d < 2^31) by lia. assert (RLF' : - 2^31 <= ds_last_flush d < 2^31) by lia.
  carve_frame 64%nat STK.
  do 8 zs. name_mem mP. zs. zs.
  zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; lia|].
  zstep. al8 (dl_S L). gF.
  zs. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [exfalso; lia|].
  zs. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [exfalso; lia|].
  zs. zstep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia; [exfalso; lia|].
  zstep. al8 (dl_As L). gF.
  zs. zstep. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia; [| exfalso; lia].
  clear K1 K2 K3 K4 K5.
  assert (RLP : relro_clean mP) by (apply (defl_relro L inp rest0 lo r me DCTX_of); unfold defl_W; exact MU).
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?x :: _) => set (fj := x) in FR end.
  assert (DIP : DPI fj d mP).
  { split; [| split; [| split; [exact ROOM| split; [exact FR| split; [exact STK| split; [exact MU| split; [exact WM| eassumption]]]]]]].
    - apply (DREP_agree me mP L d DR0).
      + eapply ag_blocks_munch; [exact LAY1| exact MUf| exact WMf| | | | |]; cbn [disjoint_from]; slia.
      + apply (agree_on_of_munch [(lo, bv_unsigned (r_sp r))]); [exact MUf| exact WMf| lia| lia| cbn [disjoint_from]; slia].
    - apply (dout_munch _ me mP L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia. }
  (* [comment removed for export] *)
  assert (C80 : forall (x13 x14 x15 : word),
    evt usegs Q (MS (mkR (r_ra r) (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) t0 t1 t2 (wz (dl_As L)) (wz (dl_S L)) (wz (-2)) (wz level) (wz strategy) x13 x14 x15 a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6) F (wz 0x17078) fc None mP (seg_rom usegs))).
  { intros x13 x14 x15.
    zs. zstep. if_cases K6; zify_cond K6; rewrite ?signed_wz, ?unsigned_lit in K6 by lia; [| exfalso; lia].
    zs. zstep. if_cases K7; zify_cond K7; rewrite ?unsigned_lit in K7 by lia; [exfalso; lia|].
    zs. zstep. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by lia; [exfalso; lia|].
    (* [comment removed for export] *)
    zs. zs. zstep. if_cases K9; zify_cond K9; rewrite ?signed_wz, ?unsigned_lit in K9 by lia; try (exfalso; lia).
    zstep. rewrite (Z.shiftl_mul_pow2 (ds_level d) 4) by lia. change (2^4) with 16.
    zs. zs. zstep.
    zstep. if_cases KG1; zify_cond KG1; rewrite ?signed_wz, ?unsigned_lit in KG1 by lia; try (exfalso; lia).
    pose proof (cfunc_addr_cases (ds_level d)) as CA1. pose proof (cfunc_addr_cases level) as CA2. unfold ZL_DEFLATE_STORED, ZL_DEFLATE_FAST, ZL_DEFLATE_SLOW in CA1, CA2.
    assert (RCA1 : 0 <= cfunc_addr (ds_level d) < 2^32) by lia. assert (RCA2 : 0 <= cfunc_addr level < 2^32) by lia.
    (* [comment removed for export] *)
    assert (C_E0 : (strategy <> ds_strategy d \/ cfunc_addr (ds_level d) <> cfunc_addr level) -> forall (x13' x14' : word),
      evt usegs Q (MS (mkR (r_ra r) (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) t0 t1 t2 (wz (dl_As L)) (wz (dl_S L)) (wz (ds_level d)) (wz level) (wz strategy) x13' x14' x15 a6 a7
                         (wz 180824) (wz 18446744073709370791) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6) F (wz 0x170d8) fc None mP (seg_rom usegs))).
    { intros HCH x13' x14'.
      zs. zs. zstep. if_cases KLF; zify_cond KLF; rewrite ?signed_wz, ?unsigned_lit in KLF by lia.
      - (* [comment removed for export] *)
        unfold KFL, ZL_DP_FLUSH, ZL_CFG_TABLE, ZL_CFG_NOT in KFLH. eapply KFLH; [| exact DIP].
        unfold dparams_flushes. replace (ds_last_flush d =? -2) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].
        rewrite <- cfunc_addr_eqb. destruct HCH as [NE|NE].
        + replace (strategy =? ds_strategy d) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
        + replace (cfunc_addr (ds_level d) =? cfunc_addr level) with false by (symmetry; apply Z.eqb_neq; exact NE). rewrite Bool.orb_true_r. reflexivity.
      - (* [comment removed for export] *)
        unfold KATL, ZL_DP_LV, ZL_CFG_TABLE, ZL_CFG_NOT in KLV. eapply KLV; [| exact DIP].
        unfold dparams_flushes. replace (ds_last_flush d =? -2) with true by (symmetry; apply Z.eqb_eq; lia). rewrite Bool.andb_false_r. reflexivity. }
    zs. zstep. if_cases KST; zify_cond KST; rewrite ?signed_wz, ?unsigned_lit in KST by lia.
    - (* [comment removed for export] *) apply C_E0. left. lia.
    - (* [comment removed for export] *)
      pose proof (cfgL_func mP (ds_level d) RLP ltac:(lia)) as CF1. pose proof (cfgL_func mP level RLP ltac:(lia)) as CF2. unfold ZL_CFG_TABLE in CF1, CF2.
      zstep. rewrite (Z.shiftl_mul_pow2 level 4) by lia. change (2^4) with 16.
      zstep. if_cases KG2; zify_cond KG2; rewrite ?signed_wz, ?unsigned_lit in KG2 by lia; try (exfalso; lia).
      replace (180824 + 16 * ds_level d + 8) with (180824 + ds_level d * 16 + 8) in CF1 by lia.
      replace (180824 + 16 * level + 8) with (180824 + level * 16 + 8) in CF2 by lia.
      zs. zs. zs. zs.
      zstep. if_cases KFN; zify_cond KFN; rewrite ?unsigned_lit in KFN by lia.
      + (* [comment removed for export] *)
        unfold KATL, ZL_DP_LV, ZL_CFG_TABLE, ZL_CFG_NOT in KLV. eapply KLV; [| exact DIP].
        unfold dparams_flushes. rewrite <- cfunc_addr_eqb.
        replace (strategy =? ds_strategy d) with true by (symmetry; apply Z.eqb_eq; lia).
        replace (cfunc_addr (ds_level d) =? cfunc_addr level) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
      + apply C_E0. right. lia. }
  (* [comment removed for export] *)
  zs. zs. zs. zstep.
  destruct HST as [E|[E|E]]; rewrite E in *.
  - (* [comment removed for export] *)
    if_cases KS; zify_cond KS; [|exfalso; revert KS; vm_compute; intros KS; apply KS; reflexivity].
    zs. zstep. closed_br. apply C80.
  - (* [comment removed for export] *)
    if_cases KS; zify_cond KS; [exfalso; revert KS; vm_compute; intros KS; discriminate KS|].
    zs. zs. zs. zs. zstep.
    if_cases KM; zify_cond KM; [exfalso; revert KM; vm_compute; intros KM; discriminate KM|].
    apply C80.
  - (* [comment removed for export] *)
    if_cases KS; zify_cond KS; [|exfalso; revert KS; vm_compute; intros KS; apply KS; reflexivity].
    zs. zstep. closed_br. zs. zstep. closed_br. zstep. apply C80.
Qed.
End DP.


(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem deflateParams_spec : deflate_in_stmtg -> slide_hash_stmt -> deflateParams_in_stmt.
Proof.
  intros HDEFL HSLH. unfold deflateParams_in_stmt. intros until m. intros DR DIN DOUT MI RL STK LO SP16 BEL IO PATH ROOM -> -> ->.
  revert PATH ROOM. generalize (deflateParams_core d level strategy) as R. intros R PATH ROOM.
  destruct PATH as (HST & RLV & RSG & RLF & RL9 & RS1 & PFL & PNF).
  set (r := mkSR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  pose proof (st_lay _ _ _ _ (proj2 DR)) as LAY. unfold Z_DPARAMS_STACK in LO.
  change sp with (r_sp r) in LO, SP16, BEL, STK.
  set (Q := deflate_in_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (fst R) (snd R) inp rest0 lo m).
  (* [comment removed for export] *)
  assert (KX : forall X rc, R = (X, rc) -> - 2^31 <= rc < 2^31 -> KEP L rest0 lo r F fc m Q rc X).
  { intros X rc ER Rrc. unfold KEP. intros until m'. intros DI. subst Q. rewrite ER. cbn [fst snd].
    exact (dp_epi L inp rest0 lo r F fc m LO SP16 LAY BEL IO RL DIN rc X Rrc fj y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 m' DI). }
  (* [comment removed for export] *)
  assert (KNE : forall X, dparams_lv level strategy R X -> ds_level X <> level -> KATL L rest0 lo r F fc m Q ZL_DP_LVNE level strategy X).
  { intros X (RLX & RMX & E1 & E2) NL.
    apply (dp_lvne L inp rest0 lo r F fc m HSLH LO SP16 LAY BEL IO RL DIN Q level strategy X RL9 RS1 RLX RMX NL).
    - intros L0 M0. exact (proj1 (E2 NL) L0 M0).
    - exact (KX _ 0 (proj2 (E2 NL)) ltac:(lia)). }
  assert (KLV : forall X, dparams_lv level strategy R X -> KATL L rest0 lo r F fc m Q ZL_DP_LV level strategy X).
  { intros X LV. pose proof LV as (RLX & RMX & E1 & E2).
    apply (dp_lv L inp rest0 lo r F fc m LO LAY BEL IO Q level strategy X RL9 RS1 RLX).
    - intros EL. exact (KX _ 0 (E1 EL) ltac:(lia)).
    - intros NL. exact (KNE X LV NL). }
  apply (dp_front L inp rest0 lo r F fc m LO SP16 LAY BEL IO RL DIN Q level strategy d t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 DR DOUT);
    [| exact STK| exact MI| exact HST| exact RL9| exact RS1| exact RLV| exact RSG| exact RLF| |].
  - (* [comment removed for export] *)
    constructor. destruct (dparams_flushes d level strategy) eqn:EF.
    + destruct (PFL eq_refl) as (PG & _ & _ & _ & _ & OLE1 & _). cbv zeta in PG. destruct PG as ([OLE0 _] & _).
      eapply Nat.le_trans; [exact OLE0|]. eapply Nat.le_trans; [exact OLE1| exact ROOM].
    + destruct (PNF eq_refl) as (_ & _ & E1 & E2). destruct (Z.eq_dec (ds_level d) level) as [EL|NL].
      * rewrite (E1 EL) in ROOM. exact ROOM.
      * destruct (E2 NL) as [_ ER]. rewrite ER in ROOM. cbn [fst] in ROOM. rewrite dparams_strm in ROOM. exact ROOM.
  - intros EF. exact (KLV d (PNF EF)).
  - intros EF. destruct (PFL EF) as (PG & RAI1 & RSS1 & RLA1 & RBS1 & OLE1 & RRC & EM2 & EM5 & LVP).
    unfold KFL. apply (dp_flush L inp rest0 lo r F fc m HDEFL LO SP16 LAY BEL IO RL DIN Q level strategy d RL9 RS1 PG).
    + cbv zeta. split; [exact RAI1|]. split; [exact RSS1|]. split; [exact RLA1|]. split; [exact RBS1|]. split; [| exact RRC].
      constructor. eapply Nat.le_trans; [exact OLE1| exact ROOM].
    + intros NE A0 S0. exact (proj1 (LVP NE A0 S0)).
    + intros E. exact (KX _ _ (EM2 E) ltac:(lia)).
    + intros NE HC. exact (KX _ _ (EM5 NE HC) ltac:(lia)).
    + intros NE A0 S0 NL. exact (KNE _ (LVP NE A0 S0) NL).
    + intros NE A0 S0 EL. pose proof (LVP NE A0 S0) as (RLX & RMX & E1 & E2).
      exact (dp_same L inp rest0 lo r F fc m LO LAY BEL IO Q strategy _ RS1 (KX _ 0 (E1 EL) ltac:(lia))).
Qed.

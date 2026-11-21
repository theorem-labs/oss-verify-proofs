(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InffastModel InffastCtx InffastSafe IfSpec IfSpec6
     If6_1 If6_2 If6_3 If6_4 If6_5I If6_6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac symex_auto ::=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia;
  try solve [ reflexivity | assumption | symex_ret_auto | symex_read_auto | symex_store_auto | symex_sok_auto | lia | split; lia ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma land_wrap32_zmask : forall h e, 0 <= h -> 0 <= e < 32 -> Z.land (wrap32 h) (zmask e) = h mod 2 ^ e.
Proof.
  intros h e Hh He. rewrite zmask_pow2, land_ones_mod, wrap32_eqmod by lia.
  apply Z.mod_mod_divide. exists (2 ^ (32 - e)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma land_zmask : forall h e, 0 <= e < 32 -> Z.land h (zmask e) = h mod 2 ^ e.
Proof. intros h e He. rewrite zmask_pow2, land_ones_mod by lia. reflexivity. Qed.


Lemma dpull_eq : forall x f e,
  0 <= f_hold f < 2 ^ f_bits f -> 0 <= f_bits f -> 0 <= e < 16 ->
  (f_bits f < e -> 0 <= arr_get (x_input x) (f_in f) < 256) ->
  (f_bits f + 8 < e -> 0 <= arr_get (x_input x) (f_in f + 1) < 256) ->
  (if f_bits f <? e then if f_bits (fpull x f) <? e then fpull x (fpull x f) else fpull x f else f)
  = (let '(i, h, b) := dpull (x_input x) (f_in f) (f_hold f) (f_bits f) e in
    mkF i (f_out f) h b (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f))
  /\ (let '(i, h, b) := dpull (x_input x) (f_in f) (f_hold f) (f_bits f) e in 0 <= h < 2 ^ b).
Proof.
  intros x f e Hh Hb He Hv0 Hv1. unfold dpull.
  destruct (Z.ltb_spec (f_bits f) e) as [Hl|Hl].
  - destruct (fpull_eq x f ltac:(lia) ltac:(lia) ltac:(lia) (Hv0 Hl)) as [E B]. rewrite E. cbn [f_bits f_in f_hold f_out f_len f_dist f_op f_from f_ob].
    pose proof (Z.pow_pos_nonneg 2 (f_bits f) ltac:(lia) ltac:(lia)) as Hp. pose proof (Hv0 Hl) as Hb0.
    destruct (Z.ltb_spec (f_bits f + 8) e) as [Hl2|Hl2].
    + set (f1 := mkF _ _ _ _ _ _ _ _ _).
      destruct (fpull_eq x f1 ltac:(subst f1; cbn; nia) ltac:(subst f1; cbn; lia) ltac:(subst f1; cbn; exact B) ltac:(subst f1; cbn; apply Hv1; lia)) as [E1 B1].
      rewrite E1. subst f1. cbn. cbn in B1. split; [f_equal; lia|]. replace (f_bits f + 16) with (f_bits f + 8 + 8) by lia. split; [nia | exact B1].
    + split; [reflexivity|]. split; [nia | exact B].
  - split; [destruct f; reflexivity | exact Hh].
Qed.

Lemma fpull2_if_eq : forall x f,
  0 <= f_hold f < 2 ^ f_bits f -> 0 <= f_bits f ->
  (f_bits f < 15 -> 0 <= arr_get (x_input x) (f_in f) < 256 /\ 0 <= arr_get (x_input x) (f_in f + 1) < 256) ->
  fpull2_if x f
  = (let '(i, h, b) := refill2 (x_input x) (f_in f) (f_hold f) (f_bits f) in
    mkF i (f_out f) h b (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f))
  /\ (let '(i, h, b) := refill2 (x_input x) (f_in f) (f_hold f) (f_bits f) in 0 <= h < 2 ^ b /\ b < f_bits f + 17).
Proof.
  intros x f Hh Hb Hv. unfold fpull2_if, refill2.
  destruct (Z.ltb_spec (f_bits f) 15) as [Hl|Hl].
  - destruct (Hv Hl) as [Hb0 Hb1].
    destruct (fpull_eq x f ltac:(lia) ltac:(lia) ltac:(lia) Hb0) as [E B]. rewrite E.
    pose proof (Z.pow_pos_nonneg 2 (f_bits f) ltac:(lia) ltac:(lia)) as Hp.
    set (f1 := mkF _ _ _ _ _ _ _ _ _).
    destruct (fpull_eq x f1 ltac:(subst f1; cbn; nia) ltac:(subst f1; cbn; lia) ltac:(subst f1; cbn; exact B) ltac:(subst f1; cbn; exact Hb1)) as [E1 B1].
    rewrite E1. subst f1. cbn. cbn in B1. split; [f_equal; lia|]. split; [|lia].
    replace (f_hold f + (arr_get (x_input x) (f_in f + 1) * 2 ^ (f_bits f + 8) + arr_get (x_input x) (f_in f) * 2 ^ f_bits f))
      with (f_hold f + arr_get (x_input x) (f_in f) * 2 ^ f_bits f + arr_get (x_input x) (f_in f + 1) * 2 ^ (f_bits f + 8)) by lia.
    replace (f_bits f + 16) with (f_bits f + 8 + 8) by lia. split; [nia | exact B1].
  - split; [destruct f; reflexivity | lia].
Qed.

Lemma fdrop_eq : forall f op, fdrop f op = mkF (f_in f) (f_out f) (Z.shiftr (f_hold f) op) (wrap32 (f_bits f - op)) (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f).
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9] op; reflexivity. Qed.

Lemma cpn_in : forall x n f, f_in (cpn x n f) = f_in f. Proof. intros. apply cpn_keep. Qed.
Lemma cpn_hold : forall x n f, f_hold (cpn x n f) = f_hold f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_bits : forall x n f, f_bits (cpn x n f) = f_bits f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_len : forall x n f, f_len (cpn x n f) = f_len f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_dist : forall x n f, f_dist (cpn x n f) = f_dist f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_ob : forall x n f, f_ob (cpn x n f) = cblit (x_window x) (f_from f) (f_ob f) (f_out f) n. Proof. intros. apply cpn_cblit. Qed.
Lemma cpn_from : forall x n f, f_from (cpn x n f) = fr_add (f_from f) n. Proof. intros. apply (cpn_cblit x n f). Qed.
Lemma fset_len_id : forall f, fset_len f (f_len f) = f. Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9]; reflexivity. Qed.

Lemma dpull_cases : forall inp fin hold bits e fin' hold' bits',
  dpull inp fin hold bits e = (fin', hold', bits') ->
  (e <= bits /\ bits' = bits /\ fin' = fin /\ hold' = hold)
  \/ (bits < e <= bits + 8 /\ bits' = bits + 8 /\ fin' = fin + 1)
  \/ (bits + 8 < e /\ bits' = bits + 16 /\ fin' = fin + 2).
Proof.
  intros inp fin hold bits e fin' hold' bits' H. unfold dpull in H.
  destruct (Z.ltb_spec bits e); [destruct (Z.ltb_spec (bits + 8) e)|]; injection H as <- <- <-; lia.
Qed.

Section Walk.
Context {mem : word -> option byte} {sp : Z} {ra : word}
        {s : inflate_state} {c : icall} {r : iregs}
        {ZP S I0 P0 WB : Z}.
Variable C : iff_pre s6_segs is6_LENFIX is6_DISTFIX ROD6_LO ROD6_HI IMG6_TOP mem sp ra s c r ZP S I0 P0 WB.
Local Notation X := (ffx_of s c r).
Local Notation IN := (arr_len (ic_input c)).
Local Notation ON := (arr_len (ic_outbuf c)).
Local Notation WN := (arr_len (is_window s)).
Local Notation LC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_lencode s)).
Local Notation DC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_distcode s)).
Local Notation LCN := (ctab_len (is_lencode s)).
Local Notation DCN := (ctab_len (is_distcode s)).
Local Notation KR := (@KREGS6 sp ZP S I0 P0 WB X (is_lenbits s) (is_distbits s) LC DC).
Local Notation MEMI := (@MEMINV s6_segs mem sp (arr_len (ic_outbuf c)) ZP S P0).
Let Hret := ifp_ret C.
Let Hzin := ifp_zs_in C. Let Hzain := ifp_zs_ain C. Let Hzout := ifp_zs_out C. Let Hzaout := ifp_zs_aout C. Let Hzst := ifp_zs_state C.
Let Hsc := ifp_scalars C. Let Hcodes := ifp_codes C. Let Hcodes_b := ifp_codes_b C.
Let Hwin := ifp_win C. Let Hwin_b := ifp_win_b C. Let Hinp := ifp_in C. Let Hinp_b := ifp_in_b C.
Let Hout := ifp_out C. Let Hout_b := ifp_out_b C. Let Hrod := ifp_rod C.
Let Hsp0 : 0x5c000 <= sp := proj1 (ifp_sp C). Let Hsp1 : sp + 112 < 2 ^ 63 := proj2 (ifp_sp C).
Let HZP0 : 0 < ZP := proj1 (ifp_ZP C). Let HZP1 : ZP + 112 < 2 ^ 63 := proj2 (ifp_ZP C).
Let HS0 : 0 < S := proj1 (ifp_S C). Let HS1 : S + 7176 < 2 ^ 63 := proj2 (ifp_S C).
Let HI0 : 0 <= I0 := proj1 (ifp_I0 C). Let HI1 : I0 + IN < 2 ^ 63 := proj2 (ifp_I0 C).
Let HP0 : 0 < P0 := proj1 (ifp_P0 C). Let HP1 : P0 + ON < 2 ^ 63 := proj2 (ifp_P0 C).
Let HW0 : 0 <= WB := proj1 (ifp_WB C). Let HWN0 : 0 <= WN := proj1 (proj2 (ifp_WB C)). Let HW1 : WB + WN < 2 ^ 63 := proj2 (proj2 (ifp_WB C)).
Let Hd_spZ := ifp_d_spZ C. Let Hd_spS := ifp_d_spS C. Let Hd_spI := ifp_d_spI C. Let Hd_spP := ifp_d_spP C. Let Hd_spW := ifp_d_spW C.
Let Hd_PZ := ifp_d_PZ C. Let Hd_PS := ifp_d_PS C. Let Hd_PI := ifp_d_PI C. Let Hd_PW := ifp_d_PW C.
Let Hd_ZS := ifp_d_ZS C. Let Hd_ZI := ifp_d_ZI C. Let Hd_ZW := ifp_d_ZW C. Let Hd_SI := ifp_d_SI C. Let Hd_SW := ifp_d_SW C.
Let Hmap_sp := ifp_map_sp C. Let Hmap_P := ifp_map_P C. Let Hmap_Z := ifp_map_Z C. Let Hmap_S := ifp_map_S C.
Let Hnin0 : 0 <= ic_next_in c := proj1 (proj1 (ifp_r_in C)). Let Hnin1 : ic_next_in c <= IN := proj2 (proj1 (ifp_r_in C)).
Let Hain0 : 0 <= ic_avail_in c := proj1 (proj2 (ifp_r_in C)). Let Hain1 : ic_avail_in c < 2 ^ 32 := proj2 (proj2 (ifp_r_in C)).
Let Hnout0 : 0 <= ic_next_out c := proj1 (ifp_r_out C). Let Haout0 : 0 <= ic_avail_out c := proj1 (proj2 (ifp_r_out C)).
Let Hroom : ic_next_out c + ic_avail_out c <= ON := proj2 (proj2 (ifp_r_out C)).
Let Hbeg0 : 0 <= ir_out r - ic_avail_out c := proj1 (ifp_r_start C). Let Hbeg1 : ir_out r - ic_avail_out c <= ic_next_out c := proj2 (ifp_r_start C).
Let HON : ON < 2 ^ 32 := ifp_r_room C.
Let Hhold0 : 0 <= is_hold s := proj1 (ifp_r_hold C). Let Hhold1 : is_hold s < 2 ^ is_bits s := proj2 (ifp_r_hold C).
Let Hbits0 : 0 <= is_bits s := proj1 (ifp_r_bits C). Let Hbits1 : is_bits s < 64 := proj2 (ifp_r_bits C).
Let Hwsize0 : 0 <= is_wsize s := proj1 (proj1 (ifp_r_w C)). Let Hwsize1 : is_wsize s < 2 ^ 31 := proj2 (proj1 (ifp_r_w C)).
Let Hwhave0 : 0 <= is_whave s := proj1 (proj1 (proj2 (ifp_r_w C))). Let Hwhave1 : is_whave s < 2 ^ 31 := proj2 (proj1 (proj2 (ifp_r_w C))).
Let Hwnext0 : 0 <= is_wnext s := proj1 (proj2 (proj2 (ifp_r_w C))). Let Hwnext1 : is_wnext s < 2 ^ 31 := proj2 (proj2 (proj2 (ifp_r_w C))).
Let Hlenbits0 : 0 <= is_lenbits s := proj1 (proj1 (ifp_r_lb C)). Let Hlenbits1 : is_lenbits s <= 15 := proj2 (proj1 (ifp_r_lb C)).
Let Hdistbits0 : 0 <= is_distbits s := proj1 (proj2 (ifp_r_lb C)). Let Hdistbits1 : is_distbits s <= 15 := proj2 (proj2 (ifp_r_lb C)).
Let Hsane0 : 0 <= is_sane s := proj1 (ifp_r_sane C). Let Hsane1 : is_sane s < 2 ^ 31 := proj2 (ifp_r_sane C).
Let Hlmask0 : 0 <= x_lmask X := proj1 (ffx_lmask_range C). Let Hlmask1 : x_lmask X < 65536 := proj2 (ffx_lmask_range C).
Let Hdmask0 : 0 <= x_dmask X := proj1 (ffx_dmask_range C). Let Hdmask1 : x_dmask X < 65536 := proj2 (ffx_dmask_range C).
Let Hlast0 : 0 <= x_last X := proj1 (ffx_last_range C). Let Hlast1 : x_last X <= IN + 2 ^ 32 := proj2 (ffx_last_range C).
Let Hend0 : 0 <= x_end X := proj1 (ffx_end_range C). Let Hend1 : x_end X <= ON + 2 ^ 32 := proj2 (ffx_end_range C).
Let Hxbeg0 : 0 <= x_beg X := proj1 (ffx_beg_range C). Let Hxbeg1 : x_beg X <= ic_next_out c := proj2 (ffx_beg_range C).
Let HLC0 : 0 <= LC := proj1 (lc_bounds C). Let HLCN0 : 0 <= LCN := proj1 (proj2 (lc_bounds C)). Let HLC1 : LC + 4 * LCN < 2 ^ 63 := proj2 (proj2 (lc_bounds C)).
Let HDC0 : 0 <= DC := proj1 (dc_bounds C). Let HDCN0 : 0 <= DCN := proj1 (proj2 (dc_bounds C)). Let HDC1 : DC + 4 * DCN < 2 ^ 63 := proj2 (proj2 (dc_bounds C)).
Let Hhold64 : is_hold s < 2 ^ 64 := hold_lt64 C.
Let Hpow_lb0 : 1 <= 2 ^ is_lenbits s := proj1 (lenbits_pow C). Let Hpow_lb1 : 2 ^ is_lenbits s <= 32768 := proj2 (lenbits_pow C).
Let Hpow_db0 : 1 <= 2 ^ is_distbits s := proj1 (distbits_pow C). Let Hpow_db1 : 2 ^ is_distbits s <= 32768 := proj2 (distbits_pow C).
Let Hlmask_eq : x_lmask X = 2 ^ is_lenbits s - 1 := ffx_lmask_eq C. Let Hdmask_eq : x_dmask X = 2 ^ is_distbits s - 1 := ffx_dmask_eq C.
Let Hbeg_eq : x_beg X = ic_next_out c - (ir_out r - ic_avail_out c) := ffx_beg_eq C.

Local Ltac side :=
  lazymatch goal with
  | |- @ex _ _ => fail
  | |- _ =>
    rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
    first [ sep_solve
          | match goal with H : getr ?rs ?i = zw _ |- getr ?rs ?i = zw _ => rewrite H; f_equal; lia end ]
  end.
Local Ltac mlia := Z.to_euclidean_division_equations; lia.
Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?Z.mod_small by lia; lia.
Local Ltac nf :=
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob x_window x_input x_wsize x_wnext x_whave ffx_of];
  repeat first [rewrite cpn_in | rewrite cpn_out | rewrite cpn_hold | rewrite cpn_bits | rewrite cpn_len | rewrite cpn_dist];
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob x_window x_input x_wsize x_wnext x_whave ffx_of].
Local Ltac fz := nf; nf; rewrite ?Z2Nat.id by lia.
Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.
Local Ltac via1 Ha H :=
  lazymatch type of H with getr _ ?r = _ => rewrite (Ha r eq_refl); exact H end.
Local Ltac clear_layout :=
  clear Hzin Hzain Hzout Hzaout Hzst Hsc Hcodes Hcodes_b Hwin Hwin_b Hinp Hinp_b Hout Hout_b Hrod
        Hd_spZ Hd_spS Hd_spI Hd_spP Hd_spW Hd_PZ Hd_PS Hd_PI Hd_PW Hd_ZS Hd_ZI Hd_ZW Hd_SI Hd_SW
        Hmap_sp Hmap_P Hmap_Z Hmap_S.



Definition FB (f : ffs) : Prop :=
  0 <= f_hold f < 2 ^ f_bits f /\ 0 <= f_bits f < 64 /\ 0 <= f_in f <= IN /\ x_beg X <= f_out f <= ON.

Definition CINV (regs0 R : bvmap 5 word) (m' : word -> option byte) (f' : ffs) : Prop :=
  KR R /\ MEMI (SAVED6 regs0 X) m' (f_ob f') /\ getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\
  getr R 13 = zw (I0 + f_in f') /\ getr R 14 = zw (P0 + f_out f') /\ getr R 11 = zw (f_hold f') /\ getr R 17 = zw (f_bits f') /\
  FB f'.

Definition BINV (regs0 R : bvmap 5 word) (m' : word -> option byte) (f' : ffs) (md : Z) (mg : option Z) : Prop :=
  getr R 2 = zw sp /\ getr R 10 = zw ZP /\ getr R 12 = zw S /\ getr R 15 = zw (I0 + x_last X) /\ getr R 16 = zw (P0 + x_end X) /\
  getr R 13 = zw (I0 + f_in f') /\ getr R 14 = zw (P0 + f_out f') /\ getr R 11 = zw (f_hold f') /\ getr R 17 = zw (f_bits f') /\
  getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\
  FB f' /\
  exists m0, MEMI (SAVED6 regs0 X) m0 (f_ob f') /\ m' = brk_mem m0 ZP S md mg.

Definition SIMRES (regs0 regs : bvmap 5 word) (m : word -> option byte) (pc : word) (res : fstep) : Prop :=
  match res with
  | FCont f' => exists R m', msteps s6_segs (mkst regs pc m s6_rom) (mkst R (0x1fa48 : word) m' s6_rom) /\ CINV regs0 R m' f'
  | FBreak f' md mg => exists R m', msteps s6_segs (mkst regs pc m s6_rom) (mkst R (0x1fd90 : word) m' s6_rom) /\ BINV regs0 R m' f' md mg
  end.

Lemma SIMRES_steps : forall regs0 regs R m m2 (pc pc2 : word) res,
  msteps s6_segs (mkst regs pc m s6_rom) (mkst R pc2 m2 s6_rom) -> SIMRES regs0 R m2 pc2 res -> SIMRES regs0 regs m pc res.
Proof.
  intros regs0 regs R m m2 pc pc2 res Hms Hres. destruct res as [f'|f' md mg]; cbn [SIMRES] in *;
    destruct Hres as (R' & m' & Hms' & H'); exists R', m'; (split; [eapply msteps_trans; [exact Hms | exact Hms'] | exact H']).
Qed.

Lemma slot0_in : forall regs0, In (0, 8%nat, x_wsize X + x_wnext X) (SAVED6 regs0 X).
Proof. intros regs0. unfold SAVED6. cbn. do 13 right. left. reflexivity. Qed.

Lemma blk_J5c : forall m regs,
  exists R, msteps s6_segs (mkst regs (0x1fc94 : word) m s6_rom) (mkst R (0x1fcd0 : word) m s6_rom) /\ (forall k, getr R k = getr regs k).
Proof.
  intros m regs. clear_layout.
  symex s6_segs fastC6 4%nat NoDirs NoReads (@nil (Z * expr)) (@nil (nat * Z)) NoRegions (@nil Z) NoVals F0 F0'
    (mkst regs (0x1fc94 : word) m s6_rom) R HR Hfr Hms.
  all: try side.
  exists R. split; [exact Hms|]. intros k; apply Hfr; reflexivity.
Qed.

Hypothesis WLEG1 : wleg_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem) (0x1fbbc : word) (0x1fbd4 : word).
Hypothesis WLEGW1 : wleg_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem) (0x1fc7c : word) (0x1fc94 : word).
Hypothesis WLEG3 : wleg_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem) (0x1fcb8 : word) (0x1fcd0 : word).
Hypothesis WLEG2 : wleg2_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Hypothesis W3 : w3_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Hypothesis W3C : w3c00_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Hypothesis DO3 : do3_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).

Lemma w3_simres : forall regs0 regs1 regs m1 m (pc1 : word) F,
  msteps s6_segs (mkst regs1 pc1 m1 s6_rom) (mkst regs (0x1fcd8 : word) m s6_rom) ->
  KR regs -> MEMI (SAVED6 regs0 X) m (f_ob F) ->
  getr regs 1 = zw (faddr WB P0 (f_from F)) -> getr regs 14 = zw (P0 + f_out F) -> getr regs 26 = zw (f_len F) ->
  getr regs 13 = zw (I0 + f_in F) -> getr regs 11 = zw (f_hold F) -> getr regs 17 = zw (f_bits F) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  0 <= f_len F < 2 ^ 17 -> srcn_ok WN (f_out F) (f_from F) (f_len F) ->
  0 <= f_hold F < 2 ^ f_bits F -> 0 <= f_bits F < 64 -> 0 <= f_in F <= IN -> x_beg X <= f_out F -> f_out F + f_len F <= ON ->
  SIMRES regs0 regs1 m1 pc1 (FCont (copy_tail X (copy_while3 X F))).
Proof.
  intros regs0 regs1 regs m1 m pc1 F Hpre HK HM H1 H14 H26 H13 H11 H17 Hg3 Hg4 Hlen Hsrc Bh Bb Bi Bo1 Bo2.
  destruct (W3 (SAVED6 regs0 X) m F regs HK HM H1 H14 H26 Hlen Bo1 Bo2 Hsrc)
    as (R & m' & Hms & HK' & HM' & A14 & Hfr & E1 & E2 & E3 & E4 & E5).
  cbn [SIMRES]. exists R, m'. split; [eapply msteps_trans; [exact Hpre | exact Hms]|].
  unfold CINV. split; [exact HK'|]. split; [exact HM'|].
  split; [rewrite (Hfr 3%bv eq_refl); exact Hg3|]. split; [rewrite (Hfr 4%bv eq_refl); exact Hg4|].
  split; [rewrite (Hfr 13%bv eq_refl), H13, E1; reflexivity|]. split; [exact A14|].
  split; [rewrite (Hfr 11%bv eq_refl), H11, E2; reflexivity|]. split; [rewrite (Hfr 17%bv eq_refl), H17, E3; reflexivity|].
  unfold FB. rewrite E1, E2, E3, E4. lia.
Qed.

Lemma w3c_simres : forall regs0 regs1 regs m1 m (pc1 : word) F,
  msteps s6_segs (mkst regs1 pc1 m1 s6_rom) (mkst regs (0x1fd38 : word) m s6_rom) ->
  KR regs -> MEMI (SAVED6 regs0 X) m (f_ob F) -> f_from F = FWin 0 ->
  getr regs 14 = zw (P0 + f_out F) -> getr regs 26 = zw (f_len F) ->
  getr regs 13 = zw (I0 + f_in F) -> getr regs 11 = zw (f_hold F) -> getr regs 17 = zw (f_bits F) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  0 <= f_len F < 2 ^ 17 -> srcn_ok WN (f_out F) (f_from F) (f_len F) ->
  0 <= f_hold F < 2 ^ f_bits F -> 0 <= f_bits F < 64 -> 0 <= f_in F <= IN -> x_beg X <= f_out F -> f_out F + f_len F <= ON ->
  SIMRES regs0 regs1 m1 pc1 (FCont (copy_tail X (copy_while3 X F))).
Proof.
  intros regs0 regs1 regs m1 m pc1 F Hpre HK HM HF0 H14 H26 H13 H11 H17 Hg3 Hg4 Hlen Hsrc Bh Bb Bi Bo1 Bo2.
  destruct (W3C (SAVED6 regs0 X) m F regs HK HM HF0 H14 H26 Hlen Bo1 Bo2 Hsrc)
    as (R & m' & Hms & HK' & HM' & A14 & Hfr & E1 & E2 & E3 & E4 & E5).
  cbn [SIMRES]. exists R, m'. split; [eapply msteps_trans; [exact Hpre | exact Hms]|].
  unfold CINV. split; [exact HK'|]. split; [exact HM'|].
  split; [rewrite (Hfr 3%bv eq_refl); exact Hg3|]. split; [rewrite (Hfr 4%bv eq_refl); exact Hg4|].
  split; [rewrite (Hfr 13%bv eq_refl), H13, E1; reflexivity|]. split; [exact A14|].
  split; [rewrite (Hfr 11%bv eq_refl), H11, E2; reflexivity|]. split; [rewrite (Hfr 17%bv eq_refl), H17, E3; reflexivity|].
  unfold FB. rewrite E1, E2, E3, E4. lia.
Qed.

Definition wplace (x : ffx) (f : ffs) : ffs :=
  if x_wnext x =? 0 then
    let f := fset_from f (FWin (x_wsize x - f_op f)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      fset_from f (FOut (f_out f - f_dist f))
    else f
  else if x_wnext x <? f_op f then
    let f := fset_from f (FWin (x_wsize x + x_wnext x - f_op f)) in
    let f := fset_op f (wrap32 (f_op f - x_wnext x)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      let f := fset_from f (FWin 0) in
      if x_wnext x <? f_len f then
        let f := fset_op f (x_wnext x) in
        let f := fset_len f (wrap32 (f_len f - f_op f)) in
        let f := copy_op x f in
        fset_from f (FOut (f_out f - f_dist f))
      else f
    else f
  else
    let f := fset_from f (FWin (x_wnext x - f_op f)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      fset_from f (FOut (f_out f - f_dist f))
    else f.

Lemma win_sim : forall regs0 regs m F,
  KR regs -> MEMI (SAVED6 regs0 X) m (f_ob F) ->
  getr regs 7 = zw (f_op F) -> getr regs 27 = zw (f_dist F) -> getr regs 26 = zw (f_len F) -> getr regs 14 = zw (P0 + f_out F) ->
  getr regs 13 = zw (I0 + f_in F) -> getr regs 11 = zw (f_hold F) -> getr regs 17 = zw (f_bits F) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  1 <= f_op F -> f_dist F < 2 ^ 17 -> f_dist F = f_op F + (f_out F - x_beg X) -> 3 <= f_len F < 2 ^ 17 ->
  0 <= f_hold F < 2 ^ f_bits F -> 0 <= f_bits F < 64 -> 0 <= f_in F <= IN -> x_beg X <= f_out F ->
  window_ok X ON WN F = true ->
  SIMRES regs0 regs m (0x1fb94 : word) (FCont (copy_tail X (copy_while3 X (wplace X F)))).
Proof.
  intros regs0 regs m F HK HM H7 H27 H26 H14 H13 H11 H17 Hg3 Hg4 Hop Hdist Hopd Hlen Bh Bb Bi Bo Hwok.
  pose proof Hwin_b as Hwb.
  unfold window_ok in Hwok. apply andb_prop in Hwok as [HfoL Hwok]. apply Z.leb_le in HfoL.
  destruct (blk_DWP C m (f_op F) regs HK H7 ltac:(lia)) as (R1 & Hms1 & Hfr1).
  unfold wplace. unfold dwp_pc in Hms1. cbn [x_wsize x_wnext x_whave ffx_of] in Hms1, Hwok |- *.
  destruct (Z.eqb_spec (is_wnext s) 0) as [Hw0|Hw0].
  -
    apply andb_prop in Hwok as [Hk1 Hwok]. apply Z.leb_le in Hk1.
    destruct (blk_W1h C m (f_op F) (f_len F) R1 (KREGS6_frame _ _ _ _ _ _ _ _ _ _ _ _ _ [] eq_refl HK ltac:(intros k _; apply Hfr1))
                ltac:(cbn [x_wnext ffx_of]; exact Hw0) ltac:(rewrite Hfr1; exact H7) ltac:(rewrite Hfr1; exact H26)
                ltac:(cbn [x_wsize ffx_of]; lia) ltac:(lia) ltac:(lia))
      as (R2 & Hms2 & HK2 & A1 & A25 & Hfr2).
    cbn [x_wsize ffx_of] in A1.
    nf.
    destruct (Z.ltb_spec (f_op F) (f_len F)) as [Hol|Hol].
    +
      apply Z.leb_le in Hwok.
      rewrite copy_op_cpn by (nf; rewrite ?wrap32_id by lia; lia). nf. rewrite (wrap32_id (f_len F - f_op F)), Z2Nat.id by lia.
      set (f1 := fset_len (fset_from F (FWin (is_wsize s - f_op F))) (f_len F - f_op F)).
      destruct (WLEGW1 (SAVED6 regs0 X) m f1 (Z.to_nat (f_op F)) (is_wsize s - f_op F) R2 HK2 ltac:(subst f1; exact HM) ltac:(subst f1; reflexivity)
                  A1 ltac:(rewrite Z2Nat.id by lia; exact (A25 Hol)) ltac:(subst f1; nf; rewrite (Hfr2 14%bv eq_refl), Hfr1; exact H14)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(subst f1; nf; lia) ltac:(subst f1; nf; lia))
        as (R3 & m3 & Hms3 & HK3 & HM3 & B14 & B1 & Hfr3).
      subst f1. nf. rewrite cpn_out in B14. cbn [f_out fset_len fset_from] in B14. rewrite Z2Nat.id in B14 by lia. rewrite Z2Nat.id in B1 by lia.
      destruct (blk_J5c m3 R3) as (R4 & Hms4 & Hfr4).
      destruct (blk_J98 C m3 (f_op F) (f_len F) R4 (KREGS6_frame _ _ _ _ _ _ _ _ _ _ _ _ _ [] eq_refl HK3 ltac:(intros k _; apply Hfr4))
                  ltac:(rewrite Hfr4, (Hfr3 7%bv eq_refl), (Hfr2 7%bv eq_refl), Hfr1; exact H7)
                  ltac:(rewrite Hfr4, (Hfr3 26%bv eq_refl), (Hfr2 26%bv eq_refl), Hfr1; exact H26) ltac:(lia) ltac:(lia))
        as (R5 & Hms5 & HK5 & C26 & Hfr5).
      destruct (blk_J9c C m3 (f_dist F) (f_out F + f_op F) R5 HK5 ltac:(rewrite (Hfr5 14%bv eq_refl), Hfr4, B14; f_equal; lia)
                  ltac:(rewrite (Hfr5 27%bv eq_refl), Hfr4, (Hfr3 27%bv eq_refl), (Hfr2 27%bv eq_refl), Hfr1; exact H27) ltac:(lia) ltac:(lia))
        as (R6 & Hms6 & HK6 & D1 & Hfr6).
      eapply (w3_simres regs0 regs R6 m m3).
      { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
        eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5 | exact Hms6]. }
     
      * fz. exact HK6. * fz. exact HM3. * fz. rewrite D1; f_equal; lia.
      * fz. rewrite (Hfr6 14%bv eq_refl), (Hfr5 14%bv eq_refl), Hfr4, B14; f_equal; lia.
      * fz. rewrite (Hfr6 26%bv eq_refl); exact C26.
      * fz. rewrite (Hfr6 13%bv eq_refl), (Hfr5 13%bv eq_refl), Hfr4, (Hfr3 13%bv eq_refl), (Hfr2 13%bv eq_refl), Hfr1; exact H13.
      * fz. rewrite (Hfr6 11%bv eq_refl), (Hfr5 11%bv eq_refl), Hfr4, (Hfr3 11%bv eq_refl), (Hfr2 11%bv eq_refl), Hfr1; exact H11.
      * fz. rewrite (Hfr6 17%bv eq_refl), (Hfr5 17%bv eq_refl), Hfr4, (Hfr3 17%bv eq_refl), (Hfr2 17%bv eq_refl), Hfr1; exact H17.
      * fz. rewrite (Hfr6 3%bv eq_refl), (Hfr5 3%bv eq_refl), Hfr4, (Hfr3 3%bv eq_refl), (Hfr2 3%bv eq_refl), Hfr1; exact Hg3.
      * fz. rewrite (Hfr6 4%bv eq_refl), (Hfr5 4%bv eq_refl), Hfr4, (Hfr3 4%bv eq_refl), (Hfr2 4%bv eq_refl), Hfr1; exact Hg4.
      * fz. lia. * fz. cbn; lia. * fz. exact Bh. * fz. exact Bb. * fz. exact Bi. * fz. lia. * fz. lia.
    +
      apply Z.leb_le in Hwok.
      eapply (w3_simres regs0 regs R2 m m); [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HK2 | ..].
      * fz. exact HM. * fz. exact A1. * fz. rewrite (Hfr2 14%bv eq_refl), Hfr1; exact H14. * fz. rewrite (Hfr2 26%bv eq_refl), Hfr1; exact H26.
      * fz. rewrite (Hfr2 13%bv eq_refl), Hfr1; exact H13. * fz. rewrite (Hfr2 11%bv eq_refl), Hfr1; exact H11. * fz. rewrite (Hfr2 17%bv eq_refl), Hfr1; exact H17.
      * fz. rewrite (Hfr2 3%bv eq_refl), Hfr1; exact Hg3. * fz. rewrite (Hfr2 4%bv eq_refl), Hfr1; exact Hg4.
      * fz. lia. * fz. cbn; lia. * fz. exact Bh. * fz. exact Bb. * fz. exact Bi. * fz. lia. * fz. lia.
  - destruct (Z.ltb_spec (is_wnext s) (f_op F)) as [Hwl|Hwl].
    +
      apply andb_prop in Hwok as [Hk1 Hwok]. apply Z.leb_le in Hk1.
      destruct (blk_W2h C (SAVED6 regs0 X) m (f_ob F) (f_op F) (f_len F) R1
                  (KREGS6_frame _ _ _ _ _ _ _ _ _ _ _ _ _ [] eq_refl HK ltac:(intros k _; apply Hfr1)) HM (slot0_in regs0)
                  ltac:(rewrite Hfr1; exact H7) ltac:(rewrite Hfr1; exact H26)
                  ltac:(cbn [x_wnext ffx_of]; lia) ltac:(cbn [x_wsize x_wnext ffx_of]; lia) ltac:(lia) ltac:(lia))
        as (R2 & Hms2 & HK2 & A1 & A7 & A25 & Hfr2).
      cbn [x_wsize x_wnext ffx_of] in A1, A7, A25, Hms2.
      nf. rewrite (wrap32_id (f_op F - is_wnext s)) by lia.
      set (opp := f_op F - is_wnext s) in *.
      destruct (Z.ltb_spec opp (f_len F)) as [Hol|Hol].
      *
        apply andb_prop in Hwok as [Hk2 Hwok]. apply Z.leb_le in Hk2.
        rewrite (copy_op_cpn X (fset_len (fset_op (fset_from F _) _) _)) by (nf; rewrite ?wrap32_id by lia; lia). nf.
        rewrite (wrap32_id (f_len F - opp)) by lia. rewrite ?Z2Nat.id by lia.
        set (f1 := fset_len (fset_op (fset_from F (FWin (is_wsize s + is_wnext s - f_op F))) opp) (f_len F - opp)).
        destruct (WLEG1 (SAVED6 regs0 X) m f1 (Z.to_nat opp) (is_wsize s + is_wnext s - f_op F) R2 HK2 ltac:(subst f1; exact HM) ltac:(subst f1; reflexivity)
                    A1 ltac:(rewrite Z2Nat.id by lia; exact (A25 Hol)) ltac:(subst f1; nf; rewrite (Hfr2 14%bv eq_refl), Hfr1; exact H14)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(subst f1; nf; lia) ltac:(subst f1; nf; lia))
          as (R3 & m3 & Hms3 & HK3 & HM3 & B14 & B1 & Hfr3).
        subst f1. nf. rewrite cpn_out in B14. cbn [f_out fset_len fset_op fset_from] in B14. rewrite Z2Nat.id in B14 by lia.
        destruct (blk_W2m C m3 opp (f_len F) R3 HK3 ltac:(rewrite (Hfr3 7%bv eq_refl); exact A7)
                    ltac:(rewrite (Hfr3 26%bv eq_refl), (Hfr2 26%bv eq_refl), Hfr1; exact H26) ltac:(lia) ltac:(lia))
          as (R4 & Hms4 & HK4 & C26 & C7 & Hfr4).
        cbn [x_wnext ffx_of] in Hms4, C7.
        destruct (Z.ltb_spec (is_wnext s) (f_len F - opp)) as [Hw2|Hw2].
        --
           apply Z.leb_le in Hwok.
           rewrite copy_op_cpn by (nf; rewrite ?wrap32_id by lia; lia). nf. rewrite (wrap32_id (f_len F - opp - is_wnext s)) by lia. rewrite ?Z2Nat.id by lia.
           set (f2 := fset_len (fset_op (fset_from (cpn X (Z.to_nat opp)
                        (fset_len (fset_op (fset_from F (FWin (is_wsize s + is_wnext s - f_op F))) opp) (f_len F - opp))) (FWin 0)) (is_wnext s))
                        (f_len F - opp - is_wnext s)).
           destruct (WLEG2 (SAVED6 regs0 X) m3 f2 R4 HK4 ltac:(subst f2; exact HM3) ltac:(subst f2; reflexivity) (C7 Hw2)
                       ltac:(subst f2; nf; rewrite (Hfr4 14%bv eq_refl), B14; f_equal; lia)
                       ltac:(cbn [x_wnext ffx_of]; lia) ltac:(cbn [x_wnext ffx_of]; lia) ltac:(subst f2; nf; lia) ltac:(subst f2; nf; lia))
             as (R5 & m5 & Hms5 & HK5 & HM5 & D14 & Hfr5).
           subst f2. nf. rewrite cpn_out in D14. cbn [f_out fset_len fset_op fset_from] in D14. rewrite cpn_out in D14.
           cbn [f_out fset_len fset_op fset_from x_wnext ffx_of] in D14. rewrite !Z2Nat.id in D14 by lia.
           destruct (blk_W2e C m5 (f_len F - opp) R5 HK5 ltac:(rewrite (Hfr5 26%bv eq_refl); exact C26) ltac:(cbn [x_wnext ffx_of]; lia))
             as (R6 & Hms6 & HK6 & E26 & Hfr6).
           cbn [x_wnext ffx_of] in E26.
           destruct (blk_J9c C m5 (f_dist F) (f_out F + opp + is_wnext s) R6 HK6 ltac:(rewrite (Hfr6 14%bv eq_refl), D14; f_equal; lia)
                       ltac:(rewrite (Hfr6 27%bv eq_refl), (Hfr5 27%bv eq_refl), (Hfr4 27%bv eq_refl), (Hfr3 27%bv eq_refl), (Hfr2 27%bv eq_refl), Hfr1; exact H27)
                       ltac:(lia) ltac:(lia))
             as (R7 & Hms7 & HK7 & G1 & Hfr7).
           eapply (w3_simres regs0 regs R7 m m5).
           { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
             eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5|]. eapply msteps_trans; [exact Hms6 | exact Hms7]. }
          
           ++ fz. exact HK7. ++ fz. exact HM5. ++ fz. rewrite G1; f_equal; lia.
           ++ fz. rewrite (Hfr7 14%bv eq_refl), (Hfr6 14%bv eq_refl), D14; f_equal; lia.
           ++ fz. rewrite (Hfr7 26%bv eq_refl); rewrite E26; f_equal; lia.
           ++ fz. rewrite (Hfr7 13%bv eq_refl), (Hfr6 13%bv eq_refl), (Hfr5 13%bv eq_refl), (Hfr4 13%bv eq_refl), (Hfr3 13%bv eq_refl), (Hfr2 13%bv eq_refl), Hfr1; exact H13.
           ++ fz. rewrite (Hfr7 11%bv eq_refl), (Hfr6 11%bv eq_refl), (Hfr5 11%bv eq_refl), (Hfr4 11%bv eq_refl), (Hfr3 11%bv eq_refl), (Hfr2 11%bv eq_refl), Hfr1; exact H11.
           ++ fz. rewrite (Hfr7 17%bv eq_refl), (Hfr6 17%bv eq_refl), (Hfr5 17%bv eq_refl), (Hfr4 17%bv eq_refl), (Hfr3 17%bv eq_refl), (Hfr2 17%bv eq_refl), Hfr1; exact H17.
           ++ fz. rewrite (Hfr7 3%bv eq_refl), (Hfr6 3%bv eq_refl), (Hfr5 3%bv eq_refl), (Hfr4 3%bv eq_refl), (Hfr3 3%bv eq_refl), (Hfr2 3%bv eq_refl), Hfr1; exact Hg3.
           ++ fz. rewrite (Hfr7 4%bv eq_refl), (Hfr6 4%bv eq_refl), (Hfr5 4%bv eq_refl), (Hfr4 4%bv eq_refl), (Hfr3 4%bv eq_refl), (Hfr2 4%bv eq_refl), Hfr1; exact Hg4.
           ++ fz. lia. ++ fz. cbn; lia. ++ fz. exact Bh. ++ fz. exact Bb. ++ fz. exact Bi. ++ fz. lia. ++ fz. lia.
        --
           apply Z.leb_le in Hwok.
           eapply (w3c_simres regs0 regs R4 m m3).
           { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3 | exact Hms4]. }
          
           ++ fz. exact HK4. ++ fz. exact HM3. ++ fz. reflexivity.
           ++ fz. rewrite (Hfr4 14%bv eq_refl), B14; f_equal; lia.
           ++ fz. exact C26.
           ++ fz. rewrite (Hfr4 13%bv eq_refl), (Hfr3 13%bv eq_refl), (Hfr2 13%bv eq_refl), Hfr1; exact H13.
           ++ fz. rewrite (Hfr4 11%bv eq_refl), (Hfr3 11%bv eq_refl), (Hfr2 11%bv eq_refl), Hfr1; exact H11.
           ++ fz. rewrite (Hfr4 17%bv eq_refl), (Hfr3 17%bv eq_refl), (Hfr2 17%bv eq_refl), Hfr1; exact H17.
           ++ fz. rewrite (Hfr4 3%bv eq_refl), (Hfr3 3%bv eq_refl), (Hfr2 3%bv eq_refl), Hfr1; exact Hg3.
           ++ fz. rewrite (Hfr4 4%bv eq_refl), (Hfr3 4%bv eq_refl), (Hfr2 4%bv eq_refl), Hfr1; exact Hg4.
           ++ fz. lia. ++ fz. cbn; lia. ++ fz. exact Bh. ++ fz. exact Bb. ++ fz. exact Bi. ++ fz. lia. ++ fz. lia.
      *
        apply Z.leb_le in Hwok.
        eapply (w3_simres regs0 regs R2 m m); [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HK2 | ..].
        -- fz. exact HM. -- fz. exact A1. -- fz. rewrite (Hfr2 14%bv eq_refl), Hfr1; exact H14. -- fz. rewrite (Hfr2 26%bv eq_refl), Hfr1; exact H26.
        -- fz. rewrite (Hfr2 13%bv eq_refl), Hfr1; exact H13. -- fz. rewrite (Hfr2 11%bv eq_refl), Hfr1; exact H11. -- fz. rewrite (Hfr2 17%bv eq_refl), Hfr1; exact H17.
        -- fz. rewrite (Hfr2 3%bv eq_refl), Hfr1; exact Hg3. -- fz. rewrite (Hfr2 4%bv eq_refl), Hfr1; exact Hg4.
        -- fz. lia. -- fz. cbn; lia. -- fz. exact Bh. -- fz. exact Bb. -- fz. exact Bi. -- fz. lia. -- fz. lia.
    +
      destruct (blk_W3h C m (f_op F) (f_len F) R1 (KREGS6_frame _ _ _ _ _ _ _ _ _ _ _ _ _ [] eq_refl HK ltac:(intros k _; apply Hfr1))
                  ltac:(rewrite Hfr1; exact H7) ltac:(rewrite Hfr1; exact H26)
                  ltac:(cbn [x_wnext ffx_of]; lia) ltac:(lia) ltac:(lia))
        as (R2 & Hms2 & HK2 & A1 & A25 & Hfr2).
      cbn [x_wnext ffx_of] in A1.
      nf.
      destruct (Z.ltb_spec (f_op F) (f_len F)) as [Hol|Hol].
      * fz. apply Z.leb_le in Hwok.
        rewrite copy_op_cpn by (nf; rewrite ?wrap32_id by lia; lia). nf. rewrite (wrap32_id (f_len F - f_op F)), Z2Nat.id by lia.
        set (f1 := fset_len (fset_from F (FWin (is_wnext s - f_op F))) (f_len F - f_op F)).
        destruct (WLEG3 (SAVED6 regs0 X) m f1 (Z.to_nat (f_op F)) (is_wnext s - f_op F) R2 HK2 ltac:(subst f1; exact HM) ltac:(subst f1; reflexivity)
                    A1 ltac:(rewrite Z2Nat.id by lia; exact (A25 Hol)) ltac:(subst f1; nf; rewrite (Hfr2 14%bv eq_refl), Hfr1; exact H14)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(subst f1; nf; lia) ltac:(subst f1; nf; lia))
          as (R3 & m3 & Hms3 & HK3 & HM3 & B14 & B1 & Hfr3).
        subst f1. nf. rewrite cpn_out in B14. cbn [f_out fset_len fset_from] in B14. rewrite Z2Nat.id in B14 by lia.
        destruct (blk_J98 C m3 (f_op F) (f_len F) R3 HK3
                    ltac:(rewrite (Hfr3 7%bv eq_refl), (Hfr2 7%bv eq_refl), Hfr1; exact H7)
                    ltac:(rewrite (Hfr3 26%bv eq_refl), (Hfr2 26%bv eq_refl), Hfr1; exact H26) ltac:(lia) ltac:(lia))
          as (R5 & Hms5 & HK5 & C26 & Hfr5).
        destruct (blk_J9c C m3 (f_dist F) (f_out F + f_op F) R5 HK5 ltac:(rewrite (Hfr5 14%bv eq_refl), B14; f_equal; lia)
                    ltac:(rewrite (Hfr5 27%bv eq_refl), (Hfr3 27%bv eq_refl), (Hfr2 27%bv eq_refl), Hfr1; exact H27) ltac:(lia) ltac:(lia))
          as (R6 & Hms6 & HK6 & D1 & Hfr6).
        eapply (w3_simres regs0 regs R6 m m3).
        { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
          eapply msteps_trans; [exact Hms5 | exact Hms6]. }
       
        -- fz. exact HK6. -- fz. exact HM3. -- fz. rewrite D1; f_equal; lia.
        -- fz. rewrite (Hfr6 14%bv eq_refl), (Hfr5 14%bv eq_refl), B14; f_equal; lia.
        -- fz. rewrite (Hfr6 26%bv eq_refl); exact C26.
        -- fz. rewrite (Hfr6 13%bv eq_refl), (Hfr5 13%bv eq_refl), (Hfr3 13%bv eq_refl), (Hfr2 13%bv eq_refl), Hfr1; exact H13.
        -- fz. rewrite (Hfr6 11%bv eq_refl), (Hfr5 11%bv eq_refl), (Hfr3 11%bv eq_refl), (Hfr2 11%bv eq_refl), Hfr1; exact H11.
        -- fz. rewrite (Hfr6 17%bv eq_refl), (Hfr5 17%bv eq_refl), (Hfr3 17%bv eq_refl), (Hfr2 17%bv eq_refl), Hfr1; exact H17.
        -- fz. rewrite (Hfr6 3%bv eq_refl), (Hfr5 3%bv eq_refl), (Hfr3 3%bv eq_refl), (Hfr2 3%bv eq_refl), Hfr1; exact Hg3.
        -- fz. rewrite (Hfr6 4%bv eq_refl), (Hfr5 4%bv eq_refl), (Hfr3 4%bv eq_refl), (Hfr2 4%bv eq_refl), Hfr1; exact Hg4.
        -- fz. lia. -- fz. cbn; lia. -- fz. exact Bh. -- fz. exact Bb. -- fz. exact Bi. -- fz. lia. -- fz. lia.
      * fz. apply Z.leb_le in Hwok.
        eapply (w3_simres regs0 regs R2 m m); [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact HK2 | ..].
        -- fz. exact HM. -- fz. exact A1. -- fz. rewrite (Hfr2 14%bv eq_refl), Hfr1; exact H14. -- fz. rewrite (Hfr2 26%bv eq_refl), Hfr1; exact H26.
        -- fz. rewrite (Hfr2 13%bv eq_refl), Hfr1; exact H13. -- fz. rewrite (Hfr2 11%bv eq_refl), Hfr1; exact H11. -- fz. rewrite (Hfr2 17%bv eq_refl), Hfr1; exact H17.
        -- fz. rewrite (Hfr2 3%bv eq_refl), Hfr1; exact Hg3. -- fz. rewrite (Hfr2 4%bv eq_refl), Hfr1; exact Hg4.
        -- fz. lia. -- fz. cbn; lia. -- fz. exact Bh. -- fz. exact Bb. -- fz. exact Bi. -- fz. lia. -- fz. lia.
Qed.

Local Ltac binv_close Hf K2 K10 K12 K15 K16 X13 X14 X11 X17 X3 X4 :=
  unfold BINV; cbn [f_in f_out f_hold f_bits f_ob fset_op];
  split; [rewrite (Hf 2%bv eq_refl); exact K2|]; split; [rewrite (Hf 10%bv eq_refl); exact K10|]; split; [rewrite (Hf 12%bv eq_refl); exact K12|];
  split; [rewrite (Hf 15%bv eq_refl); exact K15|]; split; [rewrite (Hf 16%bv eq_refl); exact K16|];
  split; [rewrite (Hf 13%bv eq_refl); exact X13|]; split; [rewrite (Hf 14%bv eq_refl); exact X14|];
  split; [rewrite (Hf 11%bv eq_refl); exact X11|]; split; [rewrite (Hf 17%bv eq_refl); exact X17|];
  split; [rewrite (Hf 3%bv eq_refl); exact X3|]; split; [rewrite (Hf 4%bv eq_refl); exact X4|].

Lemma dodist_sim : forall k regs0 regs m f didx,
  let here := code_at s (is_distcode s) didx in
  let cb := code_bits here in
  KR regs -> MEMI (SAVED6 regs0 X) m (f_ob f) ->
  getr regs 7 = zw (DC + 4 * didx) -> getr regs 27 = zw (code_op here) ->
  getr regs 11 = zw (f_hold f / 2 ^ cb) -> getr regs 17 = zw (f_bits f - cb) ->
  getr regs 13 = zw (I0 + f_in f) -> getr regs 14 = zw (P0 + f_out f) -> getr regs 26 = zw (f_len f) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  0 <= didx < DCN -> cb <= f_bits f -> FB f -> 0 <= f_len f < 2 ^ 17 ->
  dodist_ok X s IN ON WN k here f = true ->
  SIMRES regs0 regs m (dd_pc (code_op here)) (dodist k X s here f).
Proof.
  induction k as [|k IH]; intros regs0 regs m f didx here cb HK HM H7 H27 H11 H17 H13 H14 H26 Hg3 Hg4 Hdidx Hcb HFB Hlen Hok.
  { cbn [dodist_ok] in Hok. discriminate Hok. }
  destruct HFB as (Bh & Bb & Bi & Bo).
  pose proof (code_op_range here) as Hop. pose proof (code_bits_range here) as Hcbr. pose proof (code_val_range here) as Hval.
  assert (Hh1 : 0 <= f_hold f / 2 ^ cb < 2 ^ (f_bits f - cb)).
  { split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | apply shiftr_lt_pow2; lia]. }
  cbn [dodist_ok] in Hok. fold here cb in Hok.
  apply andb_prop in Hok as [_ Hok].
  cbn [dodist]. fold here cb.
  rewrite (fdrop_eq f cb) in Hok |- *. rewrite (Z.shiftr_div_pow2 (f_hold f) cb), (wrap32_id (f_bits f - cb)) in Hok |- * by lia.
  unfold dd_pc.
  destruct (Z.eqb_spec (Z.land (code_op here) 16) 0) as [H16|H16]; cbn [negb] in Hok |- *.
  -
    destruct (blk_DD1 m (code_op here) regs HK H27 ltac:(lia)) as (R1 & Hms1 & HK1 & Hfr1). unfold dd1_pc in Hms1.
    destruct (Z.eqb_spec (Z.land (code_op here) 64) 0) as [H64|H64]; cbn [negb] in Hms1.
    +
      apply andb_prop in Hok as [Hop16 Hok]. apply andb_prop in Hok as [Hi Hok]. apply Z.ltb_lt in Hop16. apply Z.ltb_lt in Hi.
      cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob] in Hi, Hok |- *.
      set (hold1 := f_hold f / 2 ^ cb) in *. set (bits1 := f_bits f - cb) in *.
      rewrite (land_zmask hold1 (code_op here)) in Hi, Hok |- * by lia.
      set (didx' := code_val here + hold1 mod 2 ^ code_op here) in *.
      pose proof (Z.mod_pos_bound hold1 (2 ^ code_op here) ltac:(apply Z.pow_pos_nonneg; lia)) as Hhm.
      set (f1 := mkF (f_in f) (f_out f) hold1 bits1 (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f)) in *.
      assert (Hcb' : code_bits (code_at s (is_distcode s) didx') <= bits1).
      { destruct k as [|k'']; cbn [dodist_ok] in Hok; [discriminate Hok|]. apply andb_prop in Hok as [Hc _]. apply Z.leb_le in Hc. exact Hc. }
      destruct (blk_DL2 C (SAVED6 regs0 X) m (f_ob f) didx hold1 bits1 R1 HK1 HM Hdidx
                  ltac:(rewrite (Hfr1 7%bv eq_refl); exact H7) ltac:(rewrite (Hfr1 27%bv eq_refl); exact H27)
                  ltac:(rewrite (Hfr1 11%bv eq_refl); exact H11) ltac:(rewrite (Hfr1 17%bv eq_refl); exact H17)
                  ltac:(lia) ltac:(exact Hh1) Hop16 ltac:(exact Hi) ltac:(exact Hcb'))
        as (R2 & Hms2 & HK2 & B7 & B27 & B11 & B17 & Hfr2 & Bh2 & Bb2).
      eapply SIMRES_steps; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      apply (IH regs0 R2 m f1 didx'); cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob].
      all: try assumption.
      * rewrite (Hfr2 13%bv eq_refl), (Hfr1 13%bv eq_refl). exact H13.
      * rewrite (Hfr2 14%bv eq_refl), (Hfr1 14%bv eq_refl). exact H14.
      * rewrite (Hfr2 26%bv eq_refl), (Hfr1 26%bv eq_refl). exact H26.
      * rewrite (Hfr2 3%bv eq_refl), (Hfr1 3%bv eq_refl). exact Hg3.
      * rewrite (Hfr2 4%bv eq_refl), (Hfr1 4%bv eq_refl). exact Hg4.
      * lia.
      * unfold FB. subst f1. cbn [f_hold f_bits f_in f_out]. lia.
    +
      destruct (blk_BADD C (SAVED6 regs0 X) m (f_ob f) R1 HK1 HM) as (R2 & Hms2 & Hfr2).
      cbn [SIMRES]. exists R2. eexists. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      pose proof HK1 as HKc. destruct HKc as (K2 & K10 & K12 & K15 & K16 & _).
      assert (X13 : getr R1 13 = zw (I0 + f_in f)) by (rewrite (Hfr1 13%bv eq_refl); exact H13).
      assert (X14 : getr R1 14 = zw (P0 + f_out f)) by (rewrite (Hfr1 14%bv eq_refl); exact H14).
      assert (X11 : getr R1 11 = zw (f_hold f / 2 ^ cb)) by (rewrite (Hfr1 11%bv eq_refl); exact H11).
      assert (X17 : getr R1 17 = zw (f_bits f - cb)) by (rewrite (Hfr1 17%bv eq_refl); exact H17).
      assert (X3 : getr R1 3 = getr regs0 3) by (rewrite (Hfr1 3%bv eq_refl); exact Hg3).
      assert (X4 : getr R1 4 = getr regs0 4) by (rewrite (Hfr1 4%bv eq_refl); exact Hg4).
      binv_close Hfr2 K2 K10 K12 K15 K16 X13 X14 X11 X17 X3 X4.
      split; [unfold FB; cbn [f_hold f_bits f_in f_out]; lia|].
      exists m. split; [exact HM|]. reflexivity.
  -
    set (hold1 := f_hold f / 2 ^ cb) in *. set (bits1 := f_bits f - cb) in *.
    unfold fset_dist in Hok |- *. cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob] in Hok |- *.
    set (e := Z.land (code_op here) 15) in *.
    assert (He : e = code_op here mod 2 ^ 4) by (subst e; change 15 with (2 ^ 4 - 1); apply land_ones_mod; lia).
    assert (He16 : 0 <= e < 16) by (rewrite He; apply Z.mod_pos_bound; lia).
    apply andb_prop in Hok as [Hpl Hok].
    assert (Hin1 : bits1 < e -> f_in f + 1 <= IN) by (intros Hc; replace (bits1 <? e) with true in Hpl by (symmetry; apply Z.ltb_lt; lia); apply andb_prop in Hpl as [H _]; apply Z.leb_le in H; lia).
    assert (Hin2 : bits1 + 8 < e -> f_in f + 2 <= IN).
    { intros Hc. replace (bits1 <? e) with true in Hpl by (symmetry; apply Z.ltb_lt; lia). apply andb_prop in Hpl as [_ H].
      replace (bits1 + 8 <? e) with true in H by (symmetry; apply Z.ltb_lt; lia). apply Z.leb_le in H. lia. }
    clear Hpl.
    pose proof Hinp_b as Hinb.
    set (f2 := mkF (f_in f) (f_out f) hold1 bits1 (f_len f) (code_val here) (f_op f) (f_from f) (f_ob f)) in *.
    destruct (dpull_eq X f2 e ltac:(subst f2; cbn; lia) ltac:(subst f2; cbn; lia) He16
                ltac:(subst f2; cbn; intros Hc; apply Hinb; lia) ltac:(subst f2; cbn; intros Hc; apply Hinb; lia)) as [Epull Bpull].
    subst f2. cbn [f_bits f_in f_hold f_out f_len f_dist f_op f_from f_ob x_input ffx_of] in Epull, Bpull.
    rewrite Epull in Hok |- *. clear Epull.
    destruct (dpull (ic_input c) (f_in f) hold1 bits1 e) as [[fin' hold'] bits'] eqn:Hdp.
    cbn [f_bits f_in f_hold f_out f_len f_dist f_op f_from f_ob] in Hok |- *.
    pose proof (dpull_cases _ _ _ _ _ _ _ _ Hdp) as Hdc.
    assert (Bb' : 0 <= bits' < 64) by lia. assert (Bi' : 0 <= fin' <= IN) by lia.
    rewrite (fdrop_eq _ e) in Hok |- *. cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob] in Hok |- *.
    apply andb_prop in Hok as [Heb Hok]. apply Z.leb_le in Heb.
    pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) ltac:(lia)) as Hpe0. pose proof (Z.mod_pos_bound hold' (2 ^ e) Hpe0) as Hme.
    pose proof (Z.pow_le_mono_r 2 e 15 ltac:(lia) ltac:(lia)) as Hpe. change (2 ^ 15) with 32768 in Hpe.
    rewrite (land_wrap32_zmask hold' e) in Hok |- * by lia.
    rewrite (wrap32_id (code_val here + hold' mod 2 ^ e)) in Hok |- * by lia.
    rewrite (Z.shiftr_div_pow2 hold' e) in Hok |- * by lia.
    rewrite (wrap32_id (bits' - e)) in Hok |- * by lia.
    rewrite (wrap32_id (f_out f - x_beg X)) in Hok |- * by lia.
    set (dist := code_val here + hold' mod 2 ^ e) in *. set (opd := f_out f - x_beg X) in *.
    apply andb_prop in Hok as [Hd1 Hok]. apply andb_prop in Hd1 as [Hd1 HfoN]. apply andb_prop in Hd1 as [Hd1 Hl3].
    apply Z.leb_le in Hd1. apply Z.leb_le in Hl3. apply Z.leb_le in HfoN.
    assert (Hh5 : 0 <= hold' / 2 ^ e < 2 ^ (bits' - e)).
    { split; [apply Z.div_pos; lia | apply shiftr_lt_pow2; lia]. }
    pose proof (blk_DX C (SAVED6 regs0 X) m (f_ob f) didx hold1 bits1 (f_in f) regs HK HM Hdidx H7 H27 H11 H17 H13 ltac:(lia) Hh1 Bi
                ltac:(intros Hc; apply Hin1; rewrite He; exact Hc) ltac:(intros Hc; apply Hin2; rewrite He; exact Hc)) as HDX.
    change (code_op (code_at s (is_distcode s) didx) mod 2 ^ 4) with (code_op here mod 2 ^ 4) in HDX.
    rewrite <- He, Hdp in HDX.
    destruct HDX as (R1 & Hms1 & HK1 & A1 & A25 & A11 & A27 & A13 & Hfr1 & _ & _ & _ & _ & Hd17).
    change (code_at s (is_distcode s) didx) with here in A27, Hd17.
    replace (hold' mod 2 ^ e + code_val here) with dist in A27, Hd17 by lia.
    destruct (blk_DOP C m e bits' dist (f_out f) R1 HK1 A1 A25 A27 ltac:(rewrite (Hfr1 14%bv eq_refl); exact H14)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (R2 & Hms2 & HK2 & B17 & Hfr2 & Hopd).
    fold opd in Hms2.
    set (f5 := mkF fin' (f_out f) (hold' / 2 ^ e) (bits' - e) (f_len f) dist (f_op f) (f_from f) (f_ob f)) in *.
    assert (B13 : getr R2 13 = zw (I0 + fin')) by (rewrite (Hfr2 13%bv eq_refl); exact A13).
    assert (B14 : getr R2 14 = zw (P0 + f_out f)) by (rewrite (Hfr2 14%bv eq_refl), (Hfr1 14%bv eq_refl); exact H14).
    assert (B26 : getr R2 26 = zw (f_len f)) by (rewrite (Hfr2 26%bv eq_refl), (Hfr1 26%bv eq_refl); exact H26).
    assert (B27 : getr R2 27 = zw dist) by (rewrite (Hfr2 27%bv eq_refl); exact A27).
    assert (B11 : getr R2 11 = zw (hold' / 2 ^ e)) by (rewrite (Hfr2 11%bv eq_refl); exact A11).
    assert (Bg3 : getr R2 3 = getr regs0 3) by (rewrite (Hfr2 3%bv eq_refl), (Hfr1 3%bv eq_refl); exact Hg3).
    assert (Bg4 : getr R2 4 = getr regs0 4) by (rewrite (Hfr2 4%bv eq_refl), (Hfr1 4%bv eq_refl); exact Hg4).
    pose proof (msteps_trans _ _ _ _ Hms1 Hms2) as Hpre2. clear Hms1 Hms2.
    destruct (Z.ltb_spec opd dist) as [Hwnd|Hdir].
    2:{
      replace (dist <=? opd) with true in Hpre2 by (symmetry; apply Z.leb_le; lia).
      destruct (blk_DCh C m dist (f_out f) R2 HK2 B14 B27 ltac:(lia) ltac:(lia)) as (R3 & Hms3 & HK3 & C14 & C7 & Hfr3).
      destruct (DO3 (SAVED6 regs0 X) m f5 R3 HK3 HM ltac:(subst f5; nf; rewrite C14; f_equal; lia) ltac:(subst f5; nf; exact C7)
                  ltac:(subst f5; nf; rewrite (Hfr3 27%bv eq_refl); exact B27)
                  ltac:(subst f5; nf; rewrite (Hfr3 26%bv eq_refl); exact B26)
                  ltac:(subst f5; nf; lia) ltac:(subst f5; nf; lia) ltac:(subst f5; nf; lia) ltac:(subst f5; nf; lia) ltac:(subst f5; nf; lia))
        as (R4 & m4 & Hms4 & HK4 & HM4 & D14 & Hfr4 & E1 & E2 & E3 & E4 & E5).
      subst f5. cbn [f_in f_hold f_bits f_out f_len f_dist] in E1, E2, E3, E4, E5.
      cbn [SIMRES]. exists R4, m4. split; [eapply msteps_trans; [exact Hpre2|]; eapply msteps_trans; [exact Hms3 | exact Hms4]|].
      unfold CINV. split; [exact HK4|]. split; [exact HM4|].
      split; [rewrite (Hfr4 3%bv eq_refl), (Hfr3 3%bv eq_refl); exact Bg3|]. split; [rewrite (Hfr4 4%bv eq_refl), (Hfr3 4%bv eq_refl); exact Bg4|].
      split; [rewrite (Hfr4 13%bv eq_refl), (Hfr3 13%bv eq_refl), B13, E1; reflexivity|]. split; [exact D14|].
      split; [rewrite (Hfr4 11%bv eq_refl), (Hfr3 11%bv eq_refl), B11, E2; reflexivity|].
      split; [rewrite (Hfr4 17%bv eq_refl), (Hfr3 17%bv eq_refl), B17, E3; reflexivity|].
      unfold FB. rewrite E1, E2, E3, E4. lia. }
    replace (dist <=? opd) with false in Hpre2 by (symmetry; apply Z.leb_gt; lia).
    rewrite (wrap32_id (dist - opd)) in Hok |- * by lia.
    set (opw := dist - opd) in *.
    destruct (blk_DW C (SAVED6 regs0 X) m (f_ob f) dist (f_out f) R2 HK2 HM B27 B14 ltac:(lia) ltac:(lia) ltac:(lia))
      as (R3 & Hms3 & HK3 & C7 & Hfr3 & Hopw & Herr).
    fold opd in Hms3, C7, Hopw, Herr. fold opw in Hms3, C7, Hopw, Herr.
    destruct ((x_whave X <? opw) && negb (x_sane X =? 0)) eqn:Eerr.
    {
      destruct (blk_FAR C (SAVED6 regs0 X) m (f_ob f) R3 HK3 HM) as (R4 & Hms4 & Hfr4).
      subst f5. cbn [SIMRES]. exists R4. eexists. split; [eapply msteps_trans; [exact Hpre2|]; eapply msteps_trans; [exact Hms3 | exact Hms4]|].
      pose proof HK3 as HKc. destruct HKc as (K2 & K10 & K12 & K15 & K16 & _).
      assert (X13 : getr R3 13 = zw (I0 + fin')) by (rewrite (Hfr3 13%bv eq_refl); exact B13).
      assert (X14 : getr R3 14 = zw (P0 + f_out f)) by (rewrite (Hfr3 14%bv eq_refl); exact B14).
      assert (X11 : getr R3 11 = zw (hold' / 2 ^ e)) by (rewrite (Hfr3 11%bv eq_refl); exact B11).
      assert (X17 : getr R3 17 = zw (bits' - e)) by (rewrite (Hfr3 17%bv eq_refl); exact B17).
      assert (X3 : getr R3 3 = getr regs0 3) by (rewrite (Hfr3 3%bv eq_refl); exact Bg3).
      assert (X4 : getr R3 4 = getr regs0 4) by (rewrite (Hfr3 4%bv eq_refl); exact Bg4).
      binv_close Hfr4 K2 K10 K12 K15 K16 X13 X14 X11 X17 X3 X4.
      split; [unfold FB, fset_op; cbn [f_hold f_bits f_in f_out]; lia|].
      exists m. split; [exact HM|]. reflexivity. }
    eapply SIMRES_steps; [eapply msteps_trans; [exact Hpre2 | exact Hms3]|].
    match goal with |- SIMRES _ _ _ _ ?res => change res with (FCont (copy_tail X (copy_while3 X (wplace X (fset_op f5 opw))))) end.
    apply (win_sim regs0 R3 m (fset_op f5 opw)); subst f5; cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob fset_op].
    all: first [ assumption | exact C7
               | rewrite (Hfr3 27%bv eq_refl); exact B27 | rewrite (Hfr3 26%bv eq_refl); exact B26 | rewrite (Hfr3 14%bv eq_refl); exact B14
               | rewrite (Hfr3 13%bv eq_refl); exact B13 | rewrite (Hfr3 11%bv eq_refl); exact B11 | rewrite (Hfr3 17%bv eq_refl); exact B17
               | rewrite (Hfr3 3%bv eq_refl); exact Bg3 | rewrite (Hfr3 4%bv eq_refl); exact Bg4
               | subst opw opd; lia | lia ].
Qed.

End Walk.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

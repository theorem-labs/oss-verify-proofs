(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout InflMem InffastModel InffastSafe.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InffastCtx IfSpec IfSpec6 If6_1 If6_2 If6_3 If6_4 If6_5I If6_5 If6_6.
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

Lemma dpull_cases : forall inp fin hold bits e fin' hold' bits',
  dpull inp fin hold bits e = (fin', hold', bits') ->
  (e <= bits /\ bits' = bits /\ fin' = fin /\ hold' = hold)
  \/ (bits < e <= bits + 8 /\ bits' = bits + 8 /\ fin' = fin + 1)
  \/ (bits + 8 < e /\ bits' = bits + 16 /\ fin' = fin + 2).
Proof.
  intros inp fin hold bits e fin' hold' bits' H. unfold dpull in H.
  destruct (Z.ltb_spec bits e); [destruct (Z.ltb_spec (bits + 8) e)|]; injection H as <- <- <-; lia.
Qed.


Lemma refill2_cases : forall inp fin hold bits fin' hold' bits',
  refill2 inp fin hold bits = (fin', hold', bits') -> (bits < 15 /\ fin' = fin + 2 /\ bits' = bits + 16) \/ (15 <= bits /\ fin' = fin /\ bits' = bits /\ hold' = hold).
Proof.
  intros inp fin hold bits fin' hold' bits' H. unfold refill2 in H. destruct (Z.ltb_spec bits 15); injection H as <- <- <-; lia.
Qed.
Lemma len_step_cases : forall inp fin hold bits val e fin' hold' bits' len,
  len_step inp fin hold bits val e = (fin', hold', bits', len) -> fin' = fin \/ fin' = fin + 1.
Proof.
  intros inp fin hold bits val e fin' hold' bits' len H. unfold len_step in H.
  destruct (Z.eqb_spec e 0); [|destruct (Z.ltb_spec bits e)]; injection H as <- <- <- <-; lia.
Qed.

Section Walk.
Context {mem : word -> option byte} {sp : Z} {ra : word}
        {s : inflate_state} {c : icall} {r : iregs}
        {ZP S I0 P0 WB : Z}.
Variable C : iff_pre s6u_segs is6_LENFIX is6_DISTFIX ROD6_LO ROD6_HI IMG6_TOP mem sp ra s c r ZP S I0 P0 WB.
Local Notation X := (ffx_of s c r).
Local Notation IN := (arr_len (ic_input c)).
Local Notation ON := (arr_len (ic_outbuf c)).
Local Notation WN := (arr_len (is_window s)).
Local Notation LC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_lencode s)).
Local Notation DC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_distcode s)).
Local Notation LCN := (ctab_len (is_lencode s)).
Local Notation DCN := (ctab_len (is_distcode s)).
Local Notation KR := (@KREGS6 sp ZP S I0 P0 WB X (is_lenbits s) (is_distbits s) LC DC).
Local Notation MEMI := (@MEMINV s6u_segs mem sp (arr_len (ic_outbuf c)) ZP S P0).
Let Hret := ifp_ret C.
Let Hzin := ifp_zs_in C. Let Hzain := ifp_zs_ain C. Let Hzout := ifp_zs_out C. Let Hzaout := ifp_zs_aout C. Let Hzst := ifp_zs_state C.
Let Hsc := ifp_scalars C. Let Hcodes := ifp_codes C. Let Hcodes_b := ifp_codes_b C.
Let Hwin := ifp_win C. Let Hwin_b := ifp_win_b C. Let Hinp := ifp_in C. Let Hinp_b := ifp_in_b C.
Let Hout := ifp_out C. Let Hout_b := ifp_out_b C. Let Hrod := ifp_rod C.
Let Hsp0 : 0x5f000 <= sp := proj1 (ifp_sp C). Let Hsp1 : sp + 160 < 2 ^ 63 := proj2 (ifp_sp C).
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
Let HalZ : ZP mod 8 = 0 := proj1 (ifp_align C). Let HalS : S mod 8 = 0 := proj2 (ifp_align C).
Let HI17 : 0 < I0 := proj1 (ifp_hi C).
Let HWpos : 0 < WN -> 0 < WB := proj2 (ifp_hi C).

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
Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.
Local Ltac via1 Ha H :=
  lazymatch type of H with getr _ ?r = _ => rewrite (Ha r eq_refl); exact H end.
Local Ltac clear_layout :=
  clear Hzin Hzain Hzout Hzaout Hzst Hsc Hcodes Hcodes_b Hwin Hwin_b Hinp Hinp_b Hout Hout_b Hrod
        Hd_spZ Hd_spS Hd_spI Hd_spP Hd_spW Hd_PZ Hd_PS Hd_PI Hd_PW Hd_ZS Hd_ZI Hd_ZW Hd_SI Hd_SW
        Hmap_sp Hmap_P Hmap_Z Hmap_S.
Local Ltac guards :=
  lazymatch goal with
  | |- @ex _ _ => idtac
  | |- Z.lxor (if 0 <? ?a then 1 else 0) (if ?b <? 1 then 1 else 0) <> 0 =>
      destruct (Z.ltb_spec 0 a); [| exfalso; mlia]; destruct (Z.ltb_spec b 1); [exfalso| discriminate];
      first [ mlia
            | match goal with H0 : Z.lxor ?o ?k < 1 |- _ =>
                pose proof (Z.lxor_nonneg o k) as HN; assert (HE : o = k) by (apply Z.lxor_eq; mlia); clear H0 HN; mlia end ]
  | |- Z.lxor 1 (if ?b <? 1 then 1 else 0) <> 0 =>
      destruct (Z.ltb_spec b 1); [exfalso; first [mlia | rewrite ?Z.lxor_m1_r in *; unfold Z.lnot in *; mlia] | discriminate]
  | |- _ => first [brc | mlia | progress (rewrite ?Z.lxor_m1_r; unfold Z.lnot); mlia | rewrite land1_mod2 by lia; mlia | idtac]
  end.
Local Ltac kr_destr HK := destruct HK as (K2 & K10 & K11 & K12 & K21 & K28 & K30 & K31 & K8 & K18 & K19 & K17 & K20 & K24 & K25 & K26).
Local Ltac nf :=
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob x_window x_input x_wsize x_wnext x_whave ffx_of];
  repeat first [rewrite cpn_in | rewrite cpn_out | rewrite cpn_hold | rewrite cpn_bits | rewrite cpn_len | rewrite cpn_dist];
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob x_window x_input x_wsize x_wnext x_whave ffx_of].
Local Ltac fz := nf; nf; rewrite ?Z2Nat.id by lia.
Local Ltac chase :=
  repeat match goal with
  | |- getr ?R ?k = _ =>
      first [ assumption
            | match goal with
              | Hf : forall r0, reg_in r0 _ = false -> getr R r0 = getr _ r0 |- _ => rewrite (Hf k eq_refl)
              | Hf : forall r0, getr R r0 = getr _ r0 |- _ => rewrite (Hf k)
              end ]
  end.
Local Ltac fin :=
  first [ assumption
        | match goal with H : getr ?R ?k = zw _ |- getr ?R ?k = zw _ => rewrite H; f_equal; cbn [faddr]; lia end
        | reflexivity | lia | cbn; lia ].

Definition FB (f : ffs) : Prop :=
  0 <= f_hold f < 2 ^ f_bits f /\ 0 <= f_bits f < 64 /\ ic_next_in c <= f_in f <= IN /\ x_beg X <= f_out f <= ON.

Definition CINV (regs0 R : bvmap 5 word) (m' : word -> option byte) (f' : ffs) : Prop :=
  KR R /\ MEMI (SAVED6 S P0 WB regs0 X) m' (f_ob f') /\ getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\
  getr R 16 = zw (I0 + f_in f') /\ getr R 22 = zw (P0 + f_out f') /\ getr R 14 = zw (f_hold f') /\ getr R 15 = zw (f_bits f') /\
  FB f'.

Definition BINV (regs0 R : bvmap 5 word) (m' : word -> option byte) (f' : ffs) (md : Z) (mg : option Z) : Prop :=
  getr R 2 = zw sp /\ getr R 10 = zw ZP /\ getr R 11 = zw S /\ getr R 12 = zw (I0 + x_last X) /\ getr R 21 = zw (P0 + x_end X) /\
  getr R 16 = zw (I0 + f_in f') /\ getr R 22 = zw (P0 + f_out f') /\ getr R 14 = zw (f_hold f') /\ getr R 15 = zw (f_bits f') /\
  getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\
  FB f' /\
  exists m0, MEMI (SAVED6 S P0 WB regs0 X) m0 (f_ob f') /\ m' = brk_mem m0 ZP S md mg.

Definition SIMRES (regs0 regs : bvmap 5 word) (m : word -> option byte) (pc : word) (res : fstep) : Prop :=
  match res with
  | FCont f' => exists R m', msteps s6u_segs (mkst regs pc m s6u_rom) (mkst R (0x22820 : word) m' s6u_rom) /\ CINV regs0 R m' f'
  | FBreak f' md mg => exists R m', msteps s6u_segs (mkst regs pc m s6u_rom) (mkst R (0x22d54 : word) m' s6u_rom) /\ BINV regs0 R m' f' md mg
  end.

Lemma SIMRES_steps : forall regs0 regs R m m2 (pc pc2 : word) res,
  msteps s6u_segs (mkst regs pc m s6u_rom) (mkst R pc2 m2 s6u_rom) -> SIMRES regs0 R m2 pc2 res -> SIMRES regs0 regs m pc res.
Proof.
  intros regs0 regs R m m2 pc pc2 res Hms Hres. destruct res as [f'|f' md mg]; cbn [SIMRES] in *;
    destruct Hres as (R' & m' & Hms' & H'); exists R', m'; (split; [eapply msteps_trans; [exact Hms | exact Hms'] | exact H']).
Qed.

Lemma slot48_in : forall regs0, In (48, 8%nat, x_dmask X) (SAVED6 S P0 WB regs0 X).
Proof. intros regs0. unfold SAVED6. cbn. do 13 right. left. reflexivity. Qed.
Lemma slot40_in : forall regs0, In (40, 8%nat, WB) (SAVED6 S P0 WB regs0 X).
Proof. intros regs0. unfold SAVED6. cbn. do 14 right. left. reflexivity. Qed.
Lemma slot32_in : forall regs0, In (32, 8%nat, P0 + x_beg X) (SAVED6 S P0 WB regs0 X).
Proof. intros regs0. unfold SAVED6. cbn. do 15 right. left. reflexivity. Qed.
Lemma slot24_in : forall regs0, In (24, 8%nat, x_whave X) (SAVED6 S P0 WB regs0 X).
Proof. intros regs0. unfold SAVED6. cbn. do 16 right. left. reflexivity. Qed.
Lemma slot16_in : forall regs0, In (16, 8%nat, S + 7160) (SAVED6 S P0 WB regs0 X).
Proof. intros regs0. unfold SAVED6. cbn. do 17 right. left. reflexivity. Qed.
Lemma slot8_in : forall regs0, In (8, 8%nat, x_wsize X) (SAVED6 S P0 WB regs0 X).
Proof. intros regs0. unfold SAVED6. cbn. do 18 right. left. reflexivity. Qed.
Lemma slot0_in : forall regs0, In (0, 8%nat, x_wsize X + x_wnext X) (SAVED6 S P0 WB regs0 X).
Proof. intros regs0. unfold SAVED6. cbn. do 19 right. left. reflexivity. Qed.

Lemma WB_pos : 0 < WN -> 0 < WB.
Proof. exact HWpos. Qed.

Lemma w3_simres : forall regs0 regs1 regs m1 m (pc1 : word) F,
  msteps s6u_segs (mkst regs1 pc1 m1 s6u_rom) (mkst regs (if f_len F <? 3 then (0x22cc8 : word) else (0x22c50 : word)) m s6u_rom) ->
  KR regs -> MEMI (SAVED6 S P0 WB regs0 X) m (f_ob F) ->
  getr regs 29 = zw (faddr WB P0 (f_from F)) -> getr regs 1 = zw (P0 + f_out F) -> getr regs 27 = zw (f_len F) ->
  getr regs 16 = zw (I0 + f_in F) -> getr regs 14 = zw (f_hold F) -> getr regs 15 = zw (f_bits F) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  0 <= f_len F < 2 ^ 17 -> srcn_ok WN (f_out F) (f_from F) (f_len F) ->
  0 <= f_hold F < 2 ^ f_bits F -> 0 <= f_bits F < 64 -> ic_next_in c <= f_in F <= IN -> x_beg X <= f_out F -> f_out F + f_len F <= ON ->
  SIMRES regs0 regs1 m1 pc1 (FCont (copy_tail X (copy_while3 X F))).
Proof.
  intros regs0 regs1 regs m1 m pc1 F Hpre HK HM H29 H1 H27 H16 H14 H15 Hg3 Hg4 Hlen Hsrc Bh Bb Bi Bo1 Bo2.
  destruct (w3 C (SAVED6 S P0 WB regs0 X) m F regs HK HM H29 H1 H27 Hlen Bo1 Bo2 Hsrc)
    as (R & m' & Hms & HK' & HM' & A22 & Hfr & E1 & E2 & E3 & E4 & E5).
  cbn [SIMRES]. exists R, m'. split; [eapply msteps_trans; [exact Hpre | exact Hms]|].
  unfold CINV. split; [exact HK'|]. split; [exact HM'|].
  split; [rewrite (Hfr 3%bv eq_refl); exact Hg3|]. split; [rewrite (Hfr 4%bv eq_refl); exact Hg4|].
  split; [rewrite (Hfr 16%bv eq_refl), H16, E1; reflexivity|]. split; [exact A22|].
  split; [rewrite (Hfr 14%bv eq_refl), H14, E2; reflexivity|]. split; [rewrite (Hfr 15%bv eq_refl), H15, E3; reflexivity|].
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

Lemma legB_join_simres : forall (hd : word) regs0 regs1 regs m1 m (pc1 : word) F wi,
  wlegB_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem) hd ->
  msteps s6u_segs (mkst regs1 pc1 m1 s6u_rom) (mkst regs hd m s6u_rom) ->
  KR regs -> MEMI (SAVED6 S P0 WB regs0 X) m (f_ob F) ->
  getr regs 6 = zw (WB + wi) -> getr regs 29 = zw (WB + wi) -> getr regs 22 = zw (P0 + f_out F) -> getr regs 13 = zw (P0 + f_out F) ->
  getr regs 5 = zw (f_op F) -> getr regs 27 = zw (f_len F - f_op F) -> getr regs 23 = zw (f_dist F) ->
  getr regs 16 = zw (I0 + f_in F) -> getr regs 14 = zw (f_hold F) -> getr regs 15 = zw (f_bits F) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  1 <= f_op F < f_len F -> f_len F < 2 ^ 17 -> 1 <= f_dist F < 2 ^ 17 -> f_dist F = f_op F + (f_out F - x_beg X) ->
  0 <= wi -> wi + f_op F <= WN -> f_out F + f_len F <= ON ->
  0 <= f_hold F < 2 ^ f_bits F -> 0 <= f_bits F < 64 -> ic_next_in c <= f_in F <= IN -> x_beg X <= f_out F ->
  SIMRES regs0 regs1 m1 pc1
    (FCont (copy_tail X (copy_while3 X
       (fset_from (fset_op (cpn X (Z.to_nat (f_op F)) (fset_len (fset_from F (FWin wi)) (f_len F - f_op F))) 0) (FOut (f_out F + f_op F - f_dist F)))))).
Proof.
  intros hd regs0 regs1 regs m1 m pc1 F wi WLEGB Hpre HK HM H6 H29 H22 H13 H5 H27 H23 H16 H14 H15 Hg3 Hg4 Hop Hlen Hdist Hopd Hwi0 Hwi1 HfoL Bh Bb Bi Bo.
  set (f1 := fset_len (fset_from F (FWin wi)) (f_len F - f_op F)).
  destruct (WLEGB (SAVED6 S P0 WB regs0 X) m f1 (Z.to_nat (f_op F)) wi regs HK ltac:(subst f1; exact HM) ltac:(subst f1; reflexivity)
              H6 H29 ltac:(subst f1; nf; exact H22) ltac:(subst f1; nf; exact H13) ltac:(rewrite Z2Nat.id by lia; exact H5)
              ltac:(lia) ltac:(lia) Hwi0 ltac:(lia) ltac:(subst f1; nf; lia) ltac:(subst f1; nf; lia))
    as (R3 & m3 & Hms3 & HK3 & HM3 & B22 & B13 & B1 & B6 & Hfr3).
  rewrite cpn_out in B22, B13, B1. subst f1. cbn [f_out fset_len fset_from] in B22, B13, B1. rewrite Z2Nat.id in B22, B13, B1 by lia.
  destruct (w3J C m3 (f_dist F) (f_out F + f_op F) (f_len F - f_op F) R3 HK3 B13 B1
              ltac:(rewrite (Hfr3 23%bv eq_refl); exact H23) ltac:(rewrite (Hfr3 27%bv eq_refl); exact H27) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - Hopd Bo Hop Hxbeg0; lia))
    as (R4 & Hms4 & HK4 & C29 & C1 & Hfr4).
  eapply (w3_simres regs0 regs1 R4 m1 m3).
  { eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hms3|]. nf. exact Hms4. }
  all: fz; chase; fin.
Qed.

Lemma stubA_simres : forall regs0 regs1 regs m1 m (pc1 : word) F wi,
  msteps s6u_segs (mkst regs1 pc1 m1 s6u_rom) (mkst regs (0x22c44 : word) m s6u_rom) ->
  KR regs -> MEMI (SAVED6 S P0 WB regs0 X) m (f_ob F) -> f_from F = FWin wi ->
  getr regs 29 = zw (WB + wi) -> getr regs 22 = zw (P0 + f_out F) -> getr regs 27 = zw (f_len F) ->
  getr regs 16 = zw (I0 + f_in F) -> getr regs 14 = zw (f_hold F) -> getr regs 15 = zw (f_bits F) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  0 <= f_len F < 2 ^ 17 -> 0 <= wi -> wi + f_len F <= WN -> f_out F + f_len F <= ON ->
  0 <= f_hold F < 2 ^ f_bits F -> 0 <= f_bits F < 64 -> ic_next_in c <= f_in F <= IN -> x_beg X <= f_out F ->
  SIMRES regs0 regs1 m1 pc1 (FCont (copy_tail X (copy_while3 X F))).
Proof.
  intros regs0 regs1 regs m1 m pc1 F wi Hpre HK HM HF H29 H22 H27 H16 H14 H15 Hg3 Hg4 Hlen Hwi0 Hwi1 HfoL Bh Bb Bi Bo.
  destruct (w3A m (WB + wi) (P0 + f_out F) (f_len F) regs HK H29 H22 H27 Hlen ltac:(lia)) as (R4 & Hms4 & HK4 & C29 & C1 & Hfr4).
  eapply (w3_simres regs0 regs1 R4 m1 m).
  { eapply msteps_trans; [exact Hpre | exact Hms4]. }
  all: rewrite ?HF; cbn [faddr]; chase; fin.
Qed.

Lemma win_sim : forall regs0 regs m F,
  KR regs -> MEMI (SAVED6 S P0 WB regs0 X) m (f_ob F) ->
  getr regs 5 = zw (f_op F) -> getr regs 23 = zw (f_dist F) -> getr regs 27 = zw (f_len F) -> getr regs 22 = zw (P0 + f_out F) ->
  getr regs 16 = zw (I0 + f_in F) -> getr regs 14 = zw (f_hold F) -> getr regs 15 = zw (f_bits F) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  1 <= f_op F -> f_dist F < 2 ^ 17 -> f_dist F = f_op F + (f_out F - x_beg X) -> 3 <= f_len F < 2 ^ 17 ->
  0 <= f_hold F < 2 ^ f_bits F -> 0 <= f_bits F < 64 -> ic_next_in c <= f_in F <= IN -> x_beg X <= f_out F ->
  window_ok X ON WN F = true ->
  SIMRES regs0 regs m (0x229d4 : word) (FCont (copy_tail X (copy_while3 X (wplace X F)))).
Proof.
  intros regs0 regs m F HK HM H5 H23 H27 H22 H16 H14 H15 Hg3 Hg4 Hop Hdist Hopd Hlen Bh Bb Bi Bo Hwok.
  pose proof Hwin_b as Hwb.
  unfold window_ok in Hwok. apply andb_prop in Hwok as [HfoL Hwok]. apply Z.leb_le in HfoL.
  destruct (blk_DWP C m (f_op F) regs HK H5 ltac:(lia)) as (R1 & Hms1 & Hfr1).
  pose proof (KREGS6_frame _ _ _ _ _ _ _ _ _ _ _ _ _ [] eq_refl HK (fun k _ => Hfr1 k)) as HK1.
  unfold wplace. unfold dwp_pc in Hms1. cbn [x_wsize x_wnext x_whave ffx_of] in Hms1, Hwok |- *.
  destruct (Z.eqb_spec (is_wnext s) 0) as [Hw0|Hw0].
  -
    apply andb_prop in Hwok as [Hk1 Hwok]. apply Z.leb_le in Hk1.
    assert (HWB : 0 < WB) by (apply WB_pos; destruct (Z.ltb_spec (f_op F) (f_len F)); apply Z.leb_le in Hwok; lia).
    destruct (blk_W1h C (SAVED6 S P0 WB regs0 X) m (f_ob F) (f_op F) (f_len F) (P0 + f_out F) R1 HK1 HM (slot8_in regs0) (slot40_in regs0) HWB
                ltac:(rewrite Hfr1; exact H5) ltac:(rewrite Hfr1; exact H27) ltac:(rewrite Hfr1; exact H22)
                ltac:(lia) ltac:(cbn [x_wsize ffx_of]; lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (R2 & Hms2 & HK2 & A29 & Alt & Age & Hfr2).
    cbn [x_wsize ffx_of] in A29, Alt.
    nf.
    destruct (Z.ltb_spec (f_op F) (f_len F)) as [Hol|Hol].
    +
      apply Z.leb_le in Hwok. destruct (Alt Hol) as (A6 & A13 & A5 & A27).
      rewrite copy_op_cpn by (nf; rewrite ?wrap32_id by lia; lia). nf. rewrite (wrap32_id (f_len F - f_op F)), Z2Nat.id by lia.
      eapply (legB_join_simres (0x22b98 : word) regs0 regs R2 m m _ F (is_wsize s - f_op F) (wlegB_22a2c C));
        [eapply msteps_trans; [exact Hms1 | exact Hms2] | ..].
      all: chase; fin.
    +
      apply Z.leb_le in Hwok.
      eapply (stubA_simres regs0 regs R2 m m _ (fset_from F (FWin (is_wsize s - f_op F))) (is_wsize s - f_op F));
        [eapply msteps_trans; [exact Hms1 | exact Hms2] | ..]; nf.
      all: chase; try exact (Age Hol); fin.
  - destruct (Z.ltb_spec (is_wnext s) (f_op F)) as [Hwl|Hwl].
    +
      apply andb_prop in Hwok as [Hk1 Hwok]. apply Z.leb_le in Hk1.
      assert (HWB : 0 < WB).
      { apply WB_pos. destruct (Z.ltb_spec (f_op F - is_wnext s) (f_len F)); [apply andb_prop in Hwok as [Hwok _]|]; apply Z.leb_le in Hwok; lia. }
      destruct (blk_W2h C (SAVED6 S P0 WB regs0 X) m (f_ob F) (f_op F) (f_len F) (P0 + f_out F) R1 HK1 HM (slot0_in regs0) (slot40_in regs0) HWB
                  ltac:(rewrite Hfr1; exact H5) ltac:(rewrite Hfr1; exact H27) ltac:(rewrite Hfr1; exact H22)
                  ltac:(cbn [x_wnext ffx_of]; lia) ltac:(cbn [x_wsize x_wnext ffx_of]; lia) ltac:(lia) ltac:(lia) ltac:(lia))
        as (R2 & Hms2 & HK2 & A29 & A1 & Alt & Age & Hfr2).
      cbn [x_wsize x_wnext ffx_of] in A29, A1, Alt, Age, Hms2.
      nf. rewrite (wrap32_id (f_op F - is_wnext s)) by lia.
      set (opp := f_op F - is_wnext s) in *.
      destruct (Z.ltb_spec opp (f_len F)) as [Hol|Hol].
      *
        apply andb_prop in Hwok as [Hk2 Hwok]. apply Z.leb_le in Hk2. destruct (Alt Hol) as (A6 & A7 & A5 & A27).
        rewrite (copy_op_cpn X (fset_len (fset_op (fset_from F _) _) _)) by (nf; rewrite ?wrap32_id by lia; lia). nf.
        rewrite (wrap32_id (f_len F - opp)) by lia. rewrite ?Z2Nat.id by lia.
        set (f1 := fset_len (fset_op (fset_from F (FWin (is_wsize s + is_wnext s - f_op F))) opp) (f_len F - opp)).
        destruct (wlegA C (SAVED6 S P0 WB regs0 X) m f1 (Z.to_nat opp) (is_wsize s + is_wnext s - f_op F) R2 HK2 ltac:(subst f1; exact HM) ltac:(subst f1; reflexivity)
                    A6 A29 ltac:(subst f1; nf; rewrite (Hfr2 22%bv eq_refl), Hfr1; exact H22) ltac:(subst f1; nf; exact A7)
                    ltac:(subst f1; nf; rewrite A5; f_equal; lia) ltac:(rewrite Z2Nat.id by lia; exact A1)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(subst f1; nf; lia) ltac:(subst f1; nf; lia))
          as (R3 & m3 & Hms3 & HK3 & HM3 & B22 & B13 & B9 & B6 & Hfr3).
        subst f1. nf. rewrite cpn_out in B22, B13, B9. cbn [f_out fset_len fset_op fset_from] in B22, B13, B9. rewrite Z2Nat.id in B22, B13, B9 by lia.
        destruct (blk_W2m C (SAVED6 S P0 WB regs0 X) m3 _ (f_len F - opp) R3 HK3 HM3 (slot40_in regs0)
                    ltac:(rewrite (Hfr3 27%bv eq_refl); exact A27) ltac:(lia))
          as (R4 & Hms4 & HK4 & Clt & Cge & Hfr4).
        cbn [x_wnext ffx_of] in Hms4, Clt, Cge.
        destruct (Z.ltb_spec (is_wnext s) (f_len F - opp)) as [Hw2|Hw2].
        --
           apply Z.leb_le in Hwok. destruct (Clt Hw2) as (C5 & C7 & C29 & C27).
           rewrite copy_op_cpn by (nf; rewrite ?wrap32_id by lia; lia). nf. rewrite (wrap32_id (f_len F - opp - is_wnext s)) by lia. rewrite ?Z2Nat.id by lia.
           set (f2 := fset_len (fset_op (fset_from (cpn X (Z.to_nat opp)
                        (fset_len (fset_op (fset_from F (FWin (is_wsize s + is_wnext s - f_op F))) opp) (f_len F - opp))) (FWin 0)) (is_wnext s))
                        (f_len F - opp - is_wnext s)).
           destruct (wleg2 C (SAVED6 S P0 WB regs0 X) m3 f2 R4 HK4 ltac:(subst f2; exact HM3) ltac:(subst f2; reflexivity) C5 C7
                       ltac:(subst f2; nf; rewrite (Hfr4 13%bv eq_refl), B13; f_equal; lia)
                       ltac:(subst f2; nf; rewrite (Hfr4 9%bv eq_refl), B9; f_equal; lia)
                       ltac:(exact C29)
                       ltac:(cbn [x_wnext ffx_of]; lia) ltac:(cbn [x_wnext ffx_of]; lia) ltac:(subst f2; nf; lia) ltac:(subst f2; nf; lia))
             as (R5 & m5 & Hms5 & HK5 & HM5 & D13 & D1 & D9 & Hfr5).
           subst f2. nf. rewrite cpn_out in D13, D1, D9. cbn [f_out fset_len fset_op fset_from] in D13, D1, D9. rewrite cpn_out in D13, D1, D9.
           cbn [f_out fset_len fset_op fset_from x_wnext ffx_of] in D13, D1, D9. rewrite !Z2Nat.id in D13, D1, D9 by lia.
           destruct (blk_W2e C m5 (f_dist F) (f_out F + opp + is_wnext s) (f_len F - opp - is_wnext s) R5 HK5
                       ltac:(rewrite D9; f_equal; lia) ltac:(rewrite D1; f_equal; lia)
                       ltac:(rewrite (Hfr5 23%bv eq_refl), (Hfr4 23%bv eq_refl), (Hfr3 23%bv eq_refl), (Hfr2 23%bv eq_refl), Hfr1; exact H23)
                       ltac:(rewrite (Hfr5 27%bv eq_refl); exact C27) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - Hopd Bo Hop Hxbeg0 Hwl Hol Hw2; subst opp; lia))
             as (R6 & Hms6 & HK6 & E29 & E1 & Hfr6).
           eapply (w3_simres regs0 regs R6 m m5).
           { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
             eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5|]. nf. exact Hms6. }
           all: fz; chase; fin.
        --
           apply Z.leb_le in Hwok.
           destruct (w3B C (SAVED6 S P0 WB regs0 X) m3 _ (P0 + (f_out F + opp)) (f_len F - opp) R4 HK4 HM3 (slot40_in regs0)
                       ltac:(rewrite (Hfr4 13%bv eq_refl); exact B13) ltac:(exact (Cge Hw2)) ltac:(lia) ltac:(lia))
             as (R6 & Hms6 & HK6 & E29 & E1 & Hfr6).
           eapply (w3_simres regs0 regs R6 m m3).
           { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
             eapply msteps_trans; [exact Hms4|]. nf. exact Hms6. }
           all: fz; chase; try exact (Cge Hw2); fin.
      *
        apply Z.leb_le in Hwok.
        eapply (stubA_simres regs0 regs R2 m m _ (fset_op (fset_from F (FWin (is_wsize s + is_wnext s - f_op F))) opp) (is_wsize s + is_wnext s - f_op F));
          [eapply msteps_trans; [exact Hms1 | exact Hms2] | ..]; nf.
        all: chase; try exact (Age Hol); fin.
    +
      assert (HWB : 0 < WB) by (apply WB_pos; destruct (Z.ltb_spec (f_op F) (f_len F)); apply Z.leb_le in Hwok; lia).
      destruct (blk_W3h C (SAVED6 S P0 WB regs0 X) m (f_ob F) (f_op F) (f_len F) (P0 + f_out F) R1 HK1 HM (slot40_in regs0) HWB
                  ltac:(rewrite Hfr1; exact H5) ltac:(rewrite Hfr1; exact H27) ltac:(rewrite Hfr1; exact H22)
                  ltac:(lia) ltac:(cbn [x_wnext ffx_of]; lia) ltac:(lia) ltac:(lia) ltac:(lia))
        as (R2 & Hms2 & HK2 & A29 & Alt & Age & Hfr2).
      cbn [x_wnext ffx_of] in A29, Alt.
      nf.
      destruct (Z.ltb_spec (f_op F) (f_len F)) as [Hol|Hol].
      * fz. apply Z.leb_le in Hwok. destruct (Alt Hol) as (A6 & A13 & A5 & A27).
        rewrite copy_op_cpn by (nf; rewrite ?wrap32_id by lia; lia). nf. rewrite (wrap32_id (f_len F - f_op F)), Z2Nat.id by lia.
        eapply (legB_join_simres (0x22c04 : word) regs0 regs R2 m m _ F (is_wnext s - f_op F) (wlegB_22a98 C));
          [eapply msteps_trans; [exact Hms1 | exact Hms2] | ..].
        all: chase; fin.
      * fz. apply Z.leb_le in Hwok.
        eapply (stubA_simres regs0 regs R2 m m _ (fset_from F (FWin (is_wnext s - f_op F))) (is_wnext s - f_op F));
          [eapply msteps_trans; [exact Hms1 | exact Hms2] | ..]; nf.
        all: chase; try exact (Age Hol); fin.
Qed.

Local Ltac binv_close Hf K2 K10 K11 K12 K21 X16 X22 X14 X15 X3 X4 :=
  unfold BINV; cbn [f_in f_out f_hold f_bits f_ob fset_op];
  split; [rewrite (Hf 2%bv eq_refl); exact K2|]; split; [rewrite (Hf 10%bv eq_refl); exact K10|]; split; [rewrite (Hf 11%bv eq_refl); exact K11|];
  split; [rewrite (Hf 12%bv eq_refl); exact K12|]; split; [rewrite (Hf 21%bv eq_refl); exact K21|];
  split; [rewrite (Hf 16%bv eq_refl); exact X16|]; split; [rewrite (Hf 22%bv eq_refl); exact X22|];
  split; [rewrite (Hf 14%bv eq_refl); exact X14|]; split; [rewrite (Hf 15%bv eq_refl); exact X15|];
  split; [rewrite (Hf 3%bv eq_refl); exact X3|]; split; [rewrite (Hf 4%bv eq_refl); exact X4|].

Lemma dodist_sim : forall k regs0 regs m f didx,
  let here := code_at s (is_distcode s) didx in
  let cb := code_bits here in
  KR regs -> MEMI (SAVED6 S P0 WB regs0 X) m (f_ob f) ->
  getr regs 13 = zw (DC + 4 * didx) -> getr regs 5 = zw (code_op here) ->
  getr regs 14 = zw (f_hold f / 2 ^ cb) -> getr regs 15 = zw (f_bits f - cb) ->
  getr regs 16 = zw (I0 + f_in f) -> getr regs 22 = zw (P0 + f_out f) -> getr regs 27 = zw (f_len f) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  0 <= didx < DCN -> cb <= f_bits f -> FB f -> 0 <= f_len f < 2 ^ 17 ->
  dodist_ok X s IN ON WN k here f = true ->
  SIMRES regs0 regs m (dd_pc (code_op here)) (dodist k X s here f).
Proof.
  induction k as [|k IH]; intros regs0 regs m f didx here cb HK HM H13 H5 H14 H15 H16 H22 H27 Hg3 Hg4 Hdidx Hcb HFB Hlen Hok.
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
  destruct (Z.eqb_spec (Z.land (code_op here) 16) 0) as [Ho16|Ho16]; cbn [negb] in Hok |- *.
  -
    destruct (blk_DD1 m (code_op here) regs HK H5 ltac:(lia)) as (R1 & Hms1 & HK1 & Hfr1). unfold dd1_pc in Hms1.
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
      destruct (blk_DL2 C (SAVED6 S P0 WB regs0 X) m (f_ob f) didx hold1 bits1 R1 HK1 HM Hdidx
                  ltac:(rewrite (Hfr1 13%bv eq_refl); exact H13) ltac:(rewrite (Hfr1 5%bv eq_refl); exact H5)
                  ltac:(rewrite (Hfr1 14%bv eq_refl); exact H14) ltac:(rewrite (Hfr1 15%bv eq_refl); exact H15)
                  ltac:(lia) ltac:(exact Hh1) Hop16 ltac:(exact Hi) ltac:(exact Hcb'))
        as (R2 & Hms2 & HK2 & B13 & B5 & B14 & B15 & Hfr2 & Bh2 & Bb2).
      eapply SIMRES_steps; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      apply (IH regs0 R2 m f1 didx'); cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob].
      all: try assumption.
      * chase.
      * chase.
      * chase.
      * chase.
      * chase.
      * lia.
      * unfold FB. subst f1. cbn [f_hold f_bits f_in f_out]. lia.
    +
      destruct (blk_BADD C (SAVED6 S P0 WB regs0 X) m (f_ob f) R1 HK1 HM) as (R2 & Hms2 & Hfr2).
      cbn [SIMRES]. exists R2. eexists. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      pose proof HK1 as HKc. destruct HKc as (K2 & K10 & K11 & K12 & K21 & _).
      assert (X16 : getr R1 16 = zw (I0 + f_in f)) by (rewrite (Hfr1 16%bv eq_refl); exact H16).
      assert (X22 : getr R1 22 = zw (P0 + f_out f)) by (rewrite (Hfr1 22%bv eq_refl); exact H22).
      assert (X14 : getr R1 14 = zw (f_hold f / 2 ^ cb)) by (rewrite (Hfr1 14%bv eq_refl); exact H14).
      assert (X15 : getr R1 15 = zw (f_bits f - cb)) by (rewrite (Hfr1 15%bv eq_refl); exact H15).
      assert (X3 : getr R1 3 = getr regs0 3) by (rewrite (Hfr1 3%bv eq_refl); exact Hg3).
      assert (X4 : getr R1 4 = getr regs0 4) by (rewrite (Hfr1 4%bv eq_refl); exact Hg4).
      binv_close Hfr2 K2 K10 K11 K12 K21 X16 X22 X14 X15 X3 X4.
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
    assert (Bb' : 0 <= bits' < 64) by lia. assert (Bi' : ic_next_in c <= fin' <= IN) by lia.
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
    pose proof (blk_DX C (SAVED6 S P0 WB regs0 X) m (f_ob f) didx hold1 bits1 (f_in f) regs HK HM Hdidx H13 H5 H14 H15 H16 ltac:(lia) Hh1 ltac:(lia)
                ltac:(intros Hc; apply Hin1; rewrite He; exact Hc) ltac:(intros Hc; apply Hin2; rewrite He; exact Hc)) as HDX.
    change (code_op (code_at s (is_distcode s) didx) mod 2 ^ 4) with (code_op here mod 2 ^ 4) in HDX.
    rewrite <- He, Hdp in HDX.
    destruct HDX as (R1 & Hms1 & HK1 & A13 & A15 & A14 & A23 & A16 & Hfr1 & _ & _ & _).
    change (code_at s (is_distcode s) didx) with here in A23.
    destruct (blk_DOP C (SAVED6 S P0 WB regs0 X) m (f_ob f) e bits' hold' (code_val here) (f_out f) R1 HK1 HM (slot32_in regs0)
                A13 A15 A14 A23 ltac:(rewrite (Hfr1 22%bv eq_refl); exact H22)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (R2 & Hms2 & HK2 & B15 & B14 & B23 & B6 & Hfr2 & _ & Hd17 & _).
    replace (hold' mod 2 ^ e + code_val here) with dist in Hms2, B23, Hd17 by lia.
    fold opd in Hms2.
    set (f5 := mkF fin' (f_out f) (hold' / 2 ^ e) (bits' - e) (f_len f) dist (f_op f) (f_from f) (f_ob f)) in *.
    assert (B16 : getr R2 16 = zw (I0 + fin')) by (rewrite (Hfr2 16%bv eq_refl); exact A16).
    assert (B22 : getr R2 22 = zw (P0 + f_out f)) by (rewrite (Hfr2 22%bv eq_refl), (Hfr1 22%bv eq_refl); exact H22).
    assert (B27 : getr R2 27 = zw (f_len f)) by (rewrite (Hfr2 27%bv eq_refl), (Hfr1 27%bv eq_refl); exact H27).
    assert (Bg3 : getr R2 3 = getr regs0 3) by (rewrite (Hfr2 3%bv eq_refl), (Hfr1 3%bv eq_refl); exact Hg3).
    assert (Bg4 : getr R2 4 = getr regs0 4) by (rewrite (Hfr2 4%bv eq_refl), (Hfr1 4%bv eq_refl); exact Hg4).
    pose proof (msteps_trans _ _ _ _ Hms1 Hms2) as Hpre2. clear Hms1 Hms2.
    destruct (Z.ltb_spec opd dist) as [Hwnd|Hdir].
    2:{
      replace (dist <=? opd) with true in Hpre2 by (symmetry; apply Z.leb_le; lia).
      destruct (blk_DCh C m dist (f_out f) R2 HK2 B22 B23 ltac:(lia) ltac:(lia) ltac:(clear - Hdir Hxbeg0 Bo; subst opd; lia)) as (R3 & Hms3 & HK3 & C5 & C29 & Hfr3).
      destruct (do3 C (SAVED6 S P0 WB regs0 X) m f5 R3 HK3 HM ltac:(subst f5; nf; rewrite (Hfr3 22%bv eq_refl); exact B22) ltac:(subst f5; nf; exact C29)
                  ltac:(exact C5) ltac:(subst f5; nf; rewrite (Hfr3 27%bv eq_refl); exact B27)
                  ltac:(subst f5; nf; lia) ltac:(subst f5; nf; lia) ltac:(subst f5; nf; lia) ltac:(subst f5; nf; lia) ltac:(subst f5; nf; lia))
        as (R4 & m4 & Hms4 & HK4 & HM4 & D22 & Hfr4 & E1 & E2 & E3 & E4 & E5).
      subst f5. cbn [f_in f_hold f_bits f_out f_len f_dist] in E1, E2, E3, E4, E5.
      cbn [SIMRES]. exists R4, m4. split; [eapply msteps_trans; [exact Hpre2|]; eapply msteps_trans; [exact Hms3 | exact Hms4]|].
      unfold CINV. split; [exact HK4|]. split; [exact HM4|].
      split; [rewrite (Hfr4 3%bv eq_refl), (Hfr3 3%bv eq_refl); exact Bg3|]. split; [rewrite (Hfr4 4%bv eq_refl), (Hfr3 4%bv eq_refl); exact Bg4|].
      split; [rewrite (Hfr4 16%bv eq_refl), (Hfr3 16%bv eq_refl), B16, E1; reflexivity|]. split; [exact D22|].
      split; [rewrite (Hfr4 14%bv eq_refl), (Hfr3 14%bv eq_refl), B14, E2; reflexivity|].
      split; [rewrite (Hfr4 15%bv eq_refl), (Hfr3 15%bv eq_refl), B15, E3; reflexivity|].
      unfold FB. rewrite E1, E2, E3, E4. lia. }
    replace (dist <=? opd) with false in Hpre2 by (symmetry; apply Z.leb_gt; lia).
    rewrite (wrap32_id (dist - opd)) in Hok |- * by lia.
    set (opw := dist - opd) in *.
    destruct (blk_DW C (SAVED6 S P0 WB regs0 X) m (f_ob f) dist (f_out f) R2 HK2 HM (slot24_in regs0) (slot16_in regs0) B23 B22 B6
                ltac:(lia) ltac:(lia) ltac:(lia))
      as (R3 & Hms3 & HK3 & C5 & Hfr3 & Hopw & Herr).
    fold opd in Hms3, C5, Hopw, Herr. fold opw in Hms3, C5, Hopw, Herr.
    destruct ((x_whave X <? opw) && negb (x_sane X =? 0)) eqn:Eerr.
    {
      destruct (blk_FAR C (SAVED6 S P0 WB regs0 X) m (f_ob f) R3 HK3 HM) as (R4 & Hms4 & Hfr4).
      subst f5. cbn [SIMRES]. exists R4. eexists. split; [eapply msteps_trans; [exact Hpre2|]; eapply msteps_trans; [exact Hms3 | exact Hms4]|].
      pose proof HK3 as HKc. destruct HKc as (K2 & K10 & K11 & K12 & K21 & _).
      assert (X16 : getr R3 16 = zw (I0 + fin')) by (rewrite (Hfr3 16%bv eq_refl); exact B16).
      assert (X22 : getr R3 22 = zw (P0 + f_out f)) by (rewrite (Hfr3 22%bv eq_refl); exact B22).
      assert (X14 : getr R3 14 = zw (hold' / 2 ^ e)) by (rewrite (Hfr3 14%bv eq_refl); exact B14).
      assert (X15 : getr R3 15 = zw (bits' - e)) by (rewrite (Hfr3 15%bv eq_refl); exact B15).
      assert (X3 : getr R3 3 = getr regs0 3) by (rewrite (Hfr3 3%bv eq_refl); exact Bg3).
      assert (X4 : getr R3 4 = getr regs0 4) by (rewrite (Hfr3 4%bv eq_refl); exact Bg4).
      binv_close Hfr4 K2 K10 K11 K12 K21 X16 X22 X14 X15 X3 X4.
      split; [unfold FB, fset_op; cbn [f_hold f_bits f_in f_out]; lia|].
      exists m. split; [exact HM|]. reflexivity. }
    eapply SIMRES_steps; [eapply msteps_trans; [exact Hpre2 | exact Hms3]|].
    match goal with |- SIMRES _ _ _ _ ?res => change res with (FCont (copy_tail X (copy_while3 X (wplace X (fset_op f5 opw))))) end.
    apply (win_sim regs0 R3 m (fset_op f5 opw)); subst f5; cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob fset_op].
    all: first [ assumption | exact C5 | chase; assumption | subst opw opd; lia | lia ].
Qed.
End Walk.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

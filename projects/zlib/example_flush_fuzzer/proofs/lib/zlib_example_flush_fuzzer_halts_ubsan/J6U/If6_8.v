(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem InffastModel InffastSafe.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InffastCtx IfSpec IfSpec6 If6_1 If6_2 If6_3 If6_4 If6_5I If6_5 If6_6 If6_7.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma len_if_eq : forall x f e,
  0 <= f_hold f < 2 ^ f_bits f -> 0 <= f_bits f < 64 -> 0 <= e < 16 -> 0 <= f_len f < 65536 ->
  (e <> 0 -> f_bits f < e -> 0 <= arr_get (x_input x) (f_in f) < 256 /\ e <= f_bits f + 8) ->
  (if negb (e =? 0) then
     fdrop (fset_len (if f_bits f <? e then fpull x f else f)
              (wrap32 (f_len (if f_bits f <? e then fpull x f else f)
                       + Z.land (wrap32 (f_hold (if f_bits f <? e then fpull x f else f))) (zmask e)))) e
   else f)
  = (let '(i, h, b, l) := len_step (x_input x) (f_in f) (f_hold f) (f_bits f) (f_len f) e in
     mkF i (f_out f) h b l (f_dist f) (f_op f) (f_from f) (f_ob f)).
Proof.
  intros x f e Hh Hb He Hl Hv. unfold len_step.
  pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) ltac:(lia)) as Hpe0.
  pose proof (Z.pow_le_mono_r 2 e 15 ltac:(lia) ltac:(lia)) as Hpe. change (2 ^ 15) with 32768 in Hpe.
  destruct (Z.eqb_spec e 0) as [He0|He0]; cbn [negb]; [destruct f; reflexivity|].
  destruct (Z.ltb_spec (f_bits f) e) as [Hlt|Hge].
  - destruct (Hv He0 Hlt) as [Hin Hle].
    destruct (fpull_eq x f ltac:(lia) ltac:(lia) ltac:(lia) Hin) as [E B]. rewrite E.
    cbn [f_len f_hold f_in f_out f_bits f_dist f_op f_from f_ob fset_len]. rewrite fdrop_eq.
    cbn [f_len f_hold f_in f_out f_bits f_dist f_op f_from f_ob fset_len].
    pose proof (Z.pow_pos_nonneg 2 (f_bits f) ltac:(lia) ltac:(lia)) as Hp.
    assert (H0 : 0 <= f_hold f + arr_get (x_input x) (f_in f) * 2 ^ f_bits f) by nia.
    pose proof (Z.mod_pos_bound (f_hold f + arr_get (x_input x) (f_in f) * 2 ^ f_bits f) (2 ^ e) Hpe0) as Hm.
    rewrite land_wrap32_zmask by lia. rewrite (wrap32_id (f_len f + _)) by lia.
    rewrite Z.shiftr_div_pow2 by lia. rewrite (wrap32_id (f_bits f + 8 - e)) by lia.
    f_equal; lia.
  - rewrite fdrop_eq. cbn [f_len f_hold f_in f_out f_bits f_dist f_op f_from f_ob fset_len].
    pose proof (Z.mod_pos_bound (f_hold f) (2 ^ e) Hpe0) as Hm.
    rewrite land_wrap32_zmask by lia. rewrite (wrap32_id (f_len f + _)) by lia.
    rewrite Z.shiftr_div_pow2 by lia. rewrite (wrap32_id (f_bits f - e)) by lia.
    f_equal; lia.
Qed.

Lemma dodist_ok_bits : forall x st IN ON WN k h f, dodist_ok x st IN ON WN k h f = true -> code_bits h <= f_bits f.
Proof.
  intros x st IN ON WN [|k] h f H; cbn [dodist_ok] in H; [discriminate H|].
  apply andb_prop in H as [H _]. apply Z.leb_le in H. exact H.
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
Local Notation FB := (FB (s:=s) (c:=c) (r:=r)).
Local Notation CINV := (CINV (mem:=mem) (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB)).
Local Notation BINV := (BINV (mem:=mem) (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB)).
Local Notation SIMRES := (SIMRES (mem:=mem) (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB)).
Local Notation SIMRES_steps := (SIMRES_steps (mem:=mem) (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB)).
Local Notation DODIST := (dodist_sim C).

Lemma dolen_sim : forall k regs0 regs m f idx,
  let here := code_at s (is_lencode s) idx in
  let cb := code_bits here in
  KR regs -> MEMI (SAVED6 S P0 WB regs0 X) m (f_ob f) ->
  getr regs 5 = zw (LC + 4 * idx) -> getr regs 13 = zw (code_op here) ->
  getr regs 14 = zw (f_hold f / 2 ^ cb) -> getr regs 15 = zw (f_bits f - cb) ->
  getr regs 16 = zw (I0 + f_in f) -> getr regs 22 = zw (P0 + f_out f) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  0 <= idx < LCN -> cb <= f_bits f -> FB f ->
  dolen_ok X s IN ON WN k here f = true ->
  SIMRES regs0 regs m (dl_pc (code_op here)) (dolen k X s here f).
Proof.
  induction k as [|k IH]; intros regs0 regs m f idx here cb HK HM H5 H13 H14 H15 H16 H22 Hg3 Hg4 Hidx Hcb HFB Hok.
  { cbn [dolen_ok] in Hok. discriminate Hok. }
  destruct HFB as (Bh & Bb & Bi & Bo).
  pose proof (code_op_range here) as Hop. pose proof (code_bits_range here) as Hcbr. pose proof (code_val_range here) as Hval.
  assert (Hh1 : 0 <= f_hold f / 2 ^ cb < 2 ^ (f_bits f - cb)).
  { split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | apply shiftr_lt_pow2; lia]. }
  assert (Hh64 : f_hold f / 2 ^ cb < 2 ^ 64).
  { pose proof (Z.pow_le_mono_r 2 (f_bits f - cb) 64 ltac:(lia) ltac:(lia)). lia. }
  cbn [dolen_ok] in Hok. fold here cb in Hok. apply andb_prop in Hok as [_ Hok].
  cbn [dolen]. fold here cb.
  rewrite (fdrop_eq f cb) in Hok |- *. rewrite (Z.shiftr_div_pow2 (f_hold f) cb), (wrap32_id (f_bits f - cb)) in Hok |- * by lia.
  cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob] in Hok |- *.
  set (hold1 := f_hold f / 2 ^ cb) in *. set (bits1 := f_bits f - cb) in *.
  unfold dl_pc.
  destruct (Z.eqb_spec (code_op here) 0) as [Hop0|Hop0].
  -
    apply Z.ltb_lt in Hok.
    destruct (blk_LIT C (SAVED6 S P0 WB regs0 X) m (f_ob f) idx (f_out f) regs HK HM Hidx H5 H22 ltac:(lia)) as (R1 & m1 & Hms1 & HK1 & A22 & Hfr1 & HM1).
    cbn [SIMRES]. exists R1, m1. split; [exact Hms1|].
    unfold CINV, fset_out, fset_ob. cbn [f_in f_out f_hold f_bits f_ob f_len f_dist f_op f_from].
    split; [exact HK1|]. split; [exact HM1|].
    split; [rewrite (Hfr1 3%bv eq_refl); exact Hg3|]. split; [rewrite (Hfr1 4%bv eq_refl); exact Hg4|].
    split; [rewrite (Hfr1 16%bv eq_refl); exact H16|]. split; [exact A22|].
    split; [rewrite (Hfr1 14%bv eq_refl); exact H14|]. split; [rewrite (Hfr1 15%bv eq_refl); exact H15|].
    unfold If6_7.FB. cbn [f_hold f_bits f_in f_out]. lia.
  - destruct (blk_D1 m (code_op here) regs HK H13 ltac:(lia)) as (R1 & Hms1 & HK1 & A13 & Hfr1). unfold d1_pc in Hms1.
    assert (B5 : getr R1 5 = zw (LC + 4 * idx)) by (rewrite (Hfr1 5%bv eq_refl); exact H5).
    assert (B14 : getr R1 14 = zw hold1) by (rewrite (Hfr1 14%bv eq_refl); exact H14).
    assert (B15 : getr R1 15 = zw bits1) by (rewrite (Hfr1 15%bv eq_refl); exact H15).
    assert (B16 : getr R1 16 = zw (I0 + f_in f)) by (rewrite (Hfr1 16%bv eq_refl); exact H16).
    assert (B22 : getr R1 22 = zw (P0 + f_out f)) by (rewrite (Hfr1 22%bv eq_refl); exact H22).
    assert (Bg3 : getr R1 3 = getr regs0 3) by (rewrite (Hfr1 3%bv eq_refl); exact Hg3).
    assert (Bg4 : getr R1 4 = getr regs0 4) by (rewrite (Hfr1 4%bv eq_refl); exact Hg4).
    destruct (Z.eqb_spec (Z.land (code_op here) 16) 0) as [Ho16|Ho16]; cbn [negb] in Hok, Hms1 |- *.
    + destruct (Z.eqb_spec (Z.land (code_op here) 64) 0) as [Ho64|Ho64]; cbn [negb] in Hms1.
      *
        apply andb_prop in Hok as [Hop16 Hok]. apply andb_prop in Hok as [Hi Hok]. apply Z.ltb_lt in Hop16. apply Z.ltb_lt in Hi.
        rewrite (land_zmask hold1 (code_op here)) in Hi, Hok |- * by lia.
        set (idx' := code_val here + hold1 mod 2 ^ code_op here) in *.
        pose proof (Z.mod_pos_bound hold1 (2 ^ code_op here) ltac:(apply Z.pow_pos_nonneg; lia)) as Hhm.
        assert (Hcb' : code_bits (code_at s (is_lencode s) idx') <= bits1).
        { destruct k as [|k'']; cbn [dolen_ok] in Hok; [discriminate Hok|]. apply andb_prop in Hok as [Hc _]. apply Z.leb_le in Hc. exact Hc. }
        destruct (blk_L2 C (SAVED6 S P0 WB regs0 X) m (f_ob f) idx hold1 bits1 R1 HK1 HM Hidx B5 A13 B14 B15 ltac:(lia) ltac:(exact Hh1) Hop16
                    ltac:(exact Hi) ltac:(exact Hcb'))
          as (R2 & Hms2 & HK2 & C7 & C25 & C14 & C15 & Hfr2 & Bh2 & Bb2).
        eapply SIMRES_steps; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        apply (IH regs0 R2 m (mkF (f_in f) (f_out f) hold1 bits1 (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f)) idx');
          cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob].
        all: try assumption.
        -- rewrite (Hfr2 16%bv eq_refl). exact B16.
        -- rewrite (Hfr2 22%bv eq_refl). exact B22.
        -- rewrite (Hfr2 3%bv eq_refl). exact Bg3.
        -- rewrite (Hfr2 4%bv eq_refl). exact Bg4.
        -- lia.
        -- unfold If6_7.FB. cbn [f_hold f_bits f_in f_out]. lia.
      *
        destruct (blk_EOB C (SAVED6 S P0 WB regs0 X) m (f_ob f) (code_op here) R1 HK1 HM A13 ltac:(lia)) as (R2 & Hms2 & Hfr2).
        pose proof HK1 as HKc. destruct HKc as (K2 & K10 & K11 & K12 & K21 & _).
        unfold eob_mem in Hms2.
        assert (HB : forall md mg m', m' = brk_mem m ZP S md mg ->
                   msteps s6u_segs (mkst R1 (0x22d1c : word) m s6u_rom) (mkst R2 (0x22d54 : word) m' s6u_rom) ->
                   SIMRES regs0 regs m (0x227c0 : word) (FBreak (mkF (f_in f) (f_out f) hold1 bits1 (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f)) md mg)).
        { intros md mg m' Hm' Hms2'. cbn [SIMRES]. exists R2, m'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2']|].
          unfold BINV. cbn [f_in f_out f_hold f_bits f_ob].
          split; [rewrite (Hfr2 2%bv eq_refl); exact K2|]. split; [rewrite (Hfr2 10%bv eq_refl); exact K10|]. split; [rewrite (Hfr2 11%bv eq_refl); exact K11|].
          split; [rewrite (Hfr2 12%bv eq_refl); exact K12|]. split; [rewrite (Hfr2 21%bv eq_refl); exact K21|].
          split; [rewrite (Hfr2 16%bv eq_refl); exact B16|]. split; [rewrite (Hfr2 22%bv eq_refl); exact B22|].
          split; [rewrite (Hfr2 14%bv eq_refl); exact B14|]. split; [rewrite (Hfr2 15%bv eq_refl); exact B15|].
          split; [rewrite (Hfr2 3%bv eq_refl); exact Bg3|]. split; [rewrite (Hfr2 4%bv eq_refl); exact Bg4|].
          split; [unfold If6_7.FB; cbn [f_hold f_bits f_in f_out]; lia|]. exists m. split; [exact HM | exact Hm']. }
        destruct (Z.eqb_spec (Z.land (code_op here) 32) 0) as [Ho32|Ho32]; cbn [negb].
        -- eapply HB; [reflexivity | exact Hms2].
        -- eapply HB; [reflexivity | exact Hms2].
    +
      set (e := Z.land (code_op here) 15) in *.
      assert (He : e = code_op here mod 2 ^ 4) by (subst e; change 15 with (2 ^ 4 - 1); apply land_ones_mod; lia).
      assert (He16 : 0 <= e < 16) by (rewrite He; apply Z.mod_pos_bound; lia).
      apply andb_prop in Hok as [Hpl Hok].
      assert (Hpull : e <> 0 -> bits1 < e -> f_in f + 1 <= IN /\ e <= bits1 + 8).
      { intros Hne Hlt. replace (e =? 0) with false in Hpl by (symmetry; apply Z.eqb_neq; exact Hne).
        cbn [negb f_bits f_in fset_len] in Hpl. replace (bits1 <? e) with true in Hpl by (symmetry; apply Z.ltb_lt; exact Hlt).
        apply andb_prop in Hpl as [Ha Hb']. apply Z.leb_le in Ha. apply Z.leb_le in Hb'. lia. }
      clear Hpl. pose proof Hinp_b as Hinb.
      assert (Hlen0 : 0 <= code_val here < 65536) by lia.
      pose proof (len_if_eq X (fset_len (mkF (f_in f) (f_out f) hold1 bits1 (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f)) (code_val here)) e
                    ltac:(cbn; lia) ltac:(cbn; lia) He16 ltac:(cbn; lia)
                    ltac:(cbn [f_bits f_in f_hold fset_len]; intros Hne Hlt; destruct (Hpull Hne Hlt) as [Ha Hb']; split; [apply Hinb; lia | exact Hb']))
        as E.
      change (x_input X) with (ic_input c) in E.
      rewrite E in Hok |- *. clear E.
      cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob fset_len] in Hok |- *.
      pose proof (blk_LEN C (SAVED6 S P0 WB regs0 X) m (f_ob f) idx hold1 bits1 (f_in f) R1 HK1 HM Hidx B5 A13 B14 B15 B16
                    ltac:(lia) Hh1 ltac:(lia) ltac:(change (code_at s (is_lencode s) idx) with here; rewrite <- He; exact Hpull)) as HLEN.
      change (code_at s (is_lencode s) idx) with here in HLEN. rewrite <- He in HLEN.
      destruct (len_step (ic_input c) (f_in f) hold1 bits1 (code_val here) e) as [[[fin' hold'] bits'] len] eqn:Hls.
      pose proof (len_step_cases _ _ _ _ _ _ _ _ _ _ Hls) as HfinM1.
      destruct HLEN as (R3 & Hms3 & HK3 & C14 & C15 & C16 & C27 & Hfr3 & Hh3 & Hb3 & Hfin3 & Hlen3).
      apply andb_prop in Hok as [Hp2 Hok]. unfold pull2_ok in Hp2. cbn [f_bits f_in] in Hp2.
      assert (Hin2 : bits' < 15 -> fin' + 2 <= IN).
      { intros Hc. replace (bits' <? 15) with true in Hp2 by (symmetry; apply Z.ltb_lt; exact Hc). apply Z.leb_le in Hp2. exact Hp2. }
      clear Hp2.
      destruct (fpull2_if_eq X (mkF fin' (f_out f) hold' bits' len (f_dist f) (f_op f) (f_from f) (f_ob f)) Hh3 ltac:(cbn; lia)
                  ltac:(cbn [f_bits f_in]; intros Hc; split; apply Hinb; lia)) as [Ep Bp].
      cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob] in Ep, Bp. change (x_input X) with (ic_input c) in Ep, Bp.
      rewrite Ep in Hok |- *. clear Ep.
      pose proof (blk_DRF C (SAVED6 S P0 WB regs0 X) m (f_ob f) fin' hold' bits' R3 HK3 HM C16 C14 C15 Hfin3 Hb3 Hh3 Hin2) as HDRF.
      destruct (refill2 (ic_input c) fin' hold' bits') as [[fin2 hold2] bits2] eqn:Hrf.
      pose proof (refill2_cases _ _ _ _ _ _ _ Hrf) as HfinM2.
      cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob] in Hok |- *.
      destruct HDRF as (R4 & Hms4 & HK4 & D16 & D14 & D15 & Hfr4 & Hh4 & Hb4 & Hfin4).
      apply andb_prop in Hok as [Hdi Hok]. apply Z.ltb_lt in Hdi.
      pose proof (dodist_ok_bits _ _ _ _ _ _ _ _ Hok) as Hcb'. cbn [f_bits] in Hcb'.
      destruct (blk_DLK C (SAVED6 S P0 WB regs0 X) m (f_ob f) hold2 bits2 R4 HK4 HM (slot48_in regs0) D14 D15 Hb4 Hh4 Hdi Hcb')
        as (R5 & Hms5 & HK5 & E13 & E5 & E14 & E15 & Hfr5 & Hh5 & Hb5).
      eapply SIMRES_steps.
      { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms3|]. eapply msteps_trans; [exact Hms4 | exact Hms5]. }
      apply (DODIST 4 regs0 R5 m (mkF fin2 (f_out f) hold2 bits2 len (f_dist f) (f_op f) (f_from f) (f_ob f)) (Z.land hold2 (x_dmask X)));
        cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob].
      all: try assumption.
      * rewrite (Hfr5 16%bv eq_refl). exact D16.
      * rewrite (Hfr5 22%bv eq_refl), (Hfr4 22%bv eq_refl), (Hfr3 22%bv eq_refl). exact B22.
      * rewrite (Hfr5 27%bv eq_refl), (Hfr4 27%bv eq_refl). exact C27.
      * rewrite (Hfr5 3%bv eq_refl), (Hfr4 3%bv eq_refl), (Hfr3 3%bv eq_refl). exact Bg3.
      * rewrite (Hfr5 4%bv eq_refl), (Hfr4 4%bv eq_refl), (Hfr3 4%bv eq_refl). exact Bg4.
      * split; [apply Z.land_nonneg; left; lia | exact Hdi].
      * unfold If6_7.FB. cbn [f_hold f_bits f_in f_out]. lia.
Qed.

Lemma dolen_ok_bits : forall x st IN ON WN k h f, dolen_ok x st IN ON WN k h f = true -> code_bits h <= f_bits f.
Proof.
  intros x st IN ON WN [|k] h f H; cbn [dolen_ok] in H; [discriminate H|].
  apply andb_prop in H as [H _]. apply Z.leb_le in H. exact H.
Qed.

Lemma trip_sim : forall regs0 regs m f,
  CINV regs0 regs m f -> getr regs 9 = zw 14 -> trip_ok X s IN ON WN f = true ->
  SIMRES regs0 regs m (0x2274c : word) (fast_trip X s f).
Proof.
  intros regs0 regs m f (HK & HM & Hg3 & Hg4 & H16 & H22 & H14 & H15 & Bh & Bb & Bi & Bo) H9 Hok.
  unfold trip_ok in Hok. apply andb_prop in Hok as [Hp2 Hok]. unfold pull2_ok in Hp2.
  assert (Hin2 : f_bits f < 15 -> f_in f + 2 <= IN).
  { intros Hc. replace (f_bits f <? 15) with true in Hp2 by (symmetry; apply Z.ltb_lt; exact Hc). apply Z.leb_le in Hp2. exact Hp2. }
  clear Hp2. pose proof Hinp_b as Hinb.
  destruct (fpull2_if_eq X f Bh ltac:(lia) ltac:(change (x_input X) with (ic_input c); intros Hc; split; apply Hinb; lia)) as [Ep Bp].
  change (x_input X) with (ic_input c) in Ep, Bp.
  unfold fast_trip. rewrite Ep in Hok |- *. clear Ep.
  pose proof (blk_L0 C (SAVED6 S P0 WB regs0 X) m (f_ob f) (f_in f) (f_hold f) (f_bits f) regs HK HM H9 H16 H14 H15 ltac:(lia) Bb Bh Hin2) as HL0.
  destruct (refill2 (ic_input c) (f_in f) (f_hold f) (f_bits f)) as [[fin2 hold2] bits2] eqn:Hrf.
  pose proof (refill2_cases _ _ _ _ _ _ _ Hrf) as HfinM2.
  cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob] in Hok |- *.
  destruct HL0 as (R1 & Hms1 & HK1 & A16 & A14 & A15 & Hfr1 & Hh1 & Hb1 & Hfin1).
  apply andb_prop in Hok as [Hli Hok]. apply Z.ltb_lt in Hli.
  pose proof (dolen_ok_bits _ _ _ _ _ _ _ _ Hok) as Hcb. cbn [f_bits] in Hcb.
  assert (Hli0 : 0 <= Z.land hold2 (x_lmask X)) by (apply Z.land_nonneg; left; lia).
  destruct (blk_D0 C (SAVED6 S P0 WB regs0 X) m (f_ob f) hold2 bits2 R1 HK1 HM A14 A15 Hb1 Hh1 Hli Hcb)
    as (R2 & Hms2 & HK2 & B5 & B13 & B14 & B15 & Hfr2 & Hh2 & Hb2).
  eapply SIMRES_steps; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
  apply (dolen_sim 4 regs0 R2 m (mkF fin2 (f_out f) hold2 bits2 (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f)) (Z.land hold2 (x_lmask X)));
    cbn [f_hold f_in f_out f_bits f_len f_dist f_op f_from f_ob].
  all: try assumption.
  - rewrite (Hfr2 16%bv eq_refl). exact A16.
  - rewrite (Hfr2 22%bv eq_refl), (Hfr1 22%bv eq_refl). exact H22.
  - rewrite (Hfr2 3%bv eq_refl), (Hfr1 3%bv eq_refl). exact Hg3.
  - rewrite (Hfr2 4%bv eq_refl), (Hfr1 4%bv eq_refl). exact Hg4.
  - lia.
  - unfold If6_7.FB. cbn [f_hold f_bits f_in f_out]. lia.
Qed.

End Walk.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

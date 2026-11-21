(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem InffastModel InffastSafe.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InffastCtx IfSpec IfSpec6 If6_1 If6_2 If6_3 If6_4 If6_5I If6_5 If6_6 If6_7 If6_8.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ff_loop (s : inflate_state) (c : icall) (r : iregs) : ffs * option (Z * option Z) :=
  iterZ (8 * ic_avail_in c + ic_avail_out c + 80)
    (fun f => match fast_trip (ffx_of s c r) s f with
              | FCont f' => if (f_in f' <? x_last (ffx_of s c r)) && (f_out f' <? x_end (ffx_of s c r)) then inl f'
                            else inr (f', None)
              | FBreak f' mode msg => inr (f', Some (mode, msg))
              end)
    (fun f => (f, None)) (ff0_of s c).

Definition ff_fin (f : ffs) : ffs :=
  let len := Z.shiftr (f_bits f) 3 in
  let f := fset_in f (f_in f - len) in
  let f := fset_bits f (wrap32 (f_bits f - Z.shiftl len 3)) in
  fset_hold f (Z.land (f_hold f) (zmask (f_bits f))).

Definition ff_post (s : inflate_state) (c : icall) (r : iregs) (x : ffx) (f : ffs) (mm : option (Z * option Z)) : iw :=
  let c := icset_outbuf c (f_ob f) in
  let c := icset_next_in c (f_in f) in
  let c := icset_next_out c (f_out f) in
  let c := icset_avail_in c (wrap32 (if f_in f <? x_last x then 5 + (x_last x - f_in f) else 5 - (f_in f - x_last x))) in
  let c := icset_avail_out c (wrap32 (if f_out f <? x_end x then 257 + (x_end x - f_out f) else 257 - (f_out f - x_end x))) in
  let s := iset_hold s (f_hold f) in
  let s := iset_bits s (f_bits f) in
  let '(s, c) := match mm with
                 | Some (mode, Some msg) => (iset_mode s mode, icset_msg c msg)
                 | Some (mode, None) => (iset_mode s mode, c)
                 | None => (s, c)
                 end in
  mkW s c r.

Lemma inflate_fast_eq : forall s c r,
  inflate_fast (mkW s c r) = let '(f, mm) := ff_loop s c r in ff_post s c r (ffx_of s c r) (ff_fin f) mm.
Proof. intros. reflexivity. Qed.

Lemma ff_fin_eq : forall f, 0 <= f_bits f < 64 ->
  ff_fin f = mkF (f_in f - f_bits f / 8) (f_out f) (f_hold f mod 2 ^ (f_bits f mod 8)) (f_bits f mod 8)
                 (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f).
Proof.
  intros f Hb. unfold ff_fin. cbn [f_in f_bits f_hold f_out f_len f_dist f_op f_from f_ob fset_in fset_bits fset_hold].
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod (f_bits f) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (f_bits f) 8 ltac:(lia)).
  rewrite (wrap32_id (f_bits f - f_bits f / 8 * 8)) by lia.
  replace (f_bits f - f_bits f / 8 * 8) with (f_bits f mod 8) by lia.
  rewrite land_zmask by lia. destruct f; reflexivity.
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
Definition xmem (m0 : word -> option byte) (mm : option (Z * option Z)) : word -> option byte :=
  match mm with None => m0 | Some (md, mg) => brk_mem m0 ZP S md mg end.

Definition XINV (regs0 R : bvmap 5 word) (m' : word -> option byte) (f' : ffs) (mm : option (Z * option Z)) : Prop :=
  getr R 2 = zw sp /\ getr R 10 = zw ZP /\ getr R 11 = zw S /\ getr R 12 = zw (I0 + x_last X) /\ getr R 21 = zw (P0 + x_end X) /\
  getr R 16 = zw (I0 + f_in f') /\ getr R 22 = zw (P0 + f_out f') /\ getr R 14 = zw (f_hold f') /\ getr R 15 = zw (f_bits f') /\
  getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\
  FB f' /\
  exists m0, MEMI (SAVED6 S P0 WB regs0 X) m0 (f_ob f') /\ m' = xmem m0 mm.

Lemma CINV_XINV : forall regs0 R m' f', CINV regs0 R m' f' -> XINV regs0 R m' f' None.
Proof.
  intros regs0 R m' f' (HK & HM & Hg3 & Hg4 & H16 & H22 & H14 & H15 & HFB).
  destruct HK as (K2 & K10 & K11 & K12 & K21 & _).
  unfold XINV. repeat (split; [assumption|]). exists m'. split; [exact HM | reflexivity].
Qed.
Lemma BINV_XINV : forall regs0 R m' f' md mg, BINV regs0 R m' f' md mg -> XINV regs0 R m' f' (Some (md, mg)).
Proof. intros regs0 R m' f' md mg H. unfold If6_7.BINV in H. unfold XINV. cbn [xmem]. exact H. Qed.

Definition LRES (regs0 regs : bvmap 5 word) (m : word -> option byte) (res : ffs * option (Z * option Z)) : Prop :=
  exit_ok (fst res) = true /\
  exists R m', msteps s6u_segs (mkst regs (0x2274c : word) m s6u_rom) (mkst R (0x22d54 : word) m' s6u_rom) /\ XINV regs0 R m' (fst res) (snd res).

Let mstep : ffs -> ffs + (ffs * option (Z * option Z)) :=
  fun f => match fast_trip X s f with
           | FCont f' => if (f_in f' <? x_last X) && (f_out f' <? x_end X) then inl f' else inr (f', None)
           | FBreak f' mode msg => inr (f', Some (mode, msg))
           end.
Let okstep : ffs -> ffs + bool :=
  fun f => if trip_ok X s IN ON WN f then
             match fast_trip X s f with
             | FCont f' => if (f_in f' <? x_last X) && (f_out f' <? x_end X) then inl f' else inr (exit_ok f')
             | FBreak f' _ _ => inr (exit_ok f')
             end
           else inr false.

Lemma loop_sim : forall n regs0 regs m f,
  CINV regs0 regs m f -> getr regs 9 = zw 14 ->
  match iterK_nat n okstep f with inl _ => false | inr b => b end = true ->
  LRES regs0 regs m (match iterK_nat n mstep f with inl f' => (f', None) | inr r => r end).
Proof.
  induction n as [|n IH]; intros regs0 regs m f HC H9 Hok; cbn [iterK_nat] in Hok |- *; [discriminate Hok|].
  unfold okstep in Hok. unfold mstep. fold mstep. fold okstep in Hok.
  destruct (trip_ok X s IN ON WN f) eqn:Ht; [|discriminate Hok].
  pose proof (trip_sim C regs0 regs m f HC H9 Ht) as HT.
  destruct (fast_trip X s f) as [f'|f' md mg].
  - cbn [If6_7.SIMRES] in HT. destruct HT as (R1 & m1 & Hms1 & HC1).
    pose proof HC1 as HCc. destruct HCc as (HK1 & HM1 & Hg3 & Hg4 & A16 & A22 & A14 & A15 & Bh & Bb & Bi & Bo).
    destruct (blk_LATCH C m1 (f_in f') (f_out f') R1 HK1 A16 A22 ltac:(lia) ltac:(lia)) as (R2 & Hms2 & HK2 & A9 & Hfr2).
    assert (HC2 : CINV regs0 R2 m1 f').
    { unfold If6_7.CINV. split; [exact HK2|]. split; [exact HM1|].
      split; [rewrite (Hfr2 3%bv eq_refl); exact Hg3|]. split; [rewrite (Hfr2 4%bv eq_refl); exact Hg4|].
      split; [rewrite (Hfr2 16%bv eq_refl); exact A16|]. split; [rewrite (Hfr2 22%bv eq_refl); exact A22|].
      split; [rewrite (Hfr2 14%bv eq_refl); exact A14|]. split; [rewrite (Hfr2 15%bv eq_refl); exact A15|].
      unfold If6_7.FB. lia. }
    destruct ((f_in f' <? x_last X) && (f_out f' <? x_end X)).
    + specialize (IH regs0 R2 m1 f' HC2 A9 Hok). revert IH.
      destruct (iterK_nat n mstep f') as [f''|[f'' mm]]; intros [Hx (R3 & m3 & Hms3 & HX3)];
        (split; [exact Hx|]); exists R3, m3; (split; [|exact HX3]);
        (eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]).
    + split; [exact Hok|]. exists R2, m1. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      apply CINV_XINV. exact HC2.
  - cbn [If6_7.SIMRES] in HT. destruct HT as (R1 & m1 & Hms1 & HB1).
    split; [exact Hok|]. exists R1, m1. split; [exact Hms1|]. apply BINV_XINV. exact HB1.
Qed.

Lemma ff_loop_sim : forall regs0 regs m,
  CINV regs0 regs m (ff0_of s c) -> getr regs 9 = zw 14 -> ff_ok s c r = true -> LRES regs0 regs m (ff_loop s c r).
Proof.
  intros regs0 regs m HC H9 Hok. unfold ff_loop. rewrite iterZ_nat.
  unfold ff_ok, loop_ok in Hok. rewrite iterZ_nat in Hok.
  exact (loop_sim _ regs0 regs m (ff0_of s c) HC H9 Hok).
Qed.

Lemma xmem_saved : forall regs0 m0 ob mm, MEMI (SAVED6 S P0 WB regs0 X) m0 ob -> fcells s6u_segs sp (xmem m0 mm) (SAVED6 S P0 WB regs0 X).
Proof.
  intros regs0 m0 ob mm HM. pose proof (MEMI_saved _ m0 ob HM) as HS.
  pose proof (fun e He => SAVED6_ok S P0 WB regs0 X e He) as Hin.
  destruct mm as [[md [a|]]|]; cbn [xmem brk_mem]; [| | exact HS].
  - apply (fcells_store_far s6u_segs sp 160); rewrite ?length_Z_to_le_bytes; try (cbn; lia); [| sep_solve | exact Hin].
    apply (fcells_store_far s6u_segs sp 160); rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact HS | sep_solve | exact Hin].
  - apply (fcells_store_far s6u_segs sp 160); rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact HS | sep_solve | exact Hin].
Qed.

Lemma xmem_mapped : forall regs0 m0 ob mm, MEMI (SAVED6 S P0 WB regs0 X) m0 ob ->
  mapped (xmem m0 mm) sp 160 /\ mapped (xmem m0 mm) ZP 112 /\ mapped (xmem m0 mm) S 7176.
Proof.
  intros regs0 m0 ob mm HM. pose proof (MEMI_FINV _ m0 ob HM) as HF.
  pose proof (FINV_map_sp _ m0 HF) as M1. pose proof (FINV_map_Z _ m0 HF) as M2. pose proof (FINV_map_S _ m0 HF) as M3.
  destruct mm as [[md [a|]]|]; cbn [xmem brk_mem]; [| | split; [exact M1 | split; [exact M2 | exact M3]]];
    (split; [|split]); repeat apply mapped_wbytes; assumption.
Qed.

Theorem inflate_fast_run : forall regs,
  getr regs 1 = ra -> getr regs 2 = zw (sp + 160) -> getr regs 10 = zw ZP -> getr regs 11 = zw (ir_out r) -> 0 <= ir_out r < 2 ^ 32 ->
  ff_ok s c r = true ->
  let '(f, mm) := ff_loop s c r in
  exists R m0,
    msteps s6u_segs (mkst regs (0x225ec : word) mem s6u_rom)
                   (mkst R ra (exit_mem6 (xmem m0 mm) ZP S I0 P0 (x_last X) (x_end X) (f_in f) (f_out f) (f_hold f) (f_bits f)) s6u_rom)
    /\ getr R 2 = zw (sp + 160)
    /\ (forall k : reg, In k [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R k = getr regs k)
    /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4
    /\ MEMI (SAVED6 S P0 WB regs X) m0 (f_ob f) /\ FB f /\ f_bits f / 8 <= f_in f.
Proof.
  intros regs H1 H2 H10 H11 Hir Hok.
  destruct (prologue_step C regs H10 H11 H2 Hir) as (R1 & m1 & Hms1 & HK1 & (A16 & A22 & A14 & A15) & HM1 & A9 & Ag3 & Ag4).
  assert (HC1 : CINV regs R1 m1 (ff0_of s c)).
  { unfold If6_7.CINV, ff0_of, If6_7.FB. cbn [f_in f_out f_hold f_bits f_ob].
    split; [exact HK1|]. split; [exact HM1|]. split; [exact Ag3|]. split; [exact Ag4|].
    split; [exact A16|]. split; [exact A22|]. split; [exact A14|]. split; [exact A15 | lia]. }
  destruct (ff_loop_sim regs R1 m1 HC1 A9 Hok) as [Hx (R2 & m2 & Hms2 & HX)].
  destruct (ff_loop s c r) as [f mm]. cbn [fst snd] in Hx, HX.
  unfold exit_ok in Hx. apply Z.leb_le in Hx. rewrite Z.shiftr_div_pow2 in Hx by lia. change (2 ^ 3) with 8 in Hx.
  destruct HX as (B2 & B10 & B11 & B12 & B21 & B16 & B22 & B14 & B15 & Bg3 & Bg4 & HFB & (m0 & HM0 & ->)).
  pose proof HFB as (Bh & Bb & Bi & Bo).
  assert (Hh64 : f_hold f < 2 ^ 64) by (pose proof (Z.pow_le_mono_r 2 (f_bits f) 64 ltac:(lia) ltac:(lia)); lia).
  destruct (xmem_mapped regs m0 (f_ob f) mm HM0) as (Wsp & WZ & WS).
  unfold mapped in Wsp, WZ, WS.
  destruct (blk_EXIT C regs R2 (xmem m0 mm) (f_in f) (f_out f) (f_hold f) (f_bits f)
              B2 B10 B11 B12 B21 (xmem_saved regs m0 (f_ob f) mm HM0) Wsp WZ WS H1 B16 B22 B14 B15 Bb ltac:(lia) ltac:(lia) Hx ltac:(lia) ltac:(lia))
    as (R3 & Hms3 & C2 & Ckeep & C3 & C4 & _).
  exists R3, m0. split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms3]. }
  split; [exact C2|]. split; [exact Ckeep|].
  split; [rewrite C3; exact Bg3|]. split; [rewrite C4; exact Bg4|].
  split; [exact HM0|]. split; [exact HFB | exact Hx].
Qed.

Local Notation LF := (FFall sp P0 (arr_len (ic_outbuf c)) ZP S).

Local Ltac cwo :=
  apply cell_write_other; rewrite ?length_Z_to_le_bytes; [ | lia | cbn; lia | lia | cbn; lia | cbn; sep_solve ].
Local Ltac cso :=
  apply cells_write_other; rewrite ?length_Z_to_le_bytes; [ | cbn; lia | lia | lia | lia | cbn; lia | cbn; sep_solve ].
Local Ltac fwo :=
  apply (fields_write_other s6u_segs _ S isl_layout _ isl_SIZE); rewrite ?length_Z_to_le_bytes;
  [ | exact isl_layout_within | lia | unfold isl_SIZE; lia | lia | cbn; lia | unfold isl_SIZE; cbn; sep_solve ].
Local Ltac sfr := first [ apply sub_franges_here; cbn; lia | apply sub_franges_later; sfr ].
Local Ltac awb := apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; [ | lia | cbn; lia | cbn; sfr ].

Lemma xmem_out : forall m0 mm g, cells s6u_segs m0 P0 1 1 ON g -> cells s6u_segs (xmem m0 mm) P0 1 1 ON g.
Proof.
  intros m0 mm g H. destruct mm as [[md [a|]]|]; cbn [xmem brk_mem]; [cso; cso; exact H | cso; exact H | exact H].
Qed.
Lemma xmem_scalars : forall m0 mm, isl_scalars s6u_segs is6_LENFIX is6_DISTFIX m0 S (ISP ZP WB) s ->
  isl_scalars s6u_segs is6_LENFIX is6_DISTFIX (xmem m0 mm) S (ISP ZP WB) (match mm with None => s | Some (md, _) => iset_mode s md end).
Proof.
  intros m0 mm H. destruct mm as [[md [a|]]|]; cbn [xmem brk_mem]; [| | exact H].
  - apply isl_upd_mode; [| lia | unfold isl_SIZE; lia]. unfold isl_scalars. fwo. exact H.
  - apply isl_upd_mode; [exact H | lia | unfold isl_SIZE; lia].
Qed.
Lemma xmem_agree : forall m0 mm, agree_out LF mem m0 -> agree_out LF mem (xmem m0 mm).
Proof.
  intros m0 mm H. unfold FFall in *. destruct mm as [[md [a|]]|]; cbn [xmem brk_mem]; [awb; awb; exact H | awb; exact H | exact H].
Qed.
Lemma xmem_grows : forall m0 mm x, m0 x <> None -> xmem m0 mm x <> None.
Proof.
  intros m0 mm x H. destruct mm as [[md [a|]]|]; cbn [xmem brk_mem]; repeat apply wbytes_grows; exact H.
Qed.
Lemma xmem_msg_some : forall m0 md a, cell s6u_segs (xmem m0 (Some (md, Some a))) (ZP + 48) 8 (msg6_addr a).
Proof.
  intros m0 md a. cbn [xmem brk_mem]. cwo. apply cell_write_same; [lia | cbn; lia].
Qed.
Lemma xmem_msg_keep : forall m0 mm v, match mm with Some (_, Some _) => False | _ => True end ->
  cell s6u_segs m0 (ZP + 48) 8 v -> cell s6u_segs (xmem m0 mm) (ZP + 48) 8 v.
Proof.
  intros m0 mm v Hmm H. destruct mm as [[md [a|]]|]; cbn [xmem brk_mem]; [destruct Hmm | cwo; exact H | exact H].
Qed.

Local Notation EXM m fin fout hold bits := (exit_mem6 m ZP S I0 P0 (x_last X) (x_end X) fin fout hold bits).

Lemma exit_out : forall m g fin fout hold bits, 0 <= fout <= ON -> 0 <= fin <= IN -> 0 <= bits ->
  cells s6u_segs m P0 1 1 ON g -> cells s6u_segs (EXM m fin fout hold bits) P0 1 1 ON g.
Proof.
  intros m g fin fout hold bits Hfo Hfi Hb H. unfold exit_mem6. do 6 cso. exact H.
Qed.
Lemma exit_scalars : forall m s1 fin fout hold bits, 0 <= bits ->
  isl_scalars s6u_segs is6_LENFIX is6_DISTFIX m S (ISP ZP WB) s1 ->
  isl_scalars s6u_segs is6_LENFIX is6_DISTFIX (EXM m fin fout hold bits) S (ISP ZP WB) (iset_bits (iset_hold s1 (hold mod 2 ^ (bits mod 8))) (bits mod 8)).
Proof.
  intros m s1 fin fout hold bits Hb H. unfold exit_mem6.
  apply isl_upd_bits; [| lia | unfold isl_SIZE; lia]. apply isl_upd_hold; [| lia | unfold isl_SIZE; lia].
  unfold isl_scalars. do 4 fwo. exact H.
Qed.
Lemma exit_zs : forall m fin fout hold bits, 0 <= fout <= ON -> 0 <= fin <= IN -> 0 <= bits / 8 <= fin ->
  cell s6u_segs (EXM m fin fout hold bits) (ZP + 0) 8 (I0 + (fin - bits / 8))
  /\ cell s6u_segs (EXM m fin fout hold bits) (ZP + 8) 4 (wrap32 (5 + (x_last X - (fin - bits / 8))))
  /\ cell s6u_segs (EXM m fin fout hold bits) (ZP + 24) 8 (P0 + fout)
  /\ cell s6u_segs (EXM m fin fout hold bits) (ZP + 32) 4 (wrap32 (257 + (x_end X - fout))).
Proof.
  intros m fin fout hold bits Hfo Hfi Hb. unfold exit_mem6. rewrite Z.add_0_r.
  split; [do 5 cwo; rewrite <- (Z.add_0_r ZP) at 2; rewrite Z.add_0_r; apply cell_write_same; [lia | cbn; lia]|].
  split; [do 3 cwo; apply cell_write_same; [lia | cbn; lia]|].
  split; [do 4 cwo; apply cell_write_same; [lia | cbn; lia]|].
  do 2 cwo; apply cell_write_same; [lia | cbn; lia].
Qed.
Lemma exit_agree : forall m fin fout hold bits, agree_out LF mem m -> agree_out LF mem (EXM m fin fout hold bits).
Proof.
  intros m fin fout hold bits H. unfold exit_mem6, FFall in *.
  awb. awb. awb. awb. awb. awb. exact H.
Qed.
Lemma exit_grows : forall m fin fout hold bits x, m x <> None -> (EXM m fin fout hold bits) x <> None.
Proof. intros m fin fout hold bits x H. unfold exit_mem6. repeat apply wbytes_grows. exact H. Qed.
Lemma exit_msg : forall m fin fout hold bits v, cell s6u_segs m (ZP + 48) 8 v -> cell s6u_segs (EXM m fin fout hold bits) (ZP + 48) 8 v.
Proof. intros m fin fout hold bits v H. unfold exit_mem6. do 6 cwo. exact H. Qed.

Lemma memi_msg : forall regs0 m0 ob v, MEMI (SAVED6 S P0 WB regs0 X) m0 ob -> cell s6u_segs mem (ZP + 48) 8 v -> cell s6u_segs m0 (ZP + 48) 8 v.
Proof.
  intros regs0 m0 ob v HM H.
  pose proof (FINV_agree _ m0 (MEMI_FINV _ m0 ob HM)) as Hag.
  apply (cell_agree_out s6u_segs (FF1 sp P0 ON) mem m0 _ _ _ Hag); [| lia | cbn; lia | exact H].
  unfold FF1. intros x Hx. cbn [in_franges]. clear - Hx Hd_spZ Hd_PZ HZP0 HZP1. unfold sep in *. lia.
Qed.

Theorem inflate_fast_correct : forall regs,
  getr regs 1 = ra -> getr regs 2 = zw (sp + 160) -> getr regs 10 = zw ZP -> getr regs 11 = zw (ir_out r) -> 0 <= ir_out r < 2 ^ 32 ->
  cell s6u_segs mem (ZP + 48) 8 (msg6_addr (ic_msg c)) ->
  ff_ok s c r = true ->
  exists R m',
    msteps s6u_segs (mkst regs (0x225ec : word) mem s6u_rom) (mkst R ra m' s6u_rom)
    /\ getr R 2 = zw (sp + 160)
    /\ (forall k : reg, In k if_kept -> getr R k = getr regs k)
    /\ FPOST s6u_segs is6_LENFIX is6_DISTFIX msg6_addr mem sp c r ZP S I0 P0 WB m' (inflate_fast (mkW s c r)).
Proof.
  intros regs H1 H2 H10 H11 Hir Hmsg Hok.
  pose proof (inflate_fast_run regs H1 H2 H10 H11 Hir Hok) as HR.
  rewrite inflate_fast_eq. destruct (ff_loop s c r) as [f mm].
  destruct HR as (R & m0 & Hms & C2 & Ckeep & Cg3 & Cg4 & HM0 & HFB & Hx).
  exists R. eexists. split; [exact Hms|].
  split; [exact C2|].
  split.
  { intros k Hk. unfold if_kept in Hk. cbn [In] in Hk.
    destruct Hk as [<-|[<-|Hk]]; [exact Cg3 | exact Cg4 |]. apply Ckeep. cbn [In]. tauto. }
  destruct HFB as (Bh & Bb & Bi & Bo).
  pose proof (Z.div_pos (f_bits f) 8 ltac:(lia) ltac:(lia)) as Hq0.
  pose proof (Z.mod_pos_bound (f_bits f) 8 ltac:(lia)) as Hm8.
  pose proof (Z.mod_pos_bound (f_hold f) (2 ^ (f_bits f mod 8)) ltac:(apply Z.pow_pos_nonneg; lia)) as Hhm.
  rewrite ff_fin_eq by lia.
  pose proof (MEMI_out _ m0 (f_ob f) HM0) as Mout. pose proof (MEMI_len _ m0 (f_ob f) HM0) as Mlen.
  pose proof (MEMI_ob_b _ m0 (f_ob f) HM0) as Mbytes. pose proof (MEMI_scalars C _ m0 (f_ob f) HM0) as Msc.
  pose proof (MEMI_FINV _ m0 (f_ob f) HM0) as MF.
  pose proof (FINV_agree _ m0 MF) as Mag. pose proof (FINV_grows _ m0 MF) as Mgr.
  pose proof (memi_msg regs m0 (f_ob f) _ HM0 Hmsg) as Mmsg.
  destruct (exit_zs (xmem m0 mm) (f_in f - 0 + 0) (f_out f) (f_hold f) (f_bits f) ltac:(lia) ltac:(lia) ltac:(lia)) as (Z0 & Z8 & Z24 & Z32).
  replace (f_in f - 0 + 0) with (f_in f) in Z0, Z8, Z24, Z32 by lia.
  unfold FPOST, ff_post.
  assert (COMMON :
    arr_len (f_ob f) = ON /\ (forall i, 0 <= i < ON -> 0 <= arr_get (f_ob f) i < 256)
    /\ cells s6u_segs (EXM (xmem m0 mm) (f_in f) (f_out f) (f_hold f) (f_bits f)) P0 1 1 ON (arr_get (f_ob f))
    /\ agree_out LF mem (EXM (xmem m0 mm) (f_in f) (f_out f) (f_hold f) (f_bits f))
    /\ (forall x, mem x <> None -> (EXM (xmem m0 mm) (f_in f) (f_out f) (f_hold f) (f_bits f)) x <> None)).
  { split; [exact Mlen|]. split; [exact Mbytes|].
    split; [apply exit_out; [lia | lia | lia |]; apply xmem_out; exact Mout|].
    split; [apply exit_agree; apply xmem_agree; exact (agree_out_weaken _ _ mem m0 Mag FF1_FF)|].
    intros x Hx0. apply exit_grows, xmem_grows, Mgr. exact Hx0. }
  destruct COMMON as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (exit_scalars (xmem m0 mm) _ (f_in f) (f_out f) (f_hold f) (f_bits f) ltac:(lia) (xmem_scalars m0 mm Msc)) as Qs.
  destruct mm as [[md [a|]]|];
    cbn [w_c w_s w_r ic_input ic_total_in ic_total_out ic_adler ic_data_type ic_outbuf ic_next_in ic_avail_in ic_next_out ic_avail_out ic_msg
         icset_outbuf icset_next_in icset_next_out icset_avail_in icset_avail_out icset_msg
         f_in f_out f_hold f_bits f_ob is_hold is_bits iset_hold iset_bits iset_mode] in Qs |- *.
  all: replace (if f_in f - f_bits f / 8 <? x_last X then 5 + (x_last X - (f_in f - f_bits f / 8)) else 5 - (f_in f - f_bits f / 8 - x_last X))
         with (5 + (x_last X - (f_in f - f_bits f / 8))) by (destruct (_ <? _); lia).
  all: replace (if f_out f <? x_end X then 257 + (x_end X - f_out f) else 257 - (f_out f - x_end X))
         with (257 + (x_end X - f_out f)) by (destruct (_ <? _); lia).
  all: split; [reflexivity|]; split; [reflexivity|]; split; [repeat split; reflexivity|].
  all: split; [exact Q1|]; split; [exact Q2|]; split; [exact Q3|].
  all: split; [exact Z0|]; split; [exact Z8|]; split; [exact Z24|]; split; [exact Z32|].
  all: split; [exact Qs|].
  all: split; [| split; [exact Q4|]; split; [exact Q5|]; lia].
  - apply exit_msg. apply xmem_msg_some.
  - apply exit_msg. apply (xmem_msg_keep m0 (Some (md, None)) _ I). exact Mmsg.
  - apply exit_msg. apply (xmem_msg_keep m0 None _ I). exact Mmsg.
Qed.
End Walk.

Theorem inflate_fast_spec6_ok : inflate_fast_spec6.
Proof.
  unfold inflate_fast_spec6, inflate_fast_spec_at, A6_INFLATE_FAST.
  intros mem sp ra s c r ZP S I0 P0 WB regs C Hmsg Hir H1 H2 H10 H11 Hok.
  symex_pc_lit. change (seg_rom s6u_segs) with s6u_rom.
  exact (inflate_fast_correct C regs H1 H2 H10 H11 Hir Hmsg Hok).
Qed.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

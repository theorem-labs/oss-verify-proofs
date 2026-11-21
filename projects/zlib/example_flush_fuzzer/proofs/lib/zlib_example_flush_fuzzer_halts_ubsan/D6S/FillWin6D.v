(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux MemFill DSLayout ZSLayout FillWinMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState DeflateLz ZChkAdl LmatchModel AdlerModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 Callee6 FillWin6A FillWin6B FillWin6C.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Notation zstR := (zst s6_segs 168672 168704 168736) (only parsing).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section Walk.
Variable mem : word -> option byte.
Variables (S sp : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (ra : word).
Variable regs0 : bvmap 5 word.
Variable ROM : (word -> option byte) -> Prop.
Hypothesis Hret : ret_ok ra.
Hypothesis HFW : fw_pre s6_segs 168672 168704 168736 144 mem S sp p zp ds.
Hypothesis Hwrap1 : ds_wrap ds = 1.
Hypothesis HD2 : 2 <= p_head p.
Hypothesis PV2 : 2 <= p_prev p.
Hypothesis HROM : ROM mem.
Hypothesis ROM_local : rom_local6 ROM.
Hypothesis MEMCPY : memcpy_run6.
Hypothesis MEMSET : memset_run6.
Hypothesis ADLER : adler32_run6 ROM.

Local Abbreviation W := (p_window p).
Local Abbreviation PV := (p_prev p).
Local Abbreviation HD := (p_head p).
Local Abbreviation strm := (p_strm p).
Local Abbreviation INP := (zp_in zp).
Local Abbreviation ws := (ds_w_size ds).
Local Abbreviation hs := (ds_hash_size ds).
Local Abbreviation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Abbreviation RI := (FillWin6A.RI mem S sp p zp ds ra regs0 ROM).
Local Abbreviation CSTL := (FillWin6A.CSTL ds).
Local Abbreviation LREGS := (FillWin6A.LREGS S sp ds).
Local Abbreviation LF := (FillWin6A.LF S sp p ds).
Local Abbreviation moreof := (FillWin6A.moreof ds).
Hypothesis HLFimg : forall x, in_franges LF x -> IMG6_LO <= x < IMG6_HI -> False.

Local Abbreviation RI_updW := (FillWin6A.RI_updW mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation RI_updZ := (FillWin6A.RI_updZ mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation RI_transport := (FillWin6A.RI_transport mem S sp p zp ds ra regs0 ROM HFW ROM_local HLFimg).
Local Abbreviation RI_lookahead := (FillWin6A.RI_lookahead mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation RI_ins_h := (FillWin6A.RI_ins_h mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation RI_insert := (FillWin6A.RI_insert mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation RI_high_water := (FillWin6A.RI_high_water mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation zst_keep_S := (FillWin6A.zst_keep_S mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation zst_keep_W := (FillWin6A.zst_keep_W mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation zst_keep_PV := (FillWin6A.zst_keep_PV mem S sp p zp ds ra regs0 ROM HFW PV2).
Local Abbreviation zst_keep_HD := (FillWin6A.zst_keep_HD mem S sp p zp ds ra regs0 ROM HFW HD2).
Local Abbreviation zst_keep_Z := (FillWin6A.zst_keep_Z mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation zst_keep_IN := (FillWin6A.zst_keep_IN mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation CSTL_set_window := (FillWin6A.CSTL_set_window ds).
Local Abbreviation RI_updPV := (FillWin6A.RI_updPV mem S sp p zp ds ra regs0 ROM HFW HD2 ROM_local HLFimg).
Local Abbreviation RI_updHD := (FillWin6A.RI_updHD mem S sp p zp ds ra regs0 ROM HFW PV2 ROM_local HLFimg).
Local Abbreviation CSTL_lookahead := (FillWin6A.CSTL_lookahead ds).
Local Abbreviation CSTL_ins_h := (FillWin6A.CSTL_ins_h ds).
Local Abbreviation CSTL_insert := (FillWin6A.CSTL_insert ds).
Local Abbreviation CSTL_set_head := (FillWin6A.CSTL_set_head ds).
Local Abbreviation CSTL_set_prev := (FillWin6A.CSTL_set_prev ds).
Local Abbreviation LREGS_via := (FillWin6A.LREGS_via S sp ds).

Local Ltac open_fw := open_fwpre HFW.
Local Ltac apart i j := apart_of HFW i j.
Local Ltac open_lregs H :=
  let H' := fresh "HL'" in pose proof H as H';
  destruct H' as (P8 & P2 & P20 & P21 & P22 & P23 & P24 & P25 & P26).
Local Ltac open_cstl HK :=
  pose proof HK as (Kwl & Kpl & Khl & Kin & Kwr & Kws & Khs);
  pose proof (f_equal (@arr_len Z) Kin) as KIL; cbn beta in KIL.
Local Ltac in_LF := unfold FillWin6A.LF; repeat first [ apply sub_franges_here; cbn; lia | apply sub_franges_later ].
Local Ltac trim := clear MEMCPY MEMSET ADLER HROM.

Local Ltac sc_close :=
  cbn [fam] in *; change (2 ^ 1) with 2 in *; zmod_bounds;
  first [ assumption
        | rewrite ?szwrap64_32_small by lia; rewrite ?szwrap32_small by lia; repeat (rewrite Z.mod_small by lia); lia
        | zcond_close
        | fam_bounds
        | symex_read_auto | symex_sok_auto | symex_store_auto ].

Local Ltac run fuel dirs rds pinsx vbx pvx F1 :=
  let pins := eval vm_compute in (LP ++ pinsx) in
  let vb := eval vm_compute in (LB ++ vbx) in
  let pv := constr:(S :: (sp - 112) :: W :: PV :: HD :: strm :: INP :: ws :: hs :: pvx) in
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  unfold mapped, dsl_SIZE, zsl_SIZE in *;
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs fwC fuel dirs rds pins vb NoRegions pv NoVals F1 F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => try sc_close
  end.

Local Ltac cellZ HRI acc name :=
  pose proof (acc s6_segs _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HRI))))))) as name.

Local Abbreviation il_exit := (FillWin6C.il_exit mem S sp p zp ds ra regs0 ROM HFW HD2 PV2).
Local Abbreviation ILREGS := (FillWin6C.ILREGS p).
Local Abbreviation ILINV := (FillWin6C.ILINV ds).
Local Abbreviation il_step := (FillWin6C.il_step mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation il_loop := (FillWin6C.il_loop mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation lc_small := (FillWin6C.lc_small mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation lc_big := (FillWin6C.lc_big mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation cond_run := (FillWin6C.cond_run mem S sp p zp ds ra regs0 ROM HFW HD2 PV2).
Local Abbreviation h_noslide := (FillWin6A.h_noslide mem S sp p zp ds ra regs0 ROM HFW HD2 PV2).
Local Abbreviation slide_run := (FillWin6A.slide_run mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local MEMCPY HLFimg).
Local Abbreviation ns_run := (FillWin6B.ns_run mem S sp p zp ds ra regs0 ROM HFW HD2 PV2).
Local Abbreviation rb_run := (FillWin6B.rb_run mem S sp p zp ds ra regs0 ROM HFW Hwrap1 HD2 PV2 ROM_local MEMCPY ADLER HLFimg).


Definition body_clob : list reg := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 27; 28; 29; 30; 31]%bv.

Lemma tail_run : forall regs m s more,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 12 = zw (szwrap 32 (cs_avail_in (ds_strm s))) -> getr regs 18 = zw more ->
  getr regs 27 = zw strm -> getr regs 11 = zw (ds_strstart s) ->
  0 <= more -> more = 2 * ws - ds_strstart s - ds_lookahead s -> cs_avail_in (ds_strm s) <> 0 ->
  let r := read_buf s (RB_window (ds_strstart s + ds_lookahead s)) more in
  let s' := fw_insert (set_lookahead (fst r) (ds_lookahead (fst r) + snd r)) in
  exists R m', msteps s6_segs (mkst regs (0x168e4 : word) m s6_rom) (mkst R (0x16a4c : word) m' s6_rom)
    /\ RI m' s' /\ CSTL s' /\ LREGS R
    /\ getr R 10 = zw (ds_lookahead s')
    /\ (forall x : reg, reg_in x body_clob = false -> getr R x = getr regs x).
Proof using HLFimg ADLER MEMCPY ROM_local PV2 HD2 Hwrap1 HFW.
  intros regs m s more HRI HW HK HL H12 H18 H27 H11 Hm0 Hmore Hai r s'. open_fw. open_wf HW.
  destruct (rb_run regs m s more HRI HW HK HL H12 H18 H27 H11 ltac:(lia) Hai)
    as (R1 & m1 & Hms1 & HRI1 & HK1 & HL1 & A9 & A10 & A27 & Hfr1).
  destruct (read_buf_wf ws hs s (ds_strstart s + ds_lookahead s) more HW eq_refl Hm0 ltac:(lia))
    as (HW2 & HC2 & EL2 & ES2 & EI2 & ESH2 & EHM2 & EWM2 & EIH2 & Hn & Hpos & EA2).
  subst r. set (r := read_buf s (RB_window (ds_strstart s + ds_lookahead s)) more) in *.
  destruct r as [s2 n]. cbn [fst snd] in *.
  subst s'. unfold fw_insert, MIN_MATCH. dsred. rewrite EL2, ES2, EI2 in *.
  destruct (Z.leb_spec 3 (ds_lookahead s + n + ds_insert s)) as [Big|Small].
  - destruct (lc_big R1 m1 s2 n HRI1 HW2 HK1 HL1 A9 ltac:(rewrite EL2; exact A10) ltac:(lia)
                ltac:(rewrite ES2, EL2; lia) ltac:(rewrite EL2, EI2; lia))
      as (R2 & m2 & Hms2 & HRI2 & HK2 & HL2 & HIL2 & Hfr2).
    rewrite EL2, ES2, EI2 in *.
    cbv zeta.
    set (str := ds_strstart s - ds_insert s) in *.
    set (s3 := set_ins_h (set_ins_h (set_lookahead s2 (ds_lookahead s + n)) (arr_get (ds_window s2) str))
           (update_hash (set_ins_h (set_lookahead s2 (ds_lookahead s + n)) (arr_get (ds_window s2) str))
              (arr_get (ds_window s2) str)
              (arr_get (ds_window s2) (str + 1)))) in *.
    assert (HIV : ILINV s3 str).
    { unfold FillWin6C.ILINV. subst s3. dsred. rewrite ?ES2, ?EI2, ?ESH2, ?EHM2, ?EWM2.
      pose proof (update_hash_range (set_ins_h (set_lookahead s2 (ds_lookahead s + n)) (arr_get (ds_window s2) str))
                    (arr_get (ds_window s2) str) (arr_get (ds_window s2) (str + 1)) ltac:(dsred; lia)) as Hh.
      revert Hh. dsred. intros Hh.
      repeat match goal with |- _ /\ _ => split end; try lia.
      - intros i Hi. apply (wf_wb _ _ _ HW2). exact Hi.
      - intros i Hi. apply (wf_pb _ _ _ HW2). exact Hi.
      - intros i Hi. apply (wf_hb _ _ _ HW2). exact Hi. }
    destruct (il_loop (Z.to_nat (ds_insert s)) R2 m2 s3 str ltac:(subst s3; dsred; lia) HRI2 HK2 HL2 HIL2 HIV
                ltac:(subst s3; dsred; lia))
      as (R3 & m3 & Hms3 & HRI3 & HK3 & HL3 & B10 & Hfr3).
    replace (Z.to_nat (ds_insert s3)) with (Z.to_nat (ds_insert s)) in * by (subst s3; dsred; rewrite EI2; reflexivity).
    destruct (fill_window_insert_wf (Z.to_nat (ds_insert s)) ws hs s3 str ltac:(subst s3; dsred; lia)
                ltac:(subst s3; destruct HW2; constructor; dsred; try assumption; try lia;
                      pose proof (update_hash_range (set_ins_h (set_lookahead s2 (ds_lookahead s + n)) (arr_get (ds_window s2) str))
                        (arr_get (ds_window s2) str) (arr_get (ds_window s2) (str + 1)) ltac:(dsred; lia)) as Hh;
                      revert Hh; dsred; intros Hh; lia)
                ltac:(lia) ltac:(subst s3; dsred; lia) ltac:(subst s3; dsred; lia))
      as (_ & _ & EL3 & _ & _).
    replace (Z.to_nat (ds_insert s3)) with (Z.to_nat (ds_insert s)) in EL3 by (subst s3; dsred; rewrite EI2; reflexivity).
    exists R3, m3.
    split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
    split; [exact HRI3|]. split; [exact HK3|]. split; [exact HL3|].
    split; [rewrite B10, EL3; subst s3; dsred; reflexivity|].
    intros x Hx.
    rewrite (Hfr3 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    rewrite (Hfr2 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    apply Hfr1. eapply reg_in_sub; [|exact Hx]; reflexivity.
  - destruct (lc_small R1 m1 s2 n HRI1 HW2 HK1 HL1 A9 ltac:(rewrite EL2; exact A10) ltac:(lia) ltac:(rewrite EL2, EI2; lia))
      as (R2 & m2 & Hms2 & HRI2 & HK2 & HL2 & B10 & Hfr2).
    rewrite EL2 in *.
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HRI2|]. split; [exact HK2|]. split; [exact HL2|].
    split; [rewrite B10; dsred; reflexivity|].
    intros x Hx.
    rewrite (Hfr2 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    apply Hfr1. eapply reg_in_sub; [|exact Hx]; reflexivity.
Qed.


Lemma body_run : forall regs m s,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 10 = zw (ds_lookahead s) -> ds_lookahead s < MIN_LOOKAHEAD ->
  let '(s', brk) := fill_window_body s ws in
  exists R m', msteps s6_segs (mkst regs (0x167cc : word) m s6_rom)
                 (mkst R (if brk then (0x16a5c : word) else (0x16a4c : word)) m' s6_rom)
    /\ RI m' s' /\ CSTL s' /\ LREGS R
    /\ (brk = false -> getr R 10 = zw (ds_lookahead s'))
    /\ (forall x : reg, reg_in x body_clob = false -> getr R x = getr regs x).
Proof using HLFimg ADLER MEMCPY ROM_local PV2 HD2 Hwrap1 HFW.
  intros regs m s HRI HW HK HL H10 Hlook. open_fw. open_wf HW. open_cstl HK.
  rewrite fill_window_body_eq.
  unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
  assert (Hmore : fw_more s = moreof s).
  { unfold fw_more, FillWin6A.moreof. rewrite Vwsz. rewrite wrap32_id by lia. lia. }
  rewrite Hmore. rewrite Vws.
  destruct (Z.leb_spec (ws + (ws - (258 + 3 + 1))) (ds_strstart s)) as [Sl|Ns].
  -
    destruct (slide_run regs m s HRI HW HK HL H10 ltac:(lia)) as (R1 & m1 & Hms1 & HRI1 & HK1 & HL1 & A18 & A11 & Hfr1).
    cbv zeta in HRI1, HK1, A11.
    set (s7 := slide_hash (FillWin6A.slide_fields ds (set_window s (arr_blit (ds_window s) 0 (ds_window s) ws
                 (ds_strstart s + ds_lookahead s - ws))))) in *.
    destruct (fw_slide_wf ws hs s (moreof s) HW ltac:(lia) ltac:(unfold FillWin6A.moreof; lia)) as (HW7 & HC7 & HL7 & HS7).
    assert (E7 : fw_slide s ws (moreof s) = s7).
    { subst s7. unfold fw_slide, FillWin6A.slide_fields. cbv zeta.
      replace (wrap32 (ws - moreof s)) with (ds_strstart s + ds_lookahead s - ws)
        by (unfold FillWin6A.moreof; rewrite wrap32_id by lia; lia).
      reflexivity. }
    rewrite E7 in HW7, HC7, HL7, HS7 |- *.
    replace (wrap32 (moreof s + ws)) with (ws + moreof s) by (unfold FillWin6A.moreof; rewrite wrap32_id by lia; lia).
    destruct HC7 as (KI7 & KW7 & _).
    destruct (ns_run R1 m1 s7 HRI1 HW7 HK1 HL1) as (R2 & Hms2 & HL2 & B27 & B12 & Hfr2).
    destruct (Z.eqb_spec (cs_avail_in (ds_strm s7)) 0) as [A0|A0].
    + exists R2, m1. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact HRI1|]. split; [exact HK1|]. split; [exact HL2|]. split; [intros; discriminate|].
      intros x Hx. rewrite (Hfr2 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
      apply Hfr1. eapply reg_in_sub; [|exact Hx]; reflexivity.
    + destruct (tail_run R2 m1 s7 (ws + moreof s) HRI1 HW7 HK1 HL2 B12
                  ltac:(rewrite (Hfr2 18%bv eq_refl); exact A18) B27 ltac:(rewrite (Hfr2 11%bv eq_refl); exact A11)
                  ltac:(unfold FillWin6A.moreof; lia) ltac:(rewrite HS7, HL7; unfold FillWin6A.moreof; lia) A0)
        as (R3 & m3 & Hms3 & HRI3 & HK3 & HL3 & C10 & Hfr3).
      destruct (read_buf s7 (RB_window (ds_strstart s7 + ds_lookahead s7)) (ws + moreof s)) as [s2 n].
      exists R3, m3. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
      split; [exact HRI3|]. split; [exact HK3|]. split; [exact HL3|]. split; [intros _; exact C10|].
      intros x Hx. rewrite (Hfr3 x Hx).
      rewrite (Hfr2 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
      apply Hfr1. eapply reg_in_sub; [|exact Hx]; reflexivity.
  -
    destruct (h_noslide regs m s HRI HW HK HL H10 ltac:(lia)) as (R1 & Hms1 & HL1 & A18 & A11 & Hfr1).
    destruct (ns_run R1 m s HRI HW HK HL1) as (R2 & Hms2 & HL2 & B27 & B12 & Hfr2).
    destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [A0|A0].
    + exists R2, m. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact HRI|]. split; [exact HK|]. split; [exact HL2|]. split; [intros; discriminate|].
      intros x Hx. rewrite (Hfr2 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
      apply Hfr1. eapply reg_in_sub; [|exact Hx]; reflexivity.
    + destruct (tail_run R2 m s (moreof s) HRI HW HK HL2 B12
                  ltac:(rewrite (Hfr2 18%bv eq_refl); exact A18) B27 ltac:(rewrite (Hfr2 11%bv eq_refl); exact A11)
                  ltac:(unfold FillWin6A.moreof; lia) ltac:(unfold FillWin6A.moreof; lia) A0)
        as (R3 & m3 & Hms3 & HRI3 & HK3 & HL3 & C10 & Hfr3).
      destruct (read_buf s (RB_window (ds_strstart s + ds_lookahead s)) (moreof s)) as [s2 n].
      exists R3, m3. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
      split; [exact HRI3|]. split; [exact HK3|]. split; [exact HL3|]. split; [intros _; exact C10|].
      intros x Hx. rewrite (Hfr3 x Hx).
      rewrite (Hfr2 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
      apply Hfr1. eapply reg_in_sub; [|exact Hx]; reflexivity.
Qed.


Lemma loop_run : forall f regs m s,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 10 = zw (ds_lookahead s) ->
  ds_lookahead s < MIN_LOOKAHEAD -> MIN_LOOKAHEAD - ds_lookahead s <= Z.of_nat f ->
  let s' := fill_window_loop f s ws in
  exists R m', msteps s6_segs (mkst regs (0x167cc : word) m s6_rom) (mkst R (0x16a5c : word) m' s6_rom)
    /\ RI m' s' /\ CSTL s' /\ fw_wf ws hs s' /\ LREGS R
    /\ (forall x : reg, reg_in x body_clob = false -> getr R x = getr regs x).
Proof using HLFimg ADLER MEMCPY ROM_local PV2 HD2 Hwrap1 HFW.
  induction f as [|f IH]; intros regs m s HRI HW HK HL H10 Hlook Hfuel s'; subst s'.
  { exfalso. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. change (Z.of_nat 0) with 0 in Hfuel. lia. }
  rewrite fill_window_loop_step.
  pose proof (body_run regs m s HRI HW HK HL H10 Hlook) as HB.
  pose proof (fill_window_body_wf ws hs s HW Hlook) as HWB.
  destruct (fill_window_body s ws) as [s1 brk].
  destruct HB as (R1 & m1 & Hms1 & HRI1 & HK1 & HL1 & Hlk & Hfr1).
  destruct HWB as (HW1 & HC1 & Hprog).
  destruct brk.
  - exists R1, m1. split; [exact Hms1|]. split; [exact HRI1|]. split; [exact HK1|]. split; [exact HW1|].
    split; [exact HL1 | exact Hfr1].
  - pose proof (Hlk eq_refl) as A10. specialize (Hprog eq_refl).
    pose proof (wf_ai _ _ _ HW1) as Vai1. pose proof (wf_wsr _ _ _ HW1) as Lws. pose proof (wf_look _ _ _ HW) as Vlook.
    destruct (cond_run R1 m1 s1 HRI1 HK1 HL1 Vai1 ltac:(lia) A10) as (R2 & Hms2 & HL2 & B10 & Hfr2).
    destruct ((ds_lookahead s1 <? MIN_LOOKAHEAD) && negb (cs_avail_in (ds_strm s1) =? 0)) eqn:Ec.
    + apply andb_prop in Ec as [El _]. apply Z.ltb_lt in El.
      destruct (IH R2 m1 s1 HRI1 HW1 HK1 HL2 B10 El ltac:(rewrite Nat2Z.inj_succ in Hfuel; lia))
        as (R3 & m3 & Hms3 & HRI3 & HK3 & HW3 & HL3 & Hfr3).
      exists R3, m3.
      split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
      split; [exact HRI3|]. split; [exact HK3|]. split; [exact HW3|]. split; [exact HL3|].
      intros x Hx. rewrite (Hfr3 x Hx). rewrite (Hfr2 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
      exact (Hfr1 x Hx).
    + exists R2, m1. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact HRI1|]. split; [exact HK1|]. split; [exact HW1|]. split; [exact HL2|].
      intros x Hx. rewrite (Hfr2 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity). exact (Hfr1 x Hx).
Qed.


Lemma wfill_run : forall regs m s off n (raw : Z),
  RI m s -> CSTL s -> (forall i, 0 <= i < 2 * ws -> 0 <= arr_get (ds_window s) i < 256) ->
  getr regs 1 = zw raw -> getr regs 10 = zw (W + off) -> getr regs 11 = zw 0 -> getr regs 12 = zw n ->
  0 <= raw < 2 ^ 64 -> raw mod 2 = 0 ->
  0 <= off -> 0 <= n -> off + n <= 2 * ws ->
  let w' := arr_fill (ds_window s) off n 0 in
  exists R m', msteps s6_segs (mkst regs (0x27c04 : word) m s6_rom) (mkst R (zw raw) m' s6_rom)
    /\ RI m' (set_window s w') /\ CSTL (set_window s w')
    /\ (forall r : reg, reg_in r memset_clob = false -> getr R r = getr regs r).
Proof using HLFimg MEMSET ROM_local PV2 HD2 HFW.
  intros regs m s off n raw HRI HK Hwb H1 H10 H11 H12 Hraw Hraw2 Hoff Hn Hon w'. open_fw. open_cstl HK.
  pose proof HRI as (Hz & _ & _ & _ & MW & _). destruct Hz as (_ & Hwin & _).
  unfold dsl_windowA in Hwin. rewrite Kwl in Hwin.
  destruct (MEMSET m regs (W + off) 0 n (zw raw) ltac:(lia) Hn ltac:(lia) ltac:(lia)
              ltac:(eapply mapped_sub; [exact MW | lia | lia]) ltac:(apply ret_ok_zw; [lia | exact Hraw2])
              H1 H10 H11 H12)
    as (R & m' & Hms & A10 & Hfr & Hfill & Hsame & Hgr).
  symex_pc_lit_in Hms.
  exists R, m'. split; [exact Hms|].
  assert (Hl' : arr_len w' = 2 * ws) by (subst w'; rewrite arr_len_fill; exact Kwl).
  split.
  { eapply (RI_updW m m' s w' off (off + n) HRI HK).
    - apply (same_outside_agree_out m m' (W + off) (W + off + n)); [exact Hsame|]. intros x Hx. cbn. lia.
    - exact Hgr.
    - lia. - lia. - lia.
    - exact Hl'.
    - pose proof (cells_filled0 s6_segs m m' W (2 * ws) (arr_get (ds_window s)) off n Hwin Hfill Hsame
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hc.
      refine (cells_ext _ _ _ _ _ _ _ _ _ Hc). intros i Hi. cbn beta. subst w'.
      rewrite arr_get_fill. unfold arr_inb. rewrite Kwl.
      destruct (Z.leb_spec off i), (Z.ltb_spec i (off + n)), (Z.ltb_spec i (off + Z.max 0 n)), (Z.leb_spec 0 i), (Z.ltb_spec i (2 * ws));
        cbn [andb]; try reflexivity; lia. }
  split; [apply CSTL_set_window; [exact HK | exact Hl']|]. exact Hfr.
Qed.

Definition x_clob : list reg := [1; 5; 6; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%bv.

Lemma xfin1 : forall regs m s init curr,
  RI m s -> CSTL s -> LREGS regs -> getr regs 9 = zw init -> getr regs 18 = zw curr ->
  0 <= init <= 258 -> 0 <= curr <= 65536 ->
  exists R, msteps s6_segs (mkst regs (0x16a9c : word) m s6_rom)
              (mkst R (0x16ae0 : word) (wbytes m (zw (S + 5952)) (Z_to_le_bytes 8 (curr + init))) s6_rom)
    /\ RI (wbytes m (zw (S + 5952)) (Z_to_le_bytes 8 (curr + init))) (set_high_water s (curr + init))
    /\ LREGS R
    /\ (forall r : reg, reg_in r [9]%bv = false -> getr R r = getr regs r).
Proof using HLFimg ROM_local PV2 HD2 HFW.
  intros regs m s init curr HRI HK HL H9 H18 Hinit Hcurr. open_fw. open_lregs HL.
  pose proof HRI as (Hz & _ & _ & MS & _). trim.
  run 10%nat NoDirs NoReads [(9, EVar 41); (18, EVar 42)] [(41%nat, 259); (42%nat, 65537)]
      [init; curr] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  exists R. replace (curr + init) with (init + curr) by lia.
  split; [exact Hms|]. split; [apply RI_high_water; [exact HRI | exact HK]|].
  split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|]. fr_weak Hfr.
Qed.

Lemma xfin2 : forall regs m s init,
  RI m s -> CSTL s -> LREGS regs -> 0 <= ds_high_water s < 2 ^ 63 ->
  getr regs 9 = zw init -> 0 <= init <= 258 ->
  exists R, msteps s6_segs (mkst regs (0x16ad4 : word) m s6_rom)
              (mkst R (0x16ae0 : word) (wbytes m (zw (S + 5952)) (Z_to_le_bytes 8 (ds_high_water s + init))) s6_rom)
    /\ RI (wbytes m (zw (S + 5952)) (Z_to_le_bytes 8 (ds_high_water s + init))) (set_high_water s (ds_high_water s + init))
    /\ LREGS R
    /\ (forall r : reg, reg_in r [9; 10]%bv = false -> getr R r = getr regs r).
Proof using HLFimg ROM_local PV2 HD2 HFW.
  intros regs m s init HRI HK HL Hhw H9 Hinit. open_fw. open_lregs HL.
  pose proof HRI as (Hz & _ & _ & MS & _). cellS Hz dsl_high_water C5952. trim.
  run 10%nat NoDirs [RVal (EVar 42)] [(9, EVar 41)] [(41%nat, 259); (42%nat, 2 ^ 63)]
      [init; ds_high_water s] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  exists R. split; [exact Hms|]. split; [apply RI_high_water; [exact HRI | exact HK]|].
  split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|]. fr_weak Hfr.
Qed.

Lemma xmem1 : forall regs m s init,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  let curr := ds_strstart s + ds_lookahead s in
  getr regs 9 = zw init -> getr regs 18 = zw curr ->
  getr regs 1 = zw 0x16a9c -> getr regs 10 = zw (W + curr) -> getr regs 11 = zw 0 -> getr regs 12 = zw init ->
  0 <= init <= 258 -> curr + init <= 2 * ws ->
  let s' := set_high_water (set_window s (arr_fill (ds_window s) curr init 0)) (curr + init) in
  exists R m', msteps s6_segs (mkst regs (0x27c04 : word) m s6_rom) (mkst R (0x16ae0 : word) m' s6_rom)
    /\ RI m' s' /\ LREGS R
    /\ (forall r : reg, reg_in r x_clob = false -> getr R r = getr regs r).
Proof using HLFimg MEMSET ROM_local PV2 HD2 HFW.
  intros regs m s init HRI HW HK HL curr H9 H18 H1 H10 H11 H12 Hinit Hci s'. open_fw. open_wf HW.
  destruct (wfill_run regs m s curr init 0x16a9c HRI HK (wf_wb _ _ _ HW) H1 H10 H11 H12
              ltac:(lia) ltac:(reflexivity) ltac:(subst curr; lia) ltac:(lia) ltac:(lia))
    as (R1 & m1 & Hms1 & HRI1 & HK1 & Hfr1).
  symex_pc_lit_in Hms1.
  destruct (xfin1 R1 m1 _ init curr HRI1 HK1 ltac:(eapply LREGS_via; [exact HL | exact Hfr1 | reflexivity])
              ltac:(rewrite (Hfr1 9%bv eq_refl); exact H9) ltac:(rewrite (Hfr1 18%bv eq_refl); exact H18)
              Hinit ltac:(subst curr; lia))
    as (R2 & Hms2 & HRI2 & HL2 & Hfr2).
  eexists R2, _. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
  split; [exact HRI2|]. split; [exact HL2|].
  intros r Hr. rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.

Lemma xmem2 : forall regs m s init,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 9 = zw init ->
  getr regs 1 = zw 0x16ad4 -> getr regs 10 = zw (W + ds_high_water s) -> getr regs 11 = zw 0 -> getr regs 12 = zw init ->
  0 <= init <= 258 -> ds_high_water s + init <= 2 * ws ->
  let s' := set_high_water (set_window s (arr_fill (ds_window s) (ds_high_water s) init 0)) (ds_high_water s + init) in
  exists R m', msteps s6_segs (mkst regs (0x27c04 : word) m s6_rom) (mkst R (0x16ae0 : word) m' s6_rom)
    /\ RI m' s' /\ LREGS R
    /\ (forall r : reg, reg_in r x_clob = false -> getr R r = getr regs r).
Proof using HLFimg MEMSET ROM_local PV2 HD2 HFW.
  intros regs m s init HRI HW HK HL H9 H1 H10 H11 H12 Hinit Hhi s'. open_fw. open_wf HW.
  destruct (wfill_run regs m s (ds_high_water s) init 0x16ad4 HRI HK (wf_wb _ _ _ HW) H1 H10 H11 H12
              ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia))
    as (R1 & m1 & Hms1 & HRI1 & HK1 & Hfr1).
  symex_pc_lit_in Hms1.
  destruct (xfin2 R1 m1 _ init HRI1 HK1 ltac:(eapply LREGS_via; [exact HL | exact Hfr1 | reflexivity]) ltac:(dsred; lia)
              ltac:(rewrite (Hfr1 9%bv eq_refl); exact H9) Hinit)
    as (R2 & Hms2 & HRI2 & HL2 & Hfr2).
  eexists R2, _. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
  split; [exact HRI2|]. split; [exact HL2|].
  intros r Hr. rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.

Local Ltac xrun dirs s :=
  run 40%nat dirs [RVal (EVar 41); RVal (EAdd (EVar 39) (EVar 39)); RVal (EVar 42); RVal (EVar 43); RVal (EVar 34)]
      NoPins [(41%nat, 2 ^ 64); (42%nat, 65537); (43%nat, 65537)]
      [ds_high_water s; ds_strstart s; ds_lookahead s] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).

Lemma exit_run : forall regs m s,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  exists R m', msteps s6_segs (mkst regs (0x16a5c : word) m s6_rom) (mkst R (0x16ae0 : word) m' s6_rom)
    /\ RI m' (fill_window_high s) /\ LREGS R
    /\ (forall r : reg, reg_in r x_clob = false -> getr R r = getr regs r).
Proof using HLFimg MEMSET ROM_local PV2 HD2 HFW.
  intros regs m s HRI HW HK HL. open_fw. open_wf HW. open_lregs HL. open_cstl HK.
  pose proof HRI as (Hz & _ & _ & MS & _).
  cellS Hz dsl_high_water C5952. cellS Hz dsl_window_size C104. rewrite Vwsz in C104.
  cellS Hz dsl_strstart C172. cellS Hz dsl_lookahead C180. cellS Hz dsl_window C96.
  unfold fill_window_high, WIN_INIT, MAX_MATCH. rewrite Vwsz.
  destruct (Z.ltb_spec (ds_high_water s) (2 * ws)) as [Hlt|Hge].
  2: {
    trim.
    run 10%nat [true] [RVal (EVar 41); RVal (EAdd (EVar 39) (EVar 39))] NoPins [(41%nat, 2 ^ 64)]
        [ds_high_water s] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
    exists R, m. split; [exact Hms|]. split; [exact HRI|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|]. fr_weak Hfr. }
  cbv zeta.
  destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s)) as [C1|C1].
  -
    destruct (Z.ltb_spec (2 * ws - (ds_strstart s + ds_lookahead s)) 258) as [I1|I1].
    + replace (if 258 <? 2 * ws - (ds_strstart s + ds_lookahead s) then 258 else 2 * ws - (ds_strstart s + ds_lookahead s))
        with (2 * ws - (ds_strstart s + ds_lookahead s))
        by (destruct (Z.ltb_spec 258 (2 * ws - (ds_strstart s + ds_lookahead s))); lia).
      rewrite (wrap32_id (2 * ws - (ds_strstart s + ds_lookahead s))) by lia.
      lazymatch goal with |- context [mkst ?regs _ _ _] => xrun [false; false; true] s end.
      symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11.
      symex_reg HR (12%bv : reg) as A12. symex_reg HR (9%bv : reg) as A9. symex_reg HR (18%bv : reg) as A18.
      destruct (xmem1 R m s (2 * ws - (ds_strstart s + ds_lookahead s)) HRI HW HK
                  ltac:(eapply LREGS_via; [exact HL | exact Hfr | reflexivity])
                  ltac:(rewrite A9; f_equal; lia) ltac:(rewrite A18; f_equal; lia) A1
                  ltac:(rewrite A10; f_equal; lia) A11 ltac:(rewrite A12; f_equal; lia) ltac:(lia) ltac:(lia))
        as (R2 & m2 & Hms2 & HRI2 & HL2 & Hfr2).
      exists R2, m2. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
      split; [exact HRI2|]. split; [exact HL2|].
      intros r Hr. rewrite (Hfr2 r Hr). apply Hfr. eapply reg_in_sub; [|exact Hr]; reflexivity.
    + replace (if 258 <? 2 * ws - (ds_strstart s + ds_lookahead s) then 258 else 2 * ws - (ds_strstart s + ds_lookahead s))
        with 258 by (destruct (Z.ltb_spec 258 (2 * ws - (ds_strstart s + ds_lookahead s))); lia).
      rewrite (wrap32_id 258) by lia.
      lazymatch goal with |- context [mkst ?regs _ _ _] => xrun [false; false; false] s end.
      symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11.
      symex_reg HR (12%bv : reg) as A12. symex_reg HR (9%bv : reg) as A9. symex_reg HR (18%bv : reg) as A18.
      destruct (xmem1 R m s 258 HRI HW HK
                  ltac:(eapply LREGS_via; [exact HL | exact Hfr | reflexivity])
                  A9 ltac:(rewrite A18; f_equal; lia) A1
                  ltac:(rewrite A10; f_equal; lia) A11 A12 ltac:(lia) ltac:(lia))
        as (R2 & m2 & Hms2 & HRI2 & HL2 & Hfr2).
      exists R2, m2. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
      split; [exact HRI2|]. split; [exact HL2|].
      intros r Hr. rewrite (Hfr2 r Hr). apply Hfr. eapply reg_in_sub; [|exact Hr]; reflexivity.
  - destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s + 258)) as [C2|C2].
    +
      destruct (Z.ltb_spec (ds_strstart s + ds_lookahead s + 258 - ds_high_water s) (2 * ws - ds_high_water s)) as [I1|I1].
      * replace (if 2 * ws - ds_high_water s <? ds_strstart s + ds_lookahead s + 258 - ds_high_water s
                 then 2 * ws - ds_high_water s else ds_strstart s + ds_lookahead s + 258 - ds_high_water s)
          with (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)
          by (destruct (Z.ltb_spec (2 * ws - ds_high_water s) (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)); lia).
        rewrite (wrap32_id (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)) by lia.
        lazymatch goal with |- context [mkst ?regs _ _ _] => xrun [false; true; false; true] s end.
        symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11.
        symex_reg HR (12%bv : reg) as A12. symex_reg HR (9%bv : reg) as A9.
        destruct (xmem2 R m s (ds_strstart s + ds_lookahead s + 258 - ds_high_water s) HRI HW HK
                    ltac:(eapply LREGS_via; [exact HL | exact Hfr | reflexivity])
                    ltac:(rewrite A9; f_equal; lia) A1 ltac:(rewrite A10; f_equal; lia) A11
                    ltac:(rewrite A12; rewrite ?Z.mod_small by lia; f_equal; lia) ltac:(lia) ltac:(lia))
          as (R2 & m2 & Hms2 & HRI2 & HL2 & Hfr2).
        exists R2, m2. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
        split; [exact HRI2|]. split; [exact HL2|].
        intros r Hr. rewrite (Hfr2 r Hr). apply Hfr. eapply reg_in_sub; [|exact Hr]; reflexivity.
      * replace (if 2 * ws - ds_high_water s <? ds_strstart s + ds_lookahead s + 258 - ds_high_water s
                 then 2 * ws - ds_high_water s else ds_strstart s + ds_lookahead s + 258 - ds_high_water s)
          with (2 * ws - ds_high_water s)
          by (destruct (Z.ltb_spec (2 * ws - ds_high_water s) (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)); lia).
        rewrite (wrap32_id (2 * ws - ds_high_water s)) by lia.
        lazymatch goal with |- context [mkst ?regs _ _ _] => xrun [false; true; false; false] s end.
        symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11.
        symex_reg HR (12%bv : reg) as A12. symex_reg HR (9%bv : reg) as A9.
        destruct (xmem2 R m s (2 * ws - ds_high_water s) HRI HW HK
                    ltac:(eapply LREGS_via; [exact HL | exact Hfr | reflexivity])
                    ltac:(rewrite A9; f_equal; lia) A1 ltac:(rewrite A10; f_equal; lia) A11
                    ltac:(rewrite A12; rewrite ?Z.mod_small by lia; f_equal; lia) ltac:(lia) ltac:(lia))
          as (R2 & m2 & Hms2 & HRI2 & HL2 & Hfr2).
        exists R2, m2. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
        split; [exact HRI2|]. split; [exact HL2|].
        intros r Hr. rewrite (Hfr2 r Hr). apply Hfr. eapply reg_in_sub; [|exact Hr]; reflexivity.
    +
      trim.
      lazymatch goal with |- context [mkst ?regs _ _ _] => xrun [false; true; true] s end.
      exists R, m. split; [exact Hms|]. split; [exact HRI|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|]. fr_weak Hfr.
Qed.


Definition fwCE : cfg :=
  CFG [] [] [EVar 33%nat] [0x167cc] [].

Definition restored : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma epi_run : forall regs m s,
  RI m s -> getr regs 2 = zw (sp - 112) ->
  exists R, msteps s6_segs (mkst regs (0x16ae0 : word) m s6_rom) (mkst R ra m s6_rom)
    /\ getr R 2 = zw sp /\ getr R 1 = ra
    /\ getr R 8 = getr regs0 8 /\ getr R 9 = getr regs0 9 /\ getr R 18 = getr regs0 18 /\ getr R 19 = getr regs0 19
    /\ getr R 20 = getr regs0 20 /\ getr R 21 = getr regs0 21 /\ getr R 22 = getr regs0 22 /\ getr R 23 = getr regs0 23
    /\ getr R 24 = getr regs0 24 /\ getr R 25 = getr regs0 25 /\ getr R 26 = getr regs0 26 /\ getr R 27 = getr regs0 27
    /\ (forall r : reg, reg_in r restored = false -> getr R r = getr regs r).
Proof using HFW Hret.
  intros regs m s HRI H2. open_fw.
  pose proof HRI as (_ & HF & MF & _). unfold FillWin6A.FRM in HF. unfold mapped in MF. trim.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 0 8 8%nat _ HF eq_refl eq_refl) as C8.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 1 16 8%nat _ HF eq_refl eq_refl) as C16.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 2 24 8%nat _ HF eq_refl eq_refl) as C24.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 3 32 8%nat _ HF eq_refl eq_refl) as C32.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 4 40 8%nat _ HF eq_refl eq_refl) as C40.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 5 48 8%nat _ HF eq_refl eq_refl) as C48.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 6 56 8%nat _ HF eq_refl eq_refl) as C56.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 7 64 8%nat _ HF eq_refl eq_refl) as C64.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 8 72 8%nat _ HF eq_refl eq_refl) as C72.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 9 80 8%nat _ HF eq_refl eq_refl) as C80.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 10 88 8%nat _ HF eq_refl eq_refl) as C88.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 11 96 8%nat _ HF eq_refl eq_refl) as C96.
  pose proof (fields_nth s6_segs m (sp - 112) _ _ 12 104 8%nat _ HF eq_refl eq_refl) as C104.
  cbn [nth FillWin6A.fr_vals] in C8, C16, C24, C32, C40, C48, C56, C64, C72, C80, C88, C96, C104.
  clear HF HRI.
  pose proof (u64_range ra) as U1. pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19.
  pose proof (u64_range (getr regs0 20)) as U20. pose proof (u64_range (getr regs0 21)) as U21.
  pose proof (u64_range (getr regs0 22)) as U22. pose proof (u64_range (getr regs0 23)) as U23.
  pose proof (u64_range (getr regs0 24)) as U24. pose proof (u64_range (getr regs0 25)) as U25.
  pose proof (u64_range (getr regs0 26)) as U26. pose proof (u64_range (getr regs0 27)) as U27.
  symex s6_segs fwCE 20%nat NoDirs
    [RVal (EVar 33); RVal (EVar 34); RVal (EVar 35); RVal (EVar 36); RVal (EVar 37); RVal (EVar 38);
     RVal (EVar 39); RVal (EVar 40); RVal (EVar 41); RVal (EVar 42); RVal (EVar 43); RVal (EVar 44); RVal (EVar 45)]
    [(2, EVar 32)]
    [(32%nat, 2 ^ 63); (33%nat, 2 ^ 64); (34%nat, 2 ^ 64); (35%nat, 2 ^ 64); (36%nat, 2 ^ 64); (37%nat, 2 ^ 64);
     (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64); (42%nat, 2 ^ 64); (43%nat, 2 ^ 64);
     (44%nat, 2 ^ 64); (45%nat, 2 ^ 64)]
    NoRegions
    [sp - 112; bv_unsigned ra; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18);
     bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 22);
     bv_unsigned (getr regs0 23); bv_unsigned (getr regs0 24); bv_unsigned (getr regs0 25); bv_unsigned (getr regs0 26);
     bv_unsigned (getr regs0 27)]
    NoVals F0 F0' (mkst regs (0x16ae0 : word) m s6_rom) R HR Hfr Hms.
  exists R. split; [exact Hms|].
  symex_reg HR (2%bv : reg) as A2. symex_reg HR (8%bv : reg) as A8. symex_reg HR (9%bv : reg) as A9.
  symex_reg HR (18%bv : reg) as A18. symex_reg HR (19%bv : reg) as A19. symex_reg HR (20%bv : reg) as A20.
  symex_reg HR (21%bv : reg) as A21. symex_reg HR (22%bv : reg) as A22. symex_reg HR (23%bv : reg) as A23.
  symex_reg HR (24%bv : reg) as A24. symex_reg HR (25%bv : reg) as A25. symex_reg HR (26%bv : reg) as A26.
  symex_reg HR (27%bv : reg) as A27.
  split; [rewrite A2; f_equal; lia|].
  symex_reg HR (1%bv : reg) as A1. split; [exact A1|].
  split; [exact A8|]. split; [exact A9|]. split; [exact A18|]. split; [exact A19|]. split; [exact A20|].
  split; [exact A21|]. split; [exact A22|]. split; [exact A23|]. split; [exact A24|]. split; [exact A25|].
  split; [exact A26|]. split; [exact A27|].
  fr_weak Hfr.
Qed.


Local Ltac cell_tower :=
  first [ apply cell_write_same; lia
        | apply cell_write_other; [cell_tower | lia | lia | lia | rewrite length_Z_to_le_bytes; lia | rewrite length_Z_to_le_bytes; lia] ].

Local Ltac cell_tower_at :=
  match goal with
  | |- cell _ ?m ?a ?w ?v =>
      match m with context [wbytes _ (zw ?b) _] => replace a with b by lia end
  end; cell_tower.

Definition pro_clob : list reg := [2; 8; 10; 11; 20; 21; 22; 23; 24; 25; 26]%bv.

Lemma pro_run :
  getr regs0 1 = ra -> getr regs0 2 = zw sp -> getr regs0 10 = zw S ->
  exists R m1, msteps s6_segs (mkst regs0 (0x16768 : word) mem s6_rom) (mkst R (0x167cc : word) m1 s6_rom)
    /\ RI m1 ds /\ CSTL ds /\ LREGS R
    /\ getr R 10 = zw (ds_lookahead ds)
    /\ (forall r : reg, reg_in r pro_clob = false -> getr R r = getr regs0 r).
Proof using HLFimg ROM_local HROM PV2 HD2 HFW.
  intros H1 H2 H10. open_fw. pose proof (fp_wf _ _ _ _ _ _ _ _ _ _ _ HFW) as HW. open_wf HW.
  pose proof (fp_zst _ _ _ _ _ _ _ _ _ _ _ HFW) as Hz.
  pose proof (fp_map _ _ _ _ _ _ _ _ _ _ _ HFW) as MF. unfold mapped in MF.
  cellS Hz dsl_w_size C80. cellS Hz dsl_lookahead C180.
  apart 0%nat 1%nat. apart 0%nat 2%nat. apart 0%nat 3%nat. apart 0%nat 4%nat. apart 0%nat 5%nat. apart 0%nat 6%nat.
  pose proof (u64_range ra) as U1.
  pose proof HROM as HROM0. trim.
  symex s6_segs fwC 40%nat NoDirs [RVal (EVar 35); RVal (EVar 36)]
    [(1, EVar 33); (2, EVar 34); (10, EVar 32)]
    [(32%nat, 2 ^ 63); (33%nat, 2 ^ 64); (34%nat, 2 ^ 64); (35%nat, 32769); (36%nat, 65537)] NoRegions
    [S; bv_unsigned ra; sp; ws; ds_lookahead ds] NoVals (fam (ds_window ds) (ds_head ds) (ds_prev ds) (cs_input (ds_strm ds))) F0'
    (mkst regs0 (0x16768 : word) mem s6_rom) R HR Hfr Hms.
  all: try solve [fam_bounds].
  all: try solve [rewrite H1; rewrite zw_u; reflexivity].
  eexists R, _. split; [exact Hms|].
  lazymatch type of Hms with msteps _ _ (mkst _ _ ?m1 _) =>
  assert (Hag : agree_out [(sp - 112, 112)] mem m1);
  [ repeat (apply agree_out_wbytes; [ | lia | rewrite length_Z_to_le_bytes; lia | apply sub_franges_here; rewrite ?length_Z_to_le_bytes; lia]);
    apply agree_out_refl
  | assert (Hgr : forall x, mem x <> None -> m1 x <> None)
      by (intros x Hx; repeat apply wbytes_grows; exact Hx) ]
  end.
  pose proof (fp_wf _ _ _ _ _ _ _ _ _ _ _ HFW) as HW'.
  pose proof (f_equal (@arr_len Z) (eq_refl (cs_input (ds_strm ds)))) as KIL.
  split.
  { unfold FillWin6A.RI. destruct Hz as (Hsc & Hw & Hp & Hh & Hzs & Hin).
    split.
    { unfold zst. split; [|split; [|split; [|split; [|split]]]].
      - eapply (dsl_scalars_agree s6_segs _ _ _ [(sp - 112, 112)]); [exact Hsc | exact Hag | | lia | unfold dsl_SIZE; lia].
        apply disj_franges_cons; [unfold dsl_SIZE; lia | apply disj_franges_nil].
      - unfold dsl_windowA in *. rewrite Vwl in Hw |- *.
        eapply (cells_agree_out s6_segs [(sp - 112, 112)]); [exact Hag | | cbn; lia | lia | lia | exact Hw].
        apply disj_franges_cons; [lia | apply disj_franges_nil].
      - unfold dsl_prevA in *. rewrite Vpl in Hp |- *.
        eapply (cells_agree_out s6_segs [(sp - 112, 112)]); [exact Hag | | cbn; lia | lia | lia | exact Hp].
        apply disj_franges_cons; [lia | apply disj_franges_nil].
      - unfold dsl_headA in *. rewrite Vhl in Hh |- *.
        eapply (cells_agree_out s6_segs [(sp - 112, 112)]); [exact Hag | | cbn; lia | lia | lia | exact Hh].
        apply disj_franges_cons; [lia | apply disj_franges_nil].
      - eapply (zsl_scalars_agree s6_segs [(sp - 112, 112)]); [exact Hzs | exact Hag | | lia | unfold zsl_SIZE; lia].
        apply disj_franges_cons; [unfold zsl_SIZE; lia | apply disj_franges_nil].
      - unfold zsl_input in *.
        eapply (cells_agree_out s6_segs [(sp - 112, 112)]); [exact Hag | | cbn; lia | lia | lia | exact Hin].
        apply disj_franges_cons; [lia | apply disj_franges_nil]. }
    split.
    { unfold FillWin6A.FRM, FillWin6A.fr_layout, FillWin6A.fr_vals. cbn [fields].
      repeat match goal with |- _ /\ _ => split end; try exact I; cell_tower_at. }
    split; [intros x Hx; repeat apply wbytes_grows; apply MF; lia|].
    split; [intros x Hx; repeat apply wbytes_grows; exact (fp_mapS _ _ _ _ _ _ _ _ _ _ _ HFW x Hx)|].
    split; [intros x Hx; repeat apply wbytes_grows; exact (fp_mapW _ _ _ _ _ _ _ _ _ _ _ HFW x Hx)|].
    split; [intros x Hx; repeat apply wbytes_grows; exact (fp_mapP _ _ _ _ _ _ _ _ _ _ _ HFW x Hx)|].
    split; [intros x Hx; repeat apply wbytes_grows; exact (fp_mapH _ _ _ _ _ _ _ _ _ _ _ HFW x Hx)|].
    split; [intros x Hx; repeat apply wbytes_grows; exact (fp_mapZ _ _ _ _ _ _ _ _ _ _ _ HFW x Hx)|].
    split.
    { eapply agree_out_weaken; [exact Hag|]. intros x Hx. cbn in Hx. unfold FillWin6A.LF. cbn [in_franges]. lia. }
    split; [exact Hgr|].
    apply (ROM_local mem _ HROM0). intros x Hx. apply Hag. intros HG. cbn in HG.
    apply (HLFimg (bv_unsigned x)); [|exact Hx]. unfold FillWin6A.LF. cbn [in_franges]. lia. }
  split; [unfold FillWin6A.CSTL; repeat split; assumption|].
  symex_reg HR (8%bv : reg) as A8. symex_reg HR (2%bv : reg) as A2. symex_reg HR (20%bv : reg) as A20.
  symex_reg HR (21%bv : reg) as A21. symex_reg HR (22%bv : reg) as A22. symex_reg HR (23%bv : reg) as A23.
  symex_reg HR (24%bv : reg) as A24. symex_reg HR (25%bv : reg) as A25. symex_reg HR (26%bv : reg) as A26.
  symex_reg HR (10%bv : reg) as A10.
  split.
  { unfold FillWin6A.LREGS. split; [exact A8|]. split; [rewrite A2; f_equal; lia|]. split; [rewrite A20; f_equal; lia|].
    split; [rewrite A21; rewrite ?Z.mod_small by lia; f_equal; lia|]. split; [exact A22|].
    split; [exact A23|]. split; [exact A24|]. split; [rewrite A25; rewrite ?Z.mod_small by lia; f_equal; lia|]. exact A26. }
  split; [rewrite A10; rewrite ?szwrap32_small by lia; reflexivity|]. fr_weak Hfr.
Qed.


Lemma fill_window_high_wf : forall s, fw_wf ws hs s -> fw_wf ws hs (fill_window_high s).
Proof using.
  intros s HW. pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vlook.
  pose proof (wf_wsz _ _ _ HW) as Vwsz. pose proof (wf_ins _ _ _ HW) as Vins. pose proof (wf_hw _ _ _ HW) as Vhw.
  unfold fill_window_high, WIN_INIT, MAX_MATCH. rewrite Vwsz. pose proof HW as HW'.
  destruct (Z.ltb_spec (ds_high_water s) (2 * ws)); [|exact HW]. cbv zeta.
  destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s)).
  - destruct HW; constructor; dsred; try assumption.
    + rewrite arr_len_fill. assumption.
    + destruct (Z.ltb_spec 258 (2 * ws - (ds_strstart s + ds_lookahead s))); lia.
    + intros i Hi. rewrite arr_get_fill. destruct (_ && _); [lia | match goal with Hb : forall j, _ -> 0 <= arr_get (ds_window s) j < 256 |- _ => apply Hb; exact Hi end].
  - destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s + 258)); [|exact HW].
    destruct HW; constructor; dsred; try assumption.
    + rewrite arr_len_fill. assumption.
    + destruct (Z.ltb_spec (2 * ws - ds_high_water s) (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)); lia.
    + intros i Hi. rewrite arr_get_fill. destruct (_ && _); [lia | match goal with Hb : forall j, _ -> 0 <= arr_get (ds_window s) j < 256 |- _ => apply Hb; exact Hi end].
Qed.

Lemma reg_in_true_In : forall (r : reg) l, reg_in r l = true -> In r l.
Proof using.
  intros r l. induction l as [|x l IH]; cbn [reg_in]; [discriminate|].
  intros H. apply Bool.orb_true_iff in H as [H|H].
  - left. symmetry. apply bv_eq. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H.
  - right. apply IH. exact H.
Qed.

Lemma reg_in_app_false : forall (r : reg) l1 l2, reg_in r l1 = false -> reg_in r l2 = false -> reg_in r (l1 ++ l2) = false.
Proof using.
  intros r l1 l2 H1 H2. induction l1 as [|x l IH]; cbn [reg_in app] in *; [exact H2|].
  apply Bool.orb_false_iff in H1 as [Hx Hl]. rewrite Hx, (IH Hl). reflexivity.
Qed.

Theorem fill_window_correct :
  getr regs0 1 = ra -> getr regs0 2 = zw sp -> getr regs0 10 = zw S ->
  exists R m', msteps s6_segs (mkst regs0 (0x16768 : word) mem s6_rom) (mkst R ra m' s6_rom)
    /\ getr R 2 = zw sp
    /\ (forall r : reg, reg_in r c_clob = false -> getr R r = getr regs0 r)
    /\ zstR m' S p zp (fill_window ds)
    /\ fw_wf ws hs (fill_window ds) /\ CSTL (fill_window ds)
    /\ agree_out LF mem m' /\ (forall x, mem x <> None -> m' x <> None) /\ ROM m'.
Proof using HLFimg ADLER MEMSET MEMCPY ROM_local HROM PV2 HD2 Hwrap1 HFW Hret.
  intros H1 H2 H10. pose proof (fp_wf _ _ _ _ _ _ _ _ _ _ _ HFW) as HW. pose proof (fp_look _ _ _ _ _ _ _ _ _ _ _ HFW) as Hlook.
  pose proof (wf_look _ _ _ HW) as Vlook.
  destruct (pro_run H1 H2 H10) as (R1 & m1 & Hms1 & HRI1 & HK1 & HL1 & A10 & Hfr1).
  destruct (loop_run 263%nat R1 m1 ds HRI1 HW HK1 HL1 A10 Hlook
              ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; change (Z.of_nat 263) with 263; lia))
    as (R2 & m2 & Hms2 & HRI2 & HK2 & HW2 & HL2 & Hfr2).
  destruct (exit_run R2 m2 _ HRI2 HW2 HK2 HL2) as (R3 & m3 & Hms3 & HRI3 & HL3 & Hfr3).
  pose proof HL3 as (_ & B2 & _).
  destruct (epi_run R3 m3 _ HRI3 B2)
    as (R4 & Hms4 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27 & Hfr4).
  exists R4, m3.
  split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
    eapply msteps_trans; [exact Hms3 | exact Hms4]. }
  split; [exact C2|].
  split.
  { intros r Hr.
    destruct (reg_in r restored) eqn:E.
    - apply reg_in_true_In in E. cbn [In] in E.
      destruct E as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
        first [ rewrite C1; symmetry; exact H1 | rewrite C2; symmetry; exact H2 | assumption ].
    - pose proof (reg_in_app_false r c_clob restored Hr E) as Hbig.
      rewrite (Hfr4 r E).
      rewrite (Hfr3 r) by (eapply reg_in_sub; [|exact Hbig]; reflexivity).
      rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hbig]; reflexivity).
      apply Hfr1. eapply reg_in_sub; [|exact Hbig]; reflexivity. }
  destruct HRI3 as (Hz3 & _ & _ & _ & _ & _ & _ & _ & Hag3 & Hgr3 & Hrom3).
  unfold fill_window. cbv zeta.
  split; [exact Hz3|].
  split; [apply fill_window_high_wf; exact HW2|].
  split.
  { revert HK2. unfold FillWin6A.CSTL, fill_window_high. cbv zeta.
    destruct (_ <? _); [|tauto]. destruct (_ <? _); [dsred; rewrite arr_len_fill; tauto|].
    destruct (_ <? _); [dsred; rewrite arr_len_fill; tauto | tauto]. }
  split; [exact Hag3|]. split; [exact Hgr3 | exact Hrom3].
Qed.

End Walk.
End FXG.

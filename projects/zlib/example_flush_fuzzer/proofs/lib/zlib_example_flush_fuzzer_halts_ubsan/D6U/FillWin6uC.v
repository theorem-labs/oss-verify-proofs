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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u Callee6u FillWin6uA.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Notation zstR := (zst s6u_segs 180992 181024 181056) (only parsing).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition hidden (P : Prop) : Prop := P.
Lemma hide : forall P : Prop, P -> hidden P. Proof. intros P H; exact H. Qed.

Section Walk.
Variable mem : word -> option byte.
Variables (S sp : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (ra : word).
Variable regs0 : bvmap 5 word.
Variable ROM : (word -> option byte) -> Prop.
Hypothesis Hret : ret_ok ra.
Hypothesis HFW : fw_pre s6u_segs 180992 181024 181056 272 mem S sp p zp ds.
Hypothesis Hwrap1 : ds_wrap ds = 1.
Hypothesis HD2 : 2 <= p_head p.
Hypothesis PV2 : 2 <= p_prev p.
Hypothesis HROM : ROM mem.
Hypothesis ROM_local : rom_local6u ROM.
Hypothesis MEMCPY : memcpy_run6u.
Hypothesis MEMSET : memset_run6u.
Hypothesis ADLER : adler32_run6u ROM.
Hypothesis HUB : ub_pre S p zp.

Local Abbreviation W := (p_window p).
Local Abbreviation PV := (p_prev p).
Local Abbreviation HD := (p_head p).
Local Abbreviation strm := (p_strm p).
Local Abbreviation INP := (zp_in zp).
Local Abbreviation ws := (ds_w_size ds).
Local Abbreviation hs := (ds_hash_size ds).
Local Abbreviation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Abbreviation RI := (FillWin6uA.RI mem S sp p zp ds ra regs0 ROM).
Local Abbreviation CSTL := (FillWin6uA.CSTL ds).
Local Abbreviation LREGS := (FillWin6uA.LREGS S sp ds).
Local Abbreviation LF := (FillWin6uA.LF S sp p ds).
Local Abbreviation moreof := (FillWin6uA.moreof ds).
Hypothesis HLFimg : forall x, in_franges LF x -> IMG6U_LO <= x < IMG6U_HI -> False.

Local Abbreviation RI_updW := (FillWin6uA.RI_updW mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation RI_updZ := (FillWin6uA.RI_updZ mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation RI_transport := (FillWin6uA.RI_transport mem S sp p zp ds ra regs0 ROM HFW ROM_local HLFimg).
Local Abbreviation RI_lookahead := (FillWin6uA.RI_lookahead mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation RI_ins_h := (FillWin6uA.RI_ins_h mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation RI_insert := (FillWin6uA.RI_insert mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation RI_high_water := (FillWin6uA.RI_high_water mem S sp p zp ds ra regs0 ROM HFW HD2 PV2 ROM_local HLFimg).
Local Abbreviation zst_keep_S := (FillWin6uA.zst_keep_S mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation zst_keep_W := (FillWin6uA.zst_keep_W mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation zst_keep_PV := (FillWin6uA.zst_keep_PV mem S sp p zp ds ra regs0 ROM HFW PV2).
Local Abbreviation zst_keep_HD := (FillWin6uA.zst_keep_HD mem S sp p zp ds ra regs0 ROM HFW HD2).
Local Abbreviation zst_keep_Z := (FillWin6uA.zst_keep_Z mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation zst_keep_IN := (FillWin6uA.zst_keep_IN mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation CSTL_set_window := (FillWin6uA.CSTL_set_window ds).
Local Abbreviation RI_updPV := (FillWin6uA.RI_updPV mem S sp p zp ds ra regs0 ROM HFW HD2 ROM_local HLFimg).
Local Abbreviation RI_updHD := (FillWin6uA.RI_updHD mem S sp p zp ds ra regs0 ROM HFW PV2 ROM_local HLFimg).
Local Abbreviation CSTL_lookahead := (FillWin6uA.CSTL_lookahead ds).
Local Abbreviation CSTL_ins_h := (FillWin6uA.CSTL_ins_h ds).
Local Abbreviation CSTL_insert := (FillWin6uA.CSTL_insert ds).
Local Abbreviation CSTL_set_head := (FillWin6uA.CSTL_set_head ds).
Local Abbreviation CSTL_set_prev := (FillWin6uA.CSTL_set_prev ds).
Local Abbreviation LREGS_via := (FillWin6uA.LREGS_via S sp ds).

Local Ltac open_fw := open_fwpre HFW.
Local Ltac apart i j := apart_of HFW i j.
Local Ltac open_lregs H :=
  let H' := fresh "HL'" in pose proof H as H';
  destruct H' as (P8 & P2 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25).
Local Ltac open_cstl HK :=
  pose proof HK as (Kwl & Kpl & Khl & Kin & Kwr & Kws & Khs);
  pose proof (f_equal (@arr_len Z) Kin) as KIL; cbn beta in KIL.
Local Ltac in_LF := unfold FillWin6uA.LF; repeat first [ apply sub_franges_here; cbn; lia | apply sub_franges_later ].
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
  let pv := constr:(S :: (sp - 96) :: W :: PV :: HD :: strm :: INP :: ws :: hs :: pvx) in
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  unfold mapped, dsl_SIZE, zsl_SIZE in *;
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs fwC fuel dirs rds pins vb NoRegions pv NoVals F1 F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => try sc_close
  end.

Local Ltac cellZ HRI acc name :=
  pose proof (acc s6u_segs _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HRI))))))) as name.


Lemma lc_small : forall regs m s len,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 10 = zw len -> 0 <= len <= 65536 ->
  ds_lookahead s + len + ds_insert s < 3 ->
  let s' := set_lookahead s (ds_lookahead s + len) in
  exists R m', msteps s6u_segs (mkst regs (0x16bc4 : word) m s6u_rom) (mkst R (0x16d00 : word) m' s6u_rom)
    /\ RI m' s' /\ CSTL s' /\ LREGS R
    /\ getr R 10 = zw (ds_lookahead s + len)
    /\ (forall r : reg, reg_in r [10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s len HRI HW HK HL H10 Hlen Hsm s'. open_fw. open_wf HW. open_lregs HL. open_cstl HK.
  pose proof HRI as (Hz & _ & _ & MS & _). cellS Hz dsl_insert C5932. cellS Hz dsl_lookahead C180. trim.
  run 15%nat [true] [RVal (EVar 42); RVal (EVar 43)] [(10, EVar 41)]
      [(41%nat, 65537); (42%nat, 65537); (43%nat, 65537)]
      [len; ds_lookahead s; ds_insert s] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  eexists R, _. split; [rewrite ?(szwrap32_small (ds_lookahead s + len)) in Hms by lia; exact Hms|].
  split; [apply RI_lookahead; [exact HRI | exact HK]|].
  split; [apply CSTL_lookahead; exact HK|].
  split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  symex_reg HR (10%bv : reg) as A10. rewrite ?szwrap32_small in A10 by lia.
  split; [rewrite A10; f_equal; lia|]. fr_weak Hfr.
Qed.

Definition ILREGS (regs : bvmap 5 word) (s : deflate_state) (str : Z) : Prop :=
  getr regs 11 = zw (ds_insert s) /\ getr regs 10 = zw (ds_lookahead s) /\ getr regs 13 = zw str
  /\ getr regs 14 = zw (ds_hash_shift s) /\ getr regs 12 = zw W /\ getr regs 16 = zw (ds_hash_mask s)
  /\ getr regs 17 = zw (ds_ins_h s) /\ getr regs 15 = zw (18446744073709551615 - W).

Lemma lc_big : forall regs m s len,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 10 = zw len -> 0 <= len ->
  ds_strstart s + ds_lookahead s + len <= 2 * ws ->
  3 <= ds_lookahead s + len + ds_insert s ->
  let str := ds_strstart s - ds_insert s in
  let s1 := set_lookahead s (ds_lookahead s + len) in
  let s2 := set_ins_h s1 (arr_get (ds_window s) str) in
  let s3 := set_ins_h s2 (update_hash s2 (ds_ins_h s2) (arr_get (ds_window s) (str + 1))) in
  exists R m', msteps s6u_segs (mkst regs (0x16bc4 : word) m s6u_rom) (mkst R (0x16c4c : word) m' s6u_rom)
    /\ RI m' s3 /\ CSTL s3 /\ LREGS R /\ ILREGS R s3 str
    /\ (forall r : reg, reg_in r [5; 10; 11; 12; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s len HRI HW HK HL H10 Hlen Hsl Hbig str s1 s2 s3. open_fw. open_wf HW. open_lregs HL. open_cstl HK.
  pose proof HRI as (Hz & _ & _ & MS & _).
  cellS Hz dsl_insert C5932. cellS Hz dsl_strstart C172. cellS Hz dsl_window C96. cellS Hz dsl_hash_shift C144.
  cellS Hz dsl_hash_mask C140. cellS Hz dsl_lookahead C180.
  pose proof Hz as (_ & Hwin & _). unfold dsl_windowA in Hwin. rewrite Kwl in Hwin.
  assert (Hcw : cells s6u_segs m W 1 1 (2 * ws) (wb (ds_window s))).
  { refine (cells_ext _ _ _ _ _ _ _ _ _ Hwin). intros i Hi. symmetry. apply wb_get; [|rewrite Kwl; exact Hi].
    intros j Hj. apply (wf_wb _ _ _ HW). rewrite <- Kwl. exact Hj. }
  clear Hwin. pose proof (fun j (_ : 0 <= j < 2 * ws) => wb_range (ds_window s) j) as Hwr.
  replace (ds_strstart s) with (ds_insert s + str) in C172 by lia.
  apart 1%nat 2%nat. trim.
  run 45%nat [false; false; false; false; false; false]
      [RVal (EVar 42); RVal (EVar 43); RVal (EAdd (EVar 43) (EVar 44)); RVal (EVar 34);
       RVal (EApp1 0%nat (EVar 44)); RVal (EVar 45); RVal (EApp1 0%nat (EAdd (EVar 44) (ELit 1))); RVal (EVar 46)]
      [(10, EVar 41)]
      [(41%nat, 65537); (42%nat, 65537); (43%nat, 65537); (44%nat, 65537); (45%nat, 32); (46%nat, 65536)]
      [len; ds_lookahead s; ds_insert s; str; ds_hash_shift s; ds_hash_mask s]
      (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  eexists R, _. split; [rewrite ?(szwrap32_small (ds_lookahead s + len)) in Hms by lia;
                        rewrite ?(szwrap32_small (ds_insert s + str - ds_insert s)) in Hms by lia; exact Hms|].
  cbn [fam].
  rewrite (wb_get (ds_window s) ltac:(intros j Hj; apply (wf_wb _ _ _ HW); rewrite <- Kwl; exact Hj) str) by (rewrite Kwl; lia).
  rewrite (wb_get (ds_window s) ltac:(intros j Hj; apply (wf_wb _ _ _ HW); rewrite <- Kwl; exact Hj) (str + 1)) by (rewrite Kwl; lia).
  pose proof (wf_wb _ _ _ HW str ltac:(lia)) as Hb0.
  rewrite (update_hash_sllw s2 (arr_get (ds_window s) str) (ds_hash_shift s) (arr_get (ds_window s) (str + 1)) (ds_hash_mask s))
    by (subst s2 s1; dsred; try reflexivity; lia).
  replace (ds_insert s + str - ds_insert s) with str by lia.
  assert (HRI1 : RI (wbytes m (zw (S + 180)) (Z_to_le_bytes 4 (ds_lookahead s + len))) s1) by (apply RI_lookahead; [exact HRI | exact HK]).
  pose proof (CSTL_lookahead s (ds_lookahead s + len) HK) as HK1. fold s1 in HK1.
  pose proof (RI_ins_h _ s1 (arr_get (ds_window s) str) HRI1 HK1) as HRI2. fold s2 in HRI2.
  pose proof (CSTL_ins_h s1 (arr_get (ds_window s) str) HK1) as HK2. fold s2 in HK2.
  assert (Eih : ds_ins_h s2 = arr_get (ds_window s) str) by reflexivity.
  rewrite <- Eih.
  pose proof (RI_ins_h _ s2 (update_hash s2 (ds_ins_h s2) (arr_get (ds_window s) (str + 1))) HRI2 HK2) as HRI3. fold s3 in HRI3.
  pose proof (CSTL_ins_h s2 (update_hash s2 (ds_ins_h s2) (arr_get (ds_window s) (str + 1))) HK2) as HK3. fold s3 in HK3.
  split; [exact HRI3|]. split; [exact HK3|].
  split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  symex_reg HR (11%bv : reg) as A11. symex_reg HR (10%bv : reg) as A10. symex_reg HR (13%bv : reg) as A13.
  symex_reg HR (14%bv : reg) as A14. symex_reg HR (12%bv : reg) as A12. symex_reg HR (16%bv : reg) as A16.
  symex_reg HR (17%bv : reg) as A17. symex_reg HR (15%bv : reg) as A15.
  split.
  { unfold ILREGS. subst s3 s2 s1. dsred.
    split; [exact A11|]. split; [rewrite A10; rewrite ?szwrap32_small by lia; f_equal; lia|].
    split; [rewrite A13; rewrite ?szwrap32_small by lia; f_equal; lia|].
    split; [exact A14|]. split; [exact A12|]. split; [rewrite A16; rewrite ?szwrap32_small by lia; reflexivity|].
    split.
    { rewrite A17. cbn [fam].
      rewrite !(wb_get (ds_window s) ltac:(intros j Hj; apply (wf_wb _ _ _ HW); rewrite <- Kwl; exact Hj)) by (rewrite Kwl; lia).
      replace (ds_insert s + str - ds_insert s) with str by lia.
      rewrite (update_hash_sllw (set_ins_h (set_lookahead s (ds_lookahead s + len)) (arr_get (ds_window s) str))
                 (arr_get (ds_window s) str) (ds_hash_shift s) (arr_get (ds_window s) (str + 1)) (ds_hash_mask s))
        by (dsred; try reflexivity; lia).
      reflexivity. }
    rewrite A15. apply zw_eqm. rewrite lxor_m1_mod64 by lia. rewrite Z.mod_small by lia. reflexivity. }
  fr_weak Hfr.
Qed.



Definition ILINV (s : deflate_state) (str : Z) : Prop :=
  0 <= ds_hash_shift s < 32 /\ ds_hash_mask s = hs - 1 /\ ds_w_mask s = ws - 1
  /\ 0 <= str /\ ds_insert s = ds_strstart s - str /\ 0 <= ds_insert s
  /\ 0 <= ds_ins_h s < 2 ^ 32 /\ 0 <= ds_lookahead s
  /\ ds_strstart s + ds_lookahead s <= 2 * ws
  /\ (forall i, 0 <= i < 2 * ws -> 0 <= arr_get (ds_window s) i < 256)
  /\ (forall i, 0 <= i < ws -> 0 <= arr_get (ds_prev s) i < 65536)
  /\ (forall i, 0 <= i < hs -> 0 <= arr_get (ds_head s) i < 65536).

Definition il_next (s : deflate_state) (str : Z) : deflate_state :=
  let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + 2)) in
  let s1 := set_ins_h s h in
  let s2 := set_prev s1 (arr_set (ds_prev s1) (Z.land str (ds_w_mask s1)) (arr_get (ds_head s1) h)) in
  let s3 := set_head s2 (arr_set (ds_head s2) h (wrap16 str)) in
  set_insert s3 (ds_insert s3 - 1).

Definition il_clob : list reg := [5; 6; 7; 11; 13; 17; 28; 29]%bv.

Lemma il_exit : forall regs m s str,
  RI m s -> CSTL s -> LREGS regs -> ILREGS regs s str -> ILINV s str ->
  ds_insert s = 0 ->
  exists R, msteps s6u_segs (mkst regs (0x16c4c : word) m s6u_rom) (mkst R (0x16d00 : word) m s6u_rom)
    /\ LREGS R /\ getr R 10 = zw (ds_lookahead s)
    /\ (forall r : reg, reg_in r il_clob = false -> getr R r = getr regs r).
Proof.
  intros regs m s str HRI HK HL HIL HIV Hz0. open_fw. open_lregs HL.
  destruct HIL as (I11 & I10 & I13 & I14 & I12 & I16 & I17 & I15).
  destruct HIV as (Vsh & Vhm & Vwm & Vstr & Vins & Vins0 & Vih & Vlook & Vsl & Hwb & Hpb & Hhb).
  rewrite Hz0 in I11. trim.
  run 10%nat [true] NoReads [(11, ELit 0); (10, EVar 41)] [(41%nat, 65537)]
      [ds_lookahead s] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  exists R. split; [exact Hms|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  symex_reg HR (10%bv : reg) as A10. split; [exact A10|]. fr_weak Hfr.
Qed.

Local Ltac il_fin :=
  lazymatch goal with
  | X := ?Xb : Z, Y := ?Yb : Z, s1 := _ : deflate_state, s2 := _ : deflate_state, s3 := _ : deflate_state,
    HRI : RI ?m ?s, HK : CSTL _, HL : LREGS ?regs, Hprev : cells _ _ PV 2 2 _ _, Hhb : forall i, _ -> 0 <= arr_get (ds_head _) i < 65536,
    I13 : getr _ 13 = zw ?str
    |- _ =>
  lazymatch goal with
  | R : bvmap 5 word, HR : regs_ok _ _ _, Hfr : forall r, _ -> getr _ r = getr _ r, Hms : msteps _ _ _ |- _ =>
    eexists R, _; split; [exact Hms|];
    repeat match goal with H : hidden _ |- _ => unfold hidden in H end;
    fold X; fold Y;
    rewrite (Z_to_le_bytes_eqm 2 (pb (ds_head s) X) (arr_get (ds_head s) X))
      by (unfold pb; change (2 ^ (8 * Z.of_nat 2)) with 65536; rewrite !Z.mod_mod by lia; reflexivity);
    rewrite (Z_to_le_bytes_eqm 2 str (wrap16 str))
      by (rewrite wrap16_mod; change (2 ^ (8 * Z.of_nat 2)) with (2 ^ 16); rewrite Z.mod_mod by lia; reflexivity);
    rewrite (szwrap32_small (ds_insert s + -1)) by lia;
    let HRI1 := fresh "HRI1" in let HK1 := fresh "HK1" in
    pose proof (RI_ins_h m s X HRI HK) as HRI1; fold s1 in HRI1;
    pose proof (CSTL_ins_h s X HK) as HK1; fold s1 in HK1;
    let Hp1 := fresh "Hp1" in
    assert (Hp1 : cells s6u_segs (wbytes m (zw (S + 128)) (Z_to_le_bytes 4 X)) PV 2 2 ws (arr_get (ds_prev s)))
      by (apply cells_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia); exact Hprev);
    let Hp2 := fresh "Hp2" in
    pose proof (cells_write_cell s6u_segs _ PV 2 2 ws (arr_get (ds_prev s)) Y (arr_get (ds_head s) X) Hp1
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hp2;
    replace (PV + 2 * Y) with (PV + Y * 2 ^ 1) in Hp2 by lia;
    let HRI2 := fresh "HRI2" in let HK2 := fresh "HK2" in
    assert (HRI2 : RI (wbytes (wbytes m (zw (S + 128)) (Z_to_le_bytes 4 X)) (zw (PV + Y * 2 ^ 1)) (Z_to_le_bytes 2 (arr_get (ds_head s) X))) s2);
    [ eapply (RI_updPV _ _ s1 _ HRI1 HK1);
      [ apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try lia; [apply agree_out_refl | apply sub_franges_here; cbn; lia]
      | intros x Hx; apply wbytes_grows; exact Hx
      | rewrite arr_len_set; subst s1; dsred; unfold FillWin6uA.CSTL in HK; tauto
      | refine (cells_ext _ _ _ _ _ _ _ _ _ Hp2); intros i Hi; cbn beta; subst s1; dsred;
        subst Y; rewrite arr_get_set; unfold arr_inb;
        match goal with K : arr_len (ds_prev s) = _ |- _ => rewrite K end;
        destruct (Z.eqb_spec (Z.land str (ds_w_mask s)) i), (Z.eqb_spec i (Z.land str (ds_w_mask s))),
                 (Z.leb_spec 0 (Z.land str (ds_w_mask s))), (Z.ltb_spec (Z.land str (ds_w_mask s)) ws);
          cbn [andb]; try reflexivity; lia ]
    | assert (HK2 : CSTL s2) by (apply CSTL_set_prev; [exact HK1 | rewrite arr_len_set; subst s1; dsred; unfold FillWin6uA.CSTL in HK; tauto]);
      let Hh2 := fresh "Hh2" in
      assert (Hh2 : cells s6u_segs (wbytes (wbytes m (zw (S + 128)) (Z_to_le_bytes 4 X)) (zw (PV + Y * 2 ^ 1)) (Z_to_le_bytes 2 (arr_get (ds_head s) X)))
                      HD 2 2 hs (arr_get (ds_head s)));
      [ apply cells_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia);
        apply cells_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia);
        match goal with Hh : cells _ m HD 2 2 _ (arr_get _) |- _ => exact Hh end
      | let Hh3 := fresh "Hh3" in
        pose proof (cells_write_cell s6u_segs _ HD 2 2 hs (arr_get (ds_head s)) X (wrap16 str) Hh2
                      ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hh3;
        replace (HD + 2 * X) with (HD + X * 2 ^ 1) in Hh3 by lia;
        let HRI3 := fresh "HRI3" in let HK3 := fresh "HK3" in
        assert (HRI3 : RI (wbytes (wbytes (wbytes m (zw (S + 128)) (Z_to_le_bytes 4 X)) (zw (PV + Y * 2 ^ 1)) (Z_to_le_bytes 2 (arr_get (ds_head s) X)))
                             (zw (HD + X * 2 ^ 1)) (Z_to_le_bytes 2 (wrap16 str))) s3);
        [ eapply (RI_updHD _ _ s2 _ HRI2 HK2);
          [ apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try lia; [apply agree_out_refl | apply sub_franges_here; cbn; lia]
          | intros x Hx; apply wbytes_grows; exact Hx
          | rewrite arr_len_set; subst s2 s1; dsred; unfold FillWin6uA.CSTL in HK; tauto
          | refine (cells_ext _ _ _ _ _ _ _ _ _ Hh3); intros i Hi; cbn beta; subst s2 s1; dsred;
            rewrite arr_get_set; unfold arr_inb;
            match goal with K : arr_len (ds_head s) = _ |- _ => rewrite K end;
            destruct (Z.eqb_spec X i), (Z.eqb_spec i X), (Z.leb_spec 0 X), (Z.ltb_spec X hs);
              cbn [andb]; try reflexivity; lia ]
        | assert (HK3 : CSTL s3) by (apply CSTL_set_head; [exact HK2 | rewrite arr_len_set; subst s2 s1; dsred; unfold FillWin6uA.CSTL in HK; tauto]);
          replace (ds_insert s + -1) with (ds_insert s3 - 1) by (subst s3 s2 s1; dsred; lia);
          split; [apply RI_insert; [exact HRI3 | exact HK3]|];
          split; [apply CSTL_insert; exact HK3|];
          split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|];
          split;
          [ unfold ILREGS; subst s3 s2 s1; dsred;
            let A := fresh "A" in
            split; [symex_reg HR (11%bv : reg) as A; rewrite A; rewrite ?szwrap32_small by lia; f_equal; lia|];
            split; [rewrite (Hfr 10%bv eq_refl); assumption|];
            split; [symex_reg HR (13%bv : reg) as A; rewrite A; rewrite ?szwrap32_small by lia; f_equal; lia|];
            split; [rewrite (Hfr 14%bv eq_refl); assumption|];
            split; [rewrite (Hfr 12%bv eq_refl); assumption|];
            split; [rewrite (Hfr 16%bv eq_refl); assumption|];
            split; [symex_reg HR (17%bv : reg) as A; rewrite A; reflexivity|];
            rewrite (Hfr 15%bv eq_refl); assumption
          | split; [| fr_weak Hfr];
            unfold ILINV; subst s3 s2 s1; dsred;
            repeat match goal with |- _ /\ _ => split end; try lia;
            first
              [ assumption
              | let i := fresh "i" in let Hi := fresh "Hi" in
                intros i Hi; rewrite arr_get_set;
                destruct (_ && _);
                [ first [ apply Hhb; lia | pose proof (wrap16_range str); lia ]
                | first [ match goal with Hpb : forall j, _ -> 0 <= arr_get (ds_prev s) j < 65536 |- _ => apply Hpb; exact Hi end
                        | apply Hhb; exact Hi ] ] ] ] ] ] ]
  end end.

Lemma il_step : forall regs m s str,
  RI m s -> CSTL s -> LREGS regs -> ILREGS regs s str -> ILINV s str ->
  ds_insert s <> 0 -> 3 <= ds_lookahead s + ds_insert s ->
  let s4 := il_next s str in
  exists R m', msteps s6u_segs (mkst regs (0x16c4c : word) m s6u_rom)
                 (mkst R (if ds_lookahead s4 + ds_insert s4 <? 3 then (0x16d00 : word) else (0x16c4c : word)) m' s6u_rom)
    /\ RI m' s4 /\ CSTL s4 /\ LREGS R /\ ILREGS R s4 (str + 1) /\ ILINV s4 (str + 1)
    /\ (forall r : reg, reg_in r il_clob = false -> getr R r = getr regs r).
Proof.
  intros regs m s str HRI HK HL HIL HIV Hnz Hbig s4. open_fw. open_lregs HL. open_cstl HK. open_ub HUB.
  destruct HIL as (I11 & I10 & I13 & I14 & I12 & I16 & I17 & I15).
  pose proof HIV as (Vsh & Vhm & Vwm & Vstr & Vins & Vins0 & Vih & Vlook & Vsl & Hwb & Hpb & Hhb).
  pose proof HRI as (Hz & _ & _ & MS & MW & MP & MH & _).
  cellS Hz dsl_head C120. cellS Hz dsl_w_mask C88. cellS Hz dsl_prev C112. cellS Hz dsl_insert C5932.
  pose proof Hz as (_ & Hwin & Hprev & Hhead & _).
  unfold dsl_windowA in Hwin. rewrite Kwl in Hwin. unfold dsl_prevA in Hprev. rewrite Kpl in Hprev.
  unfold dsl_headA in Hhead. rewrite Khl in Hhead.
  assert (Hcw : cells s6u_segs m W 1 1 (2 * ws) (wb (ds_window s))).
  { refine (cells_ext _ _ _ _ _ _ _ _ _ Hwin). intros i Hi. symmetry. apply wb_get; [|rewrite Kwl; exact Hi].
    intros j Hj. apply Hwb. rewrite <- Kwl. exact Hj. }
  assert (Hch : cells s6u_segs m HD 2 2 hs (pb (ds_head s))).
  { refine (cells_ext _ _ _ _ _ _ _ _ _ Hhead). intros i Hi. symmetry. apply pb_get; [|rewrite Khl; exact Hi].
    intros j Hj. apply Hhb. rewrite <- Khl. exact Hj. }
  clear Hwin.
  pose proof (fun j (_ : 0 <= j < 2 * ws) => wb_range (ds_window s) j) as Hwr.
  pose proof (fun j (_ : 0 <= j < hs) => pb_range (ds_head s) j) as Hhr.
  set (F := fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  set (X := Z.land (Z.lxor (zaluw ALU_SLL (ds_ins_h s) (ds_hash_shift s)) (F 0%nat (str + 2))) (ds_hash_mask s)).
  set (Y := Z.land str (ds_w_mask s)).
  pose proof (land_mask_range (Z.lxor (zaluw ALU_SLL (ds_ins_h s) (ds_hash_shift s)) (F 0%nat (str + 2))) (ds_hash_mask s) ltac:(lia)) as HX.
  fold X in HX.
  assert (HY : 0 <= Y <= ws - 1).
  { subst Y. rewrite Vwm. apply land_mask_range. lia. }
  pose proof (even_plus_shl1 HD X UHD2 ltac:(lia) ltac:(lia)) as EHX.
  pose proof (even_plus_shl1 PV Y UPV2 ltac:(lia) ltac:(lia)) as EPY.
  apart 1%nat 3%nat. apart 3%nat 4%nat.
  repeat match goal with H : _ \/ _ |- _ => apply hide in H end.
  apart 1%nat 4%nat.
  assert (EX : X = update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + 2))).
  { subst X F. cbn [fam]. rewrite (wb_get (ds_window s) ltac:(intros j Hj; apply Hwb; rewrite <- Kwl; exact Hj)) by (rewrite Kwl; lia).
    apply update_hash_sllw; try reflexivity; lia. }
  subst s4. unfold il_next. rewrite <- EX.
  set (s1 := set_ins_h s X).
  set (s2 := set_prev s1 (arr_set (ds_prev s1) (Z.land str (ds_w_mask s1)) (arr_get (ds_head s1) X))).
  set (s3 := set_head s2 (arr_set (ds_head s2) X (wrap16 str))).
  replace (ds_lookahead (set_insert s3 (ds_insert s3 - 1)) + ds_insert (set_insert s3 (ds_insert s3 - 1)))
    with (ds_lookahead s + ds_insert s - 1) by (subst s3 s2 s1; dsred; lia).
  trim.
  destruct (Z.ltb_spec (ds_lookahead s + ds_insert s - 1) 3) as [Brk|Cont].
  - run 60%nat [false; false; false; false; false; false; false; false; false; false; false; false]
      [RVal (EApp1 0%nat (EAdd (EVar 42) (ELit 2))); RVal (EVar 36); RVal (EVar 47); RVal (EVar 35); RVal (EVar 48)]
      [(11, EVar 41); (13, EVar 42); (17, EVar 43); (14, EVar 44); (16, EVar 45); (10, EVar 46); (12, EVar 34);
       (15, ESub (ELit 18446744073709551615) (EVar 34))]
      [(41%nat, 65537); (42%nat, 65537); (43%nat, 2 ^ 32); (44%nat, 32); (45%nat, 65536); (46%nat, 65537); (47%nat, 65536); (48%nat, 65536)]
      [ds_insert s; str; ds_ins_h s; ds_hash_shift s; ds_hash_mask s; ds_lookahead s; ds_w_mask s; pb (ds_head s) X]
      F.
    all: try solve [rewrite I15; f_equal; lia].
    il_fin.
  - run 60%nat [false; false; false; false; false; false; false; false; false; false; false; true]
      [RVal (EApp1 0%nat (EAdd (EVar 42) (ELit 2))); RVal (EVar 36); RVal (EVar 47); RVal (EVar 35); RVal (EVar 48)]
      [(11, EVar 41); (13, EVar 42); (17, EVar 43); (14, EVar 44); (16, EVar 45); (10, EVar 46); (12, EVar 34);
       (15, ESub (ELit 18446744073709551615) (EVar 34))]
      [(41%nat, 65537); (42%nat, 65537); (43%nat, 2 ^ 32); (44%nat, 32); (45%nat, 65536); (46%nat, 65537); (47%nat, 65536); (48%nat, 65536)]
      [ds_insert s; str; ds_ins_h s; ds_hash_shift s; ds_hash_mask s; ds_lookahead s; ds_w_mask s; pb (ds_head s) X]
      F.
    all: try solve [rewrite I15; f_equal; lia].
    il_fin.
Qed.

Lemma il_loop : forall n regs m s str,
  ds_insert s = Z.of_nat n ->
  RI m s -> CSTL s -> LREGS regs -> ILREGS regs s str -> ILINV s str ->
  (ds_insert s <> 0 -> 3 <= ds_lookahead s + ds_insert s) ->
  exists R m', msteps s6u_segs (mkst regs (0x16c4c : word) m s6u_rom) (mkst R (0x16d00 : word) m' s6u_rom)
    /\ RI m' (fill_window_insert (Z.to_nat (ds_insert s)) s str)
    /\ CSTL (fill_window_insert (Z.to_nat (ds_insert s)) s str)
    /\ LREGS R /\ getr R 10 = zw (ds_lookahead s)
    /\ (forall r : reg, reg_in r il_clob = false -> getr R r = getr regs r).
Proof.
  induction n as [|n IH]; intros regs m s str Hn HRI HK HL HIL HIV Hbig.
  - destruct (il_exit regs m s str HRI HK HL HIL HIV ltac:(lia)) as (R & Hms & HL' & A10 & Hfr).
    exists R, m. rewrite Hn. change (Z.to_nat (Z.of_nat 0)) with 0%nat. cbn [fill_window_insert].
    split; [exact Hms|]. split; [exact HRI|]. split; [exact HK|]. split; [exact HL'|]. split; [exact A10|exact Hfr].
  - assert (Hnz : ds_insert s <> 0) by lia. specialize (Hbig Hnz).
    destruct (il_step regs m s str HRI HK HL HIL HIV Hnz Hbig) as (R1 & m1 & Hms1 & HRI1 & HK1 & HL1 & HIL1 & HIV1 & Hfr1).
    rewrite (fill_window_insert_step (ds_insert s) s str) by lia.
    replace (ds_insert s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    change (str + (MIN_MATCH - 1)) with (str + 2). cbv zeta.
    lazymatch goal with |- context [fill_window_insert _ ?s4v (str + 1)] => change s4v with (il_next s str) end.
    lazymatch goal with |- context [if ?c <? MIN_MATCH then ?s4v else _] =>
      change s4v with (il_next s str); change c with (ds_lookahead (il_next s str) + ds_insert (il_next s str)) end.
    set (s4 := il_next s str) in *. unfold MIN_MATCH.
    assert (EL4 : ds_lookahead s4 = ds_lookahead s) by (subst s4; unfold il_next; dsred; reflexivity).
    destruct (Z.ltb_spec (ds_lookahead s4 + ds_insert s4) 3) as [Brk|Cont].
    + exists R1, m1. split; [exact Hms1|]. split; [exact HRI1|]. split; [exact HK1|].
      split; [exact HL1|]. split; [rewrite <- EL4; exact (proj1 (proj2 HIL1))|exact Hfr1].
    + assert (Hn' : ds_insert s4 = Z.of_nat n) by (subst s4; unfold il_next; dsred; lia).
      destruct (IH R1 m1 s4 (str + 1) Hn' HRI1 HK1 HL1 HIL1 HIV1 ltac:(lia))
        as (R2 & m2 & Hms2 & HRI2 & HK2 & HL2 & B10 & Hfr2).
      replace (Z.to_nat (ds_insert s - 1)) with (Z.to_nat (ds_insert s4)) by (rewrite Hn'; lia).
      exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact HRI2|]. split; [exact HK2|]. split; [exact HL2|]. split; [rewrite B10, EL4; reflexivity|].
      intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.


Lemma cond_run : forall regs m s,
  RI m s -> CSTL s -> LREGS regs ->
  0 <= cs_avail_in (ds_strm s) < 2 ^ 32 -> 0 <= ds_lookahead s <= 65536 ->
  getr regs 10 = zw (ds_lookahead s) ->
  exists R, msteps s6u_segs (mkst regs (0x16d00 : word) m s6u_rom)
              (mkst R (if (ds_lookahead s <? MIN_LOOKAHEAD) && negb (cs_avail_in (ds_strm s) =? 0)
                       then (0x16a20 : word) else (0x16d1c : word)) m s6u_rom)
    /\ LREGS R /\ getr R 10 = zw (ds_lookahead s)
    /\ (forall r : reg, reg_in r [11; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s HRI HK HL Hai Hlook H10. open_fw. open_lregs HL. open_cstl HK. open_ub HUB.
  pose proof HRI as (Hz & _). cellS Hz dsl_strm C0. rewrite Z.add_0_r in C0. cellZ HRI zsl_avail_in Z8.
  pose proof (szwrap32_u64_zero (cs_avail_in (ds_strm s)) ltac:(lia)) as Hsw. trim.
  unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH. change (258 + 3 + 1) with 262.
  destruct (Z.ltb_spec (ds_lookahead s) 262) as [Ll|Lg]; cbn [andb].
  - destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [A0|A0]; cbn [negb].
    + run 12%nat [false; false; false; false] [RVal (EVar 37); RVal (EVar 42)] [(10, EVar 41)]
          [(41%nat, 65537); (42%nat, 2 ^ 32)] [ds_lookahead s; cs_avail_in (ds_strm s)]
          (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
      all: try solve [pose proof (proj2 Hsw A0); zcond_close].
      all: try solve [intros E; apply E; apply (proj2 Hsw); exact A0].
      exists R. split; [exact Hms|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
      split; [rewrite (Hfr 10%bv eq_refl); exact H10|]. fr_weak Hfr.
    + run 12%nat [false; false; false; true] [RVal (EVar 37); RVal (EVar 42)] [(10, EVar 41)]
          [(41%nat, 65537); (42%nat, 2 ^ 32)] [ds_lookahead s; cs_avail_in (ds_strm s)]
          (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
      all: try solve [intros E; apply A0; apply (proj1 Hsw); exact E].
      exists R. split; [exact Hms|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
      split; [rewrite (Hfr 10%bv eq_refl); exact H10|]. fr_weak Hfr.
  - run 12%nat [true] [RVal (EVar 37); RVal (EVar 42)] [(10, EVar 41)]
        [(41%nat, 65537); (42%nat, 2 ^ 32)] [ds_lookahead s; cs_avail_in (ds_strm s)]
        (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
    exists R. split; [exact Hms|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
    split; [rewrite (Hfr 10%bv eq_refl); exact H10|]. fr_weak Hfr.
Qed.

End Walk.
End FXG.

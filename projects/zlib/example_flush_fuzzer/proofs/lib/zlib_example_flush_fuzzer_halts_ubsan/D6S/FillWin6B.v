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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 Callee6 FillWin6A.
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


Lemma ns_run : forall regs m s,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  exists R, msteps s6_segs (mkst regs (0x168d8 : word) m s6_rom)
              (mkst R (if cs_avail_in (ds_strm s) =? 0 then (0x16a5c : word) else (0x168e4 : word)) m s6_rom)
    /\ LREGS R /\ getr R 27 = zw strm /\ getr R 12 = zw (szwrap 32 (cs_avail_in (ds_strm s)))
    /\ (forall r : reg, reg_in r [12; 27]%bv = false -> getr R r = getr regs r).
Proof using PV2 HD2 HFW.
  intros regs m s HRI HW HK HL. open_fw. open_wf HW. open_lregs HL.
  pose proof HRI as (Hz & _). cellS Hz dsl_strm C0. rewrite Z.add_0_r in C0. cellZ HRI zsl_avail_in Z8.
  pose proof (szwrap32_u64_zero (cs_avail_in (ds_strm s)) ltac:(lia)) as Hsw. trim.
  destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [E0|N0].
  - run 10%nat [true] [RVal (EVar 37); RVal (EVar 41)] NoPins [(41%nat, 2 ^ 32)]
        [cs_avail_in (ds_strm s)] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
    all: try solve [apply (proj2 Hsw); exact E0].
    exists R. split; [exact Hms|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
    symex_reg HR (27%bv : reg) as A27. symex_reg HR (12%bv : reg) as A12.
    split; [exact A27|]. split; [exact A12|]. fr_weak Hfr.
  - run 10%nat [false] [RVal (EVar 37); RVal (EVar 41)] NoPins [(41%nat, 2 ^ 32)]
        [cs_avail_in (ds_strm s)] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
    all: try solve [intros E; apply N0; apply (proj1 Hsw); exact E].
    exists R. split; [exact Hms|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
    symex_reg HR (27%bv : reg) as A27. symex_reg HR (12%bv : reg) as A12.
    split; [exact A27|]. split; [exact A12|]. fr_weak Hfr.
Qed.



Definition rb_clob1 : list reg := [1; 9; 10; 11; 12; 13; 14; 18; 19]%bv.

Lemma rb1 : forall regs m s more,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 12 = zw (szwrap 32 (cs_avail_in (ds_strm s))) -> getr regs 18 = zw more ->
  getr regs 27 = zw strm -> getr regs 11 = zw (ds_strstart s) ->
  0 <= more <= 65536 -> cs_avail_in (ds_strm s) <> 0 ->
  let ai := cs_avail_in (ds_strm s) in
  let len := (if more <? ai then more else ai) in
  exists R,
    (len = 0 /\ msteps s6_segs (mkst regs (0x168e4 : word) m s6_rom) (mkst R (0x16980 : word) m s6_rom)
     /\ LREGS R /\ getr R 9 = zw 0 /\ getr R 10 = zw (ds_lookahead s) /\ getr R 27 = zw strm
     /\ (forall r : reg, reg_in r rb_clob1 = false -> getr R r = getr regs r))
    \/ (0 < len /\ msteps s6_segs (mkst regs (0x168e4 : word) m s6_rom)
                     (mkst R (0x27800 : word) (wbytes m (zw (strm + 8)) (Z_to_le_bytes 4 (ai - len))) s6_rom)
     /\ LREGS R /\ getr R 1 = zw 0x1692c
     /\ getr R 10 = zw (W + (ds_strstart s + ds_lookahead s)) /\ getr R 11 = zw (INP + cs_next_in (ds_strm s))
     /\ getr R 12 = zw len /\ getr R 9 = zw len /\ getr R 18 = zw len
     /\ getr R 19 = zw (W + (ds_strstart s + ds_lookahead s)) /\ getr R 27 = zw strm
     /\ (forall r : reg, reg_in r rb_clob1 = false -> getr R r = getr regs r)).
Proof using PV2 HD2 HFW.
  intros regs m s more HRI HW HK HL H12 H18 H27 H11 Hmore Hai ai len. open_fw. open_wf HW. open_lregs HL. open_cstl HK.
  pose proof HRI as (Hz & _ & _ & _ & _ & _ & _ & MZ & _).
  cellS Hz dsl_lookahead C180. cellS Hz dsl_window C96. cellZ HRI zsl_next_in ZN. rewrite Z.add_0_r in ZN.
  pose proof (szwrap32_u64 (cs_avail_in (ds_strm s)) ltac:(lia)) as Hu.
  subst ai len. trim.
  destruct (Z_lt_le_dec (cs_avail_in (ds_strm s)) more) as [Blt|Bge].
  2: {
    replace (if more <? cs_avail_in (ds_strm s) then more else cs_avail_in (ds_strm s)) with more
      by (destruct (Z.ltb_spec more (cs_avail_in (ds_strm s))); lia).
    destruct (Z.eq_dec more 0) as [M0|M0].
    + run 30%nat [false; true] [RVal (EVar 43); RVal (EVar 34); RVal (EAdd (EVar 38) (EVar 45))]
        [(12, ESx 32 (EVar 41)); (18, EVar 42); (27, EVar 37); (11, EVar 44)]
        [(41%nat, 2 ^ 32); (42%nat, 65537); (43%nat, 65537); (44%nat, 65537); (45%nat, 2 ^ 63)]
        [cs_avail_in (ds_strm s); more; ds_lookahead s; ds_strstart s; cs_next_in (ds_strm s)]
        (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
      all: try solve [rewrite Hu; destruct (Z.ltb_spec (cs_avail_in (ds_strm s)) (2 ^ 31)); lia].
      exists R. left. split; [lia|]. split; [exact Hms|].
      split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
      symex_reg HR (9%bv : reg) as A9. symex_reg HR (10%bv : reg) as A10. symex_reg HR (27%bv : reg) as A27.
      split; [rewrite A9; f_equal; lia|]. split; [exact A10|]. split; [exact A27|]. fr_weak Hfr.
    + run 30%nat [false; false] [RVal (EVar 43); RVal (EVar 34); RVal (EAdd (EVar 38) (EVar 45))]
        [(12, ESx 32 (EVar 41)); (18, EVar 42); (27, EVar 37); (11, EVar 44)]
        [(41%nat, 2 ^ 32); (42%nat, 65537); (43%nat, 65537); (44%nat, 65537); (45%nat, 2 ^ 63)]
        [cs_avail_in (ds_strm s); more; ds_lookahead s; ds_strstart s; cs_next_in (ds_strm s)]
        (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
      all: try solve [rewrite Hu; destruct (Z.ltb_spec (cs_avail_in (ds_strm s)) (2 ^ 31)); lia].
      exists R. right. split; [lia|].
      split.
      { match type of Hms with context [Z_to_le_bytes 4 ?e] =>
          rewrite (Z_to_le_bytes_eqm 4 (cs_avail_in (ds_strm s) - more) e);
            [exact Hms | change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); rewrite ?szwrap_eqm by lia;
                         rewrite ?szwrap32_small by lia; first [reflexivity | f_equal; lia] ] end. }
      split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
      symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11.
      symex_reg HR (12%bv : reg) as A12. symex_reg HR (9%bv : reg) as A9. symex_reg HR (18%bv : reg) as A18.
      symex_reg HR (19%bv : reg) as A19. symex_reg HR (27%bv : reg) as A27.
      split; [exact A1|]. split; [rewrite A10; f_equal; lia|]. split; [exact A11|].
      split; [rewrite A12; rewrite ?Z.mod_small by lia; f_equal; lia|]. split; [exact A9|].
      split; [rewrite A18; rewrite ?Z.mod_small by lia; f_equal; lia|].
      split; [rewrite A19; f_equal; lia|]. split; [exact A27|]. fr_weak Hfr. }
  -
    replace (if more <? cs_avail_in (ds_strm s) then more else cs_avail_in (ds_strm s)) with (cs_avail_in (ds_strm s))
      by (destruct (Z.ltb_spec more (cs_avail_in (ds_strm s))); lia).
    run 30%nat [true; false] [RVal (EVar 43); RVal (EVar 34); RVal (EAdd (EVar 38) (EVar 45))]
        [(12, ESx 32 (EVar 41)); (18, EVar 42); (27, EVar 37); (11, EVar 44)]
        [(41%nat, 2 ^ 32); (42%nat, 65537); (43%nat, 65537); (44%nat, 65537); (45%nat, 2 ^ 63)]
        [cs_avail_in (ds_strm s); more; ds_lookahead s; ds_strstart s; cs_next_in (ds_strm s)]
        (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
    all: try solve [rewrite Hu; destruct (Z.ltb_spec (cs_avail_in (ds_strm s)) (2 ^ 31)); lia].
    exists R. right. split; [lia|].
    split.
    { match type of Hms with context [Z_to_le_bytes 4 ?e] =>
        rewrite (Z_to_le_bytes_eqm 4 (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm s)) e);
          [exact Hms | change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); rewrite ?szwrap_eqm by lia;
                       rewrite ?szwrap32_small by lia; first [reflexivity | f_equal; lia] ] end. }
    split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
    symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11.
    symex_reg HR (12%bv : reg) as A12. symex_reg HR (9%bv : reg) as A9. symex_reg HR (18%bv : reg) as A18.
    symex_reg HR (19%bv : reg) as A19. symex_reg HR (27%bv : reg) as A27.
    rewrite ?szwrap32_small in A9 by lia. rewrite ?szwrap32_small in A12 by lia. rewrite ?szwrap32_small in A18 by lia.
    split; [exact A1|]. split; [rewrite A10; f_equal; lia|]. split; [exact A11|].
    split; [rewrite A12; rewrite ?Z.mod_small by lia; f_equal; lia|]. split; [rewrite A9; f_equal; lia|].
    split; [rewrite A18; rewrite ?Z.mod_small by lia; f_equal; lia|].
    split; [rewrite A19; f_equal; lia|]. split; [exact A27|]. fr_weak Hfr.
Qed.



Lemma rb_copy : forall regs m s len,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 1 = zw 0x1692c -> getr regs 10 = zw (W + (ds_strstart s + ds_lookahead s)) ->
  getr regs 11 = zw (INP + cs_next_in (ds_strm s)) -> getr regs 12 = zw len ->
  0 < len -> cs_next_in (ds_strm s) + len <= arr_len (cs_input (ds_strm s)) ->
  len <= 2 * ws - ds_strstart s - ds_lookahead s ->
  let off := ds_strstart s + ds_lookahead s in
  let bytes := arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) len in
  let bs := fbytes (arr_get (cs_input (ds_strm s))) (cs_next_in (ds_strm s)) (Z.to_nat len) in
  let w' := arr_upd (ds_window s) off bytes in
  exists R, msteps s6_segs (mkst regs (0x27800 : word) m s6_rom)
                             (mkst R (0x1692c : word) (wbytes m (zw (W + off)) bs) s6_rom)
    /\ RI (wbytes m (zw (W + off)) bs) (set_window s w') /\ CSTL (set_window s w') /\ LREGS R
    /\ getr R 10 = zw (W + off)
    /\ (forall r : reg, reg_in r memcpy_clob = false -> getr R r = getr regs r)
    /\ rdn s6_segs (wbytes m (zw (W + off)) bs) (zw (W + off)) (Z.to_nat len) = Some bs
    /\ bZ bs = bytes /\ length bs = Z.to_nat len.
Proof using HLFimg MEMCPY ROM_local PV2 HD2 HFW.
  intros regs m s len HRI HW HK HL H1 H10 H11 H12 Hlen0 Hlen1 Hlen2 off bytes bs w'. open_fw. open_wf HW. open_cstl HK.
  pose proof HRI as (Hz & _ & _ & _ & MW & _). destruct Hz as (_ & Hwin & _ & _ & _ & Hin).
  unfold dsl_windowA in Hwin. rewrite Kwl in Hwin. unfold zsl_input in Hin.
  assert (Hrd : rdn s6_segs m (zw (INP + cs_next_in (ds_strm s))) (Z.to_nat len) = Some bs).
  { subst bs. apply (cells_rdn s6_segs m INP (arr_len (cs_input (ds_strm s)))); try lia. exact Hin. }
  assert (Hlen : length bs = Z.to_nat len) by (subst bs; apply fbytes_length).
  apart 2%nat 6%nat.
  destruct (MEMCPY m regs (W + off) (INP + cs_next_in (ds_strm s)) (Z.to_nat len) bs (zw 0x1692c) Hrd
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(eapply mapped_sub; [exact MW | lia | lia])
              ltac:(apply ret_ok_zw; [lia | reflexivity])
              H1 H10 H11 ltac:(rewrite Z2Nat.id by lia; exact H12))
    as (R & Hms & A10 & Hfr).
  symex_pc_lit_in Hms.
  exists R. split; [exact Hms|].
  assert (Hl' : arr_len w' = 2 * ws) by (subst w'; rewrite arr_len_upd; exact Kwl).
  assert (Hib : forall i, cs_next_in (ds_strm s) <= i < cs_next_in (ds_strm s) + Z.of_nat (Z.to_nat len) ->
                0 <= arr_get (cs_input (ds_strm s)) i < 256).
  { intros i Hi. apply (wf_ib _ _ _ HW). lia. }
  split.
  { eapply (RI_updW m _ s w' off (off + len) HRI HK).
    - replace (off + len - off) with (Z.of_nat (length bs)) by lia. apply memcpy_agree_out; lia.
    - intros x Hx. apply wbytes_grows. exact Hx.
    - lia. - lia. - lia.
    - exact Hl'.
    - pose proof (cells_wbytes_bytes s6_segs m W (2 * ws) (arr_get (ds_window s)) off bs Hwin
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hc.
      refine (cells_ext _ _ _ _ _ _ _ _ _ Hc). intros i Hi. cbn beta. subst w' bytes.
      rewrite (arr_get_upd _ _ _ _ 0). unfold arr_inb. rewrite Kwl, Hlen, arr_slice_length.
      destruct (Z.leb_spec off i), (Z.ltb_spec i (off + Z.of_nat (Z.to_nat len))), (Z.ltb_spec i (off + Z.max 0 len)),
        (Z.leb_spec 0 i), (Z.ltb_spec i (2 * ws)); cbn [andb]; try reflexivity; try lia.
      subst bs. rewrite fbytes_nth by (try lia; exact Hib).
      unfold arr_slice. rewrite arr_slice_nat_nth by lia. all: try (f_equal; lia). }
  split; [apply CSTL_set_window; [exact HK | exact Hl']|].
  split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  split; [exact A10|]. split; [exact Hfr|].
  split.
  { rewrite <- Hlen. apply rdn_wbytes_hit. rewrite u_zw_small by lia. lia. }
  split; [|exact Hlen].
  subst bs bytes. unfold arr_slice. apply bZ_fbytes_slice. exact Hib.
Qed.


Lemma rb_ck : forall regs m s len dst,
  RI m s -> CSTL s -> LREGS regs ->
  0 <= cs_adler (ds_strm s) < 2 ^ 64 ->
  getr regs 27 = zw strm -> getr regs 9 = zw len -> getr regs 19 = zw dst ->
  0 <= len <= 65536 -> 0 <= dst < 2 ^ 63 ->
  exists R, msteps s6_segs (mkst regs (0x1692c : word) m s6_rom) (mkst R (0x1a3d4 : word) m s6_rom)
    /\ LREGS R /\ getr R 27 = zw strm /\ getr R 9 = zw len /\ getr R 19 = zw dst
    /\ getr R 1 = zw 0x1694c /\ getr R 10 = zw (cs_adler (ds_strm s)) /\ getr R 11 = zw dst /\ getr R 12 = zw len
    /\ (forall r : reg, reg_in r [1; 10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof using PV2 HD2 Hwrap1 HFW.
  intros regs m s len dst HRI HK HL Had H27 H9 H19 Hlen Hdst. open_fw. open_lregs HL. open_cstl HK.
  pose proof HRI as (Hz & _). cellS Hz dsl_wrap C48. cellZ HRI zsl_state Z56. cellZ HRI zsl_adler Z96.
  rewrite Kwr, Hwrap1 in C48. trim.
  run 15%nat [false; false] [RVal (EVar 32); RVal (ELit 1); RVal (EVar 44)]
      [(27, EVar 37); (9, EVar 42); (19, EVar 43)]
      [(42%nat, 65537); (43%nat, 2 ^ 63); (44%nat, 2 ^ 64)]
      [0; len; dst; cs_adler (ds_strm s)] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  exists R. split; [exact Hms|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  symex_reg HR (27%bv : reg) as A27. symex_reg HR (9%bv : reg) as A9. symex_reg HR (19%bv : reg) as A19.
  symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11.
  symex_reg HR (12%bv : reg) as A12.
  split; [exact A27|]. split; [exact A9|]. split; [exact A19|]. split; [exact A1|]. split; [exact A10|].
  split; [exact A11|]. split; [exact A12|]. fr_weak Hfr.
Qed.

Lemma RI_below : forall m m' s,
  RI m s -> CSTL s -> agree_out [(sp - 144, 32)] m m' -> (forall x, m x <> None -> m' x <> None) -> RI m' s.
Proof using HLFimg ROM_local PV2 HD2 HFW.
  intros m m' s HRI HK Hag Hgr. open_fw.
  apart 0%nat 1%nat. apart 0%nat 2%nat. apart 0%nat 3%nat. apart 0%nat 4%nat. apart 0%nat 5%nat. apart 0%nat 6%nat.
  pose proof HK as (_ & _ & _ & Kin & _). pose proof (f_equal (@arr_len Z) Kin) as KIL. cbn beta in KIL.
  eapply (RI_transport m m' s s [(sp - 144, 32)] HRI HK Hag); try assumption.
  - intros x Hx. cbn in Hx. unfold FillWin6A.LF. cbn [in_franges]. left. lia.
  - intros; exact I.
  - apply (zst_keep_S m _ s _ HRI Hag). apply disj_franges_cons; [unfold dsl_SIZE; lia | apply disj_franges_nil].
  - apply (zst_keep_W m _ s _ HRI HK Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_PV m _ s _ HRI HK Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_HD m _ s _ HRI HK Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_Z m _ s _ HRI Hag). apply disj_franges_cons; [unfold zsl_SIZE; lia | apply disj_franges_nil].
  - apply (zst_keep_IN m _ s _ HRI HK Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply disj_franges_cons; [lia | apply disj_franges_nil].
Qed.


Lemma rb_adler : forall regs m s P (d : list byte) adler,
  RI m s -> CSTL s -> LREGS regs ->
  rdn s6_segs m (zw P) (length d) = Some d -> W <= P -> P + Z.of_nat (length d) <= W + 2 * ws ->
  Z.of_nat (length d) <= 65536 -> adler_canon adler ->
  getr regs 1 = zw 0x1694c -> getr regs 10 = zw adler -> getr regs 11 = zw P ->
  getr regs 12 = zw (Z.of_nat (length d)) ->
  exists R m', msteps s6_segs (mkst regs (0x1a3d4 : word) m s6_rom) (mkst R (0x1694c : word) m' s6_rom)
    /\ RI m' s /\ LREGS R /\ getr R 10 = zw (adler32_upd adler (bZ d))
    /\ (forall r : reg, reg_in r c_clob = false -> getr R r = getr regs r).
Proof using HLFimg ADLER ROM_local PV2 HD2 HFW.
  intros regs m s P d adler HRI HK HL Hrd HP HPl Hdl Hcan H1 H10 H11 H12. open_fw. open_lregs HL.
  pose proof Hcan as ((Ha0 & Ha1) & _ & _).
  pose proof HRI as (_ & _ & MF & _ & _ & _ & _ & _ & _ & _ & HROMm).
  apart 0%nat 2%nat.
  destruct (ADLER m regs adler P d (sp - 112) (zw 0x1694c) Hrd
              ltac:(lia) Hcan ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold ADLER_FR6; lia) ltac:(lia)
              ltac:(unfold ADLER_FR6; eapply mapped_sub; [exact MF | lia | lia])
              ltac:(unfold ADLER_FR6; lia)
              HROMm ltac:(apply ret_ok_zw; [lia | reflexivity])
              H1 P2 H10 H11 H12)
    as (R & m' & Hms & A10 & A2 & Hfr & Hag & Hgr).
  symex_pc_lit_in Hms.
  exists R, m'. split; [exact Hms|].
  split.
  { apply (RI_below m m' s HRI HK); [|exact Hgr].
    unfold ADLER_FR6 in Hag. replace (sp - 112 - 32) with (sp - 144) in Hag by lia. exact Hag. }
  split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  split.
  { change (reg_get R 10 = zw (adler32_upd adler (bZ d))). rewrite A10. unfold adler32_upd.
    rewrite (adler32_z_spec_canon adler P d Hcan) by lia. reflexivity. }
  exact Hfr.
Qed.


Lemma rb_st : forall regs m s A len,
  RI m s -> CSTL s -> LREGS regs ->
  0 <= cs_next_in (ds_strm s) -> cs_next_in (ds_strm s) + len <= arr_len (cs_input (ds_strm s)) ->
  0 <= cs_total_in (ds_strm s) < 2 ^ 64 -> 0 <= ds_lookahead s < 2 ^ 31 ->
  getr regs 27 = zw strm -> getr regs 10 = zw A -> getr regs 18 = zw len -> 0 <= A < 2 ^ 64 -> 0 <= len <= 65536 ->
  let st1 := cset_adler (ds_strm s) A in
  let st2 := cset_next_in st1 (cs_next_in (ds_strm s) + len) in
  let st3 := cset_total_in st2 (wrap64 (cs_total_in (ds_strm s) + len)) in
  exists R m', msteps s6_segs (mkst regs (0x1694c : word) m s6_rom) (mkst R (0x16980 : word) m' s6_rom)
    /\ RI m' (set_strm s st3) /\ CSTL (set_strm s st3) /\ LREGS R
    /\ getr R 10 = zw (ds_lookahead s)
    /\ (forall r : reg, reg_in r [10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof using HLFimg ROM_local PV2 HD2 HFW.
  intros regs m s A len HRI HK HL Hni Hnl Hti Hlook H27 H10 H18 HA Hlen st1 st2 st3. open_fw. open_lregs HL. open_cstl HK.
  pose proof HRI as (Hz & _ & _ & _ & _ & _ & _ & MZ & _).
  cellS Hz dsl_lookahead C180. cellZ HRI zsl_next_in ZN. rewrite Z.add_0_r in ZN. cellZ HRI zsl_total_in Z16.
  assert (HRI1 : RI (wbytes m (zw (strm + 96)) (Z_to_le_bytes 8 A)) (set_strm s st1)).
  { eapply RI_updZ; [exact HRI | exact HK | | reflexivity | in_LF | lia | unfold zsl_SIZE; cbn; lia].
    apply zsl_upd_adler; [exact (proj1 (proj2 (proj2 (proj2 (proj2 Hz))))) | lia | unfold zsl_SIZE; lia]. }
  assert (HK1 : CSTL (set_strm s st1)) by (unfold FillWin6A.CSTL in *; dsred; exact HK).
  assert (HRI2 : RI (wbytes (wbytes m (zw (strm + 96)) (Z_to_le_bytes 8 A)) (zw strm)
                    (Z_to_le_bytes 8 (INP + cs_next_in (ds_strm s) + len))) (set_strm s st2)).
  { replace (zw strm) with (zw (strm + 0)) by (f_equal; lia).
    replace (INP + cs_next_in (ds_strm s) + len) with (INP + (cs_next_in (ds_strm s) + len)) by lia.
    change (set_strm s st2) with (set_strm (set_strm s st1) st2).
    eapply RI_updZ; [exact HRI1 | exact HK1 | | reflexivity | in_LF | lia | unfold zsl_SIZE; cbn; lia].
    apply zsl_upd_next_in; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HRI1)))))) | lia | unfold zsl_SIZE; lia]. }
  assert (HK2 : CSTL (set_strm s st2)) by (unfold FillWin6A.CSTL in *; dsred; exact HK).
  trim. apart 1%nat 5%nat.
  run 15%nat NoDirs [RVal (EAdd (EVar 38) (EVar 42)); RVal (EVar 43); RVal (EVar 44)]
      [(27, EVar 37); (10, EVar 45); (18, EVar 41)]
      [(41%nat, 65537); (42%nat, 2 ^ 63); (43%nat, 2 ^ 64); (44%nat, 2 ^ 31); (45%nat, 2 ^ 64)]
      [len; cs_next_in (ds_strm s); cs_total_in (ds_strm s); ds_lookahead s; A]
      (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  eexists R, _. split; [exact Hms|].
  split.
  { rewrite (Z_to_le_bytes_eqm 8 (cs_total_in (ds_strm s) + len) (wrap64 (cs_total_in (ds_strm s) + len)))
      by (rewrite wrap64_mod; change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); rewrite Z.mod_mod by lia; reflexivity).
    change (set_strm s st3) with (set_strm (set_strm s st2) st3).
    eapply RI_updZ; [exact HRI2 | exact HK2 | | reflexivity | in_LF | lia | unfold zsl_SIZE; cbn; lia].
    apply zsl_upd_total_in; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HRI2)))))) | lia | unfold zsl_SIZE; lia]. }
  split; [unfold FillWin6A.CSTL in *; dsred; exact HK|].
  split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  symex_reg HR (10%bv : reg) as B10. split; [exact B10|]. fr_weak Hfr.
Qed.



Definition rb_clob : list reg := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 28; 29; 30; 31]%bv.

Lemma rb_run : forall regs m s more,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 12 = zw (szwrap 32 (cs_avail_in (ds_strm s))) -> getr regs 18 = zw more ->
  getr regs 27 = zw strm -> getr regs 11 = zw (ds_strstart s) ->
  0 <= more <= 2 * ws - ds_strstart s - ds_lookahead s -> cs_avail_in (ds_strm s) <> 0 ->
  let r := read_buf s (RB_window (ds_strstart s + ds_lookahead s)) more in
  exists R m', msteps s6_segs (mkst regs (0x168e4 : word) m s6_rom) (mkst R (0x16980 : word) m' s6_rom)
    /\ RI m' (fst r) /\ CSTL (fst r) /\ LREGS R
    /\ getr R 9 = zw (snd r) /\ getr R 10 = zw (ds_lookahead s) /\ getr R 27 = zw strm
    /\ (forall x : reg, reg_in x rb_clob = false -> getr R x = getr regs x).
Proof using HLFimg ADLER MEMCPY ROM_local PV2 HD2 Hwrap1 HFW.
  intros regs m s more HRI HW HK HL H12 H18 H27 H11 Hmore Hai r. open_fw. open_wf HW. open_cstl HK.
  destruct (rb1 regs m s more HRI HW HK HL H12 H18 H27 H11 ltac:(lia) Hai) as (R1 & Hrb1).
  subst r. unfold read_buf. cbv beta iota zeta.
  set (ai := cs_avail_in (ds_strm s)) in *. set (len := if more <? ai then more else ai) in *.
  assert (Hlen : 0 <= len <= ai /\ len <= more) by (subst len; destruct (Z.ltb_spec more ai); lia).
  assert (Elen : len = (if more <? ai then more else ai)) by reflexivity.
  assert (Eai : ai = cs_avail_in (ds_strm s)) by reflexivity.
  clearbody len ai.
  destruct Hrb1 as [(L0 & Hms1 & HL1 & A9 & A10 & A27 & Hfr1) | (Lp & Hms1 & HL1 & A1 & A10 & A11 & A12 & A9 & A18 & A19 & A27 & Hfr1)].
  -
    rewrite L0. cbn [Z.eqb fst snd].
    exists R1, m. split; [exact Hms1|]. split; [exact HRI|]. split; [exact HK|]. split; [exact HL1|].
    split; [exact A9|]. split; [exact A10|]. split; [exact A27|]. fr_weak Hfr1.
  - replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    set (m1 := wbytes m (zw (strm + 8)) (Z_to_le_bytes 4 (ai - len))) in *.
    assert (HRIa : RI m1 (set_strm s (cset_avail_in (ds_strm s) (ai - len)))).
    { subst m1. eapply RI_updZ; [exact HRI | exact HK | | reflexivity | in_LF | lia | unfold zsl_SIZE; cbn; lia].
      apply zsl_upd_avail_in; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HRI)))))) | lia | unfold zsl_SIZE; lia]. }
    assert (HKa : CSTL (set_strm s (cset_avail_in (ds_strm s) (ai - len)))) by (unfold FillWin6A.CSTL in *; dsred; exact HK).
    assert (HWa : fw_wf ws hs (set_strm s (cset_avail_in (ds_strm s) (ai - len)))).
    { destruct HW; constructor; dsred; try assumption; subst ai; lia. }
    destruct (rb_copy R1 m1 (set_strm s (cset_avail_in (ds_strm s) (ai - len))) len HRIa HWa HKa HL1 A1
                ltac:(dsred; exact A10) ltac:(dsred; exact A11) A12 ltac:(lia)
                ltac:(subst ai; dsred; lia) ltac:(subst ai; dsred; lia))
      as (R2 & Hms2 & HRI2 & HK2 & HL2 & B10 & Hfr2 & Hrd2 & HbZ & Hlen2).
    revert Hms2 HRI2 HK2 Hrd2 HbZ Hlen2. dsred. intros Hms2 HRI2 HK2 Hrd2 HbZ Hlen2.
    set (bs := fbytes (arr_get (cs_input (ds_strm s))) (cs_next_in (ds_strm s)) (Z.to_nat len)) in *.
    set (bytes := arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) len) in *.
    set (w' := arr_upd (ds_window s) (ds_strstart s + ds_lookahead s) bytes) in *.
    set (m2 := wbytes m1 (zw (W + (ds_strstart s + ds_lookahead s))) bs) in *.
    set (s2 := set_window (set_strm s (cset_avail_in (ds_strm s) (ai - len))) w') in *.
    pose proof (wf_ad1 _ _ _ HW ltac:(lia)) as Hcan. pose proof Hcan as ((Hc0 & Hc1) & _ & _).
    destruct (rb_ck R2 m2 s2 len (W + (ds_strstart s + ds_lookahead s)) HRI2 HK2 HL2
                ltac:(subst s2; dsred; lia)
                ltac:(rewrite (Hfr2 27%bv eq_refl); exact A27) ltac:(rewrite (Hfr2 9%bv eq_refl); exact A9)
                ltac:(rewrite (Hfr2 19%bv eq_refl); exact A19) ltac:(lia) ltac:(lia))
      as (R3 & Hms3 & HL3 & C27 & C9 & C19 & C1 & C10 & C11 & C12 & Hfr3).
    replace (cs_adler (ds_strm s2)) with (cs_adler (ds_strm s)) in C10 by (subst s2; dsred; reflexivity).
    destruct (rb_adler R3 m2 s2 (W + (ds_strstart s + ds_lookahead s)) bs (cs_adler (ds_strm s)) HRI2 HK2 HL3
                ltac:(rewrite Hlen2; exact Hrd2) ltac:(lia) ltac:(rewrite Hlen2; lia) ltac:(rewrite Hlen2; lia)
                Hcan C1 C10 C11 ltac:(rewrite Hlen2, Z2Nat.id by lia; exact C12))
      as (R4 & m4 & Hms4 & HRI4 & HL4 & D10 & Hfr4).
    rewrite HbZ in D10.
    pose proof (adler32_model_canon (cs_adler (ds_strm s)) bytes) as ((Hn0 & Hn1) & _ & _).
    destruct (rb_st R4 m4 s2 (adler32_upd (cs_adler (ds_strm s)) bytes) len HRI4 HK2 HL4
                ltac:(subst s2; dsred; lia) ltac:(subst s2 ai; dsred; lia) ltac:(subst s2; dsred; lia) ltac:(subst s2; dsred; lia)
                ltac:(rewrite (Hfr4 27%bv eq_refl); exact C27) D10
                ltac:(rewrite (Hfr4 18%bv eq_refl), (Hfr3 18%bv eq_refl), (Hfr2 18%bv eq_refl); exact A18)
                ltac:(unfold adler32_upd; lia) ltac:(lia))
      as (R5 & m5 & Hms5 & HRI5 & HK5 & HL5 & E10 & Hfr5).
    exists R5, m5.
    split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
      eapply msteps_trans; [exact Hms3|]. eapply msteps_trans; [exact Hms4 | exact Hms5]. }
    cbn [fst snd]. subst s2 w' bytes ai. revert HRI5 HK5. dsred. rewrite Kwr, Hwrap1. cbn [Z.eqb Pos.eqb].
    dsred. intros HRI5 HK5.
    split; [exact HRI5|]. split; [exact HK5|].
    split; [exact HL5|].
    split; [rewrite (Hfr5 9%bv eq_refl), (Hfr4 9%bv eq_refl); exact C9|].
    split; [rewrite E10; dsred; reflexivity|].
    split; [rewrite (Hfr5 27%bv eq_refl), (Hfr4 27%bv eq_refl); exact C27|].
    intros x Hx. rewrite (Hfr5 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    rewrite (Hfr4 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    rewrite (Hfr3 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    rewrite (Hfr2 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    apply Hfr1. eapply reg_in_sub; [|exact Hx]; reflexivity.
Qed.

End Walk.
End FXG.

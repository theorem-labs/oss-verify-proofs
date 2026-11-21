(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux MemFill DSLayout ZSLayout FillWinMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState DeflateLz ZChkAdl LmatchModel AdlerModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u Callee6u FillWin6uA.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Local Abbreviation zstR := (zst s6u_segs 180992 181024 181056).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

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
Local Abbreviation zst_keep_S := (FillWin6uA.zst_keep_S mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation zst_keep_W := (FillWin6uA.zst_keep_W mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation zst_keep_PV := (FillWin6uA.zst_keep_PV mem S sp p zp ds ra regs0 ROM HFW PV2).
Local Abbreviation zst_keep_HD := (FillWin6uA.zst_keep_HD mem S sp p zp ds ra regs0 ROM HFW HD2).
Local Abbreviation zst_keep_Z := (FillWin6uA.zst_keep_Z mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation zst_keep_IN := (FillWin6uA.zst_keep_IN mem S sp p zp ds ra regs0 ROM HFW).
Local Abbreviation CSTL_set_window := (FillWin6uA.CSTL_set_window ds).
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

Local Ltac runx fuel dirs rds pins vbx pvx F1 :=
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


Lemma ns_run : forall regs m s,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  exists R, msteps s6u_segs (mkst regs (0x16b68 : word) m s6u_rom)
              (mkst R (if cs_avail_in (ds_strm s) =? 0 then (0x16d1c : word) else (0x16b80 : word)) m s6u_rom)
    /\ LREGS R /\ getr R 10 = zw strm /\ getr R 12 = zw (szwrap 32 (cs_avail_in (ds_strm s)))
    /\ (forall r : reg, reg_in r [10; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s HRI HW HK HL. open_fw. open_wf HW. open_lregs HL.
  pose proof HRI as (Hz & _). cellS Hz dsl_strm C0. rewrite Z.add_0_r in C0. cellZ HRI zsl_avail_in Z8.
  pose proof (szwrap32_u64_zero (cs_avail_in (ds_strm s)) ltac:(lia)) as Hsw.
  open_ub HUB. trim.
  destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [E0|N0].
  - run 10%nat [false; false; true] [RVal (EVar 37); RVal (EVar 41)] NoPins [(41%nat, 2 ^ 32)]
        [cs_avail_in (ds_strm s)] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
    all: try solve [apply (proj2 Hsw); exact E0].
    exists R. split; [exact Hms|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
    symex_reg HR (10%bv : reg) as A10. symex_reg HR (12%bv : reg) as A12.
    split; [exact A10|]. split; [exact A12|]. fr_weak Hfr.
  - run 10%nat [false; false; false] [RVal (EVar 37); RVal (EVar 41)] NoPins [(41%nat, 2 ^ 32)]
        [cs_avail_in (ds_strm s)] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
    all: try solve [intros E; apply N0; apply (proj1 Hsw); exact E].
    exists R. split; [exact Hms|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
    symex_reg HR (10%bv : reg) as A10. symex_reg HR (12%bv : reg) as A12.
    split; [exact A10|]. split; [exact A12|]. fr_weak Hfr.
Qed.


Lemma rb_call : forall regs m s more,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 10 = zw strm -> getr regs 11 = zw (ds_strstart s) -> getr regs 9 = zw more -> 0 <= more <= 65536 ->
  exists R, msteps s6u_segs (mkst regs (0x16b80 : word) m s6u_rom) (mkst R (0x19458 : word) m s6u_rom)
    /\ LREGS R /\ getr R 10 = zw strm /\ getr R 11 = zw (W + (ds_strstart s + ds_lookahead s))
    /\ getr R 12 = zw more /\ getr R 1 = zw 0x16bc4 /\ getr R 9 = zw more
    /\ (forall r : reg, reg_in r [1; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s more HRI HW HK HL H10 H11 H9 Hmore. open_fw. open_wf HW. open_lregs HL.
  pose proof HRI as (Hz & _). cellS Hz dsl_window C96. cellS Hz dsl_lookahead C180. trim.
  run 20%nat [false; false; false; false] [RVal (EVar 34); RVal (EVar 43)]
      [(10, EVar 37); (11, EVar 41); (9, EVar 42)] [(41%nat, 65537); (42%nat, 65537); (43%nat, 65537)]
      [ds_strstart s; more; ds_lookahead s] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  exists R. split; [exact Hms|]. split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11. symex_reg HR (12%bv : reg) as A12.
  symex_reg HR (1%bv : reg) as A1. symex_reg HR (9%bv : reg) as A9.
  split; [exact A10|]. split; [rewrite A11; rewrite ?Z.mod_small by lia; f_equal; lia|]. split; [exact A12|].
  split; [exact A1|]. split; [exact A9|]. fr_weak Hfr.
Qed.


Definition rb_layout : list (Z * nat) := [(8, 8%nat); (16, 8%nat); (24, 8%nat); (32, 8%nat); (40, 8%nat)].
Definition rb_vals (more : Z) : list Z := [ws; S + 5932; more; S; 0x16bc4].
Definition RBF (more : Z) (m : word -> option byte) : Prop := fields s6u_segs m (sp - 144) rb_layout (rb_vals more).
(* 1.4 UBSan: read_buf's 48-byte frame sits under fill_window's 96-byte one (1.3.1: under 80) *)

Lemma rb_layout_within : layout_within rb_layout 48 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma RBF_keep : forall more m m' G,
  RBF more m -> agree_out G m m' -> disj_franges G (sp - 144) 48 -> RBF more m'.
Proof.
  intros more m m' G HF Hag Hd. open_fw. unfold RBF in *.
  eapply (fields_agree_out s6u_segs G); [exact HF | exact rb_layout_within | exact Hag | exact Hd | lia | lia].
Qed.

Definition RBREGS (regs : bvmap 5 word) (buf len : Z) : Prop :=
  getr regs 8 = zw strm /\ getr regs 2 = zw (sp - 144) /\ getr regs 19 = zw buf /\ getr regs 9 = zw len
  /\ getr regs 20 = zw 3 /\ getr regs 21 = zw 32 /\ getr regs 22 = zw 2 /\ getr regs 23 = zw 261
  /\ getr regs 24 = zw (ws + -262) /\ getr regs 25 = zw 1.

Lemma RBREGS_via : forall regs R buf len (l : list reg),
  RBREGS regs buf len -> (forall r : reg, reg_in r l = false -> getr R r = getr regs r) ->
  forallb (fun r : reg => negb (reg_in r l)) [8; 2; 19; 9; 20; 21; 22; 23; 24; 25]%bv = true ->
  RBREGS R buf len.
Proof.
  intros regs R buf len l (A8 & A2 & A19 & A9 & A20 & A21 & A22 & A23 & A24 & A25) Hfr Hl.
  cbn [forallb] in Hl. rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in Hl.
  destruct Hl as (X8 & X2 & X19 & X9 & X20 & X21 & X22 & X23 & X24 & X25 & _).
  unfold RBREGS. rewrite !Hfr by assumption.
  repeat split; assumption.
Qed.

Local Ltac open_rbregs H :=
  let H' := fresh "HQ'" in pose proof H as H';
  destruct H' as (Q8 & Q2 & Q19 & Q9 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25).

Lemma RI_below : forall m m' s,
  RI m s -> CSTL s -> agree_out [(sp - 272, 176)] m m' -> (forall x, m x <> None -> m' x <> None) -> RI m' s.
Proof.
  intros m m' s HRI HK Hag Hgr. open_fw.
  apart 0%nat 1%nat. apart 0%nat 2%nat. apart 0%nat 3%nat. apart 0%nat 4%nat. apart 0%nat 5%nat. apart 0%nat 6%nat.
  pose proof HK as (_ & _ & _ & Kin & _). pose proof (f_equal (@arr_len Z) Kin) as KIL. cbn beta in KIL.
  eapply (RI_transport m m' s s [(sp - 272, 176)] HRI HK Hag); try assumption.
  - intros x Hx. cbn in Hx. unfold FillWin6uA.LF. cbn [in_franges]. left. lia.
  - intros; exact I.
  - apply (zst_keep_S m _ s _ HRI Hag). apply disj_franges_cons; [unfold dsl_SIZE; lia | apply disj_franges_nil].
  - apply (zst_keep_W m _ s _ HRI HK Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_PV m _ s _ HRI HK Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_HD m _ s _ HRI HK Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_Z m _ s _ HRI Hag). apply disj_franges_cons; [unfold zsl_SIZE; lia | apply disj_franges_nil].
  - apply (zst_keep_IN m _ s _ HRI HK Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply disj_franges_cons; [lia | apply disj_franges_nil].
Qed.

Local Ltac cell_tower :=
  first [ apply cell_write_same; lia
        | apply cell_write_other; [cell_tower | lia | lia | lia | rewrite length_Z_to_le_bytes; lia | rewrite length_Z_to_le_bytes; lia] ].
Local Ltac cell_tower_at :=
  match goal with
  | |- cell _ ?m ?a ?w ?v =>
      match m with context [wbytes _ (zw ?b) _] => replace a with b by lia end
  end; cell_tower.


Definition rb_clob1 : list reg := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition rb_clob2 : list reg := [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 28; 29; 30; 31]%bv.

Lemma rb1 : forall regs m s more,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 10 = zw strm -> getr regs 11 = zw (W + (ds_strstart s + ds_lookahead s)) -> getr regs 12 = zw more ->
  getr regs 1 = zw 0x16bc4 -> getr regs 9 = zw more ->
  0 <= more <= 65536 -> cs_avail_in (ds_strm s) <> 0 ->
  let ai := cs_avail_in (ds_strm s) in
  let len := (if more <? ai then more else ai) in
  exists R m',
    (len = 0 /\ msteps s6u_segs (mkst regs (0x19458 : word) m s6u_rom) (mkst R (0x16bc4 : word) m' s6u_rom)
     /\ RI m' s /\ LREGS R /\ getr R 10 = zw 0 /\ getr R 9 = zw more
     /\ (forall r : reg, reg_in r rb_clob1 = false -> getr R r = getr regs r))
    \/ (0 < len /\ msteps s6u_segs (mkst regs (0x19458 : word) m s6u_rom) (mkst R (0x2a824 : word) m' s6u_rom)
     /\ RI m' (set_strm s (cset_avail_in (ds_strm s) (ai - len))) /\ RBF more m'
     /\ RBREGS R (W + (ds_strstart s + ds_lookahead s)) len /\ getr R 18 = zw len
     /\ getr R 1 = zw 0x194b8 /\ getr R 10 = zw (W + (ds_strstart s + ds_lookahead s))
     /\ getr R 11 = zw (INP + cs_next_in (ds_strm s)) /\ getr R 12 = zw len
     /\ (forall r : reg, reg_in r rb_clob2 = false -> getr R r = getr regs r)).
Proof.
  intros regs m s more HRI HW HK HL H10 H11 H12 H1 H9 Hmore Hai ai len. open_fw. open_wf HW. open_lregs HL. open_cstl HK.
  pose proof HRI as (Hz & _ & MF & _ & _ & _ & _ & MZ & _).
  cellZ HRI zsl_avail_in Z8. cellZ HRI zsl_next_in ZN. rewrite Z.add_0_r in ZN.
  pose proof (szwrap32_u64 (cs_avail_in (ds_strm s)) ltac:(lia)) as Hu.
  open_ub HUB.
  apart 0%nat 5%nat.
  subst ai len. trim.
  destruct (Z_lt_le_dec (cs_avail_in (ds_strm s)) more) as [Blt|Bge].
  2: {
    replace (if more <? cs_avail_in (ds_strm s) then more else cs_avail_in (ds_strm s)) with more
      by (destruct (Z.ltb_spec more (cs_avail_in (ds_strm s))); lia).
    destruct (Z.eq_dec more 0) as [M0|M0].
    + run 40%nat [false; false; false; true] [RVal (EVar 41)]
        [(10, EVar 37); (11, EVar 43); (12, EVar 42); (9, EVar 42); (1, ELit 0x16bc4)]
        [(41%nat, 2 ^ 32); (42%nat, 65537); (43%nat, 2 ^ 63 + 2 ^ 17); (44%nat, 2 ^ 63)]
        [cs_avail_in (ds_strm s); more; W + (ds_strstart s + ds_lookahead s); cs_next_in (ds_strm s)]
        (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
      all: try solve [rewrite Hu; destruct (Z.ltb_spec (cs_avail_in (ds_strm s)) (2 ^ 31)); lia].
      eexists R, _. left. split; [lia|]. split; [exact Hms|].
      split.
      { lazymatch type of Hms with msteps _ _ (mkst _ _ ?m1 _) =>
          assert (Hag : agree_out [(sp - 272, 176)] m m1)
            by (repeat (apply agree_out_wbytes; [ | lia | rewrite length_Z_to_le_bytes; lia
                                               | apply sub_franges_here; rewrite ?length_Z_to_le_bytes; lia]);
                apply agree_out_refl);
          apply (RI_below m m1 s HRI HK Hag); intros x Hx; repeat apply wbytes_grows; exact Hx end. }
      symex_reg HR (8%bv : reg) as A8. symex_reg HR (2%bv : reg) as A2. symex_reg HR (18%bv : reg) as A18.
      symex_reg HR (19%bv : reg) as A19. symex_reg HR (10%bv : reg) as A10. symex_reg HR (9%bv : reg) as A9.
      split.
      { unfold FillWin6uA.LREGS. split; [exact A8|]. split; [rewrite A2; f_equal; lia|]. split; [rewrite A18; f_equal; lia|].
        split; [rewrite A19; rewrite ?Z.mod_small by lia; f_equal; lia|].
        rewrite (Hfr 20%bv eq_refl), (Hfr 21%bv eq_refl), (Hfr 22%bv eq_refl), (Hfr 23%bv eq_refl), (Hfr 24%bv eq_refl), (Hfr 25%bv eq_refl).
        repeat split; assumption. }
      split; [rewrite A10; f_equal; lia|]. split; [rewrite A9; f_equal; lia|]. fr_weak Hfr.
    + run 40%nat [false; false; false; false] [RVal (EVar 41); RVal (EAdd (EVar 38) (EVar 44))]
        [(10, EVar 37); (11, EVar 43); (12, EVar 42); (9, EVar 42); (1, ELit 0x16bc4)]
        [(41%nat, 2 ^ 32); (42%nat, 65537); (43%nat, 2 ^ 63 + 2 ^ 17); (44%nat, 2 ^ 63)]
        [cs_avail_in (ds_strm s); more; W + (ds_strstart s + ds_lookahead s); cs_next_in (ds_strm s)]
        (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
      all: try solve [rewrite Hu; destruct (Z.ltb_spec (cs_avail_in (ds_strm s)) (2 ^ 31)); lia].
      lazymatch type of Hms with context [Z_to_le_bytes 4 ?e] =>
        rewrite (Z_to_le_bytes_eqm 4 e (cs_avail_in (ds_strm s) - more)) in Hms
          by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); rewrite ?szwrap_eqm by lia;
              rewrite ?szwrap32_small by lia; first [reflexivity | f_equal; lia]) end.
      eexists R, _. right. split; [lia|]. split; [exact Hms|].
      lazymatch type of Hms with msteps _ _ (mkst _ _ (wbytes ?m1 _ _) _) =>
        assert (Hag : agree_out [(sp - 272, 176)] m m1)
          by (repeat (apply agree_out_wbytes; [ | lia | rewrite length_Z_to_le_bytes; lia
                                             | apply sub_franges_here; rewrite ?length_Z_to_le_bytes; lia]);
              apply agree_out_refl);
        pose proof (RI_below m m1 s HRI HK Hag ltac:(intros x Hx; repeat apply wbytes_grows; exact Hx)) as HRI1
      end.
      split.
      { eapply RI_updZ; [exact HRI1 | exact HK | | reflexivity | in_LF | lia | unfold zsl_SIZE; cbn; lia].
        apply zsl_upd_avail_in; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HRI1)))))) | lia | unfold zsl_SIZE; lia]. }
      split.
      { unfold RBF, rb_layout, rb_vals.
        eapply fields_write_other; [ | exact rb_layout_within | lia | lia | lia | rewrite length_Z_to_le_bytes; lia
                                   | rewrite length_Z_to_le_bytes; lia ].
        cbn [fields]. repeat match goal with |- _ /\ _ => split end; try exact I; cell_tower_at. }
      symex_reg HR (8%bv : reg) as A8. symex_reg HR (2%bv : reg) as A2. symex_reg HR (19%bv : reg) as A19.
      symex_reg HR (9%bv : reg) as A9. symex_reg HR (18%bv : reg) as A18. symex_reg HR (1%bv : reg) as A1.
      symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11. symex_reg HR (12%bv : reg) as A12.
      split.
      { unfold RBREGS. split; [exact A8|]. split; [rewrite A2; f_equal; lia|]. split; [exact A19|]. split; [exact A9|].
        rewrite (Hfr 20%bv eq_refl), (Hfr 21%bv eq_refl), (Hfr 22%bv eq_refl), (Hfr 23%bv eq_refl), (Hfr 24%bv eq_refl), (Hfr 25%bv eq_refl).
        repeat split; assumption. }
      split; [rewrite A18; rewrite ?Z.mod_small by lia; f_equal; lia|]. split; [exact A1|]. split; [exact A10|].
      split; [exact A11|]. split; [rewrite A12; rewrite ?Z.mod_small by lia; f_equal; lia|]. fr_weak Hfr. }
  -
    replace (if more <? cs_avail_in (ds_strm s) then more else cs_avail_in (ds_strm s)) with (cs_avail_in (ds_strm s))
      by (destruct (Z.ltb_spec more (cs_avail_in (ds_strm s))); lia).
    run 40%nat [false; false; true; false] [RVal (EVar 41); RVal (EAdd (EVar 38) (EVar 44))]
        [(10, EVar 37); (11, EVar 43); (12, EVar 42); (9, EVar 42); (1, ELit 0x16bc4)]
        [(41%nat, 2 ^ 32); (42%nat, 65537); (43%nat, 2 ^ 63 + 2 ^ 17); (44%nat, 2 ^ 63)]
        [cs_avail_in (ds_strm s); more; W + (ds_strstart s + ds_lookahead s); cs_next_in (ds_strm s)]
        (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
    all: try solve [rewrite Hu; destruct (Z.ltb_spec (cs_avail_in (ds_strm s)) (2 ^ 31)); lia].
    lazymatch type of Hms with context [Z_to_le_bytes 4 ?e] =>
      rewrite (Z_to_le_bytes_eqm 4 e (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm s))) in Hms
        by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); rewrite ?szwrap_eqm by lia;
            rewrite ?szwrap32_small by lia; first [reflexivity | f_equal; lia]) end.
    eexists R, _. right. split; [lia|]. split; [exact Hms|].
    lazymatch type of Hms with msteps _ _ (mkst _ _ (wbytes ?m1 _ _) _) =>
      assert (Hag : agree_out [(sp - 272, 176)] m m1)
        by (repeat (apply agree_out_wbytes; [ | lia | rewrite length_Z_to_le_bytes; lia
                                           | apply sub_franges_here; rewrite ?length_Z_to_le_bytes; lia]);
            apply agree_out_refl);
      pose proof (RI_below m m1 s HRI HK Hag ltac:(intros x Hx; repeat apply wbytes_grows; exact Hx)) as HRI1
    end.
    split.
    { eapply RI_updZ; [exact HRI1 | exact HK | | reflexivity | in_LF | lia | unfold zsl_SIZE; cbn; lia].
      apply zsl_upd_avail_in; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HRI1)))))) | lia | unfold zsl_SIZE; lia]. }
    split.
    { unfold RBF, rb_layout, rb_vals.
      eapply fields_write_other; [ | exact rb_layout_within | lia | lia | lia | rewrite length_Z_to_le_bytes; lia
                                 | rewrite length_Z_to_le_bytes; lia ].
      cbn [fields]. repeat match goal with |- _ /\ _ => split end; try exact I; cell_tower_at. }
    symex_reg HR (8%bv : reg) as A8. symex_reg HR (2%bv : reg) as A2. symex_reg HR (19%bv : reg) as A19.
    symex_reg HR (9%bv : reg) as A9. symex_reg HR (18%bv : reg) as A18. symex_reg HR (1%bv : reg) as A1.
    symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11. symex_reg HR (12%bv : reg) as A12.
    rewrite ?szwrap32_small in A9 by lia.
    split.
    { unfold RBREGS. split; [exact A8|]. split; [rewrite A2; f_equal; lia|]. split; [exact A19|].
      split; [exact A9|].
      rewrite (Hfr 20%bv eq_refl), (Hfr 21%bv eq_refl), (Hfr 22%bv eq_refl), (Hfr 23%bv eq_refl), (Hfr 24%bv eq_refl), (Hfr 25%bv eq_refl).
      repeat split; assumption. }
    split; [rewrite A18; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; f_equal; lia|]. split; [exact A1|]. split; [exact A10|].
    split; [exact A11|]. split; [rewrite A12; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; f_equal; lia|]. fr_weak Hfr.
Qed.


Lemma rb_copy : forall regs m s len more,
  RI m s -> fw_wf ws hs s -> CSTL s -> RBREGS regs (W + (ds_strstart s + ds_lookahead s)) len -> RBF more m ->
  getr regs 1 = zw 0x194b8 -> getr regs 10 = zw (W + (ds_strstart s + ds_lookahead s)) ->
  getr regs 11 = zw (INP + cs_next_in (ds_strm s)) -> getr regs 12 = zw len ->
  0 < len -> cs_next_in (ds_strm s) + len <= arr_len (cs_input (ds_strm s)) ->
  len <= 2 * ws - ds_strstart s - ds_lookahead s ->
  let off := ds_strstart s + ds_lookahead s in
  let bytes := arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) len in
  let bs := fbytes (arr_get (cs_input (ds_strm s))) (cs_next_in (ds_strm s)) (Z.to_nat len) in
  let w' := arr_upd (ds_window s) off bytes in
  exists R, msteps s6u_segs (mkst regs (0x2a824 : word) m s6u_rom)
                             (mkst R (0x194b8 : word) (wbytes m (zw (W + off)) bs) s6u_rom)
    /\ RI (wbytes m (zw (W + off)) bs) (set_window s w') /\ CSTL (set_window s w')
    /\ RBREGS R (W + (ds_strstart s + ds_lookahead s)) len /\ RBF more (wbytes m (zw (W + off)) bs)
    /\ (forall r : reg, reg_in r memcpy_clob = false -> getr R r = getr regs r)
    /\ rdn s6u_segs (wbytes m (zw (W + off)) bs) (zw (W + off)) (Z.to_nat len) = Some bs
    /\ bZ bs = bytes /\ length bs = Z.to_nat len.
Proof.
  intros regs m s len more HRI HW HK HQ HBF H1 H10 H11 H12 Hlen0 Hlen1 Hlen2 off bytes bs w'. open_fw. open_wf HW. open_cstl HK.
  pose proof HRI as (Hz & _ & _ & _ & MW & _). destruct Hz as (_ & Hwin & _ & _ & _ & Hin).
  unfold dsl_windowA in Hwin. rewrite Kwl in Hwin. unfold zsl_input in Hin.
  assert (Hrd : rdn s6u_segs m (zw (INP + cs_next_in (ds_strm s))) (Z.to_nat len) = Some bs).
  { subst bs. apply (cells_rdn s6u_segs m INP (arr_len (cs_input (ds_strm s)))); try lia. exact Hin. }
  assert (Hlen : length bs = Z.to_nat len) by (subst bs; apply fbytes_length).
  apart 2%nat 6%nat. apart 0%nat 2%nat.
  destruct (MEMCPY m regs (W + off) (INP + cs_next_in (ds_strm s)) (Z.to_nat len) bs (zw 0x194b8) Hrd
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
  assert (Hagc : agree_out [(W + off, off + len - off)] m (wbytes m (zw (W + off)) bs)).
  { replace (off + len - off) with (Z.of_nat (length bs)) by lia. apply memcpy_agree_out; lia. }
  split.
  { eapply (RI_updW m _ s w' off (off + len) HRI HK).
    - exact Hagc.
    - intros x Hx. apply wbytes_grows. exact Hx.
    - lia. - lia. - lia.
    - exact Hl'.
    - pose proof (cells_wbytes_bytes s6u_segs m W (2 * ws) (arr_get (ds_window s)) off bs Hwin
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hc.
      refine (cells_ext _ _ _ _ _ _ _ _ _ Hc). intros i Hi. cbn beta. subst w' bytes.
      rewrite (arr_get_upd _ _ _ _ 0). unfold arr_inb. rewrite Kwl, Hlen, arr_slice_length.
      destruct (Z.leb_spec off i), (Z.ltb_spec i (off + Z.of_nat (Z.to_nat len))), (Z.ltb_spec i (off + Z.max 0 len)),
        (Z.leb_spec 0 i), (Z.ltb_spec i (2 * ws)); cbn [andb]; try reflexivity; try lia.
      subst bs. rewrite fbytes_nth by (try lia; exact Hib).
      unfold arr_slice. rewrite arr_slice_nat_nth by lia. all: try (f_equal; lia). }
  split; [apply CSTL_set_window; [exact HK | exact Hl']|].
  split; [eapply RBREGS_via; [exact HQ | exact Hfr | reflexivity]|].
  split.
  { apply (RBF_keep more m _ _ HBF Hagc). apply disj_franges_cons; [lia | apply disj_franges_nil]. }
  split; [exact Hfr|].
  split.
  { rewrite <- Hlen. apply rdn_wbytes_hit. rewrite u_zw_small by lia. lia. }
  split; [|exact Hlen].
  subst bs bytes. unfold arr_slice. apply bZ_fbytes_slice. exact Hib.
Qed.


Lemma rb_ck : forall regs m s len dst,
  RI m s -> CSTL s -> RBREGS regs dst len ->
  0 <= cs_adler (ds_strm s) < 2 ^ 64 ->
  0 <= len <= 65536 -> 0 <= dst < 2 ^ 63 + 2 ^ 17 ->
  exists R, msteps s6u_segs (mkst regs (0x194b8 : word) m s6u_rom) (mkst R (0x1af3c : word) m s6u_rom)
    /\ RBREGS R dst len
    /\ getr R 1 = zw 0x194ec /\ getr R 10 = zw (cs_adler (ds_strm s)) /\ getr R 11 = zw dst /\ getr R 12 = zw len
    /\ (forall r : reg, reg_in r [1; 10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s len dst HRI HK HQ Had Hlen Hdst. open_fw. open_rbregs HQ. open_cstl HK. open_ub HUB.
  pose proof HRI as (Hz & _). cellS Hz dsl_wrap C48. cellZ HRI zsl_state Z56. cellZ HRI zsl_adler Z96.
  rewrite Kwr, Hwrap1 in C48. trim.
  runx 20%nat [false; false; false; false] [RVal (EVar 32); RVal (ELit 1); RVal (EVar 44)]
      [(8, EVar 37); (2, EAdd (EVar 33) (ELit (-48))); (19, EVar 43); (9, EVar 42);
       (20, ELit 3); (21, ELit 32); (22, ELit 2); (23, ELit 261); (24, EAdd (EVar 39) (ELit (-262)))]
      [(42%nat, 65537); (43%nat, 2 ^ 63 + 2 ^ 17); (44%nat, 2 ^ 64)]
      [0; len; dst; cs_adler (ds_strm s)] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  all: try solve [rewrite Q2; f_equal; lia].
  exists R. split; [exact Hms|]. split; [eapply RBREGS_via; [exact HQ | exact Hfr | reflexivity]|].
  symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11.
  symex_reg HR (12%bv : reg) as A12.
  split; [exact A1|]. split; [exact A10|]. split; [exact A11|]. split; [exact A12|]. fr_weak Hfr.
Qed.


Lemma rb_adler : forall regs m s P (d : list byte) adler len more,
  RI m s -> CSTL s -> RBREGS regs P len -> RBF more m ->
  rdn s6u_segs m (zw P) (length d) = Some d -> W <= P -> P + Z.of_nat (length d) <= W + 2 * ws ->
  Z.of_nat (length d) <= 65536 -> adler_canon adler ->
  getr regs 1 = zw 0x194ec -> getr regs 10 = zw adler -> getr regs 11 = zw P ->
  getr regs 12 = zw (Z.of_nat (length d)) ->
  exists R m', msteps s6u_segs (mkst regs (0x1af3c : word) m s6u_rom) (mkst R (0x194ec : word) m' s6u_rom)
    /\ RI m' s /\ RBREGS R P len /\ RBF more m' /\ getr R 10 = zw (adler32_upd adler (bZ d))
    /\ (forall r : reg, reg_in r c_clob = false -> getr R r = getr regs r).
Proof.
  intros regs m s P d adler len more HRI HK HQ HBF Hrd HP HPl Hdl Hcan H1 H10 H11 H12. open_fw. open_rbregs HQ.
  pose proof Hcan as ((Ha0 & Ha1) & _ & _).
  pose proof HRI as (_ & _ & MF & _ & _ & _ & _ & _ & _ & _ & HROMm).
  apart 0%nat 2%nat.
  destruct (ADLER m regs adler P d (sp - 144) (zw 0x194ec) Hrd
              ltac:(lia) Hcan ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold ADLER_FR6U; lia) ltac:(lia)
              ltac:(unfold ADLER_FR6U; eapply mapped_sub; [exact MF | lia | lia])
              ltac:(unfold ADLER_FR6U; lia)
              HROMm ltac:(apply ret_ok_zw; [lia | reflexivity])
              H1 Q2 H10 H11 H12)
    as (R & m' & Hms & A10 & A2 & Hfr & Hag & Hgr).
  symex_pc_lit_in Hms.
  exists R, m'. split; [exact Hms|].
  unfold ADLER_FR6U in Hag. replace (sp - 144 - 128) with (sp - 272) in Hag by lia.
  split.
  { apply (RI_below m m' s HRI HK); [|exact Hgr].
    eapply agree_out_weaken; [exact Hag|]. intros x Hx. cbn in Hx |- *. lia. }
  split; [eapply RBREGS_via; [exact HQ | exact Hfr | reflexivity]|].
  split.
  { apply (RBF_keep more m m' _ HBF Hag). apply disj_franges_cons; [lia | apply disj_franges_nil]. }
  split.
  { change (reg_get R 10 = zw (adler32_upd adler (bZ d))). rewrite A10. unfold adler32_upd.
    rewrite (adler32_z_spec_canon adler P d Hcan) by lia. reflexivity. }
  exact Hfr.
Qed.


Lemma rb_st : forall regs m s A len more,
  RI m s -> CSTL s -> RBREGS regs (W + (ds_strstart s + ds_lookahead s)) len -> RBF more m ->
  0 <= cs_next_in (ds_strm s) -> cs_next_in (ds_strm s) + len <= arr_len (cs_input (ds_strm s)) ->
  0 <= cs_total_in (ds_strm s) < 2 ^ 64 ->
  getr regs 10 = zw A -> getr regs 18 = zw len -> 0 <= A < 2 ^ 64 -> 0 <= len <= 65536 -> 0 <= more <= 65536 ->
  let st1 := cset_adler (ds_strm s) A in
  let st2 := cset_next_in st1 (cs_next_in (ds_strm s) + len) in
  let st3 := cset_total_in st2 (wrap64 (cs_total_in (ds_strm s) + len)) in
  exists R m', msteps s6u_segs (mkst regs (0x194ec : word) m s6u_rom) (mkst R (0x16bc4 : word) m' s6u_rom)
    /\ RI m' (set_strm s st3) /\ CSTL (set_strm s st3) /\ LREGS R
    /\ getr R 10 = zw len /\ getr R 9 = zw more
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10; 11; 18; 19]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s A len more HRI HK HQ HBF Hni Hnl Hti H10 H18 HA Hlen Hmore st1 st2 st3.
  open_fw. open_rbregs HQ. open_cstl HK. open_ub HUB.
  pose proof HRI as (Hz & _ & MF & _ & _ & _ & _ & MZ & _).
  cellZ HRI zsl_next_in ZN. rewrite Z.add_0_r in ZN. cellZ HRI zsl_total_in Z16.
  unfold RBF, rb_layout, rb_vals in HBF.
  pose proof (fields_nth s6u_segs m (sp - 144) _ _ 0 8 8%nat _ HBF eq_refl eq_refl) as F8.
  pose proof (fields_nth s6u_segs m (sp - 144) _ _ 1 16 8%nat _ HBF eq_refl eq_refl) as F16.
  pose proof (fields_nth s6u_segs m (sp - 144) _ _ 2 24 8%nat _ HBF eq_refl eq_refl) as F24.
  pose proof (fields_nth s6u_segs m (sp - 144) _ _ 3 32 8%nat _ HBF eq_refl eq_refl) as F32.
  pose proof (fields_nth s6u_segs m (sp - 144) _ _ 4 40 8%nat _ HBF eq_refl eq_refl) as F40.
  clear HBF. cbn [nth rb_vals] in F8, F16, F24, F32, F40.
  replace (sp - 144 + 8) with (sp - 96 + -40) in F8 by lia.
  replace (sp - 144 + 16) with (sp - 96 + -32) in F16 by lia.
  replace (sp - 144 + 24) with (sp - 96 + -24) in F24 by lia.
  replace (sp - 144 + 32) with (sp - 96 + -16) in F32 by lia.
  replace (sp - 144 + 40) with (sp - 96 + -8) in F40 by lia.
  assert (HRI1 : RI (wbytes m (zw (strm + 96)) (Z_to_le_bytes 8 A)) (set_strm s st1)).
  { eapply RI_updZ; [exact HRI | exact HK | | reflexivity | in_LF | lia | unfold zsl_SIZE; cbn; lia].
    apply zsl_upd_adler; [exact (proj1 (proj2 (proj2 (proj2 (proj2 Hz))))) | lia | unfold zsl_SIZE; lia]. }
  assert (HK1 : CSTL (set_strm s st1)) by (unfold FillWin6uA.CSTL in *; dsred; exact HK).
  assert (HRI2 : RI (wbytes (wbytes m (zw (strm + 96)) (Z_to_le_bytes 8 A)) (zw strm)
                    (Z_to_le_bytes 8 (INP + cs_next_in (ds_strm s) + len))) (set_strm s st2)).
  { replace (zw strm) with (zw (strm + 0)) by (f_equal; lia).
    replace (INP + cs_next_in (ds_strm s) + len) with (INP + (cs_next_in (ds_strm s) + len)) by lia.
    change (set_strm s st2) with (set_strm (set_strm s st1) st2).
    eapply RI_updZ; [exact HRI1 | exact HK1 | | reflexivity | in_LF | lia | unfold zsl_SIZE; cbn; lia].
    apply zsl_upd_next_in; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HRI1)))))) | lia | unfold zsl_SIZE; lia]. }
  assert (HK2 : CSTL (set_strm s st2)) by (unfold FillWin6uA.CSTL in *; dsred; exact HK).
  trim. apart 1%nat 5%nat. apart 0%nat 5%nat.
  runx 30%nat [false; false; false]
      [RVal (EAdd (EVar 38) (EVar 42)); RVal (EVar 43); RVal (ELit 93124); RVal (EVar 32); RVal (EVar 45);
       RVal (EAdd (EVar 32) (ELit 5932)); RVal (EVar 39)]
      [(8, EVar 37); (2, EAdd (EVar 33) (ELit (-48))); (18, EVar 41); (9, EVar 41); (10, EVar 44)]
      [(41%nat, 65537); (42%nat, 2 ^ 63); (43%nat, 2 ^ 64); (44%nat, 2 ^ 64); (45%nat, 65537)]
      [len; cs_next_in (ds_strm s); cs_total_in (ds_strm s); A; more]
      (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  all: try solve [rewrite Q2; f_equal; lia].
  eexists R, _. split; [exact Hms|].
  split.
  { rewrite (Z_to_le_bytes_eqm 8 (cs_total_in (ds_strm s) + len) (wrap64 (cs_total_in (ds_strm s) + len)))
      by (rewrite wrap64_mod; change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); rewrite Z.mod_mod by lia; reflexivity).
    change (set_strm s st3) with (set_strm (set_strm s st2) st3).
    eapply RI_updZ; [exact HRI2 | exact HK2 | | reflexivity | in_LF | lia | unfold zsl_SIZE; cbn; lia].
    apply zsl_upd_total_in; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 HRI2)))))) | lia | unfold zsl_SIZE; lia]. }
  split; [unfold FillWin6uA.CSTL in *; dsred; exact HK|].
  symex_reg HR (8%bv : reg) as A8. symex_reg HR (2%bv : reg) as A2. symex_reg HR (18%bv : reg) as A18.
  symex_reg HR (19%bv : reg) as A19. symex_reg HR (10%bv : reg) as A10. symex_reg HR (9%bv : reg) as A9.
  split.
  { unfold FillWin6uA.LREGS. split; [exact A8|]. split; [rewrite A2; f_equal; lia|]. split; [rewrite A18; f_equal; lia|].
    split; [rewrite A19; rewrite ?Z.mod_small by lia; f_equal; lia|].
    rewrite (Hfr 20%bv eq_refl), (Hfr 21%bv eq_refl), (Hfr 22%bv eq_refl), (Hfr 23%bv eq_refl), (Hfr 24%bv eq_refl), (Hfr 25%bv eq_refl).
    repeat split; assumption. }
  split; [exact A10|]. split; [rewrite A9; f_equal; lia|]. fr_weak Hfr.
Qed.


Definition rb_clob : list reg := [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 28; 29; 30; 31]%bv.

Lemma rb_run : forall regs m s more,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 10 = zw strm -> getr regs 11 = zw (ds_strstart s) -> getr regs 9 = zw more ->
  0 <= more <= 2 * ws - ds_strstart s - ds_lookahead s -> cs_avail_in (ds_strm s) <> 0 ->
  let r := read_buf s (RB_window (ds_strstart s + ds_lookahead s)) more in
  exists R m', msteps s6u_segs (mkst regs (0x16b80 : word) m s6u_rom) (mkst R (0x16bc4 : word) m' s6u_rom)
    /\ RI m' (fst r) /\ CSTL (fst r) /\ LREGS R
    /\ getr R 10 = zw (snd r) /\ getr R 9 = zw more
    /\ (forall x : reg, reg_in x rb_clob = false -> getr R x = getr regs x).
Proof.
  intros regs m s more HRI HW HK HL H10 H11 H9 Hmore Hai r. open_fw. open_wf HW. open_cstl HK.
  destruct (rb_call regs m s more HRI HW HK HL H10 H11 H9 ltac:(lia)) as (R0 & Hms0 & HL0 & Z10 & Z11 & Z12 & Z1 & Z9 & Hfr0).
  destruct (rb1 R0 m s more HRI HW HK HL0 Z10 Z11 Z12 Z1 Z9 ltac:(lia) Hai) as (R1 & m1 & Hrb1).
  subst r. unfold read_buf. cbv beta iota zeta.
  set (ai := cs_avail_in (ds_strm s)) in *. set (len := if more <? ai then more else ai) in *.
  assert (Hlen : 0 <= len <= ai /\ len <= more) by (subst len; destruct (Z.ltb_spec more ai); lia).
  assert (Elen : len = (if more <? ai then more else ai)) by reflexivity.
  assert (Eai : ai = cs_avail_in (ds_strm s)) by reflexivity.
  clearbody len ai.
  destruct Hrb1 as [(L0 & Hms1 & HRI1 & HL1 & A10 & A9 & Hfr1)
                   | (Lp & Hms1 & HRI1 & HBF1 & HQ1 & A18 & A1 & A10 & A11 & A12 & Hfr1)].
  -
    rewrite L0. cbn [Z.eqb fst snd].
    exists R1, m1. split; [eapply msteps_trans; [exact Hms0 | exact Hms1]|]. split; [exact HRI1|]. split; [exact HK|]. split; [exact HL1|].
    split; [exact A10|]. split; [exact A9|].
    intros x Hx. rewrite (Hfr1 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    apply Hfr0. eapply reg_in_sub; [|exact Hx]; reflexivity.
  - replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    set (sa := set_strm s (cset_avail_in (ds_strm s) (ai - len))) in *.
    assert (HKa : CSTL sa) by (subst sa; unfold FillWin6uA.CSTL in *; dsred; exact HK).
    assert (HWa : fw_wf ws hs sa).
    { subst sa. destruct HW; constructor; dsred; try assumption; subst ai; lia. }
    destruct (rb_copy R1 m1 sa len more HRI1 HWa HKa ltac:(subst sa; dsred; exact HQ1) HBF1 A1
                ltac:(subst sa; dsred; exact A10) ltac:(subst sa; dsred; exact A11) A12 ltac:(lia)
                ltac:(subst sa ai; dsred; lia) ltac:(subst sa ai; dsred; lia))
      as (R2 & Hms2 & HRI2 & HK2 & HQ2 & HBF2 & Hfr2 & Hrd2 & HbZ & Hlen2).
    revert Hms2 HRI2 HK2 HQ2 HBF2 Hrd2 HbZ Hlen2. subst sa. dsred. intros Hms2 HRI2 HK2 HQ2 HBF2 Hrd2 HbZ Hlen2.
    set (bs := fbytes (arr_get (cs_input (ds_strm s))) (cs_next_in (ds_strm s)) (Z.to_nat len)) in *.
    set (bytes := arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) len) in *.
    set (w' := arr_upd (ds_window s) (ds_strstart s + ds_lookahead s) bytes) in *.
    set (m2 := wbytes m1 (zw (W + (ds_strstart s + ds_lookahead s))) bs) in *.
    set (s2 := set_window (set_strm s (cset_avail_in (ds_strm s) (ai - len))) w') in *.
    pose proof (wf_ad1 _ _ _ HW ltac:(lia)) as Hcan. pose proof Hcan as ((Hc0 & Hc1) & _ & _).
    destruct (rb_ck R2 m2 s2 len (W + (ds_strstart s + ds_lookahead s)) HRI2 HK2 HQ2
                ltac:(subst s2; dsred; lia) ltac:(lia) ltac:(lia))
      as (R3 & Hms3 & HQ3 & C1 & C10 & C11 & C12 & Hfr3).
    replace (cs_adler (ds_strm s2)) with (cs_adler (ds_strm s)) in C10 by (subst s2; dsred; reflexivity).
    destruct (rb_adler R3 m2 s2 (W + (ds_strstart s + ds_lookahead s)) bs (cs_adler (ds_strm s)) len more HRI2 HK2 HQ3 HBF2
                ltac:(rewrite Hlen2; exact Hrd2) ltac:(lia) ltac:(rewrite Hlen2; lia) ltac:(rewrite Hlen2; lia)
                Hcan C1 C10 C11 ltac:(rewrite Hlen2, Z2Nat.id by lia; exact C12))
      as (R4 & m4 & Hms4 & HRI4 & HQ4 & HBF4 & D10 & Hfr4).
    rewrite HbZ in D10.
    pose proof (adler32_model_canon (cs_adler (ds_strm s)) bytes) as ((Hn0 & Hn1) & _ & _).
    destruct (rb_st R4 m4 s2 (adler32_upd (cs_adler (ds_strm s)) bytes) len more HRI4 HK2
                ltac:(subst s2; dsred; exact HQ4) HBF4
                ltac:(subst s2; dsred; lia) ltac:(subst s2 ai; dsred; lia) ltac:(subst s2; dsred; lia)
                D10 ltac:(rewrite (Hfr4 18%bv eq_refl), (Hfr3 18%bv eq_refl), (Hfr2 18%bv eq_refl); exact A18)
                ltac:(unfold adler32_upd; lia) ltac:(lia) ltac:(lia))
      as (R5 & m5 & Hms5 & HRI5 & HK5 & HL5 & E10 & E9 & Hfr5).
    exists R5, m5.
    split.
    { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
      eapply msteps_trans; [exact Hms3|]. eapply msteps_trans; [exact Hms4 | exact Hms5]. }
    cbn [fst snd]. subst s2 w' bytes ai. revert HRI5 HK5. dsred. rewrite Kwr, Hwrap1. cbn [Z.eqb Pos.eqb].
    dsred. intros HRI5 HK5.
    split; [exact HRI5|]. split; [exact HK5|].
    split; [exact HL5|].
    split; [exact E10|]. split; [exact E9|].
    intros x Hx. rewrite (Hfr5 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    rewrite (Hfr4 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    rewrite (Hfr3 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    rewrite (Hfr2 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    rewrite (Hfr1 x) by (eapply reg_in_sub; [|exact Hx]; reflexivity).
    apply Hfr0. eapply reg_in_sub; [|exact Hx]; reflexivity.
Qed.

End Walk.
End FXG.

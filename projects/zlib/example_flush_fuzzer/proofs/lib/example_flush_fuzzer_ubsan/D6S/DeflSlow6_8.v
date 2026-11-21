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
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 Callee6 TreesRod6 TreesApi6 DeflBlkApi6 FillWin6D DeflSlow6_1 DeflSlow6_2 DeflSlow6_3 DeflSlow6_4 DeflSlow6_5 DeflSlow6_6 DeflSlow6_7.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.





End FXG.
Ltac unhide H := unfold hidden in H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section Walk.
Variable ROM : (word -> option byte) -> Prop.
Variables (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (flush : Z) (ra : word) (sp : Z).
Local Abbreviation W := (p_window p).
Local Abbreviation PV := (p_prev p).
Local Abbreviation HD := (p_head p).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation strm := (p_strm p).
Local Abbreviation INP := (zp_in zp).
Local Abbreviation OUTB := (zp_out zp).
Local Abbreviation ws := (ds_w_size ds).
Local Abbreviation hs := (ds_hash_size ds).
Local Abbreviation lbs := (ds_lit_bufsize ds).
Local Abbreviation PBL := (ds_lit_bufsize ds * 4).
Local Abbreviation SP := (sp - 128).
Hypothesis HH : DSH ROM mem S p zp ds flush ra sp.
Local Abbreviation DI := (DeflSlow6_1.DI ROM mem S p zp ds sp).
Local Abbreviation BRm := (BR s6_segs 168672 168704 168736 (DeflSlow6_1.Fd S p zp ds sp) mem S p PBL).
Local Abbreviation RZ := (DeflSlow6_1.RZ ROM mem S p zp ds sp).

Let HL : ZRH6 DSLOW_FRAME6 mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ HH.
Local Abbreviation HREGS := (DeflSlow6_1.HREGS S sp).
Local Abbreviation DI_eqst := (DeflSlow6_1.DI_eqst ROM mem S p zp ds sp).
Local Abbreviation LOC := (DeflSlow6_2.LOC4 sp).

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac hregs_via HRG Hfr := apply (HREGS_via S sp _ _ _ HRG Hfr); reflexivity.

Local Ltac nf := cbn [dfF].

Local Ltac rod_read :=
  lazymatch goal with
  | |- exists bs, rdn _ ?m (zw ?a) _ = Some bs /\ bytes_le_to_Z bs = arr_get length_code_a ?i =>
      eapply (length_code_read R6 s6_segs m trod_ok6 ltac:(eassumption) i a); first [reflexivity | cbn [tr_length_code R6]; lia]
  | |- exists bs, rdn _ ?m (zw ?a) _ = Some bs /\ bytes_le_to_Z bs = arr_get dist_code_a ?i =>
      eapply (dist_code_read R6 s6_segs m trod_ok6 ltac:(eassumption) i a); first [reflexivity | cbn [tr_dist_code R6]; lia]
  end.

Local Ltac head_read :=
  lazymatch goal with
  | |- exists bs, rdn ?sg ?m (zw ?a) 2 = Some bs /\ bytes_le_to_Z bs = pb ?t ?i =>
      match goal with H : cells sg m ?P 2 2%nat ?len (arr_get t) |- _ =>
        eapply (pb_read2 sg m P len t i a H); [lia | arr_range_auto | lia] end
  end.

Local Ltac side_closer :=
  try solve [ assumption
            | nf; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia);
                          rewrite ?Z.mod_small by lia; lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; head_read
            | nf; symex_read_auto
            | nf; rod_read
            | nf; symex_sok_auto
            | nf; symex_store_auto
            | intros; nf; first [apply pb_range | apply wb_range | apply Z.mod_pos_bound; lia | lia] ].

Local Ltac run_gen base fuel dirs rds pinsx vbx pvx X :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pins := eval vm_compute in (base ++ pinsx) in
  let vb := eval vm_compute in (dfVB ++ vbx) in
  let rdv := eval vm_compute in rds in
  let pv := constr:(S :: SP :: flush :: pvx) in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs DeflSlow6_2.dsC6 fuel dirs rdv pins vb NoRegions pv NoVals
          (dfF (ds_window X) (ds_head X) (ds_dyn_ltree_fc X) (ds_dyn_dtree_fc X)) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Local Ltac run fuel dirs rds pinsx vbx pvx X := run_gen HPINS fuel dirs rds pinsx vbx pvx X.
Local Ltac runT fuel dirs rds pinsx vbx pvx X := run_gen HPINST fuel dirs rds pinsx vbx pvx X.

Local Ltac open_di HDI :=
  let HB := fresh "HB" in let HRZ := fresh "HRZ" in let HS3 := fresh "HS3" in
  pose proof HDI as (HB & HRZ & HS3);
  let Ews := fresh "Ews" in let Ehs := fresh "Ehs" in let Elbs := fresh "Elbs" in
  destruct HS3 as (Ews & Ehs & Elbs);
  let Hsc := fresh "Hsc" in let Har := fresh "Har" in let MS := fresh "MS" in let MP := fresh "MP" in let Hpb := fresh "Hpb" in
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & _ & Hpb & _ & MS & MP & _); unfold mapped, ds6_SIZE, dsl_SIZE in MS, MP;
  unfold dsl_pendA in Hpb;
  let Cw := fresh "Cw" in let Cp := fresh "Cp" in let Ch := fresh "Ch" in let Zs := fresh "Zs" in
  let HRC := fresh "HRC" in let MF := fresh "MF" in let HC := fresh "HC" in
  pose proof HRZ as (Cw & Cp & Ch & Zs & _ & _ & (HRC & _ & _ & MF & _) & HC); unfold mapped in MF;
  let HRT := fresh "HRT" in let HGOT := fresh "HGOT" in pose proof (proj1 HRC) as HRT; pose proof (proj2 HRC) as HGOT; unfold got6_clear in HGOT;
  let Lw := fresh "Lw" in let Lp := fresh "Lp" in let Lh := fresh "Lh" in
  let Ein := fresh "Ein" in let Eout := fresh "Eout" in let Hao := fresh "Hao" in let Hol := fresh "Hol" in
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol); rewrite Lw in Cw; rewrite Lp in Cp; rewrite Lh in Ch;
  let RF := fresh "RF" in
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in let HW := fresh "HW" in let HPV := fresh "HPV" in let HHD := fresh "HHD" in
  let HPB := fresh "HPB" in let Hstrm := fresh "Hstrm" in let HOUT := fresh "HOUT" in let HIN := fresh "HIN" in
  destruct RF as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN);
  let RODS := fresh "RODS" in pose proof (mapped_rod_apart R6 s6_segs _ S 5968 trod_ok6 HRT MS ltac:(lia) ltac:(lia)) as RODS;
  let RODP := fresh "RODP" in pose proof (mapped_rod_apart R6 s6_segs _ (p_pending_buf p) PBL trod_ok6 HRT MP ltac:(lia) ltac:(pose proof (wf_lbs _ HWF); lia)) as RODP;
  cbn [tr_lo tr_hi tr_sdesc R6] in RODS, RODP; apply hide in RODS; apply hide in RODP;
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ HH) as Hfl;
  let HGR := fresh "HGR" in pose proof HRZ as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & HGR) & _);
  let MWm := fresh "MWm" in let MPm := fresh "MPm" in let MHm := fresh "MHm" in let MZm := fresh "MZm" in
  let T := fresh "T" in
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ HH 2 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MWm; cbv beta in MWm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ HH 3 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MPm; cbv beta in MPm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ HH 4 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MHm; cbv beta in MHm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ HH 6 ltac:(lia)) as T; unfold ZRF, zsl_SIZE in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MZm; cbv beta in MZm; clear T.

Local Ltac apartF i j H :=
  pose proof (apart_ij _ _ _ _ _ _ _ _ _ HH i j ltac:(lia) ltac:(lia)) as H;
  unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE, DSLOW_FRAME6 in H.

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P21 := fresh "P21" in let P22 := fresh "P22" in
  let P27 := fresh "P27" in let P20 := fresh "P20" in let P23 := fresh "P23" in let P24 := fresh "P24" in let P26 := fresh "P26" in
  pose proof HRG as (P8 & P2 & P21 & P22 & P27 & P20 & P23 & P24 & P26).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 | rewrite sxaddm16 | rewrite sxaddm8 | rewrite sxm16 ].

Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].

Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac di_fwd_rec HDI M ks :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) ?bs =>
      lazymatch ks with
      | ?k :: ?rest =>
          di_fwd_rec HDI M1 rest;
          lazymatch goal with
          | H1 : DeflSlow6_1.DI _ ?mem ?S ?p ?zp ?ds ?sp ?m1 M1 ?X |- _ =>
              let H2 := fresh "HDI" in
              lazymatch k with
              | KInsH => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_ins_h ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KBlockStart => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_block_start ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KMatchLength => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_match_length ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KStrstart => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_strstart ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KLookahead => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_lookahead ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KInsert => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_insert ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KSymNext => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_sym_next ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPending => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_pending ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPrevLength => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_prev_length ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPrevMatch => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_prev_match ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KMatchAvailable => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_match_available ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPendingOut ?off => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_pending_out ROM mem S p zp ds _ _ sp HH m1 M1 X off a v H1 ltac:(lia) ltac:(lia)) as H2 end
              | KPb ?i ?c' => lazymatch bs with Z_to_le_bytes _ ?c =>
                  pose proof (DI_st_pb ROM mem S p zp ds _ _ sp HH m1 M1 X a i c c' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KFc ?t ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_fc ROM mem S p zp ds _ _ sp HH m1 M1 X a t i v v' H1 ltac:(cbn [toff]; lia) ltac:(cbn [tsize]; lia) ltac:(mod_side)) as H2 end
              | KPrev ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_prev ROM mem S p zp ds _ _ sp HH m1 M1 X a i v v' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KHead ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_head ROM mem S p zp ds _ _ sp HH m1 M1 X a i v v' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KFrame => pose proof (DI_st_frame ROM mem S p zp ds _ _ sp HH m1 M1 X a bs H1 ltac:(lia)
                            ltac:(rewrite ?length_Z_to_le_bytes; lia)) as H2
              end;
              clear H1
          end
      end
  | _ => let H := fresh "HDI" in pose proof HDI as H
  end.
Ltac di_fwd HDI M ks :=
  let ksr := eval cbv beta iota zeta delta [List.rev List.app] in (List.rev ks) in di_fwd_rec HDI M ksr.

Ltac frame_cells :=
  repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                | apply cell_write_other;
                  [ | lia | cbn; lia | lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia ] ]);
  try assumption.

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.

Local Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); assumption end
        | let A := fresh "A" in
          lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf;
            first [ assumption
                  | lazymatch goal with |- ?a = ?a => reflexivity end
                  | f_equal; lia
                  | f_equal; repeat (rewrite (szwrap_small 32) by lia); rewrite ?Z.mod_small by lia; lia
                  | rewrite zw_u; first [assumption | reflexivity]
                  | lazymatch goal with |- zw ?a = _ => lazymatch isZcst a with true => apply bv_eq; vm_compute; reflexivity end end ] end ].


Local Ltac open_min :=
  let RF := fresh "RF" in
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in
  destruct RF as (Hsp & HS & _);
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ HH) as Hfl.

Local Ltac ex1 := lazymatch goal with H : msteps _ _ (mkst ?R _ _ _) |- _ => exists R end.
Local Ltac ex2 := lazymatch goal with H : msteps _ _ (mkst ?R _ ?M _) |- _ => exists R, M end.

Ltac norm_sx H := rewrite ?le_bytes_sx32 in H.


Local Abbreviation PLR := (DeflSlow6_2.PLR).
Local Abbreviation ins_str := (DeflSlow6_2.ins_str).
Local Abbreviation ILS := (DeflSlow6_5.ILS).

Local Abbreviation slit1 := (DeflSlow6_3.slit1).
Local Abbreviation fb_bufp := (DeflSlow6_6.fb_bufp p).
Local Abbreviation fb_len := (DeflSlow6_6.fb_len).
Local Abbreviation FPR := (DeflSlow6_6.FPR S p).
Local Abbreviation fpa_pc := (DeflSlow6_6.fpa_pc).
Local Abbreviation fp_tower := (DeflSlow6_6.fp_tower S p zp).
Local Abbreviation avail_pc := (DeflSlow6_6.avail_pc).

Local Abbreviation TREGS := (DeflSlow6_7.TREGS S sp).
Local Ltac runTT fuel dirs rds pinsx vbx pvx X := run_gen DeflSlow6_7.HPINS_T fuel dirs rds pinsx vbx pvx X.
Local Ltac tregs_via HRG Hfr := apply (DeflSlow6_7.TREGS_via S sp _ _ _ HRG Hfr); reflexivity.
Local Ltac open_tregs HRG := let P8 := fresh "P8" in let P2 := fresh "P2" in let P21 := fresh "P21" in pose proof HRG as (P8 & P2 & P21).


Section TailFP.
  Variables (PCB PCC PCD PCE : Z).
  Hypothesis HP : (PCB = 0x19c0c /\ PCC = 0x19c24 /\ PCD = 0x19c48 /\ PCE = 0x19c90)
                  \/ (PCB = 0x19cd0 /\ PCC = 0x19ce8 /\ PCD = 0x19d0c /\ PCE = 0x19d54).

  Lemma tb_blk : forall regs m1 m X,
    DI m1 m X -> TREGS regs -> 0 <= ds_strstart X <= 2 * ws ->
    exists R M,
      msteps s6_segs (mkst regs (zw PCB) m s6_rom) (mkst R (0x1ad94 : word) M s6_rom)
      /\ DI m1 M (set_block_start X (ds_strstart X))
      /\ TREGS R /\ FPR 19%bv 9%bv R /\ getr R 10 = zw S /\ getr R 1 = zw PCC /\ getr R 2 = zw SP
      /\ (forall r : reg, reg_in r [1; 9; 10; 19]%bv = false -> getr R r = getr regs r).
  Proof using HP PCE PCD HWF HH ra flush.
    intros regs m1 m X HDI HRG Hstr. open_di HDI. open_tregs HRG. pose proof (wf_wsz _ HWF) as Wws.
    pose proof (ds6_strm _ _ _ _ Hsc) as C0. replace (S + 0) with S in C0 by lia.
    pose proof (ds6_strstart _ _ _ _ Hsc) as C172. pose proof (zsl_state s6_segs _ _ _ _ _ Zs) as Z56.
    apartF 1%nat 6%nat A16.
    Local Ltac tb_fin R Hms HDI HRG HR Hfr :=
      clear_aparts; rewrite ?dfF_0, ?dfF_1, ?dfF_2, ?dfF_3 in Hms;
      di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KBlockStart];
      lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end;
      split; [exact Hms|];
      split; [lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => exact H end|];
      split; [tregs_via HRG Hfr|]; unfold DeflSlow6_6.FPR; repeat split; reg1 HR Hfr.
    destruct HP as [(-> & -> & _ & _)|(-> & -> & _ & _)]; symex_pc_lit.
    - runTT 20%nat NoDirs [RVal (EVar 35); RVal (EVar 36); RVal (EVar 32)] NoPins [(35%nat, 2 ^ 63); (36%nat, 65537)] [strm; ds_strstart X] X.
      tb_fin R Hms HDI HRG HR Hfr.
    - runTT 20%nat NoDirs [RVal (EVar 35); RVal (EVar 36); RVal (EVar 32)] NoPins [(35%nat, 2 ^ 63); (36%nat, 65537)] [strm; ds_strstart X] X.
      tb_fin R Hms HDI HRG HR Hfr.
  Qed.

  Lemma tc_blk : forall regs m1 m X,
    DI m1 m X -> TREGS regs -> FPR 19%bv 9%bv regs ->
    0 <= ds_pending X < 2 ^ 31 -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32 -> 0 <= ds_pending_out X <= PBL ->
    exists R,
      msteps s6_segs (mkst regs (zw PCC) m s6_rom) (mkst R (fpa_pc X (zw PCE) (0x27800 : word)) m s6_rom)
      /\ TREGS R /\ FPR 19%bv 9%bv R
      /\ (fp_len X <> 0 ->
          getr R 10 = zw (OUTB + Z.of_nat (length (cs_out_rev (ds_strm X)))) /\ getr R 11 = zw (PB + ds_pending_out X)
          /\ getr R 12 = zw (fp_len X) /\ getr R 18 = zw (fp_len X) /\ getr R 18 = zw (fp_len X) /\ getr R 1 = zw PCD /\ getr R 2 = zw SP)
      /\ (forall r : reg, reg_in r [1; 10; 11; 12; 18]%bv = false -> getr R r = getr regs r).
  Proof using HP PCB HWF HH ra flush.
    intros regs m1 m X HDI HRG (F19 & F9) Hpd Hav Hpo. open_di HDI. open_tregs HRG.
    pose proof (wf_lbs _ HWF) as Wlbs.
    pose proof (ds6_pending _ _ _ _ Hsc) as C40. pose proof (ds6_pending_out _ _ _ _ Hsc) as C32.
    pose proof (cell_low4 _ _ _ _ C40 ltac:(lia) ltac:(lia)) as C40l.
    pose proof (zsl_avail_out s6_segs _ _ _ _ _ Zs) as Z32. pose proof (zsl_next_out s6_segs _ _ _ _ _ Zs) as Z24.
    destruct (DeflSlow6_6.fp_len_eq X ltac:(lia) ltac:(lia)) as (Efl & Hfl1 & Hfl2).
    unfold DeflSlow6_6.fpa_pc.
    Local Ltac tc_fin R Hms HRG HR Hfr :=
      exists R; split; [cbv iota; symex_pc_lit; exact Hms|]; split; [tregs_via HRG Hfr|];
      split; [unfold DeflSlow6_6.FPR; split; reg1 HR Hfr|];
      split; [first [intros Hc; exfalso; lia | intros _; repeat split; reg1 HR Hfr] | fr_weak Hfr].
    Local Ltac tc_run dirs X :=
      runTT 30%nat dirs [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
          [(19, EVar 35%nat); (9, EVar 32%nat)]
          [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31); (37%nat, 2 ^ 32); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
          [strm; ds_pending X; cs_avail_out (ds_strm X); zp_out zp + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X] X.
    destruct HP as [(_ & -> & -> & ->)|(_ & -> & -> & ->)]; symex_pc_lit.
    -
      destruct (Z.ltb_spec (ds_pending X) (cs_avail_out (ds_strm X))) as [Hlt|Hge].
      + replace (fp_len X) with (ds_pending X) by (rewrite Efl; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia).
        destruct (Z.eqb_spec (ds_pending X) 0) as [Hz|Hnz].
        * tc_run [true; true] X. tc_fin R Hms HRG HR Hfr.
        * tc_run [true; false] X. tc_fin R Hms HRG HR Hfr.
      + replace (fp_len X) with (cs_avail_out (ds_strm X)) by (rewrite Efl; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia).
        destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
        * tc_run [false; true] X. tc_fin R Hms HRG HR Hfr.
        * tc_run [false; false] X. tc_fin R Hms HRG HR Hfr.
    -
      destruct (Z.ltb_spec (ds_pending X) (cs_avail_out (ds_strm X))) as [Hlt|Hge].
      + replace (fp_len X) with (ds_pending X) by (rewrite Efl; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia).
        destruct (Z.eqb_spec (ds_pending X) 0) as [Hz|Hnz].
        * tc_run [true; true] X. tc_fin R Hms HRG HR Hfr.
        * tc_run [true; false] X. tc_fin R Hms HRG HR Hfr.
      + replace (fp_len X) with (cs_avail_out (ds_strm X)) by (rewrite Efl; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia).
        destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
        * tc_run [false; true] X. tc_fin R Hms HRG HR Hfr.
        * tc_run [false; false] X. tc_fin R Hms HRG HR Hfr.
  Qed.

  Lemma td_blk : forall regs m1 M0 X len,
    DI m1 M0 X -> TREGS regs -> FPR 19%bv 9%bv regs -> getr regs 18 = zw len -> getr regs 18 = zw len ->
    0 < len <= ds_pending X -> ds_pending X < 2 ^ 31 -> len <= cs_avail_out (ds_strm X) < 2 ^ 32 ->
    0 <= ds_pending_out X -> ds_pending_out X + len <= PBL -> 0 <= cs_total_out (ds_strm X) < 2 ^ 64 ->
    exists R,
      msteps s6_segs (mkst regs (zw PCD) M0 s6_rom) (mkst R (zw PCE) (fp_tower M0 X len) s6_rom)
      /\ TREGS R /\ FPR 19%bv 9%bv R
      /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14]%bv = false -> getr R r = getr regs r).
  Proof using HP PCC PCB HWF HH ra flush.
    intros regs m1 M0 X len HDI HRG (F19 & F9) Q18 Q20 Hlen Hpd Hav Hpo0 Hpo1 Htot. open_di HDI. open_tregs HRG.
    pose proof (wf_lbs _ HWF) as Wlbs.
    pose proof (ds6_pending _ _ _ _ Hsc) as C40. pose proof (ds6_pending_out _ _ _ _ Hsc) as C32. pose proof (ds6_pending_buf _ _ _ _ Hsc) as C16.
    pose proof (zsl_avail_out s6_segs _ _ _ _ _ Zs) as Z32. pose proof (zsl_next_out s6_segs _ _ _ _ _ Zs) as Z24.
    pose proof (zsl_total_out s6_segs _ _ _ _ _ Zs) as Z40.
    apartF 1%nat 6%nat A16.
    unfold DeflSlow6_6.fp_tower.
    Local Ltac td_fin R Hms HRG HR Hfr :=
      rewrite ?le_bytes_sx32 in Hms;
      exists R; split; [exact Hms|]; split; [tregs_via HRG Hfr|]; split; [unfold DeflSlow6_6.FPR; split; reg1 HR Hfr | fr_weak Hfr].
    Local Ltac td_run dirs len X :=
      runTT 30%nat dirs [RVal (EVar 37); RVal (EVar 39); RVal (EVar 40); RVal (EVar 38); RVal (EVar 41); RVal (EVar 42)]
        [(19, EVar 35%nat); (9, EVar 32%nat); (18, EVar 36%nat)]
        [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 32); (40%nat, 2 ^ 64); (41%nat, 2 ^ 31); (42%nat, 2 ^ 63)]
        [strm; len; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X; cs_avail_out (ds_strm X); cs_total_out (ds_strm X); ds_pending X; PB] X.
    destruct HP as [(_ & _ & -> & ->)|(_ & _ & -> & ->)]; symex_pc_lit.
    - destruct (Z.eqb_spec (ds_pending X - len) 0) as [Hz|Hnz].
      + td_run [false] len X. td_fin R Hms HRG HR Hfr.
      + td_run [true] len X. td_fin R Hms HRG HR Hfr.
    - destruct (Z.eqb_spec (ds_pending X - len) 0) as [Hz|Hnz].
      + td_run [false] len X. td_fin R Hms HRG HR Hfr.
      + td_run [true] len X. td_fin R Hms HRG HR Hfr.
  Qed.
End TailFP.

Lemma fbte_blk : forall regs m1 m X,
  DI m1 m X -> TREGS regs -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32 ->
  0 <= ds_pending X < 2 ^ 31 -> (cs_avail_out (ds_strm X) = 0 -> ds_pending X <> 0 \/ 0 < ds_wrap X < 2 ^ 31) ->
  exists R,
    msteps s6_segs (mkst regs (0x19c90 : word) m s6_rom) (mkst R (0x19d64 : word) m s6_rom)
    /\ TREGS R /\ getr R 10 = zw (if cs_avail_out (ds_strm X) =? 0 then 2 else 3)
    /\ (forall r : reg, reg_in r [10; 11]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Hav Hpd Hpw. open_di HDI. open_tregs HRG.
  pose proof (ds6_strm _ _ _ _ Hsc) as C0. replace (S + 0) with S in C0 by lia. pose proof (zsl_avail_out s6_segs _ _ _ _ _ Zs) as Z32.
  pose proof (ds6_pending _ _ _ _ Hsc) as C40. pose proof (ds6_wrap _ _ _ _ Hsc) as C48.
  destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
  - change (if true then 2 else 3) with 2. rewrite Hz in Z32. destruct (Hpw Hz) as [Hp|Hw].
    + runTT 12%nat [true; true] [RVal (EVar 35); RVal (ELit 0); RVal (EVar 36)] NoPins [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31)] [strm; ds_pending X] X.
      exists R. split; [exact Hms|]. split; [tregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
    + destruct (Z.eq_dec (ds_pending X) 0) as [Hp0|Hp0].
      * rewrite Hp0 in C40. pose proof (sx32_u64_nz (ds_wrap X) ltac:(lia)) as Hsxw.
        runTT 12%nat [true; false; true] [RVal (EVar 35); RVal (ELit 0); RVal (ELit 0); RVal (EVar 36)] NoPins [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31)] [strm; ds_wrap X] X.
        exists R. split; [exact Hms|]. split; [tregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
      * runTT 12%nat [true; true] [RVal (EVar 35); RVal (ELit 0); RVal (EVar 36)] NoPins [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31)] [strm; ds_pending X] X.
        exists R. split; [exact Hms|]. split; [tregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - change (if false then 2 else 3) with 3.
    pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
    runTT 8%nat [false] [RVal (EVar 35); RVal (EVar 36)] NoPins [(35%nat, 2 ^ 63); (36%nat, 2 ^ 32)] [strm; cs_avail_out (ds_strm X)] X.
    exists R. split; [exact Hms|]. split; [tregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma fine_blk : forall regs m1 m X,
  DI m1 m X -> TREGS regs -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32 ->
  exists R,
    msteps s6_segs (mkst regs (0x19d54 : word) m s6_rom) (mkst R (avail_pc X (0x19d64 : word) (0x19d60 : word)) m s6_rom)
    /\ TREGS R /\ (cs_avail_out (ds_strm X) = 0 -> getr R 10 = zw 0)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Hav. open_di HDI. open_tregs HRG.
  pose proof (ds6_strm _ _ _ _ Hsc) as C0. replace (S + 0) with S in C0 by lia. pose proof (zsl_avail_out s6_segs _ _ _ _ _ Zs) as Z32.
  unfold DeflSlow6_6.avail_pc. destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
  - rewrite Hz in Z32.
    runTT 8%nat [true] [RVal (EVar 35); RVal (ELit 0)] NoPins [(35%nat, 2 ^ 63)] [strm] X.
    exists R. split; [exact Hms|]. split; [tregs_via HRG Hfr|]. split; [intros _; reg1 HR Hfr | fr_weak Hfr].
  - pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
    runTT 8%nat [false] [RVal (EVar 35); RVal (EVar 36)] NoPins [(35%nat, 2 ^ 63); (36%nat, 2 ^ 32)] [strm; cs_avail_out (ds_strm X)] X.
    exists R. split; [exact Hms|]. split; [tregs_via HRG Hfr|]. split; [intros Hc; exfalso; lia | fr_weak Hfr].
Qed.


Definition FRM (m : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  cell s6_segs m (SP + 120) 8 (bv_unsigned (getr regs0 1))
  /\ cell s6_segs m (SP + 112) 8 (bv_unsigned (getr regs0 8))
  /\ cell s6_segs m (SP + 104) 8 (bv_unsigned (getr regs0 9))
  /\ cell s6_segs m (SP + 96) 8 (bv_unsigned (getr regs0 18))
  /\ cell s6_segs m (SP + 88) 8 (bv_unsigned (getr regs0 19))
  /\ cell s6_segs m (SP + 80) 8 (bv_unsigned (getr regs0 20))
  /\ cell s6_segs m (SP + 72) 8 (bv_unsigned (getr regs0 21))
  /\ cell s6_segs m (SP + 64) 8 (bv_unsigned (getr regs0 22))
  /\ cell s6_segs m (SP + 56) 8 (bv_unsigned (getr regs0 23))
  /\ cell s6_segs m (SP + 48) 8 (bv_unsigned (getr regs0 24))
  /\ cell s6_segs m (SP + 40) 8 (bv_unsigned (getr regs0 25))
  /\ cell s6_segs m (SP + 32) 8 (bv_unsigned (getr regs0 26))
  /\ cell s6_segs m (SP + 24) 8 (bv_unsigned (getr regs0 27)).

Lemma FRM_keep : forall m1 m X regs0, DI m1 m X -> FRM m1 regs0 -> FRM m regs0.
Proof using HH ra flush.
  intros m1 m X regs0 HDI (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27). unfold FRM.
  repeat split; (eapply (top_keep _ _ _ _ _ _ _ _ _ HH); [exact HDI | eassumption | lia | cbn; lia]).
Qed.

Ltac di_top HDI M :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) ?bs =>
      di_top HDI M1;
      lazymatch goal with
      | H1 : DeflSlow6_1.DI _ _ _ _ _ _ _ M1 M1 ?X |- _ =>
          let H2 := fresh "HDT" in
          pose proof (DI_st_top _ _ _ _ _ _ _ _ _ HH M1 X a bs H1 ltac:(lia) ltac:(rewrite ?length_Z_to_le_bytes; cbn; lia)) as H2;
          clear H1
      end
  | _ => let H := fresh "HDT" in pose proof HDI as H
  end.

Local Ltac agree_tower :=
  lazymatch goal with
  | |- agree_out ?F ?m (wbytes ?M (zw ?b) ?bs) =>
      apply agree_out_wbytes;
      [ agree_tower | lia
      | rewrite ?length_Z_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia
      | apply sub_franges_here; rewrite ?length_Z_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia ]
  | |- agree_out ?F ?m ?m => apply agree_out_refl
  end.

Lemma pro_blk : forall regs,
  getr regs 10 = zw S -> getr regs 11 = zw flush -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R M,
    msteps s6_segs (mkst regs (0x19558 : word) mem s6_rom) (mkst R (0x19600 : word) M s6_rom)
    /\ DI M M ds /\ FRM M regs /\ LOC M
    /\ HREGS R /\ getr R 9 = zw flush
    /\ (forall r : reg, reg_in r [2; 8; 9; 10; 11; 12; 13; 20; 21; 22; 23; 24; 26; 27]%bv = false -> getr R r = getr regs r)
    /\ agree_out [(sp - 128, 128)] mem M.
Proof using HWF HH.
  intros regs P10 P11 P2 P1.
  pose proof (DI_init _ _ _ _ _ _ _ _ _ HH) as HDI. open_di HDI.
  pose proof (u64_range (getr regs 1)) as U1. pose proof (u64_range (getr regs 8)) as U8. pose proof (u64_range (getr regs 9)) as U9.
  pose proof (u64_range (getr regs 18)) as U18. pose proof (u64_range (getr regs 19)) as U19. pose proof (u64_range (getr regs 20)) as U20.
  pose proof (u64_range (getr regs 21)) as U21. pose proof (u64_range (getr regs 22)) as U22. pose proof (u64_range (getr regs 23)) as U23.
  pose proof (u64_range (getr regs 24)) as U24. pose proof (u64_range (getr regs 25)) as U25. pose proof (u64_range (getr regs 26)) as U26.
  pose proof (u64_range (getr regs 27)) as U27.
  apartF 0%nat 1%nat A01.
  run_gen ([(10, EVar 32%nat); (11, EVar 34%nat); (2, EAdd (EVar 33%nat) (ELit 128))]) 40%nat NoDirs NoReads NoPins NoBounds (@nil Z) ds.
  clear_aparts. rewrite ?le_bytes_sx32 in Hms.
  lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => di_top HDI M; exists R, M end.
  split; [exact Hms|]. split; [lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => exact H end|].
  split; [unfold FRM; repeat split; frame_cells|].
  split; [unfold DeflSlow6_2.LOC4; repeat split; frame_cells|].
  split; [unfold DeflSlow6_1.HREGS; repeat split; reg1 HR Hfr |]. split; [reg1 HR Hfr|]. split; [fr_weak Hfr|].
  agree_tower.
Qed.

Lemma epi_blk : forall regs (regs0 : bvmap 5 word) m1 m X,
  DI m1 m X -> FRM m regs0 -> getr regs0 1 = ra -> getr regs 2 = zw SP ->
  exists R,
    msteps s6_segs (mkst regs (0x19d64 : word) m s6_rom) (mkst R ra m s6_rom)
    /\ getr R 2 = zw sp /\ getr R 10 = getr regs 10
    /\ (forall r : reg, reg_in r [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = true -> getr R r = getr regs0 r)
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = false -> getr R r = getr regs r).
Proof using HWF HH flush.
  intros regs regs0 m1 m X HDI (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27) P1 P2. open_di HDI.
  pose proof (dsh_ret _ _ _ _ _ _ _ _ _ HH) as Hret. rewrite P1 in C1.
  pose proof (u64_range ra) as U1. pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19. pose proof (u64_range (getr regs0 20)) as U20.
  pose proof (u64_range (getr regs0 21)) as U21. pose proof (u64_range (getr regs0 22)) as U22. pose proof (u64_range (getr regs0 23)) as U23.
  pose proof (u64_range (getr regs0 24)) as U24. pose proof (u64_range (getr regs0 25)) as U25. pose proof (u64_range (getr regs0 26)) as U26.
  pose proof (u64_range (getr regs0 27)) as U27.
  run_gen ([(2, EVar 33%nat)]) 20%nat NoDirs
    [RVal (EVar 35); RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40); RVal (EVar 41); RVal (EVar 42); RVal (EVar 43); RVal (EVar 44);
     RVal (EVar 45); RVal (EVar 46); RVal (EVar 47)]
    NoPins [(35%nat, 2 ^ 64); (36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64); (42%nat, 2 ^ 64);
            (43%nat, 2 ^ 64); (44%nat, 2 ^ 64); (45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64)]
    [bv_unsigned ra; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18); bv_unsigned (getr regs0 19);
     bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 22); bv_unsigned (getr regs0 23); bv_unsigned (getr regs0 24);
     bv_unsigned (getr regs0 25); bv_unsigned (getr regs0 26); bv_unsigned (getr regs0 27)] X.
  exists R. split; [exact Hms|].
  split; [reg1 HR Hfr|]. split; [reg1 HR Hfr|].
  split; [| fr_weak Hfr].
  intros r Hr. apply FillWin6D.reg_in_true_In in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; first [rewrite P1; reg1 HR Hfr | reg1 HR Hfr].
Qed.

End Walk.
End FXG.

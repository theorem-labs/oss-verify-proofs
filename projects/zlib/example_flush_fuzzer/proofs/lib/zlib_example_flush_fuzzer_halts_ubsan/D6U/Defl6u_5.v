(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import DS6 CalleeKits6 DeflSlow6_1 DeflSlow6_2 Defl6Api Defl6_1 Defl6_2 Defl6_3 Defl6_5 Defl6_5b Defl6_6 Defl6_M DeflSlow6_M.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u Callee6u CalleeKits6u TreesRod6u TreesApi6u TrApi6u
  FillWin6uA DeflBlkApi6u DeflKit6u FlushPend6u DeflSlow6u_8 DeflSlow6u_9 Defl6uApi Defl6u_1 Defl6u_2 Defl6u_3 Defl6u_4 Defl6u_4b.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition dsafe6u (SSAFE : deflate_state -> Z -> Prop) (ds : deflate_state) (f : Z) : Prop :=
  dsafe6 SSAFE ds f /\ - 2 ^ 30 <= ds_last_flush ds < 2 ^ 30.
End FXG.
Global Strategy expand [dsafe6u].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

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
Local Abbreviation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Abbreviation AV0 := (cs_avail_out (ds_strm ds)).
Local Abbreviation SP := (sp - 64).
Hypothesis HF : DFH ROM mem S p zp ds flush ra sp.
Let HH : DKH ROM mem S p zp ds flush ra sp DEFL_K6u DEFL_FR6u := dfh_K _ _ _ _ _ _ _ _ _ HF.
Let HP : DPTRS S p zp := dfh_P _ _ _ _ _ _ _ _ _ HF.
Local Abbreviation DI := (DeflKit6u.DI ROM mem S p zp ds sp DEFL_K6u DEFL_FR6u).
Local Abbreviation BRm := (BR s6u_segs 180992 181024 181056 (DeflKit6u.Fd S p zp ds sp DEFL_K6u) mem S p PBL).
Local Abbreviation RZ := (DeflKit6u.RZ ROM mem S p zp ds sp DEFL_K6u DEFL_FR6u).
Local Abbreviation GD := (DeflKit6u.GD S p zp ds sp DEFL_K6u DEFL_FR6u).
Local Abbreviation GDo := (DeflKit6u.GDo S p zp ds sp DEFL_K6u DEFL_FR6u).
Local Abbreviation DI_eqst := (DeflKit6u.DI_eqst ROM mem S p zp ds sp DEFL_K6u DEFL_FR6u).

Let HL : ZRH6u DEFL_K6u mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ _ _ HH.
Let HRL : rom_local6u ROM := dsh_roml _ _ _ _ _ _ _ _ _ _ _ HH.

Hypothesis MEMCPY : memcpy_run6u.
Hypothesis TFBITS : tr_flush_bits_run6u.
Hypothesis ADLN : adler32_null_run6u.
Variable SSAFE : deflate_state -> Z -> Prop.
Hypothesis SLOW : deflate_slow_run6u ROM SSAFE.
Hypothesis MEMSET : memset_run6u.
Hypothesis TSB : tr_stored_block_run6u.

Local Abbreviation HREGS := (Defl6u_1.HREGS S p flush sp).
Local Abbreviation HREGS_via := (Defl6u_1.HREGS_via S p flush sp).
Local Abbreviation HPINS := Defl6u_1.HPINS.
Local Abbreviation dVB := Defl6u_1.dVB.
Local Abbreviation FRM := (Defl6u_1.FRM sp).
Local Abbreviation FRM_keep := (Defl6u_1.FRM_keep ROM mem S p zp ds flush ra sp HF).
Local Abbreviation img_DI := (Defl6u_1.img_DI ROM mem S p zp ds flush ra sp HF).
Local Abbreviation frame_img := (Defl6u_1.frame_img ROM mem S p zp ds flush ra sp HF).
Local Abbreviation DI_st_last_flush := (Defl6u_1.DI_st_last_flush ROM mem S p zp ds flush ra sp HF).
Local Abbreviation DI_st_status := (Defl6u_1.DI_st_status ROM mem S p zp ds flush ra sp HF).
Local Abbreviation DI_st_wrap := (Defl6u_1.DI_st_wrap ROM mem S p zp ds flush ra sp HF).
Local Abbreviation DI_st_adler := (Defl6u_1.DI_st_adler ROM mem S p zp ds flush ra sp HF).
Local Abbreviation cset_adler_io := Defl6u_1.cset_adler_io.
Local Abbreviation mask_cell := Defl6u_1.mask_cell.
Local Abbreviation dstat_live := Defl6u_1.dstat_live.
Local Abbreviation pro_a := (Defl6u_1.pro_a ROM mem S p zp ds flush ra sp HF).
Local Abbreviation le_bytes4_m1 := Defl6u_1.le_bytes4_m1.
Local Abbreviation x64_blk := (Defl6u_1.x64_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation x38_blk := (Defl6u_1.x38_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation xf0c_blk := (Defl6u_1.xf0c_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation reg_in_true_In := Defl6u_1.reg_in_true_In.
Local Abbreviation epi_blk := (Defl6u_1.epi_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation prob_pc := Defl6u_2.prob_pc.
Local Abbreviation prob_blk := (Defl6u_2.prob_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation pend0_blk := (Defl6u_2.pend0_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation fpret_blk := (Defl6u_2.fpret_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation d42_blk := (Defl6u_2.d42_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation d113_blk := (Defl6u_2.d113_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation d666_blk := (Defl6u_2.d666_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation DI_scratch := (Defl6u_3.DI_scratch ROM mem S p zp ds flush ra sp HF).
Local Abbreviation psm_st := Defl6u_3.psm_st.
Local Abbreviation psm_blk := (Defl6u_3.psm_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation init_blk := (Defl6u_3.init_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation hdr2_blk := (Defl6u_3.hdr2_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation call_adl := (Defl6u_3.call_adl ROM mem S p zp ds flush ra sp HF ADLN).
Local Abbreviation hdr_st_eq := Defl6u_3.hdr_st_eq.
Local Abbreviation adl_blk := (Defl6u_3.adl_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation fpret2_blk := (Defl6u_3.fpret2_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation g_blk := (Defl6u_3.g_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation bc74_blk := (Defl6u_4.bc74_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation b84_pc := (Defl6u_4.b84_pc flush).
Local Abbreviation b84_blk := (Defl6u_4.b84_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation call_blk := (Defl6u_4.call_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation call_slowu := (Defl6u_4.call_slowu ROM mem S p zp ds flush ra sp HF SSAFE SLOW).
Local Abbreviation bst_pc := Defl6u_4.bst_pc.
Local Abbreviation bst_blk := (Defl6u_4.bst_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation t30_pc := (Defl6u_4.t30_pc flush).
Local Abbreviation t30_blk := (Defl6u_4.t30_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation t24_blk := (Defl6u_4.t24_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation t30b_blk := (Defl6u_4.t30b_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation t38_blk := (Defl6u_4.t38_blk ROM mem S p zp ds flush ra sp HF).
Local Abbreviation trl_st_equ := Defl6u_4.trl_st_equ.
Local Abbreviation bd_a := (Defl6u_4b.bd_a ROM mem S p zp ds flush ra sp HF).
Local Abbreviation call_tsb := (Defl6u_4b.call_tsb ROM mem S p zp ds flush ra sp HF MEMCPY TSB).
Local Abbreviation bd_b := (Defl6u_4b.bd_b ROM mem S p zp ds flush ra sp HF).
Local Abbreviation call_ms := (Defl6u_4b.call_ms ROM mem S p zp ds flush ra sp HF MEMSET).
Local Abbreviation bd_c := (Defl6u_4b.bd_c ROM mem S p zp ds flush ra sp HF).
Local Abbreviation bd_d0 := (Defl6u_4b.bd_d0 ROM mem S p zp ds flush ra sp HF).
Local Abbreviation bd_d1 := (Defl6u_4b.bd_d1 ROM mem S p zp ds flush ra sp HF).
Local Abbreviation bd_e := (Defl6u_4b.bd_e ROM mem S p zp ds flush ra sp HF).
Local Abbreviation x68_blk := (Defl6u_4b.x68_blk ROM mem S p zp ds flush ra sp HF).
Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac hregs_via HRG Hfr := apply (HREGS_via _ _ _ HRG Hfr); reflexivity.

Local Ltac side_closer :=
  try solve [ assumption
            | first [ lia
                    | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia);
                      rewrite ?Z.mod_small by lia; lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | match goal with H : getr ?rs ?r = ?w |- getr ?rs ?r = ?w => exact H end
            | apply even_plus_shl1; [assumption | lia | lia]
            | change (2 ^ 3) with 8 in *; change (2 ^ 1) with 2 in *; zcond_close
            | symex_read_auto
            | symex_sok_auto
            | symex_store_auto
            | intros; first [apply Z.mod_pos_bound; lia | lia] ].

Local Ltac run_gen pins fuel dirs rds vbx pvx :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vb := eval vm_compute in (dVB ++ vbx) in
  let rdv := eval vm_compute in rds in
  let pv := constr:(S :: SP :: flush :: strm :: pvx) in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs dfCu fuel dirs rdv pinsv vb NoRegions pv NoVals F0 F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.
Local Ltac run fuel dirs rds vbx pvx := run_gen HPINS fuel dirs rds vbx pvx.

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
  pose proof HRZ as (Cw & Cp & Ch & Zs & _ & _ & (HRC & _ & _ & MF & _) & HC); unfold mapped, DEFL_K6u in MF;
  let Lw := fresh "Lw" in let Lp := fresh "Lp" in let Lh := fresh "Lh" in
  let Ein := fresh "Ein" in let Eout := fresh "Eout" in let Hao := fresh "Hao" in let Hol := fresh "Hol" in
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol); rewrite Lw in Cw; rewrite Lp in Cp; rewrite Lh in Ch;
  let RF := fresh "RF" in
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in let HW := fresh "HW" in let HPV := fresh "HPV" in let HHD := fresh "HHD" in
  let HPB := fresh "HPB" in let Hstrm := fresh "Hstrm" in let HOUT := fresh "HOUT" in let HIN := fresh "HIN" in
  destruct RF as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN); unfold DEFL_K6u in Hsp;
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl;
  let HGR := fresh "HGR" in pose proof HRZ as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & HGR) & _);
  let MZm := fresh "MZm" in let MOm := fresh "MOm" in let T := fresh "T" in
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 6 ltac:(lia)) as T; unfold ZRF, zsl_SIZE in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MZm; cbv beta in MZm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 7 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MOm; cbv beta in MOm; clear T;
  let PS := fresh "PS" in let Pstrm := fresh "Pstrm" in let Pin := fresh "Pin" in let Pza := fresh "Pza" in let Pzf := fresh "Pzf" in
  pose proof (dp_S _ _ _ HP) as PS; pose proof (dp_strm _ _ _ HP) as Pstrm; pose proof (dp_in _ _ _ HP) as Pin;
  pose proof (dp_za _ _ _ HP) as Pza; pose proof (dp_zf _ _ _ HP) as Pzf;
  let FRI := fresh "FRI" in pose proof frame_img as FRI;
  let US8 := fresh "US8" in let UST8 := fresh "UST8" in let UPB1 := fresh "UPB1" in let UO := fresh "UO" in
  pose proof (zrh_S8 _ _ _ _ _ _ _ HL) as US8; pose proof (zrh_strm8 _ _ _ _ _ _ _ HL) as UST8;
  pose proof (zrh_PB1 _ _ _ _ _ _ _ HL) as UPB1; pose proof (zrh_O _ _ _ _ _ _ _ HL) as UO;
  unfold DEFL_FR6u in MF, Hsp.

Local Ltac apartF i j H :=
  pose proof (apart_ij _ _ _ _ _ _ _ _ _ _ _ HH i j ltac:(lia) ltac:(lia)) as H;
  unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE, DEFL_K6u in H.

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in
  pose proof HRG as (P8 & P2 & P9 & P18).

Local Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 | rewrite sxaddm16 | rewrite sxaddm8 ].
Local Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].
Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Local Ltac di_fwd_rec HDI M ks :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) ?bs =>
      lazymatch ks with
      | ?k :: ?rest =>
          di_fwd_rec HDI M1 rest;
          lazymatch goal with
          | H1 : DeflKit6u.DI _ ?mem ?S ?p ?zp ?ds ?sp _ _ ?m1 M1 ?X |- _ =>
              let H2 := fresh "HDI" in
              lazymatch k with
              | KLastFlush => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_last_flush m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KStatus => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_status m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KWrap => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_wrap m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPending => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_pending ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPendingOut ?off => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_pending_out ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X off a v H1 ltac:(lia) ltac:(lia)) as H2 end
              | KPb ?i ?c' => lazymatch bs with Z_to_le_bytes _ ?c =>
                  pose proof (DI_st_pb ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a i c c' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KAdler => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_adler m1 M1 X v a H1 ltac:(lia) ltac:(lia)) as H2 end
              | KFrame => pose proof (DI_st_frame ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a bs H1 ltac:(unfold DEFL_K6u; lia)
                            ltac:(rewrite ?length_Z_to_le_bytes; unfold DEFL_FR6u; lia)) as H2
              end;
              clear H1
          end
      end
  | _ => let H := fresh "HDI" in pose proof HDI as H
  end.
Local Ltac di_fwd HDI M ks :=
  let ksr := eval cbv beta iota zeta delta [List.rev List.app] in (List.rev ks) in di_fwd_rec HDI M ksr.

Local Ltac di_top HDI M :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) ?bs =>
      di_top HDI M1;
      lazymatch goal with
      | H1 : DeflKit6u.DI _ _ _ _ _ _ _ _ _ M1 M1 ?X |- _ =>
          let H2 := fresh "HDT" in
          pose proof (DI_st_top _ _ _ _ _ _ _ _ _ _ _ HH M1 X a bs H1 ltac:(unfold DEFL_FR6u; lia) ltac:(rewrite ?length_Z_to_le_bytes; cbn; lia)) as H2;
          clear H1
      end
  | _ => let H := fresh "HDT" in pose proof HDI as H
  end.

Local Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); first [reflexivity | assumption | symmetry; assumption] end
        | let A := fresh "A" in
          lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A;
            first [ assumption
                  | symmetry; assumption
                  | lazymatch goal with |- ?a = ?a => reflexivity end
                  | f_equal; lia
                  | f_equal; repeat (rewrite (szwrap_small 32) by lia); rewrite ?Z.mod_small by lia; lia
                  | rewrite zw_u; first [assumption | reflexivity]
                  | lazymatch goal with |- zw ?a = _ => lazymatch isZcst a with true => apply bv_eq; vm_compute; reflexivity end end ] end ].

Local Ltac di_fwd_ms HDI Hms ks := lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => di_fwd HDI M ks end.
Local Ltac di_top_ms HDI Hms := lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => di_top HDI M end.

Local Ltac ex1 := lazymatch goal with H : msteps _ _ (mkst ?R _ _ _) |- _ => exists R end.
Local Ltac ex2 := lazymatch goal with H : msteps _ _ (mkst ?R _ ?M _) |- _ => exists R, M end.
Local Ltac the_DI := lazymatch goal with H : DeflKit6u.DI _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact H end.

Local Ltac sc_cell Hsc lem C := pose proof (lem _ _ _ _ Hsc) as C.
Local Ltac zs_cell Zs lem C := pose proof (lem s6u_segs _ _ _ _ _ Zs) as C.

Local Ltac frame_cells :=
  repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                | apply cell_write_other;
                  [ | lia | cbn; lia | lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia ] ]);
  try assumption.

Local Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Local Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Local Ltac st_close extra := dsred; st_peel extra.

Local Ltac regback :=
  repeat (first
    [ reflexivity
    | assumption
    | symmetry; assumption
    | lazymatch goal with |- getr ?RA ?r = _ =>
        first [ match goal with H : forall x : reg, reg_in x _ = false -> getr RA x = getr _ x |- _ => rewrite (H r) by reflexivity end
              | match goal with H : forall x : reg, reg_in x _ = true -> getr RA x = getr _ x |- _ => rewrite (H r) by reflexivity end
              | match goal with H : getr RA r = _ |- _ => rewrite H end ]
      end
    | lazymatch goal with |- _ = getr ?RB ?r => match goal with H : getr RB r = _ |- _ => rewrite H end end ]).
Local Ltac reg_frame :=
  let r := fresh "r" in let Hr := fresh "Hr" in let E := fresh "E" in
  intros r Hr; pose proof (CalleeKits6.reg_enum r) as E; unfold CalleeKits6.all_regs in E; cbn [In] in E;
  repeat (destruct E as [<-|E]; [first [discriminate Hr | solve [regback] | solve [unfold getr; cbn; reflexivity]] |]); destruct E.

Local Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Local Ltac open_min :=
  let RF := fresh "RF" in
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in let HW := fresh "HW" in let HPV := fresh "HPV" in let HHD := fresh "HHD" in
  let HPB := fresh "HPB" in let Hstrm := fresh "Hstrm" in let HOUT := fresh "HOUT" in let HIN := fresh "HIN" in
  destruct RF as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN); unfold DEFL_K6u in Hsp;
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl;
  let Pstrm := fresh "Pstrm" in pose proof (dp_strm _ _ _ HP) as Pstrm.


Local Abbreviation bc64_cond := (Defl6_5.bc64_cond flush).
Local Abbreviation bst_st := Defl6_5.bst_st.
Local Abbreviation trl_st := Defl6_6.trl_st.
Local Abbreviation t2_st := Defl6_6.t2_st.


(* 1.4 UBSan: deflate neither uses nor saves s6 (x22), so it is KEPT through the body, not restored *)
Definition KEEP (regs0 R : bvmap 5 word) : Prop :=
  getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\ getr R 23 = getr regs0 23 /\ getr R 24 = getr regs0 24
  /\ getr R 25 = getr regs0 25 /\ getr R 26 = getr regs0 26 /\ getr R 27 = getr regs0 27 /\ getr R 22 = getr regs0 22.

Lemma KEEP_via : forall regs0 R R' L,
  KEEP regs0 R -> (forall r : reg, reg_in r L = false -> getr R' r = getr R r) ->
  forallb (fun r : reg => negb (reg_in r L)) [3; 4; 23; 24; 25; 26; 27; 22]%bv = true -> KEEP regs0 R'.
Proof.
  intros regs0 R R' L (A3 & A4 & A23 & A24 & A25 & A26 & A27 & A22) Hfr Hl.
  cbn [forallb] in Hl. rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in Hl.
  destruct Hl as (X3 & X4 & X23 & X24 & X25 & X26 & X27 & X22 & _).
  unfold KEEP. rewrite !Hfr by assumption. repeat split; assumption.
Qed.

Local Ltac keep_via HK Hfr := apply (KEEP_via _ _ _ _ HK Hfr); reflexivity.

Definition REACH (regs0 R : bvmap 5 word) (pc : word) (M M0 : word -> option byte) (e : deflate_state * Z) : Prop :=
  exists R' M', msteps s6u_segs (mkst R pc M s6u_rom) (mkst R' (0x17eac : word) M' s6u_rom)
    /\ DI M0 M' (fst e) /\ KEEP regs0 R' /\ getr R' 12 = zw (snd e) /\ getr R' 2 = zw SP.

Lemma reach_x64 : forall regs0 R M0 M X,
  DI M0 M X -> HREGS R -> KEEP regs0 R -> REACH regs0 R (0x17ea0 : word) M M0 (set_last_flush X (-1), Z_OK).
Proof.
  intros regs0 R M0 M X HDI HRG HK.
  destruct (x64_blk R M0 M X HDI HRG) as (R' & M' & Hms & HDI' & A2 & A12 & Hfr).
  exists R', M'. split; [exact Hms|]. split; [exact HDI'|]. split; [keep_via HK Hfr|]. split; [exact A12 | exact A2].
Qed.

Lemma reach_x38 : forall regs0 R M0 M X,
  DI M0 M X -> getr R 2 = zw SP -> KEEP regs0 R -> REACH regs0 R (0x17f78 : word) M M0 (X, Z_OK).
Proof.
  intros regs0 R M0 M X HDI P2 HK.
  destruct (x38_blk R M P2) as (R' & Hms & A2 & A12 & Hfr).
  exists R', M. split; [exact Hms|]. split; [exact HDI|]. split; [keep_via HK Hfr|]. split; [exact A12 | exact A2].
Qed.

Lemma reach_xf0c : forall regs0 R M0 M X,
  DI M0 M X -> getr R 2 = zw SP -> KEEP regs0 R -> REACH regs0 R (0x1814c : word) M M0 (X, Z_STREAM_END).
Proof.
  intros regs0 R M0 M X HDI P2 HK.
  destruct (xf0c_blk R M P2) as (R' & Hms & A2 & A12 & Hfr).
  exists R', M. split; [exact Hms|]. split; [exact HDI|]. split; [keep_via HK Hfr|]. split; [exact A12 | exact A2].
Qed.

Local Ltac reach_step Hms :=
  lazymatch goal with H : REACH _ _ _ _ _ _ |- REACH _ _ _ _ _ _ =>
    let R' := fresh "R" in let M' := fresh "M" in let Hms' := fresh "Hms" in
    destruct H as (R' & M' & Hms' & HD' & HK' & A12' & A2');
    exists R', M'; split; [eapply msteps_trans; [exact Hms | exact Hms'] | split; [exact HD' | split; [exact HK' | split; [exact A12' | exact A2']]]]
  end.

Lemma fp_pre_of6 : forall X, fp_pre6 PBL X -> FlushPend6u.fp_pre ds X.
Proof.
  intros X (HBI & Hp1 & Hp31 & Hpo0 & Hpo1 & Hav & Htot). unfold FlushPend6u.fp_pre. cbv zeta.
  pose proof (DeflSlow6_6.fp_len_eq (tr_flush_bits X) ltac:(lia) ltac:(lia)) as (_ & Hfl1 & Hfl2).
  repeat (split; [first [assumption | lia]|]). lia.
Qed.

Lemma psm_st_strm : forall X c1 c2, ds_strm (psm_st X c1 c2) = ds_strm X.
Proof. intros X c1 c2. unfold psm_st. cbv zeta. dsred. reflexivity. Qed.
Lemma psm_st_pending : forall X c1 c2, ds_pending (psm_st X c1 c2) = ds_pending X + 2.
Proof. intros X c1 c2. unfold psm_st. cbv zeta. dsred. reflexivity. Qed.
Lemma psm_st_strstart : forall X c1 c2, ds_strstart (psm_st X c1 c2) = ds_strstart X.
Proof. intros X c1 c2. unfold psm_st. cbv zeta. dsred. reflexivity. Qed.


Lemma b2z_ltb1' : forall q, (if q =? 0 then 1 else 0) = (if q =? 0 then Z_STREAM_END else Z_OK).
Proof. intros q. unfold Z_STREAM_END, Z_OK. destruct (Z.eqb_spec q 0); lia. Qed.

Lemma reach_trailer : forall regs0 R M0 M X,
  dsafe6 SSAFE ds flush -> G7 ds flush ->
  DI M0 M X -> X = X7 ds flush -> HREGS R -> KEEP regs0 R -> getr R 10 = zw strm -> getr R 11 = zw flush ->
  REACH regs0 R (0x17f70 : word) M M0 (live_tail flush X).
Proof.
  intros regs0 R M0 M X HS HG7 HDI EX HRG HK P10 P11. subst X.
  destruct HS as (Hlive & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  destruct (Htl HG7) as (Hw7 & Hp7 & Hp74 & Ha7 & Htr). clear Htl.
  pose proof Hlive as (Hf & _). set (X := X7 ds flush) in *.
  destruct (t30_blk R M0 M X HDI HRG P10 P11 Hw7 Ha7) as (R1 & Hms1 & HRG1 & T1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1.
  unfold live_tail. unfold t30_pc in Hms1.
  destruct (Z.eqb_spec flush 4) as [Ef|Ef].
  - replace (flush =? 4) with true in Hms1 by (symmetry; apply Z.eqb_eq; exact Ef). cbn [negb] in Hms1 |- *.
    destruct (Z.leb_spec (ds_wrap X) 0) as [Hw|Hw].
    + replace (ds_wrap X <=? 0) with true in Hms1 by (symmetry; apply Z.leb_le; exact Hw). cbn [negb] in Hms1.
      pose proof (reach_xf0c regs0 R1 M0 M X HDI (proj1 (proj2 HRG1)) HK1). reach_step Hms1.
    + replace (ds_wrap X <=? 0) with false in Hms1 by (symmetry; apply Z.leb_gt; exact Hw). cbn [negb] in Hms1.
      destruct (Htr Ef Hw) as (Hfp & Hw8 & Hp8 & Hti). unfold X8 in Hw8, Hp8. fold X in Hw8, Hp8.
      destruct (T1 Ef Hw) as (A10 & A11 & A1).
      set (a := cs_adler (ds_strm X)) in *.
      destruct (psm_blk R1 M0 M X (a / 2 ^ 16) (a / 2 ^ 24) (a / 2 ^ 16) (0x18164%bv : word) HDI HRG1 A10 A11 A1
                  ltac:(apply ret_ok_even; reflexivity)
                  ltac:(split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]) ltac:(lia) ltac:(lia)
                  ltac:(apply byte3_of_hi16; lia) ltac:(reflexivity)) as (R2 & M2 & Hms2 & HDI2 & HRG2 & Hfr2).
      assert (HK2 : KEEP regs0 R2) by keep_via HK1 Hfr2.
      destruct (t24_blk R2 M0 M2 (psm_st X (a / 2 ^ 24) (a / 2 ^ 16)) HDI2 HRG2 ltac:(rewrite psm_st_strm; lia))
        as (R3 & Hms3 & HRG3 & C10 & C11 & C1 & Hfr3).
      assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
      rewrite psm_st_strm in C11. fold a in C11.
      destruct (psm_blk R3 M0 M2 (psm_st X (a / 2 ^ 24) (a / 2 ^ 16)) (a mod 2 ^ 16) (a / 2 ^ 8) a (0x18170%bv : word) HDI2 HRG3 C10 C11 C1
                  ltac:(apply ret_ok_even; reflexivity)
                  ltac:(pose proof (Z.mod_pos_bound a (2 ^ 16) ltac:(lia)); lia) ltac:(rewrite psm_st_pending; lia) ltac:(rewrite psm_st_pending; lia)
                  ltac:(apply byte1_of_low16; lia) ltac:(apply byte0_of_low16)) as (R4 & M4 & Hms4 & HDI4 & HRG4 & Hfr4).
      assert (HK4 : KEEP regs0 R4) by keep_via HK3 Hfr4.
      subst a. rewrite (trl_st_equ X) in HDI4.
      destruct (t30b_blk R4 M4 HRG4) as (R5 & Hms5 & HRG5 & D10 & D1 & Hfr5).
      assert (HK5 : KEEP regs0 R5) by keep_via HK4 Hfr5.
      destruct (FlushPend6u.call_fp ROM mem S p zp ds flush ra sp DEFL_K6u DEFL_FR6u HH ltac:(unfold DEFL_K6u, DEFL_FR6u; lia)
                  ltac:(unfold DEFL_FR6u; lia) MEMCPY TFBITS R5 M0 M4 (trl_st X) (0x18178%bv : word) HDI4 D10 (proj1 (proj2 HRG5)) D1
                  ltac:(apply ret_ok_even; reflexivity) (fp_pre_of6 _ Hfp)) as (R6 & M6 & Hms6 & HDI6 & E2 & E1 & Hfr6).
      assert (HRG6 : HREGS R6) by hregs_via HRG5 Hfr6.
      assert (HK6 : KEEP regs0 R6) by keep_via HK5 Hfr6.
      destruct (t38_blk R6 M0 M6 (flush_pending (trl_st X)) HDI6 HRG6 Hw8 Hp8) as (R7 & M7 & Hms7 & HDI7 & F2 & F12 & Hfr7).
      exists R7, M7. split.
      { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
        eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5|]. eapply msteps_trans; [exact Hms6 | exact Hms7]. }
      split; [exact HDI7|]. split; [keep_via HK6 Hfr7|]. split; [| exact F2].
      rewrite F12. cbn [snd]. rewrite b2z_ltb1'. reflexivity.
  - replace (flush =? 4) with false in Hms1 by (symmetry; apply Z.eqb_neq; exact Ef). cbn [negb] in Hms1 |- *.
    pose proof (reach_x38 regs0 R1 M0 M X HDI (proj1 (proj2 HRG1)) HK1). reach_step Hms1.
Qed.


Definition BLK : deflate_state * Z :=
  match BS ds flush with
  | finish_done => live_tail flush (X6 ds flush)
  | block_done => (if cs_avail_out (ds_strm (X6f ds flush)) =? 0 then set_last_flush (X6f ds flush) (-1) else X6f ds flush, Z_OK)
  | _ => (if cs_avail_out (ds_strm (X6 ds flush)) =? 0 then set_last_flush (X6 ds flush) (-1) else X6 ds flush, Z_OK)
  end.

Lemma avail_out_bst : forall X bs, cs_avail_out (ds_strm (bst_st X bs)) = cs_avail_out (ds_strm X).
Proof. intros X bs. unfold Defl6_5.bst_st. destruct bs; try reflexivity; destruct X; reflexivity. Qed.

Lemma clear_hash_eq : forall X hs0, ds_hash_size X = hs0 ->
  clear_hash X = set_head (set_head X (arr_set (ds_head X) (hs0 - 1) 0)) (arr_fill (ds_head (set_head X (arr_set (ds_head X) (hs0 - 1) 0))) 0 (hs0 - 1) 0).
Proof. intros X hs0 <-. unfold clear_hash, NIL. destruct X; reflexivity. Qed.

Lemma bd_st_eq : forall X hs0, ds_hash_size (tr_stored_block X None 0 0) = hs0 ->
  bd_st X = Defl6_5b.bd_reset (set_head (set_head (tr_stored_block X None 0 0) (arr_set (ds_head (tr_stored_block X None 0 0)) (hs0 - 1) 0))
                                (arr_fill (ds_head (set_head (tr_stored_block X None 0 0) (arr_set (ds_head (tr_stored_block X None 0 0)) (hs0 - 1) 0))) 0 (hs0 - 1) 0)).
Proof. intros X hs0 E. unfold bd_st, Defl6_5b.bd_reset. rewrite <- (clear_hash_eq _ _ E). reflexivity. Qed.

Lemma lookahead_sh2 : forall X a b, ds_lookahead (set_head (set_head X a) b) = ds_lookahead X.
Proof. intros X a b. destruct X; reflexivity. Qed.

Lemma reach_call : forall regs0 R M0 M X,
  dsafe6 SSAFE ds flush -> G4 ds flush ->
  DI M0 M X -> X = X4 ds flush -> RefDeflateHdr5.blocks_cond (X4 ds flush) flush = true ->
  HREGS R -> KEEP regs0 R -> rom_clear M0 0x10000 0x2c3f8 ->
  REACH regs0 R (0x17dc8 : word) M M0 BLK.
Proof.
  intros regs0 R M0 M X HS HG4 HDI EX Hbc HRG HK HR0. subst X.
  pose proof HS as HS0.
  destruct HS as (Hlive & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  destruct (Hblk HG4 Hbc) as (HSF & Hao5 & Hbd).
  destruct (call_blk R M0 M (X4 ds flush) HDI HRG Hlv4 Hsg4 HR0) as (R1 & Hms1 & HRG1 & A10 & A11 & A2 & A1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1.
  destruct (call_slowu R1 M0 M (X4 ds flush) HDI HSF A10 A11 A2 A1) as (R2 & M2 & Hms2 & HDI2 & B10 & B2 & Hfr2).
  assert (HK2 : KEEP regs0 R2) by keep_via HK1 Hfr2.
  assert (HRG2 : HREGS R2).
  { destruct HRG1 as (Q8 & Q2 & Q9 & Q18). unfold HREGS. rewrite !Hfr2 by reflexivity. repeat split; assumption. }
  change (fst (deflate_slow (X4 ds flush) flush)) with (X5 ds flush) in HDI2.
  change (snd (deflate_slow (X4 ds flush) flush)) with (BS ds flush) in B10.
  unfold BLK.
  assert (A6 : forall bs, cs_avail_out (ds_strm (bst_st (X5 ds flush) bs)) = cs_avail_out (ds_strm (X5 ds flush))) by (intros bs; apply avail_out_bst).
  destruct (BS ds flush) eqn:EBS.
  -
    destruct (bst_blk R2 M0 M2 (X5 ds flush) need_more HDI2 HRG2 B10 ltac:(discriminate) Hao5) as (R3 & M3 & Hms3 & HDI3 & HRG3 & Bfd & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    replace (bst_st (X5 ds flush) need_more) with (X6 ds flush) in HDI3 by (unfold X6; rewrite EBS; reflexivity).
    unfold bst_pc in Hms3. replace (cs_avail_out (ds_strm (X6 ds flush))) with (cs_avail_out (ds_strm (X5 ds flush))) by (unfold X6; rewrite EBS; symmetry; apply A6).
    destruct (Z.eqb_spec (cs_avail_out (ds_strm (X5 ds flush))) 0) as [Hz|Hz].
    + replace (cs_avail_out (ds_strm (X5 ds flush)) =? 0) with true in Hms3 by (symmetry; apply Z.eqb_eq; exact Hz).
      pose proof (reach_x64 regs0 R3 M0 M3 (X6 ds flush) HDI3 HRG3 HK3). pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms3)) as Hms123; reach_step Hms123.
    + replace (cs_avail_out (ds_strm (X5 ds flush)) =? 0) with false in Hms3 by (symmetry; apply Z.eqb_neq; exact Hz).
      pose proof (reach_x38 regs0 R3 M0 M3 (X6 ds flush) HDI3 (proj1 (proj2 HRG3)) HK3). pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms3)) as Hms123; reach_step Hms123.
  -
    destruct (Hbd eq_refl) as (Hf3 & HBI5 & Hroom5 & Hfp6 & Hao6 & Hlk5 & Hhs5 & Hws5).
    pose proof HDI2 as (_ & _ & (_ & Ehs5 & _)). rewrite Hhs5 in Ehs5. symmetry in Ehs5.
    destruct (bd_a R2 M0 M2 (X5 ds flush) HDI2 HRG2 B10 Hf3) as (R3 & Hms3 & HRG3 & C10 & C11 & C12 & C13 & C2 & C1 & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    destruct (call_tsb R3 M0 M2 (X5 ds flush) (0x17ee8%bv : word) HDI2 ltac:(apply ret_ok_even; reflexivity)
                HBI5 Hroom5 C10 C11 C12 C13 C2 C1) as (R4 & M4 & Hms4 & HDI4 & Hcl4 & Hfr4).
    assert (HK4 : KEEP regs0 R4) by keep_via HK3 Hfr4.
    assert (HRG4 : HREGS R4).
    { destruct HRG3 as (Q8 & Q2 & Q9 & Q18). unfold HREGS. rewrite !Hfr4 by reflexivity. repeat split; assumption. }
    set (X5' := tr_stored_block (X5 ds flush) None 0 0) in *.
    destruct (bd_b R4 M0 M4 X5' HDI4 HRG4 Hf3 Ehs5) as (R5 & M5 & Hms5 & HDI5 & HRG5 & D10 & D11 & D12 & D2 & D1 & D19 & Hfr5).
    assert (HK5 : KEEP regs0 R5) by keep_via HK4 Hfr5.
    destruct (call_ms R5 M0 M5 _ HDI5 Ehs5 D10 D11 D12 D1) as (R6 & M6 & Hms6 & HDI6 & Hcl6 & Hfr6).
    assert (HK6 : KEEP regs0 R6) by keep_via HK5 Hfr6.
    assert (HRG6 : HREGS R6).
    { destruct HRG5 as (Q8 & Q2 & Q9 & Q18). unfold HREGS. rewrite !Hfr6 by reflexivity. repeat split; assumption. }
    set (Xc := set_head (set_head X5' (arr_set (ds_head X5') (hs - 1) 0)) (arr_fill (ds_head (set_head X5' (arr_set (ds_head X5') (hs - 1) 0))) 0 (hs - 1) 0)) in *.
    assert (Hlkc : 0 <= ds_lookahead Xc < 2 ^ 31).
    {
      subst Xc X5'. rewrite lookahead_sh2, Defl6_5b.tsb0_lookahead. exact Hlk5. }
    destruct (bd_c R6 M0 M6 Xc HDI6 HRG6 Hlkc ltac:(rewrite (Hfr6 19%bv eq_refl); exact D19))
      as (R7 & M7 & Hms7 & HDI7 & HRG7 & E10 & E1 & Hfr7).
    assert (HK7 : KEEP regs0 R7) by keep_via HK6 Hfr7.
    assert (EXd : Defl6_5b.bd_reset Xc = X6d ds flush).
    { unfold X6d. subst Xc X5'. symmetry. apply bd_st_eq. rewrite Defl6_5b.tsb0_hash_size. congruence. }
    rewrite EXd in HDI7.
    destruct (FlushPend6u.call_fp ROM mem S p zp ds flush ra sp DEFL_K6u DEFL_FR6u HH ltac:(unfold DEFL_K6u, DEFL_FR6u; lia)
                ltac:(unfold DEFL_FR6u; lia) MEMCPY TFBITS R7 M0 M7 (X6d ds flush) (0x17f60%bv : word) HDI7 E10 (proj1 (proj2 HRG7)) E1
                ltac:(apply ret_ok_even; reflexivity) (fp_pre_of6 _ Hfp6)) as (R8 & M8 & Hms8 & HDI8 & F2 & F1 & Hfr8).
    assert (HRG8 : HREGS R8) by hregs_via HRG7 Hfr8.
    assert (HK8 : KEEP regs0 R8) by keep_via HK7 Hfr8.
    change (flush_pending (X6d ds flush)) with (X6f ds flush) in HDI8.
    pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 (msteps_trans _ _ _ _ Hms3 (msteps_trans _ _ _ _ Hms4
                 (msteps_trans _ _ _ _ Hms5 (msteps_trans _ _ _ _ Hms6 (msteps_trans _ _ _ _ Hms7 Hms8))))))) as Hms18.
    destruct (Z.eq_dec (cs_avail_out (ds_strm (X6f ds flush))) 0) as [Hz|Hz].
    + replace (cs_avail_out (ds_strm (X6f ds flush)) =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hz). cbv iota.
      destruct (bd_d0 R8 M0 M8 (X6f ds flush) HDI8 HRG8 Hz) as (R9 & Hms9 & HRG9 & G10 & G11 & G12 & G2 & Hfr9).
      assert (HK9 : KEEP regs0 R9) by keep_via HK8 Hfr9.
      destruct (x68_blk R9 M0 M8 (X6f ds flush) HDI8 HRG9 G12) as (R10 & M10 & Hms10 & HDI10 & H2 & H12 & Hfr10).
      exists R10, M10. split; [eapply msteps_trans; [exact Hms18 | eapply msteps_trans; [exact Hms9 | exact Hms10]]|].
      split; [exact HDI10|]. split; [keep_via HK9 Hfr10|]. split; [exact H12 | exact H2].
    + replace (cs_avail_out (ds_strm (X6f ds flush)) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). cbv iota.
      destruct (bd_d1 R8 M0 M8 (X6f ds flush) HDI8 HRG8 Hao6 Hz) as (R9 & Hms9 & HRG9 & G10 & G11 & G12 & G2 & Hfr9).
      assert (HK9 : KEEP regs0 R9) by keep_via HK8 Hfr9.
      destruct (bd_e R9 M8 G2 G11 Hf3) as (R10 & Hms10 & H2 & Hfr10).
      assert (HK10 : KEEP regs0 R10) by keep_via HK9 Hfr10.
      pose proof (reach_x38 regs0 R10 M0 M8 (X6f ds flush) HDI8 H2 HK10).
      pose proof (msteps_trans _ _ _ _ Hms18 (msteps_trans _ _ _ _ Hms9 Hms10)) as Hms1_10. reach_step Hms1_10.
  -
    destruct (bst_blk R2 M0 M2 (X5 ds flush) finish_started HDI2 HRG2 B10 ltac:(discriminate) Hao5) as (R3 & M3 & Hms3 & HDI3 & HRG3 & Bfd & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    replace (bst_st (X5 ds flush) finish_started) with (X6 ds flush) in HDI3 by (unfold X6; rewrite EBS; reflexivity).
    unfold bst_pc in Hms3. replace (cs_avail_out (ds_strm (X6 ds flush))) with (cs_avail_out (ds_strm (X5 ds flush))) by (unfold X6; rewrite EBS; symmetry; apply A6).
    destruct (Z.eqb_spec (cs_avail_out (ds_strm (X5 ds flush))) 0) as [Hz|Hz].
    + replace (cs_avail_out (ds_strm (X5 ds flush)) =? 0) with true in Hms3 by (symmetry; apply Z.eqb_eq; exact Hz).
      pose proof (reach_x64 regs0 R3 M0 M3 (X6 ds flush) HDI3 HRG3 HK3). pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms3)) as Hms123; reach_step Hms123.
    + replace (cs_avail_out (ds_strm (X5 ds flush)) =? 0) with false in Hms3 by (symmetry; apply Z.eqb_neq; exact Hz).
      pose proof (reach_x38 regs0 R3 M0 M3 (X6 ds flush) HDI3 (proj1 (proj2 HRG3)) HK3). pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms3)) as Hms123; reach_step Hms123.
  -
    destruct (bst_blk R2 M0 M2 (X5 ds flush) finish_done HDI2 HRG2 B10 ltac:(discriminate) Hao5) as (R3 & M3 & Hms3 & HDI3 & HRG3 & Bfd & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    replace (bst_st (X5 ds flush) finish_done) with (X6 ds flush) in HDI3 by (unfold X6; rewrite EBS; reflexivity).
    unfold bst_pc in Hms3.
    destruct (Bfd eq_refl) as (C11 & C10).
    assert (E7 : X6 ds flush = X7 ds flush) by (unfold X7; rewrite Hbc; cbv beta iota; reflexivity).
    pose proof (reach_trailer regs0 R3 M0 M3 (X6 ds flush) HS0 (conj HG4 (or_intror (conj Hbc EBS))) HDI3 E7 HRG3 HK3 C10 C11).
    pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms3)) as Hms123; reach_step Hms123.
Qed.


Definition AFTER4 : deflate_state * Z :=
  if RefDeflateHdr5.blocks_cond (X4 ds flush) flush then BLK
  else if flush =? 0 then (X4 ds flush, Z_OK) else live_tail flush (X4 ds flush).

Lemma reach_b84 : forall regs0 R M0 M X,
  dsafe6 SSAFE ds flush -> G4 ds flush ->
  DI M0 M X -> X = X4 ds flush -> cs_avail_in (ds_strm (X4 ds flush)) = 0 ->
  HREGS R -> KEEP regs0 R -> getr R 10 = zw strm -> getr R 11 = zw flush -> rom_clear M0 0x10000 0x2c3f8 ->
  REACH regs0 R (0x17dc0 : word) M M0 AFTER4.
Proof.
  intros regs0 R M0 M X HS HG4 HDI EX Hai0 HRG HK P10 P11 HR0. subst X.
  pose proof HS as HS0.
  destruct HS as (Hlive & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  pose proof Hlive as (Hf & _).
  destruct (b84_blk R M0 M (X4 ds flush) HDI HRG P11 Hlk4 Hst4) as (R1 & Hms1 & HRG1 & A10 & A11 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1. rewrite P10 in A10.
  unfold AFTER4. rewrite (Defl6_5.blocks_cond_eq flush (X4 ds flush)), Hai0. cbn [Z.eqb negb orb].
  unfold b84_pc in Hms1.
  destruct (Defl6_5.bc64_cond flush (X4 ds flush)) eqn:Ebc.
  - pose proof (reach_call regs0 R1 M0 M (X4 ds flush) HS0 HG4 HDI eq_refl ltac:(rewrite Defl6_5.blocks_cond_eq, Hai0; exact Ebc) HRG1 HK1 HR0).
    reach_step Hms1.
  - destruct (Z.eqb_spec flush 0) as [Ef|Ef].
    + pose proof (reach_x38 regs0 R1 M0 M (X4 ds flush) HDI (proj1 (proj2 HRG1)) HK1). reach_step Hms1.
    + assert (E7 : X4 ds flush = X7 ds flush) by (unfold X7; rewrite Defl6_5.blocks_cond_eq, Hai0, Ebc; cbn [Z.eqb negb orb]; reflexivity).
      assert (Hbcf : RefDeflateHdr5.blocks_cond (X4 ds flush) flush = false) by (rewrite Defl6_5.blocks_cond_eq, Hai0, Ebc; reflexivity).
      pose proof (reach_trailer regs0 R1 M0 M (X4 ds flush) HS0 (conj HG4 (or_introl (conj Hbcf Ef))) HDI E7 HRG1 HK1 A10 A11). reach_step Hms1.
Qed.

Lemma reach_bc74 : forall regs0 R M0 M X,
  dsafe6 SSAFE ds flush -> G4 ds flush ->
  DI M0 M X -> X = X4 ds flush ->
  HREGS R -> KEEP regs0 R -> rom_clear M0 0x10000 0x2c3f8 ->
  REACH regs0 R (0x17db0 : word) M M0 AFTER4.
Proof.
  intros regs0 R M0 M X HS HG4 HDI EX HRG HK HR0. subst X.
  pose proof HS as HS0.
  destruct HS as (Hlive & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  destruct (bc74_blk R M0 M (X4 ds flush) HDI HRG Hai4) as (R1 & Hms1 & HRG1 & A10 & A11 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1.
  destruct (Z.eqb_spec (cs_avail_in (ds_strm (X4 ds flush))) 0) as [Hz|Hz].
  - replace (cs_avail_in (ds_strm (X4 ds flush)) =? 0) with true in Hms1 by (symmetry; apply Z.eqb_eq; exact Hz).
    pose proof (reach_b84 regs0 R1 M0 M (X4 ds flush) HS0 HG4 HDI eq_refl Hz HRG1 HK1 A10 A11 HR0). reach_step Hms1.
  - replace (cs_avail_in (ds_strm (X4 ds flush)) =? 0) with false in Hms1 by (symmetry; apply Z.eqb_neq; exact Hz).
    assert (Hbc : RefDeflateHdr5.blocks_cond (X4 ds flush) flush = true) by (rewrite Defl6_5.blocks_cond_eq; rewrite (proj2 (Z.eqb_neq _ _) Hz); reflexivity).
    unfold AFTER4. rewrite Hbc.
    pose proof (reach_call regs0 R1 M0 M (X4 ds flush) HS0 HG4 HDI eq_refl Hbc HRG1 HK1 HR0). reach_step Hms1.
Qed.


Definition AFTER3 : deflate_state * Z :=
  if (ds_status ds =? 42) && negb (ds_pending (X4h ds flush) =? 0) then (set_last_flush (X4h ds flush) (-1), Z_OK)
  else AFTER4.

Lemma reach_dispatch : forall regs0 R M0 M X,
  dsafe6 SSAFE ds flush -> G3 ds flush ->
  DI M0 M X -> X = X3 ds flush ->
  HREGS R -> KEEP regs0 R -> getr R 13 = zw (ds_status ds) -> getr R 10 = zw strm -> getr R 11 = zw flush ->
  rom_clear M0 0x10000 0x2c3f8 ->
  REACH regs0 R (0x170d4 : word) M M0 AFTER3.
Proof.
  intros regs0 R M0 M X HS HG3 HDI EX HRG HK P13 P10 P11 HR0. subst X.
  pose proof HS as HS0.
  destruct HS as (Hlive & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  destruct Hlive as (Hf & Hstat & Hao & Hai & Haif & H666 & H42 & Hlv & Hsg & Hwb & Hwrap & Hpd & Hni & Had).
  pose proof (X1_keeps ds flush) as (K1s & K1w & K1p & K1ss & K1wb & K1lv & K1sg & K1st).
  unfold AFTER3.
  destruct Hstat as [E42|[E113|E666]]; rewrite E42 || rewrite E113 || rewrite E666; rewrite ?E42, ?E113, ?E666 in P13; cbn [Z.eqb Pos.eqb andb].
  -
    destruct (H42 E42) as (Hw1 & Hp00 & Hss).
    assert (EX3 : X3 ds flush = X1 ds flush) by (unfold X3; rewrite (proj2 (Z.eqb_eq _ _) Hp00); cbv beta iota; reflexivity).
    destruct (Hh E42) as (Hpbl & Hfp & Hp4 & Hs4).
    destruct (d42_blk R M HRG P13) as (R1 & Hms1 & HRG1 & A10 & Hfr1).
    assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1. rewrite P10 in A10.
    destruct (init_blk R1 M0 M (X3 ds flush) HDI HRG1
                ltac:(rewrite EX3, K1w; exact Hw1) ltac:(rewrite EX3, K1wb; exact Hwb) ltac:(rewrite EX3, K1sg; exact Hsg)
                ltac:(rewrite EX3, K1lv; exact Hlv) ltac:(rewrite EX3, K1ss; exact Hss))
      as (R2 & Hms2 & HRG2 & B10 & B11 & B1 & Hfr2).
    assert (HK2 : KEEP regs0 R2) by keep_via HK1 Hfr2.
    assert (Hp30 : ds_pending (X3 ds flush) = 0) by (rewrite EX3, K1p; exact Hp00).
    destruct (psm_blk R2 M0 M (X3 ds flush) 30876 120 30876 (0x17188%bv : word) HDI HRG2 B10 B11 B1
                ltac:(apply ret_ok_even; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity))
      as (R3 & M3 & Hms3 & HDI3 & HRG3 & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    destruct (hdr2_blk R3 M0 M3 (psm_st (X3 ds flush) 120 30876) HDI3 HRG3 ltac:(rewrite psm_st_strstart, EX3, K1ss; exact Hss))
      as (R4 & Hms4 & HRG4 & C10 & C11 & C12 & C1 & Hfr4).
    assert (HK4 : KEEP regs0 R4) by keep_via HK3 Hfr4.
    destruct (call_adl R4 M0 M3 (psm_st (X3 ds flush) 120 30876) (0x171c0%bv : word) HDI3 HRG4 C11 C12 C1 ltac:(apply ret_ok_even; reflexivity))
      as (R5 & M5 & Hms5 & HDI5 & HRG5 & D10 & Dcells & Hfr5).
    assert (HK5 : KEEP regs0 R5) by keep_via HK4 Hfr5.
    destruct (adl_blk R5 M0 M5 (psm_st (X3 ds flush) 120 30876) HDI5 HRG5 D10) as (R6 & M6 & Hms6 & HDI6 & HRG6 & E10 & E1 & Hfr6).
    assert (HK6 : KEEP regs0 R6) by keep_via HK5 Hfr6.
    rewrite (hdr_st_eq (X3 ds flush) Hp30) in HDI6.
    destruct (FlushPend6u.call_fp ROM mem S p zp ds flush ra sp DEFL_K6u DEFL_FR6u HH ltac:(unfold DEFL_K6u, DEFL_FR6u; lia)
                ltac:(unfold DEFL_FR6u; lia) MEMCPY TFBITS R6 M0 M6 (hdr_st (X3 ds flush)) (0x171d4%bv : word) HDI6 E10 (proj1 (proj2 HRG6)) E1
                ltac:(apply ret_ok_even; reflexivity) (fp_pre_of6 _ Hfp)) as (R7 & M7 & Hms7 & HDI7 & F2 & F1 & Hfr7).
    assert (HRG7 : HREGS R7) by hregs_via HRG6 Hfr7.
    assert (HK7 : KEEP regs0 R7) by keep_via HK6 Hfr7.
    change (flush_pending (hdr_st (X3 ds flush))) with (X4h ds flush) in HDI7.
    destruct (fpret2_blk R7 M0 M7 (X4h ds flush) HDI7 HRG7 Hp4 Hs4) as (R8 & Hms8 & HRG8 & G8 & Hfr8).
    assert (HK8 : KEEP regs0 R8) by keep_via HK7 Hfr8.
    unfold pend_pc in Hms8.
    pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 (msteps_trans _ _ _ _ Hms3 (msteps_trans _ _ _ _ Hms4
                 (msteps_trans _ _ _ _ Hms5 (msteps_trans _ _ _ _ Hms6 (msteps_trans _ _ _ _ Hms7 Hms8))))))) as Hms18.
    destruct (Z.eqb_spec (ds_pending (X4h ds flush)) 0) as [Hq|Hq]; cbn [negb].
    + destruct (G8 Hq) as (G10 & G13).
      destruct (g_blk R8 M7 HRG8 G13) as (R9 & Hms9 & HRG9 & Hfr9).
      assert (HK9 : KEEP regs0 R9) by keep_via HK8 Hfr9.
      assert (E4 : X4h ds flush = X4 ds flush) by (unfold X4; rewrite E42; cbn [Z.eqb Pos.eqb]; reflexivity).
      assert (HG4 : G4 ds flush) by (split; [exact HG3 | intros _; exact Hq]).
      pose proof (reach_bc74 regs0 R9 M0 M7 (X4h ds flush) HS0 HG4 HDI7 E4 HRG9 HK9 HR0).
      pose proof (msteps_trans _ _ _ _ Hms18 Hms9) as Hms19. reach_step Hms19.
    + pose proof (reach_x64 regs0 R8 M0 M7 (X4h ds flush) HDI7 HRG8 HK8). reach_step Hms18.
  -
    destruct (d113_blk R M HRG P13) as (R1 & Hms1 & HRG1 & A10 & A11 & A13 & Hfr1).
    assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1.
    destruct (g_blk R1 M HRG1 A13) as (R2 & Hms2 & HRG2 & Hfr2).
    assert (HK2 : KEEP regs0 R2) by keep_via HK1 Hfr2.
    assert (E4 : X3 ds flush = X4 ds flush) by (unfold X4; rewrite E113; cbn [Z.eqb Pos.eqb]; reflexivity).
    assert (HG4 : G4 ds flush) by (split; [exact HG3 | intros E; rewrite E113 in E; discriminate E]).
    pose proof (reach_bc74 regs0 R2 M0 M (X3 ds flush) HS0 HG4 HDI E4 HRG2 HK2 HR0).
    pose proof (msteps_trans _ _ _ _ Hms1 Hms2) as Hms12. reach_step Hms12.
  -
    destruct (d666_blk R M0 M (X3 ds flush) HDI HRG P13 P10 (Hai3 E666)) as (R1 & Hms1 & HRG1 & A10 & A11 & A12 & Hfr1).
    assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1. rewrite P11 in A11.
    assert (E4 : X3 ds flush = X4 ds flush) by (unfold X4; rewrite E666; cbn [Z.eqb Pos.eqb]; reflexivity).
    assert (HG4 : G4 ds flush) by (split; [exact HG3 | intros E; rewrite E666 in E; discriminate E]).
    pose proof (reach_b84 regs0 R1 M0 M (X3 ds flush) HS0 HG4 HDI E4 ltac:(rewrite <- E4; exact (Hai3 E666)) HRG1 HK1 A10 A11 HR0). reach_step Hms1.
Qed.


Definition FRONT : deflate_state * Z :=
  if negb (ds_pending ds =? 0) && (cs_avail_out (ds_strm (X2 ds flush)) =? 0) then (set_last_flush (X2 ds flush) (-1), Z_OK)
  else AFTER3.

Lemma live_core_front : live_core ds flush = FRONT.
Proof. reflexivity. Qed.

Lemma reach_front : forall regs0 R M1,
  dsafe6u SSAFE ds flush -> DI M1 M1 ds -> rom_clear M1 0x10000 0x2c3f8 ->
  getr R 8 = zw S -> getr R 2 = zw SP -> getr R 10 = zw strm -> getr R 11 = zw flush -> getr R 13 = zw (ds_status ds) ->
  KEEP regs0 R -> REACH regs0 R (0x17008 : word) M1 M1 FRONT.
Proof.
  intros regs0 R M1 [HS Hlf] HDI HR1 P8 P2 P10 P11 P13 HK. pose proof HS as HS0.
  destruct HS as (Hlive & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  clear Hh Hai4 Hlk4 Hst4 Hlv4 Hsg4 Hai3 Hw3 Hw3' Hblk Htl.
  pose proof Hlive as (Hf & Hstat & Hao & Hai & Haif & H666 & H42 & _ & _ & _ & _ & Hpd & Hni & _). clear Hlive.
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & HIN).
  pose proof (wf_lbs _ HWF) as Wlbs.
  assert (Hst31 : 0 <= ds_status ds < 2 ^ 31) by (destruct Hstat as [E|[E|E]]; rewrite E; lia).
  destruct (prob_blk R M1 M1 ds HDI P8 P2 P10 P11 P13 Hf
              ltac:(intros En4 E666; pose proof (Haif (H666 E666)); lia) Haif Hst31 Hai Hao ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (R2 & M2 & Hms2 & HDI2 & HRG2 & A13 & A10 & A11 & A14 & A12 & A1 & Hfr2).
  assert (HK2 : KEEP regs0 R2) by keep_via HK Hfr2.
  change (set_last_flush ds flush) with (X1 ds flush) in HDI2.
  pose proof (X1_keeps ds flush) as (K1s & K1w & K1p & K1ss & K1wb & K1lv & K1sg & K1st).
  unfold prob_pc in Hms2.
  destruct (Z.eqb_spec (ds_pending ds) 0) as [Hq0|Hq0].
  -
    destruct (pend0_blk R2 M2 ds HRG2 A14 A12 A11 Haif Hai Hlf) as (R3 & Hms3 & HRG3 & B10 & B11 & B13 & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3. rewrite A10 in B10. rewrite A11 in B11. rewrite A13 in B13.
    assert (EX3 : X1 ds flush = X3 ds flush) by (unfold X3; rewrite (proj2 (Z.eqb_eq _ _) Hq0); reflexivity).
    assert (HG3 : G3 ds flush) by (intros P; exfalso; exact (P Hq0)).
    pose proof (reach_dispatch regs0 R3 M1 M2 (X1 ds flush) HS0 HG3 HDI2 EX3 HRG3 HK3 B13 B10 B11 HR1) as H.
    replace FRONT with AFTER3 by (unfold FRONT; rewrite (proj2 (Z.eqb_eq _ _) Hq0); cbn [negb andb]; reflexivity).
    pose proof (msteps_trans _ _ _ _ Hms2 Hms3) as Hms. reach_step Hms.
  -
    destruct (Hf2 Hq0) as (Hfp & Hav2 & Hst2 & Est2 & Eai2).
    destruct (FlushPend6u.call_fp ROM mem S p zp ds flush ra sp DEFL_K6u DEFL_FR6u HH ltac:(unfold DEFL_K6u, DEFL_FR6u; lia)
                ltac:(unfold DEFL_FR6u; lia) MEMCPY TFBITS R2 M1 M2 (X1 ds flush) (0x17094%bv : word) HDI2 A10 (proj1 (proj2 HRG2)) (A1 Hq0)
                ltac:(apply ret_ok_even; reflexivity) (fp_pre_of6 _ Hfp)) as (R3 & M3 & Hms3 & HDI3 & C2 & C1 & Hfr3).
    assert (HRG3 : HREGS R3) by hregs_via HRG2 Hfr3.
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    change (flush_pending (X1 ds flush)) with (X2 ds flush) in HDI3.
    destruct (fpret_blk R3 M1 M3 (X2 ds flush) HDI3 HRG3 ltac:(lia) Hst2) as (R4 & Hms4 & HRG4 & D4 & Hfr4).
    assert (HK4 : KEEP regs0 R4) by keep_via HK3 Hfr4.
    unfold Defl6_2.avail_pc in Hms4.
    pose proof (msteps_trans _ _ _ _ Hms2 (msteps_trans _ _ _ _ Hms3 Hms4)) as Hms.
    destruct (Z.eqb_spec (cs_avail_out (ds_strm (X2 ds flush))) 0) as [Hz|Hnz].
    + pose proof (reach_x64 regs0 R4 M1 M3 (X2 ds flush) HDI3 HRG4 HK4) as H.
      replace FRONT with (set_last_flush (X2 ds flush) (-1), Z_OK)
        by (unfold FRONT; rewrite (proj2 (Z.eqb_neq _ _) Hq0); rewrite (proj2 (Z.eqb_eq _ _) Hz); cbn [negb andb]; reflexivity).
      reach_step Hms.
    + destruct (D4 Hnz) as (D10 & D11 & D13). rewrite Est2 in D13.
      assert (EX3 : X2 ds flush = X3 ds flush) by (unfold X3; rewrite (proj2 (Z.eqb_neq _ _) Hq0); reflexivity).
      assert (HG3 : G3 ds flush) by (intros _; rewrite <- EX3; exact Hnz).
      pose proof (reach_dispatch regs0 R4 M1 M3 (X2 ds flush) HS0 HG3 HDI3 EX3 HRG4 HK4 D13 D10 D11 HR1) as H.
      replace FRONT with AFTER3
        by (unfold FRONT; rewrite (proj2 (Z.eqb_neq _ _) Hq0); rewrite (proj2 (Z.eqb_neq _ _) Hnz); cbn [negb andb]; reflexivity).
      reach_step Hms.
Qed.


Lemma DI_fin : forall m1 m X, DI m1 m X -> agree_out [(sp - 64, 64)] mem m1 ->
  ZR6u m S p zp X /\ agree_out (ZRFo DEFL_K6u S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm X))))) mem m /\ rod6u m /\ ROM m
  /\ (forall x, mem x <> None -> m x <> None)
  /\ lzk ds X.
Proof.
  intros m1 m X (HB & HR & HS3) Hag1.
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  assert (HagO : agree_out (ZRFo DEFL_K6u S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm X))))) mem m).
  { eapply agree_out_trans.
    - eapply agree_out_weaken; [exact Hag1|]. unfold ZRFo, DEFL_K6u. cbn [in_franges]. intros x Hx. lia.
    - eapply agree_out_weaken; [exact HAG|]. unfold DeflKit6u.GDo, ZRFo, DEFL_K6u, DEFL_FR6u, ds6u_SIZE, zsl_SIZE. cbn [in_franges]. intros x Hx. lia. }
  split; [| split; [exact HagO | split; [exact HRC | split; [exact HRD | split; [exact HGR0|]]]]].
  - unfold ZR6u, ds6u_windowA, ds6u_prevA, ds6u_headA, ds6u_arrays. repeat (split; [assumption|]). exact Zo.
  - destruct HS3 as (E1 & E2 & E3). destruct HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
    pose proof HB as (_ & _ & _ & _ & Epbl & _). unfold lzk.
    repeat (split; [first [assumption | lia]|]). exact Hol.
Qed.

Lemma bvneq' : forall (r k : reg) (z : Z), (bv_unsigned r =? bv_unsigned k) = false -> bv_unsigned k = z -> bv_unsigned r <> z.
Proof. intros r k z H <-. apply Z.eqb_neq. exact H. Qed.

Local Ltac bvlits :=
  repeat match goal with H : (_ || _)%bool = false |- _ => apply Bool.orb_false_elim in H; destruct H end;
  repeat match goal with H : (bv_unsigned ?r =? bv_unsigned ?k) = false |- _ =>
    let z := eval vm_compute in (bv_unsigned k) in pose proof (bvneq' r k z H eq_refl); clear H end.

Lemma reg_frame_fin : forall (R4 R3 regs : bvmap 5 word),
  getr R4 2 = getr regs 2 ->
  (forall r : reg, reg_in r [1; 8; 9; 18; 19; 20; 21]%bv = true -> getr R4 r = getr regs r) ->
  (forall r : reg, reg_in r [1; 2; 8; 9; 10; 18; 19; 20; 21]%bv = false -> getr R4 r = getr R3 r) ->
  KEEP regs R3 ->
  forall r : reg, reg_in r LZ_CLOB = false -> getr R4 r = getr regs r.
Proof.
  intros R4 R3 regs H2 Hrest Hfr (K3 & K4 & K23 & K24 & K25 & K26 & K27 & K22) r Hr.
  pose proof (u5_range r) as Ur.
  destruct (reg_in r [1; 8; 9; 18; 19; 20; 21]%bv) eqn:E1; [exact (Hrest r E1)|].
  destruct (bv_eqb r 2) eqn:E2.
  { assert (Er : r = 2%bv) by (apply bv_eq; unfold bv_eqb in E2; apply Z.eqb_eq in E2; exact E2). subst r. exact H2. }
  destruct (bv_eqb r 10) eqn:E10.
  { exfalso. assert (Er : r = 10%bv) by (apply bv_eq; unfold bv_eqb in E10; apply Z.eqb_eq in E10; exact E10). subst r. discriminate Hr. }
  assert (E3 : reg_in r [1; 2; 8; 9; 10; 18; 19; 20; 21]%bv = false).
  { cbn [reg_in] in E1 |- *. rewrite E2, E10. apply Bool.orb_false_elim in E1 as [E1a E1b]. rewrite E1a. cbn [orb]. exact E1b. }
  rewrite (Hfr r E3).
  destruct (bv_eqb r 0) eqn:E0.
  { assert (Er : r = 0%bv) by (apply bv_eq; unfold bv_eqb in E0; apply Z.eqb_eq in E0; exact E0). subst r. reflexivity. }
  destruct (bv_eqb r 22) eqn:E22.
  { assert (Er : r = 22%bv) by (apply bv_eq; unfold bv_eqb in E22; apply Z.eqb_eq in E22; exact E22). subst r. exact K22. }
  destruct (bv_eqb r 3) eqn:E3'.
  { assert (Er : r = 3%bv) by (apply bv_eq; unfold bv_eqb in E3'; apply Z.eqb_eq in E3'; exact E3'). subst r. exact K3. }
  destruct (bv_eqb r 4) eqn:E4'.
  { assert (Er : r = 4%bv) by (apply bv_eq; unfold bv_eqb in E4'; apply Z.eqb_eq in E4'; exact E4'). subst r. exact K4. }
  destruct (bv_eqb r 23) eqn:E23.
  { assert (Er : r = 23%bv) by (apply bv_eq; unfold bv_eqb in E23; apply Z.eqb_eq in E23; exact E23). subst r. exact K23. }
  destruct (bv_eqb r 24) eqn:E24.
  { assert (Er : r = 24%bv) by (apply bv_eq; unfold bv_eqb in E24; apply Z.eqb_eq in E24; exact E24). subst r. exact K24. }
  destruct (bv_eqb r 25) eqn:E25.
  { assert (Er : r = 25%bv) by (apply bv_eq; unfold bv_eqb in E25; apply Z.eqb_eq in E25; exact E25). subst r. exact K25. }
  destruct (bv_eqb r 26) eqn:E26.
  { assert (Er : r = 26%bv) by (apply bv_eq; unfold bv_eqb in E26; apply Z.eqb_eq in E26; exact E26). subst r. exact K26. }
  destruct (bv_eqb r 27) eqn:E27.
  { assert (Er : r = 27%bv) by (apply bv_eq; unfold bv_eqb in E27; apply Z.eqb_eq in E27; exact E27). subst r. exact K27. }
  exfalso. unfold LZ_CLOB in Hr. cbn [reg_in] in Hr, E1, E3. unfold bv_eqb in *.
  bvlits. lia.
Qed.


Theorem deflate_run : forall regs,
  dsafe6u SSAFE ds flush ->
  getr regs 10 = zw strm -> getr regs 11 = zw flush -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m',
    msteps s6u_segs (mkst regs (0x16f84 : word) mem s6u_rom) (mkst R ra m' s6u_rom)
    /\ ZR6u m' S p zp (fst (deflate_core ds flush))
    /\ getr R 10 = zw (snd (deflate_core ds flush))
    /\ getr R 2 = zw sp
    /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R r = getr regs r)
    /\ agree_out (ZRFo DEFL_K6u S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm (fst (deflate_core ds flush))))))) mem m'
    /\ rod6u m' /\ ROM m'
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ lzk ds (fst (deflate_core ds flush)).
Proof.
  intros regs HSU P10 P11 P2 P1. pose proof HSU as [HS Hlf].
  rewrite (core_live SSAFE ds flush HS), live_core_front.
  pose proof HS as (Hlive & _). pose proof Hlive as (_ & Hstat & _).
  destruct (pro_a regs Hstat P10 P11 P2 P1)
    as (R1 & M1 & Hms1 & HDI1 & HFRM & HR1 & A8 & A2 & A10 & A11 & A13 & A12 & A1 & Hfr1 & Hag1).
  assert (HK1 : KEEP regs R1) by (unfold KEEP; repeat split; apply Hfr1; reflexivity).
  destruct (reach_front regs R1 M1 HSU HDI1 HR1 A8 A2 A10 A11 A13 HK1) as (R' & M' & Hms & HDI' & HK' & B12 & B2).
  revert HDI' B12. generalize FRONT. intros [X code] HDI' B12. cbn [fst snd] in HDI', B12 |- *.
  destruct (epi_blk R' regs M1 M' X HDI' (FRM_keep M1 M' X regs HDI' HFRM) P1 B2)
    as (R9 & Hms9 & C2 & C10 & Hrest & Hfr9).
  destruct (DI_fin M1 M' X HDI' Hag1) as (HZ & Hag & Hrc & Hrd & Hgr & Hk).
  exists R9, M'. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms | exact Hms9]|].
  split; [exact HZ|]. split; [rewrite C10; exact B12|]. split; [exact C2|].
  split; [apply (reg_frame_fin R9 R' regs); [rewrite C2, P2; reflexivity | exact Hrest | exact Hfr9 | exact HK']|].
  split; [exact Hag|]. split; [exact Hrc|]. split; [exact Hrd|]. split; [exact Hgr | exact Hk].
Qed.

End Walk.


Theorem deflate_run6u_ok :
  forall (ROM : (word -> option byte) -> Prop) (SSAFE : deflate_state -> Z -> Prop),
    memcpy_run6u -> tr_flush_bits_run6u -> adler32_null_run6u -> deflate_slow_run6u ROM SSAFE -> rom_local6u ROM ->
    memset_run6u -> tr_stored_block_run6u ->
    deflate_run6u ROM (fun ds f => DWF ds /\ dsafe6u SSAFE ds f).
Proof.
  intros ROM SSAFE MEMCPY TFBITS ADLN SLOW HRL MEMSET TSB.
  unfold deflate_run6u.
  intros mem S p zp ds flush ra sp regs HL HROMC HP Hret HZR HROM [HWF HSAFE] P10 P11 P2 P1.
  assert (Hfl : 0 <= flush <= 5) by (destruct HSAFE as [((Hf & _) & _) _]; lia).
  assert (HK6 : 0 <= DEFL_FR6u <= DEFL_K6u) by (unfold DEFL_K6u, DEFL_FR6u; lia).
  destruct (deflate_run ROM mem S p zp ds flush ra sp
              {| dfh_K := {| dsh_L := HL; dsh_ret := Hret; dsh_zr := HZR; dsh_flush := Hfl; dsh_wf := HWF; dsh_rom := HROM;
                            dsh_roml := HRL; dsh_K := HK6 |};
                 dfh_P := HP; dfh_img := HROMC |}
              MEMCPY TFBITS ADLN SSAFE SLOW MEMSET TSB regs HSAFE P10 P11 P2 P1)
    as (R & m' & Hms & HZ & A10 & A2 & Hfr & Hag & Hrc & Hrd & Hgr & Hk).
  exists R, m'. unfold A6U_DEFLATE. replace (zw 0x16f84) with (0x16f84%bv : word) by (apply bv_eq; reflexivity).
  split; [exact Hms|]. split; [exact HZ|]. split; [exact A10|]. split; [exact A2|]. split; [exact Hfr|].
  split; [exact Hag|]. split; [exact Hrc|]. split; [exact Hrd|]. split; [exact Hgr | exact Hk].
Qed.
End FXG.

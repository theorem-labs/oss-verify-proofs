(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import DS6 CalleeKits6 DeflSlow6_1 DeflSlow6_2 Defl6Api Defl6_1 Defl6_2 Defl6_3 Defl6_5 Defl6_6 Defl6_M DeflSlow6_M.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u Callee6u CalleeKits6u TreesRod6u TreesApi6u TrApi6u
  FillWin6uA DeflBlkApi6u DeflKit6u FlushPend6u DeflSlow6u_8 DeflSlow6u_9 Defl6uApi Defl6u_1 Defl6u_2.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
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



Lemma DI_scratch : forall m1 m m' X (Fc : franges),
  DI m1 m X -> agree_out Fc m m' -> (forall x, in_franges Fc x -> sp - DEFL_K6u <= x < SP) ->
  (forall x, m x <> None -> m' x <> None) -> DI m1 m' X.
Proof.
  intros m1 m m' X Fc HDI Hag HFc HGR'.
  pose proof HDI as (HB & HR & (Ews & Ehs & Elbs)).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HB as (_ & _ & _ & _ & Epbl & _).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN). unfold DEFL_K6u, DEFL_FR6u in Hsp, MF.
  pose proof (wf_lbs _ HWF) as Wlbs.
  assert (HFM : forall x : word, in_franges Fc (bv_unsigned x) -> m x <> None).
  { intros x Hx. apply MF. pose proof (HFc _ Hx). unfold DEFL_K6u in *. lia. }
  apartF 0%nat 1%nat A01. apartF 0%nat 2%nat A02. apartF 0%nat 3%nat A03. apartF 0%nat 4%nat A04.
  apartF 0%nat 5%nat A05. apartF 0%nat 6%nat A06. apartF 0%nat 7%nat A07. apartF 0%nat 8%nat A08.
  split.
  { unfold BR. split.
    { eapply (dsl_scalars_agree s6u_segs 180992 181024 181056 Fc m m'); [exact Hsc | exact Hag | | lia | unfold dsl_SIZE; lia].
      intros x Hx Hin. pose proof (HFc _ Hin). unfold dsl_SIZE, DEFL_K6u in *. lia. }
    split.
    { unfold ds6u_arrays in *. eapply (arrays_agree_out6u Fc m m'); [exact Har | exact Hag | | lia | lia].
      intros x Hx. pose proof (HFc _ Hx). unfold DEFL_K6u in *. lia. }
    split; [exact Hlens|].
    split.
    { unfold dsl_pendA in *. rewrite Epbl in Hpend. rewrite ?Epbl. eapply cells_agree_out; [exact Hag | | cbn; lia | lia | lia | exact Hpend].
      intros x Hx Hin. pose proof (HFc _ Hin). unfold DEFL_K6u in *. lia. }
    split; [exact Epbl|].
    split; [eapply agree_out_trans; [exact HagF | eapply agree_out_weaken; [exact Hag |]];
           intros x Hx; apply in_Fd; pose proof (HFc _ Hx); unfold DEFL_K6u in *; lia|].
    split; [intros x Hx; apply HGR'; apply MS; exact Hx|]. split; [intros x Hx; apply HGR'; apply MP; exact Hx|].
    intros x Hx. apply HGR'. apply HGR0. exact Hx. }
  split; [| exact (conj Ews (conj Ehs Elbs))].
  eapply (RZ_agree _ _ _ _ _ _ _ _ _ _ _ HH m1 m m' _ _ _ _ Fc HR Hag); try exact HGR'.
  - intros x Hx. apply in_GDo. pose proof (HFc _ Hx). unfold DEFL_K6u, DEFL_FR6u in *. lia.
  - exact HFM.
  - intros x Hx Hin. pose proof (HFc _ Hin). unfold DEFL_K6u in *. lia.
  - intros x Hx Hin. pose proof (HFc _ Hin). unfold DEFL_K6u in *. lia.
  - intros x Hx Hin. pose proof (HFc _ Hin). unfold DEFL_K6u in *. lia.
  - intros x Hx Hin. pose proof (HFc _ Hin). unfold DEFL_K6u in *. lia.
  - intros x Hx Hin. pose proof (HFc _ Hin). unfold DEFL_K6u in *. lia.
  - intros x Hx Hin. pose proof (HFc _ Hin). unfold DEFL_K6u in *. lia.
Qed.


Definition psm_st (X : deflate_state) (c1 c2 : Z) : deflate_state :=
  let p0 := ds_pending X in
  let pb1 := arr_set (ds_pending_buf X) p0 (wrap8 c1) in
  set_pending_buf (set_pending (set_pending_buf (set_pending X (p0 + 1)) pb1) (p0 + 2)) (arr_set pb1 (p0 + 1) (wrap8 c2)).

Lemma psm_blk : forall regs m1 m X b c1 c2 (ra' : word),
  DI m1 m X -> HREGS regs -> getr regs 10 = zw S -> getr regs 11 = zw b -> getr regs 1 = ra' -> ret_ok ra' ->
  0 <= b < 2 ^ 16 -> 0 <= ds_pending X -> ds_pending X + 2 <= PBL ->
  c1 mod 2 ^ 8 = (b / 2 ^ 8) mod 2 ^ 8 -> c2 mod 2 ^ 8 = b mod 2 ^ 8 ->
  exists R M,
    msteps s6u_segs (mkst regs (0x18288 : word) m s6u_rom) (mkst R ra' M s6u_rom)
    /\ DI m1 M (psm_st X c1 c2)
    /\ HREGS R
    /\ (forall r : reg, reg_in r [10; 12; 13; 14; 15]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X b c1 c2 ra' HDI HRG P10 P11 P1 Hret Hb Hp0 Hp2 Hc1 Hc2. open_di HDI. open_hregs HRG.
  pose proof (wf_lbs _ HWF) as Wlbs.
  sc_cell Hsc ds6u_pending C40. sc_cell Hsc ds6u_pending_buf C16.
  apartF 1%nat 5%nat A15.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (10, EVar 32%nat); (11, EVar 36%nat)] 40%nat
    [false; false; false; false; false; false; false]
    [RVal (EVar 38); RVal (EVar 37)]
    [(36%nat, 2 ^ 16); (37%nat, 2 ^ 63); (38%nat, 2 ^ 62)] [b; PB; ds_pending X].
  clear_aparts. rewrite P1 in Hms.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end)
    [KPending; KPb (ds_pending X) c1; KPending; KPb (ds_pending X + 1) c2].
  ex2. split; [exact Hms|].
  split; [lazymatch goal with H : DeflKit6u.DI _ _ _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end;
          unfold psm_st; st_close idtac|].
  split; [hregs_via HRG Hfr | fr_weak Hfr].
Qed.


Lemma init_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs ->
  ds_wrap X = 1 -> ds_w_bits X = 15 -> ds_strategy X = 0 -> ds_level X = 6 -> ds_strstart X = 0 ->
  exists R,
    msteps s6u_segs (mkst regs (0x170f8 : word) m s6u_rom) (mkst R (0x18288 : word) m s6u_rom)
    /\ HREGS R /\ getr R 10 = zw S /\ getr R 11 = zw 30876 /\ getr R 1 = (0x17188%bv : word)
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hwr Hwb Hstr Hlv Hss. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6u_wrap C48. rewrite Hwr in C48. sc_cell Hsc ds6u_w_bits C84. rewrite Hwb in C84.
  sc_cell Hsc ds6u_strategy C200. rewrite Hstr in C200. sc_cell Hsc ds6u_level C196. rewrite Hlv in C196.
  sc_cell Hsc ds6u_strstart C172. rewrite Hss in C172.
  run 60%nat [false; false; true; true; true]
    [RVal (ELit 1); RVal (ELit 15); RVal (ELit 0); RVal (ELit 6); RVal (ELit 0)] NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Lemma hdr2_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> ds_strstart X = 0 ->
  exists R,
    msteps s6u_segs (mkst regs (0x17188 : word) m s6u_rom) (mkst R (0x1af3c : word) m s6u_rom)
    /\ HREGS R /\ getr R 10 = zw 0 /\ getr R 11 = zw 0 /\ getr R 12 = zw 0 /\ getr R 1 = (0x171c0%bv : word)
    /\ (forall r : reg, reg_in r [1; 10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hss. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6u_strstart C172. rewrite Hss in C172.
  run 12%nat [true] [RVal (ELit 0)] NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Lemma call_adl : forall regs m1 m X (ra' : word),
  DI m1 m X -> HREGS regs -> getr regs 11 = zw 0 -> getr regs 12 = zw 0 -> getr regs 1 = ra' -> ret_ok ra' ->
  exists R M,
    msteps s6u_segs (mkst regs (0x1af3c : word) m s6u_rom) (mkst R ra' M s6u_rom)
    /\ DI m1 M X
    /\ HREGS R /\ getr R 10 = zw 1
    /\ (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs M a w v)
    /\ (forall r : reg, reg_in r c_clob = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X ra' HDI HRG P11 P12 P1 Hret. pose proof HRG as (P8 & P2 & P9 & P18).
  pose proof HDI as (HB & HR & HS3). pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & _). unfold DEFL_K6u, DEFL_FR6u in Hsp, MF.
  destruct (ADLN m regs SP ra' ltac:(unfold ADLER_FR6U; lia) ltac:(lia)
              ltac:(unfold ADLER_FR6U; intros x Hx; apply MF; lia) Hret P1 P2 P11 P12)
    as (R & M & Hms & A10 & A2 & Hfr & Hag & HGR').
  exists R, M. symex_pc_lit_in Hms. split; [exact Hms|].
  split; [eapply (DI_scratch m1 m M X _ HDI Hag); [| exact HGR']; unfold ADLER_FR6U, DEFL_K6u; intros x Hx; cbn in Hx; lia|].
  split.
  { unfold HREGS. rewrite (Hfr 8%bv eq_refl), (Hfr 9%bv eq_refl), (Hfr 18%bv eq_refl). repeat split; assumption. }
  split; [exact A10|]. split; [| exact Hfr].
  intros a w v Hc Ha1 Ha2. apply (cell_agree_out s6u_segs _ m M a w v Hag); [| lia | lia | exact Hc].
  unfold ADLER_FR6U. intros x Hx Hin. cbn in Hin. lia.
Qed.


Lemma hdr_st_eq : forall X, ds_pending X = 0 ->
  set_status (set_strm (psm_st X 120 30876) (cset_adler (ds_strm (psm_st X 120 30876)) 1)) 113 = hdr_st X.
Proof.
  intros X Hp. unfold hdr_st, psm_st. cbv zeta. dsred. rewrite Hp. destruct X. reflexivity.
Qed.

Lemma adl_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw 1 ->
  exists R M,
    msteps s6u_segs (mkst regs (0x171c0 : word) m s6u_rom) (mkst R (0x181ac : word) M s6u_rom)
    /\ DI m1 M (set_status (set_strm X (cset_adler (ds_strm X) 1)) 113)
    /\ HREGS R /\ getr R 10 = zw strm /\ getr R 1 = (0x171d4%bv : word)
    /\ (forall r : reg, reg_in r [1; 10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG P10. open_di HDI. open_hregs HRG.
  apartF 1%nat 6%nat A16.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (10, ELit 1)] 12%nat
    NoDirs NoReads NoBounds (@nil Z).
  clear_aparts.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KAdler; KStatus].
  ex2. split; [exact Hms|]. split; [the_DI|].
  split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Lemma fpret2_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= ds_pending X < 2 ^ 63 -> ds_status X = 113 ->
  exists R,
    msteps s6u_segs (mkst regs (0x171d4 : word) m s6u_rom) (mkst R (pend_pc X (0x17ea0 : word) (0x171e4 : word)) m s6u_rom)
    /\ HREGS R /\ (ds_pending X = 0 -> getr R 10 = zw strm /\ getr R 13 = zw 113)
    /\ (forall r : reg, reg_in r [10; 13]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hpd Hst. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6u_pending C40. sc_cell Hsc ds6u_status C8. rewrite Hst in C8.
  unfold pend_pc. destruct (Z.eqb_spec (ds_pending X) 0) as [Hz|Hnz].
  - rewrite Hz in C40.
    run 8%nat [false] [RVal (ELit 0); RVal (ELit 113)] NoBounds (@nil Z).
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros _; split; reg1 HR Hfr | fr_weak Hfr].
  - run 8%nat [true] [RVal (EVar 36)] [(36%nat, 2 ^ 63)] [ds_pending X].
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros Hc; exfalso; lia | fr_weak Hfr].
Qed.


Lemma g_blk : forall regs m,
  HREGS regs -> getr regs 13 = zw 113 ->
  exists R,
    msteps s6u_segs (mkst regs (0x171e4 : word) m s6u_rom) (mkst R (0x17db0 : word) m s6u_rom)
    /\ HREGS R
    /\ (forall r : reg, reg_in r [10; 11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m HRG P13. open_min. open_hregs HRG.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (13, ELit 113)] 16%nat
    [true; true; false; false] NoReads NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr | fr_weak Hfr].
Qed.

End Walk.
End FXG.

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
  FillWin6uA DeflBlkApi6u DeflKit6u FlushPend6u DeflSlow6u_8 DeflSlow6u_9 Defl6uApi Defl6u_1 Defl6u_2 Defl6u_3.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma cell_low2u : forall segs m a v, cell segs m a 8 v -> 0 <= a -> a + 8 <= 2 ^ 64 -> cell segs m a 2 v.
Proof.
  intros segs m a v H Ha Ha8. unfold cell in *.
  pose proof (rdn_firstn segs m 8 (zw a) _ 2 H ltac:(lia)) as H2. exact H2.
Qed.

Lemma byte1_of_low16 : forall a, 0 <= a -> (a / 2 ^ 8) mod 2 ^ 8 = ((a mod 2 ^ 16) / 2 ^ 8) mod 2 ^ 8.
Proof.
  intros a Ha.
  rewrite (Z.div_mod a (2 ^ 16)) at 1 by lia.
  replace (2 ^ 16 * (a / 2 ^ 16)) with ((2 ^ 8 * (a / 2 ^ 16)) * 2 ^ 8) by lia.
  rewrite Z.div_add_l by lia.
  rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. reflexivity.
Qed.
Lemma byte0_of_low16 : forall a, a mod 2 ^ 8 = (a mod 2 ^ 16) mod 2 ^ 8.
Proof. intros a. symmetry. apply Z.mod_mod_divide. exists (2 ^ 8). reflexivity. Qed.
Lemma byte3_of_hi16 : forall a, 0 <= a -> (a / 2 ^ 24) mod 2 ^ 8 = ((a / 2 ^ 16) / 2 ^ 8) mod 2 ^ 8.
Proof. intros a Ha. rewrite Z.div_div by lia. reflexivity. Qed.

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


Lemma bc74_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= cs_avail_in (ds_strm X) < 2 ^ 31 ->
  exists R,
    msteps s6u_segs (mkst regs (0x17db0 : word) m s6u_rom)
           (mkst R (if cs_avail_in (ds_strm X) =? 0 then (0x17dc0%bv : word) else (0x17dc8%bv : word)) m s6u_rom)
    /\ HREGS R /\ getr R 10 = zw strm /\ getr R 11 = zw flush
    /\ (forall r : reg, reg_in r [10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hai. open_di HDI. open_hregs HRG.
  zs_cell Zs (@zsl_avail_in) C8z.
  Local Ltac bc_fin R Hms HRG HR Hfr := exists R; split; [exact Hms|]; split; [hregs_via HRG Hfr|]; repeat (split; [reg1 HR Hfr|]); fr_weak Hfr.
  destruct (Z.eqb_spec (cs_avail_in (ds_strm X)) 0) as [Ea|Ea].
  - rewrite Ea in C8z.
    run 8%nat [false] [RVal (ELit 0)] NoBounds (@nil Z).
    bc_fin R Hms HRG HR Hfr.
  - pose proof (sx32_u64_nz (cs_avail_in (ds_strm X)) ltac:(lia)) as Hsx.
    run 8%nat [true] [RVal (EVar 36)] [(36%nat, 2 ^ 31)] [cs_avail_in (ds_strm X)].
    bc_fin R Hms HRG HR Hfr.
Qed.

Definition b84_pc (X : deflate_state) : word :=
  if bc64_cond X then (0x17dc8%bv : word) else if flush =? 0 then (0x17f78%bv : word) else (0x17f70%bv : word).

Lemma b84_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 11 = zw flush ->
  0 <= ds_lookahead X < 2 ^ 31 -> 0 <= ds_status X < 2 ^ 31 ->
  exists R,
    msteps s6u_segs (mkst regs (0x17dc0 : word) m s6u_rom) (mkst R (b84_pc X) m s6u_rom)
    /\ HREGS R /\ getr R 10 = getr regs 10 /\ getr R 11 = zw flush
    /\ (forall r : reg, reg_in r [12; 13]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG P11 Hlk Hst. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6u_lookahead C180. sc_cell Hsc ds6u_status C8.
  unfold b84_pc, Defl6_5.bc64_cond.
  destruct (Z.eqb_spec (ds_lookahead X) 0) as [El|El]; cbn [negb orb andb].
  - rewrite El in C180. destruct (Z.eqb_spec flush 0) as [Ef|Ef]; cbn [negb andb].
    + run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (11, EVar 34%nat)] 12%nat
        [true; true] [RVal (ELit 0)] NoBounds (@nil Z).
      bc_fin R Hms HRG HR Hfr.
    + destruct (Z.eqb_spec (ds_status X) 666) as [Es|Es]; cbn [negb].
      * rewrite Es in C8.
        run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (11, EVar 34%nat)] 14%nat
          [true; false; false] [RVal (ELit 0); RVal (ELit 666)] NoBounds (@nil Z).
        bc_fin R Hms HRG HR Hfr.
      * run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (11, EVar 34%nat)] 14%nat
          [true; false; true] [RVal (ELit 0); RVal (EVar 36)] [(36%nat, 2 ^ 31)] [ds_status X].
        bc_fin R Hms HRG HR Hfr.
  - run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (11, EVar 34%nat)] 12%nat
      [false] [RVal (EVar 36)] [(36%nat, 2 ^ 31)] [ds_lookahead X].
    bc_fin R Hms HRG HR Hfr.
Qed.


Lemma cfg6u_func_cell : forall m, rom_clear m 0x10000 0x2c3f8 -> cell s6u_segs m (0 + 180856) 8 0x19cf0.
Proof.
  intros m HR. unfold cell.
  rewrite (rdn_ext s6u_segs 8 m (fun _ => None) (zw (0 + 180856))); [| rewrite u_zw_small by lia; lia |].
  - etransitivity; [vm_compute; reflexivity|]. f_equal. apply bytes_eq_of_unsigned'. vm_compute. reflexivity.
  - intros x Hx. rewrite u_zw_small in Hx by lia. apply HR. lia.
Qed.

Lemma call_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> ds_level X = 6 -> ds_strategy X = 0 ->
  rom_clear m1 0x10000 0x2c3f8 ->
  exists R,
    msteps s6u_segs (mkst regs (0x17dc8 : word) m s6u_rom) (mkst R (0x19cf0 : word) m s6u_rom)
    /\ HREGS R /\ getr R 10 = zw S /\ getr R 11 = zw flush /\ getr R 2 = zw SP /\ getr R 1 = (0x17e4c%bv : word)
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hlv Hstr HR1. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6u_level C196. rewrite Hlv in C196. sc_cell Hsc ds6u_strategy C200. rewrite Hstr in C200.
  pose proof (cfg6u_func_cell m (img_DI m1 m X _ _ HDI HR1 ltac:(lia) ltac:(lia))) as CF.
  run 24%nat [false; false; true; false; false] [RVal (ELit 6); RVal (ELit 0); RVal (ELit 0x19cf0)] NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Lemma call_slowu : forall regs m1 m X,
  DI m1 m X -> SSAFE X flush ->
  getr regs 10 = zw S -> getr regs 11 = zw flush -> getr regs 2 = zw SP -> getr regs 1 = (0x17e4c%bv : word) ->
  exists R m',
    msteps s6u_segs (mkst regs (0x19cf0 : word) m s6u_rom) (mkst R (0x17e4c : word) m' s6u_rom)
    /\ DI m1 m' (fst (deflate_slow X flush))
    /\ getr R 10 = zw (bs_code (snd (deflate_slow X flush))) /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HSAFE P10 P11 P2 P1.
  pose proof HDI as (HB & HR & HS3). pose proof HS3 as (Ews & Ehs & Elbs).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HB as (_ & _ & _ & Hpb & Epbl & _).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN). unfold DEFL_K6u in Hsp.
  pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl. unfold DEFL_K6u, DEFL_FR6u in MF.
  assert (HL' : ZRH6u DSLOW_FRAME6u m S SP p zp X).
  { constructor.
    - unfold DSLOW_FRAME6u. lia.
    - unfold zr_regions, DSLOW_FRAME6u. rewrite Ews, Ehs, Elbs, Eout, Ein.
      pose proof (zrh_rng _ _ _ _ _ _ _ HL) as HRG0. unfold zr_regions, DEFL_K6u in HRG0.
      apply Forall_cons_iff in HRG0 as [_ HRG0]. constructor; [cbn [fst snd]; lia | exact HRG0].
    - rewrite Ein. exact (zrh_in _ _ _ _ _ _ _ HL).
    - exact (zrh_W _ _ _ _ _ _ _ HL).
    - exact (zrh_HD _ _ _ _ _ _ _ HL).
    - exact (zrh_PV _ _ _ _ _ _ _ HL).
    - unfold ZRF, DSLOW_FRAME6u. rewrite Ews, Ehs, Elbs, Eout.
      pose proof (zrh_map _ _ _ _ _ _ _ HL) as HM0. unfold ZRF, DEFL_K6u in HM0. apply Forall_cons_iff in HM0 as [_ HM0].
      constructor; [cbn [fst snd]; intros x Hx; apply MF; lia|].
      eapply Forall_impl; [| exact HM0]. intros [b k] Hb x Hx. apply HGR. exact (Hb x Hx).
    - unfold zr_regions, DSLOW_FRAME6u. rewrite Ews, Ehs, Elbs, Eout, Ein.
      pose proof (zrh_apart _ _ _ _ _ _ _ HL) as HA0. unfold zr_regions, DEFL_K6u in HA0.
      apply (Defl6_5.apart_all_shrink0 (sp - 528) 528); [exact HA0 | lia | lia | lia].
    - exact HRC.
    - intros x Hx Hi. apply (zrh_img _ _ _ _ _ _ _ HL x); [| exact Hi].
      unfold ZRF, DSLOW_FRAME6u, DEFL_K6u in *. rewrite Ews, Ehs, Elbs, Eout in Hx. cbn [in_franges] in Hx |- *. lia.
    - exact (zrh_O _ _ _ _ _ _ _ HL).
    - exact (zrh_S8 _ _ _ _ _ _ _ HL).
    - exact (zrh_S1 _ _ _ _ _ _ _ HL).
    - exact (zrh_strm1 _ _ _ _ _ _ _ HL).
    - exact (zrh_strm8 _ _ _ _ _ _ _ HL).
    - exact (zrh_HD2 _ _ _ _ _ _ _ HL).
    - exact (zrh_PV2 _ _ _ _ _ _ _ HL).
    - exact (zrh_PB1 _ _ _ _ _ _ _ HL).
    - exact (zrh_I _ _ _ _ _ _ _ HL). }
  assert (HZ : ZR6u m S p zp X).
  { unfold ZR6u, ds6u_windowA, ds6u_prevA, ds6u_headA, ds6u_arrays, ds6u_pendA. rewrite Epbl.
    repeat (split; [assumption|]). exact Zo. }
  destruct (SLOW m S p zp X flush (0x17e4c%bv : word) SP regs HL' ltac:(apply ret_ok_even; reflexivity) HZ HRD HSAFE Hfl P10 P11 P2 P1)
    as (R & m' & Hms & HZ' & A10 & A2 & Hfr & Hag & Hrod & Hrom & Hgr & Hk).
  unfold A6U_DEFLATE_SLOW in Hms. symex_pc_lit_in Hms.
  exists R, m'. split; [exact Hms|]. split; [| split; [exact A10 | split; [exact A2 | exact Hfr]]].
  set (X' := fst (deflate_slow X flush)) in *.
  destruct Hk as (Kws & Khs & Klbs & Kwl & Kpl & Khl & Kbl & Kin & Kout & Kao & Kol).
  rewrite Ews in Kws, Kwl, Kpl. rewrite Ehs in Khs, Khl. rewrite Elbs in Klbs, Kbl. rewrite Ein in Kin. rewrite Eout in Kout.
  destruct HZ' as (Zsc & Zar & Ztl & ZwA & ZpA & ZhA & ZbA & Zzs & Zzi & Zzo).
  assert (HFG : forall x, in_franges (ZRFo DSLOW_FRAME6u S SP p zp X (Z.of_nat (length (cs_out_rev (ds_strm X'))))) x ->
                          in_franges (GDo (ds_strm X')) x).
  { intros x Hx. unfold DeflKit6u.GDo. unfold ZRFo, DSLOW_FRAME6u, DEFL_K6u, DEFL_FR6u, ds6_SIZE, zsl_SIZE in Hx |- *. rewrite Ews, Ehs, Elbs in Hx.
    cbn [in_franges] in Hx |- *. lia. }
  assert (HFF : forall x, in_franges (ZRFo DSLOW_FRAME6u S SP p zp X (Z.of_nat (length (cs_out_rev (ds_strm X'))))) x ->
                          in_franges (DeflKit6u.Fd S p zp ds sp DEFL_K6u) x).
  { intros x Hx. apply (GD_Fd _ _ _ _ _ _ _ _ _ _ _ HH). apply (GDo_GD _ _ _ _ _ _ _ (ds_strm X')); [exact (HFG x Hx) | lia]. }
  split; [| split; [| exact (conj Kws (conj Khs Klbs))]].
  -
    unfold BR. unfold ds6u_pendA in ZbA. rewrite Kbl in ZbA.
    split; [exact Zsc|]. split; [exact Zar|]. split; [exact Ztl|]. split; [exact ZbA|]. split; [exact Kbl|].
    split; [eapply agree_out_trans; [exact HagF | eapply agree_out_weaken; [exact Hag | exact HFF]]|].
    split; [intros x Hx; apply Hgr; exact (MS x Hx)|]. split; [intros x Hx; apply Hgr; exact (MP x Hx)|].
    intros x Hx. apply Hgr. exact (HGR0 x Hx).
  -
    unfold DeflKit6u.RZ. unfold ds6u_windowA, ds6u_prevA, ds6u_headA in *.
    split; [exact ZwA|]. split; [exact ZpA|]. split; [exact ZhA|]. split; [exact Zzs|]. split; [exact Zzi|]. split; [exact Zzo|].
    split.
    + unfold DeflKit6u.RZmisc. split; [exact Hrod|]. split; [exact Hrom|].
      split; [eapply agree_out_trans; [eapply agree_out_weaken; [exact HAG | intros x Hx; eapply GDo_mono; [exact Hx | lia]]
                                    | eapply agree_out_weaken; [exact Hag | exact HFG]]|].
      split; [unfold DEFL_K6u; intros x Hx; apply Hgr; apply MF; exact Hx|].
      intros x Hx. apply Hgr. exact (HGR x Hx).
    + unfold DeflKit6u.CST. rewrite Kin. repeat (split; [first [assumption | reflexivity | lia]|]). lia.
Qed.


Definition bst_pc (X : deflate_state) (bs : block_state) : word :=
  match bs with
  | finish_done => (0x17f70%bv : word)
  | _ => if cs_avail_out (ds_strm X) =? 0 then (0x17ea0%bv : word) else (0x17f78%bv : word)
  end.

Lemma bst_blk : forall regs m1 m X bs,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw (bs_code bs) -> bs <> block_done ->
  0 <= cs_avail_out (ds_strm X) < 2 ^ 31 ->
  exists R M,
    msteps s6u_segs (mkst regs (0x17e4c : word) m s6u_rom) (mkst R (bst_pc X bs) M s6u_rom)
    /\ DI m1 M (bst_st X bs)
    /\ HREGS R /\ (bs = finish_done -> getr R 11 = zw flush /\ getr R 10 = zw strm)
    /\ (forall r : reg, reg_in r [10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X bs HDI HRG P10 Hbd Hav. open_di HDI. open_hregs HRG.
  zs_cell Zs (@zsl_avail_out) Z32.
  Local Ltac bst_fin Hms HDI HRG HR Hfr ks :=
    clear_aparts;
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) ks;
    ex2; split; [exact Hms|]; split; [the_DI|]; split; [hregs_via HRG Hfr|];
    split; [first [intros; discriminate | intros _; split; reg1 HR Hfr] | fr_weak Hfr].
  unfold bst_pc, Defl6_5.bst_st. destruct bs; [| exfalso; exact (Hbd eq_refl) | |]; cbn [bs_code] in P10.
  -
    destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
    + rewrite Hz in Z32.
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (10, ELit 0)] 14%nat
        [true; true; false] [RVal (ELit 0)] NoBounds (@nil Z).
      bst_fin Hms HDI HRG HR Hfr (@nil dkind).
    + pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (10, ELit 0)] 14%nat
        [true; true; true] [RVal (EVar 36)] [(36%nat, 2 ^ 32)] [cs_avail_out (ds_strm X)].
      bst_fin Hms HDI HRG HR Hfr (@nil dkind).
  -
    apartF 1%nat 6%nat A16.
    destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
    + rewrite Hz in Z32.
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (10, ELit 2)] 16%nat
        [false; true; false] [RVal (ELit 0)] NoBounds (@nil Z).
      bst_fin Hms HDI HRG HR Hfr [KStatus].
    + pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (10, ELit 2)] 16%nat
        [false; true; true] [RVal (EVar 36)] [(36%nat, 2 ^ 32)] [cs_avail_out (ds_strm X)].
      bst_fin Hms HDI HRG HR Hfr [KStatus].
  -
    apartF 1%nat 6%nat A16.
    run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (10, ELit 3)] 16%nat
      [false; false; true] NoReads NoBounds (@nil Z).
    bst_fin Hms HDI HRG HR Hfr [KStatus].
Qed.


Definition t30_pc (X : deflate_state) : word :=
  if negb (flush =? 4) then (0x17f78%bv : word) else if ds_wrap X <=? 0 then (0x1814c%bv : word) else (0x18288%bv : word).

Lemma t30_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw strm -> getr regs 11 = zw flush ->
  (ds_wrap X = 1 \/ ds_wrap X = -1) -> 0 <= cs_adler (ds_strm X) < 2 ^ 32 ->
  exists R,
    msteps s6u_segs (mkst regs (0x17f70 : word) m s6u_rom) (mkst R (t30_pc X) m s6u_rom)
    /\ HREGS R
    /\ (flush = 4 -> 0 < ds_wrap X -> getr R 10 = zw S /\ getr R 11 = zw (cs_adler (ds_strm X) / 2 ^ 16) /\ getr R 1 = (0x18164%bv : word))
    /\ (forall r : reg, reg_in r [1; 10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG P10 P11 Hw Had. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6u_wrap C48. zs_cell Zs (@zsl_adler) Z96.
  unfold t30_pc.
  Local Ltac t30_fin Hms HRG HR Hfr :=
    ex1; split; [exact Hms|]; split; [hregs_via HRG Hfr|];
    split; [first [intros Hc; exfalso; lia | intros _ Hc; exfalso; lia | intros _ _; repeat split; reg1 HR Hfr] | fr_weak Hfr].
  destruct (Z.eqb_spec flush 4) as [Ef|Ef]; cbn [negb].
  - destruct Hw as [Ew|Ew]; rewrite Ew in C48 |- *; cbn [Z.leb Z.compare].
    + run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (10, EVar 35%nat); (11, EVar 34%nat)] 16%nat
        [true; false; true] [RVal (ELit 1); RVal (EVar 36)] [(36%nat, 2 ^ 32)] [cs_adler (ds_strm X)].
      t30_fin Hms HRG HR Hfr.
    + assert (RD48 : exists bs, rdn s6u_segs m (zw (S + 48)) 4 = Some bs /\ bytes_le_to_Z bs = 4294967295)
        by exact (cell_read_at s6u_segs m (S + 48) 4 _ _ C48 eq_refl).
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (10, EVar 35%nat); (11, EVar 34%nat)] 8%nat
        [true; true] [RVal (ELit 4294967295)] NoBounds (@nil Z).
      t30_fin Hms HRG HR Hfr.
  - run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (10, EVar 35%nat); (11, EVar 34%nat)] 4%nat
      [false] NoReads NoBounds (@nil Z).
    t30_fin Hms HRG HR Hfr.
Qed.


Lemma t24_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= cs_adler (ds_strm X) ->
  exists R,
    msteps s6u_segs (mkst regs (0x18164 : word) m s6u_rom) (mkst R (0x18288 : word) m s6u_rom)
    /\ HREGS R /\ getr R 10 = zw S /\ getr R 11 = zw (cs_adler (ds_strm X) mod 2 ^ 16) /\ getr R 1 = (0x18170%bv : word)
    /\ (forall r : reg, reg_in r [1; 10; 11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Had. open_di HDI. open_hregs HRG.
  zs_cell Zs (@zsl_adler) Z96.
  pose proof (cell_low2u s6u_segs m (strm + 96) _ Z96 ltac:(lia) ltac:(lia)) as Z96_2.
  assert (RD96 : exists bs, rdn s6u_segs m (zw (strm + 96)) 2 = Some bs /\ bytes_le_to_Z bs = cs_adler (ds_strm X) mod 2 ^ 16)
    by exact (cell_read_at s6u_segs m (strm + 96) 2 _ _ Z96_2 eq_refl).
  pose proof (Z.mod_pos_bound (cs_adler (ds_strm X)) (2 ^ 16) ltac:(lia)) as Hmb.
  run 8%nat NoDirs [RVal (EVar 36)] [(36%nat, 2 ^ 16)] [cs_adler (ds_strm X) mod 2 ^ 16].
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Lemma t30b_blk : forall regs m,
  HREGS regs ->
  exists R,
    msteps s6u_segs (mkst regs (0x18170 : word) m s6u_rom) (mkst R (0x181ac : word) m s6u_rom)
    /\ HREGS R /\ getr R 10 = zw strm /\ getr R 1 = (0x18178%bv : word)
    /\ (forall r : reg, reg_in r [1; 10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m HRG. open_min. open_hregs HRG.
  run 4%nat NoDirs NoReads NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Lemma DI_st_wrap' : forall m1 m X v v' a, DI m1 m X -> a = S + 48 -> v' mod 2 ^ 32 = v mod 2 ^ 32 ->
  DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_wrap X v').
Proof.
  intros m1 m X v v' a HDI Ha Ev.
  rewrite (DeflSlow6_1.Z_to_le_bytes_mod_eq 4 v v') by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); symmetry; exact Ev).
  exact (DI_st_wrap m1 m X v' a HDI Ha).
Qed.

Lemma t38_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> (ds_wrap X = 1 \/ ds_wrap X = -1) -> 0 <= ds_pending X < 2 ^ 63 ->
  exists R M,
    msteps s6u_segs (mkst regs (0x18178 : word) m s6u_rom) (mkst R (0x17eac : word) M s6u_rom)
    /\ DI m1 M (t2_st X)
    /\ getr R 2 = zw SP /\ getr R 12 = zw (if ds_pending X =? 0 then 1 else 0)
    /\ (forall r : reg, reg_in r [10; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hw Hpd. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6u_wrap C48. sc_cell Hsc ds6u_pending C40.
  unfold Defl6_6.t2_st.
  destruct Hw as [Ew|Ew]; rewrite Ew in C48 |- *; cbn [Z.ltb Z.compare Z.opp].
  - apartF 1%nat 6%nat A16.
    destruct (Z.eqb_spec (ds_pending X) 0) as [Hz|Hnz].
    + rewrite Hz in C40.
      run 16%nat [false] [RVal (ELit 1); RVal (ELit 0)] NoBounds (@nil Z).
      clear_aparts.
      lazymatch type of Hms with msteps _ _ (mkst _ _ (wbytes ?M1 (zw ?a) (Z_to_le_bytes 4 ?v)) _) =>
        pose proof (DI_st_wrap' m1 M1 X v (-1) a HDI ltac:(lia) ltac:(reflexivity)) as HDI2 end.
      ex2. split; [exact Hms|]. split; [first [exact HDI2 | rewrite Ew; exact HDI2]|]. split; [reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
    + run 16%nat [false] [RVal (ELit 1); RVal (EVar 36)] [(36%nat, 2 ^ 63)] [ds_pending X].
      clear_aparts.
      lazymatch type of Hms with msteps _ _ (mkst _ _ (wbytes ?M1 (zw ?a) (Z_to_le_bytes 4 ?v)) _) =>
        pose proof (DI_st_wrap' m1 M1 X v (-1) a HDI ltac:(lia) ltac:(reflexivity)) as HDI2 end.
      ex2. split; [exact Hms|]. split; [first [exact HDI2 | rewrite Ew; exact HDI2]|]. split; [reg1 HR Hfr|].
      split; [symex_reg HR (12%bv : reg) as A12; rewrite A12; f_equal; destruct (Z.ltb_spec (ds_pending X) 1); lia | fr_weak Hfr].
  - assert (RD48 : exists bs, rdn s6u_segs m (zw (S + 48)) 4 = Some bs /\ bytes_le_to_Z bs = 4294967295)
      by exact (cell_read_at s6u_segs m (S + 48) 4 _ _ C48 eq_refl).
    destruct (Z.eqb_spec (ds_pending X) 0) as [Hz|Hnz].
    + rewrite Hz in C40.
      run 12%nat [true] [RVal (ELit 4294967295); RVal (ELit 0)] NoBounds (@nil Z).
      ex2. split; [exact Hms|]. split; [exact HDI|]. split; [reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
    + run 12%nat [true] [RVal (ELit 4294967295); RVal (EVar 36)] [(36%nat, 2 ^ 63)] [ds_pending X].
      ex2. split; [exact Hms|]. split; [exact HDI|]. split; [reg1 HR Hfr|].
      split; [symex_reg HR (12%bv : reg) as A12; rewrite A12; f_equal; destruct (Z.ltb_spec (ds_pending X) 1); lia | fr_weak Hfr].
Qed.

Lemma trl_st_equ : forall X, let a := cs_adler (ds_strm X) in
  psm_st (psm_st X (a / 2 ^ 24) (a / 2 ^ 16)) (a / 2 ^ 8) a = trl_st X.
Proof.
  intros X a. unfold psm_st, Defl6_6.trl_st. cbv zeta. dsred. subst a.
  replace (ds_pending X + 2 + 1) with (ds_pending X + 3) by lia.
  replace (ds_pending X + 2 + 2) with (ds_pending X + 4) by lia.
  destruct X. reflexivity.
Qed.

End Walk.
End FXG.

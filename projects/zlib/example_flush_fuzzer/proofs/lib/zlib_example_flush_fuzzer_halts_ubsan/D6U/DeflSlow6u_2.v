(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import DS6 CalleeKits6 DeflSlow6_1 DeflSlow6_2 DeflSlow6_3 DeflSlow6_4 DeflSlow6_5 DeflSlow6_5b DeflSlow6_6 DeflSlow6_7 DeflSlow6_M.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u Callee6u TreesRod6u TreesApi6u TrApi6u
  Lmatch6u_run FillWin6uA FillWin6uD DeflBlkApi6u DeflKit6u DeflSlow6u_1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
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
Local Abbreviation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Abbreviation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Abbreviation AV0 := (cs_avail_out (ds_strm ds)).
Local Abbreviation SP := (sp - 128).
Hypothesis HH : DKH ROM mem S p zp ds flush ra sp DSLOW_FRAME6u DSLOW_FR6u.
Hypothesis MEMCPY : memcpy_run6u.
Hypothesis MEMSET : memset_run6u.
Hypothesis ADLER : adler32_run6u ROM.
Hypothesis TFBITS : tr_flush_bits_run6u.
Variable FBSAFE : deflate_state -> option Z -> Z -> Z -> Prop.
Hypothesis TFB : tr_flush_block_run6u FBSAFE.
Local Abbreviation DI := (DeflKit6u.DI ROM mem S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).
Local Abbreviation BRm := (BR s6u_segs 180992 181024 181056 (DeflKit6u.Fd S p zp ds sp DSLOW_FRAME6u) mem S p PBL).
Local Abbreviation RZ := (DeflKit6u.RZ ROM mem S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).
Local Abbreviation GD := (DeflKit6u.GD S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).
Local Abbreviation GDo := (DeflKit6u.GDo S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).
Local Abbreviation DI_eqst := (DeflKit6u.DI_eqst ROM mem S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).

Let HL : ZRH6u DSLOW_FRAME6u mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ _ _ HH.
Let HRL : rom_local6u ROM := dsh_roml _ _ _ _ _ _ _ _ _ _ _ HH.
Local Abbreviation HREGS := (DeflSlow6u_1.HREGS S flush sp).
Local Abbreviation HREGS_via3 := (DeflSlow6u_1.HREGS_via S flush sp).
Local Abbreviation LOC := (DeflSlow6u_1.LOC sp).
Local Abbreviation LOC_DI := (DeflSlow6u_1.LOC_DI ROM mem S p zp ds flush ra sp HH).
Local Abbreviation avail0_st := DeflSlow6_3.avail0_st.
Local Abbreviation avail0_blk := (DeflSlow6u_1.avail0_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation head_pc := DeflSlow6u_1.head_pc.
Local Abbreviation head_blk := (DeflSlow6u_1.head_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation fillr_pc := (DeflSlow6u_1.fillr_pc flush).
Local Abbreviation fillr_blk := (DeflSlow6u_1.fillr_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation ret0_blk := (DeflSlow6u_1.ret0_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation ltail_st := DeflSlow6_2.ltail_st.
Local Abbreviation ltail_blk := (DeflSlow6u_1.ltail_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation avail_pc := DeflSlow6_6.avail_pc.
Local Abbreviation avo_blk := (DeflSlow6u_1.avo_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation ins_str := DeflSlow6_2.ins_str.
Local Abbreviation prev_st := DeflSlow6_2.prev_st.
Local Abbreviation PLR := DeflSlow6_2.PLR.
Local Abbreviation lm_filter := DeflSlow6_3.lm_filter.
Local Abbreviation dec_cond := DeflSlow6_3.dec_cond.
Local Ltac unhide H := unfold hidden in H.
Local Ltac norm_sx H := rewrite ?le_bytes_sx32 in H.

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac hregs_via HRG Hfr := apply (HREGS_via3 _ _ _ HRG Hfr); reflexivity.

Local Ltac nf := cbn [dfF].

Local Ltac rod_read :=
  lazymatch goal with
  | |- exists bs, rdn _ ?m (zw ?a) _ = Some bs /\ bytes_le_to_Z bs = arr_get length_code_a ?i =>
      eapply (length_code_read R6u s6u_segs m trod_ok6u ltac:(eassumption) i a); first [reflexivity | cbn [tr_length_code R6u]; lia]
  | |- exists bs, rdn _ ?m (zw ?a) _ = Some bs /\ bytes_le_to_Z bs = arr_get dist_code_a ?i =>
      eapply (dist_code_read R6u s6u_segs m trod_ok6u ltac:(eassumption) i a); first [reflexivity | cbn [tr_dist_code R6u]; lia]
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
            | apply even_plus_shl1; [assumption | lia | nf; lia]
            | nf; change (2 ^ 3) with 8 in *; change (2 ^ 1) with 2 in *; zcond_close
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
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs dsCu fuel dirs rdv pins vb NoRegions pv NoVals
          (dfF (ds_window X) (ds_head X) (ds_dyn_ltree_fc X) (ds_dyn_dtree_fc X)) F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
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
  let HRT := fresh "HRT" in let HGOT := fresh "HGOT" in pose proof (proj1 HRC) as HRT; pose proof (proj2 HRC) as HGOT; unfold got6u_clear in HGOT;
  let Lw := fresh "Lw" in let Lp := fresh "Lp" in let Lh := fresh "Lh" in
  let Ein := fresh "Ein" in let Eout := fresh "Eout" in let Hao := fresh "Hao" in let Hol := fresh "Hol" in
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol); rewrite Lw in Cw; rewrite Lp in Cp; rewrite Lh in Ch;
  let RF := fresh "RF" in
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in let HW := fresh "HW" in let HPV := fresh "HPV" in let HHD := fresh "HHD" in
  let HPB := fresh "HPB" in let Hstrm := fresh "Hstrm" in let HOUT := fresh "HOUT" in let HIN := fresh "HIN" in
  destruct RF as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN);
  let RODS := fresh "RODS" in pose proof (mapped_rod_apart R6u s6u_segs _ S 5968 trod_ok6u HRT MS ltac:(lia) ltac:(lia)) as RODS;
  let RODP := fresh "RODP" in pose proof (mapped_rod_apart R6u s6u_segs _ (p_pending_buf p) PBL trod_ok6u HRT MP ltac:(lia) ltac:(pose proof (wf_lbs _ HWF); lia)) as RODP;
  cbn [tr_lo tr_hi tr_sdesc R6u] in RODS, RODP; apply hide in RODS; apply hide in RODP;
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl;
  let HGR := fresh "HGR" in pose proof HRZ as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & HGR) & _);
  let MWm := fresh "MWm" in let MPm := fresh "MPm" in let MHm := fresh "MHm" in let MZm := fresh "MZm" in
  let T := fresh "T" in
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 2 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MWm; cbv beta in MWm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 3 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MPm; cbv beta in MPm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 4 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MHm; cbv beta in MHm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 6 ltac:(lia)) as T; unfold ZRF, zsl_SIZE in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MZm; cbv beta in MZm; clear T;
  let US8 := fresh "US8" in let US1 := fresh "US1" in let UST1 := fresh "UST1" in let UST8 := fresh "UST8" in
  let UPB1 := fresh "UPB1" in let UO := fresh "UO" in let UHD2 := fresh "UHD2" in let UPV2 := fresh "UPV2" in let UI := fresh "UI" in
  pose proof (zrh_S8 _ _ _ _ _ _ _ HL) as US8; pose proof (zrh_S1 _ _ _ _ _ _ _ HL) as US1;
  pose proof (zrh_strm1 _ _ _ _ _ _ _ HL) as UST1; pose proof (zrh_strm8 _ _ _ _ _ _ _ HL) as UST8;
  pose proof (zrh_PB1 _ _ _ _ _ _ _ HL) as UPB1; pose proof (zrh_O _ _ _ _ _ _ _ HL) as UO;
  pose proof (zrh_HD2 _ _ _ _ _ _ _ HL) as UHD2; pose proof (zrh_PV2 _ _ _ _ _ _ _ HL) as UPV2; pose proof (zrh_I _ _ _ _ _ _ _ HL) as UI;
  let UHD := fresh "UHD" in let UPV := fresh "UPV" in let UW := fresh "UW" in
  pose proof (zrh_HD _ _ _ _ _ _ _ HL) as UHD; pose proof (zrh_PV _ _ _ _ _ _ _ HL) as UPV; pose proof (zrh_W _ _ _ _ _ _ _ HL) as UW;
  unfold DSLOW_FRAME6u in Hsp, MF.

Local Ltac apartF i j H :=
  pose proof (apart_ij _ _ _ _ _ _ _ _ _ _ _ HH i j ltac:(lia) ltac:(lia)) as H;
  unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE, DSLOW_FRAME6u, DSLOW_FR6u in H.

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P19 := fresh "P19" in let P20 := fresh "P20" in
  let P27 := fresh "P27" in let P21 := fresh "P21" in let P18 := fresh "P18" in let P22 := fresh "P22" in let P23 := fresh "P23" in
  let P25 := fresh "P25" in let P26 := fresh "P26" in let P24 := fresh "P24" in
  pose proof HRG as (P8 & P2 & P9 & P19 & P20 & P27 & P21 & P18 & P22 & P23 & P25 & P26 & P24).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 | rewrite sxaddm16 | rewrite sxaddm8 ].

Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].

Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac di_fwd_rec HDI M ks :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) ?bs =>
      lazymatch ks with
      | ?k :: ?rest =>
          di_fwd_rec HDI M1 rest;
          lazymatch goal with
          | H1 : DeflKit6u.DI _ ?mem ?S ?p ?zp ?ds ?sp _ _ ?m1 M1 ?X |- _ =>
              let H2 := fresh "HDI" in
              lazymatch k with
              | KInsH => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_ins_h ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KBlockStart => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_block_start ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KMatchLength => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_match_length ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KStrstart => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_strstart ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KLookahead => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_lookahead ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KInsert => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_insert ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KSymNext => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_sym_next ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPending => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_pending ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPrevLength => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_prev_length ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPrevMatch => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_prev_match ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KMatchAvailable => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_match_available ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPendingOut ?off => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_pending_out ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X off a v H1 ltac:(lia) ltac:(lia)) as H2 end
              | KPb ?i ?c' => lazymatch bs with Z_to_le_bytes _ ?c =>
                  pose proof (DI_st_pb ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a i c c' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KFc ?t ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_fc ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a t i v v' H1 ltac:(cbn [toff]; lia) ltac:(cbn [tsize]; lia) ltac:(mod_side)) as H2 end
              | KPrev ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_prev ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a i v v' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KHead ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_head ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a i v v' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KFrame => pose proof (DI_st_frame ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a bs H1 ltac:(lia)
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
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in
  destruct RF as (Hsp & HS & _); unfold DSLOW_FRAME6u in Hsp;
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl.

Local Ltac ex1 := lazymatch goal with H : msteps _ _ (mkst ?R _ _ _) |- _ => exists R end.
Local Ltac ex2 := lazymatch goal with H : msteps _ _ (mkst ?R _ ?M _) |- _ => exists R, M end.

Local Ltac the_DI := lazymatch goal with H : DeflKit6u.DI _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact H end.
Local Ltac eq_DI := lazymatch goal with H : DeflKit6u.DI _ _ _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end.



Lemma ins_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs ->
  0 <= ds_strstart X -> ds_strstart X + 3 <= 2 * ws ->
  0 <= ds_ins_h X < 2 ^ 31 -> ds_hash_mask X = hs - 1 -> ds_w_mask X = ws - 1 -> 0 <= ds_hash_shift X < 32 ->
  (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256) ->
  (forall j, 0 <= j < hs -> 0 <= arr_get (ds_head X) j < 65536) ->
  let str := ds_strstart X in
  let h := update_hash X (ds_ins_h X) (arr_get (ds_window X) (str + 2)) in
  let hh := arr_get (ds_head X) h in
  exists R M,
    msteps s6u_segs (mkst regs (0x19dd0 : word) m s6u_rom) (mkst R (0x19ea0 : word) M s6u_rom)
    /\ DI m1 M (ins_str X str)
    /\ HREGS R /\ getr R 11 = zw hh /\ getr R 10 = zw str
    /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14; 15]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hs0 Hs3 Hih Hhm Hwm Hsh Hwb Hhb str h hh.
  open_di HDI. open_hregs HRG.
  pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws. pose proof (DeflSlow6_1.wf_hsz _ HWF) as Whs.
  pose proof (ds6u_strstart _ _ _ _ Hsc) as C172. pose proof (ds6u_window _ _ _ _ Hsc) as C96.
  pose proof (ds6u_hash_shift _ _ _ _ Hsc) as C144. pose proof (ds6u_ins_h _ _ _ _ Hsc) as C128.
  pose proof (ds6u_hash_mask _ _ _ _ Hsc) as C140. pose proof (ds6u_w_mask _ _ _ _ Hsc) as C88.
  pose proof (ds6u_head _ _ _ _ Hsc) as C120. pose proof (ds6u_prev _ _ _ _ Hsc) as C112.
  rewrite Hhm in C140. rewrite Hwm in C88.
  set (hx := Z.land (Z.lxor (zaluw ALU_SLL (ds_ins_h X) (ds_hash_shift X)) (wb (ds_window X) (str + 2))) (hs - 1)).
  assert (Ehx : hx = h).
  { subst hx h. rewrite (wb_get (ds_window X) ltac:(intros j Hj; apply Hwb; rewrite <- Lw; exact Hj)) by (rewrite Lw; lia).
    rewrite <- Hhm. apply update_hash_sllw; try reflexivity; lia. }
  pose proof (land_mask_range (Z.lxor (zaluw ALU_SLL (ds_ins_h X) (ds_hash_shift X)) (wb (ds_window X) (str + 2))) (hs - 1) ltac:(lia)) as Rhx.
  fold hx in Rhx.
  set (Y := Z.land (ws - 1) str).
  assert (RY : 0 <= Y <= ws - 1) by (subst Y; rewrite Z.land_comm; apply land_mask_range; lia).
  assert (Rhh : 0 <= hh < 65536) by (subst hh; apply Hhb; rewrite <- Ehx; lia).
  assert (Epb : pb (ds_head X) hx = hh) by (subst hh; rewrite <- Ehx; apply pb_get; [intros j Hj; apply Hhb; rewrite <- Lh; exact Hj | rewrite Lh; lia]).
  apartF 1%nat 3%nat A13. apartF 1%nat 4%nat A14.
  run 60%nat [false; false; false; false; false; false; false; false; false; false; false; false; false]
    [RVal (EVar 37); RVal (EVar 35); RVal (EVar 36); RVal (EVar 38); RVal (EApp1 0%nat (EAdd (EVar 35) (ELit 2))); RVal (EVar 39); RVal (EVar 40);
     RVal (EVar 41); RVal (EVar 42); RVal (EVar 43)]
    NoPins
    [(35%nat, 65537); (36%nat, 2 ^ 63); (37%nat, 32); (38%nat, 2 ^ 31); (39%nat, 65536); (40%nat, 2 ^ 63); (41%nat, 65536); (42%nat, 2 ^ 63); (43%nat, 65536)]
    [str; W; ds_hash_shift X; ds_ins_h X; hs - 1; HD; ws - 1; PV; pb (ds_head X) hx] X.
  clear_aparts. rewrite ?dfF_0, ?dfF_1, ?dfF_2, ?dfF_3 in Hms. norm_sx Hms.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end)
    [KInsH; KPrev Y (arr_get (ds_head X) hx); KHead hx (wrap16 str)].
  ex2. split; [exact Hms|].
  split.
  { eq_DI. change (ins_str X str) with
      (set_head (set_prev (set_ins_h X h) (arr_set (ds_prev X) (Z.land str (ds_w_mask X)) hh)) (arr_set (ds_head X) h (wrap16 str))).
    subst hh. rewrite <- Ehx. st_close ltac:(first [subst hx; reflexivity | rewrite Hwm; apply Z.land_comm]). }
  split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.


Lemma nil_blk : forall regs m,
  HREGS regs ->
  exists R,
    msteps s6u_segs (mkst regs (0x19e9c : word) m s6u_rom) (mkst R (0x19ea0 : word) m s6u_rom)
    /\ HREGS R /\ getr R 11 = zw 0
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m HRG. open_hregs HRG. open_min.
  run 3%nat NoDirs NoReads NoPins NoBounds (@nil Z) ds.
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.


Definition setup_pc (X : deflate_state) (hh : Z) : word :=
  if hh =? 0 then (0x19f20 : word)
  else if ds_max_lazy_match X <=? ds_match_length X then (0x19f20 : word)
  else if wrap32 (ds_strstart X - hh) <=? ws - 262 then (0x1a648 : word) else (0x19f20 : word).

Lemma setup_blk : forall regs m1 m X hh,
  DI m1 m X -> HREGS regs -> getr regs 11 = zw hh -> 0 <= hh < 65536 ->
  0 <= ds_strstart X <= 2 * ws ->
  0 <= ds_match_length X <= 258 -> 0 <= ds_match_start X < 2 ^ 32 -> 0 <= ds_max_lazy_match X < 2 ^ 31 ->
  exists R M,
    msteps s6u_segs (mkst regs (0x19ea0 : word) m s6u_rom) (mkst R (setup_pc X hh) M s6u_rom)
    /\ DI m1 M (prev_st X)
    /\ HREGS R /\ getr R 11 = zw hh
    /\ (setup_pc X hh = (0x1a648%bv : word) -> getr R 10 = zw S /\ getr R 1 = (0x19ee0%bv : word))
    /\ (setup_pc X hh <> (0x1a648%bv : word) -> getr R 10 = zw 2)
    /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r [1; 10; 12; 13]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X hh HDI HRG Q11 Rhh Hstr Hml Hms0 Hlz.
  open_di HDI. open_hregs HRG. pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof (ds6u_strstart _ _ _ _ Hsc) as C172. pose proof (ds6u_match_length _ _ _ _ Hsc) as C160.
  pose proof (ds6u_match_start _ _ _ _ Hsc) as C176. pose proof (ds6u_max_lazy_match _ _ _ _ Hsc) as C192.
  pose proof (ds6u_w_size _ _ _ _ Hsc) as C80. rewrite Ews in C80.
  unfold setup_pc.
  Local Ltac setup_fin HDI Hms HRG HR Hfr X :=
    clear_aparts; norm_sx Hms;
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KMatchLength; KPrevMatch; KPrevLength];
    lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end;
    split; [exact Hms|];
    split; [eq_DI; unfold DeflSlow6_2.prev_st; st_close idtac|];
    split; [hregs_via HRG Hfr|];
    split; [reg1 HR Hfr|];
    split; [let HX := fresh "HX" in intros HX; first [exfalso; discriminate HX | split; reg1 HR Hfr]|];
    split; [let HX := fresh "HX" in intros HX; first [exfalso; apply HX; reflexivity | reg1 HR Hfr]|];
    split; [reg1 HR Hfr | fr_weak Hfr].
  destruct (Z.eqb_spec hh 0) as [Hz|Hnz].
  - subst hh.
    run 12%nat [true] [RVal (EVar 36); RVal (EVar 35)] [(11, ELit 0)]
      [(35%nat, 259); (36%nat, 2 ^ 32)] [ds_match_length X; ds_match_start X] X.
    setup_fin HDI Hms HRG HR Hfr X.
  - assert (Hc1 : szwrap 32 (ws + -262) mod 2 ^ 64 = ws - 262) by (rewrite (szwrap_small 32) by lia; rewrite Z.mod_small by lia; lia).
    assert (Hc2 : szwrap 32 (ds_strstart X - hh) mod 2 ^ 64 <= ws - 262 <-> wrap32 (ds_strstart X - hh) <= ws - 262)
      by (apply szwrap32_u64_le; lia).
    destruct (Z.leb_spec (ds_max_lazy_match X) (ds_match_length X)) as [Hlazy|Hlazy].
    + run 16%nat [false; true] [RVal (EVar 36); RVal (EVar 35); RVal (EVar 38)] [(11, EVar 37%nat)]
        [(35%nat, 259); (36%nat, 2 ^ 32); (37%nat, 65536); (38%nat, 2 ^ 31)]
        [ds_match_length X; ds_match_start X; hh; ds_max_lazy_match X] X.
      setup_fin HDI Hms HRG HR Hfr X.
    + destruct (Z.leb_spec (wrap32 (ds_strstart X - hh)) (ws - 262)) as [Hnear|Hfar].
      * run 20%nat [false; false; false] [RVal (EVar 36); RVal (EVar 35); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40)] [(11, EVar 37%nat)]
          [(35%nat, 259); (36%nat, 2 ^ 32); (37%nat, 65536); (38%nat, 2 ^ 31); (39%nat, 65537); (40%nat, 65536)]
          [ds_match_length X; ds_match_start X; hh; ds_max_lazy_match X; ds_strstart X; ws] X.
        setup_fin HDI Hms HRG HR Hfr X.
      * run 20%nat [false; false; true] [RVal (EVar 36); RVal (EVar 35); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40)] [(11, EVar 37%nat)]
          [(35%nat, 259); (36%nat, 2 ^ 32); (37%nat, 65536); (38%nat, 2 ^ 31); (39%nat, 65537); (40%nat, 65536)]
          [ds_match_length X; ds_match_start X; hh; ds_max_lazy_match X; ds_strstart X; ws] X.
        setup_fin HDI Hms HRG HR Hfr X.
Qed.


Definition lmret_pc (X : deflate_state) (ml : Z) : word :=
  if lm_filter X ml then (0x19ef8 : word) else (0x19f20 : word).

Lemma lmret_blk : forall regs m1 m X ml,
  DI m1 m X -> HREGS regs -> LOC m1 -> getr regs 10 = zw ml -> 0 <= ml <= 258 -> 0 <= ds_strategy X <= 4 ->
  0 <= ds_strstart X <= 2 * ws -> 0 <= ds_match_start X < 2 ^ 32 ->
  exists R M,
    msteps s6u_segs (mkst regs (0x19ee0 : word) m s6u_rom) (mkst R (lmret_pc X ml) M s6u_rom)
    /\ DI m1 M (set_match_length X ml)
    /\ HREGS R /\ (lm_filter X ml = false -> getr R 10 = zw ml)
    /\ (forall r : reg, reg_in r [10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X ml HDI HRG HLOC Q10 Hml Hst Hstr Hms0. open_di HDI. open_hregs HRG. pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof (ds6u_strategy _ _ _ _ Hsc) as C200. pose proof (ds6u_strstart _ _ _ _ Hsc) as C172. pose proof (ds6u_match_start _ _ _ _ Hsc) as C176.
  pose proof (LOC_DI m1 m X HLOC HDI) as (F16 & F8).
  assert (Hc2 : szwrap 32 (ds_strstart X - ds_match_start X) mod 2 ^ 64 <= 4096 <-> wrap32 (ds_strstart X - ds_match_start X) <= 4096)
    by (apply sx32_u64_le_wrap; lia).
  apartF 0%nat 1%nat A01.
  Local Ltac lmret_fin HDI Hms HRG HR Hfr X ml :=
    clear_aparts;
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KMatchLength];
    lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end;
    split; [exact Hms|];
    split; [the_DI|];
    split; [hregs_via HRG Hfr|];
    split; [let HX := fresh "HX" in intros HX; first [exfalso; discriminate HX | reg1 HR Hfr]|];
    fr_weak Hfr.
  unfold lmret_pc, DeflSlow6_3.lm_filter.
  destruct (Z.leb_spec ml 5) as [M5|M5]; cbn [andb].
  2: { run 6%nat [true] NoReads [(10, EVar 35%nat)] [(35%nat, 259)] [ml] X. lmret_fin HDI Hms HRG HR Hfr X ml. }
  destruct (Z.eqb_spec (ds_strategy X) 1) as [S1|S1]; cbn [orb].
  { rewrite S1 in C200.
    run 8%nat [false; false] [RVal (ELit 1)] [(10, EVar 35%nat)] [(35%nat, 259)] [ml] X. lmret_fin HDI Hms HRG HR Hfr X ml. }
  destruct (Z.eqb_spec ml 3) as [M3|M3]; cbn [andb].
  2: { run 8%nat [false; true; true] [RVal (EVar 36)] [(10, EVar 35%nat)] [(35%nat, 259); (36%nat, 5)] [ml; ds_strategy X] X.
       lmret_fin HDI Hms HRG HR Hfr X ml. }
  subst ml.
  destruct (Z.ltb_spec 4096 (wrap32 (ds_strstart X - ds_match_start X))) as [Far|Near].
  - run 14%nat [false; true; false; true] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (ELit 4097)] [(10, ELit 3)]
        [(36%nat, 5); (37%nat, 65537); (38%nat, 2 ^ 32)] [0; ds_strategy X; ds_strstart X; ds_match_start X] X.
    lmret_fin HDI Hms HRG HR Hfr X 3.
  - run 14%nat [false; true; false; false] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (ELit 4097)] [(10, ELit 3)]
        [(36%nat, 5); (37%nat, 65537); (38%nat, 2 ^ 32)] [0; ds_strategy X; ds_strstart X; ds_match_start X] X.
    lmret_fin HDI Hms HRG HR Hfr X 3.
Qed.

Lemma lm2_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs ->
  exists R M,
    msteps s6u_segs (mkst regs (0x19ef8 : word) m s6u_rom) (mkst R (0x19f20 : word) M s6u_rom)
    /\ DI m1 M (set_match_length X 2)
    /\ HREGS R /\ getr R 10 = zw 2
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG. open_di HDI. open_hregs HRG.
  run 4%nat NoDirs NoReads NoPins NoBounds (@nil Z) X.
  clear_aparts.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KMatchLength].
  ex2. split; [exact Hms|]. split; [the_DI|].
  split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.


Definition dec_pc (X : deflate_state) : word := if dec_cond X then (0x19f2c : word) else (0x1a180 : word).

Lemma dec_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw (ds_match_length X) -> 0 <= ds_prev_length X <= 258 -> 0 <= ds_match_length X <= 258 ->
  exists R,
    msteps s6u_segs (mkst regs (0x19f20 : word) m s6u_rom) (mkst R (dec_pc X) m s6u_rom)
    /\ HREGS R /\ PLR R X
    /\ (forall r : reg, reg_in r [12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Q10 Hpl Hml. open_di HDI. open_hregs HRG.
  pose proof (ds6u_prev_length _ _ _ _ Hsc) as C184.
  unfold dec_pc, DeflSlow6_3.dec_cond.
  Local Ltac dec_fin HRG Hms HR Hfr Q10 :=
    ex1; split; [exact Hms|]; split; [hregs_via HRG Hfr|]; split; [split; [rewrite (Hfr 10%bv eq_refl); exact Q10 | reg1 HR Hfr] | fr_weak Hfr].
  destruct (Z.leb_spec 3 (ds_prev_length X)) as [P3|P3]; cbn [andb].
  - destruct (Z.leb_spec (ds_match_length X) (ds_prev_length X)) as [PM|PM].
    + run 6%nat [false; false] [RVal (EVar 36)] [(10, EVar 35%nat)] [(35%nat, 259); (36%nat, 259)] [ds_match_length X; ds_prev_length X] X.
      dec_fin HRG Hms HR Hfr Q10.
    + run 6%nat [false; true] [RVal (EVar 36)] [(10, EVar 35%nat)] [(35%nat, 259); (36%nat, 259)] [ds_match_length X; ds_prev_length X] X.
      dec_fin HRG Hms HR Hfr Q10.
  - run 6%nat [true] [RVal (EVar 36)] [(10, EVar 35%nat)] [(35%nat, 259); (36%nat, 259)] [ds_match_length X; ds_prev_length X] X.
    dec_fin HRG Hms HR Hfr Q10.
Qed.


Definition mavail_pc (X : deflate_state) : word :=
  if ds_match_available X =? 0 then (0x19d88 : word) else (0x1a188 : word).

Lemma mavail_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= ds_match_available X <= 1 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1a180 : word) m s6u_rom) (mkst R (mavail_pc X) m s6u_rom)
    /\ HREGS R
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hma. open_di HDI. open_hregs HRG.
  pose proof (ds6u_match_available _ _ _ _ Hsc) as C168.
  unfold mavail_pc. destruct (Z.eqb_spec (ds_match_available X) 0) as [Hz|Hnz].
  - run 4%nat [true] [RVal (EVar 35)] NoPins [(35%nat, 2)] [ds_match_available X] X.
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr | fr_weak Hfr].
  - run 4%nat [false] [RVal (EVar 35)] NoPins [(35%nat, 2)] [ds_match_available X] X.
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr | fr_weak Hfr].
Qed.

End Walk.
End FXG.

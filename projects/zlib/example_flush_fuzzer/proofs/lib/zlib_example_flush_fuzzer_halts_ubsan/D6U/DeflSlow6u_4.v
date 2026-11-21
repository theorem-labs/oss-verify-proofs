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
  Lmatch6u_run FillWin6uA FillWin6uD DeflBlkApi6u DeflKit6u DeflSlow6u_1 DeflSlow6u_2 DeflSlow6u_3.
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
Local Abbreviation ins_blk := (DeflSlow6u_2.ins_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation nil_blk := (DeflSlow6u_2.nil_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation setup_pc := (DeflSlow6u_2.setup_pc ds).
Local Abbreviation setup_blk := (DeflSlow6u_2.setup_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation lmret_pc := DeflSlow6u_2.lmret_pc.
Local Abbreviation lmret_blk := (DeflSlow6u_2.lmret_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation lm2_blk := (DeflSlow6u_2.lm2_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation dec_pc := DeflSlow6u_2.dec_pc.
Local Abbreviation dec_blk := (DeflSlow6u_2.dec_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation mavail_pc := DeflSlow6u_2.mavail_pc.
Local Abbreviation mavail_blk := (DeflSlow6u_2.mavail_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation dist_blk_near := (DeflSlow6u_3.dist_blk_near ROM mem S p zp ds flush ra sp HH).
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

Local Abbreviation sdist := DeflSlow6_5.sdist.
Local Abbreviation sdist_D := DeflSlow6_5.sdist_D.
Local Abbreviation ILS := DeflSlow6_5.ILS.


Lemma dist_blk_far : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> PLR regs X ->
  3 <= ds_prev_length X <= 258 -> 0 <= ds_strstart X <= 2 * ws -> 0 <= ds_prev_match X < 2 ^ 32 ->
  0 <= ds_lookahead X <= 2 * ws -> 3 <= ds_strstart X + ds_lookahead X -> ds_prev_length X - 1 <= ds_lookahead X ->
  0 <= ds_sym_next X -> ds_sym_next X + 3 <= 3 * lbs -> 0 <= ds_sym_end X < 2 ^ 18 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc X) i < 65536) ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc X) i < 65536) ->
  sdist_D X < 32768 -> 256 <= sdist_D X ->
  exists R M,
    msteps s6u_segs (mkst regs (0x19f2c : word) m s6u_rom) (mkst R (0x1a0b4 : word) M s6u_rom)
    /\ DI m1 M (DeflSlow6_5.dist_st X)
    /\ HREGS R
    /\ ILS R (ds_strstart X + 1) (ds_strstart X + ds_lookahead X - 3) (ds_prev_length X - 3) (ds_sym_next X + 3) (ds_sym_end X)
    /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG [Q10 Q12] Hpl Hstr Hpm Hlk Hsl3 Hpl1 Hsn0 Hsn3 Hse Hfc Hfd HDlt Hfar. unfold DeflSlow6_5.sdist_D in HDlt, Hfar.
  open_di HDI. open_hregs HRG.
  pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws. pose proof (wf_lbs _ HWF) as Wlbs.
  pose proof (ds6u_sym_buf _ _ _ _ Hsc) as C5888. rewrite Elbs in C5888.
  pose proof (ds6u_sym_next _ _ _ _ Hsc) as C5900. pose proof (ds6u_sym_end _ _ _ _ Hsc) as C5904.
  pose proof (ds6u_prev_match _ _ _ _ Hsc) as C164. pose proof (ds6u_strstart _ _ _ _ Hsc) as C172.
  pose proof (ds6u_lookahead _ _ _ _ Hsc) as C180. pose proof (ds6u_prev_length _ _ _ _ Hsc) as C184.
  replace (S + 5904) with (S + 5888 + 16) in C5904 by lia. replace (S + 5900) with (S + 5888 + 12) in C5900 by lia.
  pose proof Har as (Cfc & _ & Cfd & _).
  set (str := ds_strstart X) in *. set (pl := ds_prev_length X) in *. set (sn := ds_sym_next X) in *.
  set (pm := ds_prev_match X) in *. set (lk := ds_lookahead X) in *.
  assert (Hlc : (pl + -3) mod 2 ^ 8 = pl - 3) by (rewrite Z.mod_small by lia; lia).
  assert (Elen : wrap8 (pl - 3) = pl - 3) by (rewrite wrap8_mod'; apply Z.mod_small; lia).
  set (D := (str - pm + -2) mod 2 ^ 16) in *.
  assert (HD : 0 <= D < 65536) by (subst D; apply Z.mod_pos_bound; lia).
  assert (HD7 : 0 <= D / 2 ^ 7 < 256) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (tdist_D str pm) as ED. fold D in ED.
  pose proof (length_code_bound (pl - 3)) as Hcode. pose proof (dist_code_bound D) as HdcN. pose proof (dist_code_bound (256 + D / 2 ^ 7)) as HdcF.
  pose proof (tdist_lo_u str pm) as Eb0. pose proof (tdist_hi_u str pm) as Eb1.
  assert (Emi : szwrap 32 (str + lk + -3) = str + lk - 3) by (rewrite szwrap_small by lia; lia).
  (* 1.4 UBSan: _length_code / _dist_code come from auipc + add (same addresses 0x11ce0 / 0x11ae0), so
     the GOT reads of 1.3.1 (and their got6u_ok facts) are gone *)
  unhide HGOT. unhide RODS. unhide RODP.
  clear HGOT.
  assert (RS2 : S + 5968 <= 0x11ae0 \/ 0x12510 <= S) by (destruct RODS as [RS _]; lia).
  assert (RP2 : PB + PBL <= 0x11ae0 \/ 0x12510 <= PB) by (destruct RODP as [RP _]; lia).
  clear RODS RODP.
  apply hide in RS2. apply hide in RP2.
  apartF 1%nat 5%nat A15. apply hide in A15.
  Local Ltac d_fin HDI Hms HRG HR Hfr X str pl sn pm D dc Elbs Elen :=
    clear_aparts; rewrite ?dfF_0, ?dfF_1, ?dfF_2, ?dfF_3 in Hms;
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end)
      [KSymNext; KPb (lbs + sn) (wrap16 (wrap32 (str - 1 - pm))); KSymNext; KPb (lbs + sn + 1) (Z.shiftr (wrap16 (wrap32 (str - 1 - pm))) 8);
       KSymNext; KPb (lbs + sn + 2) (wrap8 (pl - 3));
       KFc TL (arr_get length_code_a (pl - 3) + 257) (arr_get (ds_dyn_ltree_fc X) (arr_get length_code_a (pl - 3) + 257) + 1);
       KFc TD dc (arr_get (ds_dyn_dtree_fc X) dc + 1);
       KLookahead; KPrevLength];
    lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end;
    split; [exact Hms|];
    split;
    [ eq_DI; rewrite <- dist_st6u_eq;
      unfold dist_st6u; rewrite Elbs; unfold DeflSlow6_5.sdist, DeflSlow6_5.sdist_D, d_code; subst str pl sn pm D;
      st_close ltac:(first [rewrite Elen | rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia | rewrite Z.shiftr_div_pow2 by lia])
    | split; [hregs_via HRG Hfr|];
      split; [unfold DeflSlow6_5.ILS; subst str pl sn pm D; repeat split; reg1 HR Hfr | fr_weak Hfr] ].
  unfold d_code. fold D in Hfar.
  replace (D <? 256) with false by (symmetry; apply Z.ltb_ge; exact Hfar).
  (* 1.4: the near test `bgeu a5,a3` (a5 = 255) falls through for d >= 256, then the overflow check `bltu a4,a3` *)
  run_gen HPINST 120%nat [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]
    [RVal (EAdd (EVar 38%nat) (EVar 39%nat)); RVal (EVar 37); RVal (EVar 40%nat); RVal (EVar 35); RVal (EVar 44);
     RVal (EVar 41); RVal (EApp1 2%nat (EAdd (EVar 41) (ELit 257))); RVal (EVar 42);
     RVal (EApp1 3%nat (EVar 42)); RVal (EVar 36); RVal (EVar 45)]
    [(12, EVar 36%nat); (19, EVar 46%nat); (20, EVar 43%nat); (27, EVar 47%nat);
     (21, EXor (EVar 43%nat) (ELit (-1))); (18, EXor (EVar 47%nat) (ELit (-1)))]
    [(35%nat, 65537); (36%nat, 259); (37%nat, 2 ^ 18); (38%nat, 2 ^ 63); (39%nat, 2 ^ 16); (40%nat, 2 ^ 32); (41%nat, 29); (42%nat, 30);
     (43%nat, 2 ^ 63); (44%nat, 65537); (45%nat, 2 ^ 18); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63)]
    [str; pl; sn; PB; lbs; pm; arr_get length_code_a (pl - 3); arr_get dist_code_a (256 + D / 2 ^ 7); S + 212; lk; ds_sym_end X; S + 5888; S + 2504]
    X.
  all: try (rewrite ED; nf; eapply (dist_code_read R6u s6u_segs m trod_ok6u HRT (256 + D / 2 ^ 7)); first [reflexivity | cbn [tr_dist_code R6u]; lia]).
  all: try (rewrite ?ED; first [unhide A15; lia | unhide RP2; lia | unhide RS2; lia]).
  all: try (rewrite ?ED; nf; change (2 ^ 3) with 8 in *; zcond_close).
  d_fin HDI Hms HRG HR Hfr X str pl sn pm D (arr_get dist_code_a (256 + D / 2 ^ 7)) Elbs Elen.
Qed.

Lemma dist_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> PLR regs X ->
  3 <= ds_prev_length X <= 258 -> 0 <= ds_strstart X <= 2 * ws -> 0 <= ds_prev_match X < 2 ^ 32 ->
  0 <= ds_lookahead X <= 2 * ws -> 3 <= ds_strstart X + ds_lookahead X -> ds_prev_length X - 1 <= ds_lookahead X ->
  0 <= ds_sym_next X -> ds_sym_next X + 3 <= 3 * lbs -> 0 <= ds_sym_end X < 2 ^ 18 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc X) i < 65536) ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc X) i < 65536) ->
  sdist_D X < 32768 ->
  exists R M,
    msteps s6u_segs (mkst regs (0x19f2c : word) m s6u_rom) (mkst R (0x1a0b4 : word) M s6u_rom)
    /\ DI m1 M (DeflSlow6_5.dist_st X)
    /\ HREGS R
    /\ ILS R (ds_strstart X + 1) (ds_strstart X + ds_lookahead X - 3) (ds_prev_length X - 3) (ds_sym_next X + 3) (ds_sym_end X)
    /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG HPL Hpl Hstr Hpm Hlk Hsl3 Hpl1 Hsn0 Hsn3 Hse Hfc Hfd HDlt.
  destruct (Z_lt_le_dec (DeflSlow6_5.sdist_D X) 256) as [Hn|Hf].
  - exact (dist_blk_near regs m1 m X HDI HRG HPL Hpl Hstr Hpm Hlk Hsl3 Hpl1 Hsn0 Hsn3 Hse Hfc Hfd HDlt Hn).
  - exact (dist_blk_far regs m1 m X HDI HRG HPL Hpl Hstr Hpm Hlk Hsl3 Hpl1 Hsn0 Hsn3 Hse Hfc Hfd HDlt Hf).
Qed.

End Walk.
End FXG.

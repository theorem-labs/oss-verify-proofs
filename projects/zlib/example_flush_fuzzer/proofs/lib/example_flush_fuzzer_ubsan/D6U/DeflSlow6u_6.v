(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import DS6 CalleeKits6 DeflSlow6_1 DeflSlow6_2 DeflSlow6_3 DeflSlow6_4 DeflSlow6_5 DeflSlow6_5b DeflSlow6_6 DeflSlow6_7 DeflSlow6_M.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u Callee6u TreesRod6u TreesApi6u TrApi6u
  Lmatch6u_run FillWin6uA FillWin6uD DeflBlkApi6u DeflKit6u DeflSlow6u_1 DeflSlow6u_2 DeflSlow6u_3 DeflSlow6u_4 DeflSlow6u_5.
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
Local Abbreviation dist_blk_far := (DeflSlow6u_4.dist_blk_far ROM mem S p zp ds flush ra sp HH).
Local Abbreviation dist_blk := (DeflSlow6u_4.dist_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation insl_pc := DeflSlow6u_5.insl_pc.
Local Abbreviation insl_blk := (DeflSlow6u_5.insl_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation exit_pc := DeflSlow6u_5.exit_pc.
Local Abbreviation exit_blk := (DeflSlow6u_5.exit_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation fbm_a := (DeflSlow6u_5.fbm_a ROM mem S p zp ds flush ra sp HH).
Local Abbreviation fbl_a := (DeflSlow6u_5.fbl_a ROM mem S p zp ds flush ra sp HH).
Local Abbreviation fb_b := (DeflSlow6u_5.fb_b ROM mem S p zp ds flush ra sp HH).
Local Abbreviation fbm_e := (DeflSlow6u_5.fbm_e ROM mem S p zp ds flush ra sp HH).
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

Local Abbreviation slit1 := DeflSlow6_3.slit1.
Local Abbreviation break1_st := DeflSlow6_7.break1_st.
Local Abbreviation break2_st := DeflSlow6_7.break2_st.
Local Abbreviation fb_bufp := (DeflSlow6_6.fb_bufp p).
Local Abbreviation fb_len := DeflSlow6_6.fb_len.


Definition slit_pc (X : deflate_state) : word :=
  if ds_sym_next X + 3 =? ds_sym_end X then (0x1a270 : word) else (0x1a388 : word).

Lemma slit_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs ->
  1 <= ds_strstart X <= 2 * ws ->
  0 <= ds_sym_next X -> ds_sym_next X + 3 <= 3 * lbs -> 0 <= ds_sym_end X < 2 ^ 18 ->
  (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256) ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc X) i < 65536) ->
  exists R M,
    msteps s6u_segs (mkst regs (0x1a188 : word) m s6u_rom) (mkst R (slit_pc X) M s6u_rom)
    /\ DI m1 M (slit1 X)
    /\ HREGS R
    /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hstr Hsn0 Hsn3 Hse Hwb Hfc.
  open_di HDI. open_hregs HRG.
  pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws. pose proof (wf_lbs _ HWF) as Wlbs.
  pose proof (ds6u_window _ _ _ _ Hsc) as C96. pose proof (ds6u_strstart _ _ _ _ Hsc) as C172.
  pose proof (ds6u_sym_buf _ _ _ _ Hsc) as C5888. rewrite Elbs in C5888. pose proof (ds6u_sym_end _ _ _ _ Hsc) as C5904.
  pose proof (ds6u_sym_next _ _ _ _ Hsc) as C5900.
  replace (S + 5904) with (S + 5888 + 16) in C5904 by lia. replace (S + 5900) with (S + 5888 + 12) in C5900 by lia.
  pose proof Har as (Cfc & _).
  unfold slit_pc.
  set (str := ds_strstart X) in *. set (sn := ds_sym_next X) in *.
  set (c := wb (ds_window X) (str - 1)).
  assert (Ec : c = arr_get (ds_window X) (str - 1)) by (subst c; apply wb_get; [intros j Hj; apply Hwb; rewrite <- Lw; exact Hj | rewrite Lw; lia]).
  pose proof (wb_range (ds_window X) (str - 1)) as Rc. fold c in Rc.
  assert (Ecc : wrap8 c = c) by (rewrite wrap8_mod'; apply Z.mod_small; lia).
  apartF 1%nat 2%nat A12. apartF 1%nat 5%nat A15. apartF 2%nat 5%nat A25.
  Local Ltac lit_fin HDI Hms HRG HR Hfr X str sn c Ec Ecc Elbs :=
    clear_aparts; rewrite ?dfF_0, ?dfF_1, ?dfF_2, ?dfF_3 in Hms;
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end)
      [KSymNext; KPb (lbs + sn) 0; KSymNext; KPb (lbs + sn + 1) 0; KSymNext; KPb (lbs + sn + 2) c;
       KFc TL c (arr_get (ds_dyn_ltree_fc X) c + 1)];
    lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end;
    split; [exact Hms|];
    split; [ eq_DI; unfold DeflSlow6_3.slit1; rewrite Elbs; subst str sn; rewrite <- Ec; st_close ltac:(rewrite Ecc) |];
    split; [hregs_via HRG Hfr | fr_weak Hfr].
  destruct (Z.eqb_spec (sn + 3) (ds_sym_end X)) as [Hbf|Hnbf].
  - runT 70%nat [false; false; false; false; false; false; false; false; false; false; false; false; false; false]
      [RVal (EAdd (EVar 35%nat) (ELit 1)); RVal (EVar 40); RVal (EVar 37); RVal (EAdd (EVar 38%nat) (EVar 39%nat));
       RVal (EApp1 0%nat (EVar 35)); RVal (EApp1 2%nat (EApp1 0%nat (EVar 35))); RVal (EVar 42)]
      [(20, EVar 43%nat); (21, EXor (EVar 43%nat) (ELit (-1))); (19, EVar 44%nat)]
      [(35%nat, 65536); (37%nat, 2 ^ 18); (38%nat, 2 ^ 63); (39%nat, 2 ^ 16); (40%nat, 2 ^ 63); (42%nat, 2 ^ 18); (43%nat, 2 ^ 63); (44%nat, 2 ^ 63)]
      [str - 1; 0; sn; PB; lbs; W; 0; ds_sym_end X; S + 212; S + 5888]
      X.
    all: try (nf; change (2 ^ 3) with 8 in *; change (2 ^ 1) with 2 in *; zcond_close).
    lit_fin HDI Hms HRG HR Hfr X str sn c Ec Ecc Elbs.
  - runT 70%nat [false; false; false; false; false; false; false; false; false; false; false; false; false; true]
      [RVal (EAdd (EVar 35%nat) (ELit 1)); RVal (EVar 40); RVal (EVar 37); RVal (EAdd (EVar 38%nat) (EVar 39%nat));
       RVal (EApp1 0%nat (EVar 35)); RVal (EApp1 2%nat (EApp1 0%nat (EVar 35))); RVal (EVar 42)]
      [(20, EVar 43%nat); (21, EXor (EVar 43%nat) (ELit (-1))); (19, EVar 44%nat)]
      [(35%nat, 65536); (37%nat, 2 ^ 18); (38%nat, 2 ^ 63); (39%nat, 2 ^ 16); (40%nat, 2 ^ 63); (42%nat, 2 ^ 18); (43%nat, 2 ^ 63); (44%nat, 2 ^ 63)]
      [str - 1; 0; sn; PB; lbs; W; 0; ds_sym_end X; S + 212; S + 5888]
      X.
    all: try (nf; change (2 ^ 3) with 8 in *; change (2 ^ 1) with 2 in *; zcond_close).
    lit_fin HDI Hms HRG HR Hfr X str sn c Ec Ecc Elbs.
Qed.


Lemma break1a_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> ds_match_available X = 0 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1a3c4 : word) m s6u_rom) (mkst R (0x1a4ac : word) m s6u_rom)
    /\ HREGS R
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hma. open_di HDI. open_hregs HRG.
  pose proof (ds6u_match_available _ _ _ _ Hsc) as C168. rewrite Hma in C168.
  run 4%nat [true] [RVal (ELit 0)] NoPins NoBounds (@nil Z) X.
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr | fr_weak Hfr].
Qed.

Lemma break1b_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 < ds_match_available X < 2 ^ 32 ->
  1 <= ds_strstart X <= 2 * ws ->
  0 <= ds_sym_next X -> ds_sym_next X + 3 <= 3 * lbs ->
  (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256) ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc X) i < 65536) ->
  exists R M,
    msteps s6u_segs (mkst regs (0x1a3c4 : word) m s6u_rom) (mkst R (0x1a4ac : word) M s6u_rom)
    /\ DI m1 M (break1_st X)
    /\ HREGS R
    /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hma Hstr Hsn0 Hsn3 Hwb Hfc.
  open_di HDI. open_hregs HRG.
  pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws. pose proof (wf_lbs _ HWF) as Wlbs.
  pose proof (ds6u_window _ _ _ _ Hsc) as C96. pose proof (ds6u_strstart _ _ _ _ Hsc) as C172.
  pose proof (ds6u_match_available _ _ _ _ Hsc) as C168.
  pose proof (ds6u_sym_buf _ _ _ _ Hsc) as C5888. rewrite Elbs in C5888.
  pose proof (ds6u_sym_next _ _ _ _ Hsc) as C5900.
  replace (S + 5900) with (S + 5888 + 12) in C5900 by lia.
  pose proof Har as (Cfc & _).
  set (str := ds_strstart X) in *. set (sn := ds_sym_next X) in *.
  set (c := wb (ds_window X) (str - 1)).
  assert (Ec : c = arr_get (ds_window X) (str - 1)) by (subst c; apply wb_get; [intros j Hj; apply Hwb; rewrite <- Lw; exact Hj | rewrite Lw; lia]).
  pose proof (wb_range (ds_window X) (str - 1)) as Rc. fold c in Rc.
  assert (Ecc : wrap8 c = c) by (rewrite wrap8_mod'; apply Z.mod_small; lia).
  pose proof (sx32_u64_nz (ds_match_available X) ltac:(lia)) as Hsx.
  apartF 1%nat 2%nat A12. apartF 1%nat 5%nat A15. apartF 2%nat 5%nat A25.
  runT 70%nat [false; false; false; false; false; false; false; false; false; false; false; false; false; false]
      [RVal (EVar 36); RVal (EAdd (EVar 35%nat) (ELit 1)); RVal (EVar 40); RVal (EVar 37); RVal (EAdd (EVar 38%nat) (EVar 39%nat));
       RVal (EApp1 0%nat (EVar 35)); RVal (EApp1 2%nat (EApp1 0%nat (EVar 35)))]
      [(20, EVar 43%nat); (21, EXor (EVar 43%nat) (ELit (-1))); (19, EVar 44%nat)]
      [(35%nat, 65536); (36%nat, 2 ^ 32); (37%nat, 2 ^ 18); (38%nat, 2 ^ 63); (39%nat, 2 ^ 16); (40%nat, 2 ^ 63); (43%nat, 2 ^ 63); (44%nat, 2 ^ 63)]
      [str - 1; ds_match_available X; sn; PB; lbs; W; 0; 0; S + 212; S + 5888]
      X.
  all: try (nf; change (2 ^ 3) with 8 in *; change (2 ^ 1) with 2 in *; zcond_close).
  clear_aparts. rewrite ?dfF_0, ?dfF_1, ?dfF_2, ?dfF_3 in Hms.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end)
    [KSymNext; KPb (lbs + sn) 0; KSymNext; KPb (lbs + sn + 1) 0; KSymNext; KPb (lbs + sn + 2) c;
     KFc TL c (arr_get (ds_dyn_ltree_fc X) c + 1); KMatchAvailable].
  lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end.
  split; [exact Hms|].
  split; [ eq_DI; unfold DeflSlow6_7.break1_st, DeflSlow6_3.slit1; rewrite Elbs; subst str sn; rewrite <- Ec; st_close ltac:(rewrite Ecc) |].
  split; [hregs_via HRG Hfr | fr_weak Hfr].
Qed.


Definition break2_pc : word := if flush =? 4 then (0x1bff0 : word) else (0x1a50c : word).

Lemma break2_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> LOC m ->
  0 <= ds_strstart X < 2 ^ 31 -> - 2 ^ 62 <= ds_block_start X < 2 ^ 62 ->
  exists R M,
    msteps s6u_segs (mkst regs (0x1a4ac : word) m s6u_rom) (mkst R break2_pc M s6u_rom)
    /\ DI m1 M (break2_st X)
    /\ HREGS R
    /\ (flush = 4 -> getr R 10 = zw S /\ getr R 11 = zw (fb_bufp X) /\ getr R 12 = zw (fb_len X) /\ getr R 13 = zw 1
                     /\ getr R 1 = (0x1a574%bv : word))
    /\ (flush <> 4 -> getr R 10 = zw (ds_strstart X))
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 13; 14]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG (L16 & L8) Hstr Hbs. open_di HDI. open_hregs HRG. pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof (ds6u_block_start _ _ _ _ Hsc) as C152. pose proof (ds6u_window _ _ _ _ Hsc) as C96. pose proof (ds6u_strstart _ _ _ _ Hsc) as C172.
  pose proof (ds6u_insert _ _ _ _ Hsc) as C5932.
  destruct (DeflSlow6_6.bs_facts (ds_block_start X) ltac:(lia)) as (Hsx & Hw32 & Hbsu).
  pose proof (DeflSlow6_6.len_fact (ds_strstart X) (ds_block_start X)) as Hlen.
  pose proof (fb_sovf_ok (ds_strstart X) (ds_block_start X) ltac:(lia) ltac:(lia)) as Hsov.
  assert (RD152 : exists bs, rdn s6u_segs m (zw (S + 152)) 8 = Some bs /\ bytes_le_to_Z bs = ds_block_start X mod 2 ^ 64)
    by exact (cell_read_at s6u_segs m (S + 152) 8 _ _ C152 eq_refl).
  pose proof (wrap32_range' (ds_block_start X)) as Hw32r.
  unfold break2_pc, DeflSlow6_7.break2_st, DeflSlow6_6.fb_bufp, DeflSlow6_6.fb_len.
  apartF 0%nat 1%nat A01.
  Local Ltac b2_fin Hms HDI HRG HR Hfr :=
    clear_aparts; norm_sx Hms;
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KInsert];
    lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end;
    split; [exact Hms|];
    split; [eq_DI; st_close idtac|];
    split; [hregs_via HRG Hfr|];
    split; [first [intros Hc; exfalso; lia | intros _; repeat split; reg1 HR Hfr]|];
    split; [first [intros Hc; exfalso; lia | intros _; reg1 HR Hfr] | fr_weak Hfr].
  destruct (Z.ltb_spec (ds_strstart X) 2) as [Hs2|Hs2]; destruct (Z.eqb_spec flush 4) as [Hf4|Hf4].
  - destruct (Z.ltb_spec (ds_block_start X) 0) as [Hneg|Hpos].
    + run 30%nat [true; false; true; false] [RVal (EVar 35); RVal (EVar 36)] NoPins
        [(35%nat, 2 ^ 31); (36%nat, 2 ^ 64)] [ds_strstart X; ds_block_start X mod 2 ^ 64] X.
      all: try (rewrite Hsx in *; first [lia | rewrite <- Hsov; reflexivity | rewrite Hsov; reflexivity]).
      b2_fin Hms HDI HRG HR Hfr.
    + run 30%nat [true; false; false; false; false; true] [RVal (EVar 35); RVal (EVar 36); RVal (EVar 37); RVal (ELit 4294967295)] NoPins
        [(35%nat, 2 ^ 31); (36%nat, 2 ^ 64); (37%nat, 2 ^ 63)] [ds_strstart X; ds_block_start X mod 2 ^ 64; W] X.
      all: try (rewrite Hsx in *; first [lia | rewrite <- Hsov; reflexivity | rewrite Hsov; reflexivity]).
      b2_fin Hms HDI HRG HR Hfr.
  - run 12%nat [true; true] [RVal (EVar 35)] NoPins [(35%nat, 2 ^ 31)] [ds_strstart X] X.
    b2_fin Hms HDI HRG HR Hfr.
  - destruct (Z.ltb_spec (ds_block_start X) 0) as [Hneg|Hpos].
    + run 30%nat [false; false; true; false] [RVal (EVar 35); RVal (EVar 36)] NoPins
        [(35%nat, 2 ^ 31); (36%nat, 2 ^ 64)] [ds_strstart X; ds_block_start X mod 2 ^ 64] X.
      all: try (rewrite Hsx in *; first [lia | rewrite <- Hsov; reflexivity | rewrite Hsov; reflexivity]).
      b2_fin Hms HDI HRG HR Hfr.
    + run 30%nat [false; false; false; false; false; true] [RVal (EVar 35); RVal (EVar 36); RVal (EVar 37); RVal (ELit 4294967295)] NoPins
        [(35%nat, 2 ^ 31); (36%nat, 2 ^ 64); (37%nat, 2 ^ 63)] [ds_strstart X; ds_block_start X mod 2 ^ 64; W] X.
      all: try (rewrite Hsx in *; first [lia | rewrite <- Hsov; reflexivity | rewrite Hsov; reflexivity]).
      b2_fin Hms HDI HRG HR Hfr.
  - run 12%nat [false; true] [RVal (EVar 35)] NoPins [(35%nat, 2 ^ 31)] [ds_strstart X] X.
    b2_fin Hms HDI HRG HR Hfr.
Qed.


Definition fina_pc (X : deflate_state) : word := if ds_sym_next X =? 0 then (0x1a604 : word) else (0x1bff0 : word).

Lemma fina_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> LOC m -> getr regs 10 = zw (ds_strstart X) ->
  0 <= ds_strstart X < 2 ^ 31 -> - 2 ^ 62 <= ds_block_start X < 2 ^ 62 -> 0 <= ds_sym_next X < 2 ^ 31 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1a50c : word) m s6u_rom) (mkst R (fina_pc X) m s6u_rom)
    /\ HREGS R
    /\ (ds_sym_next X <> 0 -> getr R 10 = zw S /\ getr R 11 = zw (fb_bufp X) /\ getr R 12 = zw (fb_len X) /\ getr R 13 = zw 0
                            /\ getr R 1 = (0x1a5dc%bv : word))
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 13; 14]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG (L16 & L8) Q10 Hstr Hbs Hsn. open_di HDI. open_hregs HRG. pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof (ds6u_block_start _ _ _ _ Hsc) as C152. pose proof (ds6u_window _ _ _ _ Hsc) as C96. pose proof (ds6u_strstart _ _ _ _ Hsc) as C172.
  pose proof (ds6u_sym_next _ _ _ _ Hsc) as C5900.
  destruct (DeflSlow6_6.bs_facts (ds_block_start X) ltac:(lia)) as (Hsx & Hw32 & Hbsu).
  pose proof (DeflSlow6_6.len_fact (ds_strstart X) (ds_block_start X)) as Hlen.
  pose proof (fb_sovf_ok (ds_strstart X) (ds_block_start X) ltac:(lia) ltac:(lia)) as Hsov.
  assert (RD152 : exists bs, rdn s6u_segs m (zw (S + 152)) 8 = Some bs /\ bytes_le_to_Z bs = ds_block_start X mod 2 ^ 64)
    by exact (cell_read_at s6u_segs m (S + 152) 8 _ _ C152 eq_refl).
  pose proof (wrap32_range' (ds_block_start X)) as Hw32r.
  unfold fina_pc, DeflSlow6_6.fb_bufp, DeflSlow6_6.fb_len.
  Local Ltac fa_fin Hms HRG HR Hfr :=
    lazymatch type of Hms with msteps _ _ (mkst ?R _ _ _) => exists R end; split; [exact Hms|];
    split; [hregs_via HRG Hfr|];
    split; [first [intros Hc; exfalso; lia | intros _; repeat split; reg1 HR Hfr] | fr_weak Hfr].
  destruct (Z.eqb_spec (ds_sym_next X) 0) as [Hz|Hnz].
  - run 8%nat [true] [RVal (EVar 35)] [(10, EVar 36%nat)] [(35%nat, 2 ^ 31); (36%nat, 2 ^ 31)] [ds_sym_next X; ds_strstart X] X.
    fa_fin Hms HRG HR Hfr.
  - pose proof (sx32_u64_nz (ds_sym_next X) ltac:(lia)) as Hsxn.
    destruct (Z.ltb_spec (ds_block_start X) 0) as [Hneg|Hpos].
    + run 30%nat [false; true; false] [RVal (EVar 35); RVal (EVar 37)] [(10, EVar 36%nat)]
        [(35%nat, 2 ^ 31); (36%nat, 2 ^ 31); (37%nat, 2 ^ 64)] [ds_sym_next X; ds_strstart X; ds_block_start X mod 2 ^ 64] X.
      all: try (rewrite Hsx in *; first [lia | rewrite <- Hsov; reflexivity | rewrite Hsov; reflexivity]).
      fa_fin Hms HRG HR Hfr.
    + run 30%nat [false; false; false; false; true] [RVal (EVar 35); RVal (EVar 37); RVal (EVar 38); RVal (ELit 4294967295)] [(10, EVar 36%nat)]
        [(35%nat, 2 ^ 31); (36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 63)] [ds_sym_next X; ds_strstart X; ds_block_start X mod 2 ^ 64; W] X.
      all: try (rewrite Hsx in *; first [lia | rewrite <- Hsov; reflexivity | rewrite Hsov; reflexivity]).
      fa_fin Hms HRG HR Hfr.
Qed.

Lemma b84_blk : forall regs m,
  HREGS regs ->
  exists R,
    msteps s6u_segs (mkst regs (0x1a604 : word) m s6u_rom) (mkst R (0x1a608 : word) m s6u_rom)
    /\ HREGS R /\ getr R 10 = zw 1
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m HRG. open_hregs HRG. open_min.
  run 3%nat NoDirs NoReads NoPins NoBounds (@nil Z) ds.
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.


(* 1.4: FLUSH_BLOCK(s, 1) now returns finish_started when avail_out == 0 only if
   s->pending != 0 or s->wrap != 0 (`ld a1,40(s0)` / `lw a1,48(s0)`, 0x1a544-0x1a554); the caller supplies one of the two *)
Lemma fbte_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32 ->
  0 <= ds_pending X < 2 ^ 31 -> (cs_avail_out (ds_strm X) = 0 -> ds_pending X <> 0 \/ 0 < ds_wrap X < 2 ^ 31) ->
  exists R,
    msteps s6u_segs (mkst regs (0x1a584 : word) m s6u_rom) (mkst R (0x1a608 : word) m s6u_rom)
    /\ HREGS R /\ getr R 10 = zw (if cs_avail_out (ds_strm X) =? 0 then 2 else 3)
    /\ (forall r : reg, reg_in r [10; 11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hav Hpd Hpw. open_di HDI. open_hregs HRG.
  pose proof (ds6u_strm _ _ _ _ Hsc) as C0. replace (S + 0) with S in C0 by lia. pose proof (zsl_avail_out s6u_segs _ _ _ _ _ Zs) as Z32.
  pose proof (ds6u_pending _ _ _ _ Hsc) as C40. pose proof (ds6u_wrap _ _ _ _ Hsc) as C48.
  destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
  - change (if true then 2 else 3) with 2. rewrite Hz in Z32. destruct (Hpw Hz) as [Hp|Hw].
    + run 12%nat [false; false; true; true] [RVal (EVar 35); RVal (ELit 0); RVal (EVar 36)] NoPins
        [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31)] [strm; ds_pending X] X.
      exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
    + destruct (Z.eq_dec (ds_pending X) 0) as [Hp0|Hp0].
      * rewrite Hp0 in C40. pose proof (sx32_u64_nz (ds_wrap X) ltac:(lia)) as Hsxw.
        run 12%nat [false; false; true; false; true] [RVal (EVar 35); RVal (ELit 0); RVal (ELit 0); RVal (EVar 36)] NoPins
          [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31)] [strm; ds_wrap X] X.
        exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
      * run 12%nat [false; false; true; true] [RVal (EVar 35); RVal (ELit 0); RVal (EVar 36)] NoPins
          [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31)] [strm; ds_pending X] X.
        exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - change (if false then 2 else 3) with 3.
    pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
    run 10%nat [false; false; false] [RVal (EVar 35); RVal (EVar 36)] NoPins [(35%nat, 2 ^ 63); (36%nat, 2 ^ 32)] [strm; cs_avail_out (ds_strm X)] X.
    exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma fine_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1a5ec : word) m s6u_rom) (mkst R (DeflSlow6_6.avail_pc X (0x1a608 : word) (0x1a604 : word)) m s6u_rom)
    /\ HREGS R /\ (cs_avail_out (ds_strm X) = 0 -> getr R 10 = zw 0)
    /\ (forall r : reg, reg_in r [10; 11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hav. open_di HDI. open_hregs HRG.
  pose proof (ds6u_strm _ _ _ _ Hsc) as C0. replace (S + 0) with S in C0 by lia. pose proof (zsl_avail_out s6u_segs _ _ _ _ _ Zs) as Z32.
  unfold DeflSlow6_6.avail_pc. destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
  - rewrite Hz in Z32.
    run 10%nat [false; false; true] [RVal (EVar 35); RVal (ELit 0)] NoPins [(35%nat, 2 ^ 63)] [strm] X.
    exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros _; reg1 HR Hfr | fr_weak Hfr].
  - pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
    run 10%nat [false; false; false] [RVal (EVar 35); RVal (EVar 36)] NoPins [(35%nat, 2 ^ 63); (36%nat, 2 ^ 32)] [strm; cs_avail_out (ds_strm X)] X.
    exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros Hc; exfalso; lia | fr_weak Hfr].
Qed.

End Walk.
End FXG.

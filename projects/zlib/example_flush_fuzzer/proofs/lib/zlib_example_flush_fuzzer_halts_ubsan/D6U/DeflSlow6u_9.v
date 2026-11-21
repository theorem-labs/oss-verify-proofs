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
  Lmatch6u_run FillWin6uA FillWin6uD DeflBlkApi6u DeflKit6u FlushPend6u DeflSlow6u_1 DeflSlow6u_2 DeflSlow6u_3 DeflSlow6u_4 DeflSlow6u_5 DeflSlow6u_6 DeflSlow6u_7 DeflSlow6u_8.
(* 1.4: the model-level wrap lemmas of the plain port, used qualified (Require only, no Import) *)
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require DeflSlow6_9 DeflSlow6_11.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition strip_oku (s : deflate_state) : Prop := ds_lookahead s < MIN_LOOKAHEAD -> BSI s.

Fixpoint sloop_oku (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => True
  | S f => strip_oku s /\ match snd (st_sbody s flush) with LCont => sloop_oku f (fst (st_sbody s flush)) flush | _ => True end
  end.

Lemma sloop_oku_S : forall f s flush,
  sloop_oku (S f) s flush = (strip_oku s /\ match snd (st_sbody s flush) with LCont => sloop_oku f (fst (st_sbody s flush)) flush | _ => True end).
Proof. reflexivity. Qed.

Definition slow_safe6u (FBSAFE : deflate_state -> option Z -> Z -> Z -> Prop) (ds : deflate_state) (flush : Z) : Prop :=
  slow_safe6 FBSAFE ds flush /\ sloop_oku (lz_fuel ds) ds flush
  /\ match snd (deflate_slow_loop (lz_fuel ds) ds flush) with
     | Some _ => True
     | None => - 2 ^ 62 <= ds_block_start (fst (deflate_slow_loop (lz_fuel ds) ds flush)) < 2 ^ 62
     end.

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
Local Abbreviation slit_pc := DeflSlow6u_6.slit_pc.
Local Abbreviation slit_blk := (DeflSlow6u_6.slit_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation break1a_blk := (DeflSlow6u_6.break1a_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation break1b_blk := (DeflSlow6u_6.break1b_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation break2_pc := (DeflSlow6u_6.break2_pc flush).
Local Abbreviation break2_blk := (DeflSlow6u_6.break2_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation fina_pc := DeflSlow6u_6.fina_pc.
Local Abbreviation fina_blk := (DeflSlow6u_6.fina_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation b84_blk := (DeflSlow6u_6.b84_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation fbte_blk := (DeflSlow6u_6.fbte_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation fine_blk := (DeflSlow6u_6.fine_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation FRM := (DeflSlow6u_7.FRM sp).
Local Abbreviation FRM_keep := (DeflSlow6u_7.FRM_keep ROM mem S p zp ds flush ra sp HH).
Local Abbreviation pro_blk := (DeflSlow6u_7.pro_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation epi_blk := (DeflSlow6u_7.epi_blk ROM mem S p zp ds flush ra sp HH).
Local Abbreviation call_lm := (DeflSlow6u_8.call_lm ROM mem S p zp ds flush ra sp HH).
Local Abbreviation call_fb := (DeflSlow6u_8.call_fb ROM mem S p zp ds flush ra sp HH MEMCPY MEMSET FBSAFE TFB).
Local Abbreviation call_fw := (DeflSlow6u_8.call_fw ROM mem S p zp ds flush ra sp HH MEMCPY MEMSET ADLER).
Local Abbreviation UBT_ds := (DeflSlow6u_8.UBT_ds ROM mem S p zp ds flush ra sp HH).
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

Local Abbreviation flush_ok := (flush_ok6 FBSAFE).
Local Abbreviation fb_bufp := (DeflSlow6_6.fb_bufp p).
Local Abbreviation fb_len := DeflSlow6_6.fb_len.

Definition KEEP (regs0 R : bvmap 5 word) : Prop := getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4.

Lemma KEEP_via : forall regs0 R R' L,
  KEEP regs0 R -> (forall r : reg, reg_in r L = false -> getr R' r = getr R r) ->
  reg_in 3%bv L = false -> reg_in 4%bv L = false -> KEEP regs0 R'.
Proof.
  intros regs0 R R' L (A3 & A4) Hfr E3 E4. unfold KEEP. rewrite (Hfr _ E3), (Hfr _ E4). split; assumption.
Qed.

Local Ltac keep_via HK Hfr := apply (KEEP_via _ _ _ _ HK Hfr); reflexivity.
Local Ltac retok := apply ret_ok_even; reflexivity.
Local Ltac via1 Hfr := lazymatch goal with |- getr _ ?r = _ => rewrite (Hfr r eq_refl) end.

Lemma avail_bound : forall m1 m X, DI m1 m X -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32.
Proof.
  intros m1 m X (_ & (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & Eout & Hao & Hol)) & _).
  pose proof (wf_ao _ HWF). lia.
Qed.

Lemma di_sizes : forall m1 m X, DI m1 m X -> ds_w_size X = ws /\ ds_hash_size X = hs /\ ds_lit_bufsize X = lbs.
Proof. intros m1 m X (_ & _ & HS3). exact HS3. Qed.

Lemma LOC_keep : forall m1 m X, LOC m1 -> DI m1 m X -> LOC m.
Proof. intros m1 m X HL1 HDI. exact (LOC_DI m1 m X HL1 HDI). Qed.

Lemma HREGS_fbc : forall R R', HREGS R -> (forall r : reg, reg_in r TFB_CLOB6u = false -> getr R' r = getr R r) -> HREGS R'.
Proof. intros R R' H Hfr. hregs_via H Hfr. Qed.
Lemma HREGS_fp : forall R R', HREGS R -> (forall r : reg, reg_in r FP_CLOB6u = false -> getr R' r = getr R r) -> HREGS R'.
Proof. intros R R' H Hfr. hregs_via H Hfr. Qed.


Lemma call_fb_at : forall regs0 regs m1 m X (ra' : word) last,
  DI m1 m X -> KEEP regs0 regs -> ret_ok ra' -> flush_ok X last -> 0 <= last <= 1 ->
  getr regs 10 = zw S -> getr regs 11 = zw (fb_bufp X) -> getr regs 12 = zw (fb_len X) ->
  getr regs 13 = zw last -> getr regs 2 = zw SP -> getr regs 1 = ra' ->
  let buf := if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None in
  let len := wrap64 (ds_strstart X - ds_block_start X) in
  exists R m',
    msteps s6u_segs (mkst regs (0x1bff0 : word) m s6u_rom) (mkst R ra' m' s6u_rom)
    /\ DI m1 m' (tr_flush_block X buf len last)
    /\ KEEP regs0 R
    /\ (forall r : reg, reg_in r TFB_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs0 regs m1 m X ra' last HDI HK Hret HFO Hlast A10 A11 A12 A13 A2 A1 buf len.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  unfold flush_ok6 in HFO. rewrite Elbs, Ews in HFO. fold buf len in HFO.
  destruct HFO as (Hsafe & HBI & Hsb & Hbs & Hstr & Hs31 & Hwb & _).
  assert (Elen : len = ds_strstart X - ds_block_start X) by (subst len; rewrite wrap64_mod; apply Z.mod_small; lia).
  assert (Hbuf : match buf with
                 | None => fb_bufp X = 0
                 | Some off => fb_bufp X = W + off /\ 0 <= off < 2 ^ 32 /\ (len <> 0 -> off + len <= 2 * ws)
                 end).
  { subst buf. unfold DeflSlow6_6.fb_bufp. destruct (Z.leb_spec 0 (ds_block_start X)).
    - replace (ds_block_start X <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite wrap32_mod, Z.mod_small by lia. split; [reflexivity|]. split; [lia|]. intros _. lia.
    - replace (ds_block_start X <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  unfold DeflSlow6_6.fb_len in A12. fold len in A12.
  destruct (call_fb regs m1 m X ra' buf (fb_bufp X) len last
              HDI Hret Hsafe HBI Hlast ltac:(lia) Hwb Hbuf A10 A11 A12 A13 A2 A1)
    as (R2 & m2 & Hms2 & HDI2 & CE2 & Hfr2).
  exists R2, m2. split; [exact Hms2|]. split; [exact HDI2|]. split; [keep_via HK Hfr2 | exact Hfr2].
Qed.


Lemma fp_sequ : forall (PC RA : word),
  (PC = (0x1a338%bv : word) /\ RA = (0x1a348%bv : word)) \/ (PC = (0x1a378%bv : word) /\ RA = (0x1a388%bv : word))
  \/ (PC = (0x1a574%bv : word) /\ RA = (0x1a584%bv : word)) \/ (PC = (0x1a5dc%bv : word) /\ RA = (0x1a5ec%bv : word)) ->
  forall regs0 regs m1 m X8,
  DI m1 m X8 -> HREGS regs -> KEEP regs0 regs ->
  0 <= ds_strstart X8 <= 2 * ws ->
  (let X9 := set_block_start X8 (ds_strstart X8) in
   BINV PBL X9 /\ ds_pending (tr_flush_bits X9) <= PBL
   /\ let X10 := tr_flush_bits X9 in
      0 <= ds_pending X10 < 2 ^ 31 /\ 0 <= ds_pending_out X10 /\ ds_pending_out X10 + fp_len X10 <= PBL
      /\ 0 <= cs_total_out (ds_strm X10) < 2 ^ 64) ->
  exists R M,
    msteps s6u_segs (mkst regs PC m s6u_rom) (mkst R RA M s6u_rom)
    /\ DI m1 M (let X10 := tr_flush_bits (set_block_start X8 (ds_strstart X8)) in
                if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10))
    /\ HREGS R /\ KEEP regs0 R.
Proof.
  intros PC RA HPC regs0 regs m1 m X8 HDI HRG HK Hstr (HBI & Hroom & Hpd & Hpo0 & Hpo1 & Htot).
  assert (HRA : ret_ok RA) by (destruct HPC as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]]; retok).
  destruct (fb_b PC RA regs m1 m X8 HPC HDI HRG Hstr) as (R1 & M1 & Hms1 & HDI1 & HRG1 & A10 & A1 & A2 & Hfr1).
  pose proof (avail_bound _ _ _ HDI1) as Hav9.
  pose proof (DeflSlow6_1.tr_flush_bits_nobits (set_block_start X8 (ds_strstart X8))) as En.
  unfold DeflSlow6_1.ds_nobits, DeflSlow6_1.ds_sizes, DeflSlow6_1.ds_io, DeflSlow6_1.cs_io in En.
  injection En as Ew Ep Eh Est Esz1 Esz2 Esz3 _ _.
  assert (Hav10 : 0 <= cs_avail_out (ds_strm (tr_flush_bits (set_block_start X8 (ds_strstart X8)))) < 2 ^ 32).
  { rewrite Est. exact Hav9. }
  pose proof (fp_len_equ (tr_flush_bits (set_block_start X8 (ds_strstart X8))) ltac:(lia) ltac:(lia)) as (_ & Hfl1 & Hfl2).
  pose proof (di_sizes _ _ _ HDI1) as (Ews & Ehs & Elbs).
  destruct (FlushPend6u.call_fp ROM mem S p zp ds flush ra sp DSLOW_FRAME6u DSLOW_FR6u HH
              ltac:(unfold DSLOW_FRAME6u, DSLOW_FR6u; lia) ltac:(unfold DSLOW_FR6u; lia) MEMCPY TFBITS
              R1 m1 M1 (set_block_start X8 (ds_strstart X8)) RA HDI1 A10 A2 A1 HRA
              ltac:(unfold FlushPend6u.fp_pre; cbv zeta; split; [exact HBI | repeat split; lia]))
    as (R2 & M2 & Hms2 & HDI2 & B2 & B1 & Hfr2).
  exists R2, M2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
  split; [rewrite DeflM.flush_pending_eq in HDI2; exact HDI2|].
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  split; [exact (HREGS_fp _ _ HRG1 Hfr2) | keep_via HK1 Hfr2].
Qed.


Lemma from_fb1 : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 -> getr regs 10 = zw (ds_strstart X) ->
  flush_ok X 0 ->
  exists R M,
    DI m1 M (fst (flush_block X 0)) /\ KEEP regs0 R
    /\ match snd (flush_block X 0) with
       | Some bs => msteps s6u_segs (mkst regs (0x1a2c8 : word) m s6u_rom) (mkst R (0x1a608 : word) M s6u_rom)
                    /\ getr R 10 = zw (bs_code bs) /\ getr R 2 = zw SP
       | None => msteps s6u_segs (mkst regs (0x1a2c8 : word) m s6u_rom) (mkst R (0x19da8 : word) M s6u_rom)
                 /\ HREGS R
       end.
Proof.
  intros regs0 regs m1 m X HDI HRG HK HL1 Q10 HFO.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof HFO as HFO'. unfold flush_ok6 in HFO'. rewrite Elbs, Ews in HFO'.
  destruct HFO' as (_ & _ & Hsb & Hbs & Hstr & Hs31 & _ & Hstr8 & HREST).
  pose proof (LOC_keep _ _ _ HL1 HDI) as HLm.
  destruct (fbm_a regs m1 m X HDI HRG HLm Q10 ltac:(lia) ltac:(lia)) as (R1 & Hms1 & HRG1 & A10 & A11 & A12 & A13 & A1 & A2 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  destruct (call_fb_at regs0 R1 m1 m X (0x1a338%bv : word) 0 HDI HK1 ltac:(retok) HFO ltac:(lia) A10 A11 A12 A13 A2 A1)
    as (R2 & m2 & Hms2 & HDI2 & HK2 & Hfr2).
  assert (HRG2 : HREGS R2) by exact (HREGS_fbc _ _ HRG1 Hfr2).
  rewrite flush_block_fst, flush_block_snd, flush_block_fst, flush_block_only_eq. cbv zeta.
  replace (negb (0 =? 0)) with false by reflexivity.
  revert Hstr8 HREST HDI2.
  generalize (tr_flush_block X (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None) (wrap64 (ds_strstart X - ds_block_start X)) 0).
  intros X8 Hstr8 HREST HDI2.
  destruct (fp_sequ (0x1a338%bv : word) (0x1a348%bv : word) ltac:(left; split; reflexivity) regs0 R2 m1 m2 X8 HDI2 HRG2 HK2 Hstr8 HREST)
    as (R6 & m6 & Hms6 & HDI6 & HRG6 & HK6).
  cbv zeta in HDI6. revert HDI6. generalize (tr_flush_bits (set_block_start X8 (ds_strstart X8))); intros X10.
  generalize (if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10)); intros X11 HDI6.
  pose proof (avail_bound _ _ _ HDI6) as Hav11.
  destruct (fbm_e R6 m1 m6 X11 HDI6 HRG6) as (R7 & Hms7 & HRG7 & B10 & Hfr7).
  assert (HK7 : KEEP regs0 R7) by (keep_via HK6 Hfr7).
  destruct (avo_blk R7 m1 m6 X11 HDI6 HRG7 B10 Hav11) as (R8 & Hms8 & HRG8 & Z10 & Hfr8).
  assert (HK8 : KEEP regs0 R8) by (keep_via HK7 Hfr8).
  exists R8, m6. split; [exact HDI6|]. split; [exact HK8|].
  unfold DeflSlow6_6.avail_pc in Hms8.
  destruct (Z.eqb_spec (cs_avail_out (ds_strm X11)) 0) as [Hz|Hnz].
  - cbn [bs_code]. split; [| split; [exact (Z10 Hz) | destruct HRG8 as (_ & W2 & _); exact W2]].
    eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms6|].
    eapply msteps_trans; [exact Hms7 | exact Hms8].
  - split; [| exact HRG8].
    eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms6|].
    eapply msteps_trans; [exact Hms7 | exact Hms8].
Qed.


Lemma from_fb2 : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 ->
  flush_ok X 0 ->
  exists R M,
    DI m1 M (flush_block_only X 0) /\ KEEP regs0 R /\ HREGS R
    /\ msteps s6u_segs (mkst regs (0x1a270 : word) m s6u_rom) (mkst R (0x1a388 : word) M s6u_rom).
Proof.
  intros regs0 regs m1 m X HDI HRG HK HL1 HFO.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof HFO as HFO'. unfold flush_ok6 in HFO'. rewrite Elbs, Ews in HFO'.
  destruct HFO' as (_ & _ & Hsb & Hbs & Hstr & Hs31 & _ & Hstr8 & HREST).
  pose proof (LOC_keep _ _ _ HL1 HDI) as HLm.
  destruct (fbl_a regs m1 m X HDI HRG HLm ltac:(lia) ltac:(lia)) as (R1 & Hms1 & HRG1 & A10 & A11 & A12 & A13 & A1 & A2 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  destruct (call_fb_at regs0 R1 m1 m X (0x1a378%bv : word) 0 HDI HK1 ltac:(retok) HFO ltac:(lia) A10 A11 A12 A13 A2 A1)
    as (R2 & m2 & Hms2 & HDI2 & HK2 & Hfr2).
  assert (HRG2 : HREGS R2) by exact (HREGS_fbc _ _ HRG1 Hfr2).
  rewrite flush_block_only_eq. cbv zeta.
  revert Hstr8 HREST HDI2.
  generalize (tr_flush_block X (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None) (wrap64 (ds_strstart X - ds_block_start X)) 0).
  intros X8 Hstr8 HREST HDI2.
  destruct (fp_sequ (0x1a378%bv : word) (0x1a388%bv : word) ltac:(right; left; split; reflexivity) regs0 R2 m1 m2 X8 HDI2 HRG2 HK2 Hstr8 HREST)
    as (R6 & m6 & Hms6 & HDI6 & HRG6 & HK6).
  exists R6, m6. split; [exact HDI6|]. split; [exact HK6|]. split; [exact HRG6|].
  eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms6].
Qed.


Lemma from_fbt : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs ->
  getr regs 10 = zw S -> getr regs 11 = zw (fb_bufp X) -> getr regs 12 = zw (fb_len X) ->
  getr regs 13 = zw 1 -> getr regs 1 = (0x1a574%bv : word) ->
  0 < ds_wrap X < 2 ^ 31 ->
  flush_ok X 1 ->
  exists R M,
    DI m1 M (fst (flush_block X 1)) /\ KEEP regs0 R
    /\ msteps s6u_segs (mkst regs (0x1bff0 : word) m s6u_rom) (mkst R (0x1a608 : word) M s6u_rom)
    /\ getr R 10 = zw (match snd (flush_block X 1) with Some bs => bs_code bs | None => 3 end)
    /\ getr R 2 = zw SP.
Proof.
  intros regs0 regs m1 m X HDI HRG HK A10 A11 A12 A13 A1 Hwr HFO.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof HFO as HFO'. unfold flush_ok6 in HFO'. rewrite Elbs, Ews in HFO'.
  destruct HFO' as (_ & _ & Hsb & Hbs & Hstr & Hs31 & _ & Hstr8 & HREST).
  pose proof HRG as (P8 & P2 & _).
  destruct (call_fb_at regs0 regs m1 m X (0x1a574%bv : word) 1 HDI HK ltac:(retok) HFO ltac:(lia) A10 A11 A12 A13 P2 A1)
    as (R2 & m2 & Hms2 & HDI2 & HK2 & Hfr2).
  assert (HRG2 : HREGS R2) by exact (HREGS_fbc _ _ HRG Hfr2).
  rewrite flush_block_fst, flush_block_snd, flush_block_fst, flush_block_only_eq. cbv zeta.
  replace (negb (1 =? 0)) with true by reflexivity.
  (* 1.4: carry wrap (unchanged by the flush) and a pending bound to fbte_blk *)
  pose proof (DeflSlow6_9.tfb_wrap6 X (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None) (wrap64 (ds_strstart X - ds_block_start X)) 1) as W8.
  revert Hstr8 HREST HDI2 W8.
  generalize (tr_flush_block X (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None) (wrap64 (ds_strstart X - ds_block_start X)) 1).
  intros X8 Hstr8 HREST HDI2 W8.
  pose proof (avail_bound _ _ _ HDI2) as Hav8.
  assert (W10 : ds_wrap (tr_flush_bits (set_block_start X8 (ds_strstart X8))) = ds_wrap X)
    by (rewrite DeflSlow6_9.tfbits_wrap6; destruct X8; exact W8).
  assert (A10' : 0 <= cs_avail_out (ds_strm (tr_flush_bits (set_block_start X8 (ds_strstart X8)))))
    by (rewrite DeflSlow6_9.tfbits_strm6; destruct X8; cbn in Hav8 |- *; lia).
  pose proof HREST as HR'. cbv zeta in HR'. destruct HR' as (_ & _ & Hp10 & _).
  destruct (fp_sequ (0x1a574%bv : word) (0x1a584%bv : word) ltac:(right; right; left; split; reflexivity) regs0 R2 m1 m2 X8 HDI2 HRG2 HK2 Hstr8 HREST)
    as (R6 & m6 & Hms6 & HDI6 & HRG6 & HK6).
  cbv zeta in HDI6. revert HDI6 W10 A10' Hp10. generalize (tr_flush_bits (set_block_start X8 (ds_strstart X8))); intros X10 HDI6 W10 A10' Hp10.
  assert (P11 : 0 <= ds_pending (if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10)) < 2 ^ 31).
  { destruct (Z.eqb_spec (fp_len X10) 0); [lia|]. rewrite DeflSlow6_9.fptail_pending6.
    destruct (DeflSlow6_6.fp_len_eq X10 ltac:(lia) ltac:(lia)) as (_ & Hl1 & Hl2). lia. }
  assert (W11 : ds_wrap (if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10)) = ds_wrap X).
  { destruct (_ =? 0); [exact W10 | rewrite DeflSlow6_9.fptail_wrap6; exact W10]. }
  revert HDI6 P11 W11.
  generalize (if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10)); intros X11 HDI6 P11 W11.
  pose proof (avail_bound _ _ _ HDI6) as Hav11.
  destruct (fbte_blk R6 m1 m6 X11 HDI6 HRG6 Hav11 P11 ltac:(intros _; right; lia)) as (R8 & Hms8 & HRG8 & Z10 & Hfr8).
  assert (HK8 : KEEP regs0 R8) by (keep_via HK6 Hfr8).
  exists R8, m6. split; [exact HDI6|]. split; [exact HK8|].
  split; [eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms6 | exact Hms8]|].
  split; [| destruct HRG8 as (_ & W2 & _); exact W2].
  rewrite Z10. destruct (cs_avail_out (ds_strm X11) =? 0); reflexivity.
Qed.


Lemma from_fin : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs ->
  getr regs 10 = zw S -> getr regs 11 = zw (fb_bufp X) -> getr regs 12 = zw (fb_len X) ->
  getr regs 13 = zw 0 -> getr regs 1 = (0x1a5dc%bv : word) ->
  flush_ok X 0 ->
  exists R M,
    DI m1 M (fst (flush_block X 0)) /\ KEEP regs0 R
    /\ msteps s6u_segs (mkst regs (0x1bff0 : word) m s6u_rom) (mkst R (0x1a608 : word) M s6u_rom)
    /\ getr R 10 = zw (match snd (flush_block X 0) with Some bs => bs_code bs | None => 1 end)
    /\ getr R 2 = zw SP.
Proof.
  intros regs0 regs m1 m X HDI HRG HK A10 A11 A12 A13 A1 HFO.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof HFO as HFO'. unfold flush_ok6 in HFO'. rewrite Elbs, Ews in HFO'.
  destruct HFO' as (_ & _ & Hsb & Hbs & Hstr & Hs31 & _ & Hstr8 & HREST).
  pose proof HRG as (P8 & P2 & _).
  destruct (call_fb_at regs0 regs m1 m X (0x1a5dc%bv : word) 0 HDI HK ltac:(retok) HFO ltac:(lia) A10 A11 A12 A13 P2 A1)
    as (R2 & m2 & Hms2 & HDI2 & HK2 & Hfr2).
  assert (HRG2 : HREGS R2) by exact (HREGS_fbc _ _ HRG Hfr2).
  rewrite flush_block_fst, flush_block_snd, flush_block_fst, flush_block_only_eq. cbv zeta.
  replace (negb (0 =? 0)) with false by reflexivity.
  revert Hstr8 HREST HDI2.
  generalize (tr_flush_block X (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None) (wrap64 (ds_strstart X - ds_block_start X)) 0).
  intros X8 Hstr8 HREST HDI2.
  destruct (fp_sequ (0x1a5dc%bv : word) (0x1a5ec%bv : word) ltac:(right; right; right; split; reflexivity) regs0 R2 m1 m2 X8 HDI2 HRG2 HK2 Hstr8 HREST)
    as (R6 & m6 & Hms6 & HDI6 & HRG6 & HK6).
  cbv zeta in HDI6. revert HDI6. generalize (tr_flush_bits (set_block_start X8 (ds_strstart X8))); intros X10.
  generalize (if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10)); intros X11 HDI6.
  pose proof (avail_bound _ _ _ HDI6) as Hav11.
  destruct (fine_blk R6 m1 m6 X11 HDI6 HRG6 Hav11) as (R8 & Hms8 & HRG8 & Z10 & Hfr8).
  assert (HK8 : KEEP regs0 R8) by (keep_via HK6 Hfr8).
  unfold DeflSlow6_6.avail_pc in Hms8.
  destruct (Z.eqb_spec (cs_avail_out (ds_strm X11)) 0) as [Hz|Hnz].
  - exists R8, m6. split; [exact HDI6|]. split; [exact HK8|].
    split; [eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms6 | exact Hms8]|].
    split; [cbn [bs_code]; exact (Z10 Hz) | destruct HRG8 as (_ & W2 & _); exact W2].
  - destruct (b84_blk R8 m6 HRG8) as (R9 & Hms9 & HRG9 & Z1 & Hfr9).
    exists R9, m6. split; [exact HDI6|]. split; [keep_via HK8 Hfr9|].
    split; [eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms8 | exact Hms9]|].
    split; [exact Z1 | destruct HRG9 as (_ & W2 & _); exact W2].
Qed.



Local Abbreviation sdist_ok := (DeflSlow6_M.sdist_ok FBSAFE).
Local Abbreviation slit_ok := (DeflSlow6_M.slit_ok6 FBSAFE ws).
Local Abbreviation sdec_ok := (DeflSlow6_M.sdec_ok FBSAFE ws).
Local Abbreviation shash_ok := (DeflSlow6_M.shash_ok FBSAFE ws).
Local Abbreviation strip_ok := (DeflSlow6_M.strip_ok FBSAFE ws hs).
Local Abbreviation ILS := (DeflSlow6_5.ILS).
Local Abbreviation insl_st := (DeflSlow6_6.insl_st).
Local Abbreviation exit_st := (DeflSlow6_6.exit_st).
Local Abbreviation dist_st := (DeflSlow6_5.dist_st).
Local Abbreviation slit1 := (DeflSlow6_3.slit1).


Definition EXITS (regs : bvmap 5 word) (pc : word) (m : word -> option byte)
           (R : bvmap 5 word) (M : word -> option byte) (r : deflate_state * loop_out) : Prop :=
  match snd r with
  | LCont => HREGS R /\ msteps s6u_segs (mkst regs pc m s6u_rom) (mkst R (0x19da8 : word) M s6u_rom)
  | LBreak => HREGS R /\ msteps s6u_segs (mkst regs pc m s6u_rom) (mkst R (0x1a3c4 : word) M s6u_rom)
  | LRet bs => getr R 10 = zw (bs_code bs) /\ getr R 2 = zw SP
               /\ msteps s6u_segs (mkst regs pc m s6u_rom) (mkst R (0x1a608 : word) M s6u_rom)
  end.

Lemma EXITS_pre : forall regs regs' (pc pc' : word) m m' R M r,
  msteps s6u_segs (mkst regs pc m s6u_rom) (mkst regs' pc' m' s6u_rom) ->
  EXITS regs' pc' m' R M r -> EXITS regs pc m R M r.
Proof.
  intros regs regs' pc pc' m m' R M [X o] Hms HE. unfold EXITS in *. cbn [fst snd] in *.
  destruct o as [| |bs].
  - destruct HE as (A & B). split; [exact A | eapply msteps_trans; [exact Hms | exact B]].
  - destruct HE as [A B]. split; [exact A | eapply msteps_trans; [exact Hms | exact B]].
  - destruct HE as (A & A' & B). split; [exact A|]. split; [exact A' | eapply msteps_trans; [exact Hms | exact B]].
Qed.


Definition ILIS (X : deflate_state) : Prop :=
  0 <= ds_strstart X /\ 0 <= ds_ins_h X < 2 ^ 31 /\ ds_hash_mask X = hs - 1 /\ ds_w_mask X = ws - 1 /\ 0 <= ds_hash_shift X < 32
  /\ (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256)
  /\ (forall j, 0 <= j < hs -> 0 <= arr_get (ds_head X) j < 65536)
  /\ arr_len (ds_head X) = hs.

Lemma ILIS_step : forall X mi, ILIS X ->
  ILIS (insl_st X mi) /\ ds_strstart (insl_st X mi) = ds_strstart X + 1 /\ ds_prev_length (insl_st X mi) = ds_prev_length X - 1
  /\ ds_sym_next (insl_st X mi) = ds_sym_next X /\ ds_sym_end (insl_st X mi) = ds_sym_end X
  /\ ds_lookahead (insl_st X mi) = ds_lookahead X /\ ds_window (insl_st X mi) = ds_window X.
Proof.
  intros X mi (Hs & Hih & Hhm & Hwm & Hsh & Hwb & Hhb & Lh). pose proof (DeflSlow6_1.wf_hsz _ HWF) as Whs.
  unfold ILIS, DeflSlow6_6.insl_st, DeflSlow6_2.ins_str. destruct (ds_strstart X + 1 <=? mi); dsred.
  - pose proof (update_hash_range (set_strstart X (ds_strstart X + 1)) (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 1 + 2)) ltac:(dsred; lia)) as Hh.
    dsred in Hh. rewrite Hhm in Hh.
    set (h := update_hash _ _ _) in *.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try reflexivity.
    + intros j Hj; rewrite arr_get_set; destruct (_ && _); [pose proof (wrap16_range (ds_strstart X + 1)); lia | apply Hhb; exact Hj].
    + rewrite arr_len_set; exact Lh.
  - repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try reflexivity.
Qed.

Lemma ins_loop : forall n regs0 regs m1 m X mi sn se,
  DI m1 m X -> HREGS regs -> ILS regs (ds_strstart X + 1) mi (ds_prev_length X - 1) sn se -> KEEP regs0 regs -> ILIS X ->
  ds_prev_length X = Z.of_nat n -> (1 <= n)%nat -> Z.of_nat n <= 258 -> ds_strstart X + Z.of_nat n + 2 < 2 ^ 31 ->
  0 <= mi < 2 ^ 32 -> mi + 3 <= 2 * ws -> 0 <= sn < 2 ^ 32 -> 0 <= se < 2 ^ 32 ->
  exists R M,
    msteps s6u_segs (mkst regs (0x1a0b4 : word) m s6u_rom) (mkst R (0x1a2b4 : word) M s6u_rom)
    /\ DI m1 M (deflate_slow_insert n X mi) /\ HREGS R
    /\ ILS R (ds_strstart (deflate_slow_insert n X mi) + 1) mi (ds_prev_length (deflate_slow_insert n X mi) - 1) sn se
    /\ KEEP regs0 R /\ ILIS (deflate_slow_insert n X mi)
    /\ ds_prev_length (deflate_slow_insert n X mi) = 0 /\ ds_strstart (deflate_slow_insert n X mi) = ds_strstart X + Z.of_nat n
    /\ ds_sym_next (deflate_slow_insert n X mi) = ds_sym_next X /\ ds_sym_end (deflate_slow_insert n X mi) = ds_sym_end X
    /\ ds_lookahead (deflate_slow_insert n X mi) = ds_lookahead X.
Proof.
  induction n as [|n IH]; intros regs0 regs m1 m X mi sn se HDI HRG HIL HK HILI Hpl Hn Hn8 Hroom Hmi Hmi3 Hsn Hse; [lia|].
  pose proof HILI as (Hs & Hih & Hhm & Hwm & Hsh & Hwb & Hhb & Lh).
  destruct (insl_blk regs m1 m X mi sn se HDI HRG HIL ltac:(lia) Hs ltac:(lia) ltac:(lia) Hmi Hih Hhm Hwm Hsh Hsn Hse Hwb Hhb)
    as (R1 & M1 & Hms1 & HDI1 & HRG1 & HIL1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  destruct (ILIS_step X mi HILI) as (HILI1 & E1s & E1m & E1n & E1e & E1l & E1w).
  rewrite deflate_slow_insert_step. cbv zeta. change (DeflSlow6_6.insl_st X mi) with (insl_st X mi). rewrite E1m, Hpl.
  unfold insl_pc in Hms1. rewrite Hpl in Hms1.
  destruct n as [|n'].
  - replace (Z.of_nat 1 =? 1) with true in Hms1 by reflexivity.
    replace (Z.of_nat 1 - 1 =? 0) with true by reflexivity. cbn [negb].
    exists R1, M1. split; [exact Hms1|]. split; [exact HDI1|]. split; [exact HRG1|]. split; [exact HIL1|]. split; [exact HK1|].
    split; [exact HILI1|]. rewrite E1m, E1s, E1n, E1e, E1l, Hpl. repeat split; lia.
  - replace (Z.of_nat (Datatypes.S (Datatypes.S n')) =? 1) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.of_nat (Datatypes.S (Datatypes.S n')) - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    destruct (IH regs0 R1 m1 M1 (insl_st X mi) mi sn se HDI1 HRG1 HIL1 HK1 HILI1 ltac:(rewrite E1m, Hpl; lia) ltac:(lia) ltac:(lia) ltac:(rewrite E1s; lia) Hmi Hmi3 Hsn Hse)
      as (R2 & M2 & Hms2 & HDI2 & HRG2 & HIL2 & HK2 & HILI2 & E2m & E2s & E2n & E2e & E2l).
    exists R2, M2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HDI2|]. split; [exact HRG2|]. split; [exact HIL2|]. split; [exact HK2|]. split; [exact HILI2|].
    rewrite E2m, E2s, E2n, E2e, E2l, E1s, E1n, E1e, E1l. repeat split; lia.
Qed.


Lemma st_bflush_false : forall s, st_bflush s false = (s, LCont).
Proof. reflexivity. Qed.

Lemma st_bflush_true : forall s,
  st_bflush s true = (fst (flush_block s 0), match snd (flush_block s 0) with Some bs => LRet bs | None => LCont end).
Proof. intros s. unfold st_bflush. destruct (flush_block s 0) as [s' [bs|]]; reflexivity. Qed.

Lemma from_dist : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> PLR regs X -> KEEP regs0 regs -> LOC m1 ->
  strip_inv X -> 1 <= ds_lookahead X <= 2 * ws -> dist_cond X = true -> sdist_ok X ->
  exists R M, DI m1 M (fst (st_bflush (fst (st_sdist X)) (snd (st_sdist X)))) /\ KEEP regs0 R
    /\ EXITS regs (0x19f2c : word) m R M (st_bflush (fst (st_sdist X)) (snd (st_sdist X))).
Proof.
  intros regs0 regs m1 m X HDI HRG HPL HK HL1 HTI Hlk Hdc (Dpl & Dsl & DD & Dfl7).
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws. pose proof (DeflSlow6_1.wf_hsz _ HWF) as Whs. pose proof (wf_lbs _ HWF) as Wlbs.
  unfold dist_cond in Hdc. apply andb_prop in Hdc. destruct Hdc as [Hdc1 Hdc2]. apply Z.leb_le in Hdc1. apply Z.leb_le in Hdc2.
  destruct HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
  rewrite Ews in *. rewrite Ehs in *. rewrite Elbs in *.
  destruct (sdist_eq X ltac:(lia) Dpl ltac:(lia) Dsl ltac:(lia)) as [E1 E2]. rewrite E1, E2 in *. clear E1 E2.
  destruct (dist_blk regs m1 m X HDI HRG HPL ltac:(lia) ltac:(lia) Tpm ltac:(lia) Dsl Dpl ltac:(lia) ltac:(lia) Tse Tlfc Tdfc DD)
    as (R1 & M1 & Hms1 & HDI1 & HRG1 & HIL1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  assert (V1 : (ds_prev_length (dist_st X), ds_strstart (dist_st X), ds_lookahead (dist_st X), ds_sym_next (dist_st X), ds_sym_end (dist_st X),
                ds_ins_h (dist_st X), ds_hash_mask (dist_st X), ds_w_mask (dist_st X), ds_hash_shift (dist_st X), ds_window (dist_st X), ds_head (dist_st X))
               = (ds_prev_length X - 2, ds_strstart X, ds_lookahead X + 1 - ds_prev_length X, ds_sym_next X + 3, ds_sym_end X,
                  ds_ins_h X, ds_hash_mask X, ds_w_mask X, ds_hash_shift X, ds_window X, ds_head X)).
  { unfold DeflSlow6_5.dist_st. dsred. reflexivity. }
  revert HDI1 V1 Dfl7. generalize (dist_st X). intros U HDI1 V1 Dfl7.
  injection V1 as Upl Ustr Ulk Usn Use Uih Uhm Uwm Ush Uw Uhd.
  assert (HILI1 : ILIS U).
  { unfold ILIS. rewrite Ustr, Uih, Uhm, Uwm, Ush, Uw, Uhd.
    repeat match goal with |- _ /\ _ => split end; first [exact Tih | exact Twb | exact Thb | exact Tlh | lia]. }
  set (n := Z.to_nat (ds_prev_length X - 2)) in *.
  replace (ds_strstart X + 1) with (ds_strstart U + 1) in HIL1 by lia.
  replace (ds_prev_length X - 3) with (ds_prev_length U - 1) in HIL1 by lia.
  destruct (ins_loop n regs0 R1 m1 M1 U _ _ _ HDI1 HRG1 HIL1 HK1 HILI1
              ltac:(subst n; rewrite Upl; lia) ltac:(subst n; lia) ltac:(subst n; lia) ltac:(subst n; rewrite Ustr; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (R4 & M4 & Hms4 & HDI4 & HRG4 & HIL4 & HK4 & HILI4 & E4m & E4s & E4n & E4e & E4l).
  rewrite Ustr, Usn, Use, Ulk in *.
  revert HDI4 HIL4 HILI4 E4m E4s E4n E4e E4l Dfl7 Hms4. generalize (deflate_slow_insert n U (ds_strstart X + ds_lookahead X - 3)).
  intros XL HDI4 HIL4 HILI4 E4m E4s E4n E4e E4l Dfl7 Hms4.
  destruct (exit_blk R4 m1 M4 XL (ds_strstart X + ds_lookahead X - 3) (ds_sym_next X + 3) (ds_sym_end X)
              HDI4 HRG4 HIL4 ltac:(rewrite E4s; lia) ltac:(rewrite E4s; subst n; lia) ltac:(lia) ltac:(lia))
    as (R5 & M5 & Hms5 & HDI5 & HRG5 & B10 & Hfr5).
  assert (HK5 : KEEP regs0 R5) by (keep_via HK4 Hfr5).
  assert (V5 : ds_strstart (exit_st XL) = ds_strstart XL + 1) by (unfold DeflSlow6_6.exit_st; dsred; reflexivity).
  revert HDI5 Dfl7 V5. generalize (exit_st XL). intros X8 HDI5 Dfl7 V5.
  rewrite <- V5 in B10.
  assert (Hms15 : msteps s6u_segs (mkst regs (0x19f2c : word) m s6u_rom) (mkst R5 (exit_pc (ds_sym_next X + 3) (ds_sym_end X)) M5 s6u_rom)).
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms4 | exact Hms5]. }
  clear Hms1 Hms4 Hms5. unfold exit_pc in Hms15.
  destruct (ds_sym_next X + 3 =? ds_sym_end X).
  -
    rewrite st_bflush_true.
    destruct (from_fb1 regs0 R5 m1 M5 X8 HDI5 HRG5 HK5 HL1 B10 (Dfl7 eq_refl)) as (R6 & M6 & HDI6 & HK6 & HX6).
    revert HDI6 HX6. generalize (fst (flush_block X8 0)). intros X9 HDI6 HX6.
    exists R6, M6. split; [exact HDI6|]. split; [exact HK6|].
    unfold EXITS. cbn [fst snd]. destruct (snd (flush_block X8 0)) as [bs|].
    + destruct HX6 as (Hms6 & A10 & A2). split; [exact A10|]. split; [exact A2|]. eapply msteps_trans; [exact Hms15 | exact Hms6].
    + destruct HX6 as (Hms6 & HRG6). split; [exact HRG6|]. eapply msteps_trans; [exact Hms15 | exact Hms6].
  - rewrite st_bflush_false.
    exists R5, M5. split; [exact HDI5|]. split; [exact HK5|]. unfold EXITS. cbn [fst snd]. split; [exact HRG5 | exact Hms15].
Qed.


Lemma ltail_avail : forall X, cs_avail_out (ds_strm (ltail_st X)) = cs_avail_out (ds_strm X).
Proof. intros X. unfold DeflSlow6_2.ltail_st. dsred. reflexivity. Qed.

Lemma from_mavail : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 ->
  strip_inv X -> 1 <= ds_lookahead X <= 2 * ws -> (ds_match_available X <> 0 -> slit_ok X) ->
  let r := if negb (ds_match_available X =? 0) then st_slit X else st_avail X in
  exists R M, DI m1 M (fst r) /\ KEEP regs0 R /\ EXITS regs (0x1a180 : word) m R M r.
Proof.
  intros regs0 regs m1 m X HDI HRG HK HL1 HTI Hlk HLO.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws. pose proof (wf_lbs _ HWF) as Wlbs.
  destruct HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
  rewrite Ews in *. rewrite Ehs in *. rewrite Elbs in *.
  destruct (mavail_blk regs m1 m X HDI HRG Tma) as (R1 & Hms1 & HRG1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  unfold mavail_pc in Hms1. cbv zeta.
  destruct (Z.eqb_spec (ds_match_available X) 0) as [Hz|Hnz]; cbn [negb].
  -
    rewrite st_avail_eq.
    destruct (avail0_blk R1 m1 m X HDI HRG1 Tstr ltac:(lia) Tsl) as (R2 & M2 & Hms2 & HDI2 & HRG2 & Hfr2).
    exists R2, M2. split; [exact HDI2|]. split; [keep_via HK1 Hfr2|].
    unfold EXITS. cbn [fst snd]. split; [exact HRG2 | eapply msteps_trans; [exact Hms1 | exact Hms2]].
  -
    destruct (HLO Hnz) as (Ls1 & Lfl & Ls2 & Ll2 & Lsl2). clear HLO.
    rewrite st_slit_eq. cbv zeta.
    destruct (slit_blk R1 m1 m X HDI HRG1 ltac:(lia) ltac:(lia) ltac:(lia) Tse Twb Tlfc) as (R2 & M2 & Hms2 & HDI2 & HRG2 & Hfr2).
    assert (HK2 : KEEP regs0 R2) by (keep_via HK1 Hfr2).
    unfold slit_pc in Hms2.
    revert HDI2 Lfl Ls2 Ll2 Lsl2. change (DeflSlow6_3.slit1 X) with (slit1 X). generalize (slit1 X). intros X1 HDI2 Lfl Ls2 Ll2 Lsl2.
    assert (MID : exists R3 M3,
              msteps s6u_segs (mkst regs (0x1a180 : word) m s6u_rom) (mkst R3 (0x1a388 : word) M3 s6u_rom)
              /\ DI m1 M3 (if ds_sym_next X + 3 =? ds_sym_end X then flush_block_only X1 0 else X1)
              /\ HREGS R3 /\ KEEP regs0 R3).
    { destruct (ds_sym_next X + 3 =? ds_sym_end X).
      - destruct (from_fb2 regs0 R2 m1 M2 X1 HDI2 HRG2 HK2 HL1 (Lfl eq_refl)) as (R3 & M3 & HDI3 & HK3 & HRG3 & Hms3).
        exists R3, M3. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        split; [exact HDI3|]. split; [exact HRG3 | exact HK3].
      - exists R2, M2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        split; [exact HDI2|]. split; [exact HRG2 | exact HK2]. }
    destruct MID as (R3 & M3 & Hms3 & HDI3 & HRG3 & HK3).
    revert HDI3 Ls2 Ll2 Lsl2. generalize (if ds_sym_next X + 3 =? ds_sym_end X then flush_block_only X1 0 else X1). intros X2 HDI3 Ls2 Ll2 Lsl2.
    pose proof (avail_bound _ _ _ HDI3) as Hav2.
    destruct (ltail_blk R3 m1 M3 X2 HDI3 HRG3 Ls2 Ll2 Lsl2) as (R4 & M4 & Hms4 & HDI4 & HRG4 & B10 & Hfr4).
    assert (HK4 : KEEP regs0 R4) by (keep_via HK3 Hfr4).
    rewrite ltail_avail.
    pose proof Hav2 as Hav4. rewrite <- (ltail_avail X2) in Hav4.
    destruct (avo_blk R4 m1 M4 (ltail_st X2) HDI4 HRG4 B10 Hav4) as (R5 & Hms5 & HRG5 & Z10 & Hfr5).
    assert (HK5 : KEEP regs0 R5) by (keep_via HK4 Hfr5).
    rewrite ltail_avail in Z10. unfold DeflSlow6_6.avail_pc in Hms5. rewrite ltail_avail in Hms5.
    exists R5, M4. split; [exact HDI4|]. split; [exact HK5|].
    unfold EXITS. destruct (Z.eqb_spec (cs_avail_out (ds_strm X2)) 0) as [Az|Anz]; cbn [fst snd bs_code].
    + split; [exact (Z10 Az)|]. split; [destruct HRG5 as (_ & W2 & _); exact W2|].
      eapply msteps_trans; [exact Hms3|]. eapply msteps_trans; [exact Hms4 | exact Hms5].
    + split; [exact HRG5 | eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4 | exact Hms5]].
Qed.


Lemma from_dec : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw (ds_match_length X) -> KEEP regs0 regs -> LOC m1 -> sdec_ok X ->
  exists R M, DI m1 M (fst (st_decide X)) /\ KEEP regs0 R /\ EXITS regs (0x19f20 : word) m R M (st_decide X).
Proof.
  intros regs0 regs m1 m X HDI HRG Q10 HK HL1 (HTI & Hlk & HD).
  pose proof HTI as [_ _ _ _ _ _ _ Tml _ Tpl _ _ _ _ _ _ _ _ _ _ _ _].
  destruct (dec_blk regs m1 m X HDI HRG Q10 Tpl Tml) as (R1 & Hms1 & HRG1 & HPL1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  unfold dec_pc, DeflSlow6_3.dec_cond in Hms1. unfold st_decide. change (DeflSlow6_M.dist_cond X) with ((3 <=? ds_prev_length X) && (ds_match_length X <=? ds_prev_length X))%bool in *.
  destruct ((3 <=? ds_prev_length X) && (ds_match_length X <=? ds_prev_length X))%bool eqn:Edc.
  - destruct (from_dist regs0 R1 m1 m X HDI HRG1 HPL1 HK1 HL1 HTI Hlk Edc HD) as (R & M & A & B & C).
    exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
  - edestruct (from_mavail regs0 R1 m1 m X HDI HRG1 HK1 HL1 HTI Hlk) as (R & M & A & B & C).
    { intros Hnz. destruct (Z.eqb_spec (ds_match_available X) 0); [lia|]. exact HD. }
    exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
Qed.


Lemma HREGS_lm : forall R R',
  HREGS R -> getr R' 2 = zw SP -> getr R' 8 = getr R 8 -> getr R' 9 = getr R 9 -> getr R' 18 = getr R 18 -> getr R' 19 = getr R 19 ->
  getr R' 20 = getr R 20 -> getr R' 21 = getr R 21 -> getr R' 22 = getr R 22 -> getr R' 23 = getr R 23 -> getr R' 24 = getr R 24 ->
  getr R' 25 = getr R 25 -> getr R' 26 = getr R 26 -> getr R' 27 = getr R 27 -> HREGS R'.
Proof.
  intros R R' (A8 & A2 & A9 & A19 & A20 & A27 & A21 & A18 & A22 & A23 & A25 & A26 & A24) B2 B8 B9 B18 B19 B20 B21 B22 B23 B24 B25 B26 B27. unfold HREGS.
  rewrite B2, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27.
  repeat split; assumption.
Qed.

Lemma HREGS_fw : forall R R',
  HREGS R -> getr R' 2 = zw SP ->
  (forall r : reg, reg_in r c_clob = false -> getr R' r = getr R r) -> HREGS R'.
Proof.
  intros R R' (A8 & A2 & A9 & A19 & A20 & A27 & A21 & A18 & A22 & A23 & A25 & A26 & A24) B2 Hfr. unfold HREGS.
  rewrite B2, (Hfr 8%bv eq_refl), (Hfr 9%bv eq_refl), (Hfr 19%bv eq_refl), (Hfr 20%bv eq_refl), (Hfr 27%bv eq_refl), (Hfr 21%bv eq_refl),
          (Hfr 18%bv eq_refl), (Hfr 22%bv eq_refl), (Hfr 23%bv eq_refl), (Hfr 25%bv eq_refl), (Hfr 26%bv eq_refl), (Hfr 24%bv eq_refl).
  repeat split; assumption.
Qed.


Lemma from_lm : forall regs0 regs m1 m X3 hh,
  DI m1 m X3 -> HREGS regs -> getr regs 10 = zw S -> getr regs 11 = zw hh -> getr regs 1 = (0x19ee0%bv : word) -> KEEP regs0 regs -> LOC m1 ->
  0 <= hh < 65536 -> 0 <= ds_strstart X3 <= 2 * ws -> 0 <= ds_strategy X3 <= 4 ->
  sl_lm_cond X3 hh = true -> lm_ok6 X3 hh -> sdec_ok (st_lm X3 hh) ->
  exists R M, DI m1 M (fst (st_decide (st_lm X3 hh))) /\ KEEP regs0 R /\ EXITS regs (0x1a648%bv : word) m R M (st_decide (st_lm X3 hh)).
Proof.
  intros regs0 regs m1 m X3 hh HDI HRG A10 A11 A1 HK HL1 Hhh Hstr Hstrat Hc HLM HSD.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  rewrite (st_lm_true X3 hh Hc) in HSD |- *. cbv zeta in HSD. cbv zeta.
  destruct HLM as (Lwb & Lpb & Ls0 & Ls258 & Lwm & Lpl & Lnice & Llook & Lgood & Lchain & Lch1 & Lcur & Lvis & Lml).
  rewrite Ews in *.
  pose proof HRG as (P8 & P2 & Prest).
  destruct (call_lm regs m1 m X3 hh (0x19ee0%bv : word) HDI ltac:(retok) Lwb Lpb Ls0 Ls258 Lwm Lpl Lnice Llook Lgood Lchain Lch1 ltac:(lia) Lvis
              A1 P2 A10 A11)
    as (R2 & M2 & ms & Hms2 & Ems & HDI2 & C10 & C2 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27 & Hfr2).
  assert (HK2 : KEEP regs0 R2). { destruct HK as [K3 K4]. split; [rewrite (Hfr2 3%bv eq_refl); exact K3 | rewrite (Hfr2 4%bv eq_refl); exact K4]. }
  assert (HRG2 : HREGS R2) by (apply (HREGS_lm regs R2 HRG C2 C8 C9 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27)).
  rewrite Ems in HSD |- *.
  revert HSD C10 Lml. generalize (snd (longest_match X3 hh)). intros ml HSD C10 Lml.
  rewrite sl_filter_eq in HSD |- *.
  assert (Hms32 : 0 <= ms < 2 ^ 32).
  { destruct (_ && _) in HSD; destruct HSD as ([_ _ _ _ _ _ _ _ Tms _ _ _ _ _ _ _ _ _ _ _ _ _] & _); exact Tms. }
  assert (Vst : ds_strategy (set_match_start X3 ms) = ds_strategy X3) by reflexivity.
  destruct (lmret_blk R2 m1 M2 (set_match_start X3 ms) ml HDI2 HRG2 HL1 C10 Lml ltac:(rewrite Vst; exact Hstrat)
              ltac:(dsred; exact Hstr) ltac:(dsred; exact Hms32))
    as (R3 & M3 & Hms3 & HDI3 & HRG3 & D10 & Hfr3).
  assert (HK3 : KEEP regs0 R3) by (keep_via HK2 Hfr3).
  unfold lmret_pc, DeflSlow6_3.lm_filter in Hms3, D10. rewrite Vst in Hms3, D10.
  replace (ds_strstart (set_match_start X3 ms)) with (ds_strstart X3) in Hms3, D10 by reflexivity.
  replace (ds_match_start (set_match_start X3 ms)) with ms in Hms3, D10 by reflexivity.
  set (XM := set_match_length (set_match_start X3 ms) ml) in *.
  assert (VMml : ds_match_length XM = ml) by reflexivity.
  assert (Hms13 : msteps s6u_segs (mkst regs (0x1a648%bv : word) m s6u_rom)
                    (mkst R3 (if (ml <=? 5) && ((ds_strategy X3 =? 1) || (ml =? 3) && (4096 <? wrap32 (ds_strstart X3 - ms)))
                              then (0x19ef8%bv : word) else (0x19f20%bv : word)) M3 s6u_rom))
    by (eapply msteps_trans; [exact Hms2 | exact Hms3]).
  clear Hms2 Hms3. clearbody XM.
  destruct ((ml <=? 5) && ((ds_strategy X3 =? 1) || (ml =? 3) && (4096 <? wrap32 (ds_strstart X3 - ms))))%bool.
  -
    destruct (lm2_blk R3 m1 M3 XM HDI3 HRG3) as (R4 & M4 & Hms4 & HDI4 & HRG4 & G10 & Hfr4).
    destruct (from_dec regs0 R4 m1 M4 (set_match_length XM 2) HDI4 HRG4 G10 ltac:(keep_via HK3 Hfr4) HL1 HSD) as (R & M & A & B & C).
    exists R, M. split; [exact A|]. split; [exact B|].
    exact (EXITS_pre _ _ _ _ _ _ _ _ _ ltac:(eapply msteps_trans; [exact Hms13 | exact Hms4]) C).
  - destruct (from_dec regs0 R3 m1 M3 XM HDI3 HRG3 ltac:(rewrite VMml; exact (D10 eq_refl)) HK3 HL1 HSD) as (R & M & A & B & C).
    exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms13 C).
Qed.


Lemma from_setup : forall regs0 regs m1 m XI hh,
  DI m1 m XI -> HREGS regs -> getr regs 11 = zw hh -> KEEP regs0 regs -> LOC m1 ->
  0 <= hh < 65536 -> 0 <= ds_strstart XI <= 2 * ws -> 0 <= ds_match_length XI <= 258 -> 0 <= ds_match_start XI < 2 ^ 32 ->
  0 <= ds_max_lazy_match XI < 2 ^ 31 -> 0 <= ds_strategy XI <= 4 ->
  (sl_lm_cond (prev_st XI) hh = true -> lm_ok6 (prev_st XI) hh) -> sdec_ok (st_lm (prev_st XI) hh) ->
  exists R M, DI m1 M (fst (st_decide (st_lm (prev_st XI) hh))) /\ KEEP regs0 R
    /\ EXITS regs (0x19ea0%bv : word) m R M (st_decide (st_lm (prev_st XI) hh)).
Proof.
  intros regs0 regs m1 m XI hh HDI HRG Q11 HK HL1 Hhh Hstr Hml Hms0 Hlz Hstrat HLM HSD.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  destruct (setup_blk regs m1 m XI hh HDI HRG Q11 Hhh Hstr Hml Hms0 Hlz) as (R1 & M1 & Hms1 & HDI1 & HRG1 & A11 & ALM & ANLM & A2 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  assert (Esp : setup_pc XI hh = (if sl_lm_cond (prev_st XI) hh then (0x1a648%bv : word) else (0x19f20%bv : word))).
  { unfold setup_pc, sl_lm_cond. replace (ds_prev_length (prev_st XI)) with (ds_match_length XI) by reflexivity.
    replace (ds_max_lazy_match (prev_st XI)) with (ds_max_lazy_match XI) by reflexivity.
    replace (ds_strstart (prev_st XI)) with (ds_strstart XI) by reflexivity.
    replace (ds_w_size (prev_st XI)) with (ds_w_size XI) by reflexivity. rewrite Ews.
    destruct (Z.eqb_spec hh 0); cbn [negb andb]; [reflexivity|].
    destruct (Z.leb_spec (ds_max_lazy_match XI) (ds_match_length XI)); destruct (Z.ltb_spec (ds_match_length XI) (ds_max_lazy_match XI)); cbn [andb]; try lia; [reflexivity|].
    destruct (wrap32 (ds_strstart XI - hh) <=? ws - 262); reflexivity. }
  rewrite Esp in Hms1, ALM, ANLM.
  destruct (Bool.bool_dec (sl_lm_cond (prev_st XI) hh) true) as [Ec|Ec]; [| apply Bool.not_true_is_false in Ec]; rewrite Ec in Hms1, ALM, ANLM.
  -
    destruct (ALM eq_refl) as [B10 B1].
    destruct (from_lm regs0 R1 m1 M1 (prev_st XI) hh HDI1 HRG1 B10 A11 B1 HK1 HL1 Hhh
                ltac:(change (ds_strstart (prev_st XI)) with (ds_strstart XI); lia)
                ltac:(change (ds_strategy (prev_st XI)) with (ds_strategy XI); exact Hstrat) Ec (HLM Ec) HSD)
      as (R & M & A & B & C).
    exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
  - rewrite (st_lm_false _ _ Ec) in HSD |- *.
    assert (B10 : getr R1 10 = zw (ds_match_length (prev_st XI))) by (change (ds_match_length (prev_st XI)) with 2; apply ANLM; discriminate).
    destruct (from_dec regs0 R1 m1 M1 (prev_st XI) HDI1 HRG1 B10 HK1 HL1 HSD) as (R & M & A & B & C).
    exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
Qed.


Lemma from_ins : forall regs0 regs m1 m X1,
  DI m1 m X1 -> HREGS regs -> KEEP regs0 regs -> LOC m1 -> 3 <= ds_lookahead X1 -> shash_ok X1 ->
  exists R M, DI m1 M (fst (st_srest X1)) /\ KEEP regs0 R /\ EXITS regs (0x19dd0%bv : word) m R M (st_srest X1).
Proof.
  intros regs0 regs m1 m X1 HDI HRG HK HL1 Hl3 HSH.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws. pose proof (DeflSlow6_1.wf_hsz _ HWF) as Whs.
  destruct (shash_ok_hi _ _ X1 HSH Hl3) as (HTI & Hlk & HLM & HSD). clear HSH.
  rewrite (st_srest_hi X1 Hl3).
  pose proof HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
  rewrite Ews, Ehs in *.
  destruct (ins_blk regs m1 m X1 HDI HRG Tstr ltac:(lia) Tih Thm Twm Ths Twb Thb)
    as (R1 & M1 & Hms1 & HDI1 & HRG1 & A11 & A10 & Hfr1).
  cbv zeta in Hms1, HDI1, A11, A10.
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  fold (hash_hh X1) in A11.
  pose proof (hash_hi_eq X1 Hl3) as [E1 _]. rewrite (st_hash_hi X1 Hl3) in E1. cbn [fst] in E1.
  assert (Hhh : 0 <= hash_hh X1 < 65536).
  { unfold hash_hh. apply Thb. pose proof (update_hash_range X1 (ds_ins_h X1) (arr_get (ds_window X1) (ds_strstart X1 + 2)) ltac:(rewrite Thm; lia)) as Hu. rewrite Thm in Hu. lia. }
  rewrite <- E1 in HLM, HSD |- *.
  destruct (from_setup regs0 R1 m1 M1 (ins_str X1 (ds_strstart X1)) (hash_hh X1) HDI1 HRG1 A11 HK1 HL1 Hhh
              ltac:(change (ds_strstart (ins_str X1 (ds_strstart X1))) with (ds_strstart X1); lia)
              ltac:(change (ds_match_length (ins_str X1 (ds_strstart X1))) with (ds_match_length X1); exact Tml)
              ltac:(change (ds_match_start (ins_str X1 (ds_strstart X1))) with (ds_match_start X1); exact Tms)
              ltac:(change (ds_max_lazy_match (ins_str X1 (ds_strstart X1))) with (ds_max_lazy_match X1); exact Tlazy)
              ltac:(change (ds_strategy (ins_str X1 (ds_strstart X1))) with (ds_strategy X1); exact Tstrat)
              HLM HSD)
    as (R & M & A & B & C).
  exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
Qed.

Lemma from_nil : forall regs0 regs m1 m X1,
  DI m1 m X1 -> HREGS regs -> KEEP regs0 regs -> LOC m1 -> 1 <= ds_lookahead X1 -> ds_lookahead X1 < 3 -> shash_ok X1 ->
  exists R M, DI m1 M (fst (st_srest X1)) /\ KEEP regs0 R /\ EXITS regs (0x19e9c%bv : word) m R M (st_srest X1).
Proof.
  intros regs0 regs m1 m X1 HDI HRG HK HL1 Hl1 Hl3 HSH.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  destruct (shash_ok_lo _ _ X1 HSH Hl3) as (HTI & Hlk & HLM & HSD). clear HSH.
  rewrite (st_srest_lo X1 Hl3).
  pose proof HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
  rewrite Ews in *.
  destruct (nil_blk regs m HRG) as (R1 & Hms1 & HRG1 & A11 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  destruct (from_setup regs0 R1 m1 m X1 0 HDI HRG1 A11 HK1 HL1 ltac:(lia) ltac:(lia) Tml Tms Tlazy Tstrat HLM HSD) as (R & M & A & B & C).
  exists R, M. split; [exact A|]. split; [exact B|]. exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
Qed.


Lemma trip : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 ->
  strip_ok X flush -> strip_oku X ->
  exists R M, DI m1 M (fst (st_sbody X flush)) /\ KEEP regs0 R /\ EXITS regs (0x19da8 : word) m R M (st_sbody X flush)
    /\ (ds_lookahead X < MIN_LOOKAHEAD -> BSI (fill_window X)).
Proof.
  intros regs0 regs m1 m X HDI HRG HK HL1 (Hlk0 & Hfw & Hlk1 & HSH) HBSI.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl.
  unfold st_sbody in *.
  destruct (head_blk regs m1 m X HDI HRG Hlk0) as (R1 & Hms1 & HRG1 & HLO & HHI & A2 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  unfold head_pc in Hms1.
  destruct (Z.ltb_spec (ds_lookahead X) 262) as [Hlo|Hhi].
  -
    rewrite (st_fill_lo X flush Hlo) in Hlk1, HSH |- *. cbn [fst snd] in Hlk1, HSH |- *.
    destruct (HLO Hlo) as [B10 B1]. destruct (Hfw ltac:(rewrite MIN_LOOKAHEAD_eq; lia)) as [Hfwf Hwrap].
    pose proof (HBSI ltac:(rewrite MIN_LOOKAHEAD_eq; lia)) as HBS.
    destruct (call_fw R1 m1 m X (0x19db8%bv : word) HDI ltac:(retok) HBS Hfwf ltac:(rewrite MIN_LOOKAHEAD_eq; lia) Hwrap B1 A2 B10)
      as (R2 & M2 & Hms2 & HDI2 & _ & HBS2 & C2 & _ & Hfr2).
    assert (HK2 : KEEP regs0 R2). { destruct HK1 as [K3 K4]. split; [rewrite (Hfr2 3%bv eq_refl); exact K3 | rewrite (Hfr2 4%bv eq_refl); exact K4]. }
    assert (HRG2 : HREGS R2) by (exact (HREGS_fw R1 R2 HRG1 C2 Hfr2)).
    revert Hlk1 HSH HDI2 HBS2. generalize (fill_window X). intros X1 Hlk1 HSH HDI2 HBS2.
    destruct (fillr_blk R2 m1 M2 X1 HDI2 HRG2 Hlk1) as (R3 & Hms3 & HRG3 & Q10 & Hfr3).
    assert (HK3 : KEEP regs0 R3) by (keep_via HK2 Hfr3).
    unfold fillr_pc in Hms3. unfold fill_out.
    assert (HSH' : ((ds_lookahead X1 <? 262) && (flush =? 0))%bool = false -> ds_lookahead X1 <> 0 -> shash_ok X1).
    { intros Ea Eb. apply HSH. unfold fill_out. rewrite Ea. replace (ds_lookahead X1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Eb). reflexivity. }
    assert (Hms13 : forall pc, msteps s6u_segs (mkst R2 (0x19db8 : word) M2 s6u_rom) (mkst R3 pc M2 s6u_rom) ->
                    msteps s6u_segs (mkst regs (0x19da8 : word) m s6u_rom) (mkst R3 pc M2 s6u_rom)).
    { intros pc H. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact H]. }
    destruct ((ds_lookahead X1 <? 262) && (flush =? 0))%bool eqn:Enm.
    +
      cbn [fst snd].
      destruct HRG3 as (_ & W2 & _).
      destruct (ret0_blk R3 M2 W2) as (R4 & Hms4 & Z10 & Z2 & Hfr4).
      exists R4, M2. split; [exact HDI2|]. split; [keep_via HK3 Hfr4|].
      split; [| intros _; exact HBS2].
      unfold EXITS. cbn [fst snd bs_code]. split; [exact Z10|]. split; [exact Z2|].
      eapply msteps_trans; [apply Hms13; exact Hms3 | exact Hms4].
    + destruct (Z.eqb_spec (ds_lookahead X1) 0) as [Hl0|Hl0].
      *
        cbn [fst snd]. exists R3, M2. split; [exact HDI2|]. split; [exact HK3|]. split; [| intros _; exact HBS2].
        unfold EXITS. cbn [fst snd]. split; [exact HRG3 | apply Hms13; exact Hms3].
      * cbn [fst snd].
        destruct (Z.ltb_spec (ds_lookahead X1) 3) as [Hl3|Hl3].
        --
           destruct (from_nil regs0 R3 m1 M2 X1 HDI2 HRG3 HK3 HL1 ltac:(lia) Hl3 (HSH' eq_refl Hl0)) as (R' & M & A & B & C).
           exists R', M. split; [exact A|]. split; [exact B|]. split; [| intros _; exact HBS2].
           exact (EXITS_pre _ _ _ _ _ _ _ _ _ ltac:(apply Hms13; exact Hms3) C).
        --
           destruct (from_ins regs0 R3 m1 M2 X1 HDI2 HRG3 HK3 HL1 ltac:(lia) (HSH' eq_refl Hl0)) as (R' & M & A & B & C).
           exists R', M. split; [exact A|]. split; [exact B|]. split; [| intros _; exact HBS2].
           exact (EXITS_pre _ _ _ _ _ _ _ _ _ ltac:(apply Hms13; exact Hms3) C).
  -
    rewrite (st_fill_hi X flush Hhi) in Hlk1, HSH |- *. cbn [fst snd] in Hlk1, HSH |- *.
    pose proof (HSH eq_refl) as HSHa.
    destruct (from_ins regs0 R1 m1 m X HDI HRG1 HK1 HL1 ltac:(lia) HSHa) as (R' & M & A & B & C).
    exists R', M. split; [exact A|]. split; [exact B|]. split; [| intros Hc; rewrite MIN_LOOKAHEAD_eq in Hc; exfalso; lia].
    exact (EXITS_pre _ _ _ _ _ _ _ _ _ Hms1 C).
Qed.



Local Abbreviation sloop_ok := (DeflSlow6_M.sloop_ok FBSAFE ws hs).
Local Abbreviation stail_ok := (DeflSlow6_M.stail_ok FBSAFE ws).
Local Abbreviation break1_st := DeflSlow6_7.break1_st.
Local Abbreviation break2_st := DeflSlow6_7.break2_st.


Definition LEXIT (regs : bvmap 5 word) (pc : word) (m : word -> option byte)
           (R : bvmap 5 word) (M : word -> option byte) (r : deflate_state * option block_state) : Prop :=
  match snd r with
  | None => HREGS R /\ ds_wrap (fst r) = 1 /\ msteps s6u_segs (mkst regs pc m s6u_rom) (mkst R (0x1a3c4 : word) M s6u_rom)
  | Some bs => getr R 10 = zw (bs_code bs) /\ getr R 2 = zw SP
               /\ msteps s6u_segs (mkst regs pc m s6u_rom) (mkst R (0x1a608 : word) M s6u_rom)
  end.

Lemma loop_run : forall n regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 -> sloop_ok n X flush -> sloop_oku n X flush ->
  exists R M, DI m1 M (fst (deflate_slow_loop n X flush)) /\ KEEP regs0 R
    /\ LEXIT regs (0x19da8 : word) m R M (deflate_slow_loop n X flush).
Proof.
  induction n as [|n IH]; intros regs0 regs m1 m X HDI HRG HK HL1 HLO HLU; [destruct HLO|].
  rewrite sloop_ok_S in HLO. destruct HLO as [HTO HLO]. rewrite sloop_oku_S in HLU. destruct HLU as [HTU HLU]. rewrite sloop_step'.
  destruct (trip regs0 regs m1 m X HDI HRG HK HL1 HTO HTU) as (R1 & M1 & HDI1 & HK1 & HX1 & _).
  (* 1.4: a break leaves wrap = 1 (DeflSlow6_11.brk_wrap, the plain lemma, from strip_ok) *)
  assert (Hbw : snd (st_sbody X flush) = LBreak -> ds_wrap (fst (st_sbody X flush)) = 1)
    by (intros Hb; eapply DeflSlow6_11.brk_wrap; [exact HTO | exact Hb]).
  unfold EXITS in HX1. revert HLO HLU HDI1 HX1 Hbw. generalize (fst (st_sbody X flush)). intros X' HLO HLU HDI1 HX1 Hbw.
  destruct (snd (st_sbody X flush)) as [| |bs].
  - destruct HX1 as (HRG1 & Hms1).
    destruct (IH regs0 R1 m1 M1 X' HDI1 HRG1 HK1 HL1 HLO HLU) as (R & M & HDI' & HK' & HX').
    exists R, M. split; [exact HDI'|]. split; [exact HK'|].
    unfold LEXIT in *. destruct (snd (deflate_slow_loop n X' flush)) as [bs|].
    + destruct HX' as (A & B & C). split; [exact A|]. split; [exact B|]. eapply msteps_trans; [exact Hms1 | exact C].
    + destruct HX' as (A & W & C). split; [exact A|]. split; [exact W|]. eapply msteps_trans; [exact Hms1 | exact C].
  - exists R1, M1. split; [exact HDI1|]. split; [exact HK1|]. unfold LEXIT. cbn [fst snd].
    split; [exact (proj1 HX1)|]. split; [exact (Hbw eq_refl) | exact (proj2 HX1)].
  - exists R1, M1. split; [exact HDI1|]. split; [exact HK1|]. exact HX1.
Qed.


Lemma deflate_tail_fin : forall s fl, fl = Z_FINISH ->
  deflate_tail s fl = (fst (flush_block s 1), match snd (flush_block s 1) with Some bs => bs | None => finish_done end).
Proof.
  intros s fl ->. unfold deflate_tail. cbn [Z.eqb Z_FINISH Pos.eqb].
  destruct (flush_block s 1) as [s' [bs|]]; reflexivity.
Qed.

Lemma deflate_tail_none : forall s fl, fl <> Z_FINISH -> ds_sym_next s = 0 ->
  deflate_tail s fl = (s, block_done).
Proof.
  intros s fl Hf Hs. unfold deflate_tail. destruct (Z.eqb_spec fl Z_FINISH); [lia|].
  rewrite Hs. reflexivity.
Qed.

Lemma deflate_tail_fbt : forall s fl, fl <> Z_FINISH -> ds_sym_next s <> 0 ->
  deflate_tail s fl = (fst (flush_block s 0), match snd (flush_block s 0) with Some bs => bs | None => block_done end).
Proof.
  intros s fl Hf Hs. unfold deflate_tail. destruct (Z.eqb_spec fl Z_FINISH); [lia|].
  destruct (Z.eqb_spec (ds_sym_next s) 0); [lia|]. cbn [negb].
  destruct (flush_block s 0) as [s' [bs|]]; reflexivity.
Qed.

Lemma break1_bs : forall X, ds_block_start (break1_st X) = ds_block_start X.
Proof. intros X. destruct X; reflexivity. Qed.

Lemma tail_break1 : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> strip_inv X -> ds_w_size X = ws -> ds_lit_bufsize X = lbs ->
  (ds_match_available X <> 0 -> 1 <= ds_strstart X) ->
  exists R1 M1, msteps s6u_segs (mkst regs (0x1a3c4 : word) m s6u_rom) (mkst R1 (0x1a4ac : word) M1 s6u_rom)
    /\ DI m1 M1 (if negb (ds_match_available X =? 0) then break1_st X else X) /\ HREGS R1 /\ KEEP regs0 R1.
Proof.
  intros regs0 regs m1 m X HDI HRG HK HTI Ews Elbs Hma1.
  pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  destruct HTI as [Tstr Tsl Tlook Tih Thm Twm Ths Tml Tms Tpl Tpm Tma Tstrat Tlazy Tsn Tse Twb Thb Tpb Tlh Tlfc Tdfc].
  rewrite Ews in Tsl, Twb, Tpb. rewrite Elbs in Tsn.
  destruct (Z.eqb_spec (ds_match_available X) 0) as [Hz|Hnz]; cbn [negb].
  - destruct (break1a_blk regs m1 m X HDI HRG Hz) as (R1 & Hms1 & HRG1 & Hfr1).
    exists R1, m. split; [exact Hms1|]. split; [exact HDI|]. split; [exact HRG1 | keep_via HK Hfr1].
  - destruct (break1b_blk regs m1 m X HDI HRG ltac:(lia) ltac:(pose proof (Hma1 Hnz); lia) ltac:(lia) ltac:(lia) Twb Tlfc)
      as (R1 & M1 & Hms1 & HDI1 & HRG1 & Hfr1).
    exists R1, M1. split; [exact Hms1|]. split; [exact HDI1|]. split; [exact HRG1 | keep_via HK Hfr1].
Qed.

Lemma code_fin : forall (R : bvmap 5 word) (o : option block_state),
  getr R 10 = zw (match o with Some bs => bs_code bs | None => 3 end) ->
  getr R 10 = zw (bs_code (match o with Some bs => bs | None => finish_done end)).
Proof. intros R [bs|] H; exact H. Qed.
Lemma code_blk : forall (R : bvmap 5 word) (o : option block_state),
  getr R 10 = zw (match o with Some bs => bs_code bs | None => 1 end) ->
  getr R 10 = zw (bs_code (match o with Some bs => bs | None => block_done end)).
Proof. intros R [bs|] H; exact H. Qed.

Lemma tail_fin4 : forall regs0 R3 M3 m1 XB,
  DI m1 M3 XB -> HREGS R3 -> KEEP regs0 R3 -> flush = 4 ->
  getr R3 10 = zw S -> getr R3 11 = zw (fb_bufp XB) -> getr R3 12 = zw (fb_len XB) -> getr R3 13 = zw 1 ->
  getr R3 1 = (0x1a574%bv : word) -> ds_wrap XB = 1 -> flush_ok XB 1 ->
  exists R M, DI m1 M (fst (deflate_tail XB flush)) /\ KEEP regs0 R
    /\ msteps s6u_segs (mkst R3 (0x1bff0 : word) M3 s6u_rom) (mkst R (0x1a608 : word) M s6u_rom)
    /\ getr R 10 = zw (bs_code (snd (deflate_tail XB flush))) /\ getr R 2 = zw SP.
Proof.
  intros regs0 R3 M3 m1 XB HDI3 HRG3 HK3 F4 A10 A11 A12 A13 A1 HWR HFIN.
  rewrite (deflate_tail_fin XB flush F4).
  destruct (from_fbt regs0 R3 m1 M3 XB HDI3 HRG3 HK3 A10 A11 A12 A13 A1 ltac:(lia) HFIN)
    as (R & M & HDI' & HK' & Hms' & B10 & B2).
  revert HDI' B10. generalize (flush_block XB 1). intros [X9 o] HDI' B10. cbn [fst snd] in HDI', B10 |- *.
  exists R, M. split; [exact HDI'|]. split; [exact HK'|]. split; [exact Hms'|]. split; [| exact B2].
  exact (code_fin _ _ B10).
Qed.

Lemma tail_nf : forall regs0 R3 M3 m1 XB,
  DI m1 M3 XB -> HREGS R3 -> KEEP regs0 R3 -> LOC m1 -> flush <> 4 ->
  getr R3 10 = zw (ds_strstart XB) ->
  0 <= ds_strstart XB < 2 ^ 31 -> - 2 ^ 62 <= ds_block_start XB < 2 ^ 62 -> 0 <= ds_sym_next XB < 2 ^ 31 ->
  (ds_sym_next XB <> 0 -> flush_ok XB 0) ->
  exists R M, DI m1 M (fst (deflate_tail XB flush)) /\ KEEP regs0 R
    /\ msteps s6u_segs (mkst R3 (0x1a50c : word) M3 s6u_rom) (mkst R (0x1a608 : word) M s6u_rom)
    /\ getr R 10 = zw (bs_code (snd (deflate_tail XB flush))) /\ getr R 2 = zw SP.
Proof.
  intros regs0 R3 M3 m1 XB HDI3 HRG3 HK3 HL1 F4 Q10 Hstr2 Hbs2 Hsn2 HFBT.
  pose proof (LOC_keep _ _ _ HL1 HDI3) as HLM3.
  destruct (fina_blk R3 m1 M3 XB HDI3 HRG3 HLM3 Q10 Hstr2 Hbs2 Hsn2) as (R4 & Hms4 & HRG4 & Hargs & Hfr4).
  assert (HK4 : KEEP regs0 R4) by (keep_via HK3 Hfr4).
  unfold fina_pc, DeflSlow6u_6.fina_pc in Hms4.
  revert Hms4. destruct (Z.eqb_spec (ds_sym_next XB) 0) as [N0|N0]; intros Hms4.
  - rewrite (deflate_tail_none XB flush F4 N0). cbn [fst snd bs_code].
    destruct (b84_blk R4 M3 HRG4) as (R5 & Hms5 & HRG5 & Z1 & Hfr5).
    exists R5, M3. split; [exact HDI3|]. split; [keep_via HK4 Hfr5|].
    split; [eapply msteps_trans; [exact Hms4 | exact Hms5]|].
    split; [exact Z1 | destruct HRG5 as (_ & W2 & _); exact W2].
  - rewrite (deflate_tail_fbt XB flush F4 N0).
    destruct (Hargs N0) as (A10 & A11 & A12 & A13 & A1).
    destruct (from_fin regs0 R4 m1 M3 XB HDI3 HRG4 HK4 A10 A11 A12 A13 A1 (HFBT N0))
      as (R & M & HDI' & HK' & Hms' & B10 & B2).
    revert HDI' B10. generalize (flush_block XB 0). intros [X9 o] HDI' B10. cbn [fst snd] in HDI', B10 |- *.
    exists R, M. split; [exact HDI'|]. split; [exact HK'|].
    split; [eapply msteps_trans; [exact Hms4 | exact Hms']|]. split; [| exact B2].
    exact (code_blk _ _ B10).
Qed.

Lemma tail_disp : forall regs0 regs R3 m M3 m1 XB,
  DI m1 M3 XB -> HREGS R3 -> KEEP regs0 R3 -> LOC m1 ->
  (flush = 4 -> getr R3 10 = zw S /\ getr R3 11 = zw (fb_bufp XB) /\ getr R3 12 = zw (fb_len XB) /\ getr R3 13 = zw 1
               /\ getr R3 1 = (0x1a574%bv : word)) ->
  (flush <> 4 -> getr R3 10 = zw (ds_strstart XB)) ->
  0 <= ds_strstart XB < 2 ^ 31 -> - 2 ^ 62 <= ds_block_start XB < 2 ^ 62 -> 0 <= ds_sym_next XB < 2 ^ 31 ->
  (flush = 4 -> flush_ok XB 1) -> (flush <> 4 -> ds_sym_next XB <> 0 -> flush_ok XB 0) -> ds_wrap XB = 1 ->
  msteps s6u_segs (mkst regs (0x1a3c4 : word) m s6u_rom) (mkst R3 (DeflSlow6u_6.break2_pc flush) M3 s6u_rom) ->
  exists R M, DI m1 M (fst (deflate_tail XB flush)) /\ KEEP regs0 R
    /\ msteps s6u_segs (mkst regs (0x1a3c4 : word) m s6u_rom) (mkst R (0x1a608 : word) M s6u_rom)
    /\ getr R 10 = zw (bs_code (snd (deflate_tail XB flush))) /\ getr R 2 = zw SP.
Proof.
  intros regs0 regs R3 m M3 m1 XB HDI3 HRG3 HK3 HL1 Hfin Hnf Hstr2 Hbs2 Hsn2 HFIN HFBT HWR Hms3.
  unfold DeflSlow6u_6.break2_pc in Hms3.
  revert Hms3. destruct (Z.eqb_spec flush 4) as [F4|F4]; intros Hms3.
  - destruct (Hfin F4) as (A10 & A11 & A12 & A13 & A1).
    destruct (tail_fin4 regs0 R3 M3 m1 XB HDI3 HRG3 HK3 F4 A10 A11 A12 A13 A1 HWR (HFIN F4)) as (R & M & A & B & C & D & E).
    exists R, M. split; [exact A|]. split; [exact B|]. split; [eapply msteps_trans; [exact Hms3 | exact C]|]. split; [exact D | exact E].
  - destruct (tail_nf regs0 R3 M3 m1 XB HDI3 HRG3 HK3 HL1 F4 (Hnf F4) Hstr2 Hbs2 Hsn2 (HFBT F4)) as (R & M & A & B & C & D & E).
    exists R, M. split; [exact A|]. split; [exact B|]. split; [eapply msteps_trans; [exact Hms3 | exact C]|]. split; [exact D | exact E].
Qed.

Lemma tail_run : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 -> stail_ok X flush -> - 2 ^ 62 <= ds_block_start X < 2 ^ 62 ->
  ds_wrap X = 1 ->
  let X2 := if negb (ds_match_available X =? 0) then break1_st X else X in
  exists R M, DI m1 M (fst (deflate_tail (tail_st X2) flush)) /\ KEEP regs0 R
    /\ msteps s6u_segs (mkst regs (0x1a3c4 : word) m s6u_rom) (mkst R (0x1a608 : word) M s6u_rom)
    /\ getr R 10 = zw (bs_code (snd (deflate_tail (tail_st X2) flush))) /\ getr R 2 = zw SP.
Proof.
  intros regs0 regs m1 m X HDI HRG HK HL1 (HTI & Hstr & Hma1 & HT2) HbsU HWX.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs).
  cbv zeta.
  destruct (tail_break1 regs0 regs m1 m X HDI HRG HK HTI Ews Elbs Hma1) as (R1 & M1 & Hms1 & HDI1 & HRG1 & HK1).
  assert (HbsU2 : - 2 ^ 62 <= ds_block_start (if negb (ds_match_available X =? 0) then break1_st X else X) < 2 ^ 62).
  { destruct (negb (ds_match_available X =? 0)); [rewrite break1_bs|]; exact HbsU. }
  (* 1.4: wrap survives break1 (DeflSlow6_11.wrap_break1, the plain lemma) *)
  assert (HW2 : ds_wrap (if negb (ds_match_available X =? 0) then break1_st X else X) = 1).
  { destruct (negb (ds_match_available X =? 0)); [rewrite DeflSlow6_11.wrap_break1|]; exact HWX. }
  revert HDI1 HT2 HbsU2 HW2. generalize (if negb (ds_match_available X =? 0) then break1_st X else X). intros X2 HDI1 (Hstr2 & Hbs2 & Hsn2 & HFIN & HFBT) HbsU2 HW2.
  assert (HWT : ds_wrap (tail_st X2) = 1) by (rewrite <- HW2; destruct X2; reflexivity).
  pose proof (LOC_keep _ _ _ HL1 HDI1) as HLM1.
  destruct (break2_blk R1 m1 M1 X2 HDI1 HRG1 HLM1 Hstr2 HbsU2) as (R3 & M3 & Hms3 & HDI3 & HRG3 & Hfin & Hnf & Hfr3).
  assert (HK3 : KEEP regs0 R3) by (keep_via HK1 Hfr3).
  rewrite break2_tail in HDI3.
  assert (Vs : ds_strstart (tail_st X2) = ds_strstart X2) by reflexivity.
  assert (Vn : ds_sym_next (tail_st X2) = ds_sym_next X2) by reflexivity.
  assert (Vb : ds_block_start (tail_st X2) = ds_block_start X2) by reflexivity.
  assert (Vbufp : fb_bufp (tail_st X2) = fb_bufp X2) by reflexivity.
  assert (Vlen : fb_len (tail_st X2) = fb_len X2) by reflexivity.
  rewrite <- Vbufp, <- Vlen in Hfin. rewrite <- Vs in Hnf.
  rewrite <- Vs in Hstr2. rewrite <- Vn in Hsn2, HFBT. rewrite <- Vb in HbsU2.
  unfold Z_FINISH in HFIN, HFBT.
  exact (tail_disp regs0 regs R3 m M3 m1 (tail_st X2) HDI3 HRG3 HK3 HL1 Hfin Hnf Hstr2 HbsU2 Hsn2 HFIN HFBT HWT
           ltac:(eapply msteps_trans; [exact Hms1 | exact Hms3])).
Qed.


Lemma DI_fin : forall m1 m X, DI m1 m X -> agree_out [(sp - 128, 128)] mem m1 ->
  ZR6u m S p zp X /\ agree_out (ZRFo DSLOW_FRAME6u S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm X))))) mem m /\ rod6u m /\ ROM m
  /\ (forall x, mem x <> None -> m x <> None)
  /\ lzk ds X.
Proof.
  intros m1 m X (HB & HR & HS3) Hag1.
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  assert (HagO : agree_out (ZRFo DSLOW_FRAME6u S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm X))))) mem m).
  { eapply agree_out_trans.
    - eapply agree_out_weaken; [exact Hag1|]. unfold ZRFo, DSLOW_FRAME6u. cbn [in_franges]. intros x Hx. lia.
    - eapply agree_out_weaken; [exact HAG|]. unfold DeflKit6u.GDo, ZRFo, DSLOW_FRAME6u, DSLOW_FR6u, ds6_SIZE, zsl_SIZE. cbn [in_franges]. intros x Hx. lia. }
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
  (forall r : reg, reg_in r [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = true -> getr R4 r = getr regs r) ->
  (forall r : reg, reg_in r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = false -> getr R4 r = getr R3 r) ->
  KEEP regs R3 ->
  forall r : reg, reg_in r LZ_CLOB = false -> getr R4 r = getr regs r.
Proof.
  intros R4 R3 regs H2 Hrest Hfr [K3 K4] r Hr.
  pose proof (u5_range r) as Ur.
  destruct (reg_in r [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv) eqn:E1; [exact (Hrest r E1)|].
  destruct (bv_eqb r 2) eqn:E2.
  { assert (Er : r = 2%bv) by (apply bv_eq; unfold bv_eqb in E2; apply Z.eqb_eq in E2; exact E2). subst r. exact H2. }
  assert (E3 : reg_in r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = false).
  { cbn [reg_in] in E1 |- *. rewrite E2. rewrite Bool.orb_false_l. exact E1. }
  rewrite (Hfr r E3).
  destruct (bv_eqb r 0) eqn:E0.
  { assert (Er : r = 0%bv) by (apply bv_eq; unfold bv_eqb in E0; apply Z.eqb_eq in E0; exact E0). subst r. reflexivity. }
  destruct (bv_eqb r 3) eqn:E3'.
  { assert (Er : r = 3%bv) by (apply bv_eq; unfold bv_eqb in E3'; apply Z.eqb_eq in E3'; exact E3'). subst r. exact K3. }
  destruct (bv_eqb r 4) eqn:E4'.
  { assert (Er : r = 4%bv) by (apply bv_eq; unfold bv_eqb in E4'; apply Z.eqb_eq in E4'; exact E4'). subst r. exact K4. }
  exfalso. unfold LZ_CLOB in Hr. cbn [reg_in] in Hr, E1, E3. unfold bv_eqb in *.
  bvlits. lia.
Qed.


Theorem deflate_slow_run : forall regs,
  slow_safe6u FBSAFE ds flush ->
  getr regs 10 = zw S -> getr regs 11 = zw flush -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m',
    msteps s6u_segs (mkst regs (0x19cf0 : word) mem s6u_rom) (mkst R ra m' s6u_rom)
    /\ ZR6u m' S p zp (fst (deflate_slow ds flush))
    /\ getr R 10 = zw (bs_code (snd (deflate_slow ds flush)))
    /\ getr R 2 = zw sp
    /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R r = getr regs r)
    /\ agree_out (ZRFo DSLOW_FRAME6u S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm (fst (deflate_slow ds flush))))))) mem m'
    /\ rod6u m'
    /\ ROM m'
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ lzk ds (fst (deflate_slow ds flush)).
Proof.
  intros regs ((HLO & HTL) & HLU & HTU) P10 P11 P2 P1.
  pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  rewrite deflate_slow_eq.
  revert HLO HTL HLU HTU. generalize (lz_fuel ds). intros n HLO HTL HLU HTU.
  destruct (pro_blk regs P10 P11 P2 P1) as (R0 & M0 & Hms0 & HDI0 & HFRM & HL0 & HRG0 & Hfr0 & Hag0).
  assert (HK0 : KEEP regs R0).
  { unfold KEEP. rewrite (Hfr0 3%bv eq_refl), (Hfr0 4%bv eq_refl). split; reflexivity. }
  destruct (loop_run n regs R0 M0 M0 ds HDI0 HRG0 HK0 HL0 HLO HLU) as (R3 & M3 & HDI3 & HK3 & HX3).
  unfold LEXIT in HX3.
  revert HTL HTU HDI3 HX3. generalize (fst (deflate_slow_loop n ds flush)). intros XL HTL HTU HDI3 HX3.
  assert (FIN : forall R M X (code : Z),
            DI M0 M X -> KEEP regs R -> getr R 10 = zw code -> getr R 2 = zw SP ->
            msteps s6u_segs (mkst regs (0x19cf0 : word) mem s6u_rom) (mkst R (0x1a608 : word) M s6u_rom) ->
            exists R' m',
              msteps s6u_segs (mkst regs (0x19cf0 : word) mem s6u_rom) (mkst R' ra m' s6u_rom)
              /\ ZR6u m' S p zp X /\ getr R' 10 = zw code /\ getr R' 2 = zw sp
              /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R' r = getr regs r)
              /\ agree_out (ZRFo DSLOW_FRAME6u S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm X))))) mem m' /\ rod6u m' /\ ROM m'
              /\ (forall x, mem x <> None -> m' x <> None)
              /\ lzk ds X).
  { intros R M X code HDI HK A10 A2 Hms.
    destruct (epi_blk R regs M0 M X HDI (FRM_keep M0 M X regs HDI HFRM) P1 A2)
      as (R9 & Hms9 & B2 & B10 & Hrest & Hfr9).
    destruct (DI_fin M0 M X HDI Hag0) as (HZ & Hag & Hrc & Hrd & Hgr & Hk).
    exists R9, M. split; [eapply msteps_trans; [exact Hms | exact Hms9]|].
    split; [exact HZ|]. split; [rewrite B10; exact A10|]. split; [exact B2|].
    split; [apply (reg_frame_fin R9 R regs); [rewrite B2, P2; reflexivity | exact Hrest | exact Hfr9 | exact HK]|].
    split; [exact Hag|]. split; [exact Hrc|]. split; [exact Hrd|]. split; [exact Hgr | exact Hk]. }
  destruct (snd (deflate_slow_loop n ds flush)) as [bs|].
  - destruct HX3 as (A10 & A2 & Hms3). cbn [fst snd].
    exact (FIN R3 M3 XL (bs_code bs) HDI3 HK3 A10 A2 ltac:(eapply msteps_trans; [exact Hms0 | exact Hms3])).
  - destruct HX3 as (HRG3 & HW3 & Hms3). cbv zeta.
    destruct (tail_run regs R3 M0 M3 XL HDI3 HRG3 HK3 HL0 HTL HTU HW3) as (R4 & M4 & HDI4 & HK4 & Hms4 & A10 & A2).
    exact (FIN R4 M4 _ _ HDI4 HK4 A10 A2 ltac:(eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms3 | exact Hms4])).
Qed.

End Walk.


Theorem deflate_slow_run6u_ok :
  forall (ROM : (word -> option byte) -> Prop) (FBSAFE : deflate_state -> option Z -> Z -> Z -> Prop),
    memcpy_run6u -> memset_run6u -> adler32_run6u ROM -> tr_flush_bits_run6u -> tr_flush_block_run6u FBSAFE ->
    rom_local6u ROM ->
    deflate_slow_run6u ROM (fun ds flush => DWF ds /\ slow_safe6u FBSAFE ds flush).
Proof.
  intros ROM FBSAFE MEMCPY MEMSET ADLER TFBITS TFB HRL.
  unfold deflate_slow_run6u, lz_contract6u.
  intros mem S p zp ds flush ra sp regs HL Hret HZR HROM [HWF HSAFE] Hfl P10 P11 P2 P1.
  assert (HKK : 0 <= DSLOW_FR6u <= DSLOW_FRAME6u) by (unfold DSLOW_FRAME6u, DSLOW_FR6u; lia).
  destruct (deflate_slow_run ROM mem S p zp ds flush ra sp
              {| dsh_L := HL; dsh_ret := Hret; dsh_zr := HZR; dsh_flush := Hfl; dsh_wf := HWF; dsh_rom := HROM; dsh_roml := HRL;
                 dsh_K := HKK |}
              MEMCPY MEMSET ADLER TFBITS FBSAFE TFB
              regs HSAFE P10 P11 P2 P1)
    as (R & m' & Hms & HZ & A10 & A2 & Hfr & Hag & Hrc & Hrd & Hgr & Hk).
  exists R, m'. unfold A6U_DEFLATE_SLOW. replace (zw 0x19cf0) with (0x19cf0%bv : word) by (apply bv_eq; reflexivity).
  split; [exact Hms|]. split; [exact HZ|]. split; [exact A10|]. split; [exact A2|]. split; [exact Hfr|].
  split; [exact Hag|]. split; [exact Hrc|]. split; [exact Hrd|]. split; [exact Hgr | exact Hk].
Qed.
End FXG.

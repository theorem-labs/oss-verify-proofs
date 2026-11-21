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
  Lmatch6u_run FillWin6uA FillWin6uD DeflBlkApi6u DeflKit6u DeflSlow6u_1 DeflSlow6u_2 DeflSlow6u_3 DeflSlow6u_4 DeflSlow6u_5 DeflSlow6u_6 DeflSlow6u_7.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma arrays_agree_out6u : forall F m m' S s,
  dsl_arrays s6u_segs m S s -> agree_out F m m' ->
  (forall x, in_franges F x -> ~ (S + 212 <= x < S + 5881)) ->
  0 <= S -> S + 5968 <= 2 ^ 64 ->
  dsl_arrays s6u_segs m' S s.
Proof.
  intros F m m' S s H Hag HF HS0 HS1.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). unfold dsl_arrays.
  repeat split;
    first [ eapply cells_agree_out; [exact Hag | intros x Hx Hin; apply (HF x Hin); lia | cbn; lia | lia | lia | eassumption]
          |
            intros j Hj; eapply cell_agree_out; [exact Hag | intros x Hx Hin; apply (HF x Hin); cbn in Hx; lia | lia | cbn; lia | apply A6; exact Hj] ].
Qed.

End FXG.
Ltac lia_min :=
  first [ solve [ repeat match goal with H : _ \/ _ |- _ => clear H end; lia ]
        | match goal with D : _ \/ _ |- _ =>
            solve [ repeat match goal with H : _ \/ _ |- _ => tryif constr_eq H D then fail else clear H end; lia ] end
        | lia ].
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

Let GDI : forall x, in_franges GD x -> IMG6U_LO <= x < IMG6U_HI -> False := GD_img _ _ _ _ _ _ _ _ _ _ _ HH.
Let GDoI : forall st x, in_franges (GDo st) x -> Z.of_nat (length (cs_out_rev st)) <= OLEN0 + AV0 -> IMG6U_LO <= x < IMG6U_HI -> False
  := GDo_img _ _ _ _ _ _ _ _ _ _ _ HH.

Local Ltac mappedF i H :=
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH i ltac:(lia)) as H; unfold ZRF in H; cbn [nth fst snd] in H; unfold ds6_SIZE, dsl_SIZE, zsl_SIZE, DSLOW_FRAME6u, DSLOW_FR6u in H.
Local Abbreviation Fd := (DeflKit6u.Fd S p zp ds sp DSLOW_FRAME6u).
Local Abbreviation RZ_agree := (DeflKit6u.RZ_agree ROM mem S p zp ds flush ra sp DSLOW_FRAME6u DSLOW_FR6u HH).
Local Abbreviation in_GDo := (DeflKit6u.in_GDo S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).
Local Abbreviation in_Fd := (DeflKit6u.in_Fd S p zp ds sp DSLOW_FRAME6u).
Local Abbreviation in_GD := (DeflKit6u.in_GD S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).

Lemma UBT_ds : UBT S p.
Proof.
  constructor; [exact (zrh_S8 _ _ _ _ _ _ _ HL) | exact (zrh_S1 _ _ _ _ _ _ _ HL) | exact (zrh_PB1 _ _ _ _ _ _ _ HL)
              | exact (zrh_W _ _ _ _ _ _ _ HL) | exact (zrh_strm1 _ _ _ _ _ _ _ HL) | exact (zrh_strm8 _ _ _ _ _ _ _ HL)].
Qed.

Lemma UBP_ds : ub_pre S p zp.
Proof.
  constructor; [exact (zrh_S8 _ _ _ _ _ _ _ HL) | exact (zrh_S1 _ _ _ _ _ _ _ HL) | exact (zrh_strm1 _ _ _ _ _ _ _ HL)
              | exact (zrh_strm8 _ _ _ _ _ _ _ HL) | exact (zrh_HD2 _ _ _ _ _ _ _ HL) | exact (zrh_PV2 _ _ _ _ _ _ _ HL) | exact (zrh_I _ _ _ _ _ _ _ HL)].
Qed.


Lemma call_lm : forall regs m1 m X cur (ra' : word),
  DI m1 m X -> ret_ok ra' ->
  (forall i, 0 <= i < 2 * ws -> 0 <= arr_get (ds_window X) i < 256) ->
  (forall i, 0 <= i < ws -> 0 <= arr_get (ds_prev X) i < 65536) ->
  0 <= ds_strstart X -> ds_strstart X + 258 < 2 * ws ->
  ds_w_mask X = ws - 1 -> 1 <= ds_prev_length X <= 258 -> 0 <= ds_nice_match X <= 258 ->
  0 <= ds_lookahead X < 2 ^ 31 -> 0 <= ds_good_match X < 2 ^ 31 -> 0 <= ds_max_chain_length X < 2 ^ 31 ->
  1 <= (if ds_good_match X <=? ds_prev_length X then Z.shiftr (ds_max_chain_length X) 2 else ds_max_chain_length X) ->
  0 <= cur < 2 ^ 31 -> Forall (fun c => 0 <= c < ds_strstart X) (lm_visited X cur) ->
  getr regs 1 = ra' -> getr regs 2 = zw SP -> getr regs 10 = zw S -> getr regs 11 = zw cur ->
  exists R m' ms,
    msteps s6u_segs (mkst regs (0x1a648 : word) m s6u_rom) (mkst R ra' m' s6u_rom)
    /\ fst (longest_match X cur) = set_match_start X ms
    /\ DI m1 m' (set_match_start X ms)
    /\ getr R 10 = zw (snd (longest_match X cur)) /\ getr R 2 = zw SP
    /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18
    /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22
    /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27
    /\ (forall r : reg, reg_in r lmatch_clob = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X cur ra' HDI Hret Hwb Hpb Hs0 Hs258 Hwm Hpl Hnice Hlook Hgood Hchain Hch1 Hcur Hvis P1 P2 P10 P11.
  pose proof HDI as (HB & HR & (Ews & Ehs & Elbs)).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HB as (_ & _ & _ & _ & Epbl & _). unfold dsl_pendA in Hpend. rewrite Epbl in Hpend.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN). unfold DSLOW_FRAME6u, DSLOW_FR6u in Hsp, MF.
  pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  apartF 0%nat 1%nat A01. apartF 0%nat 2%nat A02. apartF 0%nat 3%nat A03. apartF 1%nat 2%nat A12. apartF 1%nat 3%nat A13.
  destruct (longest_match_ms X cur) as [ms Ems].
  destruct (longest_match_correct m S SP p X ra' Hret Hsc
              ltac:(unfold ds6u_windowA; exact Cw) ltac:(unfold ds6u_prevA; exact Cp)
              ltac:(rewrite Lw; exact Hwb) ltac:(rewrite Lp; exact Hpb)
              ltac:(unfold ds6u_SIZE, dsl_SIZE; lia_min) ltac:(rewrite Lw; pose proof (zrh_W _ _ _ _ _ _ _ HL); lia_min) ltac:(rewrite Lp; pose proof (zrh_PV _ _ _ _ _ _ _ HL); lia_min)
              (zrh_S8 _ _ _ _ _ _ _ HL) (zrh_PV2 _ _ _ _ _ _ _ HL) ltac:(lia_min)
              ltac:(unfold ds6u_SIZE, dsl_SIZE; lia_min) ltac:(rewrite Lw; lia_min) ltac:(rewrite Lp; lia_min) ltac:(unfold ds6u_SIZE, dsl_SIZE; rewrite Lw; lia_min) ltac:(unfold ds6u_SIZE, dsl_SIZE; rewrite Lp; lia_min)
              ltac:(intros x Hx; apply MF; lia_min) ltac:(unfold ds6u_SIZE; exact MS)
              ltac:(rewrite Lw; lia_min) ltac:(rewrite Lp, Hwm; lia_min) Hpl Hnice Hlook Hgood Hchain ltac:(lia_min)
              regs cur P1 P2 P10 P11 Hch1 Hcur Hvis)
    as (R & m' & Hms & R10 & R2 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & Hfr & Hsc' & Hag & HGR').
  exists R, m', ms. split; [exact Hms|]. split; [exact Ems|].
  rewrite Ems in Hsc'.
  assert (HFG : forall x, in_franges [(SP - 112, 112); (S + 176, 4)] x -> in_franges (GDo (ds_strm X)) x).
  { intros x Hx. apply in_GDo. unfold DSLOW_FRAME6u, DSLOW_FR6u. cbn in Hx. lia_min. }
  assert (HFM : forall x : word, in_franges [(SP - 112, 112); (S + 176, 4)] (bv_unsigned x) -> m x <> None).
  { intros x Hx. cbn in Hx. destruct Hx as [Hx|[Hx|[]]]; [apply MF; lia_min | apply MS; unfold ds6_SIZE, dsl_SIZE; lia_min]. }
  split.
  { split.
    {
      unfold BR. split; [exact Hsc'|].
      split; [unfold ds6u_arrays in *; dsred; eapply arrays_agree_out6u; [exact Har | exact Hag | intros x Hx; cbn in Hx; lia_min | lia_min | lia_min]|].
      split; [exact Hlens|].
      split; [dsred; eapply cells_agree_out; [exact Hag | intros x Hx Hin; cbn in Hin; apartF 1%nat 5%nat A15; apartF 0%nat 5%nat A05; lia_min | cbn; lia_min | lia_min | lia_min | exact Hpend]|].
      split; [dsred; exact Epbl|].
      split; [eapply agree_out_trans; [exact HagF | eapply agree_out_weaken; [exact Hag | intros x Hx; apply in_Fd; unfold DSLOW_FRAME6u; cbn in Hx; lia_min]]|].
      split; [intros x Hx; apply HGR'; apply MS; exact Hx|]. split; [intros x Hx; apply HGR'; apply MP; exact Hx|].
      intros x Hx. apply HGR'. apply HGR0. exact Hx. }
    split; [| dsred; exact (conj Ews (conj Ehs Elbs))].
    dsred. eapply (RZ_agree m1 m m' _ _ _ _ [(SP - 112, 112); (S + 176, 4)] HR Hag HFG HFM); try exact HGR'.
    - intros x Hx Hin; cbn in Hin; lia_min.
    - intros x Hx Hin; cbn in Hin; lia_min.
    - apartF 0%nat 4%nat A04. apartF 1%nat 4%nat A14. intros x Hx Hin; cbn in Hin; lia_min.
    - apartF 0%nat 6%nat A06. apartF 1%nat 6%nat A16. intros x Hx Hin; cbn in Hin; lia_min.
    - apartF 0%nat 8%nat A08. apartF 1%nat 8%nat A18. intros x Hx Hin; cbn in Hin; lia_min.
    - apartF 0%nat 7%nat A07. apartF 1%nat 7%nat A17. intros x Hx Hin; cbn in Hin; lia_min. }
  split; [exact R10|]. split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R18|].
  split; [exact R19|]. split; [exact R20|]. split; [exact R21|]. split; [exact R22|].
  split; [exact R23|]. split; [exact R24|]. split; [exact R25|]. split; [exact R26|]. split; [exact R27|]. exact Hfr.
Qed.




Definition Fbits : franges := [(S, ds6_SIZE); (PB, PBL)].
Definition Ffb : franges := [(S, ds6_SIZE); (PB, PBL); (SP - TFB_FRAME6u, TFB_FRAME6u); (strm + 88, 4)].

Lemma call_fb : forall regs m1 m X (ra' : word) (buf : option Z) (bufp len last : Z),
  DI m1 m X -> ret_ok ra' ->
  FBSAFE X buf len last -> BINV PBL X ->
  0 <= last <= 1 -> 0 <= len < 2 ^ 32 ->
  (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256) ->
  match buf with
  | None => bufp = 0
  | Some off => bufp = W + off /\ 0 <= off < 2 ^ 32 /\ (len <> 0 -> off + len <= 2 * ws)
  end ->
  getr regs 10 = zw S -> getr regs 11 = zw bufp -> getr regs 12 = zw len -> getr regs 13 = zw last ->
  getr regs 2 = zw SP -> getr regs 1 = ra' ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1bff0 : word) m s6u_rom) (mkst R ra' m' s6u_rom)
    /\ DI m1 m' (tr_flush_block X buf len last)
    /\ (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v)
    /\ (forall r : reg, reg_in r TFB_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X ra' buf bufp len last HDI Hret Hsafe HBI Hlast Hlen Hwb Hbuf P10 P11 P12 P13 P2 P1.
  pose proof HDI as (HB & HR & (Ews & Ehs & Elbs)).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN). unfold DSLOW_FRAME6u, DSLOW_FR6u in Hsp, MF.
  pose proof (BRH_d _ _ _ _ _ _ _ _ _ _ _ HH) as (BA1 & BA2 & BA3 & _). pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws. pose proof (wf_lbs _ HWF) as Wlbs.
  apartF 0%nat 1%nat A01. apartF 0%nat 5%nat A05. apartF 0%nat 6%nat A06. apartF 1%nat 6%nat A16. apartF 5%nat 6%nat A56. apartF 1%nat 5%nat A15.
  mappedF 6%nat M6.
  assert (HBRH : BRH Ffb S p PBL).
  { unfold BRH, Ffb, ds6_SIZE, dsl_SIZE, TFB_FRAME6u. split; [lia_min|]. split; [lia_min|]. split; [lia_min|].
    split; [intros x Hx; cbn; lia_min|]. split; [intros x Hx; cbn; lia_min|]. split; [intros x Hx; cbn; lia_min|]. intros x Hx; cbn; lia_min. }
  assert (HFS : sub_franges Ffb S dsl_SIZE) by (unfold Ffb, ds6_SIZE, dsl_SIZE; intros x Hx; cbn; lia_min).
  assert (Hcf : call_frame Ffb m S PB PBL SP TFB_FRAME6u).
  { unfold call_frame, Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE. split; [lia_min|]. split; [intros x Hx; cbn; lia_min|].
    split; [intros x Hx; apply MF; lia_min|]. split; lia_min. }
  assert (Hsrc : fb_src6u Ffb m p X buf bufp len).
  { unfold fb_src6u. destruct buf as [off|]; [|exact Hbuf]. destruct Hbuf as (Hbp & Ho & Hrest).
    split; [exact Hbp|]. split; [lia_min|]. intros Hnz. pose proof (Hrest Hnz) as Hol'.
    split; [lia_min|]. split; [lia_min|]. split; [exact Cw|]. split; [intros j Hj; apply Hwb; lia_min|].
    split; [lia_min|]. split; [lia_min|]. rewrite Lw.
    apartF 1%nat 2%nat A12. apartF 2%nat 5%nat A25. apartF 0%nat 2%nat A02. apartF 2%nat 6%nat A26.
    unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min. }
  assert (Hstrm' : fb_strm6u Ffb m S p PBL SP X).
  { unfold fb_strm6u, Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE. split; [exact (zsl_data_type s6u_segs _ _ _ _ _ Zs)|].
    split; [lia_min|]. split; [lia_min|]. split; [intros x Hx; cbn; lia_min|].
    split; [intros x Hx; apply HGR; apply M6; lia_min|]. split; [lia_min|]. split; lia_min. }
  destruct (TFB Ffb m m S p PBL X ra' regs SP buf bufp len last MEMSET MEMCPY
              HBRH HFS Hret (BR_self s6u_segs 180992 181024 181056 _ Ffb _ _ _ _ _ _ HB) HBI (proj1 HRC) Hsafe Hlast Hlen Hcf Hsrc Hstrm' UBT_ds P10 P11 P12 P13 P2 P1)
    as (R & m' & Hms & HB' & Cdt' & Hrod' & Hfr). unfold A6U_TR_FLUSH_BLOCK in Hms. symex_pc_lit_in Hms.
  destruct (BR_back s6u_segs 180992 181024 181056 Fd Ffb mem S p PBL m m' X _ HB HB') as [HB2 Hag].
  { unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE. intros x [Hx|[Hx|[Hx|[Hx|[]]]]]; cbn in Hx; apply in_Fd; unfold DSLOW_FRAME6u; lia_min. }
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & _ & _ & _ & HGR').
  exists R, m'. split; [exact Hms|].
  assert (HFM : forall x : word, in_franges Ffb (bv_unsigned x) -> m x <> None).
  { unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE. intros x [Hx|[Hx|[Hx|[Hx|[]]]]]; cbn in Hx;
      [apply MS; exact Hx | apply MP; exact Hx | apply MF; lia_min | apply HGR; apply M6; lia_min]. }
  split.
  { split; [exact HB2|].
    pose proof (tfb_sizes X buf len last) as Esz. unfold ds_sizes in Esz. injection Esz as Esz1 Esz2 Esz3.
    split; [| rewrite Esz1, Esz2, Esz3; exact (conj Ews (conj Ehs Elbs))].
    rewrite tfb_window, tfb_prev, tfb_head.
    pose proof (tfb_io X buf len last) as EIO. unfold ds_io, cs_io in EIO. injection EIO as Ein' Eni' Eai' Eor' Eao' Eti' Eto' Emsg' Eadl'.
    unfold DeflKit6u.RZ.
    split; [eapply cells_agree_out; [exact Hag | rewrite Lw | cbn; lia_min | lia_min | rewrite Lw; lia_min | exact Cw];
           apartF 1%nat 2%nat A12; apartF 2%nat 5%nat A25; apartF 0%nat 2%nat A02; apartF 2%nat 6%nat A26;
           unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE; intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min|].
    split; [eapply cells_agree_out; [exact Hag | rewrite Lp | cbn; lia_min | lia_min | rewrite Lp; lia_min | exact Cp];
           apartF 1%nat 3%nat A13; apartF 3%nat 5%nat A35; apartF 0%nat 3%nat A03; apartF 3%nat 6%nat A36;
           unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE; intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min|].
    split; [eapply cells_agree_out; [exact Hag | rewrite Lh | cbn; lia_min | lia_min | rewrite Lh; lia_min | exact Ch];
           apartF 1%nat 4%nat A14; apartF 4%nat 5%nat A45; apartF 0%nat 4%nat A04; apartF 4%nat 6%nat A46;
           unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE; intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min|].
    split.
    { rewrite tfb_strm_eq. unfold zsl_scalars. rewrite <- zsl_vals_data_type.
      eapply (fields_agree_field s6u_segs Ffb m m' strm zsl_layout (zsl_vals zp S (ds_strm X)) zsl_SIZE 11 88 4%nat);
        [exact Zs | reflexivity | vm_compute; reflexivity | exact zsl_layout_within | exact Hag | | exact Cdt' | lia_min | unfold zsl_SIZE; lia_min].
      unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE, zsl_SIZE. intros x [Hin|[Hin|[Hin|[Hin|[]]]]] Hx; cbn in Hin; lia_min. }
    split; [unfold zsl_input in *; rewrite Ein', Ein in *; eapply cells_agree_out; [exact Hag | | cbn; lia_min | lia_min | lia_min | exact Zi];
           apartF 1%nat 8%nat A18; apartF 5%nat 8%nat A58; apartF 0%nat 8%nat A08; apartF 6%nat 8%nat A68;
           unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE; intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min|].
    split; [unfold zsl_outA6u, cs_output in *; rewrite Eor'; eapply cells_agree_out; [exact Hag | | cbn; lia_min | lia_min | lia_min | exact Zo];
           apartF 1%nat 7%nat A17; apartF 5%nat 7%nat A57; apartF 0%nat 7%nat A07; apartF 6%nat 7%nat A67;
           unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE; intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min|].
    split.
    { unfold DeflKit6u.RZmisc. split; [split; [exact (trees_rod_clear_agree R6u Ffb m m' (proj1 HRC) Hag HFM) | exact (got_agree6u Ffb m m' (proj2 HRC) Hag HFM)]|].
      split; [refine (rom_agree6u ROM Ffb m m' HRL HRD Hag _); unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE; intros x [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; apply GDI; apply in_GD; unfold DSLOW_FRAME6u, DSLOW_FR6u; lia_min|].
      split; [unfold DeflKit6u.GDo; rewrite Eor'; eapply agree_out_trans; [exact HAG | eapply agree_out_weaken; [exact Hag |]];
             unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE; intros x [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; apply (in_GDo (ds_strm X)); unfold DSLOW_FRAME6u, DSLOW_FR6u; lia_min|].
      split; [intros x Hx; apply HGR'; apply MF; exact Hx|].
      intros x Hx. apply HGR'. apply HGR. exact Hx. }
    unfold DeflKit6u.CST. rewrite Ein', Eor', Eao'. exact HC. }
  split; [| exact Hfr].
  intros a w v Hc Ha1 Ha2. unfold TFB_FRAME6u, ds6_SIZE, dsl_SIZE in *.
  apply (cell_agree_out s6u_segs Ffb m m' a w v Hag); [| lia_min | lia_min | exact Hc].
  unfold Ffb, TFB_FRAME6u, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min.
Qed.



Local Abbreviation LFW X := (FillWin6uA.LF S SP p X).

Lemma call_fw : forall regs m1 m X (ra' : word),
  DI m1 m X -> ret_ok ra' -> BSI X ->
  fw_wf ws hs X -> ds_lookahead X < MIN_LOOKAHEAD -> ds_wrap X = 1 ->
  getr regs 1 = ra' -> getr regs 2 = zw SP -> getr regs 10 = zw S ->
  exists R m',
    msteps s6u_segs (mkst regs (0x169b8 : word) m s6u_rom) (mkst R ra' m' s6u_rom)
    /\ DI m1 m' (fill_window X)
    /\ fw_wf ws hs (fill_window X) /\ BSI (fill_window X)
    /\ getr R 2 = zw SP
    /\ (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v)
    /\ (forall r : reg, reg_in r c_clob = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X ra' HDI Hret HBS HWFX Hlook Hwrap P1 P2 P10.
  pose proof HDI as (HB & HR & (Ews & Ehs & Elbs)).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HB as (_ & _ & _ & _ & Epbl & _). unfold dsl_pendA in Hpend. rewrite Epbl in Hpend.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN). unfold DSLOW_FRAME6u, DSLOW_FR6u in Hsp, MF.
  pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws. pose proof (DeflSlow6_1.wf_hsz _ HWF) as Whs. pose proof (wf_lbs _ HWF) as Wlbs.
  mappedF 2%nat M2. mappedF 3%nat M3. mappedF 4%nat M4. mappedF 6%nat M6.
  assert (HFW : fw_pre s6u_segs 180992 181024 181056 272 m S SP p zp X).
  { constructor.
    - unfold zst. split; [exact Hsc|]. split; [exact Cw|]. split; [exact Cp|]. split; [exact Ch|].
      split; [exact Zs | exact Zi].
    - rewrite Ews, Ehs. exact HWFX.
    - exact Hlook.
    - intros x Hx. apply MF. lia_min.
    - intros x Hx. apply MS. unfold ds6_SIZE, dsl_SIZE in *. lia_min.
    - rewrite Ews. intros x Hx. apply HGR. apply M2. lia_min.
    - rewrite Ews. intros x Hx. apply HGR. apply M3. lia_min.
    - rewrite Ehs. intros x Hx. apply HGR. apply M4. lia_min.
    - intros x Hx. apply HGR. apply M6. unfold zsl_SIZE in Hx. lia_min.
    - lia_min.
    - unfold dsl_SIZE. lia_min.
    - rewrite Ews. lia_min.
    - rewrite Ews. lia_min.
    - rewrite Ehs. lia_min.
    - unfold zsl_SIZE. lia_min.
    - rewrite Ein. lia_min.
    - unfold fw_regions. rewrite Ews, Ehs, Ein. unfold dsl_SIZE, zsl_SIZE. cbn [apart_all apart_from].
      repeat split; unfold apart; cbn [fst snd];
      [ apartF 0%nat 1%nat A; lia_min | apartF 0%nat 2%nat A; lia_min | apartF 0%nat 3%nat A; lia_min | apartF 0%nat 4%nat A; lia_min
      | apartF 0%nat 6%nat A; lia_min | apartF 0%nat 8%nat A; lia_min
      | apartF 1%nat 2%nat A; lia_min | apartF 1%nat 3%nat A; lia_min | apartF 1%nat 4%nat A; lia_min | apartF 1%nat 6%nat A; lia_min | apartF 1%nat 8%nat A; lia_min
      | apartF 2%nat 3%nat A; lia_min | apartF 2%nat 4%nat A; lia_min | apartF 2%nat 6%nat A; lia_min | apartF 2%nat 8%nat A; lia_min
      | apartF 3%nat 4%nat A; lia_min | apartF 3%nat 6%nat A; lia_min | apartF 3%nat 8%nat A; lia_min
      | apartF 4%nat 6%nat A; lia_min | apartF 4%nat 8%nat A; lia_min
      | apartF 6%nat 8%nat A; lia_min ]. }
  assert (HLFI : forall x, in_franges (LFW X) x -> IMG6U_LO <= x < IMG6U_HI -> False).
  { intros x Hx. apply GDI. apply in_GD. unfold DSLOW_FRAME6u, DSLOW_FR6u. unfold FillWin6uA.LF in Hx. rewrite Ews, Ehs in Hx. cbn in Hx. lia_min. }
  destruct (fill_window_correct m S SP p zp X ra' regs ROM Hret HFW Hwrap (zrh_HD _ _ _ _ _ _ _ HL) (zrh_PV _ _ _ _ _ _ _ HL)
              HRD HRL MEMCPY MEMSET ADLER UBP_ds HLFI P1 P2 P10 HBS)
    as (R & m' & Hms & R2 & Hfr & Hzst & HWF' & HK & HBS' & Hag & HGR' & HROM').
  exists R, m'. split; [exact Hms|].
  set (X' := fill_window X) in *.
  pose proof (fw_rest_fill_window X) as EK. fold X' in EK. unfold fw_rest in EK.
  injection EK as Kstatus Kpending_buf Kpending_buf_size Kpending_out Kpending Kwrap Kgzhead Kgzindex Kmethod Klast_flush Kw_size Kw_bits Kw_mask Kwindow_size Khash_size Khash_bits Khash_mask Khash_shift Kmatch_length Kprev_match Kmatch_available Kprev_length Kmax_chain_length Kmax_lazy_match Klevel Kstrategy Kgood_match Knice_match Kdyn_ltree_fc Kdyn_ltree_dl Kdyn_dtree_fc Kdyn_dtree_dl Kbl_tree_fc Kbl_tree_dl Kl_max_code Kd_max_code Kbl_max_code Kbl_count Kheap Kheap_len Kheap_max Kdepth Klit_bufsize Ksym_next Ksym_end Kopt_len Kstatic_len Kmatches Kbi_buf Kbi_valid Kinput Kout_rev Kavail_out Ktotal_out Kmsg Kdata_type.
  destruct HK as (Kwl & Kpl & Khl & Kin & Kwr & Kws & Khs).
  destruct Hzst as (Hsc' & Cw' & Cp' & Ch' & Zs' & Zi').
  assert (HFG : forall x, in_franges (LFW X) x -> in_franges (GDo (ds_strm X)) x).
  { intros x Hx. apply in_GDo. unfold DSLOW_FRAME6u, DSLOW_FR6u. unfold FillWin6uA.LF in Hx. rewrite Ews, Ehs in Hx. cbn in Hx. lia_min. }
  assert (HFM : forall x : word, in_franges (LFW X) (bv_unsigned x) -> m x <> None).
  { intros x Hx. unfold FillWin6uA.LF in Hx. rewrite Ews, Ehs in Hx. cbn in Hx.
    destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[]]]]]]]]]]]];
      first [ apply MF; lia_min | apply MS; unfold ds6_SIZE, dsl_SIZE; lia_min | apply HGR; first [apply M2; lia_min | apply M3; lia_min | apply M4; lia_min | apply M6; lia_min] ]. }
  split.
  { split.
    { unfold BR. split; [exact Hsc'|].
      split.
      { unfold ds6u_arrays, dsl_arrays in *. rewrite Kdyn_ltree_fc, Kdyn_ltree_dl, Kdyn_dtree_fc, Kdyn_dtree_dl, Kbl_tree_fc, Kbl_tree_dl, Kbl_count, Kheap, Kdepth.
        eapply (arrays_agree_out6u (LFW X) m m'); [exact Har | exact Hag | | lia_min | lia_min].
        intros x Hx. unfold FillWin6uA.LF in Hx. rewrite Ews, Ehs in Hx. cbn in Hx.
        apartF 1%nat 2%nat A12. apartF 1%nat 3%nat A13. apartF 1%nat 4%nat A14. apartF 1%nat 6%nat A16. apartF 0%nat 1%nat A01. lia_min. }
      split; [unfold tree_lens in *; rewrite Kdyn_ltree_fc, Kdyn_ltree_dl, Kdyn_dtree_fc, Kdyn_dtree_dl, Kbl_tree_fc, Kbl_tree_dl, Kbl_count, Kheap, Kdepth; exact Hlens|].
      split.
      { rewrite Kpending_buf. eapply cells_agree_out; [exact Hag | | cbn; lia_min | lia_min | lia_min | exact Hpend].
        intros x Hx Hin. unfold FillWin6uA.LF in Hin. rewrite Ews, Ehs in Hin. cbn in Hin.
        apartF 1%nat 5%nat A15. apartF 2%nat 5%nat A25. apartF 3%nat 5%nat A35. apartF 4%nat 5%nat A45. apartF 5%nat 6%nat A56. apartF 0%nat 5%nat A05. lia_min. }
      split; [rewrite Kpending_buf; exact Epbl|].
      split; [eapply agree_out_trans; [exact HagF | eapply agree_out_weaken; [exact Hag |]];
             intros x Hx; apply in_Fd; unfold DSLOW_FRAME6u; unfold FillWin6uA.LF in Hx; rewrite Ews, Ehs in Hx; cbn in Hx; lia_min|].
      split; [intros x Hx; apply HGR'; apply MS; exact Hx|]. split; [intros x Hx; apply HGR'; apply MP; exact Hx|].
      intros x Hx. apply HGR'. apply HGR0. exact Hx. }
    split; [| rewrite Kw_size, Khash_size, Klit_bufsize; exact (conj Ews (conj Ehs Elbs))].
    unfold DeflKit6u.RZ.
    split; [exact Cw'|]. split; [exact Cp'|]. split; [exact Ch'|]. split; [exact Zs'|]. split; [exact Zi'|].
    split.
    { unfold zsl_outA6u, cs_output in *. rewrite Kout_rev. eapply cells_agree_out; [exact Hag | | cbn; lia_min | lia_min | lia_min | exact Zo].
      intros x Hx Hin. unfold FillWin6uA.LF in Hin. rewrite Ews, Ehs in Hin. cbn in Hin.
      apartF 1%nat 7%nat A17. apartF 2%nat 7%nat A27. apartF 3%nat 7%nat A37. apartF 4%nat 7%nat A47. apartF 6%nat 7%nat A67. apartF 0%nat 7%nat A07. lia_min. }
    split.
    { unfold DeflKit6u.RZmisc. split; [split; [exact (trees_rod_clear_agree R6u _ m m' (proj1 HRC) Hag HFM) | exact (got_agree6u _ m m' (proj2 HRC) Hag HFM)]|].
      split; [exact HROM'|].
      split; [unfold DeflKit6u.GDo; rewrite Kout_rev; eapply agree_out_trans; [exact HAG | eapply agree_out_weaken; [exact Hag | exact HFG]]|].
      split; [intros x Hx; apply HGR'; apply MF; exact Hx|].
      intros x Hx. apply HGR'. apply HGR. exact Hx. }
    unfold DeflKit6u.CST. rewrite Kwl, Kpl, Khl, Kin, Kout_rev, Kavail_out, Ews, Ehs. repeat split; first [reflexivity | assumption | lia_min]. }
  split; [rewrite <- Ews, <- Ehs; exact HWF'|]. split; [exact HBS'|]. split; [exact R2|]. split; [| exact Hfr].
  intros a w v Hc Ha1 Ha2.
  apply (cell_agree_out s6u_segs (LFW X) m m' a w v Hag); [| lia_min | lia_min | exact Hc].
  intros x Hx Hin. unfold FillWin6uA.LF in Hin. rewrite Ews, Ehs in Hin. cbn in Hin.
  apartF 0%nat 1%nat A01. apartF 0%nat 2%nat A02. apartF 0%nat 3%nat A03. apartF 0%nat 4%nat A04. apartF 0%nat 6%nat A06. lia_min.
Qed.


End Walk.
End FXG.

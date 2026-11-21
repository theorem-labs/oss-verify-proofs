(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import DS6 CalleeKits6 DeflSlow6_1 DeflSlow6_2 Defl6Api Defl6_1 Defl6_2 Defl6_3 Defl6_5 Defl6_6 Defl6_M DeflSlow6_M.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u Callee6u CalleeKits6u TreesRod6u TreesApi6u TrApi6u
  FillWin6uA DeflBlkApi6u DeflKit6u FlushPend6u DeflSlow6u_8 DeflSlow6u_9 Defl6uApi Defl6u_1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma szwrap_congr : forall k a b, 0 < k -> (exists q, a = b + q * 2 ^ k) -> szwrap k a = szwrap k b.
Proof.
  intros k a b Hk [q ->]. apply szwrap_of_mod; [exact Hk|]. apply Z.mod_add. lia.
Qed.

Lemma rank_chk1 : forall lf, - 2 ^ 30 <= lf < 2 ^ 30 -> 0 <= szwrap 64 (szwrap 32 (lf mod 2 ^ 64 + 1073741824)).
Proof.
  intros lf H.
  rewrite (szwrap_congr 32 (lf mod 2 ^ 64 + 1073741824) (lf + 1073741824)) by
    (try lia; exists (- (lf / 2 ^ 64) * 2 ^ 32); pose proof (Z.div_mod lf (2 ^ 64) ltac:(lia)); nia).
  rewrite szwrap64_32_small by lia. lia.
Qed.

Lemma rank_chk2 : forall lf, - 2 ^ 30 <= lf < 2 ^ 30 ->
  szwrap 32 (lf mod 2 ^ 64 * 2 ^ 1 - Z.land ((if szwrap 64 (lf mod 2 ^ 64) <? 5 then 1 else 0) + -1) 9) mod 2 ^ 64
  = (szwrap 32 (lf mod 2 ^ 64 * 2 ^ 1) - Z.land ((if szwrap 64 (lf mod 2 ^ 64) <? 5 then 1 else 0) + -1) 9) mod 2 ^ 64.
Proof.
  intros lf H.
  rewrite szwrap_mod by lia. rewrite (szwrap64_small lf) by lia.
  assert (E2 : szwrap 32 (lf mod 2 ^ 64 * 2 ^ 1) = lf * 2).
  { rewrite (szwrap_congr 32 (lf mod 2 ^ 64 * 2 ^ 1) (lf * 2)) by
      (try lia; exists (- (lf / 2 ^ 64) * 2 ^ 33); pose proof (Z.div_mod lf (2 ^ 64) ltac:(lia)); nia).
    apply szwrap32_small. lia. }
  set (c := Z.land ((if lf <? 5 then 1 else 0) + -1) 9).
  assert (Hc : (lf < 5 /\ c = 0) \/ (5 <= lf /\ c = 9)) by (subst c; destruct (Z.ltb_spec lf 5); [left | right]; split; first [lia | reflexivity]).
  rewrite (szwrap_congr 32 (lf mod 2 ^ 64 * 2 ^ 1 - c) (lf * 2 - c)) by
    (try lia; exists (- (lf / 2 ^ 64) * 2 ^ 33); pose proof (Z.div_mod lf (2 ^ 64) ltac:(lia)); nia).
  rewrite E2. rewrite szwrap32_small by lia. reflexivity.
Qed.

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

Lemma zext32_small : forall a, 0 <= a < 2 ^ 32 -> (a * 2 ^ 32) mod 2 ^ 64 / 2 ^ 32 = a.
Proof.
  intros a Ha. rewrite Z.mod_small by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma sx32_of_mod : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> szwrap 32 (x mod 2 ^ 32) = x.
Proof. intros x Hx. rewrite szwrap_mod by lia. apply szwrap_small; lia. Qed.


Definition prob_pc (X : deflate_state) : word := if ds_pending X =? 0 then (0x170d0 : word) else (0x181ac : word).

Lemma prob_blk : forall regs m1 m X,
  DI m1 m X ->
  getr regs 8 = zw S -> getr regs 2 = zw SP -> getr regs 10 = zw strm -> getr regs 11 = zw flush ->
  getr regs 13 = zw (ds_status X) ->
  (flush = 0 \/ flush = 3 \/ flush = 4) -> (flush <> 4 -> ds_status X <> 666) -> (cs_avail_in (ds_strm X) = 0 -> flush = 4) ->
  0 <= ds_status X < 2 ^ 31 ->
  0 <= cs_avail_in (ds_strm X) < 2 ^ 31 -> 0 < cs_avail_out (ds_strm X) < 2 ^ 31 -> 0 <= ds_pending X < 2 ^ 63 ->
  0 <= cs_next_in (ds_strm X) -> INP + cs_next_in (ds_strm X) < 2 ^ 63 ->
  - 2 ^ 31 <= ds_last_flush X < 2 ^ 31 ->
  exists R M,
    msteps s6u_segs (mkst regs (0x17008 : word) m s6u_rom) (mkst R (prob_pc X) M s6u_rom)
    /\ DI m1 M (set_last_flush X flush)
    /\ HREGS R /\ getr R 13 = zw (ds_status X)
    /\ getr R 10 = zw strm /\ getr R 11 = zw flush /\ getr R 14 = zw (cs_avail_in (ds_strm X))
    /\ getr R 12 = zw (ds_last_flush X)
    /\ (ds_pending X <> 0 -> getr R 1 = (0x17094%bv : word))
    /\ (forall r : reg, reg_in r [1; 9; 12; 14; 15; 18]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI P8 P2 P10 P11 P13 Hf Hf0 Hai4 Hst Hai Hao Hpd Hni0 Hni1 Hlf. open_di HDI.
  zs_cell Zs (@zsl_next_out) C24. zs_cell Zs (@zsl_avail_in) C8. zs_cell Zs (@zsl_next_in) C0z. rewrite Z.add_0_r in C0z.
  zs_cell Zs (@zsl_avail_out) C32.
  sc_cell Hsc ds6u_pending C40. sc_cell Hsc ds6u_last_flush C76.
  assert (RD76 : exists bs, rdn s6u_segs m (zw (S + 76)) 4 = Some bs /\ bytes_le_to_Z bs = ds_last_flush X mod 2 ^ 32)
    by exact (cell_read_at s6u_segs m (S + 76) 4 _ _ C76 eq_refl).
  pose proof (Z.mod_pos_bound (ds_last_flush X) (2 ^ 32) ltac:(lia)) as Hlfm.
  pose proof (sx32_of_mod (ds_last_flush X) Hlf) as Hsx.
  pose proof (zrh_O _ _ _ _ _ _ _ HL) as HO.
  apartF 1%nat 6%nat A16.
  unfold prob_pc.
  Local Ltac pro_b_fin Hms HDI HR Hfr Hsx :=
    clear_aparts; rewrite ?le_bytes_sx32 in Hms;
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KLastFlush];
    ex2; split; [exact Hms|]; split; [the_DI|];
    split; [unfold HREGS; repeat split; reg1 HR Hfr|];
    split; [reg1 HR Hfr|]; split; [reg1 HR Hfr|]; split; [reg1 HR Hfr|]; split; [reg1 HR Hfr|];
    split; [let A := fresh "A" in symex_reg HR (12%bv : reg) as A; rewrite A; rewrite Hsx; reflexivity|];
    split; [first [intros Hc; exfalso; lia | intros _; reg1 HR Hfr]|];
    fr_weak Hfr.
  destruct (Z.eqb_spec (ds_pending X) 0) as [Hp0|Hpn].
  - rewrite Hp0 in *.
    destruct (Z.eq_dec (cs_avail_in (ds_strm X)) 0) as [Hz|Hnz].
    + pose proof (Hai4 Hz) as Ef. rewrite Hz in *.
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (10, EVar 35%nat); (11, EVar 34%nat); (13, EVar 36%nat)] 36%nat
        [false; false; true; true; false; true]
        [RVal (EVar 37); RVal (ELit 0); RVal (EVar 40); RVal (ELit 0); RVal (EVar 42)]
        [(36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (40%nat, 2 ^ 31); (42%nat, 2 ^ 32)]
        [ds_status X; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); 0; 0; cs_avail_out (ds_strm X); 0; ds_last_flush X mod 2 ^ 32].
      pro_b_fin Hms HDI HR Hfr Hsx.
    +
      destruct (Z.eq_dec flush 4) as [Ef | Ef4]; [| assert (Ef : flush = 0 \/ flush = 3) by lia].
      2:{ pose proof (Hf0 Ef4) as Hs6.
        run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (10, EVar 35%nat); (11, EVar 34%nat); (13, EVar 36%nat)] 36%nat
          [false; false; false; false; false; true; false; true]
          [RVal (EVar 37); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40); RVal (ELit 0); RVal (EVar 42)]
          [(36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 31); (39%nat, 2 ^ 63); (40%nat, 2 ^ 31); (42%nat, 2 ^ 32)]
          [ds_status X; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); cs_avail_in (ds_strm X); INP + cs_next_in (ds_strm X);
           cs_avail_out (ds_strm X); 0; ds_last_flush X mod 2 ^ 32].
        pro_b_fin Hms HDI HR Hfr Hsx. }
      * run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (10, EVar 35%nat); (11, EVar 34%nat); (13, EVar 36%nat)] 36%nat
          [false; false; false; false; true; false; true]
          [RVal (EVar 37); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40); RVal (ELit 0); RVal (EVar 42)]
          [(36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 31); (39%nat, 2 ^ 63); (40%nat, 2 ^ 31); (42%nat, 2 ^ 32)]
          [ds_status X; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); cs_avail_in (ds_strm X); INP + cs_next_in (ds_strm X);
           cs_avail_out (ds_strm X); 0; ds_last_flush X mod 2 ^ 32].
        pro_b_fin Hms HDI HR Hfr Hsx.
  - destruct (Z.eq_dec (cs_avail_in (ds_strm X)) 0) as [Hz|Hnz].
    + pose proof (Hai4 Hz) as Ef. rewrite Hz in *.
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (10, EVar 35%nat); (11, EVar 34%nat); (13, EVar 36%nat)] 36%nat
        [false; false; true; true; false; false]
        [RVal (EVar 37); RVal (ELit 0); RVal (EVar 40); RVal (EVar 41); RVal (EVar 42)]
        [(36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (40%nat, 2 ^ 31); (41%nat, 2 ^ 63); (42%nat, 2 ^ 32)]
        [ds_status X; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); 0; 0; cs_avail_out (ds_strm X); ds_pending X; ds_last_flush X mod 2 ^ 32].
      pro_b_fin Hms HDI HR Hfr Hsx.
    +
      destruct (Z.eq_dec flush 4) as [Ef | Ef4]; [| assert (Ef : flush = 0 \/ flush = 3) by lia].
      2:{ pose proof (Hf0 Ef4) as Hs6.
        run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (10, EVar 35%nat); (11, EVar 34%nat); (13, EVar 36%nat)] 36%nat
          [false; false; false; false; false; true; false; false]
          [RVal (EVar 37); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40); RVal (EVar 41); RVal (EVar 42)]
          [(36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 31); (39%nat, 2 ^ 63); (40%nat, 2 ^ 31); (41%nat, 2 ^ 63); (42%nat, 2 ^ 32)]
          [ds_status X; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); cs_avail_in (ds_strm X); INP + cs_next_in (ds_strm X);
           cs_avail_out (ds_strm X); ds_pending X; ds_last_flush X mod 2 ^ 32].
        pro_b_fin Hms HDI HR Hfr Hsx. }
      * run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (10, EVar 35%nat); (11, EVar 34%nat); (13, EVar 36%nat)] 36%nat
          [false; false; false; false; true; false; false]
          [RVal (EVar 37); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40); RVal (EVar 41); RVal (EVar 42)]
          [(36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 31); (39%nat, 2 ^ 63); (40%nat, 2 ^ 31); (41%nat, 2 ^ 63); (42%nat, 2 ^ 32)]
          [ds_status X; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); cs_avail_in (ds_strm X); INP + cs_next_in (ds_strm X);
           cs_avail_out (ds_strm X); ds_pending X; ds_last_flush X mod 2 ^ 32].
        pro_b_fin Hms HDI HR Hfr Hsx.
Qed.


Lemma pend0_blk : forall regs m X,
  HREGS regs -> getr regs 14 = zw (cs_avail_in (ds_strm X)) -> getr regs 12 = zw (ds_last_flush X) -> getr regs 11 = zw flush ->
  (cs_avail_in (ds_strm X) = 0 -> flush = 4) -> 0 <= cs_avail_in (ds_strm X) < 2 ^ 31 ->
  - 2 ^ 30 <= ds_last_flush X < 2 ^ 30 ->
  exists R,
    msteps s6u_segs (mkst regs (0x170d0 : word) m s6u_rom) (mkst R (0x170d4 : word) m s6u_rom)
    /\ HREGS R /\ getr R 10 = getr regs 10 /\ getr R 11 = getr regs 11 /\ getr R 13 = getr regs 13
    /\ (forall r : reg, reg_in r [12; 14; 15]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m X HRG P14 P12 P11 Hai4 Hai Hlf. open_min. open_hregs HRG.
  destruct (Z.eq_dec (cs_avail_in (ds_strm X)) 0) as [Hz|Hnz].
  - pose proof (Hai4 Hz) as Ef. rewrite Hz in P14.
    rewrite <- zw_mod in P12.
    pose proof (Z.mod_pos_bound (ds_last_flush X) (2 ^ 64) ltac:(lia)) as Hlb.
    run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (11, EVar 34%nat); (12, EVar 36%nat); (14, ELit 0)] 24%nat
      [true; false; false; true] NoReads [(36%nat, 2 ^ 64)] [ds_last_flush X mod 2 ^ 64].
    1: apply rank_chk1; exact Hlf.
    1: apply rank_chk2; exact Hlf.
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
  - run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (11, EVar 34%nat); (14, EVar 36%nat)] 4%nat
      [false] NoReads [(36%nat, 2 ^ 31)] [cs_avail_in (ds_strm X)].
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Lemma fpret_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32 -> 0 <= ds_status X < 2 ^ 31 ->
  exists R,
    msteps s6u_segs (mkst regs (0x17094 : word) m s6u_rom)
           (mkst R (Defl6_2.avail_pc X (0x17ea0 : word) (0x170d4 : word)) m s6u_rom)
    /\ HREGS R
    /\ (cs_avail_out (ds_strm X) <> 0 -> getr R 10 = zw strm /\ getr R 11 = zw flush /\ getr R 13 = zw (ds_status X))
    /\ (forall r : reg, reg_in r [10; 11; 13]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hav Hst. open_di HDI. open_hregs HRG.
  zs_cell Zs (@zsl_avail_out) C32. sc_cell Hsc ds6u_status C8.
  unfold Defl6_2.avail_pc. destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
  - rewrite Hz in C32.
    run 6%nat [true] [RVal (ELit 0)] NoBounds (@nil Z).
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros Hc; exfalso; lia | fr_weak Hfr].
  - pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
    run 10%nat [false] [RVal (EVar 36); RVal (EVar 37)] [(36%nat, 2 ^ 32); (37%nat, 2 ^ 31)] [cs_avail_out (ds_strm X); ds_status X].
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros _; repeat split; reg1 HR Hfr | fr_weak Hfr].
Qed.


Lemma d42_blk : forall regs m,
  HREGS regs -> getr regs 13 = zw 42 ->
  exists R,
    msteps s6u_segs (mkst regs (0x170d4 : word) m s6u_rom) (mkst R (0x170f8 : word) m s6u_rom)
    /\ HREGS R /\ getr R 10 = getr regs 10
    /\ (forall r : reg, reg_in r [12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m HRG P13. open_min. open_hregs HRG.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (13, ELit 42)] 4%nat
    [true] NoReads NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.

Lemma d113_blk : forall regs m,
  HREGS regs -> getr regs 13 = zw 113 ->
  exists R,
    msteps s6u_segs (mkst regs (0x170d4 : word) m s6u_rom) (mkst R (0x171e4 : word) m s6u_rom)
    /\ HREGS R /\ getr R 10 = getr regs 10 /\ getr R 11 = getr regs 11 /\ getr R 13 = zw 113
    /\ (forall r : reg, reg_in r [12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m HRG P13. open_min. open_hregs HRG.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (13, ELit 113)] 8%nat
    [false; true] NoReads NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.

Lemma d666_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 13 = zw 666 -> getr regs 10 = zw strm -> cs_avail_in (ds_strm X) = 0 ->
  exists R,
    msteps s6u_segs (mkst regs (0x170d4 : word) m s6u_rom) (mkst R (0x17dc0 : word) m s6u_rom)
    /\ HREGS R /\ getr R 10 = zw strm /\ getr R 11 = getr regs 11 /\ getr R 12 = zw 0
    /\ (forall r : reg, reg_in r [12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG P13 P10 Hai. open_di HDI. open_hregs HRG.
  zs_cell Zs (@zsl_avail_in) C8. rewrite Hai in C8.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat); (13, ELit 666); (10, EVar 35%nat)] 12%nat
    [false; false; true] [RVal (ELit 0)] NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.

End Walk.
End FXG.

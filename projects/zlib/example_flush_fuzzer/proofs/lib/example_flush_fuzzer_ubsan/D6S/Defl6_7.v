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
  RomRead TreesRod FlushBlockModel BitsLib DeflM STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel
  RefFlushPend1 RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3 RefDeflateHdr5 RefDeflateTrl1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import TrStored6 Memset6_run Segs6 DS6 Callee6 CalleeKits6 TreesRod6 TreesApi6 DeflBlkApi6
  DeflSlow6_1 DeflSlow6_2 DeflSlow6_6 DeflKit6 Defl6Api Defl6_1 Defl6_2 Defl6_3 Defl6_4 Defl6_5 Defl6_5b Defl6_6 Defl6_M.
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
Hypothesis MEMCPY : memcpy_run6.
Hypothesis TFBITS : tr_flush_bits_run6.
Variable SSAFE : deflate_state -> Z -> Prop.
Hypothesis SLOW : deflate_slow_run6 ROM SSAFE.
Hypothesis MEMSET : memset_run6.
Hypothesis TSB : tr_stored_block_run6.
Let HH : DKH ROM mem S p zp ds flush ra sp DEFL_K6 FR64 := dfh_K _ _ _ _ _ _ _ _ _ HF.
Let HP : DPTRS S p zp := dfh_P _ _ _ _ _ _ _ _ _ HF.
Local Abbreviation DI := (DeflKit6.DI ROM mem S p zp ds sp DEFL_K6 FR64).
Local Abbreviation BRm := (BR s6_segs 168672 168704 168736 (DeflKit6.Fd S p zp ds sp DEFL_K6) mem S p PBL).
Local Abbreviation RZ := (DeflKit6.RZ ROM mem S p zp ds sp DEFL_K6 FR64).
Local Abbreviation GD := (DeflKit6.GD S p zp ds sp DEFL_K6 FR64).
Local Abbreviation DI_eqst := (DeflKit6.DI_eqst ROM mem S p zp ds sp DEFL_K6 FR64).
Local Abbreviation HREGS := (Defl6_1.HREGS S p flush sp).
Local Abbreviation FRM := (Defl6_1.FRM sp).

Let HL : ZRH6 DEFL_K6 mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ _ _ HH.

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac hregs_via HRG Hfr := apply (HREGS_via S p flush sp _ _ _ HRG Hfr); reflexivity.

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
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs dfC fuel dirs rdv pinsv vb NoRegions pv NoVals F0 F0' (mkst regs pc m s6_rom) R HR Hfr Hms
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
  pose proof HRZ as (Cw & Cp & Ch & Zs & _ & _ & (HRC & _ & _ & MF & _) & HC); unfold mapped, DEFL_K6 in MF;
  let Lw := fresh "Lw" in let Lp := fresh "Lp" in let Lh := fresh "Lh" in
  let Ein := fresh "Ein" in let Eout := fresh "Eout" in let Hao := fresh "Hao" in let Hol := fresh "Hol" in
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol); rewrite Lw in Cw; rewrite Lp in Cp; rewrite Lh in Ch;
  let RF := fresh "RF" in
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in let HW := fresh "HW" in let HPV := fresh "HPV" in let HHD := fresh "HHD" in
  let HPB := fresh "HPB" in let Hstrm := fresh "Hstrm" in let HOUT := fresh "HOUT" in let HIN := fresh "HIN" in
  destruct RF as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN); unfold DEFL_K6 in Hsp;
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
  let FRI := fresh "FRI" in pose proof (frame_img _ _ _ _ _ _ _ _ _ HF) as FRI.

Local Ltac apartF i j H :=
  pose proof (apart_ij _ _ _ _ _ _ _ _ _ _ _ HH i j ltac:(lia) ltac:(lia)) as H;
  unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE, DEFL_K6 in H.

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P20 := fresh "P20" in
  pose proof HRG as (P8 & P2 & P9 & P20).

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
          | H1 : DeflKit6.DI _ ?mem ?S ?p ?zp ?ds ?sp _ _ ?m1 M1 ?X |- _ =>
              let H2 := fresh "HDI" in
              lazymatch k with
              | KLastFlush => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_last_flush _ _ _ _ _ _ _ _ _ HF m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KStatus => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_status _ _ _ _ _ _ _ _ _ HF m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KWrap => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_wrap _ _ _ _ _ _ _ _ _ HF m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPending => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_pending ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPendingOut ?off => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_pending_out ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X off a v H1 ltac:(lia) ltac:(lia)) as H2 end
              | KPb ?i ?c' => lazymatch bs with Z_to_le_bytes _ ?c =>
                  pose proof (DI_st_pb ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a i c c' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KAdler => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_adler _ _ _ _ _ _ _ _ _ HF m1 M1 X v a H1 ltac:(lia) ltac:(lia)) as H2 end
              | KFrame => pose proof (DI_st_frame ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a bs H1 ltac:(unfold DEFL_K6; lia)
                            ltac:(rewrite ?length_Z_to_le_bytes; unfold FR64; lia)) as H2
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
      | H1 : DeflKit6.DI _ _ _ _ _ _ _ _ _ M1 M1 ?X |- _ =>
          let H2 := fresh "HDT" in
          pose proof (DI_st_top _ _ _ _ _ _ _ _ _ _ _ HH M1 X a bs H1 ltac:(unfold FR64; lia) ltac:(rewrite ?length_Z_to_le_bytes; cbn; lia)) as H2;
          clear H1
      end
  | _ => let H := fresh "HDT" in pose proof HDI as H
  end.

Local Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); assumption end
        | let A := fresh "A" in
          lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A;
            first [ assumption
                  | lazymatch goal with |- ?a = ?a => reflexivity end
                  | f_equal; lia
                  | f_equal; repeat (rewrite (szwrap_small 32) by lia); rewrite ?Z.mod_small by lia; lia
                  | rewrite zw_u; first [assumption | reflexivity]
                  | lazymatch goal with |- zw ?a = _ => lazymatch isZcst a with true => apply bv_eq; vm_compute; reflexivity end end ] end ].

Local Ltac di_fwd_ms HDI Hms ks := lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => di_fwd HDI M ks end.
Local Ltac di_top_ms HDI Hms := lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => di_top HDI M end.

Local Ltac ex1 := lazymatch goal with H : msteps _ _ (mkst ?R _ _ _) |- _ => exists R end.
Local Ltac ex2 := lazymatch goal with H : msteps _ _ (mkst ?R _ ?M _) |- _ => exists R, M end.
Local Ltac the_DI := lazymatch goal with H : DeflKit6.DI _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact H end.

Local Ltac sc_cell Hsc lem C := pose proof (lem _ _ _ _ Hsc) as C.
Local Ltac zs_cell Zs lem C := pose proof (lem s6_segs _ _ _ _ _ Zs) as C.

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
  destruct RF as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN); unfold DEFL_K6 in Hsp;
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl;
  let Pstrm := fresh "Pstrm" in pose proof (dp_strm _ _ _ HP) as Pstrm.



Definition KEEP (regs0 R : bvmap 5 word) : Prop :=
  getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\ getr R 25 = getr regs0 25 /\ getr R 26 = getr regs0 26 /\ getr R 27 = getr regs0 27 /\ getr R 23 = getr regs0 23 /\ getr R 24 = getr regs0 24.

Lemma KEEP_via : forall regs0 R R' L,
  KEEP regs0 R -> (forall r : reg, reg_in r L = false -> getr R' r = getr R r) ->
  forallb (fun r : reg => negb (reg_in r L)) [3; 4; 25; 26; 27; 23; 24]%bv = true -> KEEP regs0 R'.
Proof using.
  intros regs0 R R' L (A3 & A4 & A25 & A26 & A27 & A23 & A24) Hfr Hl.
  cbn [forallb] in Hl. rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in Hl. destruct Hl as (X3 & X4 & X25 & X26 & X27 & X23 & X24 & _).
  unfold KEEP. rewrite !Hfr by assumption. repeat split; assumption.
Qed.

Local Ltac keep_via HK Hfr := apply (KEEP_via _ _ _ _ HK Hfr); reflexivity.

Definition REACH (regs0 R : bvmap 5 word) (pc : word) (M M0 : word -> option byte) (e : deflate_state * Z) : Prop :=
  exists R' M', msteps s6_segs (mkst R pc M s6_rom) (mkst R' (0x17a24 : word) M' s6_rom)
    /\ DI M0 M' (fst e) /\ KEEP regs0 R' /\ getr R' 12 = zw (snd e) /\ getr R' 2 = zw SP.

Lemma reach_x30 : forall regs0 R M0 M X,
  DI M0 M X -> HREGS R -> KEEP regs0 R -> REACH regs0 R (0x17a18 : word) M M0 (set_last_flush X (-1), Z_OK).
Proof using HF ra.
  intros regs0 R M0 M X HDI HRG HK.
  destruct (x30_blk _ _ _ _ _ _ _ _ _ HF R M0 M X HDI HRG) as (R' & M' & Hms & HDI' & A2 & A12 & Hfr).
  exists R', M'. split; [exact Hms|]. split; [exact HDI'|]. split; [keep_via HK Hfr|]. split; [exact A12 | exact A2].
Qed.

Lemma reach_xec : forall regs0 R M0 M X,
  DI M0 M X -> getr R 2 = zw SP -> KEEP regs0 R -> REACH regs0 R (0x17ad4 : word) M M0 (X, Z_OK).
Proof using HF ra flush.
  intros regs0 R M0 M X HDI P2 HK.
  destruct (xec_blk _ _ _ _ _ _ _ _ _ HF R M P2) as (R' & Hms & A2 & A12 & Hfr).
  exists R', M. split; [exact Hms|]. split; [exact HDI|]. split; [keep_via HK Hfr|]. split; [exact A12 | exact A2].
Qed.

Lemma reach_xe8 : forall regs0 R M0 M X,
  DI M0 M X -> getr R 2 = zw SP -> KEEP regs0 R -> REACH regs0 R (0x17bd0 : word) M M0 (X, Z_STREAM_END).
Proof using HF ra flush.
  intros regs0 R M0 M X HDI P2 HK.
  destruct (xe8_blk _ _ _ _ _ _ _ _ _ HF R M P2) as (R' & Hms & A2 & A12 & Hfr).
  exists R', M. split; [exact Hms|]. split; [exact HDI|]. split; [keep_via HK Hfr|]. split; [exact A12 | exact A2].
Qed.

Local Ltac reach_step Hms :=
  lazymatch goal with H : REACH _ _ _ _ _ _ |- REACH _ _ _ _ _ _ =>
    let R' := fresh "R" in let M' := fresh "M" in let Hms' := fresh "Hms" in
    destruct H as (R' & M' & Hms' & HD' & HK' & A12' & A2');
    exists R', M'; split; [eapply msteps_trans; [exact Hms | exact Hms'] | split; [exact HD' | split; [exact HK' | split; [exact A12' | exact A2']]]]
  end.



Lemma reach_trailer : forall regs0 R M0 M X,
  dsafe6 SSAFE ds flush -> G7 ds flush ->
  DI M0 M X -> X = X7 ds flush -> HREGS R -> KEEP regs0 R -> getr R 10 = zw strm -> getr R 11 = zw flush ->
  REACH regs0 R (0x17acc : word) M M0 (live_tail flush X).
Proof using TFBITS MEMCPY HF ra.
  intros regs0 R M0 M X HS HG7 HDI EX HRG HK P10 P11. subst X.
  destruct HS as (Hlive & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  destruct (Htl HG7) as (Hw7 & Hp7 & Hp74 & Ha7 & Htr). clear Htl.
  pose proof Hlive as (Hf & _). set (X := X7 ds flush) in *.
  destruct (t1_blk _ _ _ _ _ _ _ _ _ HF R M0 M X HDI HRG P10 P11 Hw7 Hp7 Hp74 Ha7) as (R1 & M1 & Hms1 & HDI1 & HRG1 & A10 & A1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1.
  unfold live_tail. unfold t1_pc, t1_st in Hms1, HDI1.
  destruct (Z.eqb_spec flush 4) as [Ef|Ef].
  - replace (flush =? 4) with true in Hms1, HDI1 by (symmetry; apply Z.eqb_eq; exact Ef). cbn [negb] in Hms1, HDI1 |- *.
    destruct (Z.leb_spec (ds_wrap X) 0) as [Hw|Hw].
    + replace (ds_wrap X <=? 0) with true in Hms1, HDI1 by (symmetry; apply Z.leb_le; exact Hw). cbn [negb] in Hms1, HDI1.
      pose proof (reach_xe8 regs0 R1 M0 M1 X HDI1 (proj1 (proj2 HRG1)) HK1). reach_step Hms1.
    + replace (ds_wrap X <=? 0) with false in Hms1, HDI1 by (symmetry; apply Z.leb_gt; exact Hw). cbn [negb] in Hms1, HDI1.
      destruct (Htr Ef Hw) as (Hfp & Hw8 & Hp8 & Hti). unfold X8 in Hw8, Hp8. fold X in Hw8, Hp8.
      destruct (call_fpn _ _ _ _ _ _ _ _ _ HF MEMCPY TFBITS R1 M0 M1 (trl_st X) (0x17c4c%bv : word) HDI1 HRG1 A10 (A1 Ef Hw)
                  ltac:(apply ret_ok_even; reflexivity) Hfp) as (R2 & M2 & Hms2 & HDI2 & HRG2 & B1 & Hfr2).
      assert (HK2 : KEEP regs0 R2) by keep_via HK1 Hfr2.
      destruct (t2_blk _ _ _ _ _ _ _ _ _ HF R2 M0 M2 (flush_pending (trl_st X)) HDI2 HRG2 Hw8 Hp8) as (R3 & M3 & Hms3 & HDI3 & C2 & C12 & Hfr3).
      exists R3, M3. split.
      { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms3]. }
      split; [exact HDI3|]. split; [keep_via HK2 Hfr3|]. split; [| exact C2].
      rewrite C12. cbn [snd]. unfold Z_STREAM_END, Z_OK. reflexivity.
  - replace (flush =? 4) with false in Hms1, HDI1 by (symmetry; apply Z.eqb_neq; exact Ef). cbn [negb] in Hms1, HDI1 |- *.
    pose proof (reach_xec regs0 R1 M0 M1 X HDI1 (proj1 (proj2 HRG1)) HK1). reach_step Hms1.
Qed.


Definition BLK : deflate_state * Z :=
  match BS ds flush with
  | finish_done => live_tail flush (X6 ds flush)
  | block_done => (if cs_avail_out (ds_strm (X6f ds flush)) =? 0 then set_last_flush (X6f ds flush) (-1) else X6f ds flush, Z_OK)
  | _ => (if cs_avail_out (ds_strm (X6 ds flush)) =? 0 then set_last_flush (X6 ds flush) (-1) else X6 ds flush, Z_OK)
  end.

Lemma avail_out_bst : forall X bs, cs_avail_out (ds_strm (bst_st X bs)) = cs_avail_out (ds_strm X).
Proof using. intros X bs. unfold bst_st. destruct bs; try reflexivity; destruct X; reflexivity. Qed.

Lemma clear_hash_eq : forall X hs0, ds_hash_size X = hs0 ->
  clear_hash X = set_head (set_head X (arr_set (ds_head X) (hs0 - 1) 0)) (arr_fill (ds_head (set_head X (arr_set (ds_head X) (hs0 - 1) 0))) 0 (hs0 - 1) 0).
Proof using. intros X hs0 <-. unfold clear_hash, NIL. destruct X; reflexivity. Qed.

Lemma bd_st_eq : forall X hs0, ds_hash_size (tr_stored_block X None 0 0) = hs0 ->
  bd_st X = Defl6_5b.bd_reset (set_head (set_head (tr_stored_block X None 0 0) (arr_set (ds_head (tr_stored_block X None 0 0)) (hs0 - 1) 0))
                                (arr_fill (ds_head (set_head (tr_stored_block X None 0 0) (arr_set (ds_head (tr_stored_block X None 0 0)) (hs0 - 1) 0))) 0 (hs0 - 1) 0)).
Proof using. intros X hs0 E. unfold bd_st, Defl6_5b.bd_reset. rewrite <- (clear_hash_eq _ _ E). reflexivity. Qed.

Lemma lookahead_sh2 : forall X a b, ds_lookahead (set_head (set_head X a) b) = ds_lookahead X.
Proof using. intros X a b. destruct X; reflexivity. Qed.

Lemma reach_call : forall regs0 R M0 M X,
  dsafe6 SSAFE ds flush -> G4 ds flush ->
  DI M0 M X -> X = X4 ds flush -> blocks_cond (X4 ds flush) flush = true ->
  HREGS R -> KEEP regs0 R -> getr R 11 = zw flush -> rom_clear M0 0x10000 0x293d8 ->
  REACH regs0 R (0x17954 : word) M M0 BLK.
Proof using TSB MEMSET SLOW TFBITS MEMCPY HF ra.
  intros regs0 R M0 M X HS HG4 HDI EX Hbc HRG HK P11 HR0. subst X.
  pose proof HS as HS0.
  destruct HS as (Hlive & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  destruct (Hblk HG4 Hbc) as (HSF & Hao5 & Hbd).
  destruct (call_blk _ _ _ _ _ _ _ _ _ HF R M0 M (X4 ds flush) HDI HRG P11 Hlv4 Hsg4 HR0) as (R1 & Hms1 & HRG1 & A10 & A11 & A2 & A1 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1.
  destruct (call_slow _ _ _ _ _ _ _ _ _ HF SSAFE SLOW R1 M0 M (X4 ds flush) HDI HSF A10 A11 A2 A1) as (R2 & M2 & Hms2 & HDI2 & B10 & B2 & Hfr2).
  assert (HK2 : KEEP regs0 R2) by keep_via HK1 Hfr2.
  assert (HRG2 : HREGS R2).
  { destruct HRG1 as (Q8 & Q2 & Q9 & Q20). unfold Defl6_1.HREGS. rewrite !Hfr2 by reflexivity. repeat split; assumption. }
  change (fst (deflate_slow (X4 ds flush) flush)) with (X5 ds flush) in HDI2.
  change (snd (deflate_slow (X4 ds flush) flush)) with (BS ds flush) in B10.
  unfold BLK.
  assert (A6 : forall bs, cs_avail_out (ds_strm (bst_st (X5 ds flush) bs)) = cs_avail_out (ds_strm (X5 ds flush))) by (intros bs; apply avail_out_bst).
  destruct (BS ds flush) eqn:EBS.
  -
    destruct (bst_blk _ _ _ _ _ _ _ _ _ HF R2 M0 M2 (X5 ds flush) need_more HDI2 HRG2 B10 ltac:(discriminate) Hao5) as (R3 & M3 & Hms3 & HDI3 & HRG3 & Bfd & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    replace (bst_st (X5 ds flush) need_more) with (X6 ds flush) in HDI3 by (unfold X6; rewrite EBS; reflexivity).
    unfold bst_pc in Hms3. replace (cs_avail_out (ds_strm (X6 ds flush))) with (cs_avail_out (ds_strm (X5 ds flush))) by (unfold X6; rewrite EBS; symmetry; apply A6).
    destruct (Z.eqb_spec (cs_avail_out (ds_strm (X5 ds flush))) 0) as [Hz|Hz].
    + replace (cs_avail_out (ds_strm (X5 ds flush)) =? 0) with true in Hms3 by (symmetry; apply Z.eqb_eq; exact Hz).
      pose proof (reach_x30 regs0 R3 M0 M3 (X6 ds flush) HDI3 HRG3 HK3). pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms3)) as Hms123; reach_step Hms123.
    + replace (cs_avail_out (ds_strm (X5 ds flush)) =? 0) with false in Hms3 by (symmetry; apply Z.eqb_neq; exact Hz).
      pose proof (reach_xec regs0 R3 M0 M3 (X6 ds flush) HDI3 (proj1 (proj2 HRG3)) HK3). pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms3)) as Hms123; reach_step Hms123.
  -
    destruct (Hbd eq_refl) as (Hf3 & HBI5 & Hroom5 & Hfp6 & Hao6 & Hlk5 & Hhs5 & Hws5).
    pose proof HDI2 as (_ & _ & (_ & Ehs5 & _)). rewrite Hhs5 in Ehs5. symmetry in Ehs5.
    destruct (bd_a _ _ _ _ _ _ _ _ _ HF R2 M0 M2 (X5 ds flush) HDI2 HRG2 B10 Hf3) as (R3 & Hms3 & HRG3 & C10 & C11 & C12 & C13 & C2 & C1 & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    destruct (call_tsb _ _ _ _ _ _ _ _ _ HF MEMCPY TSB R3 M0 M2 (X5 ds flush) (0x17a64%bv : word) HDI2 ltac:(apply ret_ok_even; reflexivity)
                HBI5 Hroom5 C10 C11 C12 C13 C2 C1) as (R4 & M4 & Hms4 & HDI4 & Hcl4 & Hfr4).
    assert (HK4 : KEEP regs0 R4) by keep_via HK3 Hfr4.
    assert (HRG4 : HREGS R4).
    { destruct HRG3 as (Q8 & Q2 & Q9 & Q20). unfold Defl6_1.HREGS. rewrite !Hfr4 by reflexivity. repeat split; assumption. }
    set (X5' := tr_stored_block (X5 ds flush) None 0 0) in *.
    destruct (bd_b _ _ _ _ _ _ _ _ _ HF R4 M0 M4 X5' HDI4 HRG4 Hf3 Ehs5) as (R5 & M5 & Hms5 & HDI5 & HRG5 & D10 & D11 & D12 & D2 & D18 & D1 & Hfr5).
    assert (HK5 : KEEP regs0 R5) by keep_via HK4 Hfr5.
    destruct (call_ms _ _ _ _ _ _ _ _ _ HF MEMSET R5 M0 M5 _ HDI5 Ehs5 D10 D11 D12 D1) as (R6 & M6 & Hms6 & HDI6 & Hcl6 & Hfr6).
    assert (HK6 : KEEP regs0 R6) by keep_via HK5 Hfr6.
    assert (HRG6 : HREGS R6).
    { destruct HRG5 as (Q8 & Q2 & Q9 & Q20). unfold Defl6_1.HREGS. rewrite !Hfr6 by reflexivity. repeat split; assumption. }
    set (Xc := set_head (set_head X5' (arr_set (ds_head X5') (hs - 1) 0)) (arr_fill (ds_head (set_head X5' (arr_set (ds_head X5') (hs - 1) 0))) 0 (hs - 1) 0)) in *.
    assert (Hlkc : 0 <= ds_lookahead Xc < 2 ^ 31).
    {
      subst Xc X5'. rewrite lookahead_sh2, Defl6_5b.tsb0_lookahead. exact Hlk5. }
    destruct (bd_c _ _ _ _ _ _ _ _ _ HF R6 M0 M6 Xc HDI6 HRG6 ltac:(rewrite (Hfr6 18%bv eq_refl); exact D18) Hlkc) as (R7 & M7 & Hms7 & HDI7 & HRG7 & E10 & E1 & Hfr7).
    assert (HK7 : KEEP regs0 R7) by keep_via HK6 Hfr7.
    assert (EXd : Defl6_5b.bd_reset Xc = X6d ds flush).
    { unfold X6d. subst Xc X5'. symmetry. apply bd_st_eq. rewrite Defl6_5b.tsb0_hash_size. congruence. }
    rewrite EXd in HDI7.
    destruct (call_fpn _ _ _ _ _ _ _ _ _ HF MEMCPY TFBITS R7 M0 M7 (X6d ds flush) (0x17abc%bv : word) HDI7 HRG7 E10 E1
                ltac:(apply ret_ok_even; reflexivity) Hfp6) as (R8 & M8 & Hms8 & HDI8 & HRG8 & F1 & Hfr8).
    assert (HK8 : KEEP regs0 R8) by keep_via HK7 Hfr8.
    change (flush_pending (X6d ds flush)) with (X6f ds flush) in HDI8.
    pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 (msteps_trans _ _ _ _ Hms3 (msteps_trans _ _ _ _ Hms4
                 (msteps_trans _ _ _ _ Hms5 (msteps_trans _ _ _ _ Hms6 (msteps_trans _ _ _ _ Hms7 Hms8))))))) as Hms18.
    destruct (Z.eq_dec (cs_avail_out (ds_strm (X6f ds flush))) 0) as [Hz|Hz].
    + replace (cs_avail_out (ds_strm (X6f ds flush)) =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hz). cbv iota.
      destruct (bd_d0 _ _ _ _ _ _ _ _ _ HF R8 M0 M8 (X6f ds flush) HDI8 HRG8 Hz) as (R9 & Hms9 & HRG9 & G10 & G11 & G12 & G2 & Hfr9).
      assert (HK9 : KEEP regs0 R9) by keep_via HK8 Hfr9.
      destruct (x34_blk _ _ _ _ _ _ _ _ _ HF R9 M0 M8 (X6f ds flush) HDI8 HRG9 G12) as (R10 & M10 & Hms10 & HDI10 & H2 & H12 & Hfr10).
      exists R10, M10. split; [eapply msteps_trans; [exact Hms18 | eapply msteps_trans; [exact Hms9 | exact Hms10]]|].
      split; [exact HDI10|]. split; [keep_via HK9 Hfr10|]. split; [exact H12 | exact H2].
    + replace (cs_avail_out (ds_strm (X6f ds flush)) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). cbv iota.
      destruct (bd_d1 _ _ _ _ _ _ _ _ _ HF R8 M0 M8 (X6f ds flush) HDI8 HRG8 Hao6 Hz) as (R9 & Hms9 & HRG9 & G10 & G11 & G12 & G2 & Hfr9).
      assert (HK9 : KEEP regs0 R9) by keep_via HK8 Hfr9.
      destruct (bd_e _ _ _ _ _ _ _ _ _ HF R9 M8 G2 G11 Hf3) as (R10 & Hms10 & H2 & Hfr10).
      assert (HK10 : KEEP regs0 R10) by keep_via HK9 Hfr10.
      pose proof (reach_xec regs0 R10 M0 M8 (X6f ds flush) HDI8 H2 HK10).
      pose proof (msteps_trans _ _ _ _ Hms18 (msteps_trans _ _ _ _ Hms9 Hms10)) as Hms1_10. reach_step Hms1_10.
  -
    destruct (bst_blk _ _ _ _ _ _ _ _ _ HF R2 M0 M2 (X5 ds flush) finish_started HDI2 HRG2 B10 ltac:(discriminate) Hao5) as (R3 & M3 & Hms3 & HDI3 & HRG3 & Bfd & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    replace (bst_st (X5 ds flush) finish_started) with (X6 ds flush) in HDI3 by (unfold X6; rewrite EBS; reflexivity).
    unfold bst_pc in Hms3. replace (cs_avail_out (ds_strm (X6 ds flush))) with (cs_avail_out (ds_strm (X5 ds flush))) by (unfold X6; rewrite EBS; symmetry; apply A6).
    destruct (Z.eqb_spec (cs_avail_out (ds_strm (X5 ds flush))) 0) as [Hz|Hz].
    + replace (cs_avail_out (ds_strm (X5 ds flush)) =? 0) with true in Hms3 by (symmetry; apply Z.eqb_eq; exact Hz).
      pose proof (reach_x30 regs0 R3 M0 M3 (X6 ds flush) HDI3 HRG3 HK3). pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms3)) as Hms123; reach_step Hms123.
    + replace (cs_avail_out (ds_strm (X5 ds flush)) =? 0) with false in Hms3 by (symmetry; apply Z.eqb_neq; exact Hz).
      pose proof (reach_xec regs0 R3 M0 M3 (X6 ds flush) HDI3 (proj1 (proj2 HRG3)) HK3). pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms3)) as Hms123; reach_step Hms123.
  -
    destruct (bst_blk _ _ _ _ _ _ _ _ _ HF R2 M0 M2 (X5 ds flush) finish_done HDI2 HRG2 B10 ltac:(discriminate) Hao5) as (R3 & M3 & Hms3 & HDI3 & HRG3 & Bfd & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    replace (bst_st (X5 ds flush) finish_done) with (X6 ds flush) in HDI3 by (unfold X6; rewrite EBS; reflexivity).
    unfold bst_pc in Hms3.
    destruct (Bfd eq_refl) as (C11 & C10).
    assert (E7 : X6 ds flush = X7 ds flush) by (unfold X7; rewrite Hbc; cbv beta iota; reflexivity).
    pose proof (reach_trailer regs0 R3 M0 M3 (X6 ds flush) HS0 (conj HG4 (or_intror (conj Hbc EBS))) HDI3 E7 HRG3 HK3 C10 C11).
    pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 Hms3)) as Hms123; reach_step Hms123.
Qed.


Definition AFTER4 : deflate_state * Z :=
  if blocks_cond (X4 ds flush) flush then BLK
  else if flush =? 0 then (X4 ds flush, Z_OK) else live_tail flush (X4 ds flush).

Lemma reach_bc64 : forall regs0 R M0 M X,
  dsafe6 SSAFE ds flush -> G4 ds flush ->
  DI M0 M X -> X = X4 ds flush -> cs_avail_in (ds_strm (X4 ds flush)) = 0 ->
  HREGS R -> KEEP regs0 R -> getr R 10 = zw strm -> getr R 11 = zw flush -> rom_clear M0 0x10000 0x293d8 ->
  REACH regs0 R (0x1794c : word) M M0 AFTER4.
Proof using TSB MEMSET SLOW TFBITS MEMCPY HF ra.
  intros regs0 R M0 M X HS HG4 HDI EX Hai0 HRG HK P10 P11 HR0. subst X.
  pose proof HS as HS0.
  destruct HS as (Hlive & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  pose proof Hlive as (Hf & _).
  destruct (bc64_blk _ _ _ _ _ _ _ _ _ HF R M0 M (X4 ds flush) HDI HRG P10 P11 Hlk4 Hst4) as (R1 & Hms1 & HRG1 & A10 & A11 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1.
  unfold AFTER4. rewrite (blocks_cond_eq flush (X4 ds flush)), Hai0. cbn [Z.eqb negb orb].
  unfold bc64_pc in Hms1.
  destruct (bc64_cond flush (X4 ds flush)) eqn:Ebc.
  - pose proof (reach_call regs0 R1 M0 M (X4 ds flush) HS0 HG4 HDI eq_refl ltac:(rewrite blocks_cond_eq, Hai0; exact Ebc) HRG1 HK1 A11 HR0).
    reach_step Hms1.
  - destruct (Z.eqb_spec flush 0) as [Ef|Ef].
    + pose proof (reach_xec regs0 R1 M0 M (X4 ds flush) HDI (proj1 (proj2 HRG1)) HK1). reach_step Hms1.
    + assert (E7 : X4 ds flush = X7 ds flush) by (unfold X7; rewrite blocks_cond_eq, Hai0, Ebc; cbn [Z.eqb negb orb]; reflexivity).
      assert (Hbcf : blocks_cond (X4 ds flush) flush = false) by (rewrite blocks_cond_eq, Hai0, Ebc; reflexivity).
      pose proof (reach_trailer regs0 R1 M0 M (X4 ds flush) HS0 (conj HG4 (or_introl (conj Hbcf Ef))) HDI E7 HRG1 HK1 A10 A11). reach_step Hms1.
Qed.

Lemma reach_bt : forall regs0 R M0 M X,
  dsafe6 SSAFE ds flush -> G4 ds flush ->
  DI M0 M X -> X = X4 ds flush ->
  HREGS R -> KEEP regs0 R -> getr R 10 = zw strm -> getr R 11 = zw flush -> rom_clear M0 0x10000 0x293d8 ->
  REACH regs0 R (0x17944 : word) M M0 AFTER4.
Proof using TSB MEMSET SLOW TFBITS MEMCPY HF ra.
  intros regs0 R M0 M X HS HG4 HDI EX HRG HK P10 P11 HR0. subst X.
  pose proof HS as HS0.
  destruct HS as (Hlive & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  destruct (bc_blk _ _ _ _ _ _ _ _ _ HF R M0 M (X4 ds flush) HDI HRG P10 Hai4) as (R1 & Hms1 & HRG1 & A10 & A11 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1. rewrite P11 in A11.
  destruct (Z.eqb_spec (cs_avail_in (ds_strm (X4 ds flush))) 0) as [Hz|Hz].
  - pose proof (reach_bc64 regs0 R1 M0 M (X4 ds flush) HS0 HG4 HDI eq_refl Hz HRG1 HK1 A10 A11 HR0). reach_step Hms1.
  - assert (Hbc : blocks_cond (X4 ds flush) flush = true) by (rewrite blocks_cond_eq; rewrite (proj2 (Z.eqb_neq _ _) Hz); reflexivity).
    unfold AFTER4. rewrite Hbc.
    pose proof (reach_call regs0 R1 M0 M (X4 ds flush) HS0 HG4 HDI eq_refl Hbc HRG1 HK1 A11 HR0). reach_step Hms1.
Qed.


Definition AFTER3 : deflate_state * Z :=
  if (ds_status ds =? 42) && negb (ds_pending (X4h ds flush) =? 0) then (set_last_flush (X4h ds flush) (-1), Z_OK)
  else AFTER4.

Lemma reach_dispatch : forall regs0 R M0 M X,
  dsafe6 SSAFE ds flush -> G3 ds flush ->
  DI M0 M X -> X = X3 ds flush ->
  HREGS R -> KEEP regs0 R -> getr R 13 = zw (ds_status ds) -> getr R 10 = zw strm -> getr R 11 = zw flush ->
  (ds_status ds = 42 -> getr R 12 = zw 0) -> rom_clear M0 0x10000 0x293d8 ->
  REACH regs0 R (0x16e20 : word) M M0 AFTER3.
Proof using TSB MEMSET SLOW TFBITS MEMCPY HF ra.
  intros regs0 R M0 M X HS HG3 HDI EX HRG HK P13 P10 P11 P12 HR0. subst X.
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
    destruct (d42_blk _ _ _ _ _ _ _ _ _ HF R M0 M (X3 ds flush) HDI HRG P13 Hw3' Hw3) as (R1 & Hms1 & HRG1 & A10 & A12 & Hfr1).
    assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1. rewrite P10 in A10. rewrite (P12 E42) in A12.
    destruct (hdr_blk _ _ _ _ _ _ _ _ _ HF R1 M0 M (X3 ds flush) HDI HRG1 A10 A12
                ltac:(rewrite EX3, K1p; exact Hp00) ltac:(rewrite EX3, K1wb; exact Hwb) ltac:(rewrite EX3, K1sg; exact Hsg)
                ltac:(rewrite EX3, K1lv; exact Hlv) ltac:(rewrite EX3, K1ss; exact Hss) Hpbl)
      as (R2 & M2 & Hms2 & HDI2 & HRG2 & B10 & B1 & B18 & Hfr2).
    assert (HK2 : KEEP regs0 R2) by keep_via HK1 Hfr2.
    destruct (call_fpn _ _ _ _ _ _ _ _ _ HF MEMCPY TFBITS R2 M0 M2 (hdr_st (X3 ds flush)) (0x16fa0%bv : word) HDI2 HRG2 B10 B1
                ltac:(apply ret_ok_even; reflexivity) Hfp) as (R3 & M3 & Hms3 & HDI3 & HRG3 & C1 & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    change (flush_pending (hdr_st (X3 ds flush))) with (X4h ds flush) in HDI3.
    destruct (hdr2_blk _ _ _ _ _ _ _ _ _ HF R3 M0 M3 (X4h ds flush) HDI3 HRG3 Hp4 Hs4) as (R4 & Hms4 & HRG4 & D10 & Hfr4).
    assert (HK4 : KEEP regs0 R4) by keep_via HK3 Hfr4.
    unfold pend_pc in Hms4.
    pose proof (msteps_trans _ _ _ _ Hms1 (msteps_trans _ _ _ _ Hms2 (msteps_trans _ _ _ _ Hms3 Hms4))) as Hms14.
    destruct (Z.eqb_spec (ds_pending (X4h ds flush)) 0) as [Hq|Hq]; cbn [negb].
    + destruct (D10 Hq) as (D10' & D11').
      assert (E4 : X4h ds flush = X4 ds flush) by (unfold X4; rewrite E42; cbn [Z.eqb Pos.eqb]; reflexivity).
      assert (HG4 : G4 ds flush) by (split; [exact HG3 | intros _; exact Hq]).
      pose proof (reach_bt regs0 R4 M0 M3 (X4h ds flush) HS0 HG4 HDI3 E4 HRG4 HK4 D10' D11' HR0). reach_step Hms14.
    + pose proof (reach_x30 regs0 R4 M0 M3 (X4h ds flush) HDI3 HRG4 HK4). reach_step Hms14.
  -
    destruct (d113_blk _ _ _ _ _ _ _ _ _ HF R M HRG P13) as (R1 & Hms1 & HRG1 & A10 & A11 & Hfr1).
    assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1. rewrite P10 in A10. rewrite P11 in A11.
    assert (E4 : X3 ds flush = X4 ds flush) by (unfold X4; rewrite E113; cbn [Z.eqb Pos.eqb]; reflexivity).
    assert (HG4 : G4 ds flush) by (split; [exact HG3 | intros E; rewrite E113 in E; discriminate E]).
    pose proof (reach_bt regs0 R1 M0 M (X3 ds flush) HS0 HG4 HDI E4 HRG1 HK1 A10 A11 HR0). reach_step Hms1.
  -
    destruct (d666_blk _ _ _ _ _ _ _ _ _ HF R M0 M (X3 ds flush) HDI HRG P13 P10 (Hai3 E666)) as (R1 & Hms1 & HRG1 & A10 & A11 & A12 & Hfr1).
    assert (HK1 : KEEP regs0 R1) by keep_via HK Hfr1. rewrite P11 in A11.
    assert (E4 : X3 ds flush = X4 ds flush) by (unfold X4; rewrite E666; cbn [Z.eqb Pos.eqb]; reflexivity).
    assert (HG4 : G4 ds flush) by (split; [exact HG3 | intros E; rewrite E666 in E; discriminate E]).
    pose proof (reach_bc64 regs0 R1 M0 M (X3 ds flush) HS0 HG4 HDI E4 ltac:(rewrite <- E4; exact (Hai3 E666)) HRG1 HK1 A10 A11 HR0). reach_step Hms1.
Qed.



Definition FRONT : deflate_state * Z :=
  if negb (ds_pending ds =? 0) && (cs_avail_out (ds_strm (X2 ds flush)) =? 0) then (set_last_flush (X2 ds flush) (-1), Z_OK)
  else AFTER3.

Lemma live_core_front : live_core ds flush = FRONT.
Proof using. reflexivity. Qed.

Lemma fp_tail_avail : forall s len, cs_avail_out (ds_strm (DeflM.fp_tail s len)) = cs_avail_out (ds_strm s) - len.
Proof using. intros s len. unfold DeflM.fp_tail. destruct (_ =? 0); destruct s; destruct ds_strm; reflexivity. Qed.

Lemma reach_front : forall regs0 R M1,
  dsafe6 SSAFE ds flush -> DI M1 M1 ds -> rom_clear M1 0x10000 0x293d8 ->
  getr R 8 = zw S -> getr R 2 = zw SP -> getr R 10 = zw strm -> getr R 11 = zw flush -> getr R 13 = zw (ds_status ds) ->
  KEEP regs0 R -> REACH regs0 R (0x16cf0 : word) M1 M1 FRONT.
Proof using HWF HH TSB MEMSET SLOW TFBITS MEMCPY HF ra.
  intros regs0 R M1 HS HDI HR1 P8 P2 P10 P11 P13 HK. pose proof HS as HS0.
  destruct HS as (Hlive & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  clear Hh Hai4 Hlk4 Hst4 Hlv4 Hsg4 Hai3 Hw3 Hw3' Hblk Htl.
  pose proof Hlive as (Hf & Hstat & Hao & Hai & Haif & H666 & H42 & _ & _ & _ & _ & Hpd & Hni & _). clear Hlive.
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & HIN).
  pose proof (wf_lbs _ HWF) as Wlbs.
  assert (Hst31 : 0 <= ds_status ds < 2 ^ 31) by (destruct Hstat as [E|[E|E]]; rewrite E; lia).
  destruct (pro_b _ _ _ _ _ _ _ _ _ HF R M1 M1 ds HDI P8 P2 P10 P11 P13 Hf
              ltac:(intros En4 E666; pose proof (Haif (H666 E666)); lia) Haif Hst31 Hai Hao ltac:(lia) ltac:(lia) ltac:(lia))
    as (R2 & M2 & Hms2 & HDI2 & HRG2 & A12 & A13 & A10 & A11 & A14 & Hfr2).
  assert (HK2 : KEEP regs0 R2) by keep_via HK Hfr2.
  change (set_last_flush ds flush) with (X1 ds flush) in HDI2.
  pose proof (X1_keeps ds flush) as (K1s & K1w & K1p & K1ss & K1wb & K1lv & K1sg & K1st).
  destruct (Z.eqb_spec (ds_pending ds) 0) as [Hq0|Hq0].
  -
    rewrite Hq0 in A12. rewrite <- K1st in A14, Haif, Hai.
    destruct (pend0_blk _ _ _ _ _ _ _ _ _ HF R2 M1 M2 (X1 ds flush) HDI2 HRG2 A12 A11 A14 Haif Hai)
      as (R3 & Hms3 & HRG3 & B12 & B11 & B10 & B13 & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3. rewrite A10 in B10. rewrite A13 in B13.
    assert (EX3 : X1 ds flush = X3 ds flush) by (unfold X3; rewrite (proj2 (Z.eqb_eq _ _) Hq0); reflexivity).
    assert (HG3 : G3 ds flush) by (intros P; exfalso; exact (P Hq0)).
    pose proof (reach_dispatch regs0 R3 M1 M2 (X1 ds flush) HS0 HG3 HDI2 EX3 HRG3 HK3 B13 B10 B11 (fun _ => B12) HR1) as H.
    replace FRONT with AFTER3 by (unfold FRONT; rewrite (proj2 (Z.eqb_eq _ _) Hq0); cbn [negb andb]; reflexivity).
    pose proof (msteps_trans _ _ _ _ Hms2 Hms3) as Hms. reach_step Hms.
  -
    destruct (Hf2 Hq0) as ((HBI & Hp1 & Hp31 & Hpo0 & Hpo1 & Hav1 & Htot1) & Hav2 & Hst2 & Est2 & Eai2).
    rewrite <- K1p in A12.
    destruct (pendnz_blk _ _ _ _ _ _ _ _ _ HF R2 M1 M2 (X1 ds flush) HDI2 HRG2 A12 ltac:(lia)) as (R3 & Hms3 & HRG3 & B10 & B1 & Hfr3).
    assert (HK3 : KEEP regs0 R3) by keep_via HK2 Hfr3.
    destruct (call_bits _ _ _ _ _ _ _ _ _ _ _ TFBITS HH R3 M1 M2 (X1 ds flush) (0x16d70%bv : word) HDI2
                ltac:(apply ret_ok_even; reflexivity) HBI ltac:(lia) B10 B1) as (R4 & M4 & Hms4 & HDI4 & Hfr4 & Hag4).
    assert (HRG4 : HREGS R4) by hregs_via HRG3 Hfr4.
    assert (HK4 : KEEP regs0 R4) by keep_via HK3 Hfr4.
    unfold X2 in Hav2, Hst2, Est2, Eai2. rewrite DeflM.flush_pending_eq in Hav2, Hst2, Est2, Eai2. cbv zeta in Hav2, Hst2, Est2, Eai2.
    set (X1' := tr_flush_bits (X1 ds flush)) in *.
    destruct (fpc_blk _ _ _ _ _ _ _ _ _ HF R4 M1 M4 X1' HDI4 HRG4 ltac:(lia) ltac:(lia) ltac:(lia)) as (R5 & Hms5 & HRG5 & C10 & C11z & Cnz & Hfr5).
    assert (HK5 : KEEP regs0 R5) by keep_via HK4 Hfr5.
    unfold fpa_pc in Hms5.
    pose proof (DeflSlow6_6.fp_len_eq X1' ltac:(lia) ltac:(lia)) as (_ & Hfl1 & Hfl2).
    destruct (Z.eq_dec (DeflM.fp_len X1') 0) as [Efl|Efl].
    +
      rewrite (proj2 (Z.eqb_eq _ _) Efl) in C10, Hav2, Hst2, Est2, Eai2, Hms5. cbv beta iota in C10, Hav2, Hst2, Est2, Eai2, Hms5.
      destruct (fpe_blk _ _ _ _ _ _ _ _ _ HF R5 M1 M4 X1' HDI4 HRG5 (C11z Efl) C10 ltac:(lia) ltac:(lia)) as (R6 & Hms6 & HRG6 & D10 & Dnz & Hfr6).
      assert (HK6 : KEEP regs0 R6) by keep_via HK5 Hfr6.
      unfold avail_pc in Hms6.
      pose proof (msteps_trans _ _ _ _ Hms2 (msteps_trans _ _ _ _ Hms3 (msteps_trans _ _ _ _ Hms4 (msteps_trans _ _ _ _ Hms5 Hms6)))) as Hms.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm X1')) 0) as [Hz|Hnz].
      * pose proof (reach_x30 regs0 R6 M1 M4 X1' HDI4 HRG6 HK6) as H.
        replace FRONT with (set_last_flush X1' (-1), Z_OK)
          by (unfold FRONT, X2; rewrite (proj2 (Z.eqb_neq _ _) Hq0); rewrite DeflM.flush_pending_eq; cbv zeta; fold X1';
              rewrite (proj2 (Z.eqb_eq _ _) Efl); cbv beta iota; rewrite (proj2 (Z.eqb_eq _ _) Hz); cbn [negb andb]; reflexivity).
        reach_step Hms.
      * destruct (Dnz Hnz) as (D13 & D11). rewrite Est2 in D13.
        assert (EX3 : X1' = X3 ds flush)
          by (unfold X3, X2; rewrite (proj2 (Z.eqb_neq _ _) Hq0); cbv beta iota; rewrite DeflM.flush_pending_eq; cbv zeta; fold X1';
              rewrite (proj2 (Z.eqb_eq _ _) Efl); cbv beta iota; reflexivity).
        assert (HG3 : G3 ds flush) by (intros _; rewrite <- EX3; exact Hnz).
        pose proof (reach_dispatch regs0 R6 M1 M4 X1' HS0 HG3 HDI4 EX3 HRG6 HK6 D13 D10 D11
                      ltac:(intros E42; exfalso; destruct (H42 E42) as (_ & P00 & _); exact (Hq0 P00)) HR1) as H.
        replace FRONT with AFTER3
          by (unfold FRONT, X2; rewrite (proj2 (Z.eqb_neq _ _) Hq0); rewrite DeflM.flush_pending_eq; cbv zeta; fold X1';
              rewrite (proj2 (Z.eqb_eq _ _) Efl); cbv beta iota; rewrite (proj2 (Z.eqb_neq _ _) Hnz); cbn [negb andb]; reflexivity).
        reach_step Hms.
    +
      rewrite (proj2 (Z.eqb_neq _ _) Efl) in C10, Hav2, Hst2, Est2, Eai2, Hms5. cbv beta iota in C10, Hav2, Hst2, Est2, Eai2, Hms5.
      destruct (Cnz Efl) as (C11 & C12 & C18 & C1).
      remember (Z.to_nat (DeflM.fp_len X1')) as n eqn:En. assert (EL : DeflM.fp_len X1' = Z.of_nat n) by lia.
      rewrite EL in C12, C18, Hav2, Hst2, Est2, Eai2, Hfl1, Hfl2. clear En.
      destruct (call_mc _ _ _ _ _ _ _ _ _ _ _ MEMCPY HH R5 M1 M4 X1' n (0x16d9c%bv : word) HDI4 ltac:(apply ret_ok_even; reflexivity)
                  ltac:(lia) ltac:(lia) ltac:(lia) C1 C10 C11 C12) as (R6 & Hms6 & E10 & Hfr6).
      set (M5 := wbytes M4 _ _) in Hms6.
      assert (HDI5 : DI M5 M5 X1').
      { subst M5. apply (DI_out_self _ _ _ _ _ _ _ _ _ _ _ HH M1 M4 X1' _ HDI4). rewrite fbytes_length. lia. }
      assert (HRG6 : HREGS R6) by hregs_via HRG5 Hfr6.
      assert (HK6 : KEEP regs0 R6) by keep_via HK5 Hfr6.
      destruct (fpd_blk _ _ _ _ _ _ _ _ _ HF R6 M5 M5 X1' (Z.of_nat n) HDI5 HRG6
                  ltac:(rewrite (Hfr6 18%bv eq_refl); exact C18)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (R7 & Hms7 & HRG7 & F11 & F10 & Hfr7).
      assert (HK7 : KEEP regs0 R7) by keep_via HK6 Hfr7.
      assert (HDI7 : DI M1 (Defl6_2.fp_tower S p zp M5 X1' (Z.of_nat n)) (DeflM.fp_tail X1' (Z.of_nat n))).
      { pose proof (fp_finish _ _ _ _ _ _ _ _ _ _ _ HH M1 M4 X1' n (cs_total_out (ds_strm X1') + Z.of_nat n) HDI4
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)) as HD6.
        cbv zeta in HD6. subst M5. unfold Defl6_2.fp_tower. cbv zeta. exact HD6. }
      set (X2' := DeflM.fp_tail X1' (Z.of_nat n)) in *.
      assert (F11' : getr R7 11 = zw (cs_avail_out (ds_strm X2'))) by (rewrite F11; subst X2'; rewrite fp_tail_avail; reflexivity).
      destruct (fpe_blk _ _ _ _ _ _ _ _ _ HF R7 M1 _ X2' HDI7 HRG7 F11' F10 Hav2 Hst2) as (R8 & Hms8 & HRG8 & G10 & Gnz & Hfr8).
      assert (HK8 : KEEP regs0 R8) by keep_via HK7 Hfr8.
      unfold avail_pc in Hms8.
      pose proof (msteps_trans _ _ _ _ Hms2 (msteps_trans _ _ _ _ Hms3 (msteps_trans _ _ _ _ Hms4 (msteps_trans _ _ _ _ Hms5
                   (msteps_trans _ _ _ _ Hms6 (msteps_trans _ _ _ _ Hms7 Hms8)))))) as Hms.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm X2')) 0) as [Hz|Hnz].
      * pose proof (reach_x30 regs0 R8 M1 _ X2' HDI7 HRG8 HK8) as H.
        replace FRONT with (set_last_flush X2' (-1), Z_OK)
          by (unfold FRONT, X2; rewrite (proj2 (Z.eqb_neq _ _) Hq0); rewrite DeflM.flush_pending_eq; cbv zeta; fold X1';
              rewrite (proj2 (Z.eqb_neq _ _) Efl); cbv beta iota; rewrite EL; fold X2';
              rewrite (proj2 (Z.eqb_eq _ _) Hz); cbn [negb andb]; reflexivity).
        reach_step Hms.
      * destruct (Gnz Hnz) as (D13 & D11). rewrite Est2 in D13.
        assert (EX3 : X2' = X3 ds flush)
          by (unfold X3, X2; rewrite (proj2 (Z.eqb_neq _ _) Hq0); cbv beta iota; rewrite DeflM.flush_pending_eq; cbv zeta; fold X1';
              rewrite (proj2 (Z.eqb_neq _ _) Efl); cbv beta iota; rewrite EL; reflexivity).
        assert (HG3 : G3 ds flush) by (intros _; rewrite <- EX3; exact Hnz).
        pose proof (reach_dispatch regs0 R8 M1 _ X2' HS0 HG3 HDI7 EX3 HRG8 HK8 D13 G10 D11
                      ltac:(intros E42; exfalso; destruct (H42 E42) as (_ & P00 & _); exact (Hq0 P00)) HR1) as H.
        replace FRONT with AFTER3
          by (unfold FRONT, X2; rewrite (proj2 (Z.eqb_neq _ _) Hq0); rewrite DeflM.flush_pending_eq; cbv zeta; fold X1';
              rewrite (proj2 (Z.eqb_neq _ _) Efl); cbv beta iota; rewrite EL; fold X2';
              rewrite (proj2 (Z.eqb_neq _ _) Hnz); cbn [negb andb]; reflexivity).
        reach_step Hms.
Qed.


Lemma DI_fin : forall m1 m X, DI m1 m X -> agree_out [(sp - 64, 64)] mem m1 ->
  ZR6 m S p zp X /\ agree_out (ZRFo DEFL_K6 S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm X))))) mem m /\ rod6 m /\ ROM m
  /\ (forall x, mem x <> None -> m x <> None)
  /\ lzk ds X.
Proof using.
  intros m1 m X (HB & HR & HS3) Hag1.
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  assert (HagO : agree_out (ZRFo DEFL_K6 S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm X))))) mem m).
  { eapply agree_out_trans.
    - eapply agree_out_weaken; [exact Hag1|]. unfold ZRFo, DEFL_K6. cbn [in_franges]. intros x Hx. lia.
    - eapply agree_out_weaken; [exact HAG|]. unfold DeflKit6.GDo, ZRFo, DEFL_K6, FR64, ds6_SIZE, zsl_SIZE. cbn [in_franges]. intros x Hx. lia. }
  split; [| split; [exact HagO | split; [exact HRC | split; [exact HRD | split; [exact HGR0|]]]]].
  - unfold ZR6, ds6_windowA, ds6_prevA, ds6_headA, ds6_arrays. repeat (split; [assumption|]). exact Zo.
  - destruct HS3 as (E1 & E2 & E3). destruct HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
    pose proof HB as (_ & _ & _ & _ & Epbl & _). unfold lzk.
    repeat (split; [first [assumption | lia]|]). exact Hol.
Qed.

Lemma bvneq' : forall (r k : reg) (z : Z), (bv_unsigned r =? bv_unsigned k) = false -> bv_unsigned k = z -> bv_unsigned r <> z.
Proof using. intros r k z H <-. apply Z.eqb_neq. exact H. Qed.

Local Ltac bvlits :=
  repeat match goal with H : (_ || _)%bool = false |- _ => apply Bool.orb_false_elim in H; destruct H end;
  repeat match goal with H : (bv_unsigned ?r =? bv_unsigned ?k) = false |- _ =>
    let z := eval vm_compute in (bv_unsigned k) in pose proof (bvneq' r k z H eq_refl); clear H end.

Lemma reg_frame_fin : forall (R4 R3 regs : bvmap 5 word),
  getr R4 2 = getr regs 2 ->
  (forall r : reg, reg_in r [1; 8; 9; 18; 19; 20; 21; 22]%bv = true -> getr R4 r = getr regs r) ->
  (forall r : reg, reg_in r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22]%bv = false -> getr R4 r = getr R3 r) ->
  KEEP regs R3 ->
  forall r : reg, reg_in r LZ_CLOB = false -> getr R4 r = getr regs r.
Proof using.
  intros R4 R3 regs H2 Hrest Hfr (K3 & K4 & K25 & K26 & K27 & K23 & K24) r Hr.
  pose proof (u5_range r) as Ur.
  destruct (reg_in r [1; 8; 9; 18; 19; 20; 21; 22]%bv) eqn:E1; [exact (Hrest r E1)|].
  destruct (bv_eqb r 2) eqn:E2.
  { assert (Er : r = 2%bv) by (apply bv_eq; unfold bv_eqb in E2; apply Z.eqb_eq in E2; exact E2). subst r. exact H2. }
  destruct (bv_eqb r 10) eqn:E10.
  { exfalso. assert (Er : r = 10%bv) by (apply bv_eq; unfold bv_eqb in E10; apply Z.eqb_eq in E10; exact E10). subst r. discriminate Hr. }
  assert (E3 : reg_in r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22]%bv = false).
  { cbn [reg_in] in E1 |- *. rewrite E2, E10. apply Bool.orb_false_elim in E1 as [E1a E1b]. rewrite E1a. cbn [orb]. exact E1b. }
  rewrite (Hfr r E3).
  destruct (bv_eqb r 0) eqn:E0.
  { assert (Er : r = 0%bv) by (apply bv_eq; unfold bv_eqb in E0; apply Z.eqb_eq in E0; exact E0). subst r. reflexivity. }
  destruct (bv_eqb r 3) eqn:E3'.
  { assert (Er : r = 3%bv) by (apply bv_eq; unfold bv_eqb in E3'; apply Z.eqb_eq in E3'; exact E3'). subst r. exact K3. }
  destruct (bv_eqb r 4) eqn:E4'.
  { assert (Er : r = 4%bv) by (apply bv_eq; unfold bv_eqb in E4'; apply Z.eqb_eq in E4'; exact E4'). subst r. exact K4. }
  destruct (bv_eqb r 25) eqn:E25.
  { assert (Er : r = 25%bv) by (apply bv_eq; unfold bv_eqb in E25; apply Z.eqb_eq in E25; exact E25). subst r. exact K25. }
  destruct (bv_eqb r 26) eqn:E26.
  { assert (Er : r = 26%bv) by (apply bv_eq; unfold bv_eqb in E26; apply Z.eqb_eq in E26; exact E26). subst r. exact K26. }
  destruct (bv_eqb r 23) eqn:E23.
  { assert (Er : r = 23%bv) by (apply bv_eq; unfold bv_eqb in E23; apply Z.eqb_eq in E23; exact E23). subst r. exact K23. }
  destruct (bv_eqb r 24) eqn:E24.
  { assert (Er : r = 24%bv) by (apply bv_eq; unfold bv_eqb in E24; apply Z.eqb_eq in E24; exact E24). subst r. exact K24. }
  destruct (bv_eqb r 27) eqn:E27.
  { assert (Er : r = 27%bv) by (apply bv_eq; unfold bv_eqb in E27; apply Z.eqb_eq in E27; exact E27). subst r. exact K27. }
  exfalso. unfold LZ_CLOB in Hr. cbn [reg_in] in Hr, E1, E3. unfold bv_eqb in *.
  bvlits. lia.
Qed.


Theorem deflate_run : forall regs,
  dsafe6 SSAFE ds flush ->
  getr regs 10 = zw strm -> getr regs 11 = zw flush -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m',
    msteps s6_segs (mkst regs (0x16c80 : word) mem s6_rom) (mkst R ra m' s6_rom)
    /\ ZR6 m' S p zp (fst (deflate_core ds flush))
    /\ getr R 10 = zw (snd (deflate_core ds flush))
    /\ getr R 2 = zw sp
    /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R r = getr regs r)
    /\ agree_out (ZRFo DEFL_K6 S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm (fst (deflate_core ds flush))))))) mem m'
    /\ rod6 m' /\ ROM m'
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ lzk ds (fst (deflate_core ds flush)).
Proof using HWF HH TSB MEMSET SLOW TFBITS MEMCPY HF.
  intros regs HS P10 P11 P2 P1.
  rewrite (core_live SSAFE ds flush HS), live_core_front.
  pose proof HS as (Hlive & _). pose proof Hlive as (_ & Hstat & _).
  destruct (pro_a _ _ _ _ _ _ _ _ _ HF regs Hstat P10 P11 P2 P1)
    as (R1 & M1 & Hms1 & HDI1 & HFRM & HR1 & A8 & A2 & A10 & A11 & A13 & A12 & A1 & Hfr1 & Hag1).
  assert (HK1 : KEEP regs R1) by (unfold KEEP; repeat split; apply Hfr1; reflexivity).
  destruct (reach_front regs R1 M1 HS HDI1 HR1 A8 A2 A10 A11 A13 HK1) as (R' & M' & Hms & HDI' & HK' & B12 & B2).
  revert HDI' B12. generalize FRONT. intros [X code] HDI' B12. cbn [fst snd] in HDI', B12 |- *.
  destruct (epi_blk _ _ _ _ _ _ _ _ _ HF R' regs M1 M' X HDI' (FRM_keep _ _ _ _ _ _ _ _ _ HF M1 M' X regs HDI' HFRM) P1 B2)
    as (R9 & Hms9 & C2 & C10 & Hrest & Hfr9).
  destruct (DI_fin M1 M' X HDI' Hag1) as (HZ & Hag & Hrc & Hrd & Hgr & Hk).
  exists R9, M'. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms | exact Hms9]|].
  split; [exact HZ|]. split; [rewrite C10; exact B12|]. split; [exact C2|].
  split; [apply (reg_frame_fin R9 R' regs); [rewrite C2, P2; reflexivity | exact Hrest | exact Hfr9 | exact HK']|].
  split; [exact Hag|]. split; [exact Hrc|]. split; [exact Hrd|]. split; [exact Hgr | exact Hk].
Qed.

End Walk.


Theorem deflate_run6_ok :
  forall (ROM : (word -> option byte) -> Prop) (SSAFE : deflate_state -> Z -> Prop),
    memcpy_run6 -> tr_flush_bits_run6 -> deflate_slow_run6 ROM SSAFE -> rom_local6 ROM ->
    memset_run6 -> tr_stored_block_run6 ->
    deflate_run6 ROM (fun ds f => DWF ds /\ dsafe6 SSAFE ds f).
Proof using.
  intros ROM SSAFE MEMCPY TFBITS SLOW HRL MEMSET TSB.
  unfold deflate_run6.
  intros mem S p zp ds flush ra sp regs HL HROMC HP Hret HZR HROM [HWF HSAFE] P10 P11 P2 P1.
  assert (Hfl : 0 <= flush <= 5) by (destruct HSAFE as ((Hf & _) & _); lia).
  assert (HK6 : 0 <= FR64 <= DEFL_K6) by (unfold DEFL_K6, FR64; lia).
  destruct (deflate_run ROM mem S p zp ds flush ra sp
              {| dfh_K := {| dsh_L := HL; dsh_ret := Hret; dsh_zr := HZR; dsh_flush := Hfl; dsh_wf := HWF; dsh_rom := HROM;
                            dsh_roml := HRL; dsh_K := HK6 |};
                 dfh_P := HP; dfh_img := HROMC |}
              MEMCPY TFBITS SSAFE SLOW MEMSET TSB regs HSAFE P10 P11 P2 P1)
    as (R & m' & Hms & HZ & A10 & A2 & Hfr & Hag & Hrc & Hrd & Hgr & Hk).
  exists R, m'. unfold A6_DEFLATE. replace (zw 0x16c80) with (0x16c80%bv : word) by (apply bv_eq; reflexivity).
  split; [exact Hms|]. split; [exact HZ|]. split; [exact A10|]. split; [exact A2|]. split; [exact Hfr|].
  split; [exact Hag|]. split; [exact Hrc|]. split; [exact Hrd|]. split; [exact Hgr | exact Hk].
Qed.
End FXG.

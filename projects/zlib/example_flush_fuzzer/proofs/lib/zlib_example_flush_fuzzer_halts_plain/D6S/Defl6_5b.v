(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout MemFill FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  ZIface DeflateState Trees TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel
  RefFlushPend1 RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3 RefDeflateHdr5 RefDeflateTrl1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 Callee6 CalleeKits6 TreesRod6 TreesApi6 DeflBlkApi6
  DeflSlow6_1 DeflSlow6_2 DeflSlow6_4 DeflSlow6_6 DeflKit6 Defl6Api Defl6_1 Defl6_4 Defl6_5 TrStored6 Memset6_run.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

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



Definition dfC5b : cfg :=
  CFG [] [] [EVar 1%nat; EVar 36%nat]
      [0x16cf0; 0x16d64; 0x16d70; 0x16d9c; 0x16df0; 0x16e20; 0x16e4c; 0x16fa0;
       0x17944; 0x1794c; 0x17954; 0x179c4; 0x17a18; 0x17a1c; 0x17a24; 0x17acc; 0x17ad4; 0x17bd0; 0x17c4c;
       0x17c80; 0x17ca4; 0x17cc8; 0x17d10;
       0x1ad94; 0x27800; 0x19558; 0x1abbc; 0x27c04] [].
Local Ltac run5b pins fuel dirs rds vbx pvx :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vb := eval vm_compute in (dVB ++ vbx) in
  let rdv := eval vm_compute in rds in
  let pv := constr:(S :: SP :: flush :: strm :: pvx) in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs dfC5b fuel dirs rdv pinsv vb NoRegions pv NoVals F0 F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.


Lemma bd_a : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw (bs_code block_done) -> flush = 3 ->
  exists R,
    msteps s6_segs (mkst regs (0x179c4 : word) m s6_rom) (mkst R (0x1abbc : word) m s6_rom)
    /\ HREGS R /\ getr R 10 = zw S /\ getr R 11 = zw 0 /\ getr R 12 = zw 0 /\ getr R 13 = zw 0
    /\ getr R 2 = zw SP /\ getr R 1 = (0x17a64%bv : word)
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG P10 Hf3. open_di HDI. open_hregs HRG. cbn [bs_code] in P10.
  rewrite Hf3 in P20.
  run5b [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, ELit 3); (10, ELit 1)] 20%nat
    [true; false; false; false; true] NoReads NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Definition Ftsb : franges := [(S, ds6_SIZE); (PB, PBL); (SP - 32, 32)].

Lemma tsb0_window : forall s, ds_window (tr_stored_block s None 0 0) = ds_window s.
Proof using. intros. exact (k_tr_stored_block ds_window true true keeps_window eq_refl s None 0 0). Qed.
Lemma tsb0_prev : forall s, ds_prev (tr_stored_block s None 0 0) = ds_prev s.
Proof using. intros. exact (k_tr_stored_block ds_prev true true DeflSlow6_1.keeps_prev eq_refl s None 0 0). Qed.
Lemma tsb0_head : forall s, ds_head (tr_stored_block s None 0 0) = ds_head s.
Proof using. intros. exact (k_tr_stored_block ds_head true true DeflSlow6_1.keeps_head eq_refl s None 0 0). Qed.
Lemma tsb0_strm : forall s, ds_strm (tr_stored_block s None 0 0) = ds_strm s.
Proof using. intros. exact (k_tr_stored_block ds_strm true true keeps_strm eq_refl s None 0 0). Qed.
Lemma tsb0_sizes : forall s, DeflSlow6_1.ds_sizes (tr_stored_block s None 0 0) = DeflSlow6_1.ds_sizes s.
Proof using. intros. exact (k_tr_stored_block DeflSlow6_1.ds_sizes true true DeflSlow6_1.keeps_sizes eq_refl s None 0 0). Qed.
Lemma keeps_lookahead : keeps ds_lookahead true true.
Proof using. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.
Lemma tsb0_lookahead : forall s, ds_lookahead (tr_stored_block s None 0 0) = ds_lookahead s.
Proof using. intros. exact (k_tr_stored_block ds_lookahead true true keeps_lookahead eq_refl s None 0 0). Qed.
Lemma tsb0_hash_size : forall s, ds_hash_size (tr_stored_block s None 0 0) = ds_hash_size s.
Proof using. intros. exact (k_tr_stored_block ds_hash_size true true DeflSlow6_1.keeps_hash_size eq_refl s None 0 0). Qed.

Lemma call_tsb : forall regs m1 m X (ra' : word),
  DI m1 m X -> ret_ok ra' -> BINV PBL X -> ds_pending (tr_stored_block X None 0 0) <= PBL ->
  getr regs 10 = zw S -> getr regs 11 = zw 0 -> getr regs 12 = zw 0 -> getr regs 13 = zw 0 ->
  getr regs 2 = zw SP -> getr regs 1 = ra' ->
  exists R m',
    msteps s6_segs (mkst regs (0x1abbc : word) m s6_rom) (mkst R ra' m' s6_rom)
    /\ DI m1 m' (tr_stored_block X None 0 0)
    /\ (forall a w v, cell s6_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6_segs m' a w v)
    /\ (forall r : reg, reg_in r SB_CLOB = false -> getr R r = getr regs r).
Proof using HWF HH TSB MEMCPY HF ra flush.
  intros regs m1 m X ra' HDI Hret HBI Hroom P10 P11 P12 P13 P2 P1.
  pose proof HDI as (HB & HR & (Ews & Ehs & Elbs)).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN). unfold DEFL_K6 in Hsp.
  unfold mapped, DEFL_K6 in MF.
  pose proof (BRH_d _ _ _ _ _ _ _ _ _ _ _ HH) as (BA1 & BA2 & BA3 & _). pose proof (wf_lbs _ HWF) as Wlbs.
  apartF 0%nat 1%nat A01. apartF 0%nat 5%nat A05. apartF 1%nat 5%nat A15.
  assert (HBRH : BRH Ftsb S p PBL).
  { unfold BRH, Ftsb, ds6_SIZE, dsl_SIZE. split; [lia|]. split; [lia|]. split; [lia|].
    split; [intros x Hx; cbn; lia|]. split; [intros x Hx; cbn; lia|]. split; [intros x Hx; cbn; lia|]. intros x Hx; cbn; lia. }
  assert (Hcf : call_frame Ftsb m S PB PBL SP 32).
  { unfold call_frame, Ftsb, ds6_SIZE, dsl_SIZE. split; [lia|]. split; [intros x Hx; cbn; lia|].
    split; [intros x Hx; apply MF; lia|]. split; lia. }
  assert (Hsrc : tsb_src Ftsb m p X None 0 0) by (intros Hnz; exfalso; exact (Hnz eq_refl)).
  (* 1.4: tr_stored_block_run6 also takes the frame's cover of bi_used (S + 5944, 4) *)
  destruct (TSB Ftsb m m S p PBL X ra' regs SP None 0 0 0 MEMCPY HBRH
              ltac:(unfold Ftsb; apply sub_franges_here; unfold ds6_SIZE, dsl_SIZE; lia) Hret (BR_self s6_segs 168672 168704 168736 _ Ftsb _ _ _ _ _ _ HB)
              HBI Hroom ltac:(lia) ltac:(lia) Hcf Hsrc P10 P11 P12 P13 P2 P1)
    as (R & m' & Hms & HB' & Hfr). unfold A6_TR_STORED_BLOCK in Hms. symex_pc_lit_in Hms.
  destruct (BR_back s6_segs 168672 168704 168736 (DeflKit6.Fd S p zp ds sp DEFL_K6) Ftsb mem S p PBL m m' X _ HB HB') as [HB2 Hag].
  { unfold Ftsb, ds6_SIZE, dsl_SIZE. intros x [Hx|[Hx|[Hx|[]]]]; cbn in Hx; apply in_Fd; unfold DEFL_K6; lia. }
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & _ & _ & _ & HGR').
  exists R, m'. split; [exact Hms|].
  assert (HFM : forall x : word, in_franges Ftsb (bv_unsigned x) -> m x <> None).
  { unfold Ftsb, ds6_SIZE, dsl_SIZE. intros x [Hx|[Hx|[Hx|[]]]]; cbn in Hx; [apply MS; exact Hx | apply MP; exact Hx | apply MF; lia]. }
  split.
  { split; [exact HB2|].
    pose proof (tsb0_sizes X) as Esz. unfold DeflSlow6_1.ds_sizes in Esz.
    assert (Esz1 : ds_w_size (tr_stored_block X None 0 0) = ds_w_size X) by congruence.
    assert (Esz2 : ds_hash_size (tr_stored_block X None 0 0) = ds_hash_size X) by congruence.
    assert (Esz3 : ds_lit_bufsize (tr_stored_block X None 0 0) = ds_lit_bufsize X) by congruence.
    split; [| rewrite Esz1, Esz2, Esz3; exact (conj Ews (conj Ehs Elbs))].
    rewrite tsb0_window, tsb0_prev, tsb0_head, tsb0_strm.
    eapply (RZ_agree _ _ _ _ _ _ _ _ _ _ _ HH m1 m m' _ _ _ _ Ftsb HR Hag); try exact HGR'; try exact HFM.
    - unfold Ftsb, ds6_SIZE, dsl_SIZE. intros x [Hx|[Hx|[Hx|[]]]]; cbn in Hx; apply in_GDo; unfold DEFL_K6, FR64; lia.
    - apartF 1%nat 2%nat A12. apartF 2%nat 5%nat A25. apartF 0%nat 2%nat A02. unfold Ftsb, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; lia.
    - apartF 1%nat 3%nat A13. apartF 3%nat 5%nat A35. apartF 0%nat 3%nat A03. unfold Ftsb, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; lia.
    - apartF 1%nat 4%nat A14. apartF 4%nat 5%nat A45. apartF 0%nat 4%nat A04. unfold Ftsb, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; lia.
    - apartF 1%nat 6%nat A16. apartF 5%nat 6%nat A56. apartF 0%nat 6%nat A06. unfold Ftsb, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; lia.
    - apartF 1%nat 8%nat A18. apartF 5%nat 8%nat A58. apartF 0%nat 8%nat A08. unfold Ftsb, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; lia.
    - apartF 1%nat 7%nat A17. apartF 5%nat 7%nat A57. apartF 0%nat 7%nat A07. unfold Ftsb, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; lia. }
  split; [| exact Hfr].
  intros a w v Hc Ha1 Ha2.
  apply (cell_agree_out s6_segs Ftsb m m' a w v Hag); [| lia | lia | exact Hc].
  unfold Ftsb, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; lia.
Qed.


Local Ltac other9' A :=
  apply cells_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia); exact A.

Lemma BR_st_gap : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 5960)) (Z_to_le_bytes 4 v)) s.
Proof using HH.
  intros m s v HB. pose proof HB as (A & B & C & D & E & G & H & I & J).
  pose proof (DeflKit6.BRH_d _ _ _ _ _ _ _ _ _ _ _ HH) as (HS & HPB & Hdisj & _).
  unfold BitsLib.BR, ds6_SIZE, dsl_SIZE in *.
  split; [eapply (DSLayout.fields_write_gap s6_segs m S dsl_layout _ 5968 5960 (Z_to_le_bytes 4 v) A);
          [exact dsl_layout_within | rewrite length_Z_to_le_bytes; vm_compute; reflexivity | lia | lia | lia | rewrite length_Z_to_le_bytes; lia]|].
  split; [unfold ds6_arrays in *; apply arrays_write_gap; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; try (cbn; lia); exact B|].
  split; [exact C|].
  split; [dsred; other9' D|].
  split; [dsred; exact E|].
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | intros x Hx; apply (DeflKit6.HFS_d S p zp ds sp DEFL_K6); cbn in Hx; unfold ds6_SIZE, dsl_SIZE; lia]|].
  split; [apply mapped_wbytes; exact H|]. split; [apply mapped_wbytes; exact I|].
  intros x Hx; apply wbytes_grows; exact (J x Hx).
Qed.

Lemma DI_st_gap : forall m1 m X v, DI m1 m X -> DI m1 (wbytes m (zw (S + 5960)) (Z_to_le_bytes 4 v)) X.
Proof using HH.
  intros m1 m X v HDI. destruct HDI as (HB & HR & HS3). split; [apply BR_st_gap; exact HB|].
  split; [dsred; eapply (DeflKit6.RZ_st_S _ _ _ _ _ _ _ _ _ _ _ HH); [exact HR | exact HB | lia | rewrite length_Z_to_le_bytes; lia]|]. dsred; exact HS3.
Qed.

Lemma bd_b : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> flush = 3 -> hs = 32768 ->
  exists R M,
    msteps s6_segs (mkst regs (0x17a64 : word) m s6_rom) (mkst R (0x27c04 : word) M s6_rom)
    /\ DI m1 M (set_head X (arr_set (ds_head X) (hs - 1) 0))
    /\ HREGS R /\ getr R 10 = zw HD /\ getr R 11 = zw 0 /\ getr R 12 = zw (2 * (hs - 1)) /\ getr R 2 = zw SP /\ getr R 18 = zw (S + 5932)
    /\ getr R 1 = (0x17a9c%bv : word)
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 18]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG Hf3 Hhs. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6_hash_size C132. rewrite Ehs, Hhs in C132. sc_cell Hsc ds6_head C120.
  rewrite Hf3 in P20.
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 4%nat ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T.
  pose proof (fun x Hx => HGR x (T x Hx)) as MHm; cbv beta in MHm; clear T. rewrite Hhs in MHm, HHD.
  run5b [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, ELit 3)] 14%nat
    [false] [RVal (EVar 36%nat); RVal (ELit 32768)] [(36%nat, 2 ^ 63)] [HD].
  pose proof (DI_st_head _ _ _ _ _ _ _ _ _ _ _ HH m1 m X (HD + 65534) (hs - 1) 0 0 HDI ltac:(lia) ltac:(lia) ltac:(reflexivity)) as HDI2.
  ex2. split; [exact Hms|]. split; [rewrite Hhs in HDI2 |- *; exact HDI2|]. split; [hregs_via HRG Hfr|].
  rewrite Hhs. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Lemma cells2_filled0 : forall (m0 m' : word -> option byte) P n f k,
  cells s6_segs m0 P 2 2 n f -> filled m' P (P + 2 * k) (ms_bb 0) -> same_outside m0 m' P (P + 2 * k) ->
  0 <= k <= n -> 0 <= P -> P + 2 * n <= 2 ^ 64 ->
  cells s6_segs m' P 2 2 n (fun i => if i <? k then 0 else f i).
Proof using.
  intros m0 m' P n f k Hc Hf Hs Hk Hp0 Hpn i Hi.
  destruct (Z.ltb_spec i k) as [Hik|Hik].
  - unfold cell. cbn [rdn Z_to_le_bytes].
    rewrite (Hf (zw (P + 2 * i))) by (rewrite u_zw_small by lia; lia).
    rewrite (Hf (bv_add (zw (P + 2 * i)) 1%bv)).
    2:{ unfold zw. rewrite Z2bv_add1. fold (zw (P + 2 * i + 1)). rewrite u_zw_small by lia. lia. }
    reflexivity.
  - apply (cell_same_outside s6_segs m0 m' P (P + 2 * k)); [exact (Hc i Hi) | exact Hs | lia | lia | cbn; lia].
Qed.

Lemma arr_fill_head_eq : forall (hd : arr) k i, 0 <= k -> 0 <= i < arr_len hd ->
  arr_get (arr_fill hd 0 k 0) i = (if i <? k then 0 else arr_get hd i).
Proof using.
  intros hd k i Hk Hi. rewrite arr_get_fill. rewrite Z.max_r by lia. rewrite Z.add_0_l.
  replace (arr_inb hd i) with true by (symmetry; apply arr_inb_spec; lia).
  destruct (Z.leb_spec 0 i); [| lia]. cbn [andb]. destruct (i <? k); reflexivity.
Qed.

Lemma call_ms : forall regs m1 m X,
  DI m1 m X -> hs = 32768 ->
  getr regs 10 = zw HD -> getr regs 11 = zw 0 -> getr regs 12 = zw (2 * (hs - 1)) -> getr regs 1 = (0x17a9c%bv : word) ->
  exists R m',
    msteps s6_segs (mkst regs (0x27c04 : word) m s6_rom) (mkst R (0x17a9c : word) m' s6_rom)
    /\ DI m1 m' (set_head X (arr_fill (ds_head X) 0 (hs - 1) 0))
    /\ (forall a w v, cell s6_segs m a w v -> (a + Z.of_nat w <= HD \/ HD + 2 * hs <= a) -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> cell s6_segs m' a w v)
    /\ (forall r : reg, reg_in r memset_clob = false -> getr R r = getr regs r).
Proof using HH MEMSET HF ra flush.
  intros regs m1 m X HDI Hhs P10 P11 P12 P1.
  pose proof HDI as (HB & HR & (Ews & Ehs & Elbs)).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN). unfold DEFL_K6 in Hsp.
  unfold mapped, DEFL_K6 in MF.
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 4%nat ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T.
  pose proof (fun x Hx => HGR x (T x Hx)) as MHm; cbv beta in MHm; clear T.
  destruct (MEMSET m regs HD 0 (2 * (hs - 1)) (0x17a9c%bv : word) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(intros x Hx; apply MHm; lia) ltac:(apply ret_ok_even; reflexivity) P1 P10 P11 P12)
    as (R & m' & Hms & A10 & Hfr & Hfill & Hso & Hgr).
  symex_pc_lit_in Hms.
  exists R, m'. split; [exact Hms|].
  assert (Hag : agree_out [(HD, 2 * (hs - 1))] m m').
  { apply (same_outside_agree_out m m' HD (HD + 2 * (hs - 1))); [exact Hso|]. intros x Hx. cbn. lia. }
  assert (HFM : forall x : word, in_franges [(HD, 2 * (hs - 1))] (bv_unsigned x) -> m x <> None).
  { intros x [Hx|[]]; cbn in Hx. apply MHm. lia. }
  apartF 1%nat 4%nat A14. apartF 4%nat 5%nat A45. apartF 2%nat 4%nat A24. apartF 3%nat 4%nat A34.
  apartF 0%nat 4%nat A04. apartF 4%nat 6%nat A46. apartF 4%nat 7%nat A47. apartF 4%nat 8%nat A48.
  split.
  { split.
    {
      pose proof HB as (Bsc & Bar & Btl & Bpend & Blen & BagF & BMS & BMP & BGR).
      unfold BR. dsred.
      split; [eapply dsl_scalars_agree; [exact Bsc | exact Hag | unfold dsl_SIZE; intros x Hx [Hin|[]]; cbn in Hin; lia | lia | unfold dsl_SIZE; lia] |].
      split; [eapply arrays_agree_out; [exact Bar | exact Hag | intros x [Hin|[]]; cbn in Hin; lia | lia | lia] |].
      split; [exact Btl|].
      split; [eapply cells_agree_out; [exact Hag | intros x Hx [Hin|[]]; cbn in Hin; lia | cbn; lia | lia | lia | exact Bpend] |].
      split; [exact Blen|].
      split; [eapply agree_out_trans; [exact BagF | eapply agree_out_weaken; [exact Hag | intros x [Hin|[]]; cbn in Hin; apply in_Fd; unfold DEFL_K6; lia]] |].
      split; [intros x Hx; apply Hgr; apply BMS; exact Hx|].
      split; [intros x Hx; apply Hgr; apply BMP; exact Hx|].
      intros x Hx. apply Hgr. apply BGR. exact Hx. }
    split; [| dsred; exact (conj Ews (conj Ehs Elbs))].
    dsred. unfold RZ.
    split; [eapply cells_agree_out; [exact Hag | intros x Hx [Hin|[]]; cbn in Hin; lia | cbn; lia | lia | lia | exact Cw] |].
    split; [eapply cells_agree_out; [exact Hag | intros x Hx [Hin|[]]; cbn in Hin; lia | cbn; lia | lia | lia | exact Cp] |].
    split.
    {
      rewrite arr_len_fill, Lh. rewrite Lh in Ch.
      intros i Hi. rewrite arr_fill_head_eq by lia.
      exact (cells2_filled0 m m' HD hs (arr_get (ds_head X)) (hs - 1) Ch Hfill Hso ltac:(lia) ltac:(lia) ltac:(lia) i Hi). }
    split.
    { unfold zsl_scalars in *. eapply fields_agree_out; [exact Zs | exact zsl_layout_within | exact Hag | unfold zsl_SIZE; intros x Hx [Hin|[]]; cbn in Hin; lia | lia | unfold zsl_SIZE; lia]. }
    split; [unfold zsl_input in *; rewrite Ein in *; eapply cells_agree_out; [exact Hag | intros x Hx [Hin|[]]; cbn in Hin; lia | cbn; lia | lia | lia | exact Zi] |].
    split; [unfold zsl_outA in *; eapply cells_agree_out; [exact Hag | intros x Hx [Hin|[]]; cbn in Hin; lia | cbn; lia | lia | lia | exact Zo] |].
    split; [| unfold CST in *; rewrite arr_len_fill; exact HC].
    unfold RZmisc. split; [split; [exact (trees_rod_clear_agree R6 _ m m' (proj1 HRC) Hag HFM) | exact (got_agree _ m m' (proj2 HRC) Hag HFM)]|].
    split; [refine (rom_agree ROM _ m m' (dsh_roml _ _ _ _ _ _ _ _ _ _ _ HH) HRD Hag _); intros x [Hin|[]]; cbn in Hin;
           apply (GD_img _ _ _ _ _ _ _ _ _ _ _ HH); apply in_GD; unfold DEFL_K6, FR64; lia|].
    split; [eapply agree_out_trans; [exact HAG | eapply agree_out_weaken; [exact Hag | intros x [Hin|[]]; cbn in Hin; apply in_GDo; unfold DEFL_K6, FR64; lia]]|].
    split; [intros x Hx; apply Hgr; apply MF; exact Hx|].
    intros x Hx. apply Hgr. apply HGR. exact Hx. }
  split; [| exact Hfr].
  intros a w v Hc Hd Ha Haw. apply (cell_same_outside s6_segs m m' HD (HD + 2 * (hs - 1)) a w v Hc Hso); lia.
Qed.


Lemma bd_reset_eq : forall s : deflate_state,
  set_insert (set_strstart (set_block_start s 0) 0) 0 = set_insert (set_block_start (set_strstart s 0) 0) 0.
Proof using. intros s. destruct s; reflexivity. Qed.

Definition bd_reset (X : deflate_state) : deflate_state :=
  if ds_lookahead X =? 0 then set_insert (set_block_start (set_strstart X 0) 0) 0 else X.

Lemma bd_c : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 18 = zw (S + 5932) -> 0 <= ds_lookahead X < 2 ^ 31 ->
  exists R M,
    msteps s6_segs (mkst regs (0x17a9c : word) m s6_rom) (mkst R (0x17c80 : word) M s6_rom)
    /\ DI m1 M (bd_reset X)
    /\ HREGS R /\ getr R 10 = zw strm /\ getr R 1 = (0x17abc%bv : word)
    /\ (forall r : reg, reg_in r [1; 10]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG P18 Hlk. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6_lookahead C180. unfold bd_reset.
  destruct (Z.eqb_spec (ds_lookahead X) 0) as [El|El].
  - rewrite El in C180.
    run5b (HPINS ++ [(18, EAdd (EVar 32%nat) (ELit 5932))]) 14%nat [false] [RVal (ELit 0)] NoBounds (@nil Z).
    lazymatch type of Hms with
    | msteps _ _ (mkst _ _ (wbytes (wbytes (wbytes (wbytes ?M0 (zw _) _) (zw ?a1) _) (zw ?a2) _) (zw ?a3) _) _) =>
        pose proof (DI_st_gap m1 M0 X 0 HDI) as HDG;
        pose proof (DI_st_block_start _ _ _ _ _ _ _ _ _ _ _ HH m1 _ X 0 a1 HDG ltac:(lia)) as HD1;
        pose proof (DI_st_strstart _ _ _ _ _ _ _ _ _ _ _ HH m1 _ _ 0 a2 HD1 ltac:(lia)) as HD2;
        pose proof (DI_st_insert _ _ _ _ _ _ _ _ _ _ _ HH m1 _ _ 0 a3 HD2 ltac:(lia)) as HD3
    end.
    ex2. split; [exact Hms|]. split; [rewrite <- bd_reset_eq; exact HD3|].
    split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
  - pose proof (sx32_u64_nz (ds_lookahead X) ltac:(lia)) as Hsx.
    run5b (HPINS ++ [(18, EAdd (EVar 32%nat) (ELit 5932))]) 6%nat [true] [RVal (EVar 36%nat)] [(36%nat, 2 ^ 31)] [ds_lookahead X].
    ex2. split; [exact Hms|]. split; [apply DI_st_gap; exact HDI|].
    split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Lemma bd_d0 : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> cs_avail_out (ds_strm X) = 0 ->
  exists R,
    msteps s6_segs (mkst regs (0x17abc : word) m s6_rom) (mkst R (0x17a1c : word) m s6_rom)
    /\ HREGS R /\ getr R 10 = zw strm /\ getr R 11 = zw flush /\ getr R 12 = zw 0 /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r [10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG Ea. open_di HDI. open_hregs HRG.
  zs_cell Zs (@zsl_avail_out) Z32. rewrite Ea in Z32.
  run5b HPINS 8%nat [true] [RVal (ELit 0)] NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.

Lemma bd_d1 : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 31 -> cs_avail_out (ds_strm X) <> 0 ->
  exists R,
    msteps s6_segs (mkst regs (0x17abc : word) m s6_rom) (mkst R (0x17acc : word) m s6_rom)
    /\ HREGS R /\ getr R 10 = zw strm /\ getr R 11 = zw flush /\ getr R 12 = zw (cs_avail_out (ds_strm X)) /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r [10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG Hav Ea. open_di HDI. open_hregs HRG.
  zs_cell Zs (@zsl_avail_out) Z32.
  pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
  run5b HPINS 8%nat [false] [RVal (EVar 36%nat)] [(36%nat, 2 ^ 31)] [cs_avail_out (ds_strm X)].
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.

Lemma bd_e : forall regs m,
  getr regs 2 = zw SP -> getr regs 11 = zw flush -> flush = 3 ->
  exists R,
    msteps s6_segs (mkst regs (0x17acc : word) m s6_rom) (mkst R (0x17ad4 : word) m s6_rom)
    /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r [12]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra ds zp p S mem ROM.
  intros regs m P2 P11 Hf3. open_min. rewrite Hf3 in P11.
  run5b [(2, EVar 33%nat); (11, ELit 3)] 4%nat [false] NoReads NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma x34_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 12 = zw 0 ->
  exists R M,
    msteps s6_segs (mkst regs (0x17a1c : word) m s6_rom) (mkst R (0x17a24 : word) M s6_rom)
    /\ DI m1 M (set_last_flush X (-1))
    /\ getr R 2 = zw SP /\ getr R 12 = zw 0
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG P12. open_di HDI. open_hregs HRG.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (12, ELit 0)] 4%nat NoDirs NoReads NoBounds (@nil Z).
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KLastFlush].
  ex2. split; [exact Hms|]. split; [the_DI|]. split; [reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

End Walk.
End FXG.

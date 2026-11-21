(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 Callee6 CalleeKits6 TreesRod6 TreesApi6 DeflBlkApi6
  DeflSlow6_1 DeflSlow6_2 DeflSlow6_6 DeflKit6 Defl6Api Defl6_1 Defl6_2.
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
Local Abbreviation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Abbreviation AV0 := (cs_avail_out (ds_strm ds)).
Local Abbreviation SP := (sp - 64).
Hypothesis HF : DFH ROM mem S p zp ds flush ra sp.
Hypothesis MEMCPY : memcpy_run6.
Hypothesis TFBITS : tr_flush_bits_run6.
Variable SSAFE : deflate_state -> Z -> Prop.
Hypothesis SLOW : deflate_slow_run6 ROM SSAFE.
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



Lemma d42_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 13 = zw 42 -> ds_wrap X <> 0 -> - 2 ^ 31 <= ds_wrap X < 2 ^ 31 ->
  exists R,
    msteps s6_segs (mkst regs (0x16e20 : word) m s6_rom) (mkst R (0x16e4c : word) m s6_rom)
    /\ HREGS R /\ getr R 10 = getr regs 10 /\ getr R 12 = getr regs 12
    /\ (forall r : reg, reg_in r [13; 14]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG P13 Hw Hwr. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6_wrap C48.
  assert (RD48 : exists bs, rdn s6_segs m (zw (S + 48)) 4 = Some bs /\ bytes_le_to_Z bs = ds_wrap X mod 2 ^ 32)
    by exact (cell_read_at s6_segs m (S + 48) 4 _ _ C48 eq_refl).
  assert (Hwm : (ds_wrap X mod 2 ^ 32) <> 0).
  { intros E. apply Hw. apply Z.mod_divide in E; [|lia]. destruct E as [k Hk]. assert (k = 0) by lia. lia. }
  pose proof (Z.mod_pos_bound (ds_wrap X) (2 ^ 32) ltac:(lia)) as Hwb.
  assert (Hsx : szwrap 32 (ds_wrap X mod 2 ^ 32) mod 2 ^ 64 <> 0).
  { destruct (sx32_cases (ds_wrap X mod 2 ^ 32) Hwb) as [[? E]|[? E]]; rewrite E; lia. }
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (13, ELit 42)] 10%nat
    [true; false] [RVal (EVar 36)] [(36%nat, 2 ^ 32)] [ds_wrap X mod 2 ^ 32].
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.

Lemma d113_blk : forall regs m,
  HREGS regs -> getr regs 13 = zw 113 ->
  exists R,
    msteps s6_segs (mkst regs (0x16e20 : word) m s6_rom) (mkst R (0x17944 : word) m s6_rom)
    /\ HREGS R /\ getr R 10 = getr regs 10 /\ getr R 11 = getr regs 11
    /\ (forall r : reg, reg_in r [12; 14]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra ds zp mem ROM.
  intros regs m HRG P13. open_min. open_hregs HRG.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (13, ELit 113)] 16%nat
    [false; true; true; true; false; false] NoReads NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.

Lemma d666_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 13 = zw 666 -> getr regs 10 = zw strm -> cs_avail_in (ds_strm X) = 0 ->
  exists R,
    msteps s6_segs (mkst regs (0x16e20 : word) m s6_rom) (mkst R (0x1794c : word) m s6_rom)
    /\ HREGS R /\ getr R 10 = zw strm /\ getr R 11 = getr regs 11 /\ getr R 12 = zw 0
    /\ (forall r : reg, reg_in r [12; 14]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG P13 P10 Hai. open_di HDI. open_hregs HRG.
  zs_cell Zs (@zsl_avail_in) C8. rewrite Hai in C8.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (13, ELit 666); (10, EVar 35%nat)] 12%nat
    [false; false; true] [RVal (ELit 0)] NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Definition hdr_st (X : deflate_state) : deflate_state :=
  set_status (set_strm
    (set_pending_buf (set_pending (set_pending_buf (set_pending X 1) (arr_set (ds_pending_buf X) 0 (wrap8 120))) 2)
                     (arr_set (arr_set (ds_pending_buf X) 0 (wrap8 120)) 1 (wrap8 30876)))
    (cset_adler (ds_strm X) 1)) 113.

Lemma hdr_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw strm -> getr regs 12 = zw 0 ->
  ds_pending X = 0 -> ds_w_bits X = 15 -> ds_strategy X = 0 -> ds_level X = 6 -> ds_strstart X = 0 -> 2 <= PBL ->
  exists R M,
    msteps s6_segs (mkst regs (0x16e4c : word) m s6_rom) (mkst R (0x17c80 : word) M s6_rom)
    /\ DI m1 M (hdr_st X)
    /\ HREGS R /\ getr R 10 = zw strm /\ getr R 1 = (0x16fa0%bv : word) /\ getr R 18 = zw strm
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 13; 14; 15; 18]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG P10 P12 Hp0 Hwb Hstr Hlv Hss Hpbl. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6_w_bits C84. rewrite Hwb in C84. sc_cell Hsc ds6_strategy C200. rewrite Hstr in C200.
  sc_cell Hsc ds6_level C196. rewrite Hlv in C196. sc_cell Hsc ds6_strstart C172. rewrite Hss in C172.
  sc_cell Hsc ds6_pending_buf C16.
  apartF 1%nat 5%nat A15. apartF 1%nat 6%nat A16.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, EVar 35%nat); (12, ELit 0)] 120%nat
    [false; true; true; true; true; true; true]
    [RVal (ELit 15); RVal (ELit 0); RVal (ELit 6); RVal (EVar 36); RVal (ELit 0)]
    [(36%nat, 2 ^ 63)] [PB].
  clear_aparts.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end)
    [KPending; KPb 0 120; KPending; KPb 1 30876; KAdler; KStatus].
  ex2. split; [exact Hms|].
  split; [lazymatch goal with H : DeflKit6.DI _ _ _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end; unfold hdr_st; st_close idtac|].
  split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Definition pend_pc (X : deflate_state) (pnz pz : word) : word :=
  if ds_pending X =? 0 then pz else pnz.

Lemma hdr2_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= ds_pending X < 2 ^ 63 -> ds_status X = 113 ->
  exists R,
    msteps s6_segs (mkst regs (0x16fa0 : word) m s6_rom) (mkst R (pend_pc X (0x17a18 : word) (0x17944 : word)) m s6_rom)
    /\ HREGS R /\ (ds_pending X = 0 -> getr R 10 = zw strm /\ getr R 11 = zw flush)
    /\ (forall r : reg, reg_in r [10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG Hpd Hst. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6_pending C40. sc_cell Hsc ds6_status C8. rewrite Hst in C8.
  unfold pend_pc. destruct (Z.eqb_spec (ds_pending X) 0) as [Hz|Hnz].
  - rewrite Hz in C40.
    run 20%nat [false; true; true; false; false] [RVal (ELit 0); RVal (ELit 113)] NoBounds (@nil Z).
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros _; split; reg1 HR Hfr | fr_weak Hfr].
  - run 8%nat [true] [RVal (EVar 36)] [(36%nat, 2 ^ 63)] [ds_pending X].
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros Hc; exfalso; lia | fr_weak Hfr].
Qed.

End Walk.
End FXG.

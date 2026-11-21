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
  ZIface DeflateState Trees TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel
  RefFlushPend1 RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3 RefDeflateHdr5 RefDeflateTrl1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 Callee6 CalleeKits6 TreesRod6 TreesApi6 DeflBlkApi6
  DeflSlow6_1 DeflSlow6_2 DeflSlow6_6 DeflKit6 Defl6Api Defl6_1.
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



Definition bc64_cond (X : deflate_state) : bool :=
  negb (ds_lookahead X =? 0) || (negb (flush =? 0) && negb (ds_status X =? 666)).
Definition bc64_pc (X : deflate_state) : word :=
  if bc64_cond X then (0x17954%bv : word) else if flush =? 0 then (0x17ad4%bv : word) else (0x17acc%bv : word).

Lemma blocks_cond_eq : forall X, blocks_cond X flush = negb (cs_avail_in (ds_strm X) =? 0) || bc64_cond X.
Proof using. intros X. unfold blocks_cond, bc64_cond, Z_NO_FLUSH, FINISH_STATE. destruct (_ =? _), (_ =? _), (_ =? _), (_ =? _); reflexivity. Qed.

Lemma bc_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw strm -> 0 <= cs_avail_in (ds_strm X) < 2 ^ 31 ->
  exists R,
    msteps s6_segs (mkst regs (0x17944 : word) m s6_rom)
           (mkst R (if cs_avail_in (ds_strm X) =? 0 then (0x1794c%bv : word) else (0x17954%bv : word)) m s6_rom)
    /\ HREGS R /\ getr R 10 = zw strm /\ getr R 11 = getr regs 11
    /\ (forall r : reg, reg_in r [12]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG P10 Hai. open_di HDI. open_hregs HRG.
  zs_cell Zs (@zsl_avail_in) C8z.
  Local Ltac bc_fin R Hms HRG HR Hfr := exists R; split; [exact Hms|]; split; [hregs_via HRG Hfr|]; repeat (split; [reg1 HR Hfr|]); fr_weak Hfr.
  destruct (Z.eqb_spec (cs_avail_in (ds_strm X)) 0) as [Ea|Ea].
  - rewrite Ea in C8z.
    run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, EVar 35%nat)] 8%nat
      [false] [RVal (ELit 0)] NoBounds (@nil Z).
    bc_fin R Hms HRG HR Hfr.
  - pose proof (sx32_u64_nz (cs_avail_in (ds_strm X)) ltac:(lia)) as Hsx.
    run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, EVar 35%nat)] 8%nat
      [true] [RVal (EVar 36)] [(36%nat, 2 ^ 31)] [cs_avail_in (ds_strm X)].
    bc_fin R Hms HRG HR Hfr.
Qed.

Lemma bc64_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw strm -> getr regs 11 = zw flush ->
  0 <= ds_lookahead X < 2 ^ 31 -> 0 <= ds_status X < 2 ^ 31 ->
  exists R,
    msteps s6_segs (mkst regs (0x1794c : word) m s6_rom) (mkst R (bc64_pc X) m s6_rom)
    /\ HREGS R /\ getr R 10 = zw strm /\ getr R 11 = zw flush
    /\ (forall r : reg, reg_in r [12; 13]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG P10 P11 Hlk Hst. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6_lookahead C180. sc_cell Hsc ds6_status C8.
  unfold bc64_pc, bc64_cond.
  destruct (Z.eqb_spec (ds_lookahead X) 0) as [El|El]; cbn [negb orb andb].
  - rewrite El in C180. destruct (Z.eqb_spec flush 0) as [Ef|Ef]; cbn [negb andb].
    + run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, EVar 35%nat); (11, EVar 34%nat)] 12%nat
        [true; true] [RVal (ELit 0)] NoBounds (@nil Z).
      bc_fin R Hms HRG HR Hfr.
    + destruct (Z.eqb_spec (ds_status X) 666) as [Es|Es]; cbn [negb].
      * rewrite Es in C8.
        run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, EVar 35%nat); (11, EVar 34%nat)] 14%nat
          [true; false; false] [RVal (ELit 0); RVal (ELit 666)] NoBounds (@nil Z).
        bc_fin R Hms HRG HR Hfr.
      * run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, EVar 35%nat); (11, EVar 34%nat)] 14%nat
          [true; false; true] [RVal (ELit 0); RVal (EVar 36)] [(36%nat, 2 ^ 31)] [ds_status X].
        bc_fin R Hms HRG HR Hfr.
  - run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, EVar 35%nat); (11, EVar 34%nat)] 12%nat
      [false] [RVal (EVar 36)] [(36%nat, 2 ^ 31)] [ds_lookahead X].
    bc_fin R Hms HRG HR Hfr.
Qed.


Lemma cfg6_func_cell : forall m, rom_clear m 0x10000 0x293d8 -> cell s6_segs m (0 + 168536) 8 0x19558.
Proof using.
  intros m HR. unfold cell.
  rewrite (rdn_ext s6_segs 8 m (fun _ => None) (zw (0 + 168536))); [| rewrite u_zw_small by lia; lia |].
  - etransitivity; [vm_compute; reflexivity|]. f_equal. apply bytes_eq_of_unsigned'. vm_compute. reflexivity.
  - intros x Hx. rewrite u_zw_small in Hx by lia. apply HR. lia.
Qed.

Lemma call_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 11 = zw flush -> ds_level X = 6 -> ds_strategy X = 0 ->
  rom_clear m1 0x10000 0x293d8 ->
  exists R,
    msteps s6_segs (mkst regs (0x17954 : word) m s6_rom) (mkst R (0x19558 : word) m s6_rom)
    /\ HREGS R /\ getr R 10 = zw S /\ getr R 11 = zw flush /\ getr R 2 = zw SP /\ getr R 1 = (0x179c4%bv : word)
    /\ (forall r : reg, reg_in r [1; 10; 12; 13]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG P11 Hlv Hstr HR1. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6_level C196. rewrite Hlv in C196. sc_cell Hsc ds6_strategy C200. rewrite Hstr in C200.
  pose proof (cfg6_func_cell m (img_DI _ _ _ _ _ _ _ _ _ HF m1 m X _ _ HDI HR1 ltac:(lia) ltac:(lia))) as CF.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (11, EVar 34%nat)] 16%nat
    [false; false; true] [RVal (ELit 6); RVal (ELit 0); RVal (ELit 0x19558)] NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Lemma apart_from_shrink : forall a n a' n' l,
  apart_from (a, n) l -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> apart_from (a', n') l.
Proof using.
  intros a n a' n' l. induction l as [|[b k] l IH]; intros H H1 H2 H3; [exact I|].
  destruct H as [A B]. split; [| exact (IH B H1 H2 H3)]. unfold apart in *. cbn [fst snd] in *. lia.
Qed.

Lemma apart_all_shrink0 : forall a n a' n' l,
  apart_all ((a, n) :: l) -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> apart_all ((a', n') :: l).
Proof using. intros a n a' n' l [A B] H1 H2 H3. split; [exact (apart_from_shrink a n a' n' l A H1 H2 H3) | exact B]. Qed.

Lemma call_slow : forall regs m1 m X,
  DI m1 m X -> SSAFE X flush ->
  getr regs 10 = zw S -> getr regs 11 = zw flush -> getr regs 2 = zw SP -> getr regs 1 = (0x179c4%bv : word) ->
  exists R m',
    msteps s6_segs (mkst regs (0x19558 : word) m s6_rom) (mkst R (0x179c4 : word) m' s6_rom)
    /\ DI m1 m' (fst (deflate_slow X flush))
    /\ getr R 10 = zw (bs_code (snd (deflate_slow X flush))) /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R r = getr regs r).
Proof using HL HH SLOW HF ra.
  intros regs m1 m X HDI HSAFE P10 P11 P2 P1.
  pose proof HDI as (HB & HR & HS3). pose proof HS3 as (Ews & Ehs & Elbs).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HB as (_ & _ & _ & Hpb & Epbl & _).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN). unfold DEFL_K6 in Hsp.
  pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl. unfold DEFL_K6 in MF.
  assert (HL' : ZRH6 DSLOW_FRAME6 m S SP p zp X).
  { constructor.
    - unfold DSLOW_FRAME6. lia.
    - unfold zr_regions, DSLOW_FRAME6. rewrite Ews, Ehs, Elbs, Eout, Ein.
      pose proof (zrh_rng _ _ _ _ _ _ _ HL) as HRG0. unfold zr_regions, DEFL_K6 in HRG0.
      apply Forall_cons_iff in HRG0 as [_ HRG0]. constructor; [cbn [fst snd]; lia | exact HRG0].
    - rewrite Ein. exact (zrh_in _ _ _ _ _ _ _ HL).
    - exact (zrh_W _ _ _ _ _ _ _ HL).
    - exact (zrh_HD _ _ _ _ _ _ _ HL).
    - exact (zrh_PV _ _ _ _ _ _ _ HL).
    - unfold ZRF, DSLOW_FRAME6. rewrite Ews, Ehs, Elbs, Eout.
      pose proof (zrh_map _ _ _ _ _ _ _ HL) as HM0. unfold ZRF, DEFL_K6 in HM0. apply Forall_cons_iff in HM0 as [_ HM0].
      constructor; [cbn [fst snd]; intros x Hx; apply MF; lia|].
      eapply Forall_impl; [| exact HM0]. intros [b k] Hb x Hx. apply HGR. exact (Hb x Hx).
    - unfold zr_regions, DSLOW_FRAME6. rewrite Ews, Ehs, Elbs, Eout, Ein.
      pose proof (zrh_apart _ _ _ _ _ _ _ HL) as HA0. unfold zr_regions, DEFL_K6 in HA0.
      apply (apart_all_shrink0 (sp - 416) 416); [exact HA0 | lia | lia | lia].
    - exact HRC.
    - intros x Hx Hi. apply (zrh_img _ _ _ _ _ _ _ HL x); [| exact Hi].
      unfold ZRF, DSLOW_FRAME6, DEFL_K6 in *. rewrite Ews, Ehs, Elbs, Eout in Hx. cbn [in_franges] in Hx |- *. lia.
    - exact (zrh_O _ _ _ _ _ _ _ HL). }
  assert (HZ : ZR6 m S p zp X).
  { unfold ZR6, ds6_windowA, ds6_prevA, ds6_headA, ds6_arrays, ds6_pendA. rewrite Epbl.
    repeat (split; [assumption|]). exact Zo. }
  destruct (SLOW m S p zp X flush (0x179c4%bv : word) SP regs HL' ltac:(apply ret_ok_even; reflexivity) HZ HRD HSAFE Hfl P10 P11 P2 P1)
    as (R & m' & Hms & HZ' & A10 & A2 & Hfr & Hag & Hrod & Hrom & Hgr & Hk).
  unfold A6_DEFLATE_SLOW in Hms. symex_pc_lit_in Hms.
  exists R, m'. split; [exact Hms|]. split; [| split; [exact A10 | split; [exact A2 | exact Hfr]]].
  set (X' := fst (deflate_slow X flush)) in *.
  destruct Hk as (Kws & Khs & Klbs & Kwl & Kpl & Khl & Kbl & Kin & Kout & Kao & Kol).
  rewrite Ews in Kws, Kwl, Kpl. rewrite Ehs in Khs, Khl. rewrite Elbs in Klbs, Kbl. rewrite Ein in Kin. rewrite Eout in Kout.
  destruct HZ' as (Zsc & Zar & Ztl & ZwA & ZpA & ZhA & ZbA & Zzs & Zzi & Zzo).
  assert (HFG : forall x, in_franges (ZRFo DSLOW_FRAME6 S SP p zp X (Z.of_nat (length (cs_out_rev (ds_strm X'))))) x ->
                          in_franges (DeflKit6.GDo S p zp ds sp DEFL_K6 FR64 (ds_strm X')) x).
  { intros x Hx. unfold DeflKit6.GDo. unfold ZRFo, DSLOW_FRAME6, DEFL_K6, FR64, ds6_SIZE, zsl_SIZE in Hx |- *. rewrite Ews, Ehs, Elbs in Hx.
    cbn [in_franges] in Hx |- *. lia. }
  assert (HFF : forall x, in_franges (ZRFo DSLOW_FRAME6 S SP p zp X (Z.of_nat (length (cs_out_rev (ds_strm X'))))) x ->
                          in_franges (DeflKit6.Fd S p zp ds sp DEFL_K6) x).
  { intros x Hx. apply (GD_Fd _ _ _ _ _ _ _ _ _ _ _ HH). apply (GDo_GD _ _ _ _ _ _ _ (ds_strm X')); [exact (HFG x Hx) | lia]. }
  split; [| split; [| exact (conj Kws (conj Khs Klbs))]].
  -
    unfold BR. unfold ds6_pendA in ZbA. rewrite Kbl in ZbA.
    split; [exact Zsc|]. split; [exact Zar|]. split; [exact Ztl|]. split; [exact ZbA|]. split; [exact Kbl|].
    split; [eapply agree_out_trans; [exact HagF | eapply agree_out_weaken; [exact Hag | exact HFF]]|].
    split; [intros x Hx; apply Hgr; exact (MS x Hx)|]. split; [intros x Hx; apply Hgr; exact (MP x Hx)|].
    intros x Hx. apply Hgr. exact (HGR0 x Hx).
  -
    unfold DeflKit6.RZ. unfold ds6_windowA, ds6_prevA, ds6_headA in *.
    split; [exact ZwA|]. split; [exact ZpA|]. split; [exact ZhA|]. split; [exact Zzs|]. split; [exact Zzi|]. split; [exact Zzo|].
    split.
    + unfold DeflKit6.RZmisc. split; [exact Hrod|]. split; [exact Hrom|].
      split; [eapply agree_out_trans; [eapply agree_out_weaken; [exact HAG | intros x Hx; eapply GDo_mono; [exact Hx | lia]]
                                    | eapply agree_out_weaken; [exact Hag | exact HFG]]|].
      split; [unfold DEFL_K6; intros x Hx; apply Hgr; apply MF; exact Hx|].
      intros x Hx. apply Hgr. exact (HGR x Hx).
    + unfold DeflKit6.CST. rewrite Kin. repeat (split; [first [assumption | reflexivity | lia]|]). lia.
Qed.


Definition bst_st (X : deflate_state) (bs : block_state) : deflate_state :=
  match bs with finish_started | finish_done => set_status X 666 | _ => X end.
Definition bst_pc (X : deflate_state) (bs : block_state) : word :=
  match bs with
  | finish_done => (0x17acc%bv : word)
  | _ => if cs_avail_out (ds_strm X) =? 0 then (0x17a18%bv : word) else (0x17ad4%bv : word)
  end.

Lemma bst_blk : forall regs m1 m X bs,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw (bs_code bs) -> bs <> block_done ->
  0 <= cs_avail_out (ds_strm X) < 2 ^ 31 ->
  exists R M,
    msteps s6_segs (mkst regs (0x179c4 : word) m s6_rom) (mkst R (bst_pc X bs) M s6_rom)
    /\ DI m1 M (bst_st X bs)
    /\ HREGS R /\ (bs = finish_done -> getr R 11 = zw flush /\ getr R 10 = zw strm)
    /\ (forall r : reg, reg_in r [10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X bs HDI HRG P10 Hbd Hav. open_di HDI. open_hregs HRG.
  zs_cell Zs (@zsl_avail_out) Z32.
  Local Ltac bst_fin Hms HDI HRG HR Hfr ks :=
    clear_aparts;
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) ks;
    ex2; split; [exact Hms|]; split; [the_DI|]; split; [hregs_via HRG Hfr|];
    split; [first [intros; discriminate | intros _; split; reg1 HR Hfr] | fr_weak Hfr].
  unfold bst_pc, bst_st. destruct bs; [| exfalso; exact (Hbd eq_refl) | |]; cbn [bs_code] in P10.
  -
    destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
    + rewrite Hz in Z32.
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, ELit 0)] 14%nat
        [true; true; false] [RVal (ELit 0)] NoBounds (@nil Z).
      bst_fin Hms HDI HRG HR Hfr (@nil dkind).
    + pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, ELit 0)] 14%nat
        [true; true; true] [RVal (EVar 36)] [(36%nat, 2 ^ 32)] [cs_avail_out (ds_strm X)].
      bst_fin Hms HDI HRG HR Hfr (@nil dkind).
  -
    apartF 1%nat 6%nat A16.
    destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
    + rewrite Hz in Z32.
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, ELit 2)] 16%nat
        [false; true; false] [RVal (ELit 0)] NoBounds (@nil Z).
      bst_fin Hms HDI HRG HR Hfr [KStatus].
    + pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, ELit 2)] 16%nat
        [false; true; true] [RVal (EVar 36)] [(36%nat, 2 ^ 32)] [cs_avail_out (ds_strm X)].
      bst_fin Hms HDI HRG HR Hfr [KStatus].
  -
    apartF 1%nat 6%nat A16.
    run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, ELit 3)] 16%nat
      [false; false; true] NoReads NoBounds (@nil Z).
    bst_fin Hms HDI HRG HR Hfr [KStatus].
Qed.

End Walk.
End FXG.

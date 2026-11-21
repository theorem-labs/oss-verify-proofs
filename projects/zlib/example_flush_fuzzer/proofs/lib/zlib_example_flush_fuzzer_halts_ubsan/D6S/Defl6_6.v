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



Lemma DI_st_wrap' : forall m1 m X v v' a, DI m1 m X -> a = S + 48 -> v' mod 2 ^ 32 = v mod 2 ^ 32 ->
  DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_wrap X v').
Proof using HF ra flush.
  intros m1 m X v v' a HDI Ha Ev.
  rewrite (Z_to_le_bytes_mod_eq 4 v v') by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); symmetry; exact Ev).
  exact (DI_st_wrap _ _ _ _ _ _ _ _ _ HF m1 m X v' a HDI Ha).
Qed.


Definition trl_st (X : deflate_state) : deflate_state :=
  let a := cs_adler (ds_strm X) in
  let p0 := ds_pending X in
  let b0 := ds_pending_buf X in
  let b1 := arr_set b0 p0 (wrap8 (a / 2 ^ 24)) in
  let b2 := arr_set b1 (p0 + 1) (wrap8 (a / 2 ^ 16)) in
  let b3 := arr_set b2 (p0 + 2) (wrap8 (a / 2 ^ 8)) in
  let b4 := arr_set b3 (p0 + 3) (wrap8 a) in
  set_pending_buf (set_pending (set_pending_buf (set_pending (set_pending_buf (set_pending (set_pending_buf (set_pending X
    (p0 + 1)) b1) (p0 + 2)) b2) (p0 + 3)) b3) (p0 + 4)) b4.

Definition t1_pc (X : deflate_state) : word :=
  if negb (flush =? 4) then (0x17ad4%bv : word) else if ds_wrap X <=? 0 then (0x17bd0%bv : word) else (0x17c80%bv : word).
Definition t1_st (X : deflate_state) : deflate_state :=
  if negb (flush =? 4) then X else if ds_wrap X <=? 0 then X else trl_st X.

Lemma t1_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw strm -> getr regs 11 = zw flush ->
  (ds_wrap X = 1 \/ ds_wrap X = -1) -> 0 <= ds_pending X -> ds_pending X + 4 <= PBL ->
  0 <= cs_adler (ds_strm X) < 2 ^ 32 ->
  exists R M,
    msteps s6_segs (mkst regs (0x17acc : word) m s6_rom) (mkst R (t1_pc X) M s6_rom)
    /\ DI m1 M (t1_st X)
    /\ HREGS R /\ getr R 10 = zw strm
    /\ (flush = 4 -> 0 < ds_wrap X -> getr R 1 = (0x17c4c%bv : word))
    /\ (forall r : reg, reg_in r [1; 11; 12; 13; 14; 15]%bv = false -> getr R r = getr regs r).
Proof using HWF HP HH HF ra.
  intros regs m1 m X HDI HRG P10 P11 Hw Hp0 Hp4 Had. open_di HDI. open_hregs HRG.
  pose proof (wf_lbs _ HWF) as Wlbs.
  sc_cell Hsc ds6_wrap C48. sc_cell Hsc ds6_pending C40. sc_cell Hsc ds6_pending_buf C16. zs_cell Zs (@zsl_adler) Z96.
  unfold t1_pc, t1_st.
  destruct (Z.eqb_spec flush 4) as [Ef|Ef]; cbn [negb].
  - destruct (Z.leb_spec (ds_wrap X) 0) as [Hle|Hgt].
    + assert (Ew : ds_wrap X = -1) by lia. rewrite Ew in C48.
      assert (RD48 : exists bs, rdn s6_segs m (zw (S + 48)) 4 = Some bs /\ bytes_le_to_Z bs = 4294967295)
        by exact (cell_read_at s6_segs m (S + 48) 4 _ _ C48 eq_refl).
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, EVar 35%nat); (11, EVar 34%nat)] 12%nat
        [true; true] [RVal (ELit 4294967295)] NoBounds (@nil Z).
      ex2. split; [exact Hms|]. split; [exact HDI|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr|].
      split; [intros _ Hc; exfalso; lia | fr_weak Hfr].
    + assert (Ew : ds_wrap X = 1) by lia. rewrite Ew in C48.
      apartF 1%nat 5%nat A15. apartF 1%nat 6%nat A16. apartF 5%nat 6%nat A56.
      pose proof (Z.div_pos (cs_adler (ds_strm X)) (2 ^ 24) ltac:(lia) ltac:(lia)) as D24.
      run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, EVar 35%nat); (11, EVar 34%nat)] 60%nat
        [true; false; true] [RVal (ELit 1); RVal (EVar 36); RVal (EVar 37); RVal (EVar 38)]
        [(36%nat, 2 ^ 32); (37%nat, 2 ^ 62); (38%nat, 2 ^ 63)]
        [cs_adler (ds_strm X); ds_pending X; PB].
      clear_aparts.
      di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end)
        [KPending; KPb (ds_pending X) (cs_adler (ds_strm X) / 2 ^ 24);
         KPending; KPb (ds_pending X + 1) (cs_adler (ds_strm X) / 2 ^ 16);
         KPending; KPb (ds_pending X + 2) (cs_adler (ds_strm X) / 2 ^ 8);
         KPending; KPb (ds_pending X + 3) (cs_adler (ds_strm X))].
      ex2. split; [exact Hms|].
      split; [lazymatch goal with H : DeflKit6.DI _ _ _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end; unfold trl_st; st_close idtac|].
      split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr|]. split; [intros _ _; reg1 HR Hfr | fr_weak Hfr].
  - run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, EVar 35%nat); (11, EVar 34%nat)] 8%nat
      [false] NoReads NoBounds (@nil Z).
    ex2. split; [exact Hms|]. split; [exact HDI|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr|].
    split; [intros Hc; exfalso; lia | fr_weak Hfr].
Qed.


Definition t2_st (X : deflate_state) : deflate_state :=
  if 0 <? ds_wrap X then set_wrap X (- ds_wrap X) else X.

Lemma t2_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> (ds_wrap X = 1 \/ ds_wrap X = -1) -> 0 <= ds_pending X < 2 ^ 63 ->
  exists R M,
    msteps s6_segs (mkst regs (0x17c4c : word) m s6_rom) (mkst R (0x17a24 : word) M s6_rom)
    /\ DI m1 M (t2_st X)
    /\ getr R 2 = zw SP /\ getr R 12 = zw (if ds_pending X =? 0 then 1 else 0)
    /\ (forall r : reg, reg_in r [10; 12]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG Hw Hpd. open_di HDI. open_hregs HRG.
  sc_cell Hsc ds6_wrap C48. sc_cell Hsc ds6_pending C40.
  unfold t2_st.
  destruct Hw as [Ew|Ew]; rewrite Ew in C48 |- *; cbn [Z.ltb Z.compare Z.opp].
  - apartF 1%nat 6%nat A16.
    destruct (Z.eqb_spec (ds_pending X) 0) as [Hz|Hnz].
    + rewrite Hz in C40.
      run 16%nat [false] [RVal (ELit 1); RVal (ELit 0)] NoBounds (@nil Z).
      clear_aparts.
      lazymatch type of Hms with msteps _ _ (mkst _ _ (wbytes ?M1 (zw ?a) (Z_to_le_bytes 4 ?v)) _) =>
        pose proof (DI_st_wrap' m1 M1 X v (-1) a HDI ltac:(lia) ltac:(reflexivity)) as HDI2 end.
      ex2. split; [exact Hms|]. split; [first [exact HDI2 | rewrite Ew; exact HDI2]|]. split; [reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
    + run 16%nat [false] [RVal (ELit 1); RVal (EVar 36)] [(36%nat, 2 ^ 63)] [ds_pending X].
      clear_aparts.
      lazymatch type of Hms with msteps _ _ (mkst _ _ (wbytes ?M1 (zw ?a) (Z_to_le_bytes 4 ?v)) _) =>
        pose proof (DI_st_wrap' m1 M1 X v (-1) a HDI ltac:(lia) ltac:(reflexivity)) as HDI2 end.
      ex2. split; [exact Hms|]. split; [first [exact HDI2 | rewrite Ew; exact HDI2]|]. split; [reg1 HR Hfr|].
      split; [symex_reg HR (12%bv : reg) as A12; rewrite A12; f_equal; destruct (Z.ltb_spec (ds_pending X) 1); lia | fr_weak Hfr].
  - assert (RD48 : exists bs, rdn s6_segs m (zw (S + 48)) 4 = Some bs /\ bytes_le_to_Z bs = 4294967295)
      by exact (cell_read_at s6_segs m (S + 48) 4 _ _ C48 eq_refl).
    destruct (Z.eqb_spec (ds_pending X) 0) as [Hz|Hnz].
    + rewrite Hz in C40.
      run 12%nat [true] [RVal (ELit 4294967295); RVal (ELit 0)] NoBounds (@nil Z).
      ex2. split; [exact Hms|]. split; [exact HDI|]. split; [reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
    + run 12%nat [true] [RVal (ELit 4294967295); RVal (EVar 36)] [(36%nat, 2 ^ 63)] [ds_pending X].
      ex2. split; [exact Hms|]. split; [exact HDI|]. split; [reg1 HR Hfr|].
      split; [symex_reg HR (12%bv : reg) as A12; rewrite A12; f_equal; destruct (Z.ltb_spec (ds_pending X) 1); lia | fr_weak Hfr].
Qed.

End Walk.
End FXG.

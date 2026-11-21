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
  ZIface DeflateState Trees TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 Callee6 CalleeKits6 TreesRod6 TreesApi6 DeflBlkApi6
  DeflSlow6_1 DeflSlow6_2 DeflSlow6_6 DeflKit6 Defl6Api Defl6_1 Defl6_2.
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



Definition FPS (m : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  cell s6_segs m (SP + -8) 8 (bv_unsigned (getr regs0 1))
  /\ cell s6_segs m (SP + -16) 8 (bv_unsigned (getr regs0 8))
  /\ cell s6_segs m (SP + -24) 8 (bv_unsigned (getr regs0 9))
  /\ cell s6_segs m (SP + -32) 8 (bv_unsigned (getr regs0 18)).

Lemma FPS_write_other : forall m regs0 (b : Z) bs,
  FPS m regs0 -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 -> (SP <= b \/ b + Z.of_nat (length bs) <= SP - 32) -> 32 <= SP <= 2 ^ 63 ->
  FPS (wbytes m (zw b) bs) regs0.
Proof using.
  intros m regs0 b bs (C1 & C8 & C9 & C18) Hb0 Hb1 Hd Hsp. unfold FPS.
  repeat split; (apply cell_write_other; [assumption | lia | cbn; lia | lia | lia | cbn; lia]).
Qed.

Lemma FPS_agree : forall F m m' regs0,
  FPS m regs0 -> agree_out F m m' -> disj_franges F (SP - 32) 32 -> 32 <= SP -> SP <= 2 ^ 63 -> FPS m' regs0.
Proof using.
  intros F m m' regs0 (C1 & C8 & C9 & C18) Hag Hd Hsp Hsp'. unfold FPS.
  repeat split; (eapply (cell_agree_out s6_segs F m m'); [exact Hag | intros x Hx; apply Hd; cbn in Hx; lia | lia | cbn; lia | assumption]).
Qed.


Lemma fpn_a : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw strm ->
  exists R M,
    msteps s6_segs (mkst regs (0x17c80 : word) m s6_rom) (mkst R (0x1ad94 : word) M s6_rom)
    /\ DI m1 M X /\ FPS M regs
    /\ getr R 8 = zw S /\ getr R 9 = zw strm /\ getr R 2 = zw (SP - 32) /\ getr R 22 = zw flush
    /\ getr R 10 = zw S /\ getr R 1 = (0x17ca4%bv : word)
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10]%bv = false -> getr R r = getr regs r).
Proof using HP HH HF ra.
  intros regs m1 m X HDI HRG P10. open_di HDI. open_hregs HRG.
  zs_cell Zs (@zsl_state) C56.
  pose proof (u64_range (getr regs 1)) as U1. pose proof (u64_range (getr regs 18)) as U18.
  apartF 0%nat 6%nat A06.
  run_gen [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (22, EVar 34%nat); (10, EVar 35%nat)] 20%nat NoDirs
    [RVal (EVar 32)] NoBounds (@nil Z).
  clear_aparts.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KFrame; KFrame; KFrame; KFrame].
  ex2. split; [exact Hms|]. split; [the_DI|].
  split; [unfold FPS; rewrite P8, P9; rewrite !u_zw_small by lia; repeat split; frame_cells|].
  repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Definition FPINS : list (Z * expr) :=
  [(8, EVar 32%nat); (9, EVar 35%nat); (2, EAdd (EVar 33%nat) (ELit (-32))); (22, EVar 34%nat)].
Definition FPREGS (R : bvmap 5 word) : Prop :=
  getr R 8 = zw S /\ getr R 9 = zw strm /\ getr R 2 = zw (SP - 32) /\ getr R 22 = zw flush.

Lemma fpn_c : forall regs m1 m X,
  DI m1 m X -> FPREGS regs ->
  0 <= ds_pending X < 2 ^ 31 -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 31 -> 0 <= ds_pending_out X <= PBL ->
  exists R,
    msteps s6_segs (mkst regs (0x17ca4 : word) m s6_rom) (mkst R (fpa_pc X (0x17d10 : word) (0x27800 : word)) m s6_rom)
    /\ FPREGS R
    /\ (fp_len X <> 0 ->
        getr R 10 = zw (OUTB + Z.of_nat (length (cs_out_rev (ds_strm X)))) /\ getr R 11 = zw (PB + ds_pending_out X)
        /\ getr R 12 = zw (fp_len X) /\ getr R 18 = zw (fp_len X) /\ getr R 1 = (0x17cc8%bv : word))
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 18]%bv = false -> getr R r = getr regs r).
Proof using HWF HP HH HF ra.
  intros regs m1 m X HDI (P8 & P9 & P2 & P20) Hpd Hav Hpo. open_di HDI.
  pose proof (wf_lbs _ HWF) as Wlbs.
  sc_cell Hsc ds6_pending C40. sc_cell Hsc ds6_pending_out C32.
  zs_cell Zs (@zsl_avail_out) Z32. zs_cell Zs (@zsl_next_out) Z24.
  destruct (DeflSlow6_6.fp_len_eq X ltac:(lia) ltac:(lia)) as (Efl & Hfl1 & Hfl2).
  pose proof (zext32_small (fp_len X) ltac:(lia)) as Hzx.
  assert (P2' : getr regs 2 = zw (SP + -32)) by (rewrite P2; f_equal; lia).
  unfold fpa_pc.
  Local Ltac fpnc_fin R Hms HR Hfr :=
    exists R; split; [exact Hms|]; split; [unfold FPREGS; repeat split; reg1 HR Hfr|];
    split; [first [intros Hc; exfalso; lia | intros _; repeat split; reg1 HR Hfr] | fr_weak Hfr].
  destruct (Z.ltb_spec (ds_pending X) (cs_avail_out (ds_strm X))) as [Hlt|Hge].
  - assert (EM : fp_len X = ds_pending X) by (rewrite Efl; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia).
    rewrite EM in *.
    destruct (Z.eqb_spec (ds_pending X) 0) as [Hz|Hnz].
    + run_gen FPINS 30%nat [true; true] [RVal (EVar 36); RVal (EVar 37)] [(36%nat, 2 ^ 31); (37%nat, 2 ^ 31)]
        [ds_pending X; cs_avail_out (ds_strm X)].
      fpnc_fin R Hms HR Hfr.
    + run_gen FPINS 30%nat [true; false] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
        [(36%nat, 2 ^ 31); (37%nat, 2 ^ 31); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
        [ds_pending X; cs_avail_out (ds_strm X); OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X].
      fpnc_fin R Hms HR Hfr.
  - assert (EM : fp_len X = cs_avail_out (ds_strm X)) by (rewrite Efl; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia).
    rewrite EM in *.
    destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
    + run_gen FPINS 30%nat [false; true] [RVal (EVar 36); RVal (EVar 37)] [(36%nat, 2 ^ 31); (37%nat, 2 ^ 31)]
        [ds_pending X; cs_avail_out (ds_strm X)].
      fpnc_fin R Hms HR Hfr.
    + run_gen FPINS 30%nat [false; false] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
        [(36%nat, 2 ^ 31); (37%nat, 2 ^ 31); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
        [ds_pending X; cs_avail_out (ds_strm X); OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X].
      fpnc_fin R Hms HR Hfr.
Qed.


Lemma fpn_d : forall regs m1 M0 X len,
  DI m1 M0 X -> FPREGS regs -> getr regs 18 = zw len ->
  0 < len <= ds_pending X -> ds_pending X < 2 ^ 31 -> len <= cs_avail_out (ds_strm X) < 2 ^ 31 ->
  0 <= ds_pending_out X -> ds_pending_out X + len <= PBL -> 0 <= cs_total_out (ds_strm X) < 2 ^ 64 ->
  exists R,
    msteps s6_segs (mkst regs (0x17cc8 : word) M0 s6_rom) (mkst R (0x17d10 : word) (Defl6_2.fp_tower S p zp M0 X len) s6_rom)
    /\ FPREGS R
    /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14]%bv = false -> getr R r = getr regs r).
Proof using HWF HP HH HF ra.
  intros regs m1 M0 X len HDI (P8 & P9 & P2 & P20) Q18 Hlen Hpd Hav Hpo0 Hpo1 Htot. open_di HDI.
  pose proof (wf_lbs _ HWF) as Wlbs.
  sc_cell Hsc ds6_pending C40. sc_cell Hsc ds6_pending_out C32. sc_cell Hsc ds6_pending_buf C16.
  zs_cell Zs (@zsl_avail_out) Z32. zs_cell Zs (@zsl_next_out) Z24. zs_cell Zs (@zsl_total_out) Z40.
  assert (P2' : getr regs 2 = zw (SP + -32)) by (rewrite P2; f_equal; lia).
  apartF 1%nat 6%nat A16.
  unfold Defl6_2.fp_tower.
  Local Ltac fpnd_fin R Hms HR Hfr :=
    rewrite ?le_bytes_sx32 in Hms;
    exists R; split; [exact Hms|]; split; [unfold FPREGS; repeat split; reg1 HR Hfr | fr_weak Hfr].
  destruct (Z.eqb_spec (ds_pending X - len) 0) as [Hz|Hnz].
  - run_gen (FPINS ++ [(18, EVar 36%nat)]) 30%nat [false]
      [RVal (EVar 37); RVal (EVar 39); RVal (EVar 40); RVal (EVar 38); RVal (EVar 41); RVal (EVar 42)]
      [(36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 31); (40%nat, 2 ^ 64); (41%nat, 2 ^ 31); (42%nat, 2 ^ 63)]
      [len; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X; cs_avail_out (ds_strm X); cs_total_out (ds_strm X); ds_pending X; PB].
    clear_aparts. fpnd_fin R Hms HR Hfr.
  - run_gen (FPINS ++ [(18, EVar 36%nat)]) 30%nat [true]
      [RVal (EVar 37); RVal (EVar 39); RVal (EVar 40); RVal (EVar 38); RVal (EVar 41); RVal (EVar 42)]
      [(36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 31); (40%nat, 2 ^ 64); (41%nat, 2 ^ 31); (42%nat, 2 ^ 63)]
      [len; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X; cs_avail_out (ds_strm X); cs_total_out (ds_strm X); ds_pending X; PB].
    clear_aparts. fpnd_fin R Hms HR Hfr.
Qed.


Lemma fpn_e : forall regs (regs0 : bvmap 5 word) m1 m X (r : word),
  DI m1 m X -> FPS m regs0 -> FPREGS regs -> getr regs0 1 = r -> ret_ok r ->
  getr regs0 8 = zw S -> getr regs0 9 = zw strm ->
  exists R,
    msteps s6_segs (mkst regs (0x17d10 : word) m s6_rom) (mkst R r m s6_rom)
    /\ HREGS R /\ getr R 1 = r /\ getr R 18 = getr regs0 18 
    /\ (forall r' : reg, reg_in r' [1; 2; 8; 9; 18]%bv = false -> getr R r' = getr regs r').
Proof using HP HH HF ra.
  intros regs regs0 m1 m X r HDI (C1 & C8 & C9 & C18) (P8 & P9 & P2 & P20) P1 Hret Q8 Q9. open_di HDI.
  rewrite P1 in C1. rewrite Q8 in C8. rewrite Q9 in C9. rewrite u_zw_small in C8 by lia. rewrite u_zw_small in C9 by lia.
  pose proof (u64_range r) as U1. pose proof (u64_range (getr regs0 18)) as U18.
  assert (P2' : getr regs 2 = zw (SP + -32)) by (rewrite P2; f_equal; lia).
  run_gen FPINS 20%nat NoDirs
    [RVal (EVar 36); RVal (EVar 32); RVal (EVar 35); RVal (EVar 37)]
    [(36%nat, 2 ^ 64); (37%nat, 2 ^ 64)]
    [bv_unsigned r; bv_unsigned (getr regs0 18)].
  exists R. split; [exact Hms|]. split; [unfold Defl6_1.HREGS; repeat split; reg1 HR Hfr|].
  repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Definition FP_CLOB : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Definition fp_pre (X : deflate_state) : Prop :=
  let X1 := tr_flush_bits X in
  BINV PBL X /\ 0 <= ds_pending X1 <= PBL /\ ds_pending X1 < 2 ^ 31 /\ 0 <= ds_pending_out X1 /\ ds_pending_out X1 + ds_pending X1 <= PBL
  /\ 0 <= cs_avail_out (ds_strm X1) < 2 ^ 31 /\ 0 <= cs_total_out (ds_strm X1) < 2 ^ 64.

Theorem call_fpn : forall regs m1 m X (r : word),
  DI m1 m X -> HREGS regs -> getr regs 10 = zw strm -> getr regs 1 = r -> ret_ok r -> fp_pre X ->
  exists R M,
    msteps s6_segs (mkst regs (0x17c80 : word) m s6_rom) (mkst R r M s6_rom)
    /\ DI m1 M (flush_pending X)
    /\ HREGS R /\ getr R 1 = r
    /\ (forall r' : reg, reg_in r' FP_CLOB = false -> getr R r' = getr regs r').
Proof using HWF HP HH TFBITS MEMCPY HF ra.
  intros regs m1 m X r HDI HRG P10 P1 Hret (HBI & Hp1 & Hp31 & Hpo0 & Hpo1 & Hav & Htot).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN). unfold DEFL_K6 in Hsp.
  pose proof (wf_lbs _ HWF) as Wlbs. pose proof HRG as (Q8 & Q2 & Q9 & Q20).
  destruct (fpn_a regs m1 m X HDI HRG P10) as (R1 & M1 & Hms1 & HDI1 & HFPS1 & A8 & A9 & A2 & A20 & A10 & A1 & Hfr1).
  destruct (call_bits _ _ _ _ _ _ _ _ _ _ _ TFBITS HH R1 m1 M1 X (0x17ca4%bv : word) HDI1
              ltac:(apply ret_ok_even; reflexivity) HBI ltac:(lia) A10 A1) as (R2 & M2 & Hms2 & HDI2 & Hfr2 & Hag2).
  assert (HFPS2 : FPS M2 regs).
  { apartF 0%nat 1%nat A01. apartF 0%nat 5%nat A05.
    eapply (FPS_agree (Fbits S p ds) M1 M2 regs HFPS1 Hag2); [| lia | lia].
    unfold Fbits, ds6_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia. }
  set (X1 := tr_flush_bits X) in *.
  assert (FR2 : FPREGS R2).
  { unfold FPREGS. rewrite !Hfr2 by reflexivity. repeat split; assumption. }
  destruct (fpn_c R2 m1 M2 X1 HDI2 FR2 ltac:(lia) ltac:(lia) ltac:(lia)) as (R3 & Hms3 & FR3 & Hnz3 & Hfr3).
  rewrite DeflM.flush_pending_eq. cbv zeta. fold X1. unfold fpa_pc in Hms3.
  destruct (fp_len X1 =? 0) eqn:Efl.
  -
    destruct (fpn_e R3 regs m1 M2 X1 r HDI2 HFPS2 FR3 P1 Hret Q8 Q9) as (R4 & Hms4 & HRG4 & B1 & B18 & Hfr4).
    exists R4, M2. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3 | exact Hms4]. }
    split; [exact HDI2|]. split; [exact HRG4|]. split; [exact B1|].
    destruct HRG4 as (C8 & C2 & C9 & C20). unfold FP_CLOB. reg_frame.
  - apply Z.eqb_neq in Efl. destruct (Hnz3 Efl) as (B10 & B11 & B12 & B18 & B1).
    pose proof (DeflSlow6_6.fp_len_eq X1 ltac:(lia) ltac:(lia)) as (_ & Hfl1 & Hfl2).
    remember (Z.to_nat (fp_len X1)) as n eqn:En. assert (EL : fp_len X1 = Z.of_nat n) by lia. rewrite EL in *.
    destruct (call_mc _ _ _ _ _ _ _ _ _ _ _ MEMCPY HH R3 m1 M2 X1 n (0x17cc8%bv : word) HDI2 ltac:(apply ret_ok_even; reflexivity)
                ltac:(lia) ltac:(lia) ltac:(lia) B1 B10 B11 B12) as (R4 & Hms4 & C10 & Hfr4).
    set (M3 := wbytes M2 _ _) in Hms4.
    assert (HDI3 : DI M3 M3 X1).
    { subst M3. apply (DI_out_self _ _ _ _ _ _ _ _ _ _ _ HH m1 M2 X1 _ HDI2). rewrite fbytes_length. lia. }
    assert (HFPS3 : FPS M3 regs).
    { subst M3. pose proof HDI2 as (_ & (_ & _ & _ & _ & _ & _ & _ & HC) & _). destruct HC as (_ & _ & _ & _ & Eout & Hao & Hol).
      apartF 0%nat 7%nat A07. apply FPS_write_other; rewrite ?fbytes_length; [exact HFPS2 | lia | lia | lia | lia]. }
    assert (FR4 : FPREGS R4).
    { unfold FPREGS. rewrite !Hfr4 by reflexivity. exact FR3. }
    destruct (fpn_d R4 M3 M3 X1 (Z.of_nat n) HDI3 FR4 ltac:(rewrite (Hfr4 18%bv eq_refl); exact B18)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (R5 & Hms5 & FR5 & Hfr5).
    assert (HDI5 : DI m1 (Defl6_2.fp_tower S p zp M3 X1 (Z.of_nat n)) (fp_tail X1 (Z.of_nat n))).
    { pose proof (fp_finish _ _ _ _ _ _ _ _ _ _ _ HH m1 M2 X1 n (cs_total_out (ds_strm X1) + Z.of_nat n) HDI2
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)) as HD6.
      cbv zeta in HD6. subst M3. unfold Defl6_2.fp_tower. cbv zeta. exact HD6. }
    assert (HFPS5 : FPS (Defl6_2.fp_tower S p zp M3 X1 (Z.of_nat n)) regs).
    { apartF 0%nat 1%nat A01. apartF 0%nat 6%nat A06. unfold Defl6_2.fp_tower. cbv zeta.
      destruct (ds_pending X1 - Z.of_nat n =? 0);
        repeat (apply FPS_write_other; rewrite ?length_Z_to_le_bytes; [| lia | cbn; lia | cbn; lia | lia]); exact HFPS3. }
    destruct (fpn_e R5 regs m1 _ _ r HDI5 HFPS5 FR5 P1 Hret Q8 Q9) as (R6 & Hms6 & HRG6 & D1 & D18 & Hfr6).
    exists R6, (Defl6_2.fp_tower S p zp M3 X1 (Z.of_nat n)). split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
      eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5 | exact Hms6]. }
    split; [exact HDI5|]. split; [exact HRG6|]. split; [exact D1|].
    destruct HRG6 as (C8 & C2 & C9 & C20). unfold FP_CLOB. reg_frame.
Qed.

End Walk.
End FXG.

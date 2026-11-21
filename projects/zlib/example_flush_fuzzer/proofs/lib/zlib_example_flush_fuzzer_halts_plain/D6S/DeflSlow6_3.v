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
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  ZIface DeflateState Trees TreeModel SendModel DeflateLz DeflateBlk LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 Callee6 TreesRod6 TreesApi6 DeflBlkApi6 DeflSlow6_1 DeflSlow6_2.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Lemma sx32_u64_le_wrap : forall d k, 0 <= k < 2 ^ 31 -> (szwrap 32 d mod 2 ^ 64 <= k <-> wrap32 d <= k).
Proof using.
  intros d k Hk. rewrite <- (szwrap_mod 32 d) by lia. rewrite wrap32_mod.
  pose proof (Z.mod_pos_bound d (2 ^ 32) ltac:(lia)) as Hd. set (d' := d mod 2 ^ 32) in *. clearbody d'.
  unfold szwrap. change (2 ^ (32 - 1)) with (2 ^ 31).
  destruct (Z_lt_le_dec d' (2 ^ 31)) as [L|G].
  - rewrite (Z.mod_small (d' + 2 ^ 31)) by lia. replace (d' + 2 ^ 31 - 2 ^ 31) with d' by lia.
    rewrite Z.mod_small by lia. tauto.
  - replace ((d' + 2 ^ 31) mod 2 ^ 32) with (d' + 2 ^ 31 - 2 ^ 32).
    2: { rewrite <- (Z.mod_add _ (-1)) by lia. symmetry. rewrite Z.mod_small by lia. lia. }
    rewrite zmod64_neg by lia. split; intros; lia.
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
Local Abbreviation SP := (sp - 128).
Hypothesis HH : DSH ROM mem S p zp ds flush ra sp.
Local Abbreviation DI := (DeflSlow6_1.DI ROM mem S p zp ds sp).
Local Abbreviation BRm := (BR s6_segs 168672 168704 168736 (DeflSlow6_1.Fd S p zp ds sp) mem S p PBL).
Local Abbreviation RZ := (DeflSlow6_1.RZ ROM mem S p zp ds sp).

Let HL : ZRH6 DSLOW_FRAME6 mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ HH.
Local Abbreviation HREGS := (DeflSlow6_1.HREGS S sp).
Local Abbreviation DI_eqst := (DeflSlow6_1.DI_eqst ROM mem S p zp ds sp).
Local Abbreviation LOC := (DeflSlow6_2.LOC4 sp).

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac hregs_via HRG Hfr := apply (HREGS_via S sp _ _ _ HRG Hfr); reflexivity.

Local Ltac nf := cbn [dfF].

Local Ltac rod_read :=
  lazymatch goal with
  | |- exists bs, rdn _ ?m (zw ?a) _ = Some bs /\ bytes_le_to_Z bs = arr_get length_code_a ?i =>
      eapply (length_code_read R6 s6_segs m trod_ok6 ltac:(eassumption) i a); first [reflexivity | cbn [tr_length_code R6]; lia]
  | |- exists bs, rdn _ ?m (zw ?a) _ = Some bs /\ bytes_le_to_Z bs = arr_get dist_code_a ?i =>
      eapply (dist_code_read R6 s6_segs m trod_ok6 ltac:(eassumption) i a); first [reflexivity | cbn [tr_dist_code R6]; lia]
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
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs DeflSlow6_2.dsC6 fuel dirs rdv pins vb NoRegions pv NoVals
          (dfF (ds_window X) (ds_head X) (ds_dyn_ltree_fc X) (ds_dyn_dtree_fc X)) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
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
  let HRT := fresh "HRT" in let HGOT := fresh "HGOT" in pose proof (proj1 HRC) as HRT; pose proof (proj2 HRC) as HGOT; unfold got6_clear in HGOT;
  let Lw := fresh "Lw" in let Lp := fresh "Lp" in let Lh := fresh "Lh" in
  let Ein := fresh "Ein" in let Eout := fresh "Eout" in let Hao := fresh "Hao" in let Hol := fresh "Hol" in
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol); rewrite Lw in Cw; rewrite Lp in Cp; rewrite Lh in Ch;
  let RF := fresh "RF" in
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in let HW := fresh "HW" in let HPV := fresh "HPV" in let HHD := fresh "HHD" in
  let HPB := fresh "HPB" in let Hstrm := fresh "Hstrm" in let HOUT := fresh "HOUT" in let HIN := fresh "HIN" in
  destruct RF as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN);
  let RODS := fresh "RODS" in pose proof (mapped_rod_apart R6 s6_segs _ S 5968 trod_ok6 HRT MS ltac:(lia) ltac:(lia)) as RODS;
  let RODP := fresh "RODP" in pose proof (mapped_rod_apart R6 s6_segs _ (p_pending_buf p) PBL trod_ok6 HRT MP ltac:(lia) ltac:(pose proof (wf_lbs _ HWF); lia)) as RODP;
  cbn [tr_lo tr_hi tr_sdesc R6] in RODS, RODP; apply hide in RODS; apply hide in RODP;
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ HH) as Hfl;
  let HGR := fresh "HGR" in pose proof HRZ as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & HGR) & _);
  let MWm := fresh "MWm" in let MPm := fresh "MPm" in let MHm := fresh "MHm" in let MZm := fresh "MZm" in
  let T := fresh "T" in
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ HH 2 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MWm; cbv beta in MWm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ HH 3 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MPm; cbv beta in MPm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ HH 4 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MHm; cbv beta in MHm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ HH 6 ltac:(lia)) as T; unfold ZRF, zsl_SIZE in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MZm; cbv beta in MZm; clear T.

Local Ltac apartF i j H :=
  pose proof (apart_ij _ _ _ _ _ _ _ _ _ HH i j ltac:(lia) ltac:(lia)) as H;
  unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE, DSLOW_FRAME6 in H.

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P21 := fresh "P21" in let P22 := fresh "P22" in
  let P27 := fresh "P27" in let P20 := fresh "P20" in let P23 := fresh "P23" in let P24 := fresh "P24" in let P26 := fresh "P26" in
  pose proof HRG as (P8 & P2 & P21 & P22 & P27 & P20 & P23 & P24 & P26).

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
          | H1 : DeflSlow6_1.DI _ ?mem ?S ?p ?zp ?ds ?sp ?m1 M1 ?X |- _ =>
              let H2 := fresh "HDI" in
              lazymatch k with
              | KInsH => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_ins_h ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KBlockStart => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_block_start ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KMatchLength => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_match_length ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KStrstart => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_strstart ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KLookahead => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_lookahead ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KInsert => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_insert ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KSymNext => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_sym_next ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPending => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_pending ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPrevLength => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_prev_length ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPrevMatch => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_prev_match ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KMatchAvailable => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_match_available ROM mem S p zp ds _ _ sp HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPendingOut ?off => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_pending_out ROM mem S p zp ds _ _ sp HH m1 M1 X off a v H1 ltac:(lia) ltac:(lia)) as H2 end
              | KPb ?i ?c' => lazymatch bs with Z_to_le_bytes _ ?c =>
                  pose proof (DI_st_pb ROM mem S p zp ds _ _ sp HH m1 M1 X a i c c' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KFc ?t ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_fc ROM mem S p zp ds _ _ sp HH m1 M1 X a t i v v' H1 ltac:(cbn [toff]; lia) ltac:(cbn [tsize]; lia) ltac:(mod_side)) as H2 end
              | KPrev ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_prev ROM mem S p zp ds _ _ sp HH m1 M1 X a i v v' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KHead ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_head ROM mem S p zp ds _ _ sp HH m1 M1 X a i v v' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KFrame => pose proof (DI_st_frame ROM mem S p zp ds _ _ sp HH m1 M1 X a bs H1 ltac:(lia)
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
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in
  destruct RF as (Hsp & HS & _);
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ HH) as Hfl.

Local Ltac ex1 := lazymatch goal with H : msteps _ _ (mkst ?R _ _ _) |- _ => exists R end.
Local Ltac ex2 := lazymatch goal with H : msteps _ _ (mkst ?R _ ?M _) |- _ => exists R, M end.

Ltac norm_sx H := rewrite ?le_bytes_sx32 in H.


Local Abbreviation PLR := (DeflSlow6_2.PLR).
Local Abbreviation prev_st := (DeflSlow6_2.prev_st).


Definition lm_filter (X : deflate_state) (ml : Z) : bool :=
  (ml <=? 5) && ((ds_strategy X =? 1) || ((ml =? 3) && (4096 <? wrap32 (ds_strstart X - ds_match_start X)))).

Definition lmret_pc (X : deflate_state) (ml : Z) : word :=
  if lm_filter X ml then (0x19704 : word) else (0x1972c : word).

Lemma lmret_blk : forall regs m1 m X ml,
  DI m1 m X -> HREGS regs -> LOC m1 -> getr regs 10 = zw ml -> 0 <= ml <= 258 -> 0 <= ds_strategy X <= 4 ->
  0 <= ds_strstart X <= 2 * ws -> 0 <= ds_match_start X < 2 ^ 32 ->
  exists R M,
    msteps s6_segs (mkst regs (0x196ec : word) m s6_rom) (mkst R (lmret_pc X ml) M s6_rom)
    /\ DI m1 M (set_match_length X ml)
    /\ HREGS R /\ (lm_filter X ml = false -> getr R 10 = zw ml)
    /\ (forall r : reg, reg_in r [10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra.
  intros regs m1 m X ml HDI HRG HLOC Q10 Hml Hst Hstr Hms0. open_di HDI. open_hregs HRG. pose proof (wf_wsz _ HWF) as Wws.
  pose proof (ds6_strategy _ _ _ _ Hsc) as C200. pose proof (ds6_strstart _ _ _ _ Hsc) as C172. pose proof (ds6_match_start _ _ _ _ Hsc) as C176.
  pose proof (LOC4_DI _ _ _ _ _ _ _ _ _ HH m1 m X HLOC HDI) as (F16 & F8).
  assert (Hc2 : szwrap 32 (ds_strstart X - ds_match_start X) mod 2 ^ 64 <= 4096 <-> wrap32 (ds_strstart X - ds_match_start X) <= 4096)
    by (apply sx32_u64_le_wrap; lia).
  apartF 0%nat 1%nat A01.
  Local Ltac lmret_fin HDI Hms HRG HR Hfr X ml :=
    clear_aparts;
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KMatchLength];
    lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end;
    split; [exact Hms|];
    split; [lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => exact H end|];
    split; [hregs_via HRG Hfr|];
    split; [let HX := fresh "HX" in intros HX; first [exfalso; discriminate HX | reg1 HR Hfr]|];
    fr_weak Hfr.
  unfold lmret_pc, lm_filter.
  destruct (Z.leb_spec ml 5) as [M5|M5]; cbn [andb].
  2: { run 6%nat [true] NoReads [(10, EVar 35%nat)] [(35%nat, 259)] [ml] X. lmret_fin HDI Hms HRG HR Hfr X ml. }
  destruct (Z.eqb_spec (ds_strategy X) 1) as [S1|S1]; cbn [orb].
  { rewrite S1 in C200.
    run 8%nat [false; false] [RVal (ELit 1)] [(10, EVar 35%nat)] [(35%nat, 259)] [ml] X. lmret_fin HDI Hms HRG HR Hfr X ml. }
  destruct (Z.eqb_spec ml 3) as [M3|M3]; cbn [andb].
  2: { run 8%nat [false; true; true] [RVal (EVar 36)] [(10, EVar 35%nat)] [(35%nat, 259); (36%nat, 5)] [ml; ds_strategy X] X.
       lmret_fin HDI Hms HRG HR Hfr X ml. }
  subst ml.
  destruct (Z.ltb_spec 4096 (wrap32 (ds_strstart X - ds_match_start X))) as [Far|Near].
  - run 14%nat [false; true; false; true] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (ELit 4097)] [(10, ELit 3)]
        [(36%nat, 5); (37%nat, 65537); (38%nat, 2 ^ 32)] [0; ds_strategy X; ds_strstart X; ds_match_start X] X.
    lmret_fin HDI Hms HRG HR Hfr X 3.
  - run 14%nat [false; true; false; false] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (ELit 4097)] [(10, ELit 3)]
        [(36%nat, 5); (37%nat, 65537); (38%nat, 2 ^ 32)] [0; ds_strategy X; ds_strstart X; ds_match_start X] X.
    lmret_fin HDI Hms HRG HR Hfr X 3.
Qed.

Lemma lm2_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs ->
  exists R M,
    msteps s6_segs (mkst regs (0x19704 : word) m s6_rom) (mkst R (0x1972c : word) M s6_rom)
    /\ DI m1 M (set_match_length X 2)
    /\ HREGS R /\ getr R 10 = zw 2
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG. open_di HDI. open_hregs HRG.
  run 4%nat NoDirs NoReads NoPins NoBounds (@nil Z) X.
  clear_aparts.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KMatchLength].
  ex2. split; [exact Hms|]. split; [lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => exact H end|].
  split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.


Lemma pl_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw (ds_match_length X) -> 0 <= ds_prev_length X <= 258 ->
  exists R,
    msteps s6_segs (mkst regs (0x1972c : word) m s6_rom) (mkst R (0x19730 : word) m s6_rom)
    /\ HREGS R /\ PLR R X
    /\ (forall r : reg, reg_in r [12]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Q10 Hpl. open_di HDI. open_hregs HRG.
  pose proof (ds6_prev_length _ _ _ _ Hsc) as C184.
  run 3%nat NoDirs [RVal (EVar 35)] NoPins [(35%nat, 259)] [ds_prev_length X] X.
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [split; [rewrite (Hfr 10%bv eq_refl); exact Q10 | reg1 HR Hfr] | fr_weak Hfr].
Qed.

Definition dec_cond (X : deflate_state) : bool := (3 <=? ds_prev_length X) && (ds_match_length X <=? ds_prev_length X).

Definition dec_pc (X : deflate_state) : word := if dec_cond X then (0x19738 : word) else (0x198c0 : word).

Lemma dec_blk : forall regs m X,
  HREGS regs -> PLR regs X -> 0 <= ds_prev_length X <= 258 -> 0 <= ds_match_length X <= 258 ->
  exists R,
    msteps s6_segs (mkst regs (0x19730 : word) m s6_rom) (mkst R (dec_pc X) m s6_rom)
    /\ HREGS R /\ PLR R X
    /\ (forall r : reg, reg_in r []%bv = false -> getr R r = getr regs r).
Proof using HH ra flush ds zp p mem ROM.
  intros regs m X HRG [Q10 Q12] Hpl Hml. open_hregs HRG. open_min.
  unfold dec_pc, dec_cond.
  destruct (Z.leb_spec 3 (ds_prev_length X)) as [P3|P3]; cbn [andb].
  - destruct (Z.leb_spec (ds_match_length X) (ds_prev_length X)) as [PM|PM].
    + run 4%nat [false; false] NoReads [(10, EVar 35%nat); (12, EVar 36%nat)] [(35%nat, 259); (36%nat, 259)] [ds_match_length X; ds_prev_length X] X.
      ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [split; reg1 HR Hfr | fr_weak Hfr].
    + run 4%nat [false; true] NoReads [(10, EVar 35%nat); (12, EVar 36%nat)] [(35%nat, 259); (36%nat, 259)] [ds_match_length X; ds_prev_length X] X.
      ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [split; reg1 HR Hfr | fr_weak Hfr].
  - run 4%nat [true] NoReads [(10, EVar 35%nat); (12, EVar 36%nat)] [(35%nat, 259); (36%nat, 259)] [ds_match_length X; ds_prev_length X] X.
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [split; reg1 HR Hfr | fr_weak Hfr].
Qed.


Definition mavail_pc (X : deflate_state) : word :=
  if ds_match_available X =? 0 then (0x19998 : word) else (0x198c8 : word).

Lemma mavail_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= ds_match_available X <= 1 ->
  exists R,
    msteps s6_segs (mkst regs (0x198c0 : word) m s6_rom) (mkst R (mavail_pc X) m s6_rom)
    /\ HREGS R
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Hma. open_di HDI. open_hregs HRG.
  pose proof (ds6_match_available _ _ _ _ Hsc) as C168.
  unfold mavail_pc. destruct (Z.eqb_spec (ds_match_available X) 0) as [Hz|Hnz].
  - run 4%nat [true] [RVal (EVar 35)] NoPins [(35%nat, 2)] [ds_match_available X] X.
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr | fr_weak Hfr].
  - run 4%nat [false] [RVal (EVar 35)] NoPins [(35%nat, 2)] [ds_match_available X] X.
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr | fr_weak Hfr].
Qed.

Definition avail0_st (X : deflate_state) : deflate_state :=
  set_lookahead (set_strstart (set_match_available X 1) (ds_strstart X + 1)) (ds_lookahead X - 1).

Lemma avail0_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs ->
  0 <= ds_strstart X -> 1 <= ds_lookahead X -> ds_strstart X + ds_lookahead X <= 2 * ws ->
  exists R M,
    msteps s6_segs (mkst regs (0x19998 : word) m s6_rom) (mkst R (0x19600 : word) M s6_rom)
    /\ DI m1 M (avail0_st X)
    /\ HREGS R
    /\ (forall r : reg, reg_in r [10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Hs0 Hl1 Hsl. open_di HDI. open_hregs HRG. pose proof (wf_wsz _ HWF) as Wws.
  pose proof (ds6_strstart _ _ _ _ Hsc) as C172. pose proof (ds6_lookahead _ _ _ _ Hsc) as C180.
  run 12%nat NoDirs [RVal (EVar 35); RVal (EVar 36)] NoPins [(35%nat, 65537); (36%nat, 65537)] [ds_strstart X; ds_lookahead X] X.
  clear_aparts.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KMatchAvailable; KStrstart; KLookahead].
  ex2. split; [exact Hms|].
  split.
  { lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end.
    unfold avail0_st. st_close idtac. }
  split; [hregs_via HRG Hfr | fr_weak Hfr].
Qed.


Definition slit1 (X : deflate_state) : deflate_state :=
  let sn := ds_sym_next X in
  let lb := ds_lit_bufsize X in
  let c := arr_get (ds_window X) (ds_strstart X - 1) in
  let X1 := set_sym_next X (sn + 1) in
  let X2 := set_pending_buf X1 (arr_set (ds_pending_buf X) (lb + sn) (wrap8 0)) in
  let X3 := set_sym_next X2 (sn + 2) in
  let X4 := set_pending_buf X3 (arr_set (ds_pending_buf X2) (lb + sn + 1) (wrap8 0)) in
  let X5 := set_sym_next X4 (sn + 3) in
  let X6 := set_pending_buf X5 (arr_set (ds_pending_buf X4) (lb + sn + 2) (wrap8 (wrap8 c))) in
  set_dyn_ltree_fc X6 (arr_set (ds_dyn_ltree_fc X) (wrap8 c) (wrap16 (arr_get (ds_dyn_ltree_fc X) (wrap8 c) + 1))).

Definition slit_pc (X : deflate_state) : word :=
  if ds_sym_next X + 3 =? ds_sym_end X then (0x1994c : word) else (0x195dc : word).

Lemma slit_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs ->
  1 <= ds_strstart X <= 2 * ws ->
  0 <= ds_sym_next X -> ds_sym_next X + 3 <= 3 * lbs -> 0 <= ds_sym_end X < 2 ^ 18 ->
  (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256) ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc X) i < 65536) ->
  exists R M,
    msteps s6_segs (mkst regs (0x198c8 : word) m s6_rom) (mkst R (slit_pc X) M s6_rom)
    /\ DI m1 M (slit1 X)
    /\ HREGS R
    /\ (forall r : reg, reg_in r [10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Hstr Hsn0 Hsn3 Hse Hwb Hfc.
  open_di HDI. open_hregs HRG.
  pose proof (wf_wsz _ HWF) as Wws. pose proof (wf_lbs _ HWF) as Wlbs.
  pose proof (ds6_window _ _ _ _ Hsc) as C96. pose proof (ds6_strstart _ _ _ _ Hsc) as C172.
  pose proof (ds6_sym_buf _ _ _ _ Hsc) as C5888. rewrite Elbs in C5888. pose proof (ds6_sym_end _ _ _ _ Hsc) as C5904.
  pose proof (ds6_sym_next _ _ _ _ Hsc) as C5900.
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
    split; [ lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end;
             unfold slit1; rewrite Elbs; subst str sn; rewrite <- Ec; st_close ltac:(rewrite Ecc) |];
    split; [hregs_via HRG Hfr | fr_weak Hfr].
  destruct (Z.eqb_spec (sn + 3) (ds_sym_end X)) as [Hbf|Hnbf].
  - runT 50%nat [false]
      [RVal (EAdd (EVar 35%nat) (ELit 1)); RVal (EAdd (EVar 38%nat) (EVar 39%nat)); RVal (EVar 37); RVal (EVar 40);
       RVal (EApp1 0%nat (EVar 35)); RVal (EApp1 2%nat (EApp1 0%nat (EVar 35))); RVal (EVar 42)]
      [(22, EVar 43%nat); (21, EVar 44%nat)]
      [(35%nat, 65536); (37%nat, 2 ^ 18); (38%nat, 2 ^ 63); (39%nat, 2 ^ 16); (40%nat, 2 ^ 63); (42%nat, 2 ^ 18); (43%nat, 2 ^ 63); (44%nat, 2 ^ 63)]
      [str - 1; 0; sn; PB; lbs; W; 0; ds_sym_end X; S + 212; S + 5888]
      X.
    lit_fin HDI Hms HRG HR Hfr X str sn c Ec Ecc Elbs.
  - runT 50%nat [true]
      [RVal (EAdd (EVar 35%nat) (ELit 1)); RVal (EAdd (EVar 38%nat) (EVar 39%nat)); RVal (EVar 37); RVal (EVar 40);
       RVal (EApp1 0%nat (EVar 35)); RVal (EApp1 2%nat (EApp1 0%nat (EVar 35))); RVal (EVar 42)]
      [(22, EVar 43%nat); (21, EVar 44%nat)]
      [(35%nat, 65536); (37%nat, 2 ^ 18); (38%nat, 2 ^ 63); (39%nat, 2 ^ 16); (40%nat, 2 ^ 63); (42%nat, 2 ^ 18); (43%nat, 2 ^ 63); (44%nat, 2 ^ 63)]
      [str - 1; 0; sn; PB; lbs; W; 0; ds_sym_end X; S + 212; S + 5888]
      X.
    lit_fin HDI Hms HRG HR Hfr X str sn c Ec Ecc Elbs.
Qed.

End Walk.
End FXG.

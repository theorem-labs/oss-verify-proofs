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
  RomRead TreesRod FlushBlockModel BitsLib DeflM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 Callee6 TreesRod6 TreesApi6 DeflBlkApi6 DeflSlow6_1 DeflSlow6_2 DeflSlow6_3 DeflSlow6_5.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.


Lemma wrap32_range' : forall z, 0 <= wrap32 z < 2 ^ 32.
Proof using. intros z. rewrite wrap32_mod. apply Z.mod_pos_bound. lia. Qed.

Lemma cell_low4 : forall segs m a v, cell segs m a 8 v -> 0 <= a -> a + 8 <= 2 ^ 64 -> cell segs m a 4 v.
Proof using.
  intros segs m a v H Ha Ha8. unfold cell in *.
  pose proof (rdn_firstn segs m 8 (zw a) _ 4 H ltac:(lia)) as H4. exact H4.
Qed.

Lemma sxm16 : forall a, (szwrap 16 a) mod 65536 = a mod 65536.
Proof using. intros a. rewrite <- (Z.add_0_r (szwrap 16 a)). rewrite sxaddm16. f_equal. lia. Qed.

End FXG.
Ltac unhide H := unfold hidden in H.
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
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 | rewrite sxaddm16 | rewrite sxaddm8 | rewrite sxm16 ].

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
Local Abbreviation ins_str := (DeflSlow6_2.ins_str).
Local Abbreviation ILS := (DeflSlow6_5.ILS).


Definition insl_st (X : deflate_state) (mi : Z) : deflate_state :=
  set_prev_length (if ds_strstart X + 1 <=? mi then ins_str (set_strstart X (ds_strstart X + 1)) (ds_strstart X + 1)
                   else set_strstart X (ds_strstart X + 1))
                  (ds_prev_length X - 1).

Definition insl_pc (X : deflate_state) : word :=
  if ds_prev_length X =? 1 then (0x19968 : word) else (0x19850 : word).

Lemma insl_strstart : forall X mi, ds_strstart (insl_st X mi) = ds_strstart X + 1.
Proof using. intros X mi. unfold insl_st, DeflSlow6_2.ins_str. destruct (_ <=? _); dsred; reflexivity. Qed.
Lemma insl_prev_length : forall X mi, ds_prev_length (insl_st X mi) = ds_prev_length X - 1.
Proof using. intros X mi. unfold insl_st, DeflSlow6_2.ins_str. destruct (_ <=? _); dsred; reflexivity. Qed.


Lemma insl_blk : forall regs m1 m X mi sn se,
  DI m1 m X -> HREGS regs -> ILS regs (ds_strstart X + 1) mi (ds_prev_length X - 1) sn se ->
  1 <= ds_prev_length X <= 258 -> 0 <= ds_strstart X -> ds_strstart X + 2 < 2 ^ 31 ->
  (ds_strstart X + 1 <= mi -> ds_strstart X + 4 <= 2 * ws) -> 0 <= mi < 2 ^ 32 ->
  0 <= ds_ins_h X < 2 ^ 31 -> ds_hash_mask X = hs - 1 -> ds_w_mask X = ws - 1 -> 0 <= ds_hash_shift X < 32 ->
  0 <= sn < 2 ^ 32 -> 0 <= se < 2 ^ 32 ->
  (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256) ->
  (forall j, 0 <= j < hs -> 0 <= arr_get (ds_head X) j < 65536) ->
  exists R M,
    msteps s6_segs (mkst regs (0x19850 : word) m s6_rom) (mkst R (insl_pc X) M s6_rom)
    /\ DI m1 M (insl_st X mi)
    /\ HREGS R /\ ILS R (ds_strstart (insl_st X mi) + 1) mi (ds_prev_length (insl_st X mi) - 1) sn se
    /\ (forall r : reg, reg_in r [5; 6; 7; 10; 14; 15; 16; 17; 28]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X mi sn se HDI HRG HIL Hpl Hs0 Hs31 Hs4 Hmi Hih Hhm Hwm Hsh Hsn Hse Hwb Hhb.
  destruct HIL as (I10 & I13 & I14 & I11 & I12).
  open_di HDI. open_hregs HRG.
  pose proof (wf_wsz _ HWF) as Wws. pose proof (wf_hsz _ HWF) as Whs.
  pose proof (ds6_window _ _ _ _ Hsc) as C96. pose proof (ds6_hash_shift _ _ _ _ Hsc) as C144. pose proof (ds6_ins_h _ _ _ _ Hsc) as C128.
  pose proof (ds6_hash_mask _ _ _ _ Hsc) as C140. pose proof (ds6_w_mask _ _ _ _ Hsc) as C88.
  pose proof (ds6_head _ _ _ _ Hsc) as C120. pose proof (ds6_prev _ _ _ _ Hsc) as C112.
  rewrite Hhm in C140. rewrite Hwm in C88.
  rewrite insl_strstart, insl_prev_length. unfold insl_pc, insl_st, DeflSlow6_2.ins_str.
  set (str := ds_strstart X) in *. set (pl := ds_prev_length X) in *.
  set (hx := Z.land (Z.lxor (zaluw ALU_SLL (ds_ins_h X) (ds_hash_shift X)) (wb (ds_window X) (str + 3))) (hs - 1)).
  assert (Epl : szwrap 32 (pl - 1 - 1) = pl - 1 - 1) by (rewrite szwrap_small; lia).
  assert (Es2 : szwrap 32 (str + 1 + 1) = str + 1 + 1) by (rewrite szwrap_small; lia).
  apartF 1%nat 2%nat A12. apartF 1%nat 3%nat A13. apartF 1%nat 4%nat A14.
  unhide RODS.
  destruct (Z.leb_spec (str + 1) mi) as [Hins|Hskip].
  -
    specialize (Hs4 Hins).
    assert (Ehx : hx = Z.land (Z.lxor (wrap32 (Z.shiftl (ds_ins_h X) (ds_hash_shift X))) (arr_get (ds_window X) (str + 1 + 2))) (ds_hash_mask X)).
    { subst hx. replace (str + 1 + 2) with (str + 3) by lia.
      rewrite (wb_get (ds_window X) ltac:(intros j Hj; apply Hwb; rewrite <- Lw; exact Hj)) by (rewrite Lw; lia).
      rewrite Hhm. apply uh_sllw; lia. }
    pose proof (land_mask_range (Z.lxor (zaluw ALU_SLL (ds_ins_h X) (ds_hash_shift X)) (wb (ds_window X) (str + 3))) (hs - 1) ltac:(lia)) as Rhx.
    fold hx in Rhx.
    set (Y := Z.land (str + 1) (ws - 1)).
    assert (RY : 0 <= Y <= ws - 1) by (subst Y; apply land_mask_range; lia).
    assert (Rph : 0 <= pb (ds_head X) hx < 65536) by (apply pb_range).
    Local Ltac ins_fin HDI Hms HRG HR Hfr X str hx Ehx Hwm Y Epl Es2 :=
      clear_aparts; rewrite ?dfF_0, ?dfF_1, ?dfF_2, ?dfF_3 in Hms; rewrite ?Epl, ?Es2 in Hms; norm_sx Hms;
      di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end)
        [KStrstart; KInsH; KPrev Y (arr_get (ds_head X) hx); KHead hx (wrap16 (str + 1)); KPrevLength];
      lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end;
      split; [exact Hms|];
      split;
      [ lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end;
        unfold update_hash; dsred; rewrite <- Ehx;
        st_close ltac:(first [subst hx; reflexivity | rewrite Hwm; apply Z.land_comm])
      | split; [hregs_via HRG Hfr|];
        split; [unfold DeflSlow6_5.ILS; dsred; repeat split; reg1 HR Hfr | fr_weak Hfr] ].
    destruct (Z.eqb_spec pl 1) as [H1|H1].
    + run 40%nat [false; true]
        [RVal (EVar 38); RVal (EVar 39); RVal (EVar 44); RVal (EVar 45); RVal (EVar 40); RVal (EApp1 0%nat (EAdd (EVar 35) (ELit 3)));
         RVal (EVar 43); RVal (EVar 41); RVal (EVar 46)]
        [(10, EAdd (EVar 35%nat) (ELit 1)); (13, EVar 37%nat); (14, EAdd (EVar 36%nat) (ELit (-1))); (11, EVar 47%nat); (12, EVar 48%nat)]
        [(35%nat, 2 ^ 31); (36%nat, 259); (37%nat, 2 ^ 32); (38%nat, 32); (39%nat, 2 ^ 63); (40%nat, 2 ^ 31); (41%nat, 65536);
         (43%nat, 65536); (44%nat, 2 ^ 63); (45%nat, 2 ^ 63); (46%nat, 65536); (47%nat, 2 ^ 32); (48%nat, 2 ^ 32)]
        [str; pl; mi; ds_hash_shift X; W; ds_ins_h X; hs - 1; 0; ws - 1; PV; HD; pb (ds_head X) hx; sn; se]
        X.
      all: try (rewrite ?H1; first [reflexivity | unhide A12; lia | unhide A13; lia | unhide A14; lia | lia]).
      ins_fin HDI Hms HRG HR Hfr X str hx Ehx Hwm Y Epl Es2.
    + run 40%nat [false; false]
        [RVal (EVar 38); RVal (EVar 39); RVal (EVar 44); RVal (EVar 45); RVal (EVar 40); RVal (EApp1 0%nat (EAdd (EVar 35) (ELit 3)));
         RVal (EVar 43); RVal (EVar 41); RVal (EVar 46)]
        [(10, EAdd (EVar 35%nat) (ELit 1)); (13, EVar 37%nat); (14, EAdd (EVar 36%nat) (ELit (-1))); (11, EVar 47%nat); (12, EVar 48%nat)]
        [(35%nat, 2 ^ 31); (36%nat, 259); (37%nat, 2 ^ 32); (38%nat, 32); (39%nat, 2 ^ 63); (40%nat, 2 ^ 31); (41%nat, 65536);
         (43%nat, 65536); (44%nat, 2 ^ 63); (45%nat, 2 ^ 63); (46%nat, 65536); (47%nat, 2 ^ 32); (48%nat, 2 ^ 32)]
        [str; pl; mi; ds_hash_shift X; W; ds_ins_h X; hs - 1; 0; ws - 1; PV; HD; pb (ds_head X) hx; sn; se]
        X.
      all: try (first [unhide A12; lia | unhide A13; lia | unhide A14; lia | lia]).
      ins_fin HDI Hms HRG HR Hfr X str hx Ehx Hwm Y Epl Es2.
  -
    Local Ltac skip_fin HDI Hms HRG HR Hfr Epl Es2 :=
      clear_aparts; rewrite ?Epl, ?Es2 in Hms; norm_sx Hms;
      di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KStrstart; KPrevLength];
      lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end;
      split; [exact Hms|];
      split;
      [ lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end; st_close idtac
      | split; [hregs_via HRG Hfr|];
        split; [unfold DeflSlow6_5.ILS; dsred; repeat split; reg1 HR Hfr | fr_weak Hfr] ].
    destruct (Z.eqb_spec pl 1) as [H1|H1].
    + run 12%nat [true; true] NoReads
        [(10, EAdd (EVar 35%nat) (ELit 1)); (13, EVar 37%nat); (14, EAdd (EVar 36%nat) (ELit (-1))); (11, EVar 47%nat); (12, EVar 48%nat)]
        [(35%nat, 2 ^ 31); (36%nat, 259); (37%nat, 2 ^ 32); (47%nat, 2 ^ 32); (48%nat, 2 ^ 32)]
        [str; pl; mi; 0; 0; 0; 0; 0; 0; 0; 0; 0; sn; se]
        X.
      all: try (rewrite ?H1; first [reflexivity | lia]).
      skip_fin HDI Hms HRG HR Hfr Epl Es2.
    + run 12%nat [true; false] NoReads
        [(10, EAdd (EVar 35%nat) (ELit 1)); (13, EVar 37%nat); (14, EAdd (EVar 36%nat) (ELit (-1))); (11, EVar 47%nat); (12, EVar 48%nat)]
        [(35%nat, 2 ^ 31); (36%nat, 259); (37%nat, 2 ^ 32); (47%nat, 2 ^ 32); (48%nat, 2 ^ 32)]
        [str; pl; mi; 0; 0; 0; 0; 0; 0; 0; 0; 0; sn; se]
        X.
      all: try lia.
      skip_fin HDI Hms HRG HR Hfr Epl Es2.
Qed.


Definition exit_st (X : deflate_state) : deflate_state :=
  set_strstart (set_match_available (set_match_length X 2) 0) (ds_strstart X + 1).

Definition exit_pc (sn se : Z) : word :=
  if sn =? se then (0x1997c : word) else (0x19600 : word).

Lemma exit_blk : forall regs m1 m X mi sn se,
  DI m1 m X -> HREGS regs -> ILS regs (ds_strstart X + 1) mi (ds_prev_length X - 1) sn se ->
  0 <= ds_strstart X -> ds_strstart X + 1 < 2 ^ 31 -> 0 <= sn < 2 ^ 32 -> 0 <= se < 2 ^ 32 ->
  exists R M,
    msteps s6_segs (mkst regs (0x19968 : word) m s6_rom) (mkst R (exit_pc sn se) M s6_rom)
    /\ DI m1 M (exit_st X)
    /\ HREGS R /\ getr R 10 = zw (ds_strstart X + 1)
    /\ (forall r : reg, reg_in r [13]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X mi sn se HDI HRG (I10 & I13 & I14 & I11 & I12) Hs0 Hs31 Hsn Hse. open_di HDI. open_hregs HRG.
  pose proof (wf_wsz _ HWF) as Wws.
  Local Ltac exit_fin HDI Hms HRG HR Hfr :=
    clear_aparts; norm_sx Hms;
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KMatchLength; KMatchAvailable; KStrstart];
    lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end;
    split; [exact Hms|];
    split; [lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end; unfold exit_st; st_close idtac|];
    split; [hregs_via HRG Hfr|]; split; [reg1 HR Hfr | fr_weak Hfr].
  unfold exit_pc. destruct (Z.eqb_spec sn se) as [Hb|Hb].
  - run 8%nat [false] NoReads [(10, EAdd (EVar 35%nat) (ELit 1)); (11, EVar 36%nat); (12, EVar 37%nat)]
      [(35%nat, 2 ^ 31); (36%nat, 2 ^ 32); (37%nat, 2 ^ 32)] [ds_strstart X; sn; se] X.
    exit_fin HDI Hms HRG HR Hfr.
  - run 8%nat [true] NoReads [(10, EAdd (EVar 35%nat) (ELit 1)); (11, EVar 36%nat); (12, EVar 37%nat)]
      [(35%nat, 2 ^ 31); (36%nat, 2 ^ 32); (37%nat, 2 ^ 32)] [ds_strstart X; sn; se] X.
    exit_fin HDI Hms HRG HR Hfr.
Qed.


Definition fb_bufp (X : deflate_state) : Z :=
  if ds_block_start X <? 0 then 0 else W + wrap32 (ds_block_start X).
Definition fb_len (X : deflate_state) : Z := wrap64 (ds_strstart X - ds_block_start X).

Lemma bs_facts : forall bs, - 2 ^ 63 <= bs < 2 ^ 63 ->
  szwrap 64 (bs mod 2 ^ 64) = bs /\ (bs mod 2 ^ 64) mod 2 ^ 32 = wrap32 bs /\ 0 <= bs mod 2 ^ 64 < 2 ^ 64.
Proof using.
  intros bs Hbs. split; [rewrite szwrap_mod by lia; apply szwrap_small; lia|].
  split; [rewrite wrap32_mod; apply mod_pow2_le; lia|].
  apply Z.mod_pos_bound. lia.
Qed.

Lemma len_fact : forall a bs, zw (a - bs mod 2 ^ 64) = zw (wrap64 (a - bs)).
Proof using.
  intros a bs. apply zw_eqm. rewrite wrap64_mod, Z.mod_mod by lia.
  rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Definition FPR (rs rS : reg) (R : bvmap 5 word) : Prop := getr R rs = zw strm /\ getr R rS = zw S.

Definition fpa_pc (X : deflate_state) (pz pc : word) : word := if fp_len X =? 0 then pz else pc.

Lemma fp_len_eq : forall X, 0 <= ds_pending X < 2 ^ 31 -> 0 <= cs_avail_out (ds_strm X) ->
  fp_len X = (if cs_avail_out (ds_strm X) <? ds_pending X then cs_avail_out (ds_strm X) else ds_pending X)
  /\ 0 <= fp_len X <= ds_pending X /\ fp_len X <= cs_avail_out (ds_strm X).
Proof using.
  intros X Hp Ha. unfold fp_len. rewrite wrap32_mod, Z.mod_small by lia.
  destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia.
Qed.

Definition fp_tower (M0 : word -> option byte) (X : deflate_state) (len : Z) : word -> option byte :=
  let olen := Z.of_nat (length (cs_out_rev (ds_strm X))) in
  let M1 := wbytes M0 (zw (strm + 24)) (Z_to_le_bytes 8 (OUTB + olen + len)) in
  let M2 := wbytes M1 (zw (strm + 32)) (Z_to_le_bytes 4 (cs_avail_out (ds_strm X) - len)) in
  let M3 := wbytes M2 (zw (strm + 40)) (Z_to_le_bytes 8 (cs_total_out (ds_strm X) + len)) in
  let M4 := wbytes M3 (zw (S + 32)) (Z_to_le_bytes 8 (PB + ds_pending_out X + len)) in
  let M5 := wbytes M4 (zw (S + 40)) (Z_to_le_bytes 8 (ds_pending X - len)) in
  if ds_pending X - len =? 0 then wbytes M5 (zw (S + 32)) (Z_to_le_bytes 8 PB) else M5.

Definition avail_pc (X : deflate_state) (pz pnz : word) : word :=
  if cs_avail_out (ds_strm X) =? 0 then pz else pnz.


Lemma fb1a_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> LOC m -> getr regs 10 = zw (ds_strstart X) ->
  0 <= ds_strstart X < 2 ^ 31 -> - 2 ^ 63 <= ds_block_start X < 2 ^ 63 ->
  exists R,
    msteps s6_segs (mkst regs (0x1997c : word) m s6_rom) (mkst R (0x1af98 : word) m s6_rom)
    /\ HREGS R /\ getr R 10 = zw S /\ getr R 11 = zw (fb_bufp X) /\ getr R 12 = zw (fb_len X) /\ getr R 13 = zw 0
    /\ getr R 1 = (0x199d8%bv : word) /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra.
  intros regs m1 m X HDI HRG (L16 & L8) Q10 Hstr Hbs. open_di HDI. open_hregs HRG. pose proof (wf_wsz _ HWF) as Wws.
  pose proof (ds6_block_start _ _ _ _ Hsc) as C152. pose proof (ds6_window _ _ _ _ Hsc) as C96.
  destruct (bs_facts (ds_block_start X) Hbs) as (Hsx & Hw32 & Hbsu).
  pose proof (len_fact (ds_strstart X) (ds_block_start X)) as Hlen.
  assert (RD152 : exists bs, rdn s6_segs m (zw (S + 152)) 8 = Some bs /\ bytes_le_to_Z bs = ds_block_start X mod 2 ^ 64)
    by exact (cell_read_at s6_segs m (S + 152) 8 _ _ C152 eq_refl).
  pose proof (wrap32_range' (ds_block_start X)) as Hw32r.
  unfold fb_bufp, fb_len.
  destruct (Z.ltb_spec (ds_block_start X) 0) as [Hneg|Hpos].
  - run 20%nat [true] [RVal (EVar 36)] [(10, EVar 35%nat)] [(35%nat, 2 ^ 31); (36%nat, 2 ^ 64)]
      [ds_strstart X; ds_block_start X mod 2 ^ 64] X.
    exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat split; reg1 HR Hfr.
  - run 20%nat [false] [RVal (EVar 36); RVal (EVar 37); RVal (ELit 4294967295)] [(10, EVar 35%nat)] [(35%nat, 2 ^ 31); (36%nat, 2 ^ 64); (37%nat, 2 ^ 63)]
      [ds_strstart X; ds_block_start X mod 2 ^ 64; W] X.
    exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. repeat split; reg1 HR Hfr.
Qed.

Lemma fb1b_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= ds_strstart X <= 2 * ws ->
  exists R M,
    msteps s6_segs (mkst regs (0x199d8 : word) m s6_rom) (mkst R (0x1ad94 : word) M s6_rom)
    /\ DI m1 M (set_block_start X (ds_strstart X))
    /\ HREGS R /\ FPR 25%bv 18%bv R /\ getr R 10 = zw S /\ getr R 1 = (0x199f0%bv : word) /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r [1; 10; 18; 25]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Hstr. open_di HDI. open_hregs HRG. pose proof (wf_wsz _ HWF) as Wws.
  pose proof (ds6_strm _ _ _ _ Hsc) as C0. replace (S + 0) with S in C0 by lia.
  pose proof (ds6_strstart _ _ _ _ Hsc) as C172. pose proof (zsl_state s6_segs _ _ _ _ _ Zs) as Z56.
  apartF 1%nat 6%nat A16.
  run 20%nat NoDirs [RVal (EVar 35); RVal (EVar 36); RVal (EVar 32)] NoPins [(35%nat, 2 ^ 63); (36%nat, 65537)] [strm; ds_strstart X] X.
  clear_aparts. rewrite ?dfF_0, ?dfF_1, ?dfF_2, ?dfF_3 in Hms.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KBlockStart].
  lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end.
  split; [exact Hms|].
  split; [lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => exact H end|].
  split; [hregs_via HRG Hfr|]. unfold FPR. repeat split; reg1 HR Hfr.
Qed.

Lemma fb1c_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> FPR 25%bv 18%bv regs ->
  0 <= ds_pending X < 2 ^ 31 -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32 -> 0 <= ds_pending_out X <= PBL ->
  exists R,
    msteps s6_segs (mkst regs (0x199f0 : word) m s6_rom) (mkst R (fpa_pc X (0x19a5c : word) (0x27800 : word)) m s6_rom)
    /\ HREGS R /\ FPR 25%bv 18%bv R
    /\ (fp_len X <> 0 ->
        getr R 10 = zw (OUTB + Z.of_nat (length (cs_out_rev (ds_strm X)))) /\ getr R 11 = zw (PB + ds_pending_out X)
        /\ getr R 12 = zw (fp_len X) /\ getr R 19 = zw (fp_len X) /\ getr R 19 = zw (fp_len X) /\ getr R 1 = (0x19a14%bv : word) /\ getr R 2 = zw SP)
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 19]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG (F25 & F18) Hpd Hav Hpo. open_di HDI. open_hregs HRG.
  pose proof (wf_lbs _ HWF) as Wlbs.
  pose proof (ds6_pending _ _ _ _ Hsc) as C40. pose proof (ds6_pending_out _ _ _ _ Hsc) as C32.
  pose proof (cell_low4 _ _ _ _ C40 ltac:(lia) ltac:(lia)) as C40l.
  pose proof (zsl_avail_out s6_segs _ _ _ _ _ Zs) as Z32. pose proof (zsl_next_out s6_segs _ _ _ _ _ Zs) as Z24.
  destruct (fp_len_eq X ltac:(lia) ltac:(lia)) as (Efl & Hfl1 & Hfl2).
  unfold fpa_pc.
  Local Ltac fb1c_fin R Hms HRG HR Hfr :=
    exists R; split; [exact Hms|]; split; [hregs_via HRG Hfr|];
    split; [unfold FPR; split; reg1 HR Hfr|];
    split; [first [intros Hc; exfalso; lia | intros _; repeat split; reg1 HR Hfr] | fr_weak Hfr].
  destruct (Z.ltb_spec (ds_pending X) (cs_avail_out (ds_strm X))) as [Hlt|Hge].
  - replace (fp_len X) with (ds_pending X) by (rewrite Efl; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia).
    destruct (Z.eqb_spec (ds_pending X) 0) as [Hz|Hnz].
    + run 30%nat [true; true] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
        [(25, EVar 35%nat); (18, EVar 32%nat)]
        [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31); (37%nat, 2 ^ 32); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
        [strm; ds_pending X; cs_avail_out (ds_strm X); zp_out zp + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X] X.
      fb1c_fin R Hms HRG HR Hfr.
    + run 30%nat [true; false] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
        [(25, EVar 35%nat); (18, EVar 32%nat)]
        [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31); (37%nat, 2 ^ 32); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
        [strm; ds_pending X; cs_avail_out (ds_strm X); zp_out zp + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X] X.
      fb1c_fin R Hms HRG HR Hfr.
  - replace (fp_len X) with (cs_avail_out (ds_strm X)) by (rewrite Efl; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia).
    destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
    + run 30%nat [false; true] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
        [(25, EVar 35%nat); (18, EVar 32%nat)]
        [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31); (37%nat, 2 ^ 32); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
        [strm; ds_pending X; cs_avail_out (ds_strm X); zp_out zp + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X] X.
      fb1c_fin R Hms HRG HR Hfr.
    + run 30%nat [false; false] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
        [(25, EVar 35%nat); (18, EVar 32%nat)]
        [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31); (37%nat, 2 ^ 32); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
        [strm; ds_pending X; cs_avail_out (ds_strm X); zp_out zp + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X] X.
      fb1c_fin R Hms HRG HR Hfr.
Qed.

Lemma fb1d_blk : forall regs m1 M0 X len,
  DI m1 M0 X -> HREGS regs -> FPR 25%bv 18%bv regs -> getr regs 19 = zw len -> getr regs 19 = zw len ->
  0 < len <= ds_pending X -> ds_pending X < 2 ^ 31 -> len <= cs_avail_out (ds_strm X) < 2 ^ 32 ->
  0 <= ds_pending_out X -> ds_pending_out X + len <= PBL -> 0 <= cs_total_out (ds_strm X) < 2 ^ 64 ->
  exists R,
    msteps s6_segs (mkst regs (0x19a14 : word) M0 s6_rom) (mkst R (0x19a5c : word) (fp_tower M0 X len) s6_rom)
    /\ HREGS R /\ FPR 25%bv 18%bv R
    /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 M0 X len HDI HRG (F25 & F18) Q19 Q9 Hlen Hpd Hav Hpo0 Hpo1 Htot. open_di HDI. open_hregs HRG.
  pose proof (wf_lbs _ HWF) as Wlbs.
  pose proof (ds6_pending _ _ _ _ Hsc) as C40. pose proof (ds6_pending_out _ _ _ _ Hsc) as C32. pose proof (ds6_pending_buf _ _ _ _ Hsc) as C16.
  pose proof (zsl_avail_out s6_segs _ _ _ _ _ Zs) as Z32. pose proof (zsl_next_out s6_segs _ _ _ _ _ Zs) as Z24.
  pose proof (zsl_total_out s6_segs _ _ _ _ _ Zs) as Z40.
  apartF 1%nat 6%nat A16.
  unfold fp_tower.
  Local Ltac fb1d_fin R Hms HRG HR Hfr :=
    rewrite ?le_bytes_sx32 in Hms;
    exists R; split; [exact Hms|]; split; [hregs_via HRG Hfr|]; split; [unfold FPR; split; reg1 HR Hfr | fr_weak Hfr].
  destruct (Z.eqb_spec (ds_pending X - len) 0) as [Hz|Hnz].
  - run 30%nat [false] [RVal (EVar 37); RVal (EVar 39); RVal (EVar 40); RVal (EVar 38); RVal (EVar 41); RVal (EVar 42)]
      [(25, EVar 35%nat); (18, EVar 32%nat); (19, EVar 36%nat)]
      [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 32); (40%nat, 2 ^ 64); (41%nat, 2 ^ 31); (42%nat, 2 ^ 63)]
      [strm; len; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X; cs_avail_out (ds_strm X); cs_total_out (ds_strm X); ds_pending X; PB] X.
    fb1d_fin R Hms HRG HR Hfr.
  - run 30%nat [true] [RVal (EVar 37); RVal (EVar 39); RVal (EVar 40); RVal (EVar 38); RVal (EVar 41); RVal (EVar 42)]
      [(25, EVar 35%nat); (18, EVar 32%nat); (19, EVar 36%nat)]
      [(35%nat, 2 ^ 63); (36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 32); (40%nat, 2 ^ 64); (41%nat, 2 ^ 31); (42%nat, 2 ^ 63)]
      [strm; len; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X; cs_avail_out (ds_strm X); cs_total_out (ds_strm X); ds_pending X; PB] X.
    fb1d_fin R Hms HRG HR Hfr.
Qed.

Lemma fb1e_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32 ->
  exists R,
    msteps s6_segs (mkst regs (0x19a5c : word) m s6_rom) (mkst R (avail_pc X (0x19d64 : word) (0x19600 : word)) m s6_rom)
    /\ HREGS R /\ (cs_avail_out (ds_strm X) = 0 -> getr R 10 = zw 0)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Hav. open_di HDI. open_hregs HRG.
  pose proof (ds6_strm _ _ _ _ Hsc) as C0. replace (S + 0) with S in C0 by lia. pose proof (zsl_avail_out s6_segs _ _ _ _ _ Zs) as Z32.
  unfold avail_pc. destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
  - rewrite Hz in Z32.
    run 8%nat [false] [RVal (EVar 35); RVal (ELit 0)] NoPins [(35%nat, 2 ^ 63)] [strm] X.
    exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros _; reg1 HR Hfr | fr_weak Hfr].
  - pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
    run 8%nat [true] [RVal (EVar 35); RVal (EVar 36)] NoPins [(35%nat, 2 ^ 63); (36%nat, 2 ^ 32)] [strm; cs_avail_out (ds_strm X)] X.
    exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros Hc; exfalso; lia | fr_weak Hfr].
Qed.

End Walk.
End FXG.

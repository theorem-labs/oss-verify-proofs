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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 Callee6 TreesRod6 TreesApi6 DeflBlkApi6 DeflSlow6_1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Definition dsC6 : cfg :=
  CFG dfFB [] [EVar 1%nat; EVar 35%nat]
      [0x195dc; 0x19600; 0x19610; 0x19620; 0x19644; 0x1964c; 0x196ec; 0x19704; 0x1972c; 0x19730; 0x19738; 0x19850; 0x198c0; 0x198c8; 0x1994c; 0x1997c;
       0x19968; 0x19998; 0x199d8; 0x199f0; 0x19a14; 0x19a5c; 0x19a84; 0x19a9c; 0x19ac0; 0x19b0c; 0x19b14;
       0x19b98; 0x19bd4; 0x19c0c; 0x19c24; 0x19c48; 0x19c90; 0x19cd0; 0x19ce8; 0x19d0c; 0x19d54; 0x19d60; 0x19d64;
       0x16768; 0x19da0; 0x1af98; 0x1ad94; 0x27800] [].

Definition LOC4 (sp : Z) (m : word -> option byte) : Prop :=
  cell s6_segs m (sp - 128 + 16) 8 4294967295 /\ cell s6_segs m (sp - 128 + 8) 8 4097.

Definition hidden (P : Prop) : Prop := P.
Lemma hide : forall P : Prop, P -> hidden P. Proof using. intros P H; exact H. Qed.

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
Local Abbreviation LOC := (LOC4 sp).

Lemma LOC4_DI : forall m1 m X, LOC m1 -> DI m1 m X -> LOC m.
Proof using HH.
  intros m1 m X (L1 & L2) (_ & (_ & _ & _ & _ & _ & _ & (_ & _ & HAG & _) & (_ & _ & _ & _ & Eout & Hao & Hol)) & _).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & _).
  unfold LOC4. split;
    (eapply (cell_agree_out s6_segs _ m1 m); [exact HAG | intros x Hx Hin; eapply out_GDo; [exact HH | exact Hin | lia | lia] | lia | cbn; lia | assumption]).
Qed.

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
    symex s6_segs dsC6 fuel dirs rdv pins vb NoRegions pv NoVals
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

Lemma le_bytes_sx32 : forall x, Z_to_le_bytes 4 (szwrap 32 x) = Z_to_le_bytes 4 x.
Proof using. intros x. apply Z_to_le_bytes_mod_eq. apply szwrap_eqm. lia. Qed.
Lemma sx32_cases : forall a, 0 <= a < 2 ^ 32 ->
  (a < 2 ^ 31 /\ szwrap 32 a mod 2 ^ 64 = a) \/ (2 ^ 31 <= a /\ szwrap 32 a mod 2 ^ 64 = a + 2 ^ 64 - 2 ^ 32).
Proof using.
  intros a Ha. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 32) with 4294967296 in *.
  change (2 ^ 31) with 2147483648. change (2 ^ 64) with 18446744073709551616.
  destruct (Z_lt_le_dec a 2147483648).
  - left. split; [lia|]. rewrite (Z.mod_small (a + 2147483648)) by lia. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|]. replace ((a + 2147483648) mod 4294967296) with (a + 2147483648 - 4294967296) by (Z.to_euclidean_division_equations; lia).
    Z.to_euclidean_division_equations; lia.
Qed.
Lemma sx32_u64_ge : forall a q, 0 <= a < 2 ^ 32 -> 0 <= q < 2 ^ 31 -> q <= a -> q <= szwrap 32 a mod 2 ^ 64.
Proof using. intros a q Ha Hp Hle. destruct (sx32_cases a Ha) as [[? E]|[? E]]; rewrite E; lia. Qed.
Lemma sx32_u64_nz : forall a, 0 < a < 2 ^ 32 -> szwrap 32 a mod 2 ^ 64 <> 0.
Proof using. intros a Ha. destruct (sx32_cases a ltac:(lia)) as [[? E]|[? E]]; rewrite E; lia. Qed.
Ltac norm_sx H := rewrite ?le_bytes_sx32 in H.


Definition ltail_st (X : deflate_state) : deflate_state :=
  set_lookahead (set_strstart X (ds_strstart X + 1)) (ds_lookahead X - 1).

Definition ltail_pc (X : deflate_state) : word :=
  if cs_avail_out (ds_strm X) =? 0 then (0x19d64 : word) else (0x19600 : word).

Lemma ltail_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs ->
  0 <= ds_strstart X -> 1 <= ds_lookahead X -> ds_strstart X + ds_lookahead X <= 2 * ws ->
  cs_avail_out (ds_strm X) < 2 ^ 32 ->
  exists R M,
    msteps s6_segs (mkst regs (0x195dc : word) m s6_rom) (mkst R (ltail_pc X) M s6_rom)
    /\ DI m1 M (ltail_st X)
    /\ HREGS R /\ (cs_avail_out (ds_strm X) = 0 -> getr R 10 = zw 0)
    /\ (forall r : reg, reg_in r [10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Hs0 Hl1 Hsl Hav. open_di HDI. open_hregs HRG. pose proof (wf_wsz _ HWF) as Wws.
  pose proof (ds6_strm _ _ _ _ Hsc) as C0. replace (S + 0) with S in C0 by lia. pose proof (zsl_avail_out s6_segs _ _ _ _ _ Zs) as Z32.
  pose proof (ds6_strstart _ _ _ _ Hsc) as C172. pose proof (ds6_lookahead _ _ _ _ Hsc) as C180.
  apartF 1%nat 6%nat A16.
  unfold ltail_pc. destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
  - rewrite Hz in Z32.
    run 12%nat [true] [RVal (EVar 35); RVal (EVar 36); RVal (EVar 37); RVal (ELit 0)] NoPins
      [(35%nat, 2 ^ 63); (36%nat, 65537); (37%nat, 65537)]
      [strm; ds_strstart X; ds_lookahead X] X.
    clear_aparts.
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KStrstart; KLookahead].
    ex2. split; [exact Hms|].
    split; [lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end; unfold ltail_st; st_close idtac|].
    split; [hregs_via HRG Hfr|]. split; [intros _; reg1 HR Hfr | fr_weak Hfr].
  - pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
    run 12%nat [false] [RVal (EVar 35); RVal (EVar 36); RVal (EVar 37); RVal (EVar 38)] NoPins
      [(35%nat, 2 ^ 63); (36%nat, 65537); (37%nat, 65537); (38%nat, 2 ^ 32)]
      [strm; ds_strstart X; ds_lookahead X; cs_avail_out (ds_strm X)] X.
    clear_aparts.
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KStrstart; KLookahead].
    ex2. split; [exact Hms|].
    split; [lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end; unfold ltail_st; st_close idtac|].
    split; [hregs_via HRG Hfr|]. split; [intros E; exfalso; exact (Hnz E) | fr_weak Hfr].
Qed.


Definition head_pc (X : deflate_state) : word :=
  if ds_lookahead X <? 262 then (0x16768 : word) else (0x19644 : word).

Lemma head_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= ds_lookahead X <= 2 * ws ->
  exists R,
    msteps s6_segs (mkst regs (0x19600 : word) m s6_rom) (mkst R (head_pc X) m s6_rom)
    /\ HREGS R
    /\ (ds_lookahead X < 262 -> getr R 10 = zw S /\ getr R 1 = (0x19610%bv : word))
    /\ (262 <= ds_lookahead X -> getr R 10 = zw (ds_lookahead X))
    /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r [1; 10]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Hlk. open_di HDI. open_hregs HRG. pose proof (wf_wsz _ HWF) as Wws.
  pose proof (ds6_lookahead _ _ _ _ Hsc) as C180.
  unfold head_pc. destruct (Z.ltb_spec (ds_lookahead X) 262) as [Hlo|Hhi].
  - run 6%nat [false] [RVal (EVar 35)] NoPins [(35%nat, 65537)] [ds_lookahead X] X.
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|].
    split; [intros _; split; reg1 HR Hfr|]. split; [intros; exfalso; lia|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - run 6%nat [true] [RVal (EVar 35)] NoPins [(35%nat, 65537)] [ds_lookahead X] X.
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|].
    split; [intros; exfalso; lia|]. split; [intros _; reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.


Definition fillr_pc (X : deflate_state) : word :=
  if (ds_lookahead X <? 262) && (flush =? 0) then (0x19b0c : word)
  else if ds_lookahead X =? 0 then (0x19b14 : word) else (0x19620 : word).

Lemma fillr_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 9 = zw flush -> 0 <= ds_lookahead X <= 2 * ws ->
  exists R,
    msteps s6_segs (mkst regs (0x19610 : word) m s6_rom) (mkst R (fillr_pc X) m s6_rom)
    /\ HREGS R /\ getr R 10 = zw (ds_lookahead X)
    /\ (forall r : reg, reg_in r [10; 11]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra.
  intros regs m1 m X HDI HRG H9 Hlk. open_di HDI. open_hregs HRG. pose proof (wf_wsz _ HWF) as Wws.
  pose proof (ds6_lookahead _ _ _ _ Hsc) as C180.
  unfold fillr_pc.
  destruct (Z.eqb_spec flush 0) as [Fz|Fnz].
  - destruct (Z.ltb_spec (ds_lookahead X) 262) as [Hlo|Hhi]; cbn [andb].
    + run 8%nat [false; true] [RVal (EVar 35)] [(9, EVar 34%nat)] [(35%nat, 65537)] [ds_lookahead X] X.
      ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
    + replace (ds_lookahead X =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      run 8%nat [false; false; false] [RVal (EVar 35)] [(9, EVar 34%nat)] [(35%nat, 65537)] [ds_lookahead X] X.
      ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - replace ((ds_lookahead X <? 262) && false) with false by (destruct (_ <? _); reflexivity).
    destruct (Z.eqb_spec (ds_lookahead X) 0) as [L0|L0].
    + run 8%nat [true; true] [RVal (EVar 35)] [(9, EVar 34%nat)] [(35%nat, 65537)] [ds_lookahead X] X.
      ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
    + run 8%nat [true; false] [RVal (EVar 35)] [(9, EVar 34%nat)] [(35%nat, 65537)] [ds_lookahead X] X.
      ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.


Lemma ret0_blk : forall regs m,
  getr regs 2 = zw SP ->
  exists R,
    msteps s6_segs (mkst regs (0x19b0c : word) m s6_rom) (mkst R (0x19d64 : word) m s6_rom)
    /\ getr R 10 = zw 0 /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof using HH ra flush ds zp p S mem ROM.
  intros regs m P2. open_min.
  run_gen [(2, EVar 33%nat)] 3%nat NoDirs NoReads NoPins NoBounds (@nil Z) ds.
  ex1. split; [exact Hms|]. repeat split; reg1 HR Hfr.
Qed.


Definition ins_str (X : deflate_state) (str : Z) : deflate_state :=
  let h := update_hash X (ds_ins_h X) (arr_get (ds_window X) (str + 2)) in
  set_head (set_prev (set_ins_h X h) (arr_set (ds_prev X) (Z.land str (ds_w_mask X)) (arr_get (ds_head X) h)))
           (arr_set (ds_head X) h (wrap16 str)).

Lemma ins_str_eq : forall X str, insert_string X str = (ins_str X str, arr_get (ds_head X) (update_hash X (ds_ins_h X) (arr_get (ds_window X) (str + 2)))).
Proof using. intros X str. unfold insert_string, ins_str, MIN_MATCH. cbv zeta. dsred. reflexivity. Qed.

Definition PLR (R : bvmap 5 word) (X : deflate_state) : Prop :=
  getr R 10 = zw (ds_match_length X) /\ getr R 12 = zw (ds_prev_length X).


Definition prev_st (X : deflate_state) : deflate_state :=
  set_prev_length (set_prev_match (set_match_length X 2) (ds_match_start X)) (ds_match_length X).

Definition short_pc (X : deflate_state) : word :=
  if 2 <? ds_lookahead X then (0x1964c : word) else (0x19730 : word).

Lemma short_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw (ds_lookahead X) ->
  0 <= ds_lookahead X <= 2 * ws -> 0 <= ds_match_length X <= 258 -> 0 <= ds_match_start X < 2 ^ 32 ->
  exists R M,
    msteps s6_segs (mkst regs (0x19620 : word) m s6_rom) (mkst R (short_pc X) M s6_rom)
    /\ (2 < ds_lookahead X -> M = m /\ getr R 12 = zw (ds_match_length X) /\ getr R 13 = zw (szwrap 32 (ds_match_start X)))
    /\ (ds_lookahead X <= 2 -> DI m1 M (prev_st X) /\ PLR R (prev_st X))
    /\ HREGS R
    /\ (forall r : reg, reg_in r [10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Q10 Hlk Hml Hms0. open_di HDI. open_hregs HRG. pose proof (wf_wsz _ HWF) as Wws.
  pose proof (ds6_match_length _ _ _ _ Hsc) as C160. pose proof (ds6_match_start _ _ _ _ Hsc) as C176.
  unfold short_pc. destruct (Z.ltb_spec 2 (ds_lookahead X)) as [Hhi|Hlo].
  - run 8%nat [true] [RVal (EVar 36); RVal (EVar 37)] [(10, EVar 35%nat)]
        [(35%nat, 65537); (36%nat, 259); (37%nat, 2 ^ 32)] [ds_lookahead X; ds_match_length X; ds_match_start X] X.
    ex2. split; [exact Hms|]. split; [intros _; split; [reflexivity|]; split; reg1 HR Hfr|].
    split; [intros; exfalso; lia|]. split; [hregs_via HRG Hfr | fr_weak Hfr].
  - run 12%nat [false] [RVal (EVar 36); RVal (EVar 37)] [(10, EVar 35%nat)]
        [(35%nat, 65537); (36%nat, 259); (37%nat, 2 ^ 32)] [ds_lookahead X; ds_match_length X; ds_match_start X] X.
    clear_aparts. norm_sx Hms.
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KMatchLength; KPrevMatch; KPrevLength].
    ex2. split; [exact Hms|]. split; [intros; exfalso; lia|].
    split.
    { intros _. split.
      - lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end. unfold prev_st. st_close idtac.
      - unfold PLR, prev_st. dsred. split; reg1 HR Hfr. }
    split; [hregs_via HRG Hfr | fr_weak Hfr].
Qed.

Lemma h45c_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= ds_match_length X <= 258 -> 0 <= ds_match_start X < 2 ^ 32 ->
  exists R,
    msteps s6_segs (mkst regs (0x19644 : word) m s6_rom) (mkst R (0x1964c : word) m s6_rom)
    /\ HREGS R /\ getr R 12 = zw (ds_match_length X) /\ getr R 13 = zw (szwrap 32 (ds_match_start X))
    /\ (forall r : reg, reg_in r [12; 13]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Hml Hms0. open_di HDI. open_hregs HRG.
  pose proof (ds6_match_length _ _ _ _ Hsc) as C160. pose proof (ds6_match_start _ _ _ _ Hsc) as C176.
  run 4%nat NoDirs [RVal (EVar 35); RVal (EVar 36)] NoPins [(35%nat, 259); (36%nat, 2 ^ 32)] [ds_match_length X; ds_match_start X] X.
  ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.


Definition hash_st (X : deflate_state) : deflate_state :=
  let str := ds_strstart X in
  let h := update_hash X (ds_ins_h X) (arr_get (ds_window X) (str + 2)) in
  let hh := arr_get (ds_head X) h in
  set_prev_length (set_prev_match (set_match_length (set_ins_h
    (set_head (set_prev X (arr_set (ds_prev X) (Z.land str (ds_w_mask X)) hh)) (arr_set (ds_head X) h (wrap16 str))) h) 2)
    (ds_match_start X)) (ds_match_length X).

Definition hash_pc (X : deflate_state) (str hh : Z) : word :=
  if hh =? 0 then (0x19730 : word)
  else if ds_max_lazy_match X <=? ds_match_length X then (0x1972c : word)
  else if wrap32 (str - hh) <=? ws - 262 then (0x19da0 : word) else (0x1972c : word).

Lemma hash_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 12 = zw (ds_match_length X) -> getr regs 13 = zw (szwrap 32 (ds_match_start X)) ->
  0 <= ds_strstart X -> ds_strstart X + 3 <= 2 * ws ->
  0 <= ds_ins_h X < 2 ^ 31 -> ds_hash_mask X = hs - 1 -> ds_w_mask X = ws - 1 -> 0 <= ds_hash_shift X < 32 ->
  (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256) ->
  (forall j, 0 <= j < hs -> 0 <= arr_get (ds_head X) j < 65536) ->
  0 <= ds_match_length X <= 258 -> 0 <= ds_match_start X < 2 ^ 32 -> 0 <= ds_max_lazy_match X < 2 ^ 31 ->
  let str := ds_strstart X in
  let h := update_hash X (ds_ins_h X) (arr_get (ds_window X) (str + 2)) in
  let hh := arr_get (ds_head X) h in
  exists R M,
    msteps s6_segs (mkst regs (0x1964c : word) m s6_rom) (mkst R (hash_pc X str hh) M s6_rom)
    /\ DI m1 M (hash_st X)
    /\ HREGS R /\ getr R 11 = zw hh
    /\ (hash_pc X str hh = (0x19da0%bv : word) -> getr R 10 = zw S /\ getr R 1 = (0x196ec%bv : word))
    /\ (hash_pc X str hh <> (0x19da0%bv : word) -> getr R 10 = zw 2)
    /\ (hh = 0 -> getr R 12 = zw (ds_match_length X))
    /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r [1; 5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r).
Proof using HWF HH ra flush.
  intros regs m1 m X HDI HRG Q12 Q13 Hs0 Hs3 Hih Hhm Hwm Hsh Hwb Hhb Hml Hms0 Hlz str h hh.
  open_di HDI. open_hregs HRG.
  pose proof (wf_wsz _ HWF) as Wws. pose proof (wf_hsz _ HWF) as Whs.
  pose proof (ds6_strstart _ _ _ _ Hsc) as C172. pose proof (ds6_window _ _ _ _ Hsc) as C96.
  pose proof (ds6_hash_shift _ _ _ _ Hsc) as C144. pose proof (ds6_ins_h _ _ _ _ Hsc) as C128.
  pose proof (ds6_hash_mask _ _ _ _ Hsc) as C140. pose proof (ds6_w_mask _ _ _ _ Hsc) as C88.
  pose proof (ds6_head _ _ _ _ Hsc) as C120. pose proof (ds6_prev _ _ _ _ Hsc) as C112.
  pose proof (ds6_w_size _ _ _ _ Hsc) as C80. pose proof (ds6_max_lazy_match _ _ _ _ Hsc) as C192.
  rewrite Hhm in C140. rewrite Hwm in C88. rewrite Ews in C80.
  set (hx := Z.land (Z.lxor (zaluw ALU_SLL (ds_ins_h X) (ds_hash_shift X)) (wb (ds_window X) (str + 2))) (hs - 1)).
  assert (Ehx : hx = h).
  { subst hx h. rewrite (wb_get (ds_window X) ltac:(intros j Hj; apply Hwb; rewrite <- Lw; exact Hj)) by (rewrite Lw; lia).
    rewrite <- Hhm. apply update_hash_sllw; try reflexivity; lia. }
  pose proof (land_mask_range (Z.lxor (zaluw ALU_SLL (ds_ins_h X) (ds_hash_shift X)) (wb (ds_window X) (str + 2))) (hs - 1) ltac:(lia)) as Rhx.
  fold hx in Rhx.
  set (Y := Z.land (ws - 1) str).
  assert (RY : 0 <= Y <= ws - 1) by (subst Y; rewrite Z.land_comm; apply land_mask_range; lia).
  assert (Rhh : 0 <= hh < 65536) by (subst hh; apply Hhb; rewrite <- Ehx; lia).
  assert (Epb : pb (ds_head X) hx = hh) by (subst hh; rewrite <- Ehx; apply pb_get; [intros j Hj; apply Hhb; rewrite <- Lh; exact Hj | rewrite Lh; lia]).
  apartF 1%nat 3%nat A13. apartF 1%nat 4%nat A14.
  unfold hash_pc.
  Local Ltac hash_fin HDI Hms HRG HR Hfr X str h hh hx Ehx Hwm Y :=
    clear_aparts; rewrite ?dfF_0, ?dfF_1, ?dfF_2, ?dfF_3 in Hms; norm_sx Hms;
    di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end)
      [KPrev Y (arr_get (ds_head X) hx); KHead hx (wrap16 str); KInsH; KMatchLength; KPrevMatch; KPrevLength];
    lazymatch type of Hms with msteps _ _ (mkst ?R _ ?M _) => exists R, M end;
    split; [exact Hms|];
    split;
    [ lazymatch goal with H : DeflSlow6_1.DI _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end;
      change (hash_st X) with (set_prev_length (set_prev_match (set_match_length (set_ins_h
         (set_head (set_prev X (arr_set (ds_prev X) (Z.land str (ds_w_mask X)) hh)) (arr_set (ds_head X) h (wrap16 str))) h) 2)
         (ds_match_start X)) (ds_match_length X));
      subst hh; rewrite <- Ehx; st_close ltac:(first [subst hx; reflexivity | rewrite Hwm; apply Z.land_comm])
    | split; [hregs_via HRG Hfr|];
      split; [reg1 HR Hfr|];
      split; [let HX := fresh "HX" in intros HX; first [exfalso; discriminate HX | split; reg1 HR Hfr]|];
      split; [let HX := fresh "HX" in intros HX; first [exfalso; apply HX; reflexivity | reg1 HR Hfr]|];
      split; [let HX := fresh "HX" in intros HX; first [exfalso; lia | reg1 HR Hfr]|];
      split; [reg1 HR Hfr | fr_weak Hfr] ].
  destruct (Z.eqb_spec hh 0) as [Hz|Hnz].
  -
    run 50%nat [true]
      [RVal (EVar 37); RVal (EVar 35); RVal (EVar 36); RVal (EVar 42); RVal (EVar 41); RVal (EVar 38);
       RVal (EApp1 0%nat (EAdd (EVar 35) (ELit 2))); RVal (EVar 39); RVal (EVar 40); RVal (EVar 43)]
      [(12, EVar 46%nat); (13, ESx 32 (EVar 47%nat))]
      [(35%nat, 65537); (36%nat, 2 ^ 63); (37%nat, 32); (38%nat, 2 ^ 31); (39%nat, 65536); (40%nat, 65536);
       (41%nat, 2 ^ 63); (42%nat, 2 ^ 63); (43%nat, 65536); (46%nat, 259); (47%nat, 2 ^ 32)]
      [str; W; ds_hash_shift X; ds_ins_h X; hs - 1; ws - 1; HD; PV; pb (ds_head X) hx; 0; 0; ds_match_length X; ds_match_start X]
      X.
    hash_fin HDI Hms HRG HR Hfr X str h hh hx Ehx Hwm Y.
  - assert (Hc1 : szwrap 32 (ws + -262) mod 2 ^ 64 = ws - 262) by (rewrite (szwrap_small 32) by lia; rewrite Z.mod_small by lia; lia).
    assert (Hc2 : szwrap 32 (str - pb (ds_head X) hx) mod 2 ^ 64 <= ws - 262 <-> wrap32 (str - hh) <= ws - 262)
      by (rewrite Epb; apply szwrap32_u64_le; lia).
    destruct (Z.leb_spec (ds_max_lazy_match X) (ds_match_length X)) as [Hlazy|Hlazy].
    + run 50%nat [false; true]
        [RVal (EVar 37); RVal (EVar 35); RVal (EVar 36); RVal (EVar 42); RVal (EVar 41); RVal (EVar 38);
         RVal (EApp1 0%nat (EAdd (EVar 35) (ELit 2))); RVal (EVar 39); RVal (EVar 40); RVal (EVar 43); RVal (EVar 44)]
        [(12, EVar 46%nat); (13, ESx 32 (EVar 47%nat))]
        [(35%nat, 65537); (36%nat, 2 ^ 63); (37%nat, 32); (38%nat, 2 ^ 31); (39%nat, 65536); (40%nat, 65536);
         (41%nat, 2 ^ 63); (42%nat, 2 ^ 63); (43%nat, 65536); (44%nat, 2 ^ 31); (45%nat, 65536); (46%nat, 259); (47%nat, 2 ^ 32)]
        [str; W; ds_hash_shift X; ds_ins_h X; hs - 1; ws - 1; HD; PV; pb (ds_head X) hx; ds_max_lazy_match X; ws; ds_match_length X; ds_match_start X]
        X.
      hash_fin HDI Hms HRG HR Hfr X str h hh hx Ehx Hwm Y.
    + destruct (Z.leb_spec (wrap32 (str - hh)) (ws - 262)) as [Hnear|Hfar].
      * run 50%nat [false; false; false]
          [RVal (EVar 37); RVal (EVar 35); RVal (EVar 36); RVal (EVar 42); RVal (EVar 41); RVal (EVar 38);
           RVal (EApp1 0%nat (EAdd (EVar 35) (ELit 2))); RVal (EVar 39); RVal (EVar 40); RVal (EVar 43); RVal (EVar 44); RVal (EVar 45)]
          [(12, EVar 46%nat); (13, ESx 32 (EVar 47%nat))]
          [(35%nat, 65537); (36%nat, 2 ^ 63); (37%nat, 32); (38%nat, 2 ^ 31); (39%nat, 65536); (40%nat, 65536);
           (41%nat, 2 ^ 63); (42%nat, 2 ^ 63); (43%nat, 65536); (44%nat, 2 ^ 31); (45%nat, 65536); (46%nat, 259); (47%nat, 2 ^ 32)]
          [str; W; ds_hash_shift X; ds_ins_h X; hs - 1; ws - 1; HD; PV; pb (ds_head X) hx; ds_max_lazy_match X; ws; ds_match_length X; ds_match_start X]
          X.
        hash_fin HDI Hms HRG HR Hfr X str h hh hx Ehx Hwm Y.
      * run 50%nat [false; false; true]
          [RVal (EVar 37); RVal (EVar 35); RVal (EVar 36); RVal (EVar 42); RVal (EVar 41); RVal (EVar 38);
           RVal (EApp1 0%nat (EAdd (EVar 35) (ELit 2))); RVal (EVar 39); RVal (EVar 40); RVal (EVar 43); RVal (EVar 44); RVal (EVar 45)]
          [(12, EVar 46%nat); (13, ESx 32 (EVar 47%nat))]
          [(35%nat, 65537); (36%nat, 2 ^ 63); (37%nat, 32); (38%nat, 2 ^ 31); (39%nat, 65536); (40%nat, 65536);
           (41%nat, 2 ^ 63); (42%nat, 2 ^ 63); (43%nat, 65536); (44%nat, 2 ^ 31); (45%nat, 65536); (46%nat, 259); (47%nat, 2 ^ 32)]
          [str; W; ds_hash_shift X; ds_ins_h X; hs - 1; ws - 1; HD; PV; pb (ds_head X) hx; ds_max_lazy_match X; ws; ds_match_length X; ds_match_start X]
          X.
        hash_fin HDI Hms HRG HR Hfr X str h hh hx Ehx Hwm Y.
Qed.

End Walk.
End FXG.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import DS6 CalleeKits6 DeflSlow6_1 DeflSlow6_2 DeflSlow6_3 DeflSlow6_4 DeflSlow6_5 DeflSlow6_5b DeflSlow6_6 DeflSlow6_7 DeflSlow6_M.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u Callee6u TreesRod6u TreesApi6u TrApi6u
  Lmatch6u_run FillWin6uA FillWin6uD DeflBlkApi6u DeflKit6u.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition dsCu : cfg :=
  CFG dfFB [] [EVar 1%nat; EVar 35%nat]
      [0x19d88; 0x19da8; 0x19db8; 0x19dd0; 0x19e9c; 0x19ea0; 0x19ee0; 0x19ef8; 0x19f20; 0x19f2c; 0x1a180; 0x1a188; 0x1a270;
       0x1a0b4; 0x1a2b4; 0x1a2c8; 0x1a338; 0x1a348; 0x1a378; 0x1a388; 0x1a3a8; 0x1a3bc; 0x1a3c4;
       0x1a4ac; 0x1a50c; 0x1a574; 0x1a584; 0x1a5dc; 0x1a5ec; 0x1a604; 0x1a608;
       0x169b8; 0x1a648; 0x1bff0; 0x181ac; 0x1a644] [].

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
Local Abbreviation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Abbreviation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Abbreviation AV0 := (cs_avail_out (ds_strm ds)).
Local Abbreviation SP := (sp - 128).
Hypothesis HH : DKH ROM mem S p zp ds flush ra sp DSLOW_FRAME6u DSLOW_FR6u.
Hypothesis MEMCPY : memcpy_run6u.
Hypothesis MEMSET : memset_run6u.
Hypothesis ADLER : adler32_run6u ROM.
Hypothesis TFBITS : tr_flush_bits_run6u.
Variable FBSAFE : deflate_state -> option Z -> Z -> Z -> Prop.
Hypothesis TFB : tr_flush_block_run6u FBSAFE.
Local Abbreviation DI := (DeflKit6u.DI ROM mem S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).
Local Abbreviation BRm := (BR s6u_segs 180992 181024 181056 (DeflKit6u.Fd S p zp ds sp DSLOW_FRAME6u) mem S p PBL).
Local Abbreviation RZ := (DeflKit6u.RZ ROM mem S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).
Local Abbreviation GD := (DeflKit6u.GD S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).
Local Abbreviation GDo := (DeflKit6u.GDo S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).
Local Abbreviation DI_eqst := (DeflKit6u.DI_eqst ROM mem S p zp ds sp DSLOW_FRAME6u DSLOW_FR6u).

Let HL : ZRH6u DSLOW_FRAME6u mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ _ _ HH.
Let HRL : rom_local6u ROM := dsh_roml _ _ _ _ _ _ _ _ _ _ _ HH.


Definition HREGS (R : bvmap 5 word) : Prop :=
  getr R 8 = zw S /\ getr R 2 = zw SP /\ getr R 9 = zw flush /\ getr R 19 = zw (S + 5888) /\ getr R 20 = zw (S + 212)
  /\ getr R 27 = zw (S + 2504) /\ getr R 21 = zw (Z.lxor (S + 212) (-1)) /\ getr R 18 = zw (Z.lxor (S + 2504) (-1))
  /\ getr R 22 = zw 18446744073709551615 /\ getr R 23 = zw 261 /\ getr R 25 = zw 3 /\ getr R 26 = zw 32 /\ getr R 24 = zw 31.

Lemma HREGS_via : forall R R' L,
  HREGS R -> (forall r : reg, reg_in r L = false -> getr R' r = getr R r) ->
  forallb (fun r : reg => negb (reg_in r L)) [8; 2; 9; 19; 20; 27; 21; 18; 22; 23; 25; 26; 24]%bv = true ->
  HREGS R'.
Proof.
  intros R R' L (A8 & A2 & A9 & A19 & A20 & A27 & A21 & A18 & A22 & A23 & A25 & A26 & A24) Hfr Hl.
  cbn [forallb] in Hl. rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in Hl.
  destruct Hl as (X8 & X2 & X9 & X19 & X20 & X27 & X21 & X18 & X22 & X23 & X25 & X26 & X24 & _).
  unfold HREGS. rewrite !Hfr by assumption.
  repeat split; assumption.
Qed.

Local Abbreviation HREGS_via3 := HREGS_via.

Definition LOC (m : word -> option byte) : Prop :=
  cell s6u_segs m (SP + 16) 8 4294967295 /\ cell s6u_segs m (SP + 8) 8 4097.

Lemma LOC_DI : forall m1 m X, LOC m1 -> DI m1 m X -> LOC m.
Proof.
  intros m1 m X (L1 & L2) (_ & (_ & _ & _ & _ & _ & _ & (_ & _ & HAG & _) & (_ & _ & _ & _ & Eout & Hao & Hol)) & _).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & _). unfold DSLOW_FRAME6u in Hsp.
  unfold LOC. split;
    (eapply (cell_agree_out s6u_segs (GDo (ds_strm X)) m1 m);
      [exact HAG | intros x Hx Hin; exact (out_GDo _ _ _ _ _ _ _ _ _ _ _ HH _ _ Hin ltac:(lia) ltac:(unfold DSLOW_FR6u; lia)) | lia | cbn; lia | assumption]).
Qed.

Definition HPINS : list (Z * expr) :=
  [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 34%nat); (19, EAdd (EVar 32%nat) (ELit 5888)); (20, EAdd (EVar 32%nat) (ELit 212));
   (27, EAdd (EVar 32%nat) (ELit 2504)); (21, EXor (EAdd (EVar 32%nat) (ELit 212)) (ELit (-1))); (18, EXor (EAdd (EVar 32%nat) (ELit 2504)) (ELit (-1)));
   (22, ELit 18446744073709551615); (23, ELit 261); (25, ELit 3); (26, ELit 32); (24, ELit 31)].

Definition HPINST : list (Z * expr) :=
  [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 34%nat);
   (22, ELit 18446744073709551615); (23, ELit 261); (25, ELit 3); (26, ELit 32); (24, ELit 31)].

Local Ltac unhide H := unfold hidden in H.
Local Ltac norm_sx H := rewrite ?le_bytes_sx32 in H.

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac hregs_via HRG Hfr := apply (HREGS_via3 _ _ _ HRG Hfr); reflexivity.

Local Ltac nf := cbn [dfF].

Local Ltac rod_read :=
  lazymatch goal with
  | |- exists bs, rdn _ ?m (zw ?a) _ = Some bs /\ bytes_le_to_Z bs = arr_get length_code_a ?i =>
      eapply (length_code_read R6u s6u_segs m trod_ok6u ltac:(eassumption) i a); first [reflexivity | cbn [tr_length_code R6u]; lia]
  | |- exists bs, rdn _ ?m (zw ?a) _ = Some bs /\ bytes_le_to_Z bs = arr_get dist_code_a ?i =>
      eapply (dist_code_read R6u s6u_segs m trod_ok6u ltac:(eassumption) i a); first [reflexivity | cbn [tr_dist_code R6u]; lia]
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
            | apply even_plus_shl1; [assumption | lia | nf; lia]
            | nf; change (2 ^ 3) with 8 in *; change (2 ^ 1) with 2 in *; zcond_close
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
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs dsCu fuel dirs rdv pins vb NoRegions pv NoVals
          (dfF (ds_window X) (ds_head X) (ds_dyn_ltree_fc X) (ds_dyn_dtree_fc X)) F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
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
  let HRT := fresh "HRT" in let HGOT := fresh "HGOT" in pose proof (proj1 HRC) as HRT; pose proof (proj2 HRC) as HGOT; unfold got6u_clear in HGOT;
  let Lw := fresh "Lw" in let Lp := fresh "Lp" in let Lh := fresh "Lh" in
  let Ein := fresh "Ein" in let Eout := fresh "Eout" in let Hao := fresh "Hao" in let Hol := fresh "Hol" in
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol); rewrite Lw in Cw; rewrite Lp in Cp; rewrite Lh in Ch;
  let RF := fresh "RF" in
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in let HW := fresh "HW" in let HPV := fresh "HPV" in let HHD := fresh "HHD" in
  let HPB := fresh "HPB" in let Hstrm := fresh "Hstrm" in let HOUT := fresh "HOUT" in let HIN := fresh "HIN" in
  destruct RF as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN);
  let RODS := fresh "RODS" in pose proof (mapped_rod_apart R6u s6u_segs _ S 5968 trod_ok6u HRT MS ltac:(lia) ltac:(lia)) as RODS;
  let RODP := fresh "RODP" in pose proof (mapped_rod_apart R6u s6u_segs _ (p_pending_buf p) PBL trod_ok6u HRT MP ltac:(lia) ltac:(pose proof (wf_lbs _ HWF); lia)) as RODP;
  cbn [tr_lo tr_hi tr_sdesc R6u] in RODS, RODP; apply hide in RODS; apply hide in RODP;
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl;
  let HGR := fresh "HGR" in pose proof HRZ as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & HGR) & _);
  let MWm := fresh "MWm" in let MPm := fresh "MPm" in let MHm := fresh "MHm" in let MZm := fresh "MZm" in
  let T := fresh "T" in
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 2 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MWm; cbv beta in MWm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 3 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MPm; cbv beta in MPm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 4 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MHm; cbv beta in MHm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 6 ltac:(lia)) as T; unfold ZRF, zsl_SIZE in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MZm; cbv beta in MZm; clear T;
  let US8 := fresh "US8" in let US1 := fresh "US1" in let UST1 := fresh "UST1" in let UST8 := fresh "UST8" in
  let UPB1 := fresh "UPB1" in let UO := fresh "UO" in let UHD2 := fresh "UHD2" in let UPV2 := fresh "UPV2" in let UI := fresh "UI" in
  pose proof (zrh_S8 _ _ _ _ _ _ _ HL) as US8; pose proof (zrh_S1 _ _ _ _ _ _ _ HL) as US1;
  pose proof (zrh_strm1 _ _ _ _ _ _ _ HL) as UST1; pose proof (zrh_strm8 _ _ _ _ _ _ _ HL) as UST8;
  pose proof (zrh_PB1 _ _ _ _ _ _ _ HL) as UPB1; pose proof (zrh_O _ _ _ _ _ _ _ HL) as UO;
  pose proof (zrh_HD2 _ _ _ _ _ _ _ HL) as UHD2; pose proof (zrh_PV2 _ _ _ _ _ _ _ HL) as UPV2; pose proof (zrh_I _ _ _ _ _ _ _ HL) as UI;
  let UHD := fresh "UHD" in let UPV := fresh "UPV" in let UW := fresh "UW" in
  pose proof (zrh_HD _ _ _ _ _ _ _ HL) as UHD; pose proof (zrh_PV _ _ _ _ _ _ _ HL) as UPV; pose proof (zrh_W _ _ _ _ _ _ _ HL) as UW;
  unfold DSLOW_FRAME6u in Hsp, MF.

Local Ltac apartF i j H :=
  pose proof (apart_ij _ _ _ _ _ _ _ _ _ _ _ HH i j ltac:(lia) ltac:(lia)) as H;
  unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE, DSLOW_FRAME6u, DSLOW_FR6u in H.

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P19 := fresh "P19" in let P20 := fresh "P20" in
  let P27 := fresh "P27" in let P21 := fresh "P21" in let P18 := fresh "P18" in let P22 := fresh "P22" in let P23 := fresh "P23" in
  let P25 := fresh "P25" in let P26 := fresh "P26" in let P24 := fresh "P24" in
  pose proof HRG as (P8 & P2 & P9 & P19 & P20 & P27 & P21 & P18 & P22 & P23 & P25 & P26 & P24).

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
          | H1 : DeflKit6u.DI _ ?mem ?S ?p ?zp ?ds ?sp _ _ ?m1 M1 ?X |- _ =>
              let H2 := fresh "HDI" in
              lazymatch k with
              | KInsH => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_ins_h ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KBlockStart => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_block_start ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KMatchLength => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_match_length ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KStrstart => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_strstart ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KLookahead => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_lookahead ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KInsert => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_insert ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KSymNext => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_sym_next ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPending => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_pending ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPrevLength => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_prev_length ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPrevMatch => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_prev_match ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KMatchAvailable => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_match_available ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPendingOut ?off => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_pending_out ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X off a v H1 ltac:(lia) ltac:(lia)) as H2 end
              | KPb ?i ?c' => lazymatch bs with Z_to_le_bytes _ ?c =>
                  pose proof (DI_st_pb ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a i c c' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KFc ?t ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_fc ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a t i v v' H1 ltac:(cbn [toff]; lia) ltac:(cbn [tsize]; lia) ltac:(mod_side)) as H2 end
              | KPrev ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_prev ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a i v v' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KHead ?i ?v' => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_head ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a i v v' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KFrame => pose proof (DI_st_frame ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a bs H1 ltac:(lia)
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
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in
  destruct RF as (Hsp & HS & _); unfold DSLOW_FRAME6u in Hsp;
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl.

Local Ltac ex1 := lazymatch goal with H : msteps _ _ (mkst ?R _ _ _) |- _ => exists R end.
Local Ltac ex2 := lazymatch goal with H : msteps _ _ (mkst ?R _ ?M _) |- _ => exists R, M end.

Local Ltac the_DI := lazymatch goal with H : DeflKit6u.DI _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact H end.
Local Ltac eq_DI := lazymatch goal with H : DeflKit6u.DI _ _ _ _ _ _ _ _ _ _ _ _ |- _ => eapply DI_eqst; [exact H|] end.



Local Abbreviation avail0_st := DeflSlow6_3.avail0_st.

Lemma avail0_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs ->
  0 <= ds_strstart X -> 1 <= ds_lookahead X -> ds_strstart X + ds_lookahead X <= 2 * ws ->
  exists R M,
    msteps s6u_segs (mkst regs (0x19d88 : word) m s6u_rom) (mkst R (0x19da8 : word) M s6u_rom)
    /\ DI m1 M (avail0_st X)
    /\ HREGS R
    /\ (forall r : reg, reg_in r [10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hs0 Hl1 Hsl. open_di HDI. open_hregs HRG. pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof (ds6u_strstart _ _ _ _ Hsc) as C172. pose proof (ds6u_lookahead _ _ _ _ Hsc) as C180.
  run 12%nat NoDirs [RVal (EVar 35); RVal (EVar 36)] NoPins [(35%nat, 65537); (36%nat, 65537)] [ds_strstart X; ds_lookahead X] X.
  clear_aparts.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KMatchAvailable; KStrstart; KLookahead].
  ex2. split; [exact Hms|].
  split; [eq_DI; unfold avail0_st; st_close idtac|].
  split; [hregs_via HRG Hfr | fr_weak Hfr].
Qed.


Definition head_pc (X : deflate_state) : word :=
  if ds_lookahead X <? 262 then (0x169b8 : word) else (0x19dd0 : word).

Lemma head_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= ds_lookahead X <= 2 * ws ->
  exists R,
    msteps s6u_segs (mkst regs (0x19da8 : word) m s6u_rom) (mkst R (head_pc X) m s6u_rom)
    /\ HREGS R
    /\ (ds_lookahead X < 262 -> getr R 10 = zw S /\ getr R 1 = (0x19db8%bv : word))
    /\ (262 <= ds_lookahead X -> getr R 10 = zw (ds_lookahead X))
    /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r [1; 10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hlk. open_di HDI. open_hregs HRG. pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof (ds6u_lookahead _ _ _ _ Hsc) as C180.
  unfold head_pc. destruct (Z.ltb_spec (ds_lookahead X) 262) as [Hlo|Hhi].
  - run 6%nat [false] [RVal (EVar 35)] NoPins [(35%nat, 65537)] [ds_lookahead X] X.
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|].
    split; [intros _; split; reg1 HR Hfr|]. split; [intros; exfalso; lia|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - run 6%nat [true] [RVal (EVar 35)] NoPins [(35%nat, 65537)] [ds_lookahead X] X.
    ex1. split; [exact Hms|]. split; [hregs_via HRG Hfr|].
    split; [intros; exfalso; lia|]. split; [intros _; reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.


Definition fillr_pc (X : deflate_state) : word :=
  if (ds_lookahead X <? 262) && (flush =? 0) then (0x1a3bc : word)
  else if ds_lookahead X =? 0 then (0x1a3c4 : word)
  else if ds_lookahead X <? 3 then (0x19e9c : word) else (0x19dd0 : word).

Lemma fillr_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> 0 <= ds_lookahead X <= 2 * ws ->
  exists R,
    msteps s6u_segs (mkst regs (0x19db8 : word) m s6u_rom) (mkst R (fillr_pc X) m s6u_rom)
    /\ HREGS R /\ getr R 10 = zw (ds_lookahead X)
    /\ (forall r : reg, reg_in r [10; 11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hlk. open_di HDI. open_hregs HRG. pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof (ds6u_lookahead _ _ _ _ Hsc) as C180.
  unfold fillr_pc.
  Local Ltac fillr_fin HRG Hms HR Hfr := ex1; split; [exact Hms|]; split; [hregs_via HRG Hfr|]; split; [reg1 HR Hfr | fr_weak Hfr].
  destruct (Z.eqb_spec flush 0) as [Fz|Fnz].
  - destruct (Z.ltb_spec (ds_lookahead X) 262) as [Hlo|Hhi]; cbn [andb].
    + run 8%nat [false; true] [RVal (EVar 35)] NoPins [(35%nat, 65537)] [ds_lookahead X] X. fillr_fin HRG Hms HR Hfr.
    + replace (ds_lookahead X =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (ds_lookahead X <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
      run 8%nat [false; false; false; false] [RVal (EVar 35)] NoPins [(35%nat, 65537)] [ds_lookahead X] X. fillr_fin HRG Hms HR Hfr.
  - replace ((ds_lookahead X <? 262) && false) with false by (destruct (_ <? _); reflexivity).
    destruct (Z.eqb_spec (ds_lookahead X) 0) as [L0|L0].
    + run 8%nat [true; true] [RVal (EVar 35)] NoPins [(35%nat, 65537)] [ds_lookahead X] X. fillr_fin HRG Hms HR Hfr.
    + destruct (Z.ltb_spec (ds_lookahead X) 3) as [L3|L3].
      * run 8%nat [true; false; true] [RVal (EVar 35)] NoPins [(35%nat, 65537)] [ds_lookahead X] X. fillr_fin HRG Hms HR Hfr.
      * run 8%nat [true; false; false] [RVal (EVar 35)] NoPins [(35%nat, 65537)] [ds_lookahead X] X. fillr_fin HRG Hms HR Hfr.
Qed.


Lemma ret0_blk : forall regs m,
  getr regs 2 = zw SP ->
  exists R,
    msteps s6u_segs (mkst regs (0x1a3bc : word) m s6u_rom) (mkst R (0x1a608 : word) m s6u_rom)
    /\ getr R 10 = zw 0 /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m P2. open_min.
  run_gen [(2, EVar 33%nat)] 3%nat NoDirs NoReads NoPins NoBounds (@nil Z) ds.
  ex1. split; [exact Hms|]. repeat split; reg1 HR Hfr.
Qed.


Local Abbreviation ltail_st := DeflSlow6_2.ltail_st.

Lemma ltail_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs ->
  0 <= ds_strstart X -> 1 <= ds_lookahead X -> ds_strstart X + ds_lookahead X <= 2 * ws ->
  exists R M,
    msteps s6u_segs (mkst regs (0x1a388 : word) m s6u_rom) (mkst R (0x1a3a8 : word) M s6u_rom)
    /\ DI m1 M (ltail_st X)
    /\ HREGS R /\ getr R 10 = zw strm
    /\ (forall r : reg, reg_in r [10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG Hs0 Hl1 Hsl. open_di HDI. open_hregs HRG. pose proof (DeflSlow6_1.wf_wsz _ HWF) as Wws.
  pose proof (ds6u_strm _ _ _ _ Hsc) as C0. replace (S + 0) with S in C0 by lia.
  pose proof (ds6u_strstart _ _ _ _ Hsc) as C172. pose proof (ds6u_lookahead _ _ _ _ Hsc) as C180.
  run 12%nat [false] [RVal (EVar 35); RVal (EVar 36); RVal (EVar 37)] NoPins
    [(35%nat, 65537); (36%nat, 65537); (37%nat, 2 ^ 63)]
    [ds_strstart X; ds_lookahead X; strm] X.
  clear_aparts.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KStrstart; KLookahead].
  ex2. split; [exact Hms|].
  split; [eq_DI; unfold ltail_st; st_close idtac|].
  split; [hregs_via HRG Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.


Local Abbreviation avail_pc := DeflSlow6_6.avail_pc.

Lemma avo_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs -> getr regs 10 = zw strm -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1a3a8 : word) m s6u_rom) (mkst R (avail_pc X (0x1a608 : word) (0x19da8 : word)) m s6u_rom)
    /\ HREGS R /\ (cs_avail_out (ds_strm X) = 0 -> getr R 10 = zw 0)
    /\ (forall r : reg, reg_in r [10; 11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG P10 Hav. open_di HDI. open_hregs HRG.
  pose proof (zsl_avail_out s6u_segs _ _ _ _ _ Zs) as Z32.
  unfold avail_pc. destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
  - rewrite Hz in Z32.
    run_gen (HPINS ++ [(10, EVar 35%nat)]) 8%nat [false; false] [RVal (ELit 0)] NoPins [(35%nat, 2 ^ 63)] [strm] X.
    exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros _; reg1 HR Hfr | fr_weak Hfr].
  - pose proof (sx32_u64_nz (cs_avail_out (ds_strm X)) ltac:(lia)) as Hsx.
    run_gen (HPINS ++ [(10, EVar 35%nat)]) 8%nat [false; true] [RVal (EVar 36)] NoPins [(35%nat, 2 ^ 63); (36%nat, 2 ^ 32)]
      [strm; cs_avail_out (ds_strm X)] X.
    exists R. split; [exact Hms|]. split; [hregs_via HRG Hfr|]. split; [intros Hc; exfalso; lia | fr_weak Hfr].
Qed.

End Walk.
End FXG.

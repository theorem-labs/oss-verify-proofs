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
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2 MemFill
  RomRead TreesRod BitsLib BuildTreeLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel SendModel TreesTab BuildTreeModel GenBitlenModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 TreesRod6 Callee6 TreesApi6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import BuildTree6_1 BuildTree6_2 BuildTree6_3 BuildTree6_4 BuildTree6_5.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section Walk.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word) (sp : Z).
Variable (t : tree_id).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation T := (S + toff t).
Local Abbreviation E := (sd_elems t).
Local Abbreviation SP := (sp - 144).
Local Abbreviation BRm := (BR6 F mem0 S p PBL).
Local Abbreviation U := (bt_upd ds t).
Local Abbreviation SDA := (SDA R6).
Local Abbreviation STP := (STP R6).
Local Abbreviation EXP := (EXP R6).

Hypothesis HH : BTH F mem0 mem S p PBL ds ra sp.

Let Hret : ret_ok ra := bth_ret _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := bth_L _ _ _ _ _ _ _ _ _ HH.
Let HFS : sub_franges F S dsl_SIZE := bth_FS _ _ _ _ _ _ _ _ _ HH.
Let Hcf : call_frame F mem S PB PBL sp 144 := bth_fr _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := bth_br _ _ _ _ _ _ _ _ _ HH.
Let HRC0 : trees_rod_clear6 mem := bth_rod _ _ _ _ _ _ _ _ _ HH.
Let Hsp : 144 <= sp <= 2 ^ 63 := proj1 Hcf.
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.


Local Abbreviation GB := (BuildTree6_1.GB S sp).
Local Abbreviation CI := (BuildTree6_1.CI F mem0 S p PBL sp).
Local Abbreviation FRM := (BuildTree6_1.FRM sp).
Local Abbreviation stree_dl := (BuildTree6_1.stree_dl t).
Local Abbreviation stF := (BuildTree6_1.stF t).
Local Abbreviation L1REGS := (BuildTree6_1.L1REGS S sp t).
Local Abbreviation X0 := (BuildTree6_1.X0 ds t).
Local Abbreviation L1 := (BuildTree6_1.L1 t).
Local Abbreviation tsize_elems := (BuildTree6_1.tsize_elems t).
Local Abbreviation elems_range := (BuildTree6_1.elems_range t).
Local Abbreviation dsc_off_val := (BuildTree6_1.dsc_off_val t).
Local Abbreviation SDA_range := (BuildTree6_1.SDA_range t).
Local Abbreviation STP_range := (BuildTree6_1.STP_range t).
Local Abbreviation EXP_range := (BuildTree6_1.EXP_range t).
Local Abbreviation slen := (BuildTree6_2.slen t).
Local Abbreviation FREGS := (BuildTree6_5.FREGS S sp t).

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [BuildTree6_1.stF].

Local Ltac side_closer :=
  try solve [ assumption
            | nf; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; symex_read_auto
            | nf; symex_store_auto
            | nf; symex_sok_auto
            | intros; nf; first [apply pb_range | apply hv_range | apply wb_range | apply Z.mod_pos_bound; lia] ].

Local Ltac run_with C vb fuel dirs rds pins pv FC DL HP DP BC :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in vb in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs C fuel dirs rdv pinsv vbv NoRegions pv NoVals ((BuildTree6_1.stF t) FC DL HP DP BC) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Local Ltac open_ci_gen thin HC :=
  let HB := fresh "HB" in let HRC := fresh "HRC" in let HAG := fresh "HAG" in let MF := fresh "MF" in
  destruct HC as (HB & HRC & HAG & MF); unfold mapped in MF;
  let HS' := fresh "HS'" in let HPB' := fresh "HPB'" in let HD := fresh "HD" in
  pose proof HLb as HL'; destruct HL' as (HS' & HPB' & HD & _); unfold dsl_SIZE in HS', HD;
  let MS := fresh "MS" in let MP := fresh "MP" in let Hsc := fresh "Hsc" in let Har := fresh "Har" in let HTL := fresh "HTL" in
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & HTL & _ & _ & MS & MP & _); unfold mapped, dsl_SIZE in MS, MP;
  let C := fresh "C" in
  pose proof (BRT_cells _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB) as C;
  let CFC := fresh "CFC" in let CDL := fresh "CDL" in let CHP := fresh "CHP" in let CDP := fresh "CDP" in let CBC := fresh "CBC" in
  let Chl := fresh "Chl" in let Chm := fresh "Chm" in let Copt := fresh "Copt" in let Cstat := fresh "Cstat" in let Cmc := fresh "Cmc" in
  destruct C as (CFC & CDL & CHP & CDP & CBC & Chl & Chm & Copt & Cstat & Cmc);
  let Cdyn := fresh "Cdyn" in let Csd := fresh "Csd" in
  destruct (BRT_desc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB) as (Cdyn & Csd);
  replace (match t with TL => 168672 | TD => 168704 | TB => 168736 end) with (SDA t) in Csd by (destruct t; reflexivity);
  let Cst := fresh "Cst" in let Cex := fresh "Cex" in let Cbase := fresh "Cbase" in let Celems := fresh "Celems" in let Cml := fresh "Cml" in
  destruct (sdesc_cells R6 _ _ trod_ok6 HRC t) as (Cst & Cex & Cbase & Celems & Cml);
  clear Hsc Har;
  let Hsp' := fresh "Hsp'" in pose proof Hsp as Hsp';
  let Htt' := fresh "Htt'" in pose proof Htt as Htt';
  let He := fresh "He" in pose proof elems_range as He;
  let Hte := fresh "Hte" in pose proof tsize_elems as Hte;
  let Hdo := fresh "Hdo" in pose proof dsc_off_val as Hdo;
  let Hsda := fresh "Hsda" in pose proof SDA_range as Hsda;
  let Hstp := fresh "Hstp" in pose proof STP_range as Hstp;
  let RODS := fresh "RODS" in
  pose proof (mapped_rod_apart R6 _ _ S 5968 trod_ok6 HRC MS ltac:(lia) ltac:(lia)) as RODS;
  let RODF := fresh "RODF" in
  pose proof (mapped_rod_apart R6 _ _ (sp - 144) 144 trod_ok6 HRC MF ltac:(lia) ltac:(lia)) as RODF;
  cbn [tr_lo tr_hi tr_sdesc R6] in RODS, RODF;
  lazymatch thin with
  | true => clear RODS RODF HD Cst Cex Cbase Celems Cml Cdyn Csd; try clear HPB'
  | false => idtac
  end.
Local Ltac open_ci HC := open_ci_gen false HC.
Local Ltac open_ciT HC := open_ci_gen true HC.


Local Ltac ag_tower HAG :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold BuildTree6_1.GB;
              first [ apply sub_franges_here; unfold dsl_SIZE; cbn; lia
                    | apply sub_franges_later; apply sub_franges_here; cbn; lia
                    | apply sub_franges_later; apply sub_franges_later; apply sub_franges_here; cbn; lia ] ]);
  exact HAG.

Local Ltac rod_tower HRC MS MP MF :=
  apply (trees_rod_clear_wr R6 _ _ HRC);
  repeat (apply wr_ok_wbytes;
          [ | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
              rewrite ?length_Z_to_le_bytes in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length] in Hx;
              first [apply MS; lia | apply MP; lia | apply MF; lia]
            | lia | rewrite ?length_Z_to_le_bytes; cbn; lia ]);
  apply wr_ok_refl.

Local Ltac oth HFf :=
  rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul];
  first [ lia | unfold dsl_SIZE in *; lia | eapply sub_franges_mono; [exact HFf | lia | lia] ].

Local Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); assumption end
        | let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf;
            first [assumption | reflexivity | f_equal; lia | f_equal; f_equal; lia | f_equal; repeat (rewrite (szwrap_small 32) by lia); lia
                  | rewrite zw_u; assumption ] end ].
Local Ltac regs_of HR Hfr := repeat split; reg1 HR Hfr.

Local Ltac blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf ks tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwdT HB M ks ltac:(oth HFf);
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [ eapply BR_eqst; [exact HB2|]; clear HB2; st_eqT; try reflexivity
                          | split; [ rod_tower HRC MS MP MF
                                   | split; [ ag_tower HAG
                                            | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                                              repeat (apply wbytes_grows); apply MF; exact Hx ] ] ]
                 | tregs ]
      end
  end.


Definition FB6 : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 16); (6%nat, 65536)].

Definition stC6 : cfg :=
  CFG FB6 [] [EVar 1%nat] [0x27c04; 0x1be5c; 0x1bed0; 0x1befc; 0x1bf7c; 0x1c074]
      [AV (EAdd (EVar 32) (EShl (EVar 38) 2)) 3008 4 2 (EVar 38);
       AV (EAdd (EVar 32) (EShl (EVar 36) 2)) 3008 4 2 (EVar 36);
       AV (EAdd (EVar 33) (EShl (EApp1 2 (EVar 38)) 2)) 2 2 1 (EApp1 2 (EVar 38));
       AV (EAdd (EVar 33) (EShl (EApp1 2 (EVar 36)) 2)) 2 2 1 (EApp1 2 (EVar 36));
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EApp1 2 (EVar 36))) 2)) 2 2 1 (EApp1 1 (EApp1 2 (EVar 36)));
       AV (EAdd (EVar 33) (EShl (EVar 48) 2)) 0 2 0 (EVar 48);
       AV (EAdd (EVar 50) (EShl (EVar 49) 1)) 0 2 4 (EVar 49);
       AV (EAdd (EVar 45) (EShl (EVar 48) 2)) 2 2 6 (EVar 48)].

Definition VB6 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300); (36%nat, 600); (37%nat, 600);
   (38%nat, 600); (39%nat, 16); (40%nat, 300); (41%nat, 600); (42%nat, 2 ^ 64); (43%nat, 2 ^ 64);
   (44%nat, 2 ^ 63); (45%nat, 2 ^ 63); (46%nat, 3000); (47%nat, 2 ^ 63); (48%nat, 600); (49%nat, 16);
   (50%nat, 2 ^ 63); (51%nat, 65536)].

Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC6 VB6 fuel dirs rds pins pv FC DL HP DP BC.

Local Abbreviation ML := (sd_max_length t).
Local Abbreviation BASE := (sd_extra_base t).

Lemma ml_range : 7 <= ML <= 15.
Proof. destruct t; cbn; unfold MAX_BITS, MAX_BL_BITS; lia. Qed.
Lemma base_range : 0 <= BASE < 300 /\ BASE < E.
Proof. pose proof elems_range. destruct t; cbn in *; unfold LITERALS, L_CODES, LITERALS, LENGTH_CODES in *; lia. Qed.
Lemma EXP_span : 0x11ae0 <= EXP t /\ EXP t + 4 * (E - BASE) <= 0x12510.
Proof.
  destruct t; cbn; unfold L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES; lia.
Qed.

Lemma extra_view_bound : forall x, 0 <= stF (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) 5%nat x < 16.
Proof.
  intros x. cbn [BuildTree6_1.stF]. destruct t; cbn [sd_extra_bits].
  - pose proof (extra_lbits_bound x). rewrite Z.mod_small; lia.
  - pose proof (extra_dbits_bound x). rewrite Z.mod_small; lia.
  - pose proof (extra_blbits_bound x). rewrite Z.mod_small; lia.
Qed.
Lemma extra_view_bound' : forall FC DL HP DP BC x, 0 <= stF FC DL HP DP BC 5%nat x < 16.
Proof. intros. apply extra_view_bound. Qed.

Lemma extra_read : forall m i a, trees_rod_clear6 m -> 0 <= i < E - BASE -> a = EXP t + i * 2 ^ 2 ->
  exists bs, rdn s6_segs m (zw a) 4 = Some bs /\ bytes_le_to_Z bs = arr_get (sd_extra_bits t) i mod 2 ^ 32.
Proof.
  intros m i a HRC Hi ->.
  destruct t; cbn [TreesRod.EXP sd_extra_bits sd_elems sd_extra_base] in *; unfold L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES in *.
  - pose proof (extra_lbits_bound i). rewrite Z.mod_small by lia. apply (extra_lbits_read R6 _ m trod_ok6 HRC i); cbn; lia.
  - pose proof (extra_dbits_bound i). rewrite Z.mod_small by lia. apply (extra_dbits_read R6 _ m trod_ok6 HRC i); cbn; lia.
  - pose proof (extra_blbits_bound i). rewrite Z.mod_small by lia. apply (extra_blbits_read R6 _ m trod_ok6 HRC i); cbn; lia.
Qed.

Lemma ret_ok_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_ok (zw z).
Proof. intros z Hz He. apply ret_ok_even. rewrite u_zw_small by exact Hz. exact He. Qed.

Lemma wrap16_sx_addk : forall a k, wrap16 (szwrap 16 a + k) = wrap16 (a + k).
Proof.
  intros a k. rewrite !wrap16_mod.
  rewrite Z.add_mod, szwrap_eqm, <- Z.add_mod by lia. reflexivity.
Qed.

Section PhaseFG.
Variables (FC HP : arr) (DP : arr) (MC K : Z).
Local Abbreviation W4 DL BC OL SL := (U FC DL HP 1 (K - 1) DP BC OL SL MC).

Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis Hmc : 0 <= MC < E.
Hypothesis HK : 1 <= K <= 573.
Hypothesis PQH : forall h, K <= h < 573 -> 0 <= arr_get HP h < tsize t.

Definition GB6 (R : bvmap 5 word) : Prop :=
  getr R 23 = zw T /\ getr R 24 = zw MC /\ getr R 26 = zw (STP t) /\ getr R 27 = zw (EXP t)
  /\ getr R 21 = zw BASE /\ getr R 25 = zw ML /\ getr R 8 = zw (S + 2976) /\ getr R 20 = zw (S + 5300)
  /\ getr R 9 = zw S /\ getr R 22 = zw (S + 3008) /\ getr R 19 = zw MC /\ getr R 18 = zw T /\ getr R 2 = zw SP.
Definition GP6 : list (Z * expr) :=
  [(23, EVar 33); (24, EVar 37); (26, EVar 45); (27, EVar 44); (21, EVar 40); (25, EVar 39); (8, EVar 50);
   (20, EAdd (EVar 32) (ELit 5300)); (9, EVar 32); (22, EAdd (EVar 32) (ELit 3008)); (19, EVar 37); (18, EVar 33); (2, EVar 34)].

Definition GS (R : bvmap 5 word) (h ovf : Z) : Prop :=
  GB6 R /\ getr R 10 = zw ovf /\ getr R 12 = zw (2 ^ 32 - 1) /\ getr R 13 = zw (h + 1)
  /\ getr R 14 = zw (S + h * 4 + 3008) /\ getr R 15 = zw 573 /\ getr R 11 = zw 2976.
Definition GSP : list (Z * expr) :=
  GP6 ++ [(10, EVar 41); (12, ELit 4294967295); (13, EAdd (EVar 36) (ELit 1));
          (14, EAdd (EAdd (EVar 32) (EShl (EVar 36) 2)) (ELit 3008)); (15, ELit 573); (11, ELit 2976)].
Definition GSA (R : bvmap 5 word) (h ovf n bits ld : Z) : Prop :=
  GS R h ovf /\ getr R 7 = zw n /\ getr R 5 = zw (T + n * 4) /\ getr R 17 = zw (n * 4) /\ getr R 6 = zw bits
  /\ getr R 16 = zw ld.
Definition GSAP : list (Z * expr) :=
  GSP ++ [(7, EVar 48); (5, EAdd (EVar 33) (EShl (EVar 48) 2)); (17, EShl (EVar 48) 2); (6, EVar 49); (16, EVar 51)].

Definition GI (m1 m : word -> option byte) (DL BC : arr) (OL SL : Z) : Prop :=
  CI m1 m (W4 DL BC OL SL)
  /\ (forall i, 0 <= i < tsize t -> 0 <= arr_get DL i < 65536) /\ arr_len DL = tsize t
  /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) /\ arr_len BC = 16
  /\ 0 <= OL < 2 ^ 64 /\ 0 <= SL < 2 ^ 64
  /\ cell s6_segs m SP 8 (S + 2047).

Local Ltac side6 :=
  try solve [ intros; apply extra_view_bound' ].

Local Ltac vfix :=
  repeat match goal with H : hv ?hh ?e = _ |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with
         | H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H
         | H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H
         end.
Local Ltac ag_read :=
  lazymatch goal with
  | |- exists bs, rdn ?sg ?m (zw ?a) ?n = Some bs /\ bytes_le_to_Z bs = arr_get ?tt ?i =>
      match goal with
      | H : cells sg m ?P 4 2%nat ?len (arr_get tt) |- _ =>
          eapply (fc_read_at sg m P len (arr_get tt) i a _ H); [lia | arr_range_auto | lia | reflexivity]
      | H : cells sg m ?P 4 4%nat ?len (arr_get tt) |- _ =>
          eapply (u32_read_at sg m P len (arr_get tt) i a _ H); [lia | arr_range_auto | lia | reflexivity]
      | H : cells sg m ?P 1 1%nat ?len (arr_get tt) |- _ =>
          eapply (bytes_read_at sg m P len (arr_get tt) i a _ H); [lia | arr_range_auto | lia | reflexivity]
      | H : cells sg m ?P 2 2%nat ?len (arr_get tt) |- _ =>
          eapply (u16_read_at sg m P len (arr_get tt) i a _ H); [lia | arr_range_auto | change (2 ^ 1) with 2; lia | reflexivity]
      end
  end.

Ltac side_closer ::=
  try solve [ assumption
            | nf; vfix; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; symex_read_auto
            | nf; vfix; first [ symex_read_auto | ag_read ]
            | nf; vfix; symex_store_auto
            | nf; vfix; symex_sok_auto
            | intros; nf; first [apply pb_range | apply hv_range | apply wb_range | apply Z.mod_pos_bound; lia] ].

Local Ltac reg1G HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); assumption end
        | let A := fresh "A" in
          lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf; vfix;
            first [ assumption
                  | lazymatch goal with |- ?a = ?a => reflexivity end
                  | f_equal; lia
                  | f_equal; repeat (rewrite (szwrap_small 32) by lia); rewrite ?Z.mod_small by lia; lia
                  | rewrite zw_u; assumption
                  | lazymatch goal with |- zw ?a = zw ?b => lazymatch isZcst a with true => lazymatch isZcst b with true =>
                      apply bv_eq; vm_compute; reflexivity end end end
                  | idtac ] end ].
Local Ltac regsG HR Hfr := repeat split; reg1G HR Hfr.

Local Ltac blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf ks tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwdT HB M ks ltac:(oth HFf);
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [ split; [ eapply BR_eqst; [exact HB2|]; clear HB2; st_eqT; try reflexivity
                                   | split; [ rod_tower HRC MS MP MF
                                            | split; [ ag_tower HAG
                                                     | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                                                       repeat (apply wbytes_grows); apply MF; exact Hx ] ] ]
                          | ]
                 | tregs ]
      end
  end.

Local Ltac nf_in H :=
  let T := type of H in let T' := eval cbn [BuildTree6_1.stF] in T in symex_recast H T'.

Local Ltac splitand H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "X" in let H2 := fresh "X" in destruct H as [H1 H2]; splitand H1; splitand H2
  | _ => idtac
  end.


Definition FX (R : bvmap 5 word) : Prop := GB6 R /\ getr R 10 = zw (S + 2976).

Lemma f1_blk : forall regs m1 m DL HP0 BC OL SL,
  CI m1 m (U FC DL HP0 1 K DP BC OL SL MC) -> 0 <= arr_get HP0 1 < 573 -> arr_len HP0 = 573 ->
  cell s6_segs m SP 8 (S + 2047) ->
  FREGS MC regs ->
  exists R m',
    msteps s6_segs (mkst regs (0x1be14 : word) m s6_rom) (mkst R (0x27c04 : word) m' s6_rom)
    /\ CI m1 m' (U FC DL (arr_set HP0 (K - 1) (arr_get HP0 1)) 1 (K - 1) DP BC OL SL MC)
    /\ (FX R /\ getr R 11 = zw 0 /\ getr R 12 = zw 32 /\ getr R 1 = zw 0x1be5c)
    /\ cell s6_segs m' SP 8 (S + 2047)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL HP0 BC OL SL HC R1 LHP C0 HF.
  open_ci HC. destruct HF as (P9 & P18 & P20 & P8 & P22 & P11 & P19 & P2).
  assert (P8' : getr regs 8 = zw (S + 2976)) by exact P8.
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml. pose proof base_range as Hbase. pose proof EXP_span as Hexp.
  assert (V1 : hv HP0 1 = arr_get HP0 1) by (apply hv_get; lia).
  run 30%nat NoDirs [RVal (EVar 38); RVal (EApp1 2 (ELit 1)); RVal (EVar 47); RVal (EVar 33); RVal (EVar 37);
                     RVal (EVar 45); RVal (EVar 44); RVal (EVar 40); RVal (EVar 39)]
      [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (8, EVar 50); (22, EAdd (EVar 32) (ELit 3008));
       (11, EAdd (EVar 32) (EVar 46)); (19, EVar 37); (2, EVar 34)]
      [S; T; SP; E; 0; MC; K; ML; BASE; 0; 0; 0; EXP t; STP t; dsc_off t; SDA t; 0; 0; S + 2976; 0] FC DL HP0 DP BC; side6.
  nf_in Hms. rewrite !V1 in Hms.
  blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KHm; KHeap (K - 1)]
    ltac:(split; [split; [unfold FX, GB6; regsG HR Hfr | regsG HR Hfr] | split; [frame_cells | fr_weak Hfr]]).
Qed.

Goal True. idtac "f1 OK". exact I. Qed.

Lemma call_memset : forall regs m1 m DL HP' BC OL SL,
  memset_run6 ->
  CI m1 m (U FC DL HP' 1 (K - 1) DP BC OL SL MC) -> arr_len BC = 16 ->
  FX regs /\ getr regs 11 = zw 0 /\ getr regs 12 = zw 32 /\ getr regs 1 = zw 0x1be5c ->
  exists R m',
    msteps s6_segs (mkst regs (0x27c04 : word) m s6_rom) (mkst R (0x1be5c : word) m' s6_rom)
    /\ CI m1 m' (U FC DL HP' 1 (K - 1) DP (arr_fill BC 0 16 0) OL SL MC)
    /\ FX R
    /\ (forall a w v, cell s6_segs m a w v -> SP <= a -> a + Z.of_nat w <= SP + 144 -> cell s6_segs m' a w v)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL HP' BC OL SL MEMSET HC LBC (HX & P11 & P12 & P1).
  destruct HC as (HB & HRC & HAG & MF).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & HTL & _ & _ & MS & MP & _).
  pose proof HLb as (HS' & _). unfold dsl_SIZE in HS', MS.
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS. pose proof Hsp as Hsp'.
  pose proof HX as (_ & P10).
  assert (Hret' : ret_ok (zw 0x1be5c)) by (apply ret_ok_lit; [lia | reflexivity]).
  destruct (MEMSET m regs (S + 2976) 0 32 _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(intros x Hx; apply MS; lia) Hret' P1 P10 P11 P12)
    as (R & m' & Hms & Q10 & Hfr & Hfill & Hsame & Hgr).
  symex_pc_lit_in Hms.
  assert (Hag : agree_out [(S + 2976, 32)] m m').
  { apply (same_outside_agree_out m m' (S + 2976) (S + 2976 + 32)); [exact Hsame|]. intros x Hx. left. cbn. lia. }
  assert (CELLS : forall a w v, cell s6_segs m a w v -> SP <= a -> a + Z.of_nat w <= SP + 144 -> cell s6_segs m' a w v).
  { intros a w v Hc Ha1 Ha2.
    apply (cell_agree_out s6_segs [(S + 2976, 32)] m m'); [exact Hag | | lia | lia | exact Hc].
    intros x Hx [Hin|[]]. cbn in Hin. lia. }
  exists R, m'. split; [exact Hms|].
  split.
  { split; [|split; [|split]].
    - exact (BRT_blc_fill _ _ _ _ F mem0 S p PBL HLb HFS ds t m m' _ _ _ _ _ _ _ _ _ _ HB LBC Hfill Hsame Hgr).
    - apply (trees_rod_clear_agree R6 [(S + 2976, 32)] m m' HRC Hag). intros x [Hx|[]]. cbn in Hx. apply MS. lia.
    - eapply agree_out_trans; [exact HAG|]. eapply agree_out_weaken; [exact Hag|].
      intros x [Hx|[]]. cbn in Hx. unfold BuildTree6_1.GB. left. cbn. unfold dsl_SIZE. lia.
    - intros x Hx. apply Hgr. apply MF. exact Hx. }
  split; [| split; [exact CELLS|]].
  - pose proof HX as X. unfold FX, GB6 in X |- *. splitand X.
    repeat split; lazymatch goal with |- getr R ?x = _ => first [rewrite (Hfr x eq_refl); assumption | exact Q10] end.
  - intros r Hr. apply Hfr. eapply reg_in_sub; [|exact Hr]. reflexivity.
Qed.

Goal True. idtac "call_memset OK". exact I. Qed.

Lemma f2_blk : forall regs m1 m DL BC OL SL,
  CI m1 m (W4 DL BC OL SL) -> K <= 573 ->
  cell s6_segs m SP 8 (S + 2047) ->
  FX regs ->
  let h1 := arr_get HP (K - 1) in
  0 <= h1 < tsize t ->
  exists R m',
    msteps s6_segs (mkst regs (0x1be5c : word) m s6_rom)
           (mkst R (if 572 <? K then (0x1c074 : word) else (0x1bed0 : word)) m' s6_rom)
    /\ CI m1 m' (W4 (arr_set DL h1 (wrap16 0)) BC OL SL)
    /\ (if 572 <? K then GB6 R else GS R K 0)
    /\ cell s6_segs m' SP 8 (S + 2047)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL BC OL SL HC HK' C0 HX h1 Rh1.
  open_ciT HC. destruct HX as ((P23 & P24 & P26 & P27 & P21 & P25 & P8 & P20 & P9 & P22 & P19 & P18 & P2) & P10).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml. pose proof base_range as Hbase. pose proof EXP_span as Hexp.
  assert (Vh1 : hv HP (K - 1) = h1) by (subst h1; apply hv_get; lia).
  destruct (Z.ltb_spec 572 K) as [CK|CK].
  - run 30%nat [true] [RVal (EVar 38)] GP6
        [S; T; SP; E; 0; MC; K - 1; ML; BASE; 0; 0; 0; EXP t; STP t; 0; 0; 0; 0; S + 2976; 0] FC DL HP DP BC; side6.
    nf_in Hms. rewrite !Vh1 in Hms.
    blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KDl h1]
      ltac:(split; [unfold GB6; regsG HR Hfr | split; [frame_cells | fr_weak Hfr]]).
  - run 30%nat [false] [RVal (EVar 38)] GP6
        [S; T; SP; E; 0; MC; K - 1; ML; BASE; 0; 0; 0; EXP t; STP t; 0; 0; 0; 0; S + 2976; 0] FC DL HP DP BC; side6.
    nf_in Hms. rewrite !Vh1 in Hms.
    blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KDl h1]
      ltac:(split; [unfold GS, GB6; regsG HR Hfr | split; [frame_cells | fr_weak Hfr]]).
Qed.

Goal True. idtac "f2 OK". exact I. Qed.


Local Ltac openGI HG HC RDL LDL RBC LBC ROL RSL C0 :=
  destruct HG as (HC & RDL & LDL & RBC & LBC & ROL & RSL & C0).

Local Ltac nodeG DL h RDL LDL Rd Vh Vn Vd Vdd :=
  assert (Vh : hv HP h = arr_get HP h) by (apply hv_get; lia);
  assert (Vn : pb DL (arr_get HP h) = arr_get DL (arr_get HP h)) by (apply (pb_get DL); [intros q Hq; apply RDL; rewrite <- LDL; exact Hq | rewrite LDL; lia]);
  assert (Vd : pb DL (arr_get DL (arr_get HP h)) = arr_get DL (arr_get DL (arr_get HP h)))
    by (apply (pb_get DL); [intros q Hq; apply RDL; rewrite <- LDL; exact Hq | rewrite LDL; lia]);
  pose proof (RDL (arr_get DL (arr_get HP h)) Rd) as Vdd.

Lemma gA_blk : forall regs m1 m DL BC OL SL h ovf,
  GI m1 m DL BC OL SL -> K <= h <= 572 -> 0 <= ovf < 599 ->
  0 <= arr_get DL (arr_get HP h) < tsize t ->
  GS regs h ovf ->
  let n := arr_get HP h in
  let ld := arr_get DL (arr_get DL n) in
  let bits := if ML <=? ld then ML else ld + 1 in
  exists R m',
    msteps s6_segs (mkst regs (0x1bed0 : word) m s6_rom) (mkst R (0x1befc : word) m' s6_rom)
    /\ GI m1 m' (arr_set DL n (wrap16 bits)) BC OL SL
    /\ GSA R h ovf n bits ld
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL BC OL SL h ovf HG Hh Hovf Rd HR0.
  openGI HG HC RDL LDL RBC LBC ROL RSL C0. open_ciT HC.
  destruct HR0 as ((P23 & P24 & P26 & P27 & P21 & P25 & P8 & P20 & P9 & P22 & P19 & P18 & P2) & P10 & P12 & P13 & P14 & P15 & P11x).
  pose proof Hcf as (_ & HFf & _ & HfS & _). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml. pose proof base_range as Hbase. pose proof EXP_span as Hexp.
  pose proof (PQH h ltac:(lia)) as Rn.
  nodeG DL h RDL LDL Rd Vh Vn Vd Vdd.
  cbv zeta.
  destruct (Z.leb_spec ML (arr_get DL (arr_get DL (arr_get HP h)))) as [Cb|Cb].
  - run 20%nat [true] NoReads GSP
        [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; 0; 0; EXP t; STP t; 0; 0; 0; 0; S + 2976; 0] FC DL HP DP BC; side6.
    nf_in Hms. rewrite !Vh in Hms.
    blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KDl (arr_get HP h)]
      ltac:(split; [unfold GSA, GS, GB6; regsG HR Hfr | fr_weak Hfr]).
    split; [|split; [rewrite arr_len_set; exact LDL | split; [exact RBC | split; [exact LBC | split; [lia | split; [lia | nf; vfix; frame_cells]]]]]].
    intros i Hi. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range ML); lia | apply RDL; exact Hi].
  - run 20%nat [false] NoReads GSP
        [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; 0; 0; EXP t; STP t; 0; 0; 0; 0; S + 2976; 0] FC DL HP DP BC; side6.
    nf_in Hms. rewrite !Vh, !Vn, !Vd in Hms.
    blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KDl (arr_get HP h)]
      ltac:(split; [unfold GSA, GS, GB6; regsG HR Hfr | fr_weak Hfr]).
    split; [|split; [rewrite arr_len_set; exact LDL | split; [exact RBC | split; [exact LBC | split; [lia | split; [lia | nf; vfix; frame_cells]]]]]].
    intros i Hi. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range (arr_get DL (arr_get DL (arr_get HP h)) + 1)); lia | apply RDL; exact Hi].
Qed.

Goal True. idtac "gA OK". exact I. Qed.


Lemma lxor_ltb1 : forall a b, Z.lxor (if a <? b then 1 else 0) 1 = (if b <=? a then 1 else 0).
Proof. intros a b. destruct (Z.ltb_spec a b), (Z.leb_spec b a); try lia; reflexivity. Qed.

Local Abbreviation xbits := (GenBitlenModel.xbits t).

Lemma xbits_range : forall n, 0 <= xbits n < 16.
Proof.
  intros n. unfold GenBitlenModel.xbits. destruct (BASE <=? n); [|lia].
  pose proof (extra_lbits_bound (n - BASE)). pose proof (extra_dbits_bound (n - BASE)). pose proof (extra_blbits_bound (n - BASE)).
  destruct t; cbn [sd_extra_bits]; lia.
Qed.

Lemma slen_E : STP t <> 0 -> E <= slen.
Proof.
  unfold BuildTree6_2.slen. destruct t; cbn [sd_elems TreesRod.STP];
    unfold L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES; cbn; intros; lia.
Qed.

Local Ltac ceqG :=
  nf; vfix;
  repeat match goal with H : _ mod 2 ^ 32 = xbits _ |- context [_ mod 2 ^ 32] => rewrite H end;
  repeat match goal with H : xbits ?n = 0 |- context [xbits ?n] => rewrite H end;
  rewrite <- ?BuildTree6_2.stree_Len_dl; rewrite ?wrap16_sx_addk;
  first [ reflexivity | f_equal; lia | f_equal; ring ].

Lemma GI_auxB : forall BC bits w,
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) -> arr_len BC = 16 ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get (arr_set BC bits (wrap16 w)) i < 65536) /\ arr_len (arr_set BC bits (wrap16 w)) = 16.
Proof.
  intros BC bits w RBC LBC. split; [| rewrite arr_len_set; exact LBC].
  intros i Hi. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range w); lia | apply RBC; exact Hi].
Qed.

Lemma gB_blk : forall regs m1 m DL BC OL SL h ovf n bits ld,
  GI m1 m DL BC OL SL -> K <= h <= 572 -> 0 <= ovf < 599 -> n = arr_get HP h -> 1 <= bits <= ML -> 0 <= ld < 65536 ->
  GSA regs h ovf n bits ld ->
  let ovf' := if ML <=? ld then ovf + 1 else ovf in
  exists R m',
    msteps s6_segs (mkst regs (0x1befc : word) m s6_rom)
           (mkst R (if h =? 572 then (0x1bf7c : word) else (0x1bed0 : word)) m' s6_rom)
    /\ (if MC <? n then GI m1 m' DL BC OL SL
        else GI m1 m' DL (arr_set BC bits (wrap16 (arr_get BC bits + 1)))
                (wrap64 (OL + arr_get FC n * (bits + xbits n)))
                (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xbits n)) else SL))
    /\ GS R (h + 1) ovf'
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL BC OL SL h ovf n bits ld HG Hh Hovf Hn Hbits Hld HR0.
  openGI HG HC RDL LDL RBC LBC ROL RSL C0. open_ci HC.
  destruct HR0 as (((P23 & P24 & P26 & P27 & P21 & P25 & P8 & P20 & P9 & P22 & P19 & P18 & P2) & P10 & P12 & P13 & P14 & P15 & P11x) & P7 & P5 & P17 & P6 & P16).
  pose proof Hcf as (_ & HFf & _ & HfS & _). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml. pose proof base_range as Hbase. pose proof EXP_span as Hexp.
  pose proof (PQH h ltac:(lia)) as Rn. rewrite <- Hn in Rn.
  pose proof (lxor_ltb1 ld ML) as Hx.
  assert (Vf : pb FC n = arr_get FC n) by (apply (pb_get FC); [intros q Hq; apply RFC; rewrite <- LFC; exact Hq | rewrite LFC; lia]).
  assert (Vb : pb BC bits = arr_get BC bits) by (apply (pb_get BC); [intros q Hq; apply RBC; rewrite <- LBC; exact Hq | rewrite LBC; lia]).
  pose proof (RFC n ltac:(lia)) as Rf. pose proof (RBC bits ltac:(lia)) as Rb.
  pose proof (xbits_range n) as Rx.
  assert (RODS' : S + 5968 <= 0x11ae0 \/ 0x12510 <= S) by (destruct RODS as [RS _]; lia).
  clear HD Cdyn Csd Cst Cex Cbase Celems Cml RODS RODF HPB'.
  cbv zeta.
  destruct (Z.ltb_spec MC n) as [Cl|Cl].
  -
    destruct (Z.eqb_spec h 572) as [Ce|Ce].
    + run 20%nat [true; true] NoReads GSAP
          [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; 0; 0; EXP t; STP t; 0; 0; n; bits; S + 2976; ld] FC DL HP DP BC; side6.
      exists R, m. split; [exact Hms|].
      split; [split; [split; [exact HB | split; [exact HRC | split; [exact HAG | exact MF]]] | repeat (split; [assumption|]); exact C0]|].
      split; [unfold GS, GB6; regsG HR Hfr; rewrite ?Hx; destruct (ML <=? ld); f_equal; lia | fr_weak Hfr].
    + run 20%nat [true; false] NoReads GSAP
          [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; 0; 0; EXP t; STP t; 0; 0; n; bits; S + 2976; ld] FC DL HP DP BC; side6.
      exists R, m. split; [exact Hms|].
      split; [split; [split; [exact HB | split; [exact HRC | split; [exact HAG | exact MF]]] | repeat (split; [assumption|]); exact C0]|].
      split; [unfold GS, GB6; regsG HR Hfr; rewrite ?Hx; destruct (ML <=? ld); f_equal; lia | fr_weak Hfr].
  - pose proof (GI_auxB BC bits (arr_get BC bits + 1) RBC LBC) as (A3 & A4).
    destruct (Z.eqb_spec (STP t) 0) as [Cs|Cs].
    +
      replace (stree_has t) with false
        by (symmetry; destruct (stree_has t) eqn:Es; [exfalso; exact (proj1 (BuildTree6_2.stree_has_STP t) Es Cs) | reflexivity]).
      rewrite Cs in P26.
      destruct (Z.leb_spec BASE n) as [Cx|Cx].
      * assert (Vx : arr_get (sd_extra_bits t) (n - BASE) mod 2 ^ 32 = xbits n)
          by (unfold GenBitlenModel.xbits; rewrite (proj2 (Z.leb_le _ _) Cx); apply Z.mod_small; unfold GenBitlenModel.xbits in Rx; rewrite (proj2 (Z.leb_le _ _) Cx) in Rx; lia).
        destruct (Z.eqb_spec h 572) as [Ce|Ce].
        -- run 60%nat [false; true; true; true] [RVal (EApp1 5 (ESub (EVar 48) (EVar 40))); RVal (EVar 42)]
              (GSP ++ [(7, EVar 48); (5, EAdd (EVar 33) (EShl (EVar 48) 2)); (17, EShl (EVar 48) 2); (6, EVar 49); (16, EVar 51); (26, ELit 0)])
              [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; 0; EXP t; 0; 0; 0; n; bits; S + 2976; ld] FC DL HP DP BC; side6.
           all: try (nf; rewrite ?(szwrap_small 32) by lia; eapply extra_read; [exact HRC | lia | lia]).
           nf_in Hms. rewrite ?Vb, ?Vf in Hms.
           blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW]
             ltac:(split; [unfold GS, GB6; regsG HR Hfr; rewrite ?Hx; destruct (ML <=? ld); f_equal; lia | fr_weak Hfr]).
           all: try ceqG.
           split; [exact RDL|]. split; [exact LDL|]. split; [exact A3|]. split; [exact A4|].
           split; [apply wrap64_range|]. split; [exact RSL|]. nf; vfix; frame_cells.
        -- run 60%nat [false; true; true; false] [RVal (EApp1 5 (ESub (EVar 48) (EVar 40))); RVal (EVar 42)]
              (GSP ++ [(7, EVar 48); (5, EAdd (EVar 33) (EShl (EVar 48) 2)); (17, EShl (EVar 48) 2); (6, EVar 49); (16, EVar 51); (26, ELit 0)])
              [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; 0; EXP t; 0; 0; 0; n; bits; S + 2976; ld] FC DL HP DP BC; side6.
           all: try (nf; rewrite ?(szwrap_small 32) by lia; eapply extra_read; [exact HRC | lia | lia]).
           nf_in Hms. rewrite ?Vb, ?Vf in Hms.
           blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW]
             ltac:(split; [unfold GS, GB6; regsG HR Hfr; rewrite ?Hx; destruct (ML <=? ld); f_equal; lia | fr_weak Hfr]).
           all: try ceqG.
           split; [exact RDL|]. split; [exact LDL|]. split; [exact A3|]. split; [exact A4|].
           split; [apply wrap64_range|]. split; [exact RSL|]. nf; vfix; frame_cells.
      * assert (Vx : xbits n = 0) by (unfold GenBitlenModel.xbits; rewrite (proj2 (Z.leb_gt _ _)) by lia; reflexivity).
        destruct (Z.eqb_spec h 572) as [Ce|Ce].
        -- run 60%nat [false; false; true; true] [RVal (EVar 42)]
              (GSP ++ [(7, EVar 48); (5, EAdd (EVar 33) (EShl (EVar 48) 2)); (17, EShl (EVar 48) 2); (6, EVar 49); (16, EVar 51); (26, ELit 0)])
              [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; 0; EXP t; 0; 0; 0; n; bits; S + 2976; ld] FC DL HP DP BC; side6.
           nf_in Hms. rewrite ?Vb, ?Vf in Hms.
           blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW]
             ltac:(split; [unfold GS, GB6; regsG HR Hfr; rewrite ?Hx; destruct (ML <=? ld); f_equal; lia | fr_weak Hfr]).
           all: try ceqG.
           split; [exact RDL|]. split; [exact LDL|]. split; [exact A3|]. split; [exact A4|].
           split; [apply wrap64_range|]. split; [exact RSL|]. nf; vfix; frame_cells.
        -- run 60%nat [false; false; true; false] [RVal (EVar 42)]
              (GSP ++ [(7, EVar 48); (5, EAdd (EVar 33) (EShl (EVar 48) 2)); (17, EShl (EVar 48) 2); (6, EVar 49); (16, EVar 51); (26, ELit 0)])
              [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; 0; EXP t; 0; 0; 0; n; bits; S + 2976; ld] FC DL HP DP BC; side6.
           nf_in Hms. rewrite ?Vb, ?Vf in Hms.
           blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW]
             ltac:(split; [unfold GS, GB6; regsG HR Hfr; rewrite ?Hx; destruct (ML <=? ld); f_equal; lia | fr_weak Hfr]).
           all: try ceqG.
           split; [exact RDL|]. split; [exact LDL|]. split; [exact A3|]. split; [exact A4|].
           split; [apply wrap64_range|]. split; [exact RSL|]. nf; vfix; frame_cells.
    +
      replace (stree_has t) with true by (symmetry; apply (proj2 (BuildTree6_2.stree_has_STP t)); exact Cs).
      pose proof (BuildTree6_2.stree_cells t m HRC Cs) as Cstl. pose proof (BuildTree6_2.stree_dl_bound t) as Rstl.
      pose proof (BuildTree6_2.slen_ge t Cs) as Hsl. pose proof (BuildTree6_2.STP_rod t Cs) as Hstr. pose proof (slen_E Cs) as HsE.
      assert (Vs : pb stree_dl n = arr_get stree_dl n) by (apply BuildTree6_2.stree_pb; lia).
      destruct (Z.leb_spec BASE n) as [Cx|Cx].
      * assert (Vx : arr_get (sd_extra_bits t) (n - BASE) mod 2 ^ 32 = xbits n)
          by (unfold GenBitlenModel.xbits; rewrite (proj2 (Z.leb_le _ _) Cx); apply Z.mod_small; unfold GenBitlenModel.xbits in Rx; rewrite (proj2 (Z.leb_le _ _) Cx) in Rx; lia).
        destruct (Z.eqb_spec h 572) as [Ce|Ce].
        -- run 60%nat [false; true; false; true] [RVal (EApp1 5 (ESub (EVar 48) (EVar 40))); RVal (EVar 42); RVal (EVar 43)] GSAP
              [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; SL; EXP t; STP t; 0; 0; n; bits; S + 2976; ld] FC DL HP DP BC; side6.
           all: try (nf; rewrite ?(szwrap_small 32) by lia; eapply extra_read; [exact HRC | lia | lia]).
           nf_in Hms. rewrite ?Vb, ?Vf, ?Vs in Hms.
           blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW; KStatW]
             ltac:(split; [unfold GS, GB6; regsG HR Hfr; rewrite ?Hx; destruct (ML <=? ld); f_equal; lia | fr_weak Hfr]).
           all: try ceqG.
           split; [exact RDL|]. split; [exact LDL|]. split; [exact A3|]. split; [exact A4|].
           split; [apply wrap64_range|]. split; [apply wrap64_range|]. nf; vfix; frame_cells.
        -- run 60%nat [false; true; false; false] [RVal (EApp1 5 (ESub (EVar 48) (EVar 40))); RVal (EVar 42); RVal (EVar 43)] GSAP
              [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; SL; EXP t; STP t; 0; 0; n; bits; S + 2976; ld] FC DL HP DP BC; side6.
           all: try (nf; rewrite ?(szwrap_small 32) by lia; eapply extra_read; [exact HRC | lia | lia]).
           nf_in Hms. rewrite ?Vb, ?Vf, ?Vs in Hms.
           blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW; KStatW]
             ltac:(split; [unfold GS, GB6; regsG HR Hfr; rewrite ?Hx; destruct (ML <=? ld); f_equal; lia | fr_weak Hfr]).
           all: try ceqG.
           split; [exact RDL|]. split; [exact LDL|]. split; [exact A3|]. split; [exact A4|].
           split; [apply wrap64_range|]. split; [apply wrap64_range|]. nf; vfix; frame_cells.
      * assert (Vx : xbits n = 0) by (unfold GenBitlenModel.xbits; rewrite (proj2 (Z.leb_gt _ _)) by lia; reflexivity).
        destruct (Z.eqb_spec h 572) as [Ce|Ce].
        -- run 60%nat [false; false; false; true] [RVal (EVar 42); RVal (EVar 43)] GSAP
              [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; SL; EXP t; STP t; 0; 0; n; bits; S + 2976; ld] FC DL HP DP BC; side6.
           nf_in Hms. rewrite ?Vb, ?Vf, ?Vs in Hms.
           blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW; KStatW]
             ltac:(split; [unfold GS, GB6; regsG HR Hfr; rewrite ?Hx; destruct (ML <=? ld); f_equal; lia | fr_weak Hfr]).
           all: try ceqG.
           split; [exact RDL|]. split; [exact LDL|]. split; [exact A3|]. split; [exact A4|].
           split; [apply wrap64_range|]. split; [apply wrap64_range|]. nf; vfix; frame_cells.
        -- run 60%nat [false; false; false; false] [RVal (EVar 42); RVal (EVar 43)] GSAP
              [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; SL; EXP t; STP t; 0; 0; n; bits; S + 2976; ld] FC DL HP DP BC; side6.
           nf_in Hms. rewrite ?Vb, ?Vf, ?Vs in Hms.
           blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW; KStatW]
             ltac:(split; [unfold GS, GB6; regsG HR Hfr; rewrite ?Hx; destruct (ML <=? ld); f_equal; lia | fr_weak Hfr]).
           all: try ceqG.
           split; [exact RDL|]. split; [exact LDL|]. split; [exact A3|]. split; [exact A4|].
           split; [apply wrap64_range|]. split; [apply wrap64_range|]. nf; vfix; frame_cells.
Qed.

Goal True. idtac "gB OK". exact I. Qed.


Lemma g_trip : forall regs m1 m DL BC OL SL h ovf,
  GI m1 m DL BC OL SL -> K <= h <= 572 -> 0 <= ovf <= h - K ->
  0 <= arr_get DL (arr_get HP h) < tsize t ->
  GS regs h ovf ->
  exists R m' DL' BC' OL' SL' ovf',
    GB1 t MC (W4 DL BC OL SL) h ovf = (W4 DL' BC' OL' SL', ovf')
    /\ msteps s6_segs (mkst regs (0x1bed0 : word) m s6_rom)
              (mkst R (if h =? 572 then (0x1bf7c : word) else (0x1bed0 : word)) m' s6_rom)
    /\ GI m1 m' DL' BC' OL' SL' /\ GS R (h + 1) ovf' /\ ovf <= ovf' <= ovf + 1
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL BC OL SL h ovf HG Hh Hovf Rd HR0.
  pose proof HG as ((HB & HRC & HAG & MF) & RDL & LDL & RBC & LBC & ROL & RSL & C0).
  pose proof ml_range as Hml.
  destruct (gA_blk regs m1 m DL BC OL SL h ovf HG Hh ltac:(lia) Rd HR0) as (R1 & ma & Hms1 & HG1 & HR1 & Hfr1).
  set (ld := arr_get DL (arr_get DL (arr_get HP h))) in *.
  pose proof (RDL (arr_get DL (arr_get HP h)) Rd) as Rld. fold ld in Rld.
  set (bits := if ML <=? ld then ML else ld + 1) in *.
  assert (Hbits : 1 <= bits <= ML) by (subst bits; destruct (Z.leb_spec ML ld); lia).
  destruct (gB_blk R1 m1 ma (arr_set DL (arr_get HP h) (wrap16 bits)) BC OL SL h ovf (arr_get HP h) bits ld
              HG1 Hh ltac:(lia) eq_refl Hbits ltac:(lia) HR1)
    as (R2 & mb & Hms2 & HG2 & HR2 & Hfr2).
  pose proof (GenBitlenModel.GB1_flat t MC ds FC DL HP 1 (K - 1) DP BC OL SL h ovf) as EF. cbv zeta in EF. fold ld in EF.
  replace (ML <? ld + 1) with (ML <=? ld) in EF by (destruct (Z.leb_spec ML ld), (Z.ltb_spec ML (ld + 1)); try reflexivity; lia).
  fold bits in EF.
  destruct (MC <? arr_get HP h).
  - eexists R2, mb, _, BC, OL, SL, _. split; [exact EF|].
    split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HG2|]. split; [exact HR2|]. split; [destruct (ML <=? ld); lia|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
  - eexists R2, mb, _, _, _, _, _. split; [exact EF|].
    split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HG2|]. split; [exact HR2|]. split; [destruct (ML <=? ld); lia|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Lemma g_loop : forall f h regs m1 m DL BC OL SL ovf,
  573 - h <= Z.of_nat f ->
  GI m1 m DL BC OL SL -> K <= h <= 572 -> 0 <= ovf <= h - K ->
  gb1_ok t MC f (W4 DL BC OL SL) h ovf ->
  GS regs h ovf ->
  exists R m' DL' BC' OL' SL' ovf',
    gen_bitlen_loop1 f (W4 DL BC OL SL) t MC BASE ML h ovf = (W4 DL' BC' OL' SL', ovf')
    /\ msteps s6_segs (mkst regs (0x1bed0 : word) m s6_rom) (mkst R (0x1bf7c : word) m' s6_rom)
    /\ GI m1 m' DL' BC' OL' SL' /\ GS R 573 ovf' /\ ovf <= ovf' <= ovf + (573 - h)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction f as [|f IH]; intros h regs m1 m DL BC OL SL ovf Hf HG Hh Hovf HOK HR0; [lia|].
  rewrite GenBitlenModel.GL1_step. cbn [GenBitlenModel.gb1_ok] in HOK.
  replace (h <? HEAP_SIZE) with true in * by (symmetry; apply Z.ltb_lt; unfold HEAP_SIZE, L_CODES, LITERALS, LENGTH_CODES; lia).
  destruct HOK as [Rd HOK]. rewrite bt_Dad, bt_heap_get in Rd.
  destruct (g_trip regs m1 m DL BC OL SL h ovf HG Hh Hovf Rd HR0)
    as (R1 & m2 & DL1 & BC1 & OL1 & SL1 & ovf1 & E1 & Hms1 & HG1 & HR1 & Ho1 & Hfr1).
  rewrite E1 in HOK |- *.
  destruct (Z.eqb_spec h 572) as [Ch|Ch].
  - rewrite GenBitlenModel.GL1_done by (unfold HEAP_SIZE, L_CODES, LITERALS, LENGTH_CODES; lia).
    exists R1, m2, DL1, BC1, OL1, SL1, ovf1. split; [reflexivity|]. split; [exact Hms1|].
    split; [exact HG1|]. subst h. split; [exact HR1|]. split; [lia | exact Hfr1].
  - destruct (IH (h + 1) R1 m1 m2 DL1 BC1 OL1 SL1 ovf1 ltac:(lia) HG1 ltac:(lia) ltac:(lia) HOK HR1)
      as (R2 & m3 & DL2 & BC2 & OL2 & SL2 & ovf2 & E2 & Hms2 & HG2 & HR2 & Ho2 & Hfr2).
    exists R2, m3, DL2, BC2, OL2, SL2, ovf2. split; [exact E2|].
    split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HG2|]. split; [exact HR2|]. split; [lia|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Goal True. idtac "g_loop OK". exact I. Qed.

End PhaseFG.
End Walk.
End FXG.

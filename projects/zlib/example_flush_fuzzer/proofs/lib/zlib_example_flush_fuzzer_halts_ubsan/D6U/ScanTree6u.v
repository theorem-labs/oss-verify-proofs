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
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2 BitsLib TrSmallModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel ScanModel SendModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u TreesRod6u Callee6u TreesApi6u TrApi6u
  CompressBlk6u_1 TrSmall6u TrStored6u.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Definition sc_upd (X : deflate_state) (mn c pl k1 : Z) : deflate_state :=
  if k1 <? mn then set_Freq X TB c (Freq X TB c + k1)
  else if negb (c =? 0) then
    set_Freq (if negb (c =? pl) then set_Freq X TB c (Freq X TB c + 1) else X) TB REP_3_6
             (Freq (if negb (c =? pl) then set_Freq X TB c (Freq X TB c + 1) else X) TB REP_3_6 + 1)
  else if k1 <=? 10 then set_Freq X TB REPZ_3_10 (Freq X TB REPZ_3_10 + 1)
  else set_Freq X TB REPZ_11_138 (Freq X TB REPZ_11_138 + 1).

Lemma scan_loop_S' : forall f X t mc n prevlen nextlen count mx mn,
  scan_tree_loop (Datatypes.S f) X t mc n prevlen nextlen count mx mn =
    if n <=? mc then
      let curlen := nextlen in
      let nextlen' := Len X t (n + 1) in
      let count' := count + 1 in
      if (count' <? mx) && (curlen =? nextlen') then
        scan_tree_loop f X t mc (n + 1) prevlen nextlen' count' mx mn
      else
        let '(mx', mn') := tree_counts curlen nextlen' in
        scan_tree_loop f (sc_upd X mn curlen prevlen count') t mc (n + 1) curlen nextlen' 0 mx' mn'
    else X.
Proof. intros. reflexivity. Qed.

Lemma set_Freq_TB_Len : forall X c v t i, Len (set_Freq X TB c v) t i = Len X t i.
Proof. intros X c v [| |] i; reflexivity. Qed.
Lemma set_Freq_TB_tree_dl : forall X c v t, tree_dl (set_Freq X TB c v) t = tree_dl X t.
Proof. intros X c v [| |]; reflexivity. Qed.
Lemma set_Freq_TB_blfc : forall X c v, ds_bl_tree_fc (set_Freq X TB c v) = arr_set (ds_bl_tree_fc X) c (wrap16 v).
Proof. intros; reflexivity. Qed.
Lemma blfc_typed_set : forall (b : arr) c v,
  (forall i, 0 <= i < 39 -> 0 <= arr_get b i < 65536) -> arr_len b = 39 ->
  forall i, 0 <= i < 39 -> 0 <= arr_get (arr_set b c (wrap16 v)) i < 65536.
Proof.
  intros b c v Hb Hl i Hi. rewrite arr_get_set. destruct (_ && _); [|apply Hb; exact Hi].
  rewrite wrap16_mod'. pose proof (Z.mod_pos_bound v (2 ^ 16) ltac:(lia)). change (2 ^ 16) with 65536 in *. lia.
Qed.
Lemma sc_upd_Len : forall X mn c pl k1 t i, Len (sc_upd X mn c pl k1) t i = Len X t i.
Proof.
  intros. unfold sc_upd. destruct (k1 <? mn); [apply set_Freq_TB_Len|].
  destruct (negb (c =? 0)); [destruct (negb (c =? pl)); rewrite !set_Freq_TB_Len; reflexivity|].
  destruct (k1 <=? 10); apply set_Freq_TB_Len.
Qed.
Lemma sc_upd_tree_dl : forall X mn c pl k1 t, tree_dl (sc_upd X mn c pl k1) t = tree_dl X t.
Proof.
  intros. unfold sc_upd. destruct (k1 <? mn); [apply set_Freq_TB_tree_dl|].
  destruct (negb (c =? 0)); [destruct (negb (c =? pl)); rewrite !set_Freq_TB_tree_dl; reflexivity|].
  destruct (k1 <=? 10); apply set_Freq_TB_tree_dl.
Qed.
Lemma sc_upd_typed : forall X mn c pl k1,
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X) i < 65536) -> arr_len (ds_bl_tree_fc X) = 39 ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc (sc_upd X mn c pl k1)) i < 65536)
  /\ arr_len (ds_bl_tree_fc (sc_upd X mn c pl k1)) = 39.
Proof.
  intros X mn c pl k1 Hb Hl. unfold sc_upd.
  destruct (k1 <? mn); [rewrite set_Freq_TB_blfc, arr_len_set; split; [apply blfc_typed_set; assumption | exact Hl]|].
  destruct (negb (c =? 0)).
  - destruct (negb (c =? pl)); rewrite !set_Freq_TB_blfc, !arr_len_set; split; try exact Hl.
    + apply blfc_typed_set; [apply blfc_typed_set; assumption | rewrite arr_len_set; exact Hl].
    + apply blfc_typed_set; assumption.
  - destruct (k1 <=? 10); rewrite set_Freq_TB_blfc, arr_len_set; split; try exact Hl; apply blfc_typed_set; assumption.
Qed.

Definition cntsnz (c nl : Z) : Z * Z := if c =? nl then (6, 3) else (7, 4).
Definition cnts (pl c : Z) : Z * Z := if c =? 0 then (138, 3) else if c =? pl then (6, 3) else (7, 4).
Definition BND (pl c k mx mn : Z) : Prop :=
  (pl = -1 \/ 0 <= pl <= 15) /\ 0 <= c <= 15 /\ 0 <= k < mx /\ (mx, mn) = cnts pl c.
Lemma BND_facts : forall pl c k mx mn, BND pl c k mx mn ->
  (mx = 138 \/ mx = 6 \/ mx = 7) /\ (mn = 3 \/ mn = 4) /\ (c = 0 -> mn = 3) /\ (c <> 0 -> c <> pl -> mn = 4) /\ (c <> 0 -> c = pl -> mn = 3).
Proof.
  intros pl c k mx mn (_ & _ & _ & E). unfold cnts in E.
  destruct (Z.eqb_spec c 0); [injection E; intros; subst; lia|].
  destruct (Z.eqb_spec c pl); injection E; intros; subst; lia.
Qed.
Lemma cnts_tree_counts : forall c nl, tree_counts c nl = cnts c nl.
Proof. intros c nl. unfold tree_counts, cnts. rewrite (Z.eqb_sym c nl). reflexivity. Qed.

Lemma lxor_ltb1 : forall a b, 0 <= a -> 0 <= b -> (Z.lxor a b <? 1) = (a =? b).
Proof.
  intros a b Ha Hb. pose proof (Z.lxor_nonneg a b) as Hn.
  destruct (Z.eqb_spec a b) as [->|Hne].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.ltb_ge. assert (Z.lxor a b <> 0) by (intros E; apply Z.lxor_eq in E; lia). lia.
Qed.

Definition SC_CLOB6u : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition SC_FRAME6u : Z := 64.
Definition A6U_SCAN_TREE' : Z := 0x1e074.

Definition scan_tree_run6u : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (X : deflate_state) (ra : word) (regs : bvmap 5 word) (sp : Z) (t : tree_id) (mc : Z),
    BRH F S p PBL -> sub_franges F S dsl_SIZE -> ret_ok ra -> BR6u F mem0 S p PBL mem X ->
    (t = TL \/ t = TD) -> 0 <= mc /\ mc + 1 < tsize t ->
    (forall i, 0 <= i <= mc -> 0 <= Len X t i <= 15) ->
    (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl X t) i < 65536) ->
    (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X) i < 65536) ->
    call_frame F mem S (p_pending_buf p) PBL sp SC_FRAME6u -> UBT S p ->
    getr regs 10 = zw S -> getr regs 11 = zw (S + toff t) -> getr regs 12 = zw mc ->
    getr regs 2 = zw sp -> getr regs 1 = ra ->
    exists R m',
      msteps s6u_segs (mkst regs (zw A6U_SCAN_TREE') mem s6u_rom) (mkst R ra m' s6u_rom)
      /\ BR6u F mem0 S p PBL m' (scan_tree X t mc)
      /\ getr R 2 = getr regs 2
      /\ (forall r : reg, reg_in r SC_CLOB6u = false -> getr R r = getr regs r).

Section Walk.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (X : deflate_state) (ra : word) (sp : Z).
Variables (t : tree_id) (mc : Z).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation SP := (sp - 64).
Local Abbreviation T := (S + toff t).
Local Abbreviation BRm := (BR6u F mem0 S p PBL).

Hypothesis HLb : BRH F S p PBL.
Hypothesis HFS : sub_franges F S dsl_SIZE.
Hypothesis Hret : ret_ok ra.
Hypothesis HBR0 : BRm mem X.
Hypothesis Ht : t = TL \/ t = TD.
Hypothesis Hmc : 0 <= mc /\ mc + 1 < tsize t.
Hypothesis Hl15 : forall i, 0 <= i <= mc -> 0 <= Len X t i <= 15.
Hypothesis Hdl : forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl X t) i < 65536.
Hypothesis Hty : forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X) i < 65536.
Hypothesis Hcf : call_frame F mem S PB PBL sp 64.
Hypothesis HUB : UBT S p.

Lemma Htt : 212 <= toff t <= 2504 /\ toff t + 4 * tsize t <= 2748 /\ tsize t <= 573 /\ toff t mod 2 = 0.
Proof. destruct Ht as [-> | ->]; cbn [toff tsize]; (split; [lia | split; [lia | split; [lia | reflexivity]]]). Qed.

Definition GS : franges := [(S, dsl_SIZE)].

Definition SI (m1 m : word -> option byte) (Y : deflate_state) : Prop := BRm m Y /\ agree_out GS m1 m.

Definition FRM (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  cell s6u_segs m (SP + 56) 8 (bv_unsigned (getr regs 8)) /\ cell s6u_segs m (SP + 48) 8 (bv_unsigned (getr regs 9))
  /\ cell s6u_segs m (SP + 40) 8 (bv_unsigned (getr regs 18)) /\ cell s6u_segs m (SP + 32) 8 (bv_unsigned (getr regs 19))
  /\ cell s6u_segs m (SP + 24) 8 (bv_unsigned (getr regs 20)) /\ cell s6u_segs m (SP + 16) 8 (bv_unsigned (getr regs 21))
  /\ cell s6u_segs m (SP + 8) 8 (bv_unsigned (getr regs 22)).

Lemma FRM_agree : forall regs m1 m, FRM regs m1 -> agree_out GS m1 m -> FRM regs m.
Proof.
  intros regs m1 m HF Hag. pose proof Hcf as (Hsp & _ & _ & HfS & _). unfold dsl_SIZE in HfS.
  assert (FC : forall a v, cell s6u_segs m1 a 8 v -> SP <= a -> a + 8 <= sp -> cell s6u_segs m a 8 v).
  { intros a v Hc Ha1 Ha2. apply (cell_agree_out s6u_segs GS m1 m a 8 v Hag); [| lia | change (Z.of_nat 8) with 8; lia | exact Hc].
    unfold GS. intros x Hx [Hin|[]]; cbn in Hin; unfold dsl_SIZE in Hin; change (Z.of_nat 8) with 8 in Hx; lia. }
  destruct HF as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold FRM. repeat split; (apply FC; [assumption | lia | lia]).
Qed.

Definition scF (Y : deflate_state) (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb (tree_dl Y t) x | _ => pb (ds_bl_tree_fc Y) x end.
Definition FBv : list (nat * Z) := [(0%nat, 65536); (1%nat, 65536)].
Definition VBS : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 17); (36%nat, 65536); (37%nat, 2); (38%nat, 2 ^ 32);
   (39%nat, 2 ^ 64); (40%nat, 2 ^ 63); (41%nat, 600); (42%nat, 2 ^ 63); (43%nat, 19); (44%nat, 2 ^ 64);
   (45%nat, 600); (46%nat, 16); (47%nat, 65536); (48%nat, 200); (49%nat, 65536); (50%nat, 200); (51%nat, 10);
   (52%nat, 2 ^ 64); (53%nat, 2 ^ 64); (54%nat, 2 ^ 64); (55%nat, 2 ^ 64); (56%nat, 2 ^ 64); (57%nat, 2 ^ 64); (58%nat, 2 ^ 64)].
Definition sC : cfg := CFG FBv [] [EVar 1%nat] [0x1e134; 0x1e128; 0x1e174; 0x1e210; 0x1e240; 0x1e24c] [].
Local Ltac PV n c nl k pl mx mn := constr:([S; 0; 0; 0; 0; 0; 0; 0; SP; mc; T; 0; 0; n; c; nl; k; pl; mx; mn]).

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.
Local Ltac nf := cbn [scF].

Local Ltac fb_read :=
  lazymatch goal with
  | |- exists bs, rdn ?sg ?m (zw ?a) ?n = Some bs /\ bytes_le_to_Z bs = pb ?tt ?i =>
      match goal with H : cells sg m ?P 4 2%nat ?len (arr_get tt) |- _ =>
        eapply (pb_read4m sg m P len tt i a H); [lia | lia] end
  end.

Local Ltac side_closer :=
  try solve [ assumption
            | rewrite zw_u; reflexivity
            | nf; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; fb_read
            | change (2 ^ 3) with 8 in *; change (2 ^ 1) with 2 in *; zcond_close
            | nf; symex_read_auto
            | nf; symex_store_auto
            | nf; symex_sok_auto
            | intros; nf; apply pb_range ].

Local Ltac runs fuel dirs rds pins pv Y :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VBS in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs sC fuel dirs rdv pinsv vbv NoRegions pv NoVals (scF Y) F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.
Local Ltac runsv fuel dirs rds pins pv rv Y :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VBS in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs sC fuel dirs rdv pinsv vbv NoRegions pv rv (scF Y) F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.
Local Ltac run_dbg fuel dirs rds pins pv :=
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VBS in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex_dbg s6u_segs sC fuel dirs rdv pinsv vbv NoRegions pv (mkst regs pc m s6u_rom)
  end.

Local Ltac open_br HB :=
  let HS' := fresh "HS'" in let HPB' := fresh "HPB'" in let HD := fresh "HD" in
  pose proof HLb as HL'; destruct HL' as (HS' & HPB' & HD & _); unfold dsl_SIZE in HS', HD;
  let MS := fresh "MS" in let MP := fresh "MP" in let Hsc := fresh "Hsc" in let Har := fresh "Har" in let HTL := fresh "HTL" in
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & HTL & _ & _ & MS & MP & _); unfold mapped, dsl_SIZE in MS, MP;
  let TDl := fresh "TDl" in let BLc := fresh "BLc" in
  pose proof (arrays_dl s6u_segs _ _ _ t Har) as TDl; pose proof (arrays_fc s6u_segs _ _ _ TB Har) as BLc;
  cbn [toff tsize tree_fc] in BLc;
  let Hsp' := fresh "Hsp'" in let HfS := fresh "HfS" in let HfP := fresh "HfP" in
  pose proof Hcf as Hcf'; destruct Hcf' as (Hsp' & _ & _ & HfS & HfP); unfold dsl_SIZE in HfS, HfP;
  pose proof Htt as Htt'; open_ubt HUB.

Local Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); assumption end
        | let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf;
            first [reflexivity | assumption | f_equal; lia | f_equal; f_equal; lia
                  | f_equal; repeat (rewrite (szwrap_small 32) by lia); lia
                  | rewrite zw_u; assumption
                  | lazymatch goal with |- zw ?a = zw ?b =>
                      lazymatch isZcst a with true => lazymatch isZcst b with true =>
                        apply bv_eq; vm_compute; reflexivity end end end ] end
        | idtac ].
Local Ltac regs_of HR Hfr := repeat split; reg1 HR Hfr.
Local Ltac cnt_reg HR :=
  lazymatch goal with |- getr ?R ?r = _ =>
    let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
    rewrite ?lxor_ltb1 by lia; rewrite ?Z.eqb_refl;
    try (replace (_ =? _) with false by (symmetry; apply Z.eqb_neq; lia));
    vm_compute; reflexivity
  end.

Definition SK (R : bvmap 5 word) : Prop :=
  getr R 11 = zw T /\ getr R 12 = zw mc /\ getr R 10 = zw 0 /\ getr R 15 = zw (S + 2047)
  /\ getr R 16 = zw 39 /\ getr R 17 = zw 4 /\ getr R 5 = zw 9
  /\ getr R 6 = zw 18446744073709551547 /\ getr R 7 = zw 18446744073709551543 /\ getr R 28 = zw 18446744073709551551
  /\ getr R 29 = zw (S + 2748) /\ getr R 30 = zw (Z.lxor (S + 2748) (-1)) /\ getr R 31 = zw 38 /\ getr R 2 = zw SP
  /\ getr R 1 = ra.
Definition SKP : list (Z * expr) :=
  [(11, EVar 42); (12, EVar 41); (10, ELit 0); (15, EAdd (EVar 32) (ELit 2047)); (16, ELit 39); (17, ELit 4); (5, ELit 9);
   (6, ELit 18446744073709551547); (7, ELit 18446744073709551543); (28, ELit 18446744073709551551);
   (29, EAdd (EVar 32) (ELit 2748)); (30, EXor (EAdd (EVar 32) (ELit 2748)) (ELit (-1))); (31, ELit 38); (2, EVar 40)].
Local Ltac skd H := destruct H as (K11 & K12 & K10 & K15 & K16 & K17 & K5 & K6 & K7 & K28 & K29 & K30 & K31 & K2 & K1).
Local Ltac skregs HR Hfr := unfold SK; regs_of HR Hfr.

Definition SH (R : bvmap 5 word) (n pl c k mx mn : Z) : Prop :=
  SK R /\ getr R 14 = zw n /\ getr R 13 = zw c /\ getr R 20 = zw k /\ getr R 9 = zw mx /\ getr R 18 = zw mn /\ getr R 19 = zw pl.
Local Ltac shd H := destruct H as (HSK & Pn & Pc & Pk & Pmx & Pmn & Ppl).
Definition SHP (plp : list (Z * expr)) : list (Z * expr) :=
  SKP ++ [(14, EVar 45); (13, EVar 46); (20, EVar 48); (9, EVar 50); (18, EVar 51)] ++ plp.

Definition SU (R : bvmap 5 word) (n pl c nl k mx mn : Z) : Prop :=
  SK R /\ getr R 14 = zw (n + 1) /\ getr R 8 = zw c /\ getr R 13 = zw nl /\ getr R 21 = zw (k + 1)
  /\ getr R 20 = zw k /\ getr R 9 = zw mx /\ getr R 18 = zw mn /\ getr R 19 = zw pl.
Local Ltac sud H := destruct H as (HSK & Pn & Pc & Pnl & Pk1 & Pk & Pmx & Pmn & Ppl).
Definition SUP (plp : list (Z * expr)) : list (Z * expr) :=
  SKP ++ [(14, EAdd (EVar 45) (ELit 1)); (8, EVar 46); (13, EVar 47); (21, EAdd (EVar 48) (ELit 1)); (20, EVar 48);
          (9, EVar 50); (18, EVar 51)] ++ plp.

Definition SG (R : bvmap 5 word) (n pl c nl : Z) : Prop :=
  SK R /\ getr R 14 = zw (n + 1) /\ getr R 8 = zw c /\ getr R 13 = zw nl /\ getr R 21 = zw 0 /\ getr R 19 = zw pl.
Local Ltac sgd H := destruct H as (HSK & Pn & Pc & Pnl & Pk1 & Ppl).
Definition SGP (plp : list (Z * expr)) : list (Z * expr) :=
  SKP ++ [(14, EAdd (EVar 45) (ELit 1)); (8, EVar 46); (13, EVar 47); (21, ELit 0)] ++ plp.

Definition SJ (R : bvmap 5 word) (n pl' nl k' mx' mn' : Z) : Prop :=
  SK R /\ getr R 14 = zw (n + 1) /\ getr R 8 = zw pl' /\ getr R 13 = zw nl /\ getr R 21 = zw k'
  /\ getr R 9 = zw mx' /\ getr R 18 = zw mn'.
Local Ltac sjd H := destruct H as (HSK & Pn & P8 & Pnl & Pk1 & Pmx & Pmn).
Definition SJP (plp : list (Z * expr)) : list (Z * expr) :=
  SKP ++ [(14, EAdd (EVar 45) (ELit 1)); (13, EVar 47); (21, EVar 48); (9, EVar 50); (18, EVar 51)] ++ plp.

Definition STGT (nl : Z) : word := if nl =? 0 then (0x1e240 : word) else (0x1e210 : word).
Definition SNEXT (n : Z) : word := if n + 1 =? mc + 1 then (0x1e24c : word) else (0x1e134 : word).

Definition SCL : list reg := [8; 9; 13; 14; 18; 19; 20; 21; 22]%bv.


Definition scnts0 : Z * Z := if Len X t 0 =? 0 then (138, 3) else (7, 4).

Lemma cell_write_same_at : forall M a b (w : nat) v,
  b = a -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  cell s6u_segs (wbytes M (zw b) (Z_to_le_bytes w v)) a w v.
Proof. intros M a b w v -> Ha Hw. apply cell_write_same; assumption. Qed.

Ltac frame_cells :=
  repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                | apply cell_write_other;
                  [ | lia | cbn; lia | lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia ] ]);
  try assumption.

Lemma mod2_of_mod8 : forall a b, a mod 8 = 0 -> b mod 2 = 0 -> (a + b) mod 2 = 0.
Proof.
  intros a b Ha Hb.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Ea. pose proof (Z.div_mod b 2 ltac:(lia)) as Eb.
  rewrite Ha, Z.add_0_r in Ea. rewrite Hb, Z.add_0_r in Eb.
  rewrite Ea, Eb. replace (8 * (a / 8) + 2 * (b / 2)) with ((4 * (a / 8) + b / 2) * 2) by lia.
  apply Z_mod_mult.
Qed.

Lemma BR_st_dl_at : forall m Y i v a,
  BRm m Y -> 0 <= i < tsize t -> a = S + toff t + 4 * i + 2 ->
  BRm (wbytes m (zw a) (Z_to_le_bytes 2 v)) (set_tree_dl Y t (arr_set (tree_dl Y t) i (wrap16 v))).
Proof. intros m Y i v a HB Hi ->. apply (BR_st_dl _ _ _ _ F mem0 S p PBL HLb HFS); assumption. Qed.
Lemma BR_st_blfc : forall m Y i v a,
  BRm m Y -> 0 <= i < 39 -> a = S + 2748 + 4 * i ->
  BRm (wbytes m (zw a) (Z_to_le_bytes 2 v)) (set_tree_fc Y TB (arr_set (tree_fc Y TB) i (wrap16 v))).
Proof.
  intros m Y i v a HB Hi ->. change (S + 2748) with (S + toff TB).
  apply (BR_st_fc _ _ _ _ F mem0 S p PBL HLb HFS); [exact HB | cbn; lia].
Qed.

Ltac pre_fwd HB M :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) (Z_to_le_bytes ?w ?v) =>
      pre_fwd HB M1;
      lazymatch goal with
      | H1 : BR ?sg ?AL ?AD ?AB ?F ?mem0 ?S ?p ?PBL M1 ?s1, HL : BRH ?F ?S ?p ?PBL |- _ =>
          let H2 := fresh "HBR" in
          first
            [ pose proof (BR_st_other sg AL AD AB F mem0 S p PBL HL M1 s1 a (Z_to_le_bytes w v) H1
                ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; cbn; lia)
                ltac:(rewrite length_Z_to_le_bytes; unfold dsl_SIZE; cbn; lia)
                ltac:(rewrite length_Z_to_le_bytes; cbn; lia)
                ltac:(rewrite length_Z_to_le_bytes;
                      solve [eapply sub_franges_mono; [eassumption | cbn; lia | cbn; lia]])) as H2
            | pose proof (BR_st_dl_at M1 s1 (mc + 1) v a H1 ltac:(lia) ltac:(lia)) as H2 ];
          clear H1
      end
  | _ => let H := fresh "HBR" in pose proof HB as H
  end.

Lemma sc_pre : forall regs,
  getr regs 10 = zw S -> getr regs 11 = zw T -> getr regs 12 = zw mc -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m1,
    msteps s6u_segs (mkst regs (0x1e074 : word) mem s6u_rom) (mkst R (0x1e134 : word) m1 s6u_rom)
    /\ BRm m1 (set_Len X t (mc + 1) 65535)
    /\ FRM regs m1
    /\ SH R 0 (-1) (Len X t 0) 0 (fst scnts0) (snd scnts0)
    /\ (forall r : reg, reg_in r (2 :: 8 :: 9 :: 18 :: 19 :: 20 :: 21 :: SC_CLOB6u)%bv = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P11 P12 P2 P1. open_br HBR0.
  pose proof Hcf as (_ & HFf & Hmf & _ & _). unfold mapped in Hmf.
  pose proof (Hdl 0 ltac:(lia)) as R0. pose proof (Hl15 0 ltac:(lia)) as V0.
  assert (E0 : pb (tree_dl X t) 0 = Len X t 0) by (unfold Len; apply pb_small; exact R0).
  assert (P2' : getr regs 2 = zw (SP + 64)) by (rewrite P2; f_equal; lia).
  assert (HT2 : (S + toff t) mod 2 = 0) by (apply mod2_of_mod8; [exact US8 | tauto]).
  assert (HT2' : (S + toff t) mod 2 ^ 1 = 0) by (change (2 ^ 1) with 2; exact HT2).
  pose proof (u64_range (getr regs 8)) as U8. pose proof (u64_range (getr regs 9)) as U9. pose proof (u64_range (getr regs 18)) as U18.
  pose proof (u64_range (getr regs 19)) as U19. pose proof (u64_range (getr regs 20)) as U20. pose proof (u64_range (getr regs 21)) as U21.
  pose proof (u64_range (getr regs 22)) as U22.
  assert (FIN : forall R M (b : bool),
    msteps s6u_segs (mkst regs (0x1e074 : word) mem s6u_rom) (mkst R (0x1e134 : word) M s6u_rom) ->
    BRm M (set_tree_dl X t (arr_set (tree_dl X t) (mc + 1) (wrap16 (-1)))) ->
    FRM regs M -> SH R 0 (-1) (Len X t 0) 0 (fst scnts0) (snd scnts0) ->
    (forall r : reg, reg_in r (2 :: 8 :: 9 :: 18 :: 19 :: 20 :: 21 :: SC_CLOB6u)%bv = false -> getr R r = getr regs r) ->
    exists R' m1,
      msteps s6u_segs (mkst regs (0x1e074 : word) mem s6u_rom) (mkst R' (0x1e134 : word) m1 s6u_rom)
      /\ BRm m1 (set_Len X t (mc + 1) 65535) /\ FRM regs m1 /\ SH R' 0 (-1) (Len X t 0) 0 (fst scnts0) (snd scnts0)
      /\ (forall r : reg, reg_in r (2 :: 8 :: 9 :: 18 :: 19 :: 20 :: 21 :: SC_CLOB6u)%bv = false -> getr R' r = getr regs r)).
  { intros R M b Hms HB HF HSH Hfr. exists R, M. split; [exact Hms|]. split; [| split; [exact HF | split; [exact HSH | exact Hfr]]].
    unfold set_Len, set_Dad. change (wrap16 65535) with (wrap16 (-1)). exact HB. }
  unfold scnts0 in *.
  destruct (Z.eqb_spec (Len X t 0) 0) as [CZ|CZ]; cbn [fst snd] in *.
  - runs 60%nat [false; true; false; false; false; false] [RVal (EApp1 0 (ELit 0))]
        [(10, EVar 32); (11, EVar 42); (12, EVar 41); (2, EAdd (EVar 40) (ELit 64))] ltac:(PV 0 0 0 0 0 0 0) X.
    lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) =>
      pre_fwd HBR0 M; apply (FIN R M true Hms); [assumption | unfold FRM; repeat match goal with |- _ /\ _ => split end; frame_cells | | fr_weak Hfr] end.
    unfold SH, SK. regs_of HR Hfr.
    + symex_reg HR (10%bv : reg) as A; rewrite A; f_equal. change (2 ^ 3) with 8. exact US8.
    + symex_reg HR (18%bv : reg) as A; rewrite A; f_equal; nf. rewrite E0, CZ. reflexivity.
  - runs 60%nat [false; false; false; false; false; false] [RVal (EApp1 0 (ELit 0))]
        [(10, EVar 32); (11, EVar 42); (12, EVar 41); (2, EAdd (EVar 40) (ELit 64))] ltac:(PV 0 0 0 0 0 0 0) X.
    lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) =>
      pre_fwd HBR0 M; apply (FIN R M true Hms); [assumption | unfold FRM; repeat match goal with |- _ /\ _ => split end; frame_cells | | fr_weak Hfr] end.
    unfold SH, SK. regs_of HR Hfr.
    + symex_reg HR (10%bv : reg) as A; rewrite A; f_equal. change (2 ^ 3) with 8. exact US8.
    + symex_reg HR (18%bv : reg) as A; rewrite A; f_equal; nf. rewrite E0.
      replace (0 <? Len X t 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma sc_head_cont : forall regs m Y n pl c k mx mn,
  BRm m Y -> SH regs n pl c k mx mn -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= k < mx -> mx <= 138 -> 0 <= mn < 10 ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl Y t) i < 65536) ->
  k + 1 < mx -> c = Len Y t (n + 1) ->
  exists R,
    msteps s6u_segs (mkst regs (0x1e134 : word) m s6u_rom) (mkst R (0x1e128 : word) m s6u_rom)
    /\ SJ R n pl (Len Y t (n + 1)) (k + 1) mx mn /\ getr R 19 = zw pl
    /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros regs m Y n pl c k mx mn HB HSH Hn Hc Hk Hmx Hmn HdlY C1 Ec. open_br HB. shd HSH. skd HSK.
  pose proof (HdlY (n + 1) ltac:(lia)) as Vnl.
  assert (Enl : pb (tree_dl Y t) (n + 1) = Len Y t (n + 1)) by (unfold Len; apply pb_small; exact Vnl).
  runs 40%nat [false; false; false; false; true] [RVal (EApp1 0 (EAdd (EVar 45) (ELit 1)))] (SHP [])
       ltac:(PV n c 0 k 0 mx mn) Y.
  exists R. split; [exact Hms|]. split; [| split; [reg1 HR Hfr | fr_weak Hfr]].
  unfold SJ. split; [skregs HR Hfr | regs_of HR Hfr].
Qed.

Lemma sc_head_emit : forall regs m Y n pl c k mx mn,
  BRm m Y -> SH regs n pl c k mx mn -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= k < mx -> mx <= 138 -> 0 <= mn < 10 ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl Y t) i < 65536) ->
  (mx <= k + 1 \/ c <> Len Y t (n + 1)) ->
  exists R,
    msteps s6u_segs (mkst regs (0x1e134 : word) m s6u_rom) (mkst R (0x1e174 : word) m s6u_rom)
    /\ SU R n pl c (Len Y t (n + 1)) k mx mn
    /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros regs m Y n pl c k mx mn HB HSH Hn Hc Hk Hmx Hmn HdlY Hcase. open_br HB. shd HSH. skd HSK.
  pose proof (HdlY (n + 1) ltac:(lia)) as Vnl.
  assert (Enl : pb (tree_dl Y t) (n + 1) = Len Y t (n + 1)) by (unfold Len; apply pb_small; exact Vnl).
  destruct (Z_le_gt_dec mx (k + 1)) as [C1|C1].
  - runs 40%nat [false; false; false; true] [RVal (EApp1 0 (EAdd (EVar 45) (ELit 1)))] (SHP [])
         ltac:(PV n c 0 k 0 mx mn) Y.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SU. split; [skregs HR Hfr | regs_of HR Hfr].
  - runs 40%nat [false; false; false; false; false] [RVal (EApp1 0 (EAdd (EVar 45) (ELit 1)))] (SHP [])
         ltac:(PV n c 0 k 0 mx mn) Y.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SU. split; [skregs HR Hfr | regs_of HR Hfr].
Qed.

Local Ltac ag_tower HAG :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold GS; apply sub_franges_here; unfold dsl_SIZE; cbn; lia ]);
  exact HAG.

Local Ltac upd_fin Hms HR Hfr HB HAG i1 i2 tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      lazymatch M with
      | wbytes (wbytes ?M0 (zw ?a1) (Z_to_le_bytes 2 ?v1)) (zw ?a2) (Z_to_le_bytes 2 ?v2) =>
          let H1 := fresh "HBR" in let H2 := fresh "HBR" in
          pose proof (BR_st_blfc M0 _ i1 v1 a1 HB ltac:(lia) ltac:(lia)) as H1;
          pose proof (BR_st_blfc _ _ i2 v2 a2 H1 ltac:(lia) ltac:(lia)) as H2; clear H1;
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eapply BR_eqst; [exact H2|]; clear H2 | ag_tower HAG] | tregs ]
      | wbytes ?M0 (zw ?a1) (Z_to_le_bytes 2 ?v1) =>
          let H1 := fresh "HBR" in
          pose proof (BR_st_blfc M0 _ i1 v1 a1 HB ltac:(lia) ltac:(lia)) as H1;
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eapply BR_eqst; [exact H1|]; clear H1 | ag_tower HAG] | tregs ]
      end
  end.

Lemma wrap16_szwrap16_add : forall x y, wrap16 (szwrap 16 x + y) = wrap16 (x + y).
Proof.
  intros x y. rewrite !wrap16_mod'. rewrite <- Zplus_mod_idemp_l, (szwrap_eqm 16 x) by lia. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma wrap16_pb_add : forall (b : arr) i y, wrap16 (pb b i + y) = wrap16 (arr_get b i + y).
Proof. intros b i y. unfold pb. rewrite !wrap16_mod'. change 65536 with (2 ^ 16). rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma wrap16_szpb_add : forall (b : arr) i y, wrap16 (szwrap 16 (pb b i) + y) = wrap16 (arr_get b i + y).
Proof. intros b i y. rewrite wrap16_szwrap16_add. apply wrap16_pb_add. Qed.

Local Ltac freq_eq :=
  unfold set_Freq, Freq; cbn [tree_fc set_tree_fc scF]; dsred;
  repeat first [ reflexivity | lia
               | rewrite arr_get_set_other by lia
               | lazymatch goal with |- wrap16 ?a = wrap16 (arr_get ?b ?i + ?y) =>
                   replace a with (szwrap 16 (pb b i) + y) by lia; apply wrap16_szpb_add end
               | f_equal ].

Lemma sc_upd_run : forall regs m1 m Y n pl c nl k mx mn,
  SI m1 m Y -> SU regs n pl c nl k mx mn -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= nl < 65536 ->
  0 <= k < mx -> mx <= 138 -> 0 <= mn < 10 -> (pl = -1 \/ 0 <= pl <= 15) ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc Y) i < 65536) ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1e174 : word) m s6u_rom) (mkst R (STGT nl) m' s6u_rom)
    /\ SI m1 m' (sc_upd Y mn c pl (k + 1))
    /\ (SG R n pl c nl /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m Y n pl c nl k mx mn [HB HAG] HSU Hn Hc Hnl Hk Hmx Hmn Hpl HtyY.
  open_br HB. sud HSU. skd HSK.
  unfold tree_lens in HTL. cbn [tree_fc tree_dl] in HTL.
  assert (Evc : forall i, 0 <= i < 39 -> pb (ds_bl_tree_fc Y) i = arr_get (ds_bl_tree_fc Y) i) by (intros i Hi; apply pb_small; apply HtyY; exact Hi).
  unfold STGT, sc_upd. change REP_3_6 with 16. change REPZ_3_10 with 17. change REPZ_11_138 with 18.
  destruct (Z.ltb_spec (k + 1) mn) as [Cm|Cm].
  -
    destruct (Z.eqb_spec nl 0) as [Enl|Enl].
    + subst nl. runs 40%nat [false; false; false; false; false] [RVal (EApp1 1 (EVar 46))] (SUP [])
          ltac:(PV n c 0 k 0 mx mn) Y.
      upd_fin Hms HR Hfr HB HAG c c ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
      freq_eq.
    + runs 40%nat [false; false; false; false; true] [RVal (EApp1 1 (EVar 46))] (SUP [])
          ltac:(PV n c nl k 0 mx mn) Y.
      upd_fin Hms HR Hfr HB HAG c c ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
      freq_eq.
  - replace (k + 1 <=? 10) with (k <=? 9) by (destruct (Z.leb_spec (k + 1) 10), (Z.leb_spec k 9); try reflexivity; lia).
    destruct (Z.eqb_spec c 0) as [Cz|Cz]; cbn [negb].
    +
      subst c.
      destruct (Z.leb_spec k 9) as [Kn9|Kn9]; destruct (Z.eqb_spec nl 0) as [Enl|Enl].
      * subst nl. runs 40%nat [true; true; false; false; false; false] [RVal (EApp1 1 (ELit 17))] (SUP [])
            ltac:(PV n 0 0 k 0 mx mn) Y.
        upd_fin Hms HR Hfr HB HAG 17 17 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
      * runs 40%nat [true; true; false; false; false; true] [RVal (EApp1 1 (ELit 17))] (SUP [])
            ltac:(PV n 0 nl k 0 mx mn) Y.
        upd_fin Hms HR Hfr HB HAG 17 17 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
      * subst nl. runs 40%nat [true; true; true; false; false; false] [RVal (EApp1 1 (ELit 18))] (SUP [])
            ltac:(PV n 0 0 k 0 mx mn) Y.
        upd_fin Hms HR Hfr HB HAG 18 18 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
      * runs 40%nat [true; true; true; false; false; true] [RVal (EApp1 1 (ELit 18))] (SUP [])
            ltac:(PV n 0 nl k 0 mx mn) Y.
        upd_fin Hms HR Hfr HB HAG 18 18 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
    +
      destruct (Z.eqb_spec c pl) as [Ecp|Ecp]; cbn [negb]; destruct (Z.eqb_spec nl 0) as [Enl|Enl].
      * subst pl nl.
        runs 40%nat [true; false; false; true; false; true] [RVal (EApp1 1 (ELit 16))] (SUP [(19, EVar 46)])
            ltac:(PV n c 0 k 0 mx mn) Y.
        upd_fin Hms HR Hfr HB HAG 16 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
      * subst pl.
        runs 40%nat [true; false; false; true; false; false] [RVal (EApp1 1 (ELit 16))] (SUP [(19, EVar 46)])
            ltac:(PV n c nl k 0 mx mn) Y.
        upd_fin Hms HR Hfr HB HAG 16 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
      * subst nl. destruct Hpl as [Hpl|Hpl].
        -- subst pl. runs 40%nat [true; false; true; false; false; false; false; true] [RVal (EApp1 1 (EVar 46)); RVal (EApp1 1 (ELit 16))]
              (SUP [(19, ELit 18446744073709551615)]) ltac:(PV n c 0 k 0 mx mn) Y.
           upd_fin Hms HR Hfr HB HAG c 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
           freq_eq.
        -- runs 40%nat [true; false; true; false; false; false; false; true] [RVal (EApp1 1 (EVar 46)); RVal (EApp1 1 (ELit 16))]
              (SUP [(19, EVar 49)]) ltac:(PV n c 0 k pl mx mn) Y.
           upd_fin Hms HR Hfr HB HAG c 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
           freq_eq.
      * destruct Hpl as [Hpl|Hpl].
        -- subst pl. runs 40%nat [true; false; true; false; false; false; false; false] [RVal (EApp1 1 (EVar 46)); RVal (EApp1 1 (ELit 16))]
              (SUP [(19, ELit 18446744073709551615)]) ltac:(PV n c nl k 0 mx mn) Y.
           upd_fin Hms HR Hfr HB HAG c 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
           freq_eq.
        -- runs 40%nat [true; false; true; false; false; false; false; false] [RVal (EApp1 1 (EVar 46)); RVal (EApp1 1 (ELit 16))]
              (SUP [(19, EVar 49)]) ltac:(PV n c nl k pl mx mn) Y.
           upd_fin Hms HR Hfr HB HAG c 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
           freq_eq.
Qed.

Lemma sc_cnz : forall regs m Y n pl c nl,
  BRm m Y -> SG regs n pl c nl -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 < nl < 65536 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1e210 : word) m s6u_rom) (mkst R (0x1e128 : word) m s6u_rom)
    /\ SJ R n c nl 0 (fst (cntsnz c nl)) (snd (cntsnz c nl)) /\ getr R 19 = zw pl
    /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros regs m Y n pl c nl HB HG Hn Hc Hnl. open_br HB. sgd HG. skd HSK. unfold cntsnz.
  destruct (Z.eqb_spec c nl) as [Ecn|Ecn]; cbn [fst snd].
  - subst c. runs 20%nat NoDirs NoReads (SGP []) ltac:(PV n nl nl 0 0 0 0) Y.
    exists R. split; [exact Hms|]. split; [| split; [reg1 HR Hfr | fr_weak Hfr]]. unfold SJ. split; [skregs HR Hfr|]. regs_of HR Hfr. all: cnt_reg HR.
  - runs 20%nat NoDirs NoReads (SGP []) ltac:(PV n c nl 0 0 0 0) Y.
    exists R. split; [exact Hms|]. split; [| split; [reg1 HR Hfr | fr_weak Hfr]]. unfold SJ. split; [skregs HR Hfr|]. regs_of HR Hfr. all: cnt_reg HR.
Qed.

Lemma sc_cz : forall regs m Y n pl c,
  BRm m Y -> SG regs n pl c 0 -> 0 <= n <= mc -> 0 <= c <= 15 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1e240 : word) m s6u_rom) (mkst R (0x1e128 : word) m s6u_rom)
    /\ SJ R n c 0 0 138 3 /\ getr R 19 = zw pl
    /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros regs m Y n pl c HB HG Hn Hc. open_br HB. sgd HG. skd HSK.
  runs 20%nat NoDirs NoReads (SGP []) ltac:(PV n c 0 0 0 0 0) Y.
  exists R. split; [exact Hms|]. split; [| split; [reg1 HR Hfr | fr_weak Hfr]]. unfold SJ. split; [skregs HR Hfr|]. regs_of HR Hfr.
Qed.

Lemma sc_latch : forall regs m Y n pl pl' nl k' mx' mn',
  BRm m Y -> SJ regs n pl' nl k' mx' mn' -> getr regs 19 = zw pl -> 0 <= n <= mc ->
  0 <= nl < 65536 -> 0 <= k' < 200 -> 0 <= mx' < 200 -> 0 <= mn' < 10 -> (pl' = -1 \/ 0 <= pl' <= 15) ->
  exists R,
    msteps s6u_segs (mkst regs (0x1e128 : word) m s6u_rom) (mkst R (SNEXT n) m s6u_rom)
    /\ SH R (n + 1) pl' nl k' mx' mn'
    /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros regs m Y n pl pl' nl k' mx' mn' HB HJ P19 Hn Hnl Hk Hmx Hmn Hpl. open_br HB. sjd HJ. skd HSK. unfold SNEXT.
  destruct (Z.eqb_spec (n + 1) (mc + 1)) as [En|En].
  - runs 20%nat [true] NoReads (SJP []) ltac:(PV n 0 nl k' 0 mx' mn') Y.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr.
  - runs 20%nat [false] NoReads (SJP []) ltac:(PV n 0 nl k' 0 mx' mn') Y.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr.
Qed.

Local Ltac frc2 a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr); exact (b r Hr).

Lemma sc_loop : forall m1 f n, 0 <= n -> mc + 1 - n <= Z.of_nat f ->
  forall regs m Y pl c k mx mn,
    SI m1 m Y -> SH regs n pl c k mx mn -> n <= mc -> BND pl c k mx mn -> c = Len Y t n ->
    (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl Y t) i < 65536) ->
    (forall i, 0 <= i <= mc -> 0 <= Len Y t i <= 15) ->
    (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc Y) i < 65536) ->
    exists R m',
      msteps s6u_segs (mkst regs (0x1e134 : word) m s6u_rom) (mkst R (0x1e24c : word) m' s6u_rom)
      /\ SI m1 m' (scan_tree_loop (Z.to_nat (mc + 1 - n)) Y t mc n pl c k mx mn)
      /\ SK R
      /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros m1. induction f as [|f IH]; intros n Hn0 Hf regs m Y pl c k mx mn HSI HSH Hn HB Ec HdlY Hl15Y HtyY; [exfalso; lia|].
  pose proof (BND_facts _ _ _ _ _ HB) as (Bmx & Bmn & Bc0 & Bc1 & Bc2). pose proof HB as (Bpl & Bc & Bk & Bcn).
  pose proof (HdlY (n + 1) ltac:(lia)) as R1.
  replace (Z.to_nat (mc + 1 - n)) with (Datatypes.S (Z.to_nat (mc + 1 - (n + 1)))) by lia.
  rewrite scan_loop_S'. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  set (nl := Len Y t (n + 1)) in *.
  assert (Rnl : 0 <= nl < 65536) by (unfold nl, Len; exact R1).
  pose proof HSI as [HBm HAGm].
  assert (IHn : forall R' m' Y' pl' c' k' mx' mn',
            SI m1 m' Y' -> SH R' (n + 1) pl' c' k' mx' mn' -> n + 1 <= mc -> BND pl' c' k' mx' mn' -> c' = Len Y' t (n + 1) ->
            (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl Y' t) i < 65536) ->
            (forall i, 0 <= i <= mc -> 0 <= Len Y' t i <= 15) ->
            (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc Y') i < 65536) ->
            exists R m'', msteps s6u_segs (mkst R' (0x1e134 : word) m' s6u_rom) (mkst R (0x1e24c : word) m'' s6u_rom)
              /\ SI m1 m'' (scan_tree_loop (Z.to_nat (mc + 1 - (n + 1))) Y' t mc (n + 1) pl' c' k' mx' mn')
              /\ SK R /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr R' r)).
  { intros. apply (IH (n + 1)); try assumption; lia. }
  assert (LATCH : forall R' m' Y' pl' k' mx' mn',
            SI m1 m' Y' -> SJ R' n pl' nl k' mx' mn' -> getr R' 19 = zw pl -> (n + 1 <= mc -> BND pl' nl k' mx' mn') ->
            0 <= k' < 200 -> 0 <= mx' < 200 -> 0 <= mn' < 10 -> (pl' = -1 \/ 0 <= pl' <= 15) -> nl = Len Y' t (n + 1) ->
            (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl Y' t) i < 65536) ->
            (forall i, 0 <= i <= mc -> 0 <= Len Y' t i <= 15) ->
            (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc Y') i < 65536) ->
            exists R m'', msteps s6u_segs (mkst R' (0x1e128 : word) m' s6u_rom) (mkst R (0x1e24c : word) m'' s6u_rom)
              /\ SI m1 m'' (scan_tree_loop (Z.to_nat (mc + 1 - (n + 1))) Y' t mc (n + 1) pl' nl k' mx' mn')
              /\ SK R /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr R' r)).
  { intros R' m' Y' pl' k' mx' mn' HSI' HSJ' Q19 HB' Hk' Hmx' Hmn' Hpl' Enl' Hdl' Hl15' Hty'. pose proof HSI' as [HB2 _].
    destruct (sc_latch R' m' Y' n pl pl' nl k' mx' mn' HB2 HSJ' Q19 ltac:(lia) Rnl Hk' Hmx' Hmn' Hpl') as (Rl & Hmsl & HSHl & Hfrl).
    unfold SNEXT in Hmsl. destruct (Z.eqb_spec (n + 1) (mc + 1)) as [En|En].
    - rewrite scan_loop_out by lia. exists Rl, m'. split; [exact Hmsl|]. split; [exact HSI'|].
      split; [exact (proj1 HSHl) | exact Hfrl].
    - destruct (IHn Rl m' Y' pl' nl k' mx' mn' HSI' HSHl ltac:(lia) (HB' ltac:(lia)) Enl' Hdl' Hl15' Hty') as (Rb & mb & Hmsb & HSIb & HSKb & Hfrb).
      exists Rb, mb. split; [eapply msteps_trans; [exact Hmsl | exact Hmsb]|]. split; [exact HSIb|]. split; [exact HSKb | frc2 Hfrb Hfrl]. }
  pose proof HSH as (_ & _ & _ & _ & _ & _ & P19).
  destruct (Sumbool.sumbool_of_bool ((k + 1 <? mx) && (c =? nl))) as [CC|CC]; rewrite CC.
  -
    apply andb_prop in CC. destruct CC as [C1 C2]. apply Z.ltb_lt in C1. apply Z.eqb_eq in C2.
    destruct (sc_head_cont regs m Y n pl c k mx mn HBm HSH ltac:(lia) Bc Bk ltac:(lia) ltac:(lia) HdlY C1 C2)
      as (Ra & Hmsa & HSJa & Q19a & Hfra).
    destruct (LATCH Ra m Y pl (k + 1) mx mn HSI HSJa Q19a
                ltac:(intros Hle; unfold BND; rewrite <- C2; repeat split; try lia; exact Bcn) ltac:(lia) ltac:(lia) ltac:(lia) Bpl eq_refl HdlY Hl15Y HtyY)
      as (Rb & mb & Hmsb & HSIb & HSKb & Hfrb).
    exists Rb, mb. split; [eapply msteps_trans; [exact Hmsa | exact Hmsb]|]. split; [exact HSIb|]. split; [exact HSKb | frc2 Hfrb Hfra].
  -
    assert (Hcase : mx <= k + 1 \/ c <> nl).
    { apply Bool.andb_false_iff in CC. destruct CC as [C1|C1]; [apply Z.ltb_ge in C1; lia | apply Z.eqb_neq in C1; lia]. }
    destruct (sc_head_emit regs m Y n pl c k mx mn HBm HSH ltac:(lia) Bc Bk ltac:(lia) ltac:(lia) HdlY Hcase)
      as (Rd & Hmsd & HSU & Hfrd).
    destruct (sc_upd_run Rd m1 m Y n pl c nl k mx mn HSI HSU ltac:(lia) Bc Rnl Bk ltac:(lia) ltac:(lia) Bpl HtyY)
      as (Ru & mu & Hmsu & HSIu & HSGu & Hfru).
    set (Y' := sc_upd Y mn c pl (k + 1)) in *.
    assert (HTL : arr_len (ds_bl_tree_fc Y) = 39).
    { destruct HBm as (_ & _ & HL & _). unfold tree_lens in HL. tauto. }
    pose proof (sc_upd_typed Y mn c pl (k + 1) HtyY HTL) as [Hty' HTL']. fold Y' in Hty', HTL'.
    assert (Hdl' : forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl Y' t) i < 65536) by (intros i Hi; subst Y'; rewrite sc_upd_tree_dl; apply HdlY; exact Hi).
    assert (Hl15x : forall i, 0 <= i <= mc -> 0 <= Len Y' t i <= 15) by (intros i Hi; subst Y'; rewrite sc_upd_Len; apply Hl15Y; exact Hi).
    assert (Enl' : nl = Len Y' t (n + 1)) by (subst Y'; rewrite sc_upd_Len; reflexivity).
    pose proof HSIu as [HBu _].
    rewrite cnts_tree_counts. unfold cnts in *; unfold STGT in *.
    destruct (Z.eqb_spec nl 0) as [E1|E1].
    +
      rewrite E1 in HSGu, LATCH, Enl' |- *.
      destruct (sc_cz Ru mu Y' n pl c HBu HSGu ltac:(lia) Bc) as (Rt & Hmst & HSJt & Q19t & Hfrt).
      destruct (LATCH Rt mu Y' c 0 138 3 HSIu HSJt Q19t ltac:(intros Hle; unfold BND, cnts; cbn; repeat split; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Enl' Hdl' Hl15x Hty') as (Rb & mb & Hmsb & HSIb & HSKb & Hfrb).
      exists Rb, mb. split.
      { eapply msteps_trans; [exact Hmsd|]. eapply msteps_trans; [exact Hmsu|]. eapply msteps_trans; [exact Hmst | exact Hmsb]. }
      split; [exact HSIb|]. split; [exact HSKb|]. intros r Hr. rewrite (Hfrb r Hr), (Hfrt r Hr), (Hfru r Hr). exact (Hfrd r Hr).
    + destruct (sc_cnz Ru mu Y' n pl c nl HBu HSGu ltac:(lia) Bc ltac:(lia)) as (Rt & Hmst & HSJt & Q19t & Hfrt).
      unfold cntsnz in HSJt. rewrite (Z.eqb_sym c nl) in HSJt.
      destruct (Z.eqb_spec nl c) as [E2|E2]; cbn [fst snd] in HSJt.
      * destruct (LATCH Rt mu Y' c 0 6 3 HSIu HSJt Q19t
                    ltac:(intros Hle; pose proof (Hl15Y (n + 1) ltac:(lia)) as L15; unfold BND, cnts; replace (nl =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
                          rewrite E2, Z.eqb_refl; repeat split; lia)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Enl' Hdl' Hl15x Hty') as (Rb & mb & Hmsb & HSIb & HSKb & Hfrb).
        exists Rb, mb. split.
        { eapply msteps_trans; [exact Hmsd|]. eapply msteps_trans; [exact Hmsu|]. eapply msteps_trans; [exact Hmst | exact Hmsb]. }
        split; [exact HSIb|]. split; [exact HSKb|]. intros r Hr. rewrite (Hfrb r Hr), (Hfrt r Hr), (Hfru r Hr). exact (Hfrd r Hr).
      * destruct (LATCH Rt mu Y' c 0 7 4 HSIu HSJt Q19t
                    ltac:(intros Hle; pose proof (Hl15Y (n + 1) ltac:(lia)) as L15; unfold BND, cnts; replace (nl =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
                          replace (nl =? c) with false by (symmetry; apply Z.eqb_neq; lia); repeat split; lia)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Enl' Hdl' Hl15x Hty') as (Rb & mb & Hmsb & HSIb & HSKb & Hfrb).
        exists Rb, mb. split.
        { eapply msteps_trans; [exact Hmsd|]. eapply msteps_trans; [exact Hmsu|]. eapply msteps_trans; [exact Hmst | exact Hmsb]. }
        split; [exact HSIb|]. split; [exact HSKb|]. intros r Hr. rewrite (Hfrb r Hr), (Hfrt r Hr), (Hfru r Hr). exact (Hfrd r Hr).
Qed.

Lemma sc_post : forall regs (regs0 : bvmap 5 word) m Y,
  BRm m Y -> SK regs -> FRM regs0 m ->
  exists R,
    msteps s6u_segs (mkst regs (0x1e24c : word) m s6u_rom) (mkst R ra m s6u_rom)
    /\ getr R 2 = zw sp
    /\ getr R 8 = getr regs0 8 /\ getr R 9 = getr regs0 9 /\ getr R 18 = getr regs0 18 /\ getr R 19 = getr regs0 19
    /\ getr R 20 = getr regs0 20 /\ getr R 21 = getr regs0 21 /\ getr R 22 = getr regs0 22
    /\ (forall r : reg, reg_in r (2 :: SCL)%bv = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m Y HB HSK (C56 & C48 & C40 & C32 & C24 & C16 & C8). open_br HB. skd HSK.
  pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9. pose proof (u64_range (getr regs0 18)) as U18.
  pose proof (u64_range (getr regs0 19)) as U19. pose proof (u64_range (getr regs0 20)) as U20. pose proof (u64_range (getr regs0 21)) as U21.
  pose proof (u64_range (getr regs0 22)) as U22.
  runsv 20%nat NoDirs [RVal (EVar 52); RVal (EVar 53); RVal (EVar 54); RVal (EVar 55); RVal (EVar 56); RVal (EVar 57); RVal (EVar 58)]
        [(2, EVar 40)]
        constr:([S; 0; 0; 0; 0; 0; 0; 0; SP; mc; T; 0; 0; 0; 0; 0; 0; 0; 0; 0;
                 bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18); bv_unsigned (getr regs0 19);
                 bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 22)]) NoVals Y.
  rewrite K1 in Hms.
  exists R. split; [exact Hms|]. regs_of HR Hfr.
Qed.

Theorem scan_tree_run : forall regs,
  getr regs 10 = zw S -> getr regs 11 = zw T -> getr regs 12 = zw mc -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1e074 : word) mem s6u_rom) (mkst R ra m' s6u_rom)
    /\ BRm m' (scan_tree X t mc)
    /\ getr R 2 = getr regs 2
    /\ (forall r : reg, reg_in r SC_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P11 P12 P2 P1.
  destruct (sc_pre regs P10 P11 P12 P2 P1) as (R1 & m1 & Hms1 & HB1 & HF1 & HSH1 & Hfr1).
  assert (HTL : arr_len (tree_dl X t) = tsize t).
  { destruct HBR0 as (_ & _ & HL & _). apply (tree_lens_dl X t) in HL. exact HL. }
  set (X1 := set_Len X t (mc + 1) 65535) in *.
  assert (EL : forall i, i <> mc + 1 -> Len X1 t i = Len X t i).
  { intros i Hi. subst X1. rewrite Len_set_Len by (rewrite HTL; lia). replace (mc + 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  assert (Hdl1 : forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl X1 t) i < 65536).
  { intros i Hi. subst X1. unfold set_Len, set_Dad. rewrite tree_dl_set_tree_dl. rewrite arr_get_set.
    destruct (_ && _); [rewrite wrap16_mod'; change (2 ^ 16) with 65536; apply Z.mod_pos_bound; lia | apply Hdl; exact Hi]. }
  assert (Hl151 : forall i, 0 <= i <= mc -> 0 <= Len X1 t i <= 15) by (intros i Hi; rewrite EL by lia; apply Hl15; exact Hi).
  assert (Hty1 : forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X1) i < 65536).
  { intros i Hi. subst X1. unfold set_Len, set_Dad. destruct Ht as [-> | ->]; apply Hty; exact Hi. }
  assert (HB0 : BND (-1) (Len X t 0) 0 (fst scnts0) (snd scnts0)).
  { pose proof (Hl15 0 ltac:(lia)) as L0. unfold BND, cnts, scnts0.
    destruct (Z.eqb_spec (Len X t 0) 0); cbn [fst snd]; [repeat split; lia|].
    replace (Len X t 0 =? -1) with false by (symmetry; apply Z.eqb_neq; lia). repeat split; lia. }
  assert (HSI1 : SI m1 m1 X1) by (split; [exact HB1 | apply agree_out_refl]).
  destruct (sc_loop m1 (Datatypes.S (Z.to_nat (mc + 1))) 0 ltac:(lia) ltac:(lia) R1 m1 X1 (-1) (Len X t 0) 0 (fst scnts0) (snd scnts0)
              HSI1 HSH1 ltac:(lia) HB0 ltac:(symmetry; apply EL; lia) Hdl1 Hl151 Hty1) as (R2 & m2 & Hms2 & HSI2 & HSK2 & Hfr2).
  destruct HSI2 as [HB2 HAG2].
  pose proof (FRM_agree regs m1 m2 HF1 HAG2) as HF2.
  destruct (sc_post R2 regs m2 _ HB2 HSK2 HF2) as (R3 & Hms3 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & Hfr3).
  exists R3, m2. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
  split.
  { unfold scan_tree. unfold scnts0 in HB2. replace (mc + 1 - 0) with (mc + 1) in HB2 by lia. subst X1.
    destruct (Len X t 0 =? 0); exact HB2. }
  split; [rewrite E2; symmetry; exact P2|].
  apply (frame_fix R3 regs 2%bv); [rewrite E2; symmetry; exact P2|].
  apply (frame_fix R3 regs 8%bv); [exact E8|]. apply (frame_fix R3 regs 9%bv); [exact E9|].
  apply (frame_fix R3 regs 18%bv); [exact E18|]. apply (frame_fix R3 regs 19%bv); [exact E19|].
  apply (frame_fix R3 regs 20%bv); [exact E20|]. apply (frame_fix R3 regs 21%bv); [exact E21|].
  apply (frame_fix R3 regs 22%bv); [exact E22|].
  intros r Hr. rewrite (Hfr3 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
  rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
  apply Hfr1. eapply reg_in_sub; [| exact Hr]; reflexivity.
Qed.

End Walk.

Theorem scan_tree_run6u_ok : scan_tree_run6u.
Proof.
  unfold scan_tree_run6u, A6U_SCAN_TREE'.
  intros F mem0 mem S p PBL X ra regs sp t mc HL HFS Hret HB Ht Hmc Hl15 Hdl Hty Hcf HU P10 P11 P12 P2 P1.
  replace (zw 0x1e074) with (0x1e074%bv : word) by (apply bv_eq; reflexivity).
  exact (scan_tree_run F mem0 mem S p PBL X ra sp t mc HL HFS Hret HB Ht Hmc Hl15 Hdl Hty Hcf HU regs P10 P11 P12 P2 P1).
Qed.
End FXG.

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
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod BitsLib BuildTreeLib TrSmallModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel ScanModel SendModel TreesTab CompressModel
  BuildTreeModel GenBitlenModel RefSendTree3 RefSendTree4 RefFlushBlk9 RefFlushBlk11.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u TreesRod6u Callee6u TreesApi6u TrApi6u FillWin6uD
  CompressBlk6u_1 CompressBlk6u_4 BuildTree6u_11 TrSmall6u TrStored6u ScanTree6u SendTree6u_1 SendTree6u_5.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Local Opaque length_code_a dist_code_a extra_lbits_a base_length_a extra_dbits_a base_dist_a
             static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl bl_order_a extra_blbits_a.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition fb_extra6u (ds : deflate_state) (buf : option Z) (len last : Z) : Prop :=
  0 < ds_level ds ->
  let s0 := if cs_data_type (ds_strm ds) =? Z_UNKNOWN
            then set_strm ds (cset_data_type (ds_strm ds) (detect_data_type ds)) else ds in
  let X1 := build_tree s0 TL in
  let X2 := build_tree X1 TD in
  let mcl := ds_l_max_code X2 in
  let X3 := scan_tree X2 TL mcl in
  let mcd := ds_d_max_code X3 in
  let X4 := scan_tree X3 TD mcd in
  let X5 := build_tree X4 TB in
  let mb := build_bl_tree_loop 17 X5 18 in
  let X6 := set_opt_len X5 (wrap64 (ds_opt_len X5 + 3 * (mb + 1) + 5 + 5 + 4)) in
  256 <= ds_l_max_code X6 /\ 3 <= mb
  /\ (forall i, 0 <= i < 286 -> 0 <= arr_get (ds_dyn_ltree_fc X6) i < 2 ^ 15)
  /\ (forall i, 0 <= i < 30 -> 0 <= arr_get (ds_dyn_dtree_fc X6) i < 2 ^ 15)
  /\ (forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_fc X6) c < 2 ^ 15).

Definition FBSAFE6u (ds : deflate_state) (buf : option Z) (len last : Z) : Prop :=
  fb_safe ds buf len last /\ fb_extra6u ds buf len last.




Record FBHu (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
       (ds : deflate_state) (ra : word) (sp : Z) (buf : option Z) (bufp len last : Z) : Prop := {
  fbh_mset : memset_run6u;
  fbh_mcpy : memcpy_run6u;
  fbh_L : BRH F S p PBL;
  fbh_FS : sub_franges F S dsl_SIZE;
  fbh_ret : ret_ok ra;
  fbh_br : BR6u F mem0 S p PBL mem ds;
  fbh_binv : BINV PBL ds;
  fbh_rod : trees_rod_clear6u mem;
  fbh_last : 0 <= last <= 1;
  fbh_len : 0 <= len < 2 ^ 32;
  fbh_fr : call_frame F mem S (p_pending_buf p) PBL sp TFB_FRAME6u;
  fbh_src : fb_src6u F mem p ds buf bufp len;
  fbh_strm : fb_strm6u F mem S p PBL sp ds;
  fbh_pbl : 0 < PBL;
  fbh_ub : UBT S p }.

Section Walk.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word) (sp : Z).
Variables (buf : option Z) (bufp len last : Z).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation SP := (sp - 64).
Local Abbreviation BRm := (BR6u F mem0 S p PBL).

Hypothesis HH : FBHu F mem0 mem S p PBL ds ra sp buf bufp len last.

Let MEMSET : memset_run6u := fbh_mset _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let MEMCPY : memcpy_run6u := fbh_mcpy _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := fbh_L _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HFS : sub_franges F S dsl_SIZE := fbh_FS _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hret : ret_ok ra := fbh_ret _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := fbh_br _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hbinv : BINV PBL ds := fbh_binv _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HRC0 : trees_rod_clear6u mem := fbh_rod _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hlast : 0 <= last <= 1 := fbh_last _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hlen : 0 <= len < 2 ^ 32 := fbh_len _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hcf : call_frame F mem S PB PBL sp TFB_FRAME6u := fbh_fr _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HPBL : 0 < PBL := fbh_pbl _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HUB : UBT S p := fbh_ub _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hsp : TFB_FRAME6u <= sp <= 2 ^ 63 := proj1 Hcf.
Definition GFB : franges := [(S, dsl_SIZE); (PB, PBL); (SP - 272, 272)].

Definition FI (m1 m : word -> option byte) (X : deflate_state) : Prop :=
  BRm m X /\ trees_rod_clear6u m /\ agree_out GFB m1 m /\ mapped m (SP - 272) 336
  /\ (forall x, mem x <> None -> m x <> None).

Lemma FI_self : forall m1 m X, FI m1 m X -> FI m m X.
Proof. intros m1 m X (A & B & C & D & E). split; [exact A|]. split; [exact B|]. split; [apply agree_out_refl|]. split; assumption. Qed.

Lemma FI_call_frame : forall m1 m X K, FI m1 m X -> 0 <= K <= 272 ->
  call_frame (Fmin S PB PBL SP K) m S PB PBL SP K.
Proof.
  intros m1 m X K (HB & HRC & HAG & MF & HGR) HK.
  pose proof Hcf as (Hsp0 & HFf & Hmf & HfS & HfP). unfold TFB_FRAME6u in *.
  unfold call_frame, Fmin.
  split; [lia|]. split; [apply sub_franges_later; apply sub_franges_later; apply sub_franges_here; lia|].
  split; [intros x Hx; apply MF; lia|]. split; lia.
Qed.

Lemma Fmin_sub : forall K x, 0 <= K <= 272 -> in_franges (Fmin S PB PBL SP K) x -> in_franges F x.
Proof.
  intros K x HK Hx. pose proof Hcf as (Hsp0 & HFf & _). pose proof HLb as (_ & _ & _ & _ & _ & _ & Hsb). unfold TFB_FRAME6u in *.
  unfold Fmin in Hx. destruct Hx as [Hx|[Hx|[Hx|[]]]]; cbn in Hx.
  - apply HFS. exact Hx.
  - apply Hsb. exact Hx.
  - apply HFf. lia.
Qed.

Lemma FI_after : forall m1 m m' X X' K,
  FI m1 m X -> 0 <= K <= 272 -> BR6u (Fmin S PB PBL SP K) m S p PBL m' X' -> trees_rod_clear6u m' ->
  FI m1 m' X'
  /\ (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v).
Proof.
  intros m1 m m' X X' K HF HK HB' HRC'. pose proof HF as (HB & HRC & HAG & MF & HGR).
  pose proof Hcf as (Hsp0 & HFf & Hmf & HfS & HfP). pose proof HLb as ((HS1 & HS2) & (HP1 & HP2) & Hapb & _ & _ & _ & Hsb).
  unfold TFB_FRAME6u, dsl_SIZE in *.
  destruct (BR_back F _ mem0 S p PBL m m' X _ HB HB' (fun x Hx => Fmin_sub K x HK Hx)) as [HB2 Hag].
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & _ & MS' & MP' & HGR').
  split.
  - split; [exact HB2|]. split; [exact HRC'|]. split.
    { eapply agree_out_trans; [exact HAG|]. eapply agree_out_weaken; [exact Hag|].
      unfold Fmin, GFB. intros x [Hx|[Hx|[Hx|[]]]]; cbn in Hx |- *; unfold dsl_SIZE in *; lia. }
    split; [intros x Hx; apply HGR'; apply MF; exact Hx|].
    intros x Hx. apply HGR'. apply HGR. exact Hx.
  - intros a w v Hc Ha1 Ha2.
    apply (cell_agree_out s6u_segs _ m m' a w v Hag); [| lia | lia | exact Hc].
    unfold Fmin. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; unfold dsl_SIZE in Hin; lia.
Qed.

Lemma rod_after : forall m m' K, 0 <= K <= 272 -> trees_rod_clear6u m -> mapped m S dsl_SIZE -> mapped m PB PBL ->
  mapped m (SP - 272) 336 -> agree_out (Fmin S PB PBL SP K) m m' -> trees_rod_clear6u m'.
Proof.
  intros m m' K HK HRC MS MP MF Hag. pose proof Hcf as (Hsp0 & _). unfold TFB_FRAME6u in *.
  apply (trees_rod_clear_agree R6u _ m m' HRC Hag).
  unfold Fmin. intros x [Hx|[Hx|[Hx|[]]]]; cbn in Hx; [apply MS; exact Hx | apply MP; exact Hx | apply MF; lia].
Qed.

Definition tfF (X : deflate_state) (f : nat) (x : Z) : Z :=
  match f with
  | 0%nat => pb (ds_dyn_ltree_fc X) x | 1%nat => pb (ds_dyn_ltree_dl X) x | 2%nat => pb (ds_dyn_dtree_dl X) x
  | 3%nat => pb (ds_bl_tree_fc X) x | 4%nat => pb (ds_bl_tree_dl X) x | _ => arr_get bl_order_a x
  end.

Definition FBv : list (nat * Z) := [(0%nat, 65536); (1%nat, 65536); (2%nat, 65536); (3%nat, 65536); (4%nat, 65536); (5%nat, 19)].

Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 17); (36%nat, 65536); (37%nat, 2); (38%nat, 2 ^ 32);
   (39%nat, 2 ^ 64); (40%nat, 2 ^ 63); (41%nat, 600); (42%nat, 600); (43%nat, 19); (44%nat, 2 ^ 64);
   (45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64); (48%nat, 2 ^ 64); (49%nat, 2 ^ 64);
   (50%nat, 2 ^ 64); (51%nat, 2 ^ 64); (52%nat, 2 ^ 64); (53%nat, 2 ^ 64); (54%nat, 2 ^ 64); (55%nat, 2 ^ 64);
   (56%nat, 2 ^ 64); (57%nat, 2 ^ 64)].

Definition KR (R : bvmap 5 word) : Prop :=
  getr R 8 = zw S /\ getr R 9 = zw last /\ getr R 20 = zw (S + 5912) /\ getr R 21 = zw (S + 2047) /\ getr R 2 = zw SP.
Definition KPN : list (Z * expr) :=
  [(8, EVar 32); (9, EVar 37); (20, EAdd (EVar 32) (ELit 5912)); (21, EAdd (EVar 32) (ELit 2047)); (2, EVar 40)].

Definition KRW (R : bvmap 5 word) : Prop := getr R 8 = zw S /\ getr R 9 = zw last /\ getr R 2 = zw SP.
Definition KPW : list (Z * expr) := [(8, EVar 32); (9, EVar 37); (2, EVar 40)].
Lemma KR_W : forall R, KR R -> KRW R.
Proof. intros R (K8 & K9 & _ & _ & K2). exact (conj K8 (conj K9 K2)). Qed.

Lemma HS8 : S mod 8 = 0.
Proof. exact (ubt_S8 _ _ HUB). Qed.


Lemma call_bt : forall regs m1 m X tt (ra' : word),
  FI m1 m X -> bt_safe X tt -> ret_ok ra' ->
  getr regs 10 = zw S -> getr regs 11 = zw (S + dsc_off tt) -> getr regs 2 = zw SP -> getr regs 1 = ra' ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1ca38 : word) m s6u_rom) (mkst R ra' m' s6u_rom)
    /\ FI m1 m' (build_tree X tt)
    /\ (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v)
    /\ getr R 2 = getr regs 2
    /\ (forall r : reg, reg_in r BT_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X tt ra' HF HS Hret' P10 P11 P2 P1. pose proof HF as (HB & HRC & HAG & MF & HGR).
  pose proof (build_tree_run6u_ok (Fmin S PB PBL SP 272) m m S p PBL X ra' SP tt regs
                (BRH_min F S p PBL SP 272 HLb) (Fmin_S _ _ _ _ _) Hret' HS8 (BR_self F _ mem0 S p PBL m X HB) HRC HS
                (FI_call_frame m1 m X 272 HF ltac:(lia)) P10 P11 P2 P1) as (R & m' & Hms & HB' & HRC' & Q2 & Hfr).
  unfold A6U_BUILD_TREE in Hms. replace (zw 0x1ca38) with (0x1ca38%bv : word) in Hms by (apply bv_eq; reflexivity).
  destruct (FI_after m1 m m' X _ 272 HF ltac:(lia) HB' HRC') as [HF' HC].
  exists R, m'. split; [exact Hms|]. split; [exact HF'|]. split; [exact HC|]. split; [exact Q2 | exact Hfr].
Qed.


Lemma call_sc : forall regs m1 m X t mc (ra' : word),
  FI m1 m X -> ret_ok ra' ->
  (t = TL \/ t = TD) -> 0 <= mc /\ mc + 1 < tsize t ->
  (forall i, 0 <= i <= mc -> 0 <= Len X t i <= 15) ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl X t) i < 65536) ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X) i < 65536) ->
  getr regs 10 = zw S -> getr regs 11 = zw (S + toff t) -> getr regs 12 = zw mc -> getr regs 2 = zw SP -> getr regs 1 = ra' ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1e074 : word) m s6u_rom) (mkst R ra' m' s6u_rom)
    /\ FI m1 m' (scan_tree X t mc)
    /\ (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v)
    /\ getr R 2 = getr regs 2
    /\ (forall r : reg, reg_in r SC_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X t mc ra' HF Hret' Ht Hmc Hlen' Hdl Hbc P10 P11 P12 P2 P1.
  pose proof HF as (HB & HRC & HAG & MF & HGR).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & MP & _).
  pose proof (scan_tree_run6u_ok (Fmin S PB PBL SP 64) m m S p PBL X ra' regs SP t mc
                (BRH_min F S p PBL SP 64 HLb) (Fmin_S _ _ _ _ _) Hret' (BR_self F _ mem0 S p PBL m X HB)
                Ht Hmc Hlen' Hdl Hbc (FI_call_frame m1 m X 64 HF ltac:(lia)) HUB P10 P11 P12 P2 P1)
    as (R & m' & Hms & HB' & Q2 & Hfr).
  unfold A6U_SCAN_TREE' in Hms. replace (zw 0x1e074) with (0x1e074%bv : word) in Hms by (apply bv_eq; reflexivity).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & Hag & _).
  destruct (FI_after m1 m m' X _ 64 HF ltac:(lia) HB' (rod_after m m' 64 ltac:(lia) HRC MS MP MF Hag)) as [HF' HC].
  exists R, m'. split; [exact Hms|]. split; [exact HF'|]. split; [exact HC|]. split; [exact Q2 | exact Hfr].
Qed.


Lemma call_ib : forall regs m1 m X (ra' : word),
  FI m1 m X -> ret_ok ra' ->
  getr regs 10 = zw S -> getr regs 1 = ra' ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1b73c : word) m s6u_rom) (mkst R ra' m' s6u_rom)
    /\ FI m1 m' (init_block X)
    /\ (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v)
    /\ (forall r : reg, reg_in r IB_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X ra' HF Hret' P10 P1. pose proof HF as (HB & HRC & HAG & MF & HGR).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & MP & _).
  pose proof (init_block_run6u_ok (Fmin S PB PBL SP 0) m m S p PBL X ra' regs
                (BRH_min F S p PBL SP 0 HLb) (Fmin_S _ _ _ _ _) Hret' (BR_self F _ mem0 S p PBL m X HB) HUB P10 P1)
    as (R & m' & Hms & HB' & Hfr).
  unfold A6U_INIT_BLOCK in Hms. replace (zw 0x1b73c) with (0x1b73c%bv : word) in Hms by (apply bv_eq; reflexivity).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & Hag & _).
  destruct (FI_after m1 m m' X _ 0 HF ltac:(lia) HB' (rod_after m m' 0 ltac:(lia) HRC MS MP MF Hag)) as [HF' HC].
  exists R, m'. split; [exact Hms|]. split; [exact HF'|]. split; [exact HC | exact Hfr].
Qed.


Lemma tsb_src_now : forall m X,
  BRm m X -> ds_window X = ds_window ds -> (len <> 0 -> buf <> None) -> tsb_src6u F m p X buf bufp len.
Proof.
  intros m X HB EW Hb Hnz. rewrite EW.
  pose proof (fbh_src _ _ _ _ _ _ _ _ _ _ _ _ _ HH) as Hsrc. unfold fb_src6u in Hsrc.
  destruct buf as [off|]; [| exfalso; exact (Hb Hnz eq_refl)].
  destruct Hsrc as (Hbp & Hnz' & Hrest). destruct (Hrest Hnz) as (Ho & Hoff & Hcells & Hrng & Hw1 & Hw2 & Hdisj).
  exists off. split; [reflexivity|]. split; [exact Hbp|]. split; [exact Ho|]. split; [exact Hoff|].
  split.
  { pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HBR0) as (_ & _ & _ & _ & Hag0 & _).
    pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & Hag1 & _).
    apply (cells_agree_out s6u_segs F mem m); [exact (agree_out_via F mem0 mem m Hag0 Hag1) | | cbn; lia | lia | lia | exact Hcells].
    intros x Hx. apply Hdisj. lia. }
  split; [exact Hrng|]. split; [exact Hw1|]. split; [exact Hw2 | exact Hdisj].
Qed.

Lemma tsb_src_min : forall m X K, 0 <= K <= 272 -> tsb_src6u F m p X buf bufp len -> tsb_src6u (Fmin S PB PBL SP K) m p X buf bufp len.
Proof.
  intros m X K HK H Hnz. destruct (H Hnz) as (off & A & B & C & D & E & G & I1 & I2 & J).
  exists off. repeat (split; [assumption|]).
  intros x Hx Hin. exact (J x Hx (Fmin_sub K x HK Hin)).
Qed.

Lemma call_tsb : forall regs m1 m X (ra' : word),
  FI m1 m X -> BINV PBL X -> ds_pending (tr_stored_block X buf len last) <= PBL ->
  ds_window X = ds_window ds -> (len <> 0 -> buf <> None) -> ret_ok ra' ->
  getr regs 10 = zw S -> getr regs 11 = zw bufp -> getr regs 12 = zw len -> getr regs 13 = zw last ->
  getr regs 2 = zw SP -> getr regs 1 = ra' ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1b9e4 : word) m s6u_rom) (mkst R ra' m' s6u_rom)
    /\ FI m1 m' (tr_stored_block X buf len last)
    /\ (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v)
    /\ (forall r : reg, reg_in r SB_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X ra' HF HBI Hroom EW Hb Hret' P10 P11 P12 P13 P2 P1. pose proof HF as (HB & HRC & HAG & MF & HGR).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & MP & _).
  pose proof (tr_stored_block_run6u_ok (Fmin S PB PBL SP 48) m m S p PBL X ra' regs SP buf bufp len last MEMCPY
                (BRH_min F S p PBL SP 48 HLb)
                (sub_franges_mono _ S dsl_SIZE (S + 5944) 4 (Fmin_S S PB PBL SP 48) ltac:(lia) ltac:(unfold dsl_SIZE; lia))
                Hret' (BR_self F _ mem0 S p PBL m X HB) HBI Hroom Hlast Hlen
                (FI_call_frame m1 m X 48 HF ltac:(lia))
                (tsb_src_min m X 48 ltac:(lia) (tsb_src_now m X HB EW Hb)) HUB P10 P11 P12 P13 P2 P1)
    as (R & m' & Hms & HB' & Hfr).
  unfold A6U_TR_STORED_BLOCK in Hms. replace (zw 0x1b9e4) with (0x1b9e4%bv : word) in Hms by (apply bv_eq; reflexivity).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & Hag & _).
  destruct (FI_after m1 m m' X _ 48 HF ltac:(lia) HB' (rod_after m m' 48 ltac:(lia) HRC MS MP MF Hag)) as [HF' HC].
  exists R, m'. split; [exact Hms|]. split; [exact HF'|]. split; [exact HC | exact Hfr].
Qed.


Lemma call_st : forall regs m1 m X t mc (ra' : word),
  FI m1 m X -> ret_ok ra' ->
  (t = TL \/ t = TD) -> 0 <= mc /\ mc + 1 < tsize t ->
  (forall i, 0 <= i <= mc -> 0 <= Len X t i <= 15) ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl X t) i < 65536) ->
  (forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_fc X) c < 2 ^ 15) ->
  (forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl X) c < 16) ->
  BINV PBL X -> 0 < PBL ->
  RefSendTree4.send_tree_safe PBL X t mc ->
  getr regs 10 = zw S -> getr regs 11 = zw (S + toff t) -> getr regs 12 = zw mc -> getr regs 2 = zw SP -> getr regs 1 = ra' ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1e274 : word) m s6u_rom) (mkst R ra' m' s6u_rom)
    /\ FI m1 m' (send_tree X t mc)
    /\ SendTree6u_1.PURE PBL X (send_tree X t mc)
    /\ (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v)
    /\ getr R 2 = getr regs 2
    /\ (forall r : reg, reg_in r ST_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X t mc ra' HF Hret' Ht Hmc Hlen' Hdl Hbc Hbl HBI HPBL0 Hsafe P10 P11 P12 P2 P1.
  pose proof HF as (HB & HRC & HAG & MF & HGR).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & MP & _).
  assert (HH' : STH (Fmin S PB PBL SP 112) m m S p PBL X ra' SP t mc).
  { refine {| sth_ret := Hret'; sth_L := BRH_min F S p PBL SP 112 HLb; sth_fr := FI_call_frame m1 m X 112 HF ltac:(lia);
              sth_br := BR_self F _ mem0 S p PBL m X HB; sth_t := Ht; sth_mc := Hmc;
              sth_len := Hlen'; sth_dl := Hdl; sth_bc := Hbc; sth_bl := Hbl; sth_binv := HBI; sth_pbl := HPBL0; sth_ub := HUB |}. }
  destruct (send_tree_run _ m m S p PBL X ra' SP t mc HH' regs P10 P11 P12 P2 P1 Hsafe)
    as (R & m' & Hms & HB' & HPU & Q2 & Hfr).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & Hag & _).
  destruct (FI_after m1 m m' X _ 112 HF ltac:(lia) HB' (rod_after m m' 112 ltac:(lia) HRC MS MP MF Hag)) as [HF' HC].
  exists R, m'. split; [exact Hms|]. split; [exact HF'|]. split; [exact HPU|]. split; [exact HC|]. split; [exact Q2 | exact Hfr].
Qed.


Lemma call_cb : forall regs m1 m X LT DT lfc ldl dfc ddl (ra' : word),
  FI m1 m X -> ret_ok ra' ->
  compress_block_ok PBL X lfc ldl dfc ddl ->
  (forall m'' s', BR6u (Fmin S PB PBL SP 96) m S p PBL m'' s' ->
     (forall t, tree_fc s' t = tree_fc X t) -> (forall t, tree_dl s' t = tree_dl X t) -> trees_rod_clear6u m'' ->
     cells s6u_segs m'' LT 4 2 286 (arr_get lfc) /\ cells s6u_segs m'' (LT + 2) 4 2 286 (arr_get ldl)
     /\ cells s6u_segs m'' DT 4 2 30 (arr_get dfc) /\ cells s6u_segs m'' (DT + 2) 4 2 30 (arr_get ddl)) ->
  0 <= LT /\ LT + 1144 <= 2 ^ 63 -> 0 <= DT /\ DT + 120 <= 2 ^ 63 ->
  0 <= ds_sym_next X /\ ds_sym_next X + 3 < 2 ^ 31 -> 0 <= ds_lit_bufsize X < 2 ^ 32 -> 0 < PBL ->
  0 < LT /\ LT mod 2 = 0 -> 0 < DT /\ DT mod 2 = 0 ->
  (forall i, 0 <= i < 286 -> 0 <= arr_get lfc i < 2 ^ 15) -> (forall i, 0 <= i < 30 -> 0 <= arr_get dfc i < 2 ^ 15) ->
  getr regs 10 = zw S -> getr regs 11 = zw LT -> getr regs 12 = zw DT -> getr regs 2 = zw SP -> getr regs 1 = ra' ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1d5c8 : word) m s6u_rom) (mkst R ra' m' s6u_rom)
    /\ FI m1 m' (compress_block X lfc ldl dfc ddl)
    /\ (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v)
    /\ getr R 2 = getr regs 2
    /\ (forall r : reg, reg_in r CompressBlk6u_1.CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X LT DT lfc ldl dfc ddl ra' HF Hret' Hok HT HLT HDT Hsn HLB HPBL0 Hlt2 Hdt2 Hl15 Hd15 P10 P11 P12 P2 P1.
  pose proof HF as (HB & HRC & HAG & MF & HGR).
  pose proof (ubt_pb1 _ _ HUB) as Hpb0.
  assert (HH' : CBHu (Fmin S PB PBL SP 96) m m S p PBL X ra' SP LT DT lfc ldl dfc ddl).
  { refine {| cbh_ret := Hret'; cbh_L := BRH_min F S p PBL SP 96 HLb; cbh_fr := FI_call_frame m1 m X 96 HF ltac:(lia);
              cbh_br := BR_self F _ mem0 S p PBL m X HB; cbh_rod := HRC; cbh_ok := Hok; cbh_T := HT;
              cbh_LT := HLT; cbh_DT := HDT; cbh_sn := Hsn; cbh_LB := HLB; cbh_PBL := HPBL0;
              cbh_al := HS8; cbh_pb0 := Hpb0; cbh_lt0 := Hlt2; cbh_dt0 := Hdt2; cbh_lfc15 := Hl15; cbh_dfc15 := Hd15 |}. }
  destruct (compress_block_run _ m m S p PBL X ra' SP LT DT lfc ldl dfc ddl HH' regs P10 P11 P12 P2 P1)
    as (R & m' & Hms & HB' & HRC' & Q2 & Hfr).
  destruct (FI_after m1 m m' X _ 96 HF ltac:(lia) HB' HRC') as [HF' HC].
  exists R, m'. split; [exact Hms|]. split; [exact HF'|]. split; [exact HC|]. split; [exact Q2 | exact Hfr].
Qed.

End Walk.
End FXG.

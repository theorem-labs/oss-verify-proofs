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
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2 MemFill
  RomRead TreesRod BitsLib BuildTreeLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel SendModel TreesTab BuildTreeModel GenBitlenModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 TreesRod6 Callee6 TreesApi6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import BuildTree6_1 BuildTree6_2 BuildTree6_3 BuildTree6_4 BuildTree6_5 BuildTree6_5b BuildTree6_6 BuildTree6_7 BuildTree6_8 BuildTree6_9.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

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



Definition stC10 : cfg := CFG BuildTree6_6.FB6 [] [EVar 35%nat] [0x1b94c] [].

Definition VB10 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 64);
   (36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64);
   (42%nat, 2 ^ 64); (43%nat, 2 ^ 64); (44%nat, 2 ^ 64); (45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64)].

Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC10 VB10 fuel dirs rds pins pv FC DL HP DP BC.

Local Abbreviation ML := (sd_max_length t).
Local Abbreviation BASE := (sd_extra_base t).


Lemma epi_blk : forall regs (regs0 : bvmap 5 word) m,
  FRM m regs0 -> mapped m SP 144 -> getr regs0 1 = ra -> getr regs 2 = zw SP ->
  exists R,
    msteps s6_segs (mkst regs (0x1c1d4 : word) m s6_rom) (mkst R ra m s6_rom)
    /\ getr R 2 = zw sp
    /\ getr R 1 = getr regs0 1 /\ getr R 8 = getr regs0 8 /\ getr R 9 = getr regs0 9
    /\ getr R 18 = getr regs0 18 /\ getr R 19 = getr regs0 19 /\ getr R 20 = getr regs0 20 /\ getr R 21 = getr regs0 21
    /\ getr R 22 = getr regs0 22 /\ getr R 23 = getr regs0 23 /\ getr R 24 = getr regs0 24 /\ getr R 25 = getr regs0 25
    /\ getr R 26 = getr regs0 26 /\ getr R 27 = getr regs0 27
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m HF MF P1 P2.
  destruct HF as (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'. pose proof Hsp as Hsp'. pose proof Hret as Hret'.
  pose proof Htt as Htt'.
  unfold mapped in MF. rewrite P1 in C1.
  pose proof (u64_range ra) as U1.
  pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19.
  pose proof (u64_range (getr regs0 20)) as U20. pose proof (u64_range (getr regs0 21)) as U21.
  pose proof (u64_range (getr regs0 22)) as U22. pose proof (u64_range (getr regs0 23)) as U23.
  pose proof (u64_range (getr regs0 24)) as U24. pose proof (u64_range (getr regs0 25)) as U25.
  pose proof (u64_range (getr regs0 26)) as U26. pose proof (u64_range (getr regs0 27)) as U27.
  run 20%nat NoDirs
      [RVal (EVar 35); RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40); RVal (EVar 41);
       RVal (EVar 42); RVal (EVar 43); RVal (EVar 44); RVal (EVar 45); RVal (EVar 46); RVal (EVar 47)]
      [(2, EVar 34)]
      [S; T; SP; bv_unsigned ra; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18);
       bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 22);
       bv_unsigned (getr regs0 23); bv_unsigned (getr regs0 24); bv_unsigned (getr regs0 25); bv_unsigned (getr regs0 26);
       bv_unsigned (getr regs0 27)]
      (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) (arr_make 1 0).
  all: try solve [intros; apply (BuildTree6_6.extra_view_bound' t)].
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ _ _) => exists R; split; [exact Hms|]; clear Hms
  end.
  repeat match goal with |- _ /\ _ => split end;
    try (let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; rewrite <- ?P1; rewrite ?zw_u; first [reflexivity | f_equal; lia] end).
  fr_weak Hfr.
Qed.

Goal True. idtac "epi_blk OK". exact I. Qed.

Lemma FRM_keep : forall m1 m regs0, agree_out GB m1 m -> (S + dsl_SIZE <= SP \/ SP + 144 <= S) -> FRM m1 regs0 -> FRM m regs0.
Proof.
  intros m1 m regs0 HAG Hapart HF. pose proof Hsp as Hsp'.
  assert (K : forall a v, cell s6_segs m1 a 8 v -> SP + 40 <= a /\ a + 8 <= SP + 144 -> cell s6_segs m a 8 v).
  { intros a v Hc Ha. apply (cell_agree_out s6_segs GB m1 m a 8 v HAG); [| lia | cbn; lia | exact Hc].
    intros x Hx [H|[H|[H|[]]]]; cbn in H; unfold dsl_SIZE in *; lia. }
  unfold BuildTree6_1.FRM in HF |- *.
  repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with |- cell _ _ ?a 8 _ =>
      apply K; [ (repeat match type of HF with _ /\ _ => let X := fresh in destruct HF as [X HF]; try exact X end); try exact HF | lia ] end.
Qed.


Local Ltac frs Hfrs Hr :=
  lazymatch Hfrs with
  | ?H :: ?rest => rewrite (H _ ltac:(eapply reg_in_sub; [|exact Hr]; reflexivity)); frs rest Hr
  | _ => idtac
  end.

Theorem build_tree_run : forall regs,
  memset_run6 ->
  GenBitlenModel.bt_safe ds t ->
  getr regs 10 = zw S -> getr regs 11 = zw (S + dsc_off t) -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m',
    msteps s6_segs (mkst regs (0x1b94c : word) mem s6_rom) (mkst R ra m' s6_rom)
    /\ BRm m' (build_tree ds t)
    /\ trees_rod_clear6 m'
    /\ getr R 2 = getr regs 2
    /\ (forall r : reg, reg_in r BT_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs MEMSET HSAFE P10 P11 P2 P1.
  pose proof elems_range as He. pose proof tsize_elems as Hte. pose proof Htt as Htt'. pose proof (BuildTree6_6.ml_range t) as Hml.
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  assert (Hapart : S + dsl_SIZE <= SP \/ SP + 144 <= S) by (unfold dsl_SIZE; lia).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HBR0) as (_ & _ & HTL & _).
  pose proof (tree_lens_fc ds t HTL) as LFC0. pose proof (tree_lens_dl ds t HTL) as LDL0.
  pose proof HTL as (_ & _ & _ & _ & _ & _ & LBC0 & LHP0 & LDP0).
  unfold GenBitlenModel.bt_safe in HSAFE. cbv zeta in HSAFE.
  destruct HSAFE as (RFC0 & ROL0 & RSL0 & HS1).
  assert (E0 : set_heap_max (set_heap_len ds 0) HEAP_SIZE = X0).
  { unfold BuildTree6_1.X0. rewrite <- (bt_upd_self ds t) at 1. rewrite bt_set_heap_len, bt_set_heap_max. reflexivity. }
  rewrite E0 in HS1. unfold BuildTree6_1.X0 in HS1.
  destruct (BuildTree6_1.pro_blk _ _ _ _ _ _ _ _ _ t HH regs P10 P11 P2 P1) as (R0 & m1 & Hms0 & HC0 & HR0 & HFRM & HM1 & Hfr0).
  destruct (BuildTree6_1.l1_loop _ _ _ _ _ _ _ _ _ _ HH (tree_fc ds t) (ds_bl_count ds) 573 (ds_opt_len ds) (ds_static_len ds) (max_code ds t) RFC0
              (Z.to_nat E) 0 R0 m1 m1 (tree_dl ds t) (ds_heap ds) 0 (ds_depth ds) (-1)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(left; split; reflexivity) LDL0 LHP0 LDP0 HC0 HR0)
    as (R1 & m2 & DL1 & HP1 & HL1 & DP1 & mc1 & E1 & Hms1 & HC1 & HR1 & Hhl1 & LDL1 & LHP1 & LDP1 & Hinv1 & Hfr1).
  unfold BuildTree6_1.L1 in E1. rewrite Z.sub_0_r in E1.
  rewrite E1 in HS1. cbv beta iota in HS1.
  destruct (BuildTree6_2.c_phase _ _ _ _ _ _ _ _ _ _ HH R1 m1 m2 DL1 HP1 HL1 DP1 mc1 HC1 Hhl1 Hinv1 RFC0 LFC0 LHP1 LDP1 ROL0 RSL0 HR1)
    as (R2 & m3 & FC2 & HP2 & HL2 & DP2 & OL2 & SL2 & mc2 & E2 & Hms2 & HC2 & HR2 & Hhl2 & Hmc2 & LFC2 & LHP2 & LDP2 & ROL2 & RSL2 & Hfr2).
  unfold BuildTree6_2.L2 in E2. rewrite E2 in HS1. cbv beta iota zeta in HS1.
  rewrite (bt_set_max_code ds t) in HS1. rewrite !(bt_heap_len ds t) in HS1.
  destruct HS1 as (Hheap3 & Hdepth3 & Hfreq3 & HS4).
  assert (PQ2 : BuildTree6_3.PQ t HL2 HP2).
  { intros i Hi. pose proof (Hheap3 i Hi) as X. rewrite bt_heap_get in X. exact X. }
  assert (RDP2 : forall i, 0 <= i < 573 -> 0 <= arr_get DP2 i < 256).
  { intros i Hi. pose proof (Hdepth3 i Hi) as X. rewrite bt_depth_get in X. exact X. }
  assert (RFC2 : forall i, 0 <= i < tsize t -> 0 <= arr_get FC2 i < 65536).
  { intros i Hi. pose proof (Hfreq3 i Hi) as X. rewrite bt_Freq in X. exact X. }
  assert (Hhl2' : 2 <= HL2 <= 572) by lia. assert (Hmc2' : 0 <= mc2 < 600) by lia.
  destruct (BuildTree6_3.d_pro _ _ _ _ _ _ _ _ _ _ HH FC2 DL1 HL2 573 DP2 (ds_bl_count ds) OL2 SL2 mc2 RFC2 Hhl2' LFC2 Hmc2'
              R2 m1 m3 HP2 (max_code ds t) HC2 PQ2 LHP2 HR2)
    as (R3 & m4 & Hms3 & HD3 & HO3 & Hfr3).
  assert (Hdiv : 1 <= HL2 / 2 /\ HL2 / 2 * 2 <= HL2) by (pose proof (Z.div_mod HL2 2 ltac:(lia)); pose proof (Z.mod_pos_bound HL2 2 ltac:(lia)); lia).
  destruct (BuildTree6_3.outer3 _ _ _ _ _ _ _ _ _ _ HH FC2 DL1 HL2 573 DP2 (ds_bl_count ds) OL2 SL2 mc2 RFC2 RDP2 Hhl2' LFC2 LDP2 Hmc2'
              (Z.to_nat (HL2 / 2)) (HL2 / 2) R3 m1 m4 HP2 ltac:(lia) HD3 HO3 ltac:(lia) ltac:(lia))
    as (R4 & m5 & HP4 & E4 & Hms4 & HD4 & HO4 & Hfr4).
  unfold BuildTree6_3.L3 in E4. rewrite E4 in HS4.
  destruct HD4 as (HC4 & PQ4 & LHP4).
  destruct (BuildTree6_4.e0_blk _ _ _ _ _ _ _ _ _ _ HH (ds_bl_count ds) OL2 SL2 mc2 Hmc2' R4 m1 m5 FC2 DL1 HP4 HL2 573 DP2
              HC4 (conj PQ4 LHP4) (conj RFC2 (conj RDP2 (conj LFC2 LDP2))) LDL1 Hhl2' HO4)
    as (R5 & m6 & Hms5 & HE5 & HR5 & Hfr5).
  destruct (BuildTree6_5b.e_loop _ _ _ _ _ _ _ _ _ _ HH (ds_bl_count ds) OL2 SL2 mc2 Hmc2' 573%nat R5 m1 m6 FC2 DL1 HP4 HL2 573 DP2 E
              HE5 HR5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (R6 & m7 & FC5 & DL5 & HP5 & K & DP5 & E5 & Hms6 & HE6 & HR6 & HK & Hfr6).
  rewrite E5 in HS4.
  rewrite !(bt_heap_max ds t), !(bt_set_heap_max ds t), !(bt_heap_max ds t) in HS4. unfold SMALLEST in HS4.
  rewrite !(bt_heap_get ds t), !(bt_heap_set ds t) in HS4.
  destruct HE6 as (HC6 & (PQ6 & LHP6) & (RFC6 & RDP6 & LFC6 & LDP6) & LDL6 & C0_6).
  assert (Rh1 : 0 <= arr_get HP5 1 < tsize t) by (apply PQ6; lia).
  rewrite !(bt_heap_max ds t) in HS4.
  destruct HS4 as (PQH & RDL5 & HS8).
  rewrite !(bt_tree_dl ds t) in RDL5.
  rewrite !(bt_bl_count ds t), !(bt_set_bl_count ds t) in HS8. change (MAX_BITS + 1) with 16 in HS8.
  rewrite !(bt_heap_max ds t), !(bt_heap_get ds t) in HS8.
  rewrite (arr_get_set HP5 (K - 1) (K - 1)) in HS8. unfold arr_inb in HS8. rewrite LHP6 in HS8.
  replace ((K - 1 =? K - 1) && ((0 <=? K - 1) && (K - 1 <? 573))) with true in HS8
    by (symmetry; rewrite !Bool.andb_true_iff, Z.eqb_eq, Z.leb_le, Z.ltb_lt; lia).
  rewrite !(bt_set_Len ds t) in HS8. rewrite !(bt_heap_max ds t) in HS8. replace (K - 1 + 1) with K in HS8 by lia.
  destruct HS8 as (HOK1 & HS10).
  assert (HK' : 1 <= K <= 573) by lia.
  assert (PQH' : forall h, K <= h < 573 -> 0 <= arr_get (arr_set HP5 (K - 1) (arr_get HP5 1)) h < tsize t).
  { intros h Hh. pose proof (PQH h ltac:(unfold HEAP_SIZE, L_CODES, LITERALS, LENGTH_CODES; lia)) as X. rewrite bt_heap_get in X. exact X. }
  set (HP' := arr_set HP5 (K - 1) (arr_get HP5 1)) in *.
  destruct (BuildTree6_6.f1_blk _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K RFC6 LFC6 Hmc2 HK' PQH' R6 m1 m7 DL5 HP5 (ds_bl_count ds) OL2 SL2
              HC6 ltac:(lia) LHP6 C0_6 HR6)
    as (R7 & m8 & Hms7 & HC7 & HX7 & C0_7 & Hfr7).
  destruct (BuildTree6_6.call_memset _ _ _ _ _ _ _ _ _ _ HH FC5 DP5 mc2 K R7 m1 m8 DL5 HP' (ds_bl_count ds) OL2 SL2 MEMSET HC7 LBC0 HX7)
    as (R8 & m9 & Hms8 & HC8 & HX8 & CELLS8 & Hfr8).
  pose proof (CELLS8 _ _ _ C0_7 ltac:(lia) ltac:(cbn; lia)) as C0_8.
  assert (Rh1' : 0 <= arr_get HP' (K - 1) < tsize t).
  { subst HP'. rewrite arr_get_set. unfold arr_inb. rewrite LHP6.
    replace ((K - 1 =? K - 1) && ((0 <=? K - 1) && (K - 1 <? 573))) with true
      by (symmetry; rewrite !Bool.andb_true_iff, Z.eqb_eq, Z.leb_le, Z.ltb_lt; lia). exact Rh1. }
  destruct (BuildTree6_6.f2_blk _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K RFC6 LFC6 Hmc2 HK' PQH' R8 m1 m9 DL5 (arr_fill (ds_bl_count ds) 0 16 0) OL2 SL2
              HC8 ltac:(lia) C0_8 HX8 Rh1')
    as (R9 & m10 & Hms9 & HC9 & HR9 & C0_9 & Hfr9).
  replace (572 <? K) with false in Hms9, HR9 by (symmetry; apply Z.ltb_ge; lia).
  assert (Eh1 : arr_get HP' (K - 1) = arr_get HP5 1).
  { subst HP'. rewrite arr_get_set. unfold arr_inb. rewrite LHP6.
    replace ((K - 1 =? K - 1) && ((0 <=? K - 1) && (K - 1 <? 573))) with true
      by (symmetry; rewrite !Bool.andb_true_iff, Z.eqb_eq, Z.leb_le, Z.ltb_lt; lia). reflexivity. }
  rewrite Eh1 in HC9.
  set (DL' := arr_set DL5 (arr_get HP5 1) (wrap16 0)) in *. set (BC' := arr_fill (ds_bl_count ds) 0 16 0) in *.
  assert (GI0 : BuildTree6_6.GI F mem0 S p PBL ds sp t FC5 HP' DP5 mc2 K m1 m10 DL' BC' OL2 SL2).
  { split; [exact HC9|]. split.
    { intros i Hi. subst DL'. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range' 0); lia | apply RDL5; exact Hi]. }
    split; [subst DL'; rewrite arr_len_set; exact LDL6|]. split.
    { intros i Hi. subst BC'. rewrite arr_get_fill. unfold arr_inb. rewrite LBC0.
      replace ((0 <=? i) && (i <? 0 + Z.max 0 16) && ((0 <=? i) && (i <? 16))) with true
        by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
      lia. }
    split; [subst BC'; rewrite arr_len_fill; exact LBC0|]. split; [exact ROL2|]. split; [exact RSL2 | exact C0_9]. }
  destruct (BuildTree6_6.g_loop _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K RFC6 LFC6 Hmc2 HK' PQH' 573%nat K R9 m1 m10 DL' BC' OL2 SL2 0
              ltac:(lia) GI0 ltac:(lia) ltac:(lia) HOK1 HR9)
    as (R10 & m11 & DL7 & BC7 & OL7 & SL7 & ovf & E7 & Hms10 & GI7 & HR10 & Hovf & Hfr10).
  rewrite E7 in HS10. cbv beta iota in HS10. destruct HS10 as [HOK23 HLEN].
  assert (EGB0 : gen_bitlen (U FC5 DL5 HP' 1 (K - 1) DP5 (ds_bl_count ds) OL2 SL2 mc2) t
               = (if ovf =? 0 then U FC5 DL7 HP' 1 (K - 1) DP5 BC7 OL7 SL7 mc2
                  else gen_bitlen_loop3 (Z.to_nat ML) (gen_bitlen_loop2 573%nat (U FC5 DL7 HP' 1 (K - 1) DP5 BC7 OL7 SL7 mc2) ML ovf) t mc2 ML HEAP_SIZE)).
  { unfold gen_bitlen. rewrite !(bt_max_code ds t), !(bt_bl_count ds t), !(bt_set_bl_count ds t). change (MAX_BITS + 1) with 16.
    rewrite !(bt_heap_max ds t), !(bt_heap_get ds t). fold BC'. rewrite Eh1.
    rewrite !(bt_set_Len ds t), !(bt_heap_max ds t). replace (K - 1 + 1) with K by lia. fold DL'.
    rewrite E7. reflexivity. }
  pose proof GI7 as (HC11 & RDL7 & LDL7 & RBC7 & LBC7 & ROL7 & RSL7 & C0_11).
  destruct (BuildTree6_7.h1_setup _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K Hmc2 HK' R10 m1 m11 DL7 BC7 OL7 SL7 ovf GI7 ltac:(lia) HR10)
    as (R11 & Hms11 & HR11 & Hfr11).
  assert (HPH : exists R12 m12 DL8 BC8 OL8,
            gen_bitlen (U FC5 DL5 HP' 1 (K - 1) DP5 (ds_bl_count ds) OL2 SL2 mc2) t = U FC5 DL8 HP' 1 (K - 1) DP5 BC8 OL8 SL7 mc2
            /\ msteps s6_segs (mkst R11 (if ovf =? 0 then (0x1c074 : word) else (0x1bfa8 : word)) m11 s6_rom) (mkst R12 (0x1c074 : word) m12 s6_rom)
            /\ BuildTree6_6.GI F mem0 S p PBL ds sp t FC5 HP' DP5 mc2 K m1 m12 DL8 BC8 OL8 SL7
            /\ BuildTree6_8.GCREGS S sp t mc2 R12
            /\ (forall r : reg, reg_in r CLOBI = false -> getr R12 r = getr R11 r)).
  { rewrite EGB0. destruct (Z.eqb_spec ovf 0) as [Co|Co].
    - exists R11, m11, DL7, BC7, OL7. split; [reflexivity|]. split; [apply mst_refl|]. split; [exact GI7|].
      split; [| intros r _; reflexivity].
      destruct HR11 as (_ & _ & _ & _ & _ & _ & Q8 & _ & _ & Q19 & Q18 & Q2). unfold BuildTree6_8.GCREGS. repeat split; assumption.
    - specialize (HOK23 Co). destruct HOK23 as [HOK2 HOK3].
      destruct (BuildTree6_7.h1_loop _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K Hmc2 HK' 573%nat R11 m1 m11 DL7 BC7 OL7 SL7 ovf
                  ltac:(lia) GI7 ltac:(lia) HOK2 HR11)
        as (R12 & m12 & BC8 & E12 & Hms12 & GI12 & HR12 & Hfr12).
      rewrite E12 in HOK3 |- *.
      pose proof GI12 as (HC12 & _ & _ & RBC8 & LBC8 & _).
      destruct (BuildTree6_8.h2_entry _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K BC8 SL7 RFC6 LFC6 Hmc2 HK' R12 m1 m12 DL7 OL7 GI12 HR12)
        as (R13 & Hms13 & HR13 & Hfr13).
      destruct (BuildTree6_8.h2_loop _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K BC8 SL7 RFC6 LFC6 Hmc2 HK' (Z.to_nat ML) ML R13 m1 m12 DL7 OL7 573
                  ltac:(lia) GI12 ltac:(lia) ltac:(lia) HOK3 HR13)
        as (R14 & m14 & DL8 & OL8 & E14 & Hms14 & GI14 & HC14 & Hfr14).
      exists R14, m14, DL8, BC8, OL8. split; [exact E14|].
      split; [eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13 | exact Hms14]|].
      split; [exact GI14|]. split; [exact HC14|].
      intros r Hr. rewrite (Hfr14 r Hr), (Hfr13 r Hr). exact (Hfr12 r Hr). }
  clear HR11. destruct HPH as (R12 & m12 & DL8 & BC8 & OL8 & EGB & Hms12 & GI12 & HC12 & Hfr12).
  assert (HLEN' : forall i, 0 <= i <= mc2 -> 0 <= arr_get DL8 i <= 15).
  { intros i Hi. pose proof (HLEN i Hi) as X. rewrite EGB, bt_Len in X. exact X. }
  pose proof GI12 as (HCg & RDL8 & LDL8 & RBC8 & LBC8 & _).
  destruct (BuildTree6_9.i_phase _ _ _ _ _ _ _ _ _ _ HH DL8 HP' (K - 1) DP5 BC8 OL8 SL7 mc2 Hmc2 RBC8 RDL8 LDL8 HLEN' R12 m1 m12 FC5 HCg HC12)
    as (R15 & m15 & FC9 & E15 & Hms15 & HC15 & Q2 & Hfr15).
  destruct HC15 as (HB15 & HRC15 & HAG15 & MF15).
  destruct (epi_blk R15 regs m15 (FRM_keep m1 m15 regs HAG15 Hapart HFRM) MF15 P1 Q2)
    as (R16 & Hms16 & W2 & W1 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & Hfr16).
  exists R16, m15. split.
  { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
    eapply msteps_trans; [exact Hms3|]. eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5|].
    eapply msteps_trans; [exact Hms6|]. eapply msteps_trans; [exact Hms7|]. eapply msteps_trans; [exact Hms8|].
    eapply msteps_trans; [exact Hms9|]. eapply msteps_trans; [exact Hms10|]. eapply msteps_trans; [exact Hms11|].
    eapply msteps_trans; [exact Hms12|]. eapply msteps_trans; [exact Hms15 | exact Hms16]. }
  split.
  {
    replace (build_tree ds t) with (U FC9 DL8 HP' 1 (K - 1) DP5 BC8 OL8 SL7 mc2); [exact HB15|].
    symmetry. unfold build_tree. rewrite E0. unfold BuildTree6_1.X0. rewrite E1. cbv beta iota.
    rewrite E2. cbv beta iota. rewrite (bt_set_max_code ds t), !(bt_heap_len ds t), E4, E5.
    rewrite !(bt_heap_max ds t), !(bt_set_heap_max ds t), !(bt_heap_max ds t). unfold SMALLEST.
    rewrite !(bt_heap_get ds t), !(bt_heap_set ds t). fold HP'. rewrite EGB. exact E15. }
  split; [exact HRC15|].
  split; [rewrite W2, P2; reflexivity|].
  apply (frame_fix R16 regs 1%bv); [exact W1|].
  apply (frame_fix R16 regs 2%bv); [rewrite W2, P2; reflexivity|].
  apply (frame_fix R16 regs 8%bv); [exact W8|]. apply (frame_fix R16 regs 9%bv); [exact W9|].
  apply (frame_fix R16 regs 18%bv); [exact W18|]. apply (frame_fix R16 regs 19%bv); [exact W19|].
  apply (frame_fix R16 regs 20%bv); [exact W20|]. apply (frame_fix R16 regs 21%bv); [exact W21|].
  apply (frame_fix R16 regs 22%bv); [exact W22|]. apply (frame_fix R16 regs 23%bv); [exact W23|].
  apply (frame_fix R16 regs 24%bv); [exact W24|]. apply (frame_fix R16 regs 25%bv); [exact W25|].
  apply (frame_fix R16 regs 26%bv); [exact W26|]. apply (frame_fix R16 regs 27%bv); [exact W27|].
  intros r Hr.
  rewrite (Hfr16 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr15 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr12 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr11 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr10 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr9 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr8 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr7 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr6 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr5 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr4 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr3 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr1 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  apply Hfr0. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.

Goal True. idtac "build_tree_run OK". exact I. Qed.

End Walk.


Theorem build_tree_run6_ok : build_tree_run6 GenBitlenModel.bt_safe.
Proof.
  unfold build_tree_run6.
  intros F mem0 mem S p PBL ds ra sp t regs MEMSET HL HFS Hret HBR HRC HSAFE Hcf P10 P11 P2 P1.
  replace (zw A6_BUILD_TREE) with (0x1b94c%bv : word) by (apply bv_eq; vm_compute; reflexivity).
  exact (build_tree_run F mem0 mem S p PBL ds ra sp t
           {| bth_ret := Hret; bth_L := HL; bth_FS := HFS; bth_fr := Hcf; bth_br := HBR; bth_rod := HRC |}
           regs MEMSET HSAFE P10 P11 P2 P1).
Qed.
End FXG.

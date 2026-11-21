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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u TreesRod6u TreesApi6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import BuildTree6u_1 BuildTree6u_2 BuildTree6u_2c BuildTree6u_pq BuildTree6u_pq2 BuildTree6u_3 BuildTree6u_4 BuildTree6u_5 BuildTree6u_6 BuildTree6u_7 BuildTree6u_7b BuildTree6u_7c BuildTree6u_7d BuildTree6u_8 BuildTree6u_9 BuildTree6u_10.
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
Local Abbreviation SP := (sp - 208).
Local Abbreviation BRm := (BR6u F mem0 S p PBL).
Local Abbreviation U := (bt_upd ds t).
Local Abbreviation SDA := (SDA R6u).
Local Abbreviation STP := (STP R6u).
Local Abbreviation EXP := (EXP R6u).
Local Abbreviation NT := (2 ^ 64 - 1 - (S + toff t)).
Local Abbreviation NHP := (2 ^ 64 - 1 - (S + 3008)).
Local Abbreviation NDP := (2 ^ 64 - 1 - (S + 5308)).

Hypothesis HH : BTH F mem0 mem S p PBL ds ra sp.

Let Hret : ret_ok ra := bth_ret _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := bth_L _ _ _ _ _ _ _ _ _ HH.
Let HFS : sub_franges F S dsl_SIZE := bth_FS _ _ _ _ _ _ _ _ _ HH.
Let HS8 : S mod 8 = 0 := bth_al _ _ _ _ _ _ _ _ _ HH.
Let Hcf : call_frame F mem S PB PBL sp 272 := bth_fr _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := bth_br _ _ _ _ _ _ _ _ _ HH.
Let HRC0 : trees_rod_clear6u mem := bth_rod _ _ _ _ _ _ _ _ _ HH.
Let Hsp : 272 <= sp <= 2 ^ 63 := proj1 Hcf.
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.


Local Abbreviation GB := (BuildTree6u_1.GB S sp).
Local Abbreviation CI := (BuildTree6u_1.CI F mem0 S p PBL sp).
Local Abbreviation FRM := (BuildTree6u_1.FRM sp).
Local Abbreviation LOC := (BuildTree6u_1.LOC S sp t).
Local Abbreviation stree_dl := (BuildTree6u_1.stree_dl t).
Local Abbreviation stF := (BuildTree6u_1.stF t).
Local Abbreviation L1REGS := (BuildTree6u_1.L1REGS S sp t).
Local Abbreviation X0 := (BuildTree6u_1.X0 ds t).
Local Abbreviation L1 := (BuildTree6u_1.L1 t).
Local Abbreviation tsize_elems := (BuildTree6u_1.tsize_elems t).
Local Abbreviation elems_range := (BuildTree6u_1.elems_range t).
Local Abbreviation dsc_off_val := (BuildTree6u_1.dsc_off_val t).
Local Abbreviation toff_mod4 := (BuildTree6u_1.toff_mod4 t).
Local Abbreviation SDA_range := (BuildTree6u_1.SDA_range t).
Local Abbreviation STP_range := (BuildTree6u_1.STP_range t).
Local Abbreviation EXP_range := (BuildTree6u_1.EXP_range t).
Local Abbreviation LOC_keep := (BuildTree6u_1.LOC_keep F mem0 mem S p PBL ds ra sp t HH).


Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [BuildTree6u_1.stF].

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
      | H : cells sg m ?P 2 2%nat ?len (arr_get tt) |- _ =>
          eapply (u16_read_at sg m P len (arr_get tt) i a _ H); [lia | arr_range_auto | change (2 ^ 1) with 2; lia | reflexivity]
      | H : cells sg m ?P 1 1%nat ?len (arr_get tt) |- _ =>
          eapply (bytes_read_at sg m P len (arr_get tt) i a _ H); [lia | arr_range_auto | lia | reflexivity]
      end
  end.

Local Ltac zc :=
  change (2 ^ 3) with 8 in *;
  first [ lazymatch goal with
          | |- _ mod _ = 0 => keep_mod_facts; Z.to_euclidean_division_equations; lia
          end
        | zcond_close ].

Local Ltac side_closer :=
  try solve [ assumption
            | nf; vfix; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); rewrite ?Z.mod_small by lia; lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; symex_read_auto
            | nf; vfix; first [symex_read_auto | ag_read]
            | nf; vfix; symex_store_auto
            | nf; vfix; symex_sok_auto
            | nf; vfix; zc
            | intros; nf; first [apply pb_range | apply hv_range | apply wb_range | apply Z.mod_pos_bound; lia] ].

Local Ltac run_with C vb fuel dirs rds pins pv FC DL HP DP BC :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in vb in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs C fuel dirs rdv pinsv vbv NoRegions pv NoVals ((BuildTree6u_1.stF t) FC DL HP DP BC) F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
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
  replace (match t with TL => 180992 | TD => 181024 | TB => 181056 end) with (SDA t) in Csd by (destruct t; reflexivity);
  let Cst := fresh "Cst" in let Cex := fresh "Cex" in let Cbase := fresh "Cbase" in let Celems := fresh "Celems" in let Cml := fresh "Cml" in
  destruct (sdesc_cells R6u _ _ trod_ok6u HRC t) as (Cst & Cex & Cbase & Celems & Cml);
  clear Hsc Har;
  let Hsp' := fresh "Hsp'" in pose proof Hsp as Hsp';
  let HS8' := fresh "HS8'" in pose proof HS8 as HS8';
  let Htt' := fresh "Htt'" in pose proof Htt as Htt';
  let Htm := fresh "Htm" in pose proof toff_mod4 as Htm;
  let He := fresh "He" in pose proof elems_range as He;
  let Hte := fresh "Hte" in pose proof tsize_elems as Hte;
  let Hdo := fresh "Hdo" in let Hdo8 := fresh "Hdo8" in pose proof dsc_off_val as Hdo; destruct Hdo as [Hdo Hdo8];
  let Hsda := fresh "Hsda" in let Hsda8 := fresh "Hsda8" in pose proof SDA_range as Hsda; destruct Hsda as [Hsda Hsda8];
  let Hstp := fresh "Hstp" in pose proof STP_range as Hstp;
  let RODS := fresh "RODS" in
  pose proof (mapped_rod_apart R6u _ _ S 5968 trod_ok6u HRC MS ltac:(lia) ltac:(lia)) as RODS;
  let RODF := fresh "RODF" in
  pose proof (mapped_rod_apart R6u _ _ (SP - 64) 272 trod_ok6u HRC MF ltac:(lia) ltac:(lia)) as RODF;
  cbn [tr_lo tr_hi tr_sdesc R6u] in RODS, RODF;
  lazymatch thin with
  | true => clear RODS RODF HD Cst Cex Cbase Celems Cml Cdyn Csd Hsda Hsda8; try clear HPB'
  | false => idtac
  end.
Local Ltac open_ci HC := open_ci_gen false HC.
Local Ltac open_ciT HC := open_ci_gen true HC.

Local Ltac ag_tower HAG :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold BuildTree6u_1.GB;
              first [ apply sub_franges_here; unfold dsl_SIZE; cbn; lia
                    | apply sub_franges_later; apply sub_franges_here; cbn; lia
                    | apply sub_franges_later; apply sub_franges_later; apply sub_franges_here; cbn; lia
                    | apply sub_franges_later; apply sub_franges_later; apply sub_franges_later; apply sub_franges_here; cbn; lia ] ]);
  exact HAG.

Local Ltac rod_tower HRC MS MP MF :=
  apply (trees_rod_clear_wr R6u _ _ HRC);
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
        | let A := fresh "A" in
          lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf; vfix;
            first [ assumption
                  | lazymatch goal with |- ?a = ?a => reflexivity end
                  | f_equal; lia
                  | f_equal; repeat (rewrite (szwrap_small 32) by lia); rewrite ?Z.mod_small by lia; lia
                  | rewrite zw_u; assumption
                  | apply zw_not; lia
                  | rewrite zw_not by lia; f_equal; lia
                  | lazymatch goal with |- zw ?a = zw ?b => lazymatch isZcst a with true => lazymatch isZcst b with true =>
                      apply bv_eq; vm_compute; reflexivity end end end
                  | idtac ] end ].
Local Ltac regs_of HR Hfr := repeat split; reg1 HR Hfr.

Local Ltac ci_tower HB HRC HAG MS MP MF HFf M ks :=
  br_fwdT HB M ks ltac:(oth HFf);
  lazymatch goal with
  | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
      split; [ eapply BR_eqst; [exact HB2|]; clear HB2; st_eqT;
               try (first [reflexivity | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); lia])
             | split; [ rod_tower HRC MS MP MF
                      | split; [ ag_tower HAG
                               | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                                 repeat (apply wbytes_grows); apply MF; exact Hx ] ] ]
  end.

Local Ltac blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf ks tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [ ci_tower HB HRC HAG MS MP MF HFf M ks | tregs ]
  end.

Local Ltac dbg_left := idtac.

Local Ltac nf_in H :=
  let T := type of H in let T' := eval cbn [BuildTree6u_1.stF] in T in symex_recast H T'.


Definition stC11 : cfg := CFG FB6 [] [EVar 35%nat] [0x1ca38] [].
Definition VB11 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 64);
   (36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64);
   (42%nat, 2 ^ 64); (43%nat, 2 ^ 64); (44%nat, 2 ^ 64); (45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64)].
Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC11 VB11 fuel dirs rds pins pv FC DL HP DP BC.

Local Abbreviation ML := (sd_max_length t).
Local Abbreviation BASE := (sd_extra_base t).


Lemma epi_blk : forall regs (regs0 : bvmap 5 word) m,
  FRM m regs0 -> mapped m (SP - 64) 272 -> getr regs0 1 = ra -> getr regs 2 = zw SP ->
  exists R,
    msteps s6u_segs (mkst regs (0x1d3b8 : word) m s6u_rom) (mkst R ra m s6u_rom)
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
  all: try solve [intros; apply (BuildTree6u_6.extra_view_bound' S t)].
  all: dbg_left.
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ _ _) => exists R; split; [exact Hms|]; clear Hms
  end.
  repeat match goal with |- _ /\ _ => split end;
    try (let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; rewrite <- ?P1; rewrite ?zw_u; first [reflexivity | f_equal; lia] end).
  fr_weak Hfr.
Qed.

Goal True. idtac "epi_blk OK". exact I. Qed.


Theorem build_tree_run : forall regs,
  GenBitlenModel.bt_safe ds t ->
  getr regs 10 = zw S -> getr regs 11 = zw (S + dsc_off t) -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1ca38 : word) mem s6u_rom) (mkst R ra m' s6u_rom)
    /\ BRm m' (build_tree ds t)
    /\ trees_rod_clear6u m'
    /\ getr R 2 = getr regs 2
    /\ (forall r : reg, reg_in r BT_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs HSAFE P10 P11 P2 P1.
  pose proof elems_range as He. pose proof tsize_elems as Hte. pose proof Htt as Htt'. pose proof (BuildTree6u_6.ml_range t) as Hml.
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HBR0) as (_ & _ & HTL & _).
  pose proof (tree_lens_fc ds t HTL) as LFC0. pose proof (tree_lens_dl ds t HTL) as LDL0.
  pose proof HTL as (_ & _ & _ & _ & _ & _ & LBC0 & LHP0 & LDP0).
  unfold GenBitlenModel.bt_safe in HSAFE. cbv zeta in HSAFE.
  destruct HSAFE as (RFC0 & ROL0 & RSL0 & HS1).
  assert (E0 : set_heap_max (set_heap_len ds 0) HEAP_SIZE = X0).
  { unfold BuildTree6u_1.X0. rewrite <- (bt_upd_self ds t) at 1. rewrite bt_set_heap_len, bt_set_heap_max. reflexivity. }
  rewrite E0 in HS1. unfold BuildTree6u_1.X0 in HS1.
  destruct (BuildTree6u_1.pro_blk _ _ _ _ _ _ _ _ _ t HH regs P10 P11 P2 P1) as (R0 & m1 & Hms0 & HC0 & HR0 & HFRM & HLOC & Hfr0).
  destruct (BuildTree6u_1.l1_loop _ _ _ _ _ _ _ _ _ _ HH (tree_fc ds t) (ds_bl_count ds) 573 (ds_opt_len ds) (ds_static_len ds) (max_code ds t) RFC0
              (Z.to_nat E) 0 R0 m1 m1 (tree_dl ds t) (ds_heap ds) 0 (ds_depth ds) (-1)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(left; split; reflexivity) LDL0 LHP0 LDP0 HC0 HLOC HR0)
    as (R1 & m2 & DL1 & HP1 & HL1 & DP1 & mc1 & E1 & Hms1 & HC1 & HR1 & Hhl1 & LDL1 & LHP1 & LDP1 & Hinv1 & Hfr1).
  unfold BuildTree6u_1.L1 in E1. rewrite Z.sub_0_r in E1.
  rewrite E1 in HS1. cbv beta iota in HS1.
  destruct (BuildTree6u_2c.c_phase _ _ _ _ _ _ _ _ _ _ HH R1 m1 m2 DL1 HP1 HL1 DP1 mc1 HC1 HLOC Hhl1 Hinv1 RFC0 LFC0 LHP1 LDP1 ROL0 RSL0 HR1)
    as (R2 & m3 & FC2 & HP2 & HL2 & DP2 & OL2 & SL2 & mc2 & E2 & Hms2 & HC2 & HR2 & Hhl2 & Hmc2 & LFC2 & LHP2 & LDP2 & ROL2 & RSL2 & Hfr2).
  unfold BuildTree6u_2.L2 in E2. rewrite E2 in HS1. cbv beta iota zeta in HS1.
  rewrite (bt_set_max_code ds t) in HS1. rewrite !(bt_heap_len ds t) in HS1.
  destruct HS1 as (Hheap3 & Hdepth3 & Hfreq3 & HS4).
  assert (PQ2 : BuildTree6u_pq.PQ t HL2 HP2).
  { intros i Hi. pose proof (Hheap3 i Hi) as X. rewrite bt_heap_get in X. exact X. }
  assert (RDP2 : forall i, 0 <= i < 573 -> 0 <= arr_get DP2 i < 256).
  { intros i Hi. pose proof (Hdepth3 i Hi) as X. rewrite bt_depth_get in X. exact X. }
  assert (RFC2 : forall i, 0 <= i < tsize t -> 0 <= arr_get FC2 i < 65536).
  { intros i Hi. pose proof (Hfreq3 i Hi) as X. rewrite bt_Freq in X. exact X. }
  assert (Hhl2' : 2 <= HL2 <= 572) by lia. assert (Hmc2' : 0 <= mc2 < 600) by lia.
  destruct (BuildTree6u_3.d_pro _ _ _ _ _ _ _ _ _ _ HH FC2 DL1 HL2 573 DP2 (ds_bl_count ds) OL2 SL2 mc2 RFC2 Hhl2' LFC2 Hmc2'
              R2 m1 m3 HP2 (max_code ds t) regs HC2 HLOC HFRM PQ2 LHP2 HR2)
    as (R3 & m4 & Hms3 & HD3 & HLOC4 & HFRM4 & C8_4 & HO3 & Hfr3).
  assert (Hdiv : 1 <= HL2 / 2 /\ HL2 / 2 * 2 <= HL2) by (pose proof (Z.div_mod HL2 2 ltac:(lia)); pose proof (Z.mod_pos_bound HL2 2 ltac:(lia)); lia).
  destruct (BuildTree6u_3.d_loop _ _ _ _ _ _ _ _ _ _ HH FC2 DL1 HL2 573 DP2 (ds_bl_count ds) OL2 SL2 mc2 RFC2 RDP2 Hhl2' LFC2 LDP2
              (Z.to_nat (HL2 / 2)) (HL2 / 2) R3 m4 m4 HP2 ltac:(lia) HD3 HO3 ltac:(lia) ltac:(lia))
    as (R4 & m5 & HP4 & E4 & Hms4 & HD4 & HO4 & Hfr4).
  unfold BuildTree6u_3.L3 in E4. rewrite E4 in HS4.
  destruct HD4 as (HC4 & PQ4 & LHP4).
  destruct (BuildTree6u_4.e0_blk _ _ _ _ _ _ _ _ _ _ HH (ds_bl_count ds) OL2 SL2 mc2 R4 m4 m5 FC2 DL1 HP4 HL2 573 DP2 regs
              HC4 HLOC4 C8_4 HFRM4 (conj PQ4 LHP4) (conj RFC2 (conj RDP2 (conj LFC2 LDP2))) LDL1 Hhl2' HO4)
    as (R5 & m6 & Hms5 & HE5 & HLOC6 & HFRM6 & HR5 & Hfr5).
  destruct (BuildTree6u_5.e_loop _ _ _ _ _ _ _ _ _ _ HH (ds_bl_count ds) OL2 SL2 mc2 573%nat R5 m6 m6 FC2 DL1 HP4 HL2 573 DP2 E
              HE5 HLOC6 HR5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (R6 & m7 & FC5 & DL5 & HP5 & K & DP5 & E5 & Hms6 & HE6 & HF6 & HK & Hfr6).
  rewrite E5 in HS4.
  rewrite !(bt_heap_max ds t), !(bt_set_heap_max ds t), !(bt_heap_max ds t) in HS4. unfold SMALLEST in HS4.
  rewrite !(bt_heap_get ds t), !(bt_heap_set ds t) in HS4.
  destruct HE6 as (HC6 & (PQ6 & LHP6) & (RFC6 & RDP6 & LFC6 & LDP6) & LDL6).
  assert (Rh1 : 0 <= arr_get HP5 1 < tsize t) by (apply PQ6; lia).
  rewrite !(bt_heap_max ds t) in HS4.
  destruct HS4 as (PQH & RDL5 & HSg).
  rewrite !(bt_tree_dl ds t) in RDL5.
  rewrite !(bt_bl_count ds t), !(bt_set_bl_count ds t) in HSg. change (MAX_BITS + 1) with 16 in HSg.
  rewrite !(bt_heap_max ds t), !(bt_heap_get ds t) in HSg.
  rewrite (arr_get_set HP5 (K - 1) (K - 1)) in HSg. unfold arr_inb in HSg. rewrite LHP6 in HSg.
  replace ((K - 1 =? K - 1) && ((0 <=? K - 1) && (K - 1 <? 573))) with true in HSg
    by (symmetry; rewrite !Bool.andb_true_iff, Z.eqb_eq, Z.leb_le, Z.ltb_lt; lia).
  rewrite !(bt_set_Len ds t) in HSg. rewrite !(bt_heap_max ds t) in HSg. replace (K - 1 + 1) with K in HSg by lia.
  destruct HSg as (HOK1 & HS10).
  assert (HK' : 2 <= K <= 571) by lia. assert (HK'' : 1 <= K <= 573) by lia.
  assert (PQH' : forall h, K <= h < 573 -> 0 <= arr_get (arr_set HP5 (K - 1) (arr_get HP5 1)) h < tsize t).
  { intros h Hh. pose proof (PQH h ltac:(unfold HEAP_SIZE, L_CODES, LITERALS, LENGTH_CODES; lia)) as X. rewrite bt_heap_get in X. exact X. }
  set (HP' := arr_set HP5 (K - 1) (arr_get HP5 1)) in *.
  destruct (BuildTree6u_6.f1_blk _ _ _ _ _ _ _ _ _ _ HH FC5 DP5 mc2 K (ds_bl_count ds) OL2 SL2 RFC6 LFC6 Hmc2 HK' R6 m6 m7 DL5 HP5
              HC6 HLOC6 ltac:(lia) LHP6 HF6)
    as (R7 & m8 & Hms7 & HC7 & HX7 & Hfr7).
  fold HP' in HC7.
  destruct (BuildTree6u_6.f2_fill _ _ _ _ _ _ _ _ _ _ HH FC5 DP5 mc2 K (ds_bl_count ds) OL2 SL2 RFC6 LFC6 Hmc2 HK' R7 m6 m8 DL5 HP'
              HC7 LBC0 HX7)
    as (R8 & m9 & Hms8 & HC8 & HX8 & Hfr8).
  assert (LHP' : arr_len HP' = 573) by (subst HP'; rewrite arr_len_set; exact LHP6).
  assert (Eh1 : arr_get HP' (K - 1) = arr_get HP5 1).
  { subst HP'. rewrite arr_get_set. unfold arr_inb. rewrite LHP6.
    replace ((K - 1 =? K - 1) && ((0 <=? K - 1) && (K - 1 <? 573))) with true
      by (symmetry; rewrite !Bool.andb_true_iff, Z.eqb_eq, Z.leb_le, Z.ltb_lt; lia). reflexivity. }
  destruct (BuildTree6u_6.f3_blk _ _ _ _ _ _ _ _ _ _ HH FC5 DP5 mc2 K OL2 SL2 RFC6 LFC6 Hmc2 HK' R8 m6 m9 DL5 HP' (arr_fill (ds_bl_count ds) 0 16 0)
              HC8 HLOC6 LHP' RDL5 LDL6 HX8 ltac:(rewrite Eh1; exact Rh1))
    as (R9 & m10 & Hms9 & HC9 & HR9 & Hfr9).
  rewrite Eh1 in HC9.
  set (DL' := arr_set DL5 (arr_get HP5 1) (wrap16 0)) in *. set (BC' := arr_fill (ds_bl_count ds) 0 16 0) in *.
  assert (GI0 : BuildTree6u_7.GI F mem0 S p PBL ds sp t FC5 HP' DP5 mc2 K m6 m10 DL' BC' OL2 SL2).
  { split; [exact HC9|]. split.
    { intros i Hi. subst DL'. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range' 0); lia | apply RDL5; exact Hi]. }
    split; [subst DL'; rewrite arr_len_set; exact LDL6|]. split.
    { intros i Hi. subst BC'. rewrite arr_get_fill. unfold arr_inb. rewrite LBC0.
      replace ((0 <=? i) && (i <? 0 + Z.max 0 16) && ((0 <=? i) && (i <? 16))) with true
        by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
      lia. }
    split; [subst BC'; rewrite arr_len_fill; exact LBC0|]. split; [exact ROL2 | exact RSL2]. }
  destruct (BuildTree6u_7d.g_loop _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K RFC6 LFC6 Hmc2 HK'' PQH' 573%nat K R9 m6 m10 DL' BC' OL2 SL2 0
              ltac:(lia) GI0 HLOC6 ltac:(lia) ltac:(lia) HOK1 HR9)
    as (R10 & m11 & DL7 & BC7 & OL7 & SL7 & ovf & E7 & Hms10 & GI7 & HR10 & Hovf & Hfr10).
  rewrite E7 in HS10. cbv beta iota in HS10. destruct HS10 as [HOK23 HLEN].
  assert (EGB0 : gen_bitlen (U FC5 DL5 HP' 1 (K - 1) DP5 (ds_bl_count ds) OL2 SL2 mc2) t
               = (if ovf =? 0 then U FC5 DL7 HP' 1 (K - 1) DP5 BC7 OL7 SL7 mc2
                  else gen_bitlen_loop3 (Z.to_nat ML) (gen_bitlen_loop2 573%nat (U FC5 DL7 HP' 1 (K - 1) DP5 BC7 OL7 SL7 mc2) ML ovf) t mc2 ML HEAP_SIZE)).
  { unfold gen_bitlen. rewrite !(bt_max_code ds t), !(bt_bl_count ds t), !(bt_set_bl_count ds t). change (MAX_BITS + 1) with 16.
    rewrite !(bt_heap_max ds t), !(bt_heap_get ds t). fold BC'. rewrite Eh1.
    rewrite !(bt_set_Len ds t), !(bt_heap_max ds t). replace (K - 1 + 1) with K by lia. fold DL'.
    rewrite E7. reflexivity. }
  destruct (BuildTree6u_8.h1_setup _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K Hmc2 HK'' R10 m6 m11 DL7 BC7 OL7 SL7 ovf GI7 ltac:(lia) HR10)
    as (R11 & Hms11 & HR11 & Hfr11).
  assert (HPH : exists R12 m12 DL8 BC8 OL8,
            gen_bitlen (U FC5 DL5 HP' 1 (K - 1) DP5 (ds_bl_count ds) OL2 SL2 mc2) t = U FC5 DL8 HP' 1 (K - 1) DP5 BC8 OL8 SL7 mc2
            /\ msteps s6u_segs (mkst R11 (if ovf =? 0 then (0x1d23c : word) else (0x1d12c : word)) m11 s6u_rom) (mkst R12 (0x1d23c : word) m12 s6u_rom)
            /\ BuildTree6u_7.GI F mem0 S p PBL ds sp t FC5 HP' DP5 mc2 K m6 m12 DL8 BC8 OL8 SL7
            /\ BuildTree6u_8.GCR S sp t R12
            /\ (forall r : reg, reg_in r CLOBI = false -> getr R12 r = getr R11 r)).
  { rewrite EGB0. destruct (Z.eqb_spec ovf 0) as [Co|Co].
    - exists R11, m11, DL7, BC7, OL7. split; [reflexivity|]. split; [apply mst_refl|]. split; [exact GI7|].
      split; [exact HR11 | intros r _; reflexivity].
    - specialize (HOK23 Co). destruct HOK23 as [HOK2 HOK3].
      destruct (BuildTree6u_8.h1_loop _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K Hmc2 HK'' 573%nat R11 m6 m11 DL7 BC7 OL7 SL7 ovf
                  ltac:(lia) GI7 ltac:(lia) HOK2 HR11)
        as (R12 & m12 & BC8 & E12 & Hms12 & GI12 & HR12 & Hfr12).
      rewrite E12 in HOK3 |- *.
      destruct (BuildTree6u_9.h2_entry _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K BC8 Hmc2 HK'' R12 m12 HR12)
        as (R13 & Hms13 & HR13 & Hfr13).
      destruct (BuildTree6u_9.h2_loop _ _ _ _ _ _ _ _ _ _ HH FC5 HP' DP5 mc2 K BC8 SL7 RFC6 LFC6 Hmc2 HK'' (Z.to_nat ML) ML R13 m6 m12 DL7 OL7 573
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
  destruct (BuildTree6u_10.i_phase _ _ _ _ _ _ _ _ _ _ HH DL8 HP' (K - 1) DP5 BC8 OL8 SL7 mc2 Hmc2 RBC8 RDL8 LDL8 HLEN' R12 m6 m12 FC5 HCg HLOC6 HC12)
    as (R15 & m15 & FC9 & E15 & Hms15 & HC15 & Q2 & Hfr15).
  destruct HC15 as (HB15 & HRC15 & HAG15 & MF15).
  destruct (epi_blk R15 regs m15 (BuildTree6u_4.FRM_keep _ _ _ _ _ _ _ _ _ HH m6 m15 regs HAG15 HFRM6) MF15 P1 Q2)
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
    symmetry. unfold build_tree. rewrite E0. unfold BuildTree6u_1.X0. rewrite E1. cbv beta iota.
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


Theorem build_tree_run6u_ok : build_tree_run6u GenBitlenModel.bt_safe.
Proof.
  unfold build_tree_run6u.
  intros F mem0 mem S p PBL ds ra sp t regs HL HFS Hret HS8 HBR HRC HSAFE Hcf P10 P11 P2 P1.
  replace (zw A6U_BUILD_TREE) with (0x1ca38%bv : word) by (apply bv_eq; vm_compute; reflexivity).
  exact (build_tree_run F mem0 mem S p PBL ds ra sp t
           {| bth_ret := Hret; bth_L := HL; bth_FS := HFS; bth_al := HS8; bth_fr := Hcf; bth_br := HBR; bth_rod := HRC |}
           regs HSAFE P10 P11 P2 P1).
Qed.
End FXG.

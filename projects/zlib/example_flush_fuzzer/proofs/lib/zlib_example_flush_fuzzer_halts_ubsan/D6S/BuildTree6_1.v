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
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Record BTH (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
       (ds : deflate_state) (ra : word) (sp : Z) : Prop := {
  bth_ret : ret_ok ra;
  bth_L : BRH F S p PBL;
  bth_FS : sub_franges F S dsl_SIZE;
  bth_fr : call_frame F mem S (p_pending_buf p) PBL sp 144;
  bth_br : BR6 F mem0 S p PBL mem ds;
  bth_rod : trees_rod_clear6 mem }.

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


Lemma tsize_elems : tsize t = 2 * E + 1.
Proof. destruct t; reflexivity. Qed.
Lemma elems_range : 19 <= E <= 286.
Proof. destruct t; cbn; unfold L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES; lia. Qed.
Lemma dsc_off_val : 2904 <= dsc_off t <= 2952.
Proof. destruct t; cbn; lia. Qed.
Lemma SDA_range : 0x292e0 <= SDA t <= 0x29320.
Proof. destruct t; cbn; unfold A_static_l_desc, A_static_d_desc, A_static_bl_desc; cbn; lia. Qed.
Lemma STP_range : 0 <= STP t < 2 ^ 32.
Proof. destruct t; cbn; lia. Qed.
Lemma EXP_range : 0x122d8 <= EXP t <= 0x123c4.
Proof. destruct t; cbn; lia. Qed.

Definition GB : franges := [(S, dsl_SIZE); (SP, 8); (SP + 8, 32)].

Definition CI (m1 m : word -> option byte) (X : deflate_state) : Prop :=
  BRm m X /\ trees_rod_clear6 m /\ agree_out GB m1 m /\ mapped m SP 144.

Definition FRM (m : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  cell s6_segs m (SP + 136) 8 (bv_unsigned (getr regs0 1))
  /\ cell s6_segs m (SP + 128) 8 (bv_unsigned (getr regs0 8))
  /\ cell s6_segs m (SP + 120) 8 (bv_unsigned (getr regs0 9))
  /\ cell s6_segs m (SP + 112) 8 (bv_unsigned (getr regs0 18))
  /\ cell s6_segs m (SP + 104) 8 (bv_unsigned (getr regs0 19))
  /\ cell s6_segs m (SP + 96) 8 (bv_unsigned (getr regs0 20))
  /\ cell s6_segs m (SP + 88) 8 (bv_unsigned (getr regs0 21))
  /\ cell s6_segs m (SP + 80) 8 (bv_unsigned (getr regs0 22))
  /\ cell s6_segs m (SP + 72) 8 (bv_unsigned (getr regs0 23))
  /\ cell s6_segs m (SP + 64) 8 (bv_unsigned (getr regs0 24))
  /\ cell s6_segs m (SP + 56) 8 (bv_unsigned (getr regs0 25))
  /\ cell s6_segs m (SP + 48) 8 (bv_unsigned (getr regs0 26))
  /\ cell s6_segs m (SP + 40) 8 (bv_unsigned (getr regs0 27)).

Definition CLOBI : list reg := [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.


Definition stree_dl : arr := match t with TL => static_ltree_dl | TD => static_dtree_dl | TB => arr_make 1 0 end.

Definition stF (FC DL HP DP BC : arr) (f : nat) (x : Z) : Z :=
  match f with
  | 0%nat => pb FC x | 1%nat => pb DL x | 2%nat => hv HP x | 3%nat => wb DP x | 4%nat => pb BC x
  | 5%nat => arr_get (sd_extra_bits t) x mod 2 ^ 32 | _ => pb stree_dl x
  end.

Definition FB : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 2 ^ 32); (6%nat, 65536)].

Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300);
   (36%nat, 600); (37%nat, 600); (38%nat, 600); (39%nat, 600); (40%nat, 600); (41%nat, 600);
   (42%nat, 65536); (43%nat, 65536); (44%nat, 65536); (45%nat, 65536);
   (46%nat, 2 ^ 64); (47%nat, 2 ^ 64); (48%nat, 2 ^ 63); (49%nat, 2 ^ 32); (50%nat, 2 ^ 63); (51%nat, 3000)].

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [stF].

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
    symex s6_segs C fuel dirs rdv pinsv vbv NoRegions pv NoVals (stF FC DL HP DP BC) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Local Ltac open_ci HC :=
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
  cbn [tr_lo tr_hi tr_sdesc R6] in RODS, RODF.

Local Ltac ag_tower HAG :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold GB;
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
            first [reflexivity | f_equal; lia | f_equal; f_equal; lia | f_equal; repeat (rewrite (szwrap_small 32) by lia); lia] end ].
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

Definition stC1 : cfg := CFG FB [] [EVar 1%nat] [0x1b9ec; 0x1ba24] [].
Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC1 VB fuel dirs rds pins pv FC DL HP DP BC.


Definition L1REGS (R : bvmap 5 word) (n mc : Z) : Prop :=
  getr R 9 = zw S /\ getr R 18 = zw T /\ getr R 20 = zw (S + 5300) /\ getr R 21 = zw (S + 2047)
  /\ getr R 10 = zw E /\ getr R 11 = zw (S + dsc_off t) /\ getr R 12 = zw (STP t)
  /\ getr R 2 = zw SP /\ getr R 14 = zw n /\ getr R 15 = zw (S + 3008)
  /\ getr R 16 = zw (S + 5308 + n) /\ getr R 17 = zw (T + 4 * n + 2) /\ getr R 5 = zw (T + 4 * E + 2)
  /\ getr R 19 = zw mc /\ getr R 13 = zw 4096.

Definition L1P : list (Z * expr) :=
  [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (21, EAdd (EVar 32) (ELit 2047));
   (10, EVar 35); (2, EVar 34); (14, EVar 36); (15, EAdd (EVar 32) (ELit 3008));
   (16, EAdd (EAdd (EVar 32) (ELit 5308)) (EVar 36)); (17, EAdd (EAdd (EVar 33) (EShl (EVar 36) 2)) (ELit 2));
   (5, EAdd (EAdd (EVar 33) (EShl (EVar 35) 2)) (ELit 2)); (13, ELit 4096)].

Definition X0 : deflate_state :=
  U (tree_fc ds t) (tree_dl ds t) (ds_heap ds) 0 573 (ds_depth ds) (ds_bl_count ds) (ds_opt_len ds) (ds_static_len ds) (max_code ds t).

Lemma pro_blk : forall regs,
  getr regs 10 = zw S -> getr regs 11 = zw (S + dsc_off t) -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m1,
    msteps s6_segs (mkst regs (0x1b94c : word) mem s6_rom) (mkst R (0x1b9ec : word) m1 s6_rom)
    /\ CI m1 m1 X0
    /\ L1REGS R 0 (-1)
    /\ FRM m1 regs
    /\ mapped m1 SP 144
    /\ (forall r : reg, reg_in r [2; 5; 9; 10; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P11 P2 P1.
  pose proof (BRT_start s6_segs 168672 168704 168736 F mem0 S p PBL ds t mem HBR0) as HB0.
  pose proof Hcf as (_ & HFf & Hmf & HfS & HfP). unfold dsl_SIZE in HfS.
  assert (HC : CI mem mem (U (tree_fc ds t) (tree_dl ds t) (ds_heap ds) (ds_heap_len ds) (ds_heap_max ds) (ds_depth ds)
                            (ds_bl_count ds) (ds_opt_len ds) (ds_static_len ds) (max_code ds t))).
  { split; [exact HB0|]. split; [exact HRC0|]. split; [apply agree_out_refl | exact Hmf]. }
  clear HB0. open_ci HC.
  assert (P2' : getr regs 2 = zw (SP + 144)) by (rewrite P2; f_equal; lia).
  run 60%nat [false]
      [RVal (EVar 33); RVal (EVar 48); RVal (EVar 49); RVal (EVar 35)]
      [(10, EVar 32); (11, EAdd (EVar 32) (EVar 51)); (2, EAdd (EVar 34) (ELit 144))]
      [S; T; SP; E; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; SDA t; STP t; 0; dsc_off t]
      (tree_fc ds t) (tree_dl ds t) (ds_heap ds) (ds_depth ds) (ds_bl_count ds).
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwdT HB M
        [KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther;
         KHl; KHm] ltac:(oth HFf);
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M _ |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [exact HB2 | split; [rod_tower HRC MS MP MF | split; [apply agree_out_refl|]]] |]
      end
  end.
  { repeat (apply mapped_wbytes). exact Hmf. }
  split; [unfold L1REGS; regs_of HR Hfr|].
  split; [unfold FRM; repeat split; frame_cells|].
  split; [repeat (apply mapped_wbytes); exact Hmf|].
  fr_weak Hfr.
Qed.


Section Loop1.
Variables (FC BC : arr) (HM OL SL MC : Z).
Local Abbreviation V DL HP HL DP := (U FC DL HP HL HM DP BC OL SL MC).

Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.

Lemma l1_step : forall regs m1 m DL HP HL DP n mc,
  CI m1 m (V DL HP HL DP) -> 0 <= n < E -> 0 <= HL <= n ->
  arr_len DL = tsize t -> arr_len HP = 573 -> arr_len DP = 573 ->
  L1REGS regs n mc ->
  exists R m',
    msteps s6_segs (mkst regs (0x1b9ec : word) m s6_rom)
           (mkst R (if n + 1 =? E then (0x1ba24 : word) else (0x1b9ec : word)) m' s6_rom)
    /\ CI m1 m' (if negb (arr_get FC n =? 0)
                 then V DL (arr_set HP (HL + 1) n) (HL + 1) (arr_set DP n (wrap8 0))
                 else V (arr_set DL n (wrap16 0)) HP HL DP)
    /\ L1REGS R (n + 1) (if negb (arr_get FC n =? 0) then n else mc)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL HP HL DP n mc HC Hn Hhl LDL LHP LDP HR0.
  open_ci HC.
  destruct HR0 as (P9 & P18 & P20 & P21 & P10 & P11 & P12 & P2 & P14 & P15 & P16 & P17 & P5 & P19 & P13).
  pose proof Hcf as (_ & HFf & _).
  pose proof (RFC n ltac:(rewrite tsize_elems; lia)) as Rn.
  assert (Efc : pb FC n = arr_get FC n) by (unfold pb; apply Z.mod_small; exact Rn).
  destruct (Z.eqb_spec (arr_get FC n) 0) as [CZ|CZ]; destruct (Z.eqb_spec (n + 1) E) as [CE|CE]; cbn [negb].
  - run 40%nat [true; true] [RVal (EApp1 0 (EVar 36))] L1P
        [S; T; SP; E; n; HL; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; STP t; 0; dsc_off t] FC DL HP DP BC.
    blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KDl n] ltac:(split; [unfold L1REGS; regs_of HR Hfr | fr_weak Hfr]).
  - run 40%nat [true; false] [RVal (EApp1 0 (EVar 36))] L1P
        [S; T; SP; E; n; HL; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; STP t; 0; dsc_off t] FC DL HP DP BC.
    blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KDl n] ltac:(split; [unfold L1REGS; regs_of HR Hfr | fr_weak Hfr]).
  - run 40%nat [false; false] [RVal (EApp1 0 (EVar 36)); RVal (EVar 37)] L1P
        [S; T; SP; E; n; HL; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; STP t; 0; dsc_off t] FC DL HP DP BC.
    blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KHl; KHeap (HL + 1); KDepth n]
      ltac:(split; [unfold L1REGS; regs_of HR Hfr | fr_weak Hfr]).
  - run 40%nat [false; true] [RVal (EApp1 0 (EVar 36)); RVal (EVar 37)] L1P
        [S; T; SP; E; n; HL; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; STP t; 0; dsc_off t] FC DL HP DP BC.
    blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KHl; KHeap (HL + 1); KDepth n]
      ltac:(split; [unfold L1REGS; regs_of HR Hfr | fr_weak Hfr]).
Qed.

Definition L1 (X : deflate_state) (n mc : Z) : deflate_state * Z :=
  build_tree_loop1 (Z.to_nat (E - n)) X t E n mc.

Lemma L1_step : forall DL HP HL DP n mc, 0 <= n < E ->
  L1 (V DL HP HL DP) n mc =
    if negb (arr_get FC n =? 0)
    then L1 (V DL (arr_set HP (HL + 1) n) (HL + 1) (arr_set DP n (wrap8 0))) (n + 1) n
    else L1 (V (arr_set DL n (wrap16 0)) HP HL DP) (n + 1) mc.
Proof.
  intros DL HP HL DP n mc Hn. unfold L1.
  replace (Z.to_nat (E - n)) with (Datatypes.S (Z.to_nat (E - (n + 1)))) by lia.
  cbn [build_tree_loop1]. replace (n <? E) with true by (symmetry; apply Z.ltb_lt; lia).
  autorewrite with btupd. reflexivity.
Qed.

Lemma L1_end : forall X mc, L1 X E mc = (X, mc).
Proof. intros. unfold L1. replace (Z.to_nat (E - E)) with 0%nat by lia. reflexivity. Qed.

Lemma l1_loop : forall k n regs m1 m DL HP HL DP mc,
  E - n <= Z.of_nat k -> 0 <= n < E -> 0 <= HL <= n ->
  (mc = -1 /\ HL = 0 \/ 0 <= mc < n /\ 1 <= HL) ->
  arr_len DL = tsize t -> arr_len HP = 573 -> arr_len DP = 573 ->
  CI m1 m (V DL HP HL DP) -> L1REGS regs n mc ->
  exists R m' DL' HP' HL' DP' mc',
    L1 (V DL HP HL DP) n mc = (V DL' HP' HL' DP', mc')
    /\ msteps s6_segs (mkst regs (0x1b9ec : word) m s6_rom) (mkst R (0x1ba24 : word) m' s6_rom)
    /\ CI m1 m' (V DL' HP' HL' DP')
    /\ L1REGS R E mc'
    /\ 0 <= HL' <= E /\ arr_len DL' = tsize t /\ arr_len HP' = 573 /\ arr_len DP' = 573
    /\ (mc' = -1 /\ HL' = 0 \/ 0 <= mc' < E /\ 1 <= HL')
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction k as [|k IH]; intros n regs m1 m DL HP HL DP mc Hk Hn Hhl Hinv LDL LHP LDP HC HR0; [lia|].
  pose proof tsize_elems as Hte.
  destruct (l1_step regs m1 m DL HP HL DP n mc HC Hn Hhl LDL LHP LDP HR0) as (R1 & m2 & Hms1 & HC1 & HR1 & Hfr1).
  rewrite L1_step by lia.
  destruct (Z.eqb_spec (arr_get FC n) 0) as [CZ|CZ]; cbn [negb] in *;
    destruct (Z.eqb_spec (n + 1) E) as [CE|CE].
  -
    rewrite CE, L1_end. rewrite CE in HR1.
    exists R1, m2, (arr_set DL n (wrap16 0)), HP, HL, DP, mc.
    split; [reflexivity|]. split; [exact Hms1|]. split; [exact HC1|]. split; [exact HR1|].
    rewrite arr_len_set. repeat (split; [lia|]). exact Hfr1.
  - destruct (IH (n + 1) R1 m1 m2 (arr_set DL n (wrap16 0)) HP HL DP mc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(rewrite arr_len_set; exact LDL) LHP LDP HC1 HR1)
      as (R2 & m3 & DL' & HP' & HL' & DP' & mc' & E2 & Hms2 & HC2 & HR2 & B1 & B2 & B3 & B4 & B5 & Hfr2).
    exists R2, m3, DL', HP', HL', DP', mc'. split; [exact E2|].
    split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HC2|]. split; [exact HR2|].
    repeat (split; [assumption|]).
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
  - rewrite CE, L1_end. rewrite CE in HR1.
    exists R1, m2, DL, (arr_set HP (HL + 1) n), (HL + 1), (arr_set DP n (wrap8 0)), n.
    split; [reflexivity|]. split; [exact Hms1|]. split; [exact HC1|]. split; [exact HR1|].
    rewrite !arr_len_set. repeat (split; [lia|]). exact Hfr1.
  - destruct (IH (n + 1) R1 m1 m2 DL (arr_set HP (HL + 1) n) (HL + 1) (arr_set DP n (wrap8 0)) n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                 LDL ltac:(rewrite arr_len_set; exact LHP) ltac:(rewrite arr_len_set; exact LDP) HC1 HR1)
      as (R2 & m3 & DL' & HP' & HL' & DP' & mc' & E2 & Hms2 & HC2 & HR2 & B1 & B2 & B3 & B4 & B5 & Hfr2).
    exists R2, m3, DL', HP', HL', DP', mc'. split; [exact E2|].
    split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HC2|]. split; [exact HR2|].
    repeat (split; [assumption|]).
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.
End Loop1.

End Walk.
End FXG.

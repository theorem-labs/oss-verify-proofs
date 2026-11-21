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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import BuildTree6u_1 BuildTree6u_2 BuildTree6u_3 BuildTree6u_pq BuildTree6u_pq2 BuildTree6u_4.
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
            | nf; vfix; symex_read_auto
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


Definition stC5 : cfg :=
  CFG FB [] [EVar 1%nat] [0x1cc40; 0x1de0c; 0x1cdcc]
      [AV (EAdd (EVar 32) (EShl (EVar 37) 2)) 3008 4 2 (EVar 37);
       AV (EAdd (EVar 32) (EShl (EVar 38) 2)) 3008 4 2 (EVar 38);
       AV (EAdd (EVar 33) (EShl (EVar 39) 2)) 0 2 0 (EVar 39);
       AV (EAdd (EVar 33) (EShl (EVar 40) 2)) 0 2 0 (EVar 40);
       AV (EAdd (EVar 33) (EShl (EApp1 2 (ELit 1)) 2)) 0 2 0 (EApp1 2 (ELit 1));
       AV (EAdd (EVar 32) (EVar 39)) 5308 1 3 (EVar 39);
       AV (EAdd (EVar 32) (EVar 40)) 5308 1 3 (EVar 40);
       AV (EAdd (EVar 32) (EApp1 2 (ELit 1))) 5308 1 3 (EApp1 2 (ELit 1));
       AV (EAdd (EVar 32) (EVar 36)) 5308 1 3 (EVar 36)].
Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC5 VB4 fuel dirs rds pins pv FC DL HP DP BC.

Lemma wrap16_sx_add : forall a b, wrap16 (szwrap 16 a + szwrap 16 b) = wrap16 (a + b).
Proof.
  intros a b. rewrite !wrap16_mod.
  rewrite Z.add_mod, !szwrap_eqm, <- Z.add_mod by lia. reflexivity.
Qed.

Section PhaseE.
Variables (BC : arr) (OL SL MC : Z).
Local Abbreviation W6 FC DL HP HL HM DP := (U FC DL HP HL HM DP BC OL SL MC).
Hypothesis Hmc : 0 <= MC < 600.

Local Abbreviation EB := (BuildTree6u_4.EB S sp t).
Local Abbreviation EREGS := (BuildTree6u_4.EREGS S sp t).
Local Abbreviation X2REGS := (BuildTree6u_4.X2REGS S sp t).
Local Abbreviation FREGS := (BuildTree6u_4.FREGS S sp t).
Local Abbreviation RNG := (BuildTree6u_4.RNG t).
Local Abbreviation PQ4 := (BuildTree6u_4.PQ4 t).
Local Abbreviation EI := (BuildTree6u_4.EI F mem0 S p PBL ds sp t BC OL SL MC).
Local Abbreviation LOC2 := (BuildTree6u_4.LOC2 S sp t MC).
Local Abbreviation LOC2_keep := (BuildTree6u_4.LOC2_keep F mem0 mem S p PBL ds ra sp t HH MC).
Local Abbreviation e_remove := (BuildTree6u_4.e_remove F mem0 mem S p PBL ds ra sp t HH BC OL SL MC).
Local Abbreviation pq_flat := (BuildTree6u_4.pq_flat ds t BC OL SL MC).

Definition Q3REGS (R : bvmap 5 word) (node : Z) : Prop :=
  EB R /\ getr R 8 = zw (T + node * 4) /\ getr R 21 = zw (T + node * 4) /\ getr R 20 = zw node /\ getr R 26 = zw (node + 1)
  /\ getr R 10 = zw S /\ getr R 11 = zw T /\ getr R 12 = zw 1 /\ getr R 1 = zw 0x1cdb4.
Definition L3REGS (R : bvmap 5 word) (node : Z) : Prop :=
  EB R /\ getr R 8 = zw (T + node * 4) /\ getr R 21 = zw (T + node * 4) /\ getr R 20 = zw node /\ getr R 26 = zw (node + 1).

Definition X2P : list (Z * expr) :=
  EBP ++ [(8, EAdd (EVar 33) (EShl (EVar 36) 2)); (21, EAdd (EVar 33) (EShl (EVar 36) 2)); (20, EVar 36); (26, EVar 36); (23, EVar 39)].
Definition L3P : list (Z * expr) :=
  EBP ++ [(8, EAdd (EVar 33) (EShl (EVar 36) 2)); (21, EAdd (EVar 33) (EShl (EVar 36) 2)); (20, EVar 36); (26, EAdd (EVar 36) (ELit 1))].

Local Ltac eregs HR Hfr := unfold BuildTree6u_4.EREGS, Q3REGS, L3REGS, BuildTree6u_4.FREGS, BuildTree6u_4.EB; repeat split; reg1 HR Hfr.

Local Ltac nodef FC DP x PF PD :=
  assert (PF : pb FC x = arr_get FC x)
    by (apply (pb_get FC); [intros q Hq; match goal with Hr : RNG FC DP |- _ => apply (proj1 Hr); rewrite <- (proj1 (proj2 (proj2 Hr))); exact Hq end
                         | match goal with Hr : RNG FC DP |- _ => rewrite (proj1 (proj2 (proj2 Hr))); lia end]);
  assert (PD : wb DP x = arr_get DP x)
    by (apply (wb_get DP); [intros q Hq; match goal with Hr : RNG FC DP |- _ => apply (proj1 (proj2 Hr)); rewrite <- (proj2 (proj2 (proj2 Hr))); exact Hq end
                         | match goal with Hr : RNG FC DP |- _ => rewrite (proj2 (proj2 (proj2 Hr))); lia end]).

Definition dmax (DP : arr) (n m : Z) : Z := if arr_get DP m <=? arr_get DP n then arr_get DP n else arr_get DP m.

Local Ltac e2_fin :=
  first
    [ nf; vfix; rewrite wrap16_sx_add; f_equal; f_equal; lia
    | nf; vfix; f_equal; f_equal;
      repeat match goal with |- context [if ?a <=? ?b then _ else _] => destruct (Z.leb_spec a b) end; lia
    |
      lazymatch goal with
      | |- BuildTree6u_4.PQ4 _ _ _ /\ _ =>
          split; [|split; [|rewrite !arr_len_set; assumption]];
          [ split; [|rewrite !arr_len_set; assumption];
            intros i Hi; rewrite !arr_get_set; unfold arr_inb; rewrite !arr_len_set;
            match goal with L : arr_len ?h = 573 |- context [arr_len ?h] => rewrite L end;
            repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end;
            rewrite ?Bool.andb_true_iff, ?Bool.andb_false_iff, ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_le, ?Z.ltb_lt in *;
            try lia;
            match goal with Hp : forall q, 1 <= q <= _ -> 0 <= arr_get ?h q < tsize t |- 0 <= arr_get ?h _ < _ => apply Hp; lia end
          | match goal with Hr : BuildTree6u_4.RNG _ ?FC ?DP |- _ =>
              destruct Hr as (RFC' & RDP' & LFC' & LDP');
              split; [|split; [|split; [rewrite arr_len_set; exact LFC' | rewrite arr_len_set; exact LDP']]];
              [ intros i Hi; rewrite arr_get_set; destruct (_ =? i); destruct (arr_inb FC _); cbn [andb];
                [apply wrap16_range' | apply RFC'; exact Hi..]
              | intros i Hi; rewrite arr_get_set; destruct (_ =? i); destruct (arr_inb DP _); cbn [andb];
                [rewrite wrap8_mod'; apply Z.mod_pos_bound; lia | apply RDP'; exact Hi..] ] end ]
      end ].


Lemma e2_blk : forall regs m1 m FC DL HP HLc HM DP node n,
  EI m1 m FC DL HP HLc HM DP -> LOC2 m1 -> 1 <= HLc <= 571 -> 0 <= node < tsize t -> 3 <= HM <= 573 ->
  0 <= n < tsize t ->
  X2REGS regs node n ->
  let m_ := arr_get HP 1 in
  exists R m',
    msteps s6u_segs (mkst regs (0x1cc7c : word) m s6u_rom) (mkst R (0x1de0c : word) m' s6u_rom)
    /\ EI m1 m' (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_)))
                (arr_set (arr_set DL m_ (wrap16 node)) n (wrap16 node))
                (arr_set (arr_set (arr_set HP (HM - 1) n) (HM - 2) m_) 1 node) HLc (HM - 2)
                (arr_set DP node (wrap8 (dmax DP n m_ + 1)))
    /\ Q3REGS R node
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC DL HP HLc HM DP node n (HC & HPQ & HRN & LDL) HLOC Hhl Hnode Hhm Hn HE.
  pose proof HC as (_ & _ & HAG0 & _). pose proof (LOC2_keep m1 m HAG0 HLOC) as ((C16 & C56 & C40 & C32 & C24 & C48) & C64 & C8). clear HAG0.
  open_ciT HC. destruct HE as ((P9 & P18 & P19 & P22 & P24 & P25 & P27 & P2) & P8 & P21 & P20 & P26 & P23).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof HPQ as [HPQ1 LHP]. pose proof HRN as (RFC & RDP & LFC & LDP).
  assert (R1 : 0 <= arr_get HP 1 < tsize t) by (apply HPQ1; lia).
  assert (V1 : hv HP 1 = arr_get HP 1) by (apply hv_get; lia).
  nodef FC DP n PFn PDn. nodef FC DP (arr_get HP 1) PFm PDm.
  assert (C4' : cell s6u_segs m (S + 5304) 4 (HM - 2 + 2)) by (replace (HM - 2 + 2) with HM by lia; exact Chm).
  cbv zeta. unfold dmax.
  destruct (Z.ltb_spec (arr_get DP (arr_get HP 1)) (arr_get DP n)) as [Cd|Cd].
  - run 80%nat [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true; false; false]
        [RVal (EAdd (EVar 38) (ELit 2)); RVal (EApp1 2 (ELit 1)); RVal (EVar 44); RVal (EVar 35); RVal (EVar 32)] X2P
        [S; T; SP; E; node; HLc; HM - 2; n; 0; S + 2976; 0; 0; NHP; NDP; NT; 0; STP t; dsc_off t; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    nf_in Hms. rewrite !V1 in Hms.
    lazymatch type of Hms with
    | msteps _ _ (mkst ?R _ ?M _) =>
        exists R, M; split; [exact Hms|]; clear Hms;
        split; [ split; [ci_tower HB HRC HAG MS MP MF HFf M
                            [KHm; KHeap (HM - 1); KHm; KHeap (HM - 2); KFc node; KDepth node; KDl (arr_get HP 1); KDl n; KHeap 1] | ]
               | split; [eregs HR Hfr | fr_weak Hfr] ]
    end.
    all: e2_fin.
  - run 80%nat [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]
        [RVal (EAdd (EVar 38) (ELit 2)); RVal (EApp1 2 (ELit 1)); RVal (EVar 44); RVal (EVar 35); RVal (EVar 32)] X2P
        [S; T; SP; E; node; HLc; HM - 2; n; 0; S + 2976; 0; 0; NHP; NDP; NT; 0; STP t; dsc_off t; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    nf_in Hms. rewrite !V1 in Hms.
    lazymatch type of Hms with
    | msteps _ _ (mkst ?R _ ?M _) =>
        exists R, M; split; [exact Hms|]; clear Hms;
        split; [ split; [ci_tower HB HRC HAG MS MP MF HFf M
                            [KHm; KHeap (HM - 1); KHm; KHeap (HM - 2); KFc node; KDepth node; KDl (arr_get HP 1); KDl n; KHeap 1] | ]
               | split; [eregs HR Hfr | fr_weak Hfr] ]
    end.
    all: e2_fin.
Qed.

Goal True. idtac "e2_blk OK". exact I. Qed.


Lemma x3_blk : forall regs m1 m FC DL HP HLc HM DP node,
  EI m1 m FC DL HP HLc HM DP -> 1 <= HLc <= 571 -> 0 <= node < tsize t ->
  Q3REGS regs node ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1de0c : word) m s6u_rom)
           (mkst R (if 1 <? HLc then (0x1cc40 : word) else (0x1cdcc : word)) m' s6u_rom)
    /\ EI m1 m' FC DL (ds_heap (pqdownheap (W6 FC DL HP HLc HM DP) t 1)) HLc HM DP
    /\ (if 1 <? HLc then EREGS R HLc (node + 1) else FREGS R)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC DL HP HLc HM DP node (HC & [HPQ1 LHP] & HRN & LDL) Hhl Hnode HQ.
  pose proof HRN as (RFC & RDP & LFC & LDP).
  destruct HQ as (HB1 & P8 & P21 & P20 & P26 & P10 & P11 & P12 & P1).
  pose proof HB1 as (Q9 & Q18 & Q19 & Q22 & Q24 & Q25 & Q27 & Q2).
  assert (Hrq : ret_ok (zw 0x1cdb4)) by (apply ret_ok_lit; [lia | reflexivity]).
  destruct (BuildTree6u_pq2.pq_run _ _ _ _ _ _ _ _ _ _ HH FC DL HLc HM DP BC OL SL MC RFC RDP ltac:(lia) LFC LDP
              regs m1 m HP 1 (zw 0x1cdb4) (conj HC (conj HPQ1 LHP)) ltac:(lia) P10 P11 P12 Q2 P1 Hrq)
    as (R1 & ma & Hms1 & (HC1 & HPQ2 & LHP2) & W2 & Hfr1).
  symex_pc_lit_in Hms1.
  assert (HL1 : L3REGS R1 node).
  { unfold L3REGS, BuildTree6u_4.EB. rewrite !Hfr1 by reflexivity. repeat split; assumption. }
  clear HB1 P8 P21 P20 P26 P10 P11 P12 P1 Q9 Q18 Q19 Q22 Q24 Q25 Q27 Q2.
  enough (HX : exists R m', msteps s6u_segs (mkst R1 (0x1cdb4 : word) ma s6u_rom)
                                 (mkst R (if 1 <? HLc then (0x1cc40 : word) else (0x1cdcc : word)) m' s6u_rom)
            /\ EI m1 m' FC DL (ds_heap (pqdownheap (W6 FC DL HP HLc HM DP) t 1)) HLc HM DP
            /\ (if 1 <? HLc then EREGS R HLc (node + 1) else FREGS R)
            /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr R1 r)).
  { destruct HX as (R2 & mb & Hms2 & HE2 & HR2 & Hfr2). exists R2, mb.
    split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HE2|]. split; [exact HR2|].
    intros r Hr. rewrite (Hfr2 r Hr). apply Hfr1. eapply reg_in_sub; [| exact Hr]. reflexivity. }
  destruct HL1 as ((P9 & P18 & P19 & P22 & P24 & P25 & P27 & P2) & P8 & P21 & P20 & P26).
  open_ciT HC1.
  destruct (Z.ltb_spec 1 HLc) as [C|C].
  - run 20%nat [true] [RVal (EVar 37)] L3P
        [S; T; SP; E; node; HLc; 0; 0; 0; S + 2976; 0; 0; NHP; NDP; NT; 0; STP t; dsc_off t; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    exists R, ma. split; [exact Hms|].
    split; [split; [split; [exact HB | split; [exact HRC | split; [exact HAG | exact MF]]] | split; [split; [exact HPQ2 | exact LHP2] | split; [exact HRN | exact LDL]]]|].
    split; [eregs HR Hfr | fr_weak Hfr].
  - run 20%nat [false] [RVal (EVar 37)] L3P
        [S; T; SP; E; node; HLc; 0; 0; 0; S + 2976; 0; 0; NHP; NDP; NT; 0; STP t; dsc_off t; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    exists R, ma. split; [exact Hms|].
    split; [split; [split; [exact HB | split; [exact HRC | split; [exact HAG | exact MF]]] | split; [split; [exact HPQ2 | exact LHP2] | split; [exact HRN | exact LDL]]]|].
    split; [eregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "x3_blk OK". exact I. Qed.


Section Trip.
Variables (FC DL HP : arr) (HL HM : Z) (DP : arr) (node : Z).
Let n := arr_get HP 1.
Let HP1 := arr_set HP 1 (arr_get HP HL).
Let HP2 := ds_heap (pqdownheap (W6 FC DL HP1 (HL - 1) HM DP) t 1).
Let m_ := arr_get HP2 1.
Let FC' := arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_)).
Let DL' := arr_set (arr_set DL m_ (wrap16 node)) n (wrap16 node).
Let HP3 := arr_set (arr_set (arr_set HP2 (HM - 1) n) (HM - 2) m_) 1 node.
Let DP' := arr_set DP node (wrap8 (dmax DP n m_ + 1)).
Definition trip : deflate_state := pqdownheap (W6 FC' DL' HP3 (HL - 1) (HM - 2) DP') t 1.

Lemma trip_flat : trip = W6 FC' DL' (ds_heap trip) (HL - 1) (HM - 2) DP'.
Proof. unfold trip. apply pq_flat. Qed.

Lemma L4_step : forall f,
  build_tree_loop4 (Datatypes.S f) (W6 FC DL HP HL HM DP) t node =
    if 2 <=? HL - 1 then build_tree_loop4 f trip t (node + 1) else trip.
Proof.
  intros f. cbn [build_tree_loop4]. unfold SMALLEST. autorewrite with btupd.
  rewrite (pq_flat FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP).
  fold HP1. fold HP2. autorewrite with btupd.
  unfold trip. subst n m_ FC' DL' HP3 DP'. fold HP1. fold HP2.
  rewrite pqdownheap_heap_len, bt_heap_len. unfold dmax.
  replace (HM - 1 - 1) with (HM - 2) by lia. reflexivity.
Qed.

Lemma e_trip : forall regs m1 m,
  EI m1 m FC DL HP HL HM DP -> LOC2 m1 -> 2 <= HL <= 572 -> 3 <= HM <= 573 -> 0 <= node < tsize t ->
  EREGS regs HL node ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1cc40 : word) m s6u_rom)
           (mkst R (if 1 <? HL - 1 then (0x1cc40 : word) else (0x1cdcc : word)) m' s6u_rom)
    /\ EI m1 m' FC' DL' (ds_heap trip) (HL - 1) (HM - 2) DP'
    /\ (if 1 <? HL - 1 then EREGS R (HL - 1) (node + 1) else FREGS R)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m HE HLOC Hhl Hhm Hnode HRE.
  pose proof Htt as Htt'. pose proof elems_range as He. pose proof tsize_elems as Hte.
  assert (Hn : 0 <= n < tsize t) by (subst n; apply (proj1 (proj1 (proj2 HE))); lia).
  destruct (e_remove regs m1 m FC DL HP HL HM DP node HE HLOC Hhl ltac:(lia) HRE)
    as (R1 & ma & Hms1 & HE1 & HR1 & Hfr1).
  fold HP1 in HE1. fold HP2 in HE1.
  assert (Hm : 0 <= m_ < tsize t) by (subst m_; apply (proj1 (proj1 (proj2 HE1))); lia).
  destruct (e2_blk R1 m1 ma FC DL HP2 (HL - 1) HM DP node n HE1 HLOC ltac:(lia) Hnode Hhm Hn HR1) as (R2 & mb & Hms2 & HE2 & HR2 & Hfr2).
  fold m_ in HE2. fold FC' in HE2. fold DL' in HE2. fold HP3 in HE2. fold DP' in HE2.
  destruct (x3_blk R2 m1 mb FC' DL' HP3 (HL - 1) (HM - 2) DP' node HE2 ltac:(lia) Hnode HR2) as (R3 & mc & Hms3 & HE3 & HR3 & Hfr3).
  exists R3, mc. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
  split; [exact HE3|]. split; [exact HR3|].
  intros r Hr. rewrite (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.
End Trip.

Goal True. idtac "e_trip OK". exact I. Qed.

Lemma e_loop : forall f regs m1 m FC DL HP HL HM DP node,
  EI m1 m FC DL HP HL HM DP -> LOC2 m1 -> EREGS regs HL node ->
  2 <= HL -> 2 * HL - 1 <= HM <= 573 -> 0 <= node -> node + HL <= tsize t ->
  HL - 1 <= Z.of_nat f ->
  exists R m' FC' DL' HP' HM' DP',
    build_tree_loop4 f (W6 FC DL HP HL HM DP) t node = W6 FC' DL' HP' 1 HM' DP'
    /\ msteps s6u_segs (mkst regs (0x1cc40 : word) m s6u_rom) (mkst R (0x1cdcc : word) m' s6u_rom)
    /\ EI m1 m' FC' DL' HP' 1 HM' DP'
    /\ FREGS R /\ HM' = HM - 2 * (HL - 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction f as [|f IH]; intros regs m1 m FC DL HP HL HM DP node HE HLOC HRE Hhl Hhm Hn0 Hnh Hf; [lia|].
  pose proof Htt as Htt'. pose proof tsize_elems as Hte. pose proof elems_range as He.
  assert (Hhl572 : HL <= 572) by lia.
  rewrite L4_step.
  destruct (e_trip FC DL HP HL HM DP node regs m1 m HE HLOC ltac:(lia) ltac:(lia) ltac:(lia) HRE)
    as (R1 & m2 & Hms1 & HE1 & HR1 & Hfr1).
  destruct (Z.leb_spec 2 (HL - 1)) as [C|C].
  - replace (1 <? HL - 1) with true in Hms1, HR1 by (symmetry; apply Z.ltb_lt; lia).
    rewrite (trip_flat FC DL HP HL HM DP node).
    destruct (IH R1 m1 m2 _ _ _ (HL - 1) (HM - 2) _ (node + 1) HE1 HLOC HR1 C ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (R2 & m3 & FC' & DL' & HP' & HM' & DP' & E2 & Hms2 & HE2 & HF2 & EHM & Hfr2).
    exists R2, m3, FC', DL', HP', HM', DP'. split; [exact E2|].
    split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HE2|]. split; [exact HF2|]. split; [lia|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
  - replace (1 <? HL - 1) with false in Hms1, HR1 by (symmetry; apply Z.ltb_ge; lia).
    rewrite (trip_flat FC DL HP HL HM DP node). replace (HL - 1) with 1 in * by lia.
    eexists R1, m2, _, _, _, (HM - 2), _. split; [reflexivity|].
    split; [exact Hms1|]. split; [exact HE1|]. split; [exact HR1|]. split; [lia|]. exact Hfr1.
Qed.

Goal True. idtac "e_loop OK". exact I. Qed.

End PhaseE.
End Walk.
End FXG.

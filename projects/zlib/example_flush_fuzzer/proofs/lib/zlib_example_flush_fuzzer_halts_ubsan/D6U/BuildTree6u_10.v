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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u TreesRod6u TreesApi6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import BuildTree6u_1 BuildTree6u_4 BuildTree6u_6 BuildTree6u_8.
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


Lemma pb_read2 : forall m P n (a0 : arr) i a,
  cells s6u_segs m P 2 2 n (arr_get a0) -> 0 <= i < n -> 0 <= arr_get a0 i < 65536 -> a = P + 2 * i ->
  exists bs, rdn s6u_segs m (zw a) 2 = Some bs /\ bytes_le_to_Z bs = pb a0 i.
Proof.
  intros m P n a0 i a Hc Hi Hr ->. unfold pb. rewrite Z.mod_small by exact Hr.
  apply (cells_read_small s6u_segs m P 2 2 n (arr_get a0) i Hc Hi). cbn. lia.
Qed.

Lemma eqm_add : forall M a a' b b', M <> 0 -> a mod M = a' mod M -> b mod M = b' mod M -> (a + b) mod M = (a' + b') mod M.
Proof. intros M a a' b b' HM Ha Hb.
  rewrite (Z.add_mod a b M HM), (Z.add_mod a' b' M HM), Ha, Hb. reflexivity. Qed.
Lemma eqm_add_comm : forall M a a' b b', M <> 0 -> a mod M = b' mod M -> b mod M = a' mod M -> (a + b) mod M = (a' + b') mod M.
Proof. intros M a a' b b' HM Ha Hb. rewrite (Z.add_comm a' b'). apply eqm_add; assumption. Qed.
Lemma eqm_mul : forall M a a' c, M <> 0 -> a mod M = a' mod M -> (a * c) mod M = (a' * c) mod M.
Proof. intros M a a' c HM Ha.
  rewrite (Z.mul_mod a c M HM), (Z.mul_mod a' c M HM), Ha. reflexivity. Qed.
Lemma eqm_sx16 : forall a a', a mod 2 ^ 16 = a' mod 2 ^ 16 -> szwrap 16 a mod 2 ^ 16 = a' mod 2 ^ 16.
Proof. intros a a' Ha. rewrite szwrap_eqm by lia. exact Ha. Qed.

Ltac eqm16 :=
  first [ reflexivity
        | apply eqm_sx16; eqm16
        | apply eqm_mul; [lia | eqm16]
        | apply eqm_add; [lia | solve [eqm16] | solve [eqm16]]
        | apply eqm_add_comm; [lia | solve [eqm16] | solve [eqm16]] ].


Definition VB9 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300); (36%nat, 600); (37%nat, 600);
   (38%nat, 16); (39%nat, 65536); (40%nat, 65536); (41%nat, 65536); (42%nat, 2 ^ 64); (43%nat, 2 ^ 64);
   (44%nat, 2 ^ 64); (45%nat, 2 ^ 64); (46%nat, 2 ^ 64)].

Definition stC9 : cfg :=
  CFG FB6 [] [EVar 1%nat] [0x1d350; 0x1d38c; 0x1d3a4; 0x1d3b8]
      [AV (EVar 32) 2976 2 4 (ELit 0);
       AV (EAdd (EVar 33) (EShl (EVar 36) 2)) 2 2 1 (EVar 36)].

Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC9 VB9 fuel dirs rds pins pv FC DL HP DP BC.

Ltac side_closer ::=
  try solve [ assumption
            | nf; vfix; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); rewrite ?Z.mod_small by lia; lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; lazymatch goal with
                  | |- exists bs, rdn _ ?m (zw ?a) 2%nat = Some bs /\ bytes_le_to_Z bs = pb ?a0 ?i =>
                      match goal with H : cells _ m ?P 2 2%nat ?len (arr_get a0) |- _ =>
                        eapply (pb_read2 m P len a0 i a H); [lia | arr_range_auto | lia] end
                  end
            | nf; symex_read_auto
            | nf; vfix; first [symex_read_auto | ag_read]
            | nf; vfix;
              lazymatch goal with
              | |- exists bs, rdn ?sg ?m (zw ?a) ?w = Some bs /\ bytes_le_to_Z bs = arr_get ?tt ?i =>
                  match goal with H : cell sg m ?a' w (arr_get tt i) |- _ =>
                    first [constr_eq a a' | replace a with a' by lia];
                    eapply (cell_read_at sg m a' w _ _ H); rewrite Z.mod_small; [reflexivity | cbn; arr_range_auto] end
              end
            | nf; vfix; symex_store_auto
            | nf; vfix; symex_sok_auto
            | nf; vfix; zc
            | intros; first [apply (BuildTree6u_6.extra_view_bound' S t) | nf; first [apply pb_range | apply hv_range | apply wb_range | apply Z.mod_pos_bound; lia]] ].

Local Ltac regsG HR Hfr := repeat split; reg1 HR Hfr.


Section PhaseI.
Variables (DL HP : arr) (HM : Z) (DP BC : arr) (OL SL MC : Z).
Local Abbreviation WI a := (U a DL HP 1 HM DP BC OL SL MC).
Local Abbreviation GCR := (BuildTree6u_8.GCR S sp t).
Local Abbreviation LOC2 := (BuildTree6u_4.LOC2 S sp t MC).
Local Abbreviation LOC2_keep := (BuildTree6u_4.LOC2_keep F mem0 mem S p PBL ds ra sp t HH MC).
Local Abbreviation NNC := (2 ^ 64 - 1 - (SP + 72)).
Hypothesis Hmc : 0 <= MC < E.
Hypothesis RBC : forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536.
Hypothesis LBC : arr_len BC = 16.
Hypothesis RDL : forall i, 0 <= i < tsize t -> 0 <= arr_get DL i < 65536.
Hypothesis LDL : arr_len DL = tsize t.
Hypothesis Hlen : forall i, 0 <= i <= MC -> 0 <= arr_get DL i <= 15.

Definition NCX (m : word -> option byte) (nc : arr) : Prop :=
  forall i, 1 <= i <= 15 -> cell s6u_segs m (SP + 72 + 2 * i) 2 (arr_get nc i).

Definition GI9 (m1 m : word -> option byte) (a nc : arr) : Prop :=
  CI m1 m (WI a) /\ arr_len a = tsize t /\ NCX m nc /\ arr_len nc = 16
  /\ (forall i, 1 <= i <= 15 -> 0 <= arr_get nc i < 65536).

Definition IB (R : bvmap 5 word) : Prop :=
  getr R 22 = zw T /\ getr R 2 = zw SP /\ getr R 11 = zw (SP + 72) /\ getr R 12 = zw 16 /\ getr R 13 = zw NNC
  /\ getr R 14 = zw (2 ^ 31 - 1) /\ getr R 15 = zw 1 /\ getr R 29 = zw MC.
Definition IBP : list (Z * expr) :=
  [(22, EVar 33); (2, EVar 34); (11, EAdd (EVar 34) (ELit 72)); (12, ELit 16); (13, EVar 42); (14, ELit 2147483647); (15, ELit 1); (29, EVar 37)].
Definition HREGS (R : bvmap 5 word) (n : Z) : Prop := IB R /\ getr R 10 = zw n.
Definition HP9 : list (Z * expr) := IBP ++ [(10, EVar 36)].
Definition RREGS (R : bvmap 5 word) (n len code res : Z) : Prop :=
  IB R /\ getr R 10 = zw n /\ getr R 16 = zw (T + n * 4) /\ getr R 6 = zw (len + 1)
  /\ getr R 5 = zw code /\ getr R 17 = zw res.
Definition RP9 : list (Z * expr) :=
  IBP ++ [(10, EVar 36); (16, EAdd (EVar 33) (EShl (EVar 36) 2)); (6, EAdd (EVar 38) (ELit 1)); (5, EVar 39); (17, EVar 40)].
Definition WREGS (R : bvmap 5 word) (n v : Z) : Prop :=
  IB R /\ getr R 10 = zw n /\ getr R 16 = zw (T + n * 4) /\ getr R 7 = zw v.
Definition WP9 : list (Z * expr) :=
  IBP ++ [(10, EVar 36); (16, EAdd (EVar 33) (EShl (EVar 36) 2)); (7, EVar 41)].


Definition PRE9 (m : word -> option byte) (k : Z) : Prop :=
  forall i, 1 <= i < k -> cell s6u_segs m (SP + 72 + 2 * i) 2 (arr_get (NC BC) i).

Lemma pb_blc : forall i, 0 <= i < 16 -> pb BC i = arr_get BC i.
Proof. intros i Hi. unfold pb. apply Z.mod_small. apply RBC. exact Hi. Qed.

Lemma PRE9_write : forall m (k : nat) a0 v',
  PRE9 m (Z.of_nat k) -> (1 <= k <= 15)%nat -> a0 = SP + 72 + 2 * Z.of_nat k ->
  v' mod 2 ^ 16 = gcode (pb BC) k mod 2 ^ 16 ->
  PRE9 (wbytes m (zw a0) (Z_to_le_bytes 2 v')) (Z.of_nat k + 1).
Proof.
  intros m k a0 v' Hnc Hk -> Ev. pose proof Hsp as Hsp'. unfold PRE9 in *.
  intros i Hi. destruct (Z.eq_dec i (Z.of_nat k)) as [->|Hne].
  - replace (Z_to_le_bytes 2 v') with (Z_to_le_bytes 2 (arr_get (NC BC) (Z.of_nat k))).
    { apply cell_write_same; cbn; lia. }
    apply Z_to_le_bytes_eqm. change (2 ^ (8 * Z.of_nat 2)) with (2 ^ 16). rewrite Ev.
    rewrite (proj2 (NC_spec BC RBC) k) by lia.
    rewrite (gcode_ext (pb BC) (arr_get BC)) by (intros; apply pb_blc; lia).
    rewrite wrap16_mod. apply Z.mod_mod. lia.
  - apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). apply Hnc. lia.
Qed.

Lemma pro_blk : forall regs m1 m FC,
  CI m1 m (WI FC) -> LOC2 m1 -> arr_len FC = tsize t -> GCR regs ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1d23c : word) m s6u_rom) (mkst R (0x1d350 : word) m' s6u_rom)
    /\ HREGS R 0 /\ GI9 m1 m' FC (NC BC)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HC HLOC LFC HR0. pose proof HC as HC'.
  pose proof HC as (_ & _ & HAG0 & _). pose proof (LOC2_keep m1 m HAG0 HLOC) as ((C16 & C56 & C40 & C32 & C24 & C48) & C64 & C8). clear HAG0.
  open_ciT HC. destruct HR0 as (P24 & P22 & P2).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  run 80%nat [false; false] [RVal (EVar 37); RVal (ELit 0)] [(24, EAdd (EVar 32) (ELit 2976)); (22, EVar 33); (2, EVar 34)]
      [S; T; SP; E; 0; MC; 0; 0; 0; 0; NNC; 0; 0; 0; NT] FC DL HP DP BC.
  all: dbg_left.
  lazymatch goal with
  | Hms : msteps _ _ (mkst ?R _ ?M _), HR : regs_ok _ _ ?R, Hfr : forall r, _ -> getr ?R r = _ |- _ =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [unfold HREGS, IB; regsG HR Hfr|];
      split; [| fr_weak Hfr];
      split; [ci_tower HB HRC HAG MS MP MF HFf M
                [KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther; KOther] |]
  end.
  split; [exact LFC|].
  split; [| split; [exact (proj1 (NC_spec BC RBC)) | intros i Hi; apply NC_range; [exact RBC | lia]]].
  intros i Hi. apply (fun H : PRE9 _ 16 => H i ltac:(lia)).
  change 16 with (Z.of_nat 15 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 15) with (Z.of_nat 14 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 14) with (Z.of_nat 13 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 13) with (Z.of_nat 12 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 12) with (Z.of_nat 11 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 11) with (Z.of_nat 10 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 10) with (Z.of_nat 9 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 9) with (Z.of_nat 8 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 8) with (Z.of_nat 7 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 7) with (Z.of_nat 6 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 6) with (Z.of_nat 5 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 5) with (Z.of_nat 4 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 4) with (Z.of_nat 3 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 3) with (Z.of_nat 2 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  change (Z.of_nat 2) with (Z.of_nat 1 + 1). apply PRE9_write; [|lia|cbn; lia|nf; cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm16].
  intros j Hj. lia.
Qed.

Goal True. idtac "pro_blk OK". exact I. Qed.



Lemma loop2_WI : forall f a nc n,
  gen_codes_loop2 (Datatypes.S f) (WI a) t nc MC n =
    if n <=? MC then
      let len := arr_get DL n in
      if len =? 0 then gen_codes_loop2 f (WI a) t nc MC (n + 1)
      else
        let ncv := arr_get nc len in
        gen_codes_loop2 f (WI (arr_set a n (wrap16 (bi_reverse ncv len)))) t
                        (arr_set nc len (wrap16 (ncv + 1))) MC (n + 1)
    else WI a.
Proof.
  intros. cbn [gen_codes_loop2]. rewrite bt_Len.
  destruct (n <=? MC); [|reflexivity]. cbv zeta.
  destruct (arr_get DL n =? 0); [reflexivity|]. unfold set_Code. rewrite bt_set_Freq. reflexivity.
Qed.

Lemma NCX_write : forall m nc l v b v',
  NCX m nc -> arr_len nc = 16 -> (forall i, 1 <= i <= 15 -> 0 <= arr_get nc i < 65536) ->
  1 <= l <= 15 -> b = SP + 72 + 2 * l -> Z_to_le_bytes 2 v' = Z_to_le_bytes 2 v ->
  NCX (wbytes m (zw b) (Z_to_le_bytes 2 v')) (arr_set nc l (wrap16 v))
  /\ arr_len (arr_set nc l (wrap16 v)) = 16
  /\ (forall i, 1 <= i <= 15 -> 0 <= arr_get (arr_set nc l (wrap16 v)) i < 65536).
Proof.
  intros m nc l v b v' Hnc Lnc Rnc Hl -> Ev. pose proof Hsp as Hsp'. split; [|split].
  - intros j Hj. rewrite arr_get_set. unfold arr_inb. rewrite Lnc.
    destruct (Z.eq_dec l j) as [<-|Hne].
    + replace ((0 <=? l) && (l <? 16)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      rewrite Z.eqb_refl, Ev.
      rewrite <- (SymExec.Z_to_le_bytes_mod 2 v). change (2 ^ (8 * Z.of_nat 2)) with 65536. rewrite <- wrap16_mod.
      apply cell_write_same; cbn; lia.
    + replace (l =? j) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact (Hnc j Hj).
  - rewrite arr_len_set. exact Lnc.
  - intros j Hj. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range' | exact (Rnc j Hj)].
Qed.

Lemma NCX_other : forall m nc (b : Z) bs,
  NCX m nc -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (SP + 104 <= b \/ b + Z.of_nat (length bs) <= SP + 74) ->
  NCX (wbytes m (zw b) bs) nc.
Proof.
  intros m nc b bs Hnc Hb Hbn Hd j Hj. pose proof Hsp as Hsp'.
  apply cell_write_other; try (cbn; lia). exact (Hnc j Hj).
Qed.

Lemma h_blk : forall regs m1 m a nc n,
  GI9 m1 m a nc -> LOC2 m1 -> HREGS regs n -> 0 <= n <= MC ->
  let len := arr_get DL n in
  if len =? 0 then
    exists R, msteps s6u_segs (mkst regs (0x1d350 : word) m s6u_rom)
                     (mkst R (if n =? MC then (0x1d3b8 : word) else (0x1d350 : word)) m s6u_rom)
      /\ HREGS R (n + 1)
      /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)
  else
    exists R m', msteps s6u_segs (mkst regs (0x1d350 : word) m s6u_rom) (mkst R (0x1d38c : word) m' s6u_rom)
      /\ RREGS R n len (arr_get nc len) 0
      /\ GI9 m1 m' a (arr_set nc len (wrap16 (arr_get nc len + 1)))
      /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m a nc n HG HLOC HR0 Hn. pose proof HG as (HC & La & Hnc & Lnc & Rnc).
  pose proof HC as (_ & _ & HAG0 & _). pose proof (LOC2_keep m1 m HAG0 HLOC) as ((C16 & C56 & C40 & C32 & C24 & C48) & C64 & C8). clear HAG0.
  open_ciT HC.
  destruct HR0 as ((P22 & P2 & P11 & P12 & P13 & P14 & P15 & P29) & P10).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  assert (Vn : pb DL n = arr_get DL n) by (apply (pb_get DL); [intros q Hq; apply RDL; rewrite <- LDL; exact Hq | rewrite LDL; lia]).
  pose proof (Hlen n Hn) as Ln. cbv zeta.
  destruct (Z.eqb_spec (arr_get DL n) 0) as [C1|C1].
  - destruct (Z.eqb_spec n MC) as [C2|C2].
    + subst n. run 20%nat [false; true; false; false] [RVal (EVar 46)] HP9 [S; T; SP; E; MC; MC; 0; 0; 0; 0; NNC; 0; 0; 0; NT] a DL HP DP BC.
      all: dbg_left.
      exists R. split; [exact Hms|]. split; [unfold HREGS, IB; regsG HR Hfr | fr_weak Hfr].
    + run 20%nat [false; true; false; true] [RVal (EVar 46)] HP9 [S; T; SP; E; n; MC; 0; 0; 0; 0; NNC; 0; 0; 0; NT] a DL HP DP BC.
      all: dbg_left.
      exists R. split; [exact Hms|]. split; [unfold HREGS, IB; regsG HR Hfr | fr_weak Hfr].
  - set (len := arr_get DL n) in *.
    assert (Cl : cell s6u_segs m (SP + len * 2 ^ 1 + 72) 2 (arr_get nc len)).
    { replace (SP + len * 2 ^ 1 + 72) with (SP + 72 + 2 * len) by lia. apply Hnc. lia. }
    pose proof (Rnc len ltac:(lia)) as Rl.
    run 30%nat [false; false; false; false] [RVal (EVar 46); RVal (EVar 41)] HP9 [S; T; SP; E; n; MC; len; 0; 0; arr_get nc len; NNC; 0; 0; 0; NT] a DL HP DP BC.
    all: dbg_left.
    nf_in Hms. rewrite !Vn in Hms.
    lazymatch goal with
    | Hms : msteps _ _ (mkst ?R _ ?M _), HR : regs_ok _ _ ?R, Hfr : forall r, _ -> getr ?R r = _ |- _ =>
        exists R, M; split; [exact Hms|]; clear Hms;
        split; [unfold RREGS, IB; regsG HR Hfr|];
        split; [| fr_weak Hfr];
        split; [ci_tower HB HRC HAG MS MP MF HFf M [KOther] |]
    end.
    split; [exact La|].
    apply (NCX_write m nc len (arr_get nc len + 1)); [exact Hnc | exact Lnc | exact Rnc | lia | lia |].
    apply Z_to_le_bytes_eqm. nf. vfix. reflexivity.
Qed.

Goal True. idtac "h_blk OK". exact I. Qed.


Lemma r_blk : forall regs m n len code res,
  RREGS regs n len code res -> 0 <= n <= MC -> 1 <= len <= 15 -> 0 <= code < 65536 -> 0 <= res < 65536 ->
  let v := Z.lor (code mod 2 ^ 1) res in
  exists R, msteps s6u_segs (mkst regs (0x1d38c : word) m s6u_rom)
                   (mkst R (if len =? 1 then (0x1d3a4 : word) else (0x1d38c : word)) m s6u_rom)
    /\ (if len =? 1 then WREGS R n v else RREGS R n (len - 1) (code / 2 ^ 1) (v * 2 ^ 1))
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m n len code res HRg Hn Hl Hc Hr. cbv zeta.
  pose proof Hsp as Hsp'. pose proof Htt as Htt'. pose proof Hmc as Hmc'. pose proof elems_range as He.
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'.
  destruct HRg as ((P22 & P2 & P11 & P12 & P13 & P14 & P15 & P29) & P10 & P16 & P6 & P5 & P17).
  destruct (Z.eqb_spec len 1) as [C1|C1].
  - subst len. run 20%nat [false] NoReads RP9 [S; T; SP; E; n; MC; 1; code; res; 0; NNC; 0; 0; 0; 0] (arr_make 1 0) DL HP DP BC.
    all: dbg_left.
    exists R. split; [exact Hms|]. split; [unfold WREGS, IB; regsG HR Hfr | fr_weak Hfr].
    all: rewrite (Z.lor_comm res); first [reflexivity | f_equal; lia].
  - run 20%nat [true] NoReads RP9 [S; T; SP; E; n; MC; len; code; res; 0; NNC; 0; 0; 0; 0] (arr_make 1 0) DL HP DP BC.
    all: dbg_left.
    exists R. split; [exact Hms|]. split; [unfold RREGS, IB; regsG HR Hfr | fr_weak Hfr].
    all: rewrite (Z.lor_comm res); first [reflexivity | f_equal; lia].
Qed.

Goal True. idtac "r_blk OK". exact I. Qed.

Lemma r_loop : forall k regs m n len code res,
  RREGS regs n len code res -> 0 <= n <= MC -> 1 <= len <= 15 -> len = Z.of_nat k ->
  0 <= code < 65536 -> 0 <= res < 2 ^ (16 - len) ->
  exists R, msteps s6u_segs (mkst regs (0x1d38c : word) m s6u_rom) (mkst R (0x1d3a4 : word) m s6u_rom)
    /\ WREGS R n (brl code res len)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction k as [|k IH]; intros regs m n len code res HRg Hn Hl Hk Hc Hr; [lia|].
  assert (Hp : 2 ^ (16 - len) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (Hr' : 0 <= res < 65536) by (change 65536 with (2 * 2 ^ 15); lia).
  assert (Hv : 0 <= Z.lor (code mod 2 ^ 1) res < 2 ^ (16 - len)).
  { apply lor_bit_bound; [lia | exact Hr |]. apply (Z.le_lt_trans _ (2 ^ 0)); [lia|]. apply Z.pow_lt_mono_r; lia. }
  assert (Hv31 : Z.lor (code mod 2 ^ 1) res < 2 ^ 31).
  { apply (Z.lt_le_trans _ (2 ^ (16 - len))); [lia|]. apply Z.pow_le_mono_r; lia. }
  pose proof (r_blk regs m n len code res HRg Hn Hl Hc Hr') as HB. cbv zeta in HB.
  set (v := Z.lor (code mod 2 ^ 1) res) in *.
  destruct (Z.eqb_spec len 1) as [C1|C1].
  - destruct HB as (R1 & Hms1 & HW1 & Hfr1). rewrite C1. rewrite brl_last by (subst v; lia).
    exists R1. split; [exact Hms1|]. split; [exact HW1 | exact Hfr1].
  - destruct HB as (R1 & Hms1 & HR1 & Hfr1).
    rewrite brl_step by (subst v; lia). fold v.
    destruct (IH R1 m n (len - 1) (code / 2 ^ 1) (v * 2 ^ 1) HR1 Hn ltac:(lia) ltac:(lia))
      as (R2 & Hms2 & HW2 & Hfr2).
    { change (2 ^ 1) with 2. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
    { replace (16 - (len - 1)) with (16 - len + 1) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia. }
    exists R2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HW2|].
    intros r Hr0. rewrite (Hfr2 r Hr0). exact (Hfr1 r Hr0).
Qed.

Goal True. idtac "r_loop OK". exact I. Qed.


Lemma w_blk : forall regs m1 m a nc n v,
  GI9 m1 m a nc -> WREGS regs n v -> 0 <= n <= MC -> 0 <= v < 65536 ->
  exists R m', msteps s6u_segs (mkst regs (0x1d3a4 : word) m s6u_rom)
                      (mkst R (if n =? MC then (0x1d3b8 : word) else (0x1d350 : word)) m' s6u_rom)
    /\ HREGS R (n + 1)
    /\ GI9 m1 m' (arr_set a n (wrap16 v)) nc
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m a nc n v HG HW Hn Hv. pose proof HG as (HC & La & Hnc & Lnc & Rnc). open_ciT HC.
  destruct HW as ((P22 & P2 & P11 & P12 & P13 & P14 & P15 & P29) & P10 & P16 & P7).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  destruct (Z.eqb_spec n MC) as [C1|C1].
  - subst n. run 20%nat [false; false] NoReads WP9 [S; T; SP; E; MC; MC; 0; 0; 0; v; NNC; 0; 0; 0; 0] a DL HP DP BC.
    all: dbg_left.
    lazymatch goal with
    | Hms : msteps _ _ (mkst ?R _ ?M _), HR : regs_ok _ _ ?R, Hfr : forall r, _ -> getr ?R r = _ |- _ =>
        exists R, M; split; [exact Hms|]; clear Hms;
        split; [unfold HREGS, IB; regsG HR Hfr|];
        split; [| fr_weak Hfr];
        split; [ci_tower HB HRC HAG MS MP MF HFf M [KFc MC] |]
    end.
    split; [rewrite arr_len_set; exact La|]. split; [| split; [exact Lnc | exact Rnc]].
    apply NCX_other; [exact Hnc | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia].
  - run 20%nat [false; true] NoReads WP9 [S; T; SP; E; n; MC; 0; 0; 0; v; NNC; 0; 0; 0; 0] a DL HP DP BC.
    all: dbg_left.
    lazymatch goal with
    | Hms : msteps _ _ (mkst ?R _ ?M _), HR : regs_ok _ _ ?R, Hfr : forall r, _ -> getr ?R r = _ |- _ =>
        exists R, M; split; [exact Hms|]; clear Hms;
        split; [unfold HREGS, IB; regsG HR Hfr|];
        split; [| fr_weak Hfr];
        split; [ci_tower HB HRC HAG MS MP MF HFf M [KFc n] |]
    end.
    split; [rewrite arr_len_set; exact La|]. split; [| split; [exact Lnc | exact Rnc]].
    apply NCX_other; [exact Hnc | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia].
Qed.

Goal True. idtac "w_blk OK". exact I. Qed.


Local Ltac frc2 a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr); exact (b r Hr).
Local Ltac frc3 a b c := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr); exact (c r Hr).
Local Ltac frc4 a b c d := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr), (c r Hr); exact (d r Hr).

Lemma loop_run : forall f n regs m1 m a nc,
  GI9 m1 m a nc -> LOC2 m1 -> HREGS regs n -> 0 <= n <= MC -> (Z.to_nat (MC - n) < f)%nat ->
  exists R m' a' nc',
    msteps s6u_segs (mkst regs (0x1d350 : word) m s6u_rom) (mkst R (0x1d3b8 : word) m' s6u_rom)
    /\ gen_codes_loop2 f (WI a) t nc MC n = WI a'
    /\ GI9 m1 m' a' nc'
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction f as [|f IH]; intros n regs m1 m a nc HG HLOC HRn Hn Hf; [lia|].
  rewrite loop2_WI. replace (n <=? MC) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  pose proof (h_blk regs m1 m a nc n HG HLOC HRn Hn) as HB. cbv zeta in HB.
  pose proof (Hlen n Hn) as Ln.
  destruct (Z.eqb_spec (arr_get DL n) 0) as [C1|C1].
  - destruct HB as (R1 & Hms1 & HH1 & Hfr1).
    destruct (Z.eqb_spec n MC) as [C2|C2].
    + subst n. rewrite loop2_out by lia.
      exists R1, m, a, nc. split; [exact Hms1|]. split; [reflexivity|]. split; [exact HG | exact Hfr1].
    + destruct (IH (n + 1) R1 m1 m a nc HG HLOC HH1 ltac:(lia) ltac:(lia)) as (R2 & m2 & a2 & nc2 & Hms2 & E2 & HG2 & Hfr2).
      exists R2, m2, a2, nc2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact E2|]. split; [exact HG2 | frc2 Hfr2 Hfr1].
  - destruct HB as (R1 & m1' & Hms1 & HR1 & HG1 & Hfr1).
    set (len := arr_get DL n) in *.
    pose proof HG as (_ & _ & _ & Lnc & Rnc).
    pose proof (Rnc len ltac:(lia)) as Hncv.
    destruct (r_loop (Z.to_nat len) R1 m1' n len (arr_get nc len) 0 HR1 Hn ltac:(lia) ltac:(lia) Hncv
                ltac:(split; [lia | apply Z.pow_pos_nonneg; lia])) as (R2 & Hms2 & HW2 & Hfr2).
    assert (Hbr : 0 <= brl (arr_get nc len) 0 len < 65536).
    { pose proof (brl_bound (Z.to_nat len) (arr_get nc len) 0) as B. cbv zeta in B.
      rewrite Z2Nat.id in B by lia. change (2 ^ 16) with 65536 in B.
      apply B; [lia | lia |]. split; [lia|]. apply Z.pow_pos_nonneg; lia. }
    rewrite <- bi_reverse_brl in HW2, Hbr by lia.
    destruct (w_blk R2 m1 m1' a _ n _ HG1 HW2 Hn Hbr) as (R3 & m3 & Hms3 & HH3 & HG3 & Hfr3).
    destruct (Z.eqb_spec n MC) as [C2|C2].
    + subst n. rewrite loop2_out by lia.
      exists R3, m3, (arr_set a MC (wrap16 (bi_reverse (arr_get nc len) len))), (arr_set nc len (wrap16 (arr_get nc len + 1))).
      split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
      split; [reflexivity|]. split; [exact HG3 | frc3 Hfr3 Hfr2 Hfr1].
    + destruct (IH (n + 1) R3 m1 m3 _ _ HG3 HLOC HH3 ltac:(lia) ltac:(lia)) as (R4 & m4 & a4 & nc4 & Hms4 & E4 & HG4 & Hfr4).
      exists R4, m4, a4, nc4.
      split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3 | exact Hms4]|].
      split; [exact E4|]. split; [exact HG4 | frc4 Hfr4 Hfr3 Hfr2 Hfr1].
Qed.

Goal True. idtac "loop_run OK". exact I. Qed.


Lemma i_phase : forall regs m1 m FC,
  CI m1 m (WI FC) -> LOC2 m1 -> GCR regs ->
  exists R m' FC',
    gen_codes (WI FC) t MC = WI FC'
    /\ msteps s6u_segs (mkst regs (0x1d23c : word) m s6u_rom) (mkst R (0x1d3b8 : word) m' s6u_rom)
    /\ CI m1 m' (WI FC')
    /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HC HLOC HR0.
  assert (LFC : arr_len FC = tsize t).
  { destruct HC as (HB & _). destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & HTL & _).
    pose proof (tree_lens_fc _ t HTL) as L. rewrite bt_tree_fc in L. exact L. }
  destruct (pro_blk regs m1 m FC HC HLOC LFC HR0) as (R1 & m' & Hms1 & HH1 & HG1 & Hfr1).
  destruct (loop_run (Datatypes.S (Z.to_nat MC)) 0 R1 m1 m' FC (NC BC) HG1 HLOC HH1 ltac:(lia) ltac:(lia))
    as (R2 & m2 & a2 & nc2 & Hms2 & E2 & HG2 & Hfr2).
  exists R2, m2, a2.
  split.
  { unfold gen_codes. rewrite bt_bl_count. fold (NC BC).
    replace (Z.to_nat (MC + 1)) with (Datatypes.S (Z.to_nat MC)) by lia. exact E2. }
  split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
  split; [exact (proj1 HG2)|].
  split; [rewrite (Hfr2 2%bv eq_refl); destruct HH1 as ((_ & P2 & _) & _); exact P2|].
  frc2 Hfr2 Hfr1.
Qed.

Goal True. idtac "i_phase OK". exact I. Qed.

End PhaseI.
End Walk.
End FXG.

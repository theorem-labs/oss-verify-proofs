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
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel SendModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 TreesRod6 TreesApi6 CompressBlk6_1 SendTree6_1 SendTree6_2 SendTree6_3 SendTree6_4.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Section Walk.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word) (sp : Z).
Variables (t : tree_id) (mc : Z).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation T := (S + toff t).
Local Abbreviation SP := (sp - 80).
Local Abbreviation BRm := (BR6 F mem0 S p PBL).
Local Abbreviation L i := (Len ds t i).
Local Abbreviation BC c := (arr_get (ds_bl_tree_fc ds) c).
Local Abbreviation BL c := (arr_get (ds_bl_tree_dl ds) c).

Hypothesis HH : STH F mem0 mem S p PBL ds ra sp t mc.

Let Hret : ret_ok ra := sth_ret _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := sth_L _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hfr80 : call_frame F mem S PB PBL sp 80 := sth_fr _ _ _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := sth_br _ _ _ _ _ _ _ _ _ _ _ HH.
Let Ht : t = TL \/ t = TD := sth_t _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hmc : 0 <= mc /\ mc + 1 < tsize t := sth_mc _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hlen : forall i, 0 <= i <= mc -> 0 <= Len ds t i <= 15 := sth_len _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hdl : forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl ds t) i < 65536 := sth_dl _ _ _ _ _ _ _ _ _ _ _ HH.
Let HbC : forall c, 0 <= c < 39 -> 0 <= arr_get (ds_bl_tree_fc ds) c < 65536 := sth_bc _ _ _ _ _ _ _ _ _ _ _ HH.
Let HbL : forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl ds) c < 16 := sth_bl _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hbinv : BINV PBL ds := sth_binv _ _ _ _ _ _ _ _ _ _ _ HH.
Let HPBL : 0 < PBL := sth_pbl _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hsp : 80 <= sp <= 2 ^ 63 := proj1 Hfr80.
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Local Abbreviation PURE := (SendTree6_1.PURE PBL ds).
Local Abbreviation GI := (SendTree6_1.GI S p PBL).
Local Abbreviation CI := (SendTree6_1.CI F mem0 S p PBL ds).
Local Abbreviation PURE_send := (SendTree6_1.PURE_send PBL ds).
Local Abbreviation PURE_Len := (SendTree6_1.PURE_Len PBL ds t).
Local Abbreviation PURE_blc := (SendTree6_1.PURE_blc PBL ds).
Local Abbreviation KREGS := (SendTree6_1.KREGS S sp t mc).
Local Abbreviation HREGS := (SendTree6_1.HREGS S sp t mc).
Local Abbreviation DREGS := (SendTree6_1.DREGS S sp t mc).
Local Abbreviation GREGS := (SendTree6_1.GREGS S sp t mc).
Local Abbreviation stF := (SendTree6_1.stF ds t).
Local Abbreviation FRAME := (SendTree6_1.FRAME sp).
Local Abbreviation cnts0 := (SendTree6_1.cnts0 ds t).
Local Abbreviation DP := SendTree6_2.DP.
Local Abbreviation CIx := (SendTree6_3.CIx F mem0 S p PBL ds).
Local Abbreviation cntsnz := SendTree6_1.cntsnz.


Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [SendTree6_1.stF].

Local Ltac st_read :=
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
            | nf; st_read
            | zcond_close
            | nf; symex_read_auto
            | nf; symex_store_auto
            | nf; symex_sok_auto
            | intros; nf; apply pb_range ].

Local Ltac run_with vb fuel dirs rds pins pv :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in vb in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs stC fuel dirs rdv pinsv vbv NoRegions pv NoVals (SendTree6_1.stF ds t) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.
Local Ltac run fuel dirs rds pins pv := run_with VB fuel dirs rds pins pv.
Local Ltac run_dbg fuel dirs rds pins pv :=
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex_dbg s6_segs stC fuel dirs rdv pinsv vbv NoRegions pv (mkst regs pc m s6_rom)
  end.

Local Ltac open_br HB HP :=
  let P1 := fresh "Pbinv" in let P2 := fresh "Pfc" in let P3 := fresh "Pdl" in let P4 := fresh "Plen" in let P5 := fresh "Plens" in
  pose proof HP as HP'; destruct HP' as (P1 & P2 & P3 & P4 & P5);
  let Hbv := fresh "Hbv" in let Hbb := fresh "Hbb" in let Hpd := fresh "Hpd" in
  pose proof P1 as HBI'; destruct HBI' as (Hbv & Hbb & Hpd);
  let HS' := fresh "HS'" in let HPB' := fresh "HPB'" in let HD := fresh "HD" in
  pose proof HLb as HL'; destruct HL' as (HS' & HPB' & HD & _); unfold dsl_SIZE in HS', HD;
  let MS := fresh "MS" in let MP := fresh "MP" in let Hsc := fresh "Hsc" in let Har := fresh "Har" in
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & _ & _ & _ & MS & MP & _); unfold mapped, dsl_SIZE in MS, MP;
  let C40 := fresh "C40" in let C16 := fresh "C16" in let C5936 := fresh "C5936" in let C5940 := fresh "C5940" in
  let Cpb := fresh "Cpb" in
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HB) as (C40 & C16 & C5936 & C5940 & Cpb); dsred in C40; dsred in C5940; dsred in C5936; dsred in Cpb;
  let TDl := fresh "TDl" in let BLc := fresh "BLc" in let BLd := fresh "BLd" in
  pose proof (arrays_dl s6_segs _ _ _ t Har) as TDl; pose proof (arrays_fc s6_segs _ _ _ TB Har) as BLc;
  pose proof (arrays_dl s6_segs _ _ _ TB Har) as BLd; cbn [toff tsize] in BLc, BLd;
  rewrite ?tree_dl_set_bi_buf in TDl; rewrite ?tree_fc_set_bi_buf in BLc; rewrite ?tree_dl_set_bi_buf in BLd;
  try rewrite (P3 t) in TDl; try rewrite (P2 TB) in BLc; try rewrite (P3 TB) in BLd;
  cbn [tree_fc tree_dl] in BLc, BLd;
  replace (S + 2748 + 2) with (S + 2750) in BLd by lia;
  clear Hsc Har;
  let Hsp' := fresh "Hsp'" in pose proof Hsp as Hsp';
  let Htt' := fresh "Htt'" in pose proof Htt as Htt';
  let Hmc' := fresh "Hmc'" in pose proof Hmc as Hmc'.

Local Ltac ag_tower HAG :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold GI;
              first [ apply sub_franges_here; cbn; lia | apply sub_franges_later; apply sub_franges_here; cbn; lia ] ]);
  exact HAG.

Local Ltac kregs HR Hfr :=
  unfold KREGS; repeat split;
  lazymatch goal with |- getr ?R ?r = _ =>
    first [ rewrite (Hfr r eq_refl); assumption
          | let A := fresh "A" in symex_reg HR r as A; rewrite A;
            first [ reflexivity | f_equal; lia
                  | lazymatch goal with |- zw ?a = zw ?b =>
                      lazymatch isZcst a with true => lazymatch isZcst b with true =>
                        apply bv_eq; vm_compute; reflexivity end end end ] ]
  end.

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

Local Ltac vcongr := first [ reflexivity | apply pb_mod16 | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite szwrap32_mod16, wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity
                           | apply mod16_congr; lia
                           | apply mod16_up; lia
                           | rewrite land16_mod; first [apply mod16_congr; lia | apply mod16_up; lia]
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; first [apply mod16_congr; lia | apply mod16_up; lia] ].
Local Ltac vwrap := first [ reflexivity | apply pb_wrap16 | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; first [reflexivity | apply mod16_congr; lia | apply mod16_up; lia]
                          | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | rewrite wrap16_mod', wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity
                          | apply wrap16_id'; lia
                          | apply land16_wrap16; first [apply mod16_congr; lia | apply mod16_up; lia] ].
Local Ltac vrange := first [ apply pb_range | lia | apply Z.mod_pos_bound; lia | apply land16_range ].
Local Ltac rbm := first [ assumption | apply szwrap16_mod; assumption | apply szwrap16_mod; lia
                        | lazymatch goal with H : RBr _ _ _ |- _ => exact H end
                        | apply Z.mod_small; lia ].

Local Ltac st_flush vnorm :=
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); st_eq;
  [ vnorm; f_equal;
    [ f_equal; [lia | apply byte0_eq; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr]]
    | lia
    | apply byte1_eq2; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr] ]
  | lia
  | first [reflexivity | vnorm; apply srl_eq'; [vrange | vwrap | lia]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; lia] ].
Local Ltac rb_flush r HR vnorm :=
  unfold RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_buf;
  vnorm; apply srl_eq'; [vrange | vwrap | lia].
Local Ltac bv_flush r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; lia.
Local Ltac st_keep vnorm :=
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); st_eq;
  [ reflexivity
  | reflexivity
  | first [reflexivity | vnorm; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); lia] ].
Local Ltac rb_keep r HR vnorm :=
  unfold RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_buf;
  vnorm; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr].
Local Ltac bv_keep r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); lia.
Local Ltac sll_flush r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; f_equal; lia.
Local Ltac sll_keep r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); f_equal; lia.
Local Ltac pure_fin HP := first [exact HP | apply PURE_send; [exact HP | lia | unfold sb_room, Buf_size; intros; lia]].

Local Ltac site_fin Hms HR Hfr HB HP HAG tst tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd HB M;
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eapply BR_eqst; [exact HB2|]; clear HB2; tst
                        | split; [pure_fin HP | ag_tower HAG] ]
                 | tregs ]
      end
  end.

Local Ltac site_finx Hms HR Hfr HB HP HAG tst tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd HB M;
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eexists; eapply BR_eqst; [exact HB2|]; clear HB2; tst
                        | split; [pure_fin HP | ag_tower HAG] ]
                 | tregs ]
      end
  end.

Local Ltac cnt_reg HR :=
  lazymatch goal with |- getr ?R ?r = _ =>
    let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
    rewrite ?lxor_ltb1 by lia; rewrite ?Z.eqb_refl;
    try (replace (_ =? _) with false by (symmetry; apply Z.eqb_neq; lia));
    vm_compute; reflexivity
  end.

Local Ltac kd H := destruct H as (K10 & K11 & K12 & K13 & K16 & K17 & K5 & K6 & K7 & K28 & K29 & K30 & K31 & K2).


Definition SL (s : deflate_state) (n pl c k mx mn : Z) : deflate_state :=
  send_tree_loop (Z.to_nat (mc + 1 - n)) s t mc n pl c k mx mn.
Definition OK (s : deflate_state) (n pl c k mx mn : Z) : Prop :=
  send_tree_ok PBL (Z.to_nat (mc + 1 - n)) s t mc n pl c k mx mn.

Lemma SL_step : forall s n pl c k mx mn, 0 <= n <= mc -> 1 <= mn ->
  SL s n pl c k mx mn =
    (let nl := Len s t (n + 1) in
     if (k + 1 <? mx) && (c =? nl) then SL s (n + 1) pl nl (k + 1) mx mn
     else let '(mx', mn') := tree_counts c nl in
          SL (sbs_run s (st_calls s mn c pl (k + 1))) (n + 1) c nl 0 mx' mn').
Proof.
  intros s n pl c k mx mn Hn Hmn. unfold SL.
  replace (Z.to_nat (mc + 1 - n)) with (Datatypes.S (Z.to_nat (mc + 1 - (n + 1)))) by lia.
  rewrite send_loop_S by exact Hmn. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  destruct ((k + 1 <? mx) && (c =? Len s t (n + 1))); [reflexivity|].
  destruct (tree_counts c (Len s t (n + 1))); reflexivity.
Qed.

Lemma SL_out : forall s n pl c k mx mn, mc < n -> SL s n pl c k mx mn = s.
Proof. intros. unfold SL. apply send_loop_out. lia. Qed.

Lemma OK_step : forall s n pl c k mx mn, 0 <= n <= mc ->
  OK s n pl c k mx mn ->
    (let nl := Len s t (n + 1) in
     if (k + 1 <? mx) && (c =? nl) then OK s (n + 1) pl nl (k + 1) mx mn
     else let '(mx', mn') := tree_counts c nl in
          sbs_ok PBL s (st_calls s mn c pl (k + 1))
          /\ OK (sbs_run s (st_calls s mn c pl (k + 1))) (n + 1) c nl 0 mx' mn').
Proof.
  intros s n pl c k mx mn Hn H. unfold OK in *.
  replace (Z.to_nat (mc + 1 - n)) with (Datatypes.S (Z.to_nat (mc + 1 - (n + 1)))) in H by lia.
  cbn [send_tree_ok] in H. replace (n <=? mc) with true in H by (symmetry; apply Z.leb_le; lia).
  cbv zeta in H. exact H.
Qed.

Definition cnts (pl c : Z) : Z * Z := if c =? 0 then (138, 3) else if c =? pl then (6, 3) else (7, 4).

Lemma cnts_tree_counts : forall c nl, tree_counts c nl = cnts c nl.
Proof. intros c nl. unfold tree_counts, cnts. rewrite (Z.eqb_sym c nl). reflexivity. Qed.

Definition BND (pl c k mx mn : Z) : Prop :=
  (pl = -1 \/ 0 <= pl <= 15) /\ 0 <= c <= 15 /\ 0 <= k < mx /\ (mx, mn) = cnts pl c.

Lemma BND_facts : forall pl c k mx mn, BND pl c k mx mn ->
  (mx = 138 \/ mx = 6 \/ mx = 7) /\ (mn = 3 \/ mn = 4) /\ (c = 0 -> mn = 3) /\ (c <> 0 -> c <> pl -> mn = 4) /\ (c <> 0 -> c = pl -> mn = 3).
Proof.
  intros pl c k mx mn (_ & _ & _ & E). unfold cnts in E.
  destruct (Z.eqb_spec c 0); [injection E; intros; subst; lia|].
  destruct (Z.eqb_spec c pl); injection E; intros; subst; lia.
Qed.


Definition FIN (m0 : word -> option byte) (regs : bvmap 5 word) (pc : word) (m : word -> option byte) (s' : deflate_state) : Prop :=
  exists R m', msteps s6_segs (mkst regs pc m s6_rom) (mkst R (0x1cc40 : word) m' s6_rom)
    /\ CI m0 m' s' /\ KREGS R
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).

Local Ltac frc2 a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr); exact (b r Hr).

Lemma FIN_step : forall m0 regs pc m R1 pc1 m1 s',
  msteps s6_segs (mkst regs pc m s6_rom) (mkst R1 pc1 m1 s6_rom) ->
  (forall r : reg, reg_in r CLOBI = false -> getr R1 r = getr regs r) ->
  FIN m0 R1 pc1 m1 s' -> FIN m0 regs pc m s'.
Proof.
  intros m0 regs pc m R1 pc1 m1 s' Hms1 Hfr1 (R2 & m2 & Hms2 & HC & HK & Hfr2).
  exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HC|]. split; [exact HK|]. frc2 Hfr2 Hfr1.
Qed.

Lemma L_facts : forall i, 0 <= i <= mc + 1 -> 0 <= L i < 65536 /\ (i <= mc -> L i <= 15).
Proof.
  intros i Hi. pose proof Hmc as Hmc'. split.
  - unfold Len. apply Hdl. lia.
  - intros Hle. apply (proj2 (Hlen i ltac:(lia))).
Qed.

Lemma CI_PURE : forall m0 m s, CI m0 m s -> PURE s.
Proof. intros m0 m s (_ & P & _). exact P. Qed.

Lemma latch : forall m0 R m s' n' pl' c' k' mx' mn' (IHn : Prop),
  (n' = mc + 1 \/ n' <= mc) ->
  CI m0 m s' -> HREGS R n' pl' c' k' mx' mn' ->
  (n' <= mc -> FIN m0 R (0x1c79c : word) m (SL s' n' pl' c' k' mx' mn')) ->
  FIN m0 R (if n' =? mc + 1 then (0x1cc40 : word) else (0x1c79c : word)) m (SL s' n' pl' c' k' mx' mn').
Proof.
  intros m0 R m s' n' pl' c' k' mx' mn' _ Hn HC HRg HIH.
  destruct (Z.eqb_spec n' (mc + 1)) as [En|En].
  - rewrite SL_out by lia. exists R, m. split; [apply mst_refl|]. split; [exact HC|].
    split; [exact (proj1 HRg) | intros r Hr; reflexivity].
  - apply HIH. lia.
Qed.

Section Level.
Variable m0 : word -> option byte.

Lemma level : forall f n, 0 <= n -> mc + 1 - n <= Z.of_nat f ->
  forall regs m s pl c k mx mn,
    CI m0 m s -> HREGS regs n pl c k mx mn -> n <= mc -> BND pl c k mx mn -> c = L n ->
    OK s n pl c k mx mn -> FIN m0 regs (0x1c79c : word) m (SL s n pl c k mx mn).
Proof.
  induction f as [|f IH]; intros n Hn0 Hf regs m s pl c k mx mn HC HRg Hn HB Ec Hok; [exfalso; lia|].
  pose proof Hmc as Hmc'.
  pose proof (BND_facts _ _ _ _ _ HB) as (Bmx & Bmn & Bc0 & Bc1 & Bc2). pose proof HB as (Bpl & Bc & Bk & Bcn).
  pose proof (L_facts (n + 1) ltac:(lia)) as [R1 R1'].
  pose proof (OK_step s n pl c k mx mn ltac:(lia) Hok) as Hok'. cbv zeta in Hok'.
  rewrite SL_step by lia. cbv zeta.
  rewrite (PURE_Len s (n + 1) (CI_PURE _ _ _ HC)) in Hok' |- *.
  set (nl := L (n + 1)) in *.
  assert (IHn : forall R' m' s' pl' c' k' mx' mn',
            CI m0 m' s' -> HREGS R' (n + 1) pl' c' k' mx' mn' -> n + 1 <= mc -> BND pl' c' k' mx' mn' -> c' = nl ->
            OK s' (n + 1) pl' c' k' mx' mn' -> FIN m0 R' (0x1c79c : word) m' (SL s' (n + 1) pl' c' k' mx' mn')).
  { intros. apply (IH (n + 1)); try assumption; lia. }
  destruct (Sumbool.sumbool_of_bool ((k + 1 <? mx) && (c =? nl))) as [CC|CC]; rewrite CC in Hok' |- *.
  -
    apply andb_prop in CC. destruct CC as [C1 C2]. apply Z.ltb_lt in C1. apply Z.eqb_eq in C2.
    destruct (h_cont _ _ _ _ _ _ _ _ _ _ _ HH regs m0 m s n pl c k mx mn HC HRg ltac:(lia) Bc Bk ltac:(lia) ltac:(lia) C1 C2)
      as (R & Hms & HRg' & Hfr).
    eapply FIN_step; [exact Hms | exact Hfr|].
    rewrite <- C2. apply (latch m0 R m s (n + 1) pl c (k + 1) mx mn True); [lia | exact HC | exact HRg' |].
    intros Hle. apply (IHn R m s pl c (k + 1) mx mn HC HRg' Hle); [| exact C2 | rewrite C2; exact Hok'].
    unfold BND. repeat split; try lia. exact Bcn.
  -
    assert (Hcase : mx <= k + 1 \/ c <> nl).
    { apply Bool.andb_false_iff in CC. destruct CC as [C1|C1]; [apply Z.ltb_ge in C1; lia | apply Z.eqb_neq in C1; lia]. }
    destruct (h_emit _ _ _ _ _ _ _ _ _ _ _ HH regs m0 m s n pl c k mx mn HC HRg ltac:(lia) Bc Bk ltac:(lia) ltac:(lia) Hcase)
      as (Rd & Hmsd & HD & Hfrd).
    eapply FIN_step; [exact Hmsd | exact Hfrd|].
    rewrite cnts_tree_counts in Hok' |- *.
    assert (Hok1 : sbs_ok PBL s (st_calls s mn c pl (k + 1))).
    { clear -Hok'. unfold cnts in Hok'. destruct (nl =? 0); [exact (proj1 Hok')|]. destruct (nl =? c); exact (proj1 Hok'). }
    assert (ARM : exists R m', msteps s6_segs (mkst Rd (0x1c7bc : word) m s6_rom) (mkst R (TGT nl) m' s6_rom)
                  /\ CI m0 m' (sbs_run s (st_calls s mn c pl (k + 1))) /\ GREGS R n c nl
                  /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr Rd r)).
    { unfold st_calls in Hok1 |- *. rewrite !(PURE_blc s _ (CI_PURE _ _ _ HC)) in Hok1 |- *.
      change REP_3_6 with 16 in *. change REPZ_3_10 with 17 in *. change REPZ_11_138 with 18 in *.
      destruct (Z.ltb_spec (k + 1) mn) as [Km|Km].
      - exact (rep_arm _ _ _ _ _ _ _ _ _ _ _ HH Rd m0 m s n pl c nl k mx mn HC HD ltac:(lia) Bc R1 ltac:(lia) Km ltac:(lia) ltac:(lia) Hok1).
      - destruct (Z.eqb_spec c 0) as [Cz|Cz]; cbn [negb] in Hok1 |- *.
        + pose proof (Bc0 Cz) as Mn3. rewrite Cz in HD |- *.
          exact (z_arm _ _ _ _ _ _ _ _ _ _ _ HH Rd m0 m s n pl nl k mx mn HC HD ltac:(lia) R1 ltac:(lia) Km ltac:(lia) ltac:(lia) ltac:(lia) Bpl Hok1).
        + replace (k + 1 - 1) with k in Hok1 |- * by lia.
          exact (e_arm _ _ _ _ _ _ _ _ _ _ _ HH Rd m0 m s n pl c nl k mx mn HC HD ltac:(lia) ltac:(lia) R1 ltac:(lia) Km ltac:(lia) ltac:(lia) ltac:(lia) Bpl Hok1). }
    destruct ARM as (Ra & ma & Hmsa & HCa & HGa & Hfra).
    eapply FIN_step; [exact Hmsa | exact Hfra|].
    set (s' := sbs_run s _) in *.
    unfold cnts in Hok' |- *. unfold TGT.
    destruct (Z.eqb_spec nl 0) as [E1|E1].
    +
      cbn beta iota zeta in Hok'. destruct Hok' as [_ Hok2].
      rewrite E1 in HGa, Hok2 |- *.
      destruct (tz_blk _ _ _ _ _ _ _ _ _ _ _ HH Ra ma n c HGa ltac:(lia) Bc) as (Rt & Hmst & HRt & Hfrt).
      eapply FIN_step; [exact Hmst | exact Hfrt|].
      apply (latch m0 Rt ma s' (n + 1) c 0 0 138 3 True); [lia | exact HCa | exact HRt |].
      intros Hle. apply (IHn Rt ma s' c 0 0 138 3 HCa HRt Hle); [| symmetry; exact E1 | exact Hok2].
      unfold BND, cnts. cbn. repeat split; lia.
    + destruct (tnz_blk _ _ _ _ _ _ _ _ _ _ _ HH Ra ma n c nl HGa ltac:(lia) Bc ltac:(lia)) as (Rt & Hmst & HRt & Hfrt).
      eapply FIN_step; [exact Hmst | exact Hfrt|].
      unfold SendTree6_1.cntsnz in HRt. rewrite (Z.eqb_sym c nl) in HRt.
      destruct (Z.eqb_spec nl c) as [E2|E2]; cbn [fst snd] in HRt; cbn beta iota zeta in Hok'; destruct Hok' as [_ Hok2].
      * apply (latch m0 Rt ma s' (n + 1) c nl 0 6 3 True); [lia | exact HCa | exact HRt |].
        intros Hle. apply (IHn Rt ma s' c nl 0 6 3 HCa HRt Hle); [| reflexivity | exact Hok2].
        unfold BND, cnts. replace (nl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite E2, Z.eqb_refl.
        repeat split; lia.
      * apply (latch m0 Rt ma s' (n + 1) c nl 0 7 4 True); [lia | exact HCa | exact HRt |].
        intros Hle. apply (IHn Rt ma s' c nl 0 7 4 HCa HRt Hle); [| reflexivity | exact Hok2].
        unfold BND, cnts. replace (nl =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (nl =? c) with false by (symmetry; apply Z.eqb_neq; lia). repeat split; lia.
Qed.
End Level.


Definition send_tree_safe : Prop := OK ds 0 (-1) (L 0) 0 (fst cnts0) (snd cnts0).

Lemma PURE0 : PURE ds.
Proof.
  pose proof HBR0 as HB. destruct HB as (_ & _ & Hlens & _ & Hplen & _).
  unfold SendTree6_1.PURE. split; [exact Hbinv|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
  split; [exact Hplen | exact Hlens].
Qed.

Lemma send_tree_SL : send_tree ds t mc = SL ds 0 (-1) (L 0) 0 (fst cnts0) (snd cnts0).
Proof.
  unfold send_tree, SL, SendTree6_1.cnts0. cbv zeta. replace (mc + 1 - 0) with (mc + 1) by lia.
  destruct (L 0 =? 0); reflexivity.
Qed.

Lemma frame_keep : forall m1 m2 a v,
  agree_out GI m1 m2 -> cell s6_segs m1 a 8 v -> SP <= a -> a + 8 <= sp -> cell s6_segs m2 a 8 v.
Proof.
  intros m1 m2 a v Hag Hc Ha1 Ha2.
  pose proof Hfr80 as (Hsp' & _ & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof HLb as (HS' & HPB' & _). unfold dsl_SIZE in HS'.
  apply (cell_agree_out s6_segs GI m1 m2 a 8 v Hag); [| lia | cbn; lia | exact Hc].
  unfold SendTree6_1.GI. apply disj_franges_cons; [cbn; lia|]. apply disj_franges_cons; [cbn; lia|]. apply disj_franges_nil.
Qed.

Lemma mapped_keep : forall m1 m2,
  agree_out GI m1 m2 -> mapped m1 SP 80 -> mapped m2 SP 80.
Proof.
  intros m1 m2 Hag Hm x Hx.
  pose proof Hfr80 as (Hsp' & _ & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof HLb as (HS' & HPB' & _). unfold dsl_SIZE in HS'.
  rewrite (Hag x).
  - exact (Hm x Hx).
  - unfold SendTree6_1.GI. intros [H|[H|H]]; cbn in H; [lia | lia | exact H].
Qed.

Theorem send_tree_run : forall regs,
  getr regs 10 = zw S -> getr regs 11 = zw T -> getr regs 12 = zw mc -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  send_tree_safe ->
  exists R m',
    msteps s6_segs (mkst regs (0x1c6fc : word) mem s6_rom) (mkst R ra m' s6_rom)
    /\ BRm m' (send_tree ds t mc)
    /\ PURE (send_tree ds t mc)
    /\ getr R 2 = getr regs 2
    /\ (forall r : reg, reg_in r ST_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P11 P12 P2 P1 Hsafe.
  pose proof PURE0 as HP0. pose proof Hmc as Hmc'.
  destruct (pro_blk _ _ _ _ _ _ _ _ _ _ _ HH regs P10 P11 P12 P2 P1 HP0) as (R1 & m1 & Hms1 & HC1 & HH1 & Q1 & HF1 & HM1 & Hfr1).
  pose proof (L_facts 0 ltac:(lia)) as [R0 R0']. specialize (R0' ltac:(lia)).
  assert (HB0 : BND (-1) (L 0) 0 (fst cnts0) (snd cnts0)).
  { unfold BND, cnts, SendTree6_1.cnts0. destruct (Z.eqb_spec (L 0) 0); cbn [fst snd]; [repeat split; lia|].
    replace (L 0 =? -1) with false by (symmetry; apply Z.eqb_neq; lia). repeat split; lia. }
  destruct (level m1 (Datatypes.S (Z.to_nat (mc + 1))) 0 ltac:(lia) ltac:(lia) R1 m1 ds (-1) (L 0) 0 (fst cnts0) (snd cnts0)
              HC1 HH1 ltac:(lia) HB0 eq_refl Hsafe) as (R2 & m2 & Hms2 & HC2 & K2 & Hfr2).
  rewrite <- send_tree_SL in HC2.
  pose proof HC2 as (HB2 & HPU2 & HAG2).
  destruct HF1 as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & U).
  assert (HF2 : FRAME m2 [bv_unsigned (getr regs 8); bv_unsigned (getr regs 9); bv_unsigned (getr regs 18);
                          bv_unsigned (getr regs 19); bv_unsigned (getr regs 20); bv_unsigned (getr regs 21);
                          bv_unsigned (getr regs 22); bv_unsigned (getr regs 23); bv_unsigned (getr regs 24)]).
  { unfold SendTree6_1.FRAME. repeat (split; [apply (frame_keep m1 m2 _ _ HAG2); [assumption | lia | lia]|]). exact U. }
  destruct (exit_blk _ _ _ _ _ _ _ _ _ _ _ HH R2 m2 _ _ _ _ _ _ _ _ _ K2 ltac:(rewrite (Hfr2 1%bv eq_refl); exact Q1) HF2 (mapped_keep m1 m2 HAG2 HM1))
    as (R3 & Hms3 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E2 & Hfr3).
  exists R3, m2. split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms3]. }
  split; [exact HB2|]. split; [exact HPU2|].
  split; [rewrite E2, P2; reflexivity|].
  apply (frame_fix R3 regs 2%bv); [rewrite E2, P2; reflexivity|].
  apply (frame_fix R3 regs 8%bv); [rewrite E8; apply zw_u|].
  apply (frame_fix R3 regs 9%bv); [rewrite E9; apply zw_u|].
  apply (frame_fix R3 regs 18%bv); [rewrite E18; apply zw_u|].
  apply (frame_fix R3 regs 19%bv); [rewrite E19; apply zw_u|].
  apply (frame_fix R3 regs 20%bv); [rewrite E20; apply zw_u|].
  apply (frame_fix R3 regs 21%bv); [rewrite E21; apply zw_u|].
  apply (frame_fix R3 regs 22%bv); [rewrite E22; apply zw_u|].
  apply (frame_fix R3 regs 23%bv); [rewrite E23; apply zw_u|].
  apply (frame_fix R3 regs 24%bv); [rewrite E24; apply zw_u|].
  intros r Hr. rewrite (Hfr3 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.

End Walk.


End FXG.

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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 TreesRod6 TreesApi6 CompressBlk6_1 SendTree6_1.
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
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | rewrite wrap16_mod', wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity
                          | apply wrap16_id'; lia
                          | apply land16_wrap16; first [apply mod16_congr; lia | apply mod16_up; lia] ].
Local Ltac vrange := first [ apply pb_range | lia | apply Z.mod_pos_bound; lia | apply land16_range ].
Local Ltac rbm := first [ assumption | apply szwrap16_mod; assumption | apply szwrap16_mod; lia
                        | lazymatch goal with H : RBr _ _ _ |- _ => exact H end ].

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

Local Ltac dregs H := destruct H as (HK & P8 & P15 & P14 & P18 & P9 & P19 & P20 & P21).


Definition RREGS (R : bvmap 5 word) (n c nl j : Z) (s : deflate_state) : Prop :=
  KREGS R /\ getr R 8 = zw c /\ getr R 15 = zw (n + 1) /\ getr R 14 = zw nl /\ getr R 18 = zw j
  /\ getr R 9 = zw (S + 2748 + 4 * c) /\ getr R 20 = zw (ds_bi_valid s).

Local Ltac rregs H := destruct H as (HK & P8 & P15 & P14 & P18 & P9 & P20).

Definition DP (plp : list (Z * expr)) : list (Z * expr) :=
  KP ++ [(8, EVar 39); (15, EAdd (EVar 38) (ELit 1)); (14, EVar 40); (18, EAdd (EVar 41) (ELit 1)); (9, EVar 41);
         (19, EVar 43); (20, EVar 44)] ++ plp.
Definition RP : list (Z * expr) :=
  KP ++ [(8, EVar 39); (15, EAdd (EVar 38) (ELit 1)); (14, EVar 40); (18, EVar 46);
         (9, EAdd (EAdd (EVar 32) (ELit 2748)) (EShl (EVar 39) 2)); (20, EVar 35)].

Lemma rep0 : forall regs m0 m s n pl c nl k mx mn,
  CI m0 m s -> DREGS regs n pl c nl k mx mn -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= nl < 65536 ->
  0 <= k -> k + 1 < mn -> mn < 10 -> 0 <= mx <= 138 ->
  exists R,
    msteps s6_segs (mkst regs (0x1c7bc : word) m s6_rom) (mkst R (0x1c828 : word) m s6_rom)
    /\ RREGS R n c nl (k + 1) s
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m0 m s n pl c nl k mx mn (HB & HPu & HAG) HD Hn Hc Hnl Hk Hkm Hmn Hmx.
  open_br HB HPu. dregs HD. kd HK.
  run 30%nat [false] [RVal (EVar 35)] (DP [])
      [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; k; 0; mx; mn; SP; 0; 0].
  exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold RREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
Qed.

Lemma repi : forall regs m0 m s n c nl j,
  CI m0 m s -> RREGS regs n c nl j s -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= nl < 65536 -> 1 <= j < 10 ->
  sb_room PBL s (BL c) ->
  let s' := send_bits s (BC c) (BL c) in
  exists R m',
    msteps s6_segs (mkst regs (0x1c828 : word) m s6_rom)
           (mkst R (if j - 1 =? 0 then (0x1c858 : word) else (0x1c828 : word)) m' s6_rom)
    /\ CI m0 m' s'
    /\ (RREGS R n c nl (j - 1) s'
        /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)).
Proof.
  intros regs m0 m s n c nl j (HB & HPu & HAG) HRr Hn Hc Hnl Hj Hroom. cbv zeta.
  open_br HB HPu. rregs HRr. kd HK.
  pose proof (HbC c ltac:(lia)) as Vfc. pose proof (HbL c ltac:(lia)) as Vdl.
  assert (Efc : pb (ds_bl_tree_fc ds) c = BC c) by (apply pb_small; exact Vfc).
  assert (Edl : pb (ds_bl_tree_dl ds) c = BL c) by (apply pb_small; lia).
  unfold sb_room, Buf_size in Hroom.
  destruct (Z.ltb_spec (16 - BL c) (ds_bi_valid s)) as [CF|CF];
    [specialize (Hroom ltac:(unfold Buf_size; lia))|]; destruct (Z.eqb_spec (j - 1) 0) as [Ej|Ej].
  - run 80%nat [true; true]
        [RVal (EApp1 2 (EVar 39)); RVal (EApp1 1 (EVar 39)); RVal (EVar 47); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)]
        RP [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; j; ds_bi_buf s].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_flush ltac:(nf; rewrite ?Efc, ?Edl))
      ltac:(split; [| fr_weak Hfr]; unfold RREGS; split; [kregs HR Hfr|]; repeat split;
            first [ bv_flush (20%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | reg1 HR Hfr ]).
  - run 80%nat [true; false]
        [RVal (EApp1 2 (EVar 39)); RVal (EApp1 1 (EVar 39)); RVal (EVar 47); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)]
        RP [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; j; ds_bi_buf s].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_flush ltac:(nf; rewrite ?Efc, ?Edl))
      ltac:(split; [| fr_weak Hfr]; unfold RREGS; split; [kregs HR Hfr|]; repeat split;
            first [ bv_flush (20%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | reg1 HR Hfr ]).
  - run 80%nat [false; false]
        [RVal (EApp1 2 (EVar 39)); RVal (EApp1 1 (EVar 39)); RVal (EVar 47)]
        RP [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; j; ds_bi_buf s].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_keep ltac:(nf; rewrite ?Efc, ?Edl))
      ltac:(split; [| fr_weak Hfr]; unfold RREGS; split; [kregs HR Hfr|]; repeat split;
            first [ bv_keep (20%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | reg1 HR Hfr ]).
  - run 80%nat [false; true]
        [RVal (EApp1 2 (EVar 39)); RVal (EApp1 1 (EVar 39)); RVal (EVar 47)]
        RP [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; j; ds_bi_buf s].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_keep ltac:(nf; rewrite ?Efc, ?Edl))
      ltac:(split; [| fr_weak Hfr]; unfold RREGS; split; [kregs HR Hfr|]; repeat split;
            first [ bv_keep (20%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | reg1 HR Hfr ]).
Qed.

Lemma rep_loop : forall jn (j : Z) regs m0 m s n c nl,
  j = Z.of_nat jn -> (1 <= jn)%nat -> j < 10 ->
  CI m0 m s -> RREGS regs n c nl j s -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= nl < 65536 ->
  sbs_ok PBL s (repeat (BC c, BL c) jn) ->
  exists R m',
    msteps s6_segs (mkst regs (0x1c828 : word) m s6_rom) (mkst R (0x1c858 : word) m' s6_rom)
    /\ CI m0 m' (sbs_run s (repeat (BC c, BL c) jn))
    /\ RREGS R n c nl 0 (sbs_run s (repeat (BC c, BL c) jn))
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction jn as [|jn IH]; intros j regs m0 m s n c nl Hj Hjn Hj10 HC HRr Hn Hc Hnl Hok; [lia|].
  cbn [repeat sbs_ok sbs_run] in Hok |- *. destruct Hok as (_ & Hroom & Hok).
  destruct (repi regs m0 m s n c nl j HC HRr Hn Hc Hnl ltac:(lia) Hroom) as (R1 & m1 & Hms1 & HC1 & HR1 & Hfr1).
  destruct jn as [|jn'].
  - replace (j - 1 =? 0) with true in Hms1 by (symmetry; apply Z.eqb_eq; lia).
    replace (j - 1) with 0 in HR1 by lia. cbn [repeat sbs_run].
    exists R1, m1. split; [exact Hms1|]. split; [exact HC1|]. split; [exact HR1 | exact Hfr1].
  - replace (j - 1 =? 0) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
    destruct (IH (j - 1) R1 m0 m1 _ n c nl ltac:(lia) ltac:(lia) ltac:(lia) HC1 HR1 Hn Hc Hnl Hok)
      as (R2 & m2 & Hms2 & HC2 & HR2 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HC2|]. split; [exact HR2|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Lemma repx : forall regs m n c nl j s,
  RREGS regs n c nl j s -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= nl < 65536 -> 0 <= j < 10 -> 0 <= ds_bi_valid s <= 16 ->
  exists R,
    msteps s6_segs (mkst regs (0x1c858 : word) m s6_rom) (mkst R (TGT nl) m s6_rom)
    /\ GREGS R n c nl
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m n c nl j s HRr Hn Hc Hnl Hj Hbv. rregs HRr. kd HK.
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'. pose proof Hsp as Hsp'. pose proof Htt as Htt'.
  pose proof Hmc as Hmc'. unfold TGT.
  destruct (Z.eqb_spec nl 0) as [Enl|Enl].
  - run 20%nat [true] NoReads RP [S; 0; 0; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; j; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold GREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
  - run 20%nat [false] NoReads RP [S; 0; 0; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; j; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold GREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
Qed.

Lemma rep_arm : forall regs m0 m s n pl c nl k mx mn,
  CI m0 m s -> DREGS regs n pl c nl k mx mn -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= nl < 65536 ->
  0 <= k -> k + 1 < mn -> mn < 10 -> 0 <= mx <= 138 ->
  sbs_ok PBL s (repeat (BC c, BL c) (Z.to_nat (k + 1))) ->
  let s' := sbs_run s (repeat (BC c, BL c) (Z.to_nat (k + 1))) in
  exists R m',
    msteps s6_segs (mkst regs (0x1c7bc : word) m s6_rom) (mkst R (TGT nl) m' s6_rom)
    /\ CI m0 m' s'
    /\ GREGS R n c nl
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m0 m s n pl c nl k mx mn HC HD Hn Hc Hnl Hk Hkm Hmn Hmx Hok. cbv zeta.
  destruct (rep0 regs m0 m s n pl c nl k mx mn HC HD Hn Hc Hnl Hk Hkm Hmn Hmx) as (R1 & Hms1 & HR1 & Hfr1).
  destruct (rep_loop (Z.to_nat (k + 1)) (k + 1) R1 m0 m s n c nl ltac:(lia) ltac:(lia) ltac:(lia) HC HR1 Hn Hc Hnl Hok)
    as (R2 & m2 & Hms2 & HC2 & HR2 & Hfr2).
  assert (Hbv2 : 0 <= ds_bi_valid (sbs_run s (repeat (BC c, BL c) (Z.to_nat (k + 1)))) <= 16).
  { destruct HC2 as (_ & (HBI & _) & _). destruct HBI as (Hbv & _). exact Hbv. }
  destruct (repx R2 m2 n c nl 0 _ HR2 Hn Hc Hnl ltac:(lia) Hbv2) as (R3 & Hms3 & HG3 & Hfr3).
  exists R3, m2. split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms3]. }
  split; [exact HC2|]. split; [exact HG3|].
  intros r Hr. rewrite (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.
End Walk.
End FXG.

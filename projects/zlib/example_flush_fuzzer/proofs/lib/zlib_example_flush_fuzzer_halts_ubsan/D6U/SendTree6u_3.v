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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u TreesRod6u TreesApi6u TrApi6u CompressBlk6u_1 SendTree6u_1 SendTree6u_2.
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
Local Abbreviation SP := (sp - 112).
Local Abbreviation BRm := (BR6u F mem0 S p PBL).
Local Abbreviation L i := (Len ds t i).
Local Abbreviation BC c := (arr_get (ds_bl_tree_fc ds) c).
Local Abbreviation BL c := (arr_get (ds_bl_tree_dl ds) c).

Hypothesis HH : STH F mem0 mem S p PBL ds ra sp t mc.

Let Hret : ret_ok ra := sth_ret _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := sth_L _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hfr112 : call_frame F mem S PB PBL sp 112 := sth_fr _ _ _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := sth_br _ _ _ _ _ _ _ _ _ _ _ HH.
Let Ht : t = TL \/ t = TD := sth_t _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hmc : 0 <= mc /\ mc + 1 < tsize t := sth_mc _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hlen : forall i, 0 <= i <= mc -> 0 <= Len ds t i <= 15 := sth_len _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hdl : forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl ds t) i < 65536 := sth_dl _ _ _ _ _ _ _ _ _ _ _ HH.
Let HbC : forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_fc ds) c < 2 ^ 15 := sth_bc _ _ _ _ _ _ _ _ _ _ _ HH.
Let HbL : forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl ds) c < 16 := sth_bl _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hbinv : BINV PBL ds := sth_binv _ _ _ _ _ _ _ _ _ _ _ HH.
Let HPBL : 0 < PBL := sth_pbl _ _ _ _ _ _ _ _ _ _ _ HH.
Let HUB : UBT S p := sth_ub _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hsp : 112 <= sp <= 2 ^ 63 := proj1 Hfr112.
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Local Abbreviation PURE := (SendTree6u_1.PURE PBL ds).
Local Abbreviation GI := (SendTree6u_1.GI S p PBL).
Local Abbreviation CI := (SendTree6u_1.CI F mem0 S p PBL ds).
Local Abbreviation PURE_send := (SendTree6u_1.PURE_send PBL ds).
Local Abbreviation PURE_Len := (SendTree6u_1.PURE_Len PBL ds t).
Local Abbreviation PURE_blc := (SendTree6u_1.PURE_blc PBL ds).
Local Abbreviation KREGS := (SendTree6u_1.KREGS S sp t mc).
Local Abbreviation HREGS := (SendTree6u_1.HREGS S sp t mc).
Local Abbreviation DREGS := (SendTree6u_1.DREGS S sp t mc).
Local Abbreviation GREGS := (SendTree6u_1.GREGS S sp t mc).
Local Abbreviation JREGS := (SendTree6u_1.JREGS S sp t mc).
Local Abbreviation FRAME := (SendTree6u_1.FRAME sp).
Local Abbreviation cnts0 := (SendTree6u_1.cnts0 ds t).
Local Abbreviation SNEXT := (SendTree6u_1.SNEXT mc).
Local Abbreviation Htt2 := (SendTree6u_1.Htt2 F mem0 mem S p PBL ds ra sp t mc HH).
Local Abbreviation HT2 := (SendTree6u_1.HT2 F mem0 mem S p PBL ds ra sp t mc HH).
Local Abbreviation DP := SendTree6u_2.DP.


Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [SendTree6u_1.stF].

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
            | change (2 ^ 3) with 8 in *; change (2 ^ 1) with 2 in *; zcond_close
            | nf; match goal with H : zaluw ALU_SRL _ _ = 0 |- _ => rewrite !H end; zcond_close
            | nf; apply srl_check0u; lia
            | nf; symex_read_auto
            | nf; symex_store_auto
            | nf; symex_sok_auto
            | intros; nf; apply pb_range ].

Local Ltac run_with vb fuel dirs rds pins pv :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in vb in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs stC fuel dirs rdv pinsv vbv NoRegions pv NoVals (SendTree6u_1.stF ds t) F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
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
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex_dbg s6u_segs stC fuel dirs rdv pinsv vbv NoRegions pv (mkst regs pc m s6u_rom)
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
  pose proof (arrays_dl s6u_segs _ _ _ t Har) as TDl; pose proof (arrays_fc s6u_segs _ _ _ TB Har) as BLc;
  pose proof (arrays_dl s6u_segs _ _ _ TB Har) as BLd; cbn [toff tsize] in BLc, BLd;
  rewrite ?tree_dl_set_bi_buf in TDl; rewrite ?tree_fc_set_bi_buf in BLc; rewrite ?tree_dl_set_bi_buf in BLd;
  try rewrite (P3 t) in TDl; try rewrite (P2 TB) in BLc; try rewrite (P3 TB) in BLd;
  cbn [tree_fc tree_dl] in BLc, BLd;
  replace (S + 2748 + 2) with (S + 2750) in BLd by lia;
  clear Hsc Har;
  let Hsp' := fresh "Hsp'" in pose proof Hsp as Hsp';
  let Htt' := fresh "Htt'" in pose proof Htt as Htt';
  let Hmc' := fresh "Hmc'" in pose proof Hmc as Hmc';
  let HfS := fresh "HfS" in let HfP := fresh "HfP" in
  pose proof Hfr112 as Hcf'; destruct Hcf' as (_ & _ & _ & HfS & HfP); unfold dsl_SIZE in HfS, HfP;
  pose proof Htt2 as Htt2'; open_ubt HUB.

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
                  | f_equal; change (2 ^ 3) with 8; assumption
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
  | first [reflexivity | vnorm; apply srl_eq'u; [vrange | vwrap | lia]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; lia] ].
Local Ltac rb_flush r HR vnorm :=
  unfold RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_buf;
  vnorm; apply srl_eq'u; [vrange | vwrap | lia].
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

Local Ltac kd H := destruct H as (K10 & K11 & K12 & K13 & K16 & K17 & K5 & K6 & K7 & K28 & K29 & K30 & K31 & K20 & K21 & K22 & K2).

Local Ltac dregs H := destruct H as (HK & P23 & P14 & P15 & P25 & P24 & P26 & P27 & P1).


Definition MREGS (R : bvmap 5 word) (n c nl cnt : Z) : Prop :=
  KREGS R /\ getr R 23 = zw c /\ getr R 14 = zw (n + 1) /\ getr R 15 = zw nl /\ getr R 24 = zw cnt.
Local Ltac mregs H := destruct H as (HK & P23 & P14 & P15 & P24).

Definition XREGS (R : bvmap 5 word) (n c nl cnt : Z) (s : deflate_state) : Prop :=
  KREGS R /\ getr R 23 = zw c /\ getr R 14 = zw (n + 1) /\ getr R 15 = zw nl
  /\ RBr 26%bv R s /\ getr R 25 = zw (ds_bi_valid s) /\ getr R 24 = zw cnt /\ getr R 8 = zw (ds_bi_valid s).
Local Ltac xregs H := destruct H as (HK & P23 & P14 & P15 & HRB & P25 & P24 & P8).

Definition MP (plp : list (Z * expr)) : list (Z * expr) :=
  KP ++ [(23, EVar 39); (14, EAdd (EVar 38) (ELit 1)); (15, EVar 40); (24, EVar 46)] ++ plp.
Definition XP : list (Z * expr) :=
  KP ++ [(23, EVar 39); (14, EAdd (EVar 38) (ELit 1)); (15, EVar 40); (26, EVar 48); (25, EVar 35); (24, EVar 46); (8, EVar 35)].


Lemma ec_blk : forall regs m0 m s n pl c nl k mx mn,
  CI m0 m s -> DREGS regs n pl c nl k mx mn -> 0 <= n <= mc -> 1 <= c <= 15 -> 0 <= nl < 65536 ->
  0 <= k -> mn <= k + 1 -> k + 1 <= 138 -> 0 <= mn < 10 -> 0 <= mx <= 138 -> (pl = -1 \/ 0 <= pl <= 15) -> pl <> c ->
  sb_room PBL s (BL c) ->
  let s' := send_bits s (BC c) (BL c) in
  exists R m',
    msteps s6u_segs (mkst regs (0x1e374 : word) m s6u_rom) (mkst R (0x1e90c : word) m' s6u_rom)
    /\ CI m0 m' s'
    /\ (MREGS R n c nl k
        /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)).
Proof.
  intros regs m0 m s n pl c nl k mx mn (HB & HPu & HAG) HD Hn Hc Hnl Hk Hkm Hk1 Hmn Hmx Hpl Hplc Hroom. cbv zeta.
  open_br HB HPu. dregs HD. kd HK.
  pose proof (HbC c ltac:(lia)) as Vfc. pose proof (HbL c ltac:(lia)) as Vdl.
  assert (Efc : pb (ds_bl_tree_fc ds) c = BC c) by (apply pb_small; lia).
  assert (Edl : pb (ds_bl_tree_dl ds) c = BL c) by (apply pb_small; lia).
  assert (Hchk : zaluw ALU_SRL (pb (ds_bl_tree_fc ds) c) (Z.lxor (ds_bi_valid s) (-1)) = 0) by (apply srl_check0u; lia).
  unfold sb_room, Buf_size in Hroom.
  destruct (Z.ltb_spec (16 - BL c) (ds_bi_valid s)) as [CF|CF];
    [specialize (Hroom ltac:(unfold Buf_size; lia))|]; destruct Hpl as [Hpl|Hpl]; try subst pl.
  - run 120%nat [true; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]
        [RVal (EApp1 2 (EVar 39)); RVal (EVar 35); RVal (EApp1 1 (EVar 39)); RVal (EVar 47); RVal (EVar 34); RVal (EVar 33)]
        (DP [(1, ELit 18446744073709551615)]) [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; k; 0; mx; mn; SP; 0; ds_bi_buf s].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_flush ltac:(nf; rewrite ?Efc, ?Edl))
      ltac:(split; [| fr_weak Hfr]; unfold MREGS; split; [kregs HR Hfr|]; repeat split; reg1 HR Hfr).
  - run 120%nat [true; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]
        [RVal (EApp1 2 (EVar 39)); RVal (EVar 35); RVal (EApp1 1 (EVar 39)); RVal (EVar 47); RVal (EVar 34); RVal (EVar 33)]
        (DP [(1, EVar 42)]) [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; k; pl; mx; mn; SP; 0; ds_bi_buf s].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_flush ltac:(nf; rewrite ?Efc, ?Edl))
      ltac:(split; [| fr_weak Hfr]; unfold MREGS; split; [kregs HR Hfr|]; repeat split; reg1 HR Hfr).
  - run 80%nat [true; false; true; false; false; false; true; false; false; false]
        [RVal (EApp1 2 (EVar 39)); RVal (EVar 35); RVal (EApp1 1 (EVar 39)); RVal (EVar 47)]
        (DP [(1, ELit 18446744073709551615)]) [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; k; 0; mx; mn; SP; 0; ds_bi_buf s].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_keep ltac:(nf; rewrite ?Efc, ?Edl))
      ltac:(split; [| fr_weak Hfr]; unfold MREGS; split; [kregs HR Hfr|]; repeat split; reg1 HR Hfr).
  - run 80%nat [true; false; true; false; false; false; true; false; false; false]
        [RVal (EApp1 2 (EVar 39)); RVal (EVar 35); RVal (EApp1 1 (EVar 39)); RVal (EVar 47)]
        (DP [(1, EVar 42)]) [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; k; pl; mx; mn; SP; 0; ds_bi_buf s].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_keep ltac:(nf; rewrite ?Efc, ?Edl))
      ltac:(split; [| fr_weak Hfr]; unfold MREGS; split; [kregs HR Hfr|]; repeat split; reg1 HR Hfr).
Qed.

Lemma ep_blk : forall regs m0 m s n c nl k mx mn,
  CI m0 m s -> DREGS regs n c c nl k mx mn -> 0 <= n <= mc -> 1 <= c <= 15 -> 0 <= nl < 65536 ->
  0 <= k -> mn <= k + 1 -> k + 1 <= 138 -> 0 <= mn < 10 -> 0 <= mx <= 138 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1e374 : word) m s6u_rom) (mkst R (0x1e90c : word) m s6u_rom)
    /\ MREGS R n c nl (k + 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m0 m s n c nl k mx mn (HB & HPu & HAG) HD Hn Hc Hnl Hk Hkm Hk1 Hmn Hmx.
  open_br HB HPu. dregs HD. kd HK.
  run 40%nat [true; false; false; true] NoReads
      (DP [(1, EVar 39)]) [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; k; 0; mx; mn; SP; 0; 0].
  exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold MREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
Qed.


Definition X2 (s : deflate_state) : word := if 15 <=? ds_bi_valid s then (0x1e9ec : word) else (0x1eac8 : word).

Lemma r36a : forall regs m0 m s n c nl cnt,
  CI m0 m s -> MREGS regs n c nl cnt -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= nl < 65536 -> 0 <= cnt < 200 ->
  sb_room PBL s (BL 16) ->
  let s' := send_bits s (BC 16) (BL 16) in
  exists R m',
    msteps s6u_segs (mkst regs (0x1e90c : word) m s6u_rom) (mkst R (X2 s') m' s6u_rom)
    /\ CI m0 m' s'
    /\ (XREGS R n c nl cnt s'
        /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)).
Proof.
  intros regs m0 m s n c nl cnt (HB & HPu & HAG) HM Hn Hc Hnl Hcnt Hroom. cbv zeta.
  open_br HB HPu. mregs HM. kd HK.
  pose proof (HbC 16 ltac:(lia)) as Vfc. pose proof (HbL 16 ltac:(lia)) as Vdl.
  assert (Efc : pb (ds_bl_tree_fc ds) 16 = BC 16) by (apply pb_small; lia).
  assert (Edl : pb (ds_bl_tree_dl ds) 16 = BL 16) by (apply pb_small; lia).
  assert (Hchk : zaluw ALU_SRL (pb (ds_bl_tree_fc ds) 16) (Z.lxor (ds_bi_valid s) (-1)) = 0) by (apply srl_check0u; lia).
  unfold sb_room, Buf_size in Hroom. unfold X2.
  destruct (Z.ltb_spec (16 - BL 16) (ds_bi_valid s)) as [CF|CF];
    [specialize (Hroom ltac:(unfold Buf_size; lia))|].
  - assert (Ebv : ds_bi_valid (send_bits s (BC 16) (BL 16)) = ds_bi_valid s + BL 16 - 16)
      by (rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
    rewrite Ebv. destruct (Z.leb_spec 15 (ds_bi_valid s + BL 16 - 16)) as [C2|C2].
    + run 120%nat [false; false; false; false; false; false; false; false; false; false; false; false; false]
          [RVal (EApp1 2 (ELit 16)); RVal (EVar 35); RVal (EApp1 1 (ELit 16)); RVal (EVar 47); RVal (EVar 34); RVal (EVar 33)]
          (MP []) [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; cnt; ds_bi_buf s].
      site_fin Hms HR Hfr HB HPu HAG ltac:(st_flush ltac:(nf; rewrite ?Efc, ?Edl))
        ltac:(split; [| fr_weak Hfr]; unfold XREGS; split; [kregs HR Hfr|]; repeat split;
              first [ rb_flush (26%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | bv_flush (25%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl)
                    | bv_flush (8%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | reg1 HR Hfr ]).
    + run 120%nat [false; false; false; false; false; false; false; false; false; false; false; false; true]
          [RVal (EApp1 2 (ELit 16)); RVal (EVar 35); RVal (EApp1 1 (ELit 16)); RVal (EVar 47); RVal (EVar 34); RVal (EVar 33)]
          (MP []) [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; cnt; ds_bi_buf s].
      site_fin Hms HR Hfr HB HPu HAG ltac:(st_flush ltac:(nf; rewrite ?Efc, ?Edl))
        ltac:(split; [| fr_weak Hfr]; unfold XREGS; split; [kregs HR Hfr|]; repeat split;
              first [ rb_flush (26%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | bv_flush (25%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl)
                    | bv_flush (8%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | reg1 HR Hfr ]).
  - assert (Ebv : ds_bi_valid (send_bits s (BC 16) (BL 16)) = ds_bi_valid s + BL 16)
      by (rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
    rewrite Ebv. destruct (Z.leb_spec 15 (ds_bi_valid s + BL 16)) as [C2|C2].
    + run 80%nat [false; true; false; true]
          [RVal (EApp1 2 (ELit 16)); RVal (EVar 35); RVal (EApp1 1 (ELit 16)); RVal (EVar 47)]
          (MP []) [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; cnt; ds_bi_buf s].
      site_fin Hms HR Hfr HB HPu HAG ltac:(st_keep ltac:(nf; rewrite ?Efc, ?Edl))
        ltac:(split; [| fr_weak Hfr]; unfold XREGS; split; [kregs HR Hfr|]; repeat split;
              first [ rb_keep (26%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | bv_keep (25%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl)
                    | bv_keep (8%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | reg1 HR Hfr ]).
    + run 80%nat [false; true; false; false]
          [RVal (EApp1 2 (ELit 16)); RVal (EVar 35); RVal (EApp1 1 (ELit 16)); RVal (EVar 47)]
          (MP []) [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; cnt; ds_bi_buf s].
      site_fin Hms HR Hfr HB HPu HAG ltac:(st_keep ltac:(nf; rewrite ?Efc, ?Edl))
        ltac:(split; [| fr_weak Hfr]; unfold XREGS; split; [kregs HR Hfr|]; repeat split;
              first [ rb_keep (26%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | bv_keep (25%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl)
                    | bv_keep (8%bv : reg) HR ltac:(nf; rewrite ?Efc, ?Edl) | reg1 HR Hfr ]).
Qed.


Lemma r36k : forall regs m0 m s n c nl cnt,
  CI m0 m s -> XREGS regs n c nl cnt s -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= nl < 65536 -> 3 <= cnt < 200 ->
  0 <= ds_bi_valid s <= 14 ->
  let s' := send_bits s (cnt - 3) 2 in
  exists R m',
    msteps s6u_segs (mkst regs (0x1eac8 : word) m s6u_rom) (mkst R (TGT nl) m' s6u_rom)
    /\ CI m0 m' s'
    /\ (GREGS R n c nl
        /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)).
Proof.
  intros regs m0 m s n c nl cnt (HB & HPu & HAG) HX Hn Hc Hnl Hcnt Hbv. cbv zeta.
  open_br HB HPu. xregs HX. kd HK.
  pose proof (u64_range (getr regs 26)) as U26.
  unfold TGT. destruct (Z.eqb_spec nl 0) as [Enl|Enl].
  - subst nl. run 60%nat [false; false] NoReads XP
        [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; 0; 0; 0; 0; 0; SP; cnt; 0; bv_unsigned (getr regs 26)].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_keep nf)
      ltac:(split; [| fr_weak Hfr]; unfold GREGS; split; [kregs HR Hfr|]; repeat split; reg1 HR Hfr).
  - run 60%nat [false; true] NoReads XP
        [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; cnt; 0; bv_unsigned (getr regs 26)].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_keep nf)
      ltac:(split; [| fr_weak Hfr]; unfold GREGS; split; [kregs HR Hfr|]; repeat split; reg1 HR Hfr).
Qed.

Lemma r36f : forall regs m0 m s n c nl cnt,
  CI m0 m s -> XREGS regs n c nl cnt s -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= nl < 65536 -> 3 <= cnt < 200 ->
  15 <= ds_bi_valid s <= 16 -> ds_pending s + 2 <= PBL ->
  let s' := send_bits s (cnt - 3) 2 in
  exists R m',
    msteps s6u_segs (mkst regs (0x1e9ec : word) m s6u_rom) (mkst R (TGT nl) m' s6u_rom)
    /\ CI m0 m' s'
    /\ (GREGS R n c nl
        /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)).
Proof.
  intros regs m0 m s n c nl cnt (HB & HPu & HAG) HX Hn Hc Hnl Hcnt Hbv Hroom. cbv zeta.
  open_br HB HPu. xregs HX. kd HK.
  pose proof (u64_range (getr regs 26)) as U26.
  assert (Emod : (cnt + 65533) mod 2 ^ 16 = cnt - 3) by (rewrite (mod16_up (cnt + 65533) (cnt - 3)) by lia; apply Z.mod_small; lia).
  assert (Hchk2 : zaluw ALU_SRL ((cnt + 65533) mod 2 ^ 16) (Z.lxor (ds_bi_valid s) (-1)) = 0) by (rewrite Emod; apply srl_check0u; lia).
  unfold TGT. destruct (Z.eqb_spec nl 0) as [Enl|Enl].
  - subst nl. run 120%nat [false; false; false; false; false; false; false; false; false; false; true; false]
        [RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] XP
        [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; 0; 0; 0; 0; 0; SP; cnt; 0; bv_unsigned (getr regs 26)].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_flush nf)
      ltac:(split; [| fr_weak Hfr]; unfold GREGS; split; [kregs HR Hfr|]; repeat split; reg1 HR Hfr).
  - run 120%nat [false; false; false; false; false; false; false; false; false; false; true; true]
        [RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] XP
        [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; nl; 0; 0; 0; 0; SP; cnt; 0; bv_unsigned (getr regs 26)].
    site_fin Hms HR Hfr HB HPu HAG ltac:(st_flush nf)
      ltac:(split; [| fr_weak Hfr]; unfold GREGS; split; [kregs HR Hfr|]; repeat split; reg1 HR Hfr).
Qed.


Local Ltac frc3 a b c := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr); exact (c r Hr).

Lemma r36b : forall regs m0 m s1 n c nl cnt,
  CI m0 m s1 -> XREGS regs n c nl cnt s1 -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= nl < 65536 -> 3 <= cnt < 200 ->
  sb_room PBL s1 2 ->
  exists R m',
    msteps s6u_segs (mkst regs (X2 s1) m s6u_rom) (mkst R (TGT nl) m' s6u_rom)
    /\ CI m0 m' (send_bits s1 (cnt - 3) 2)
    /\ (GREGS R n c nl /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)).
Proof.
  intros regs m0 m s1 n c nl cnt HC HX Hn Hc Hnl Hcnt Hroom.
  pose proof HC as (_ & (HBI & _) & _). destruct HBI as (Hbv & Hbb & Hpd).
  unfold sb_room, Buf_size in Hroom. unfold X2.
  destruct (Z.leb_spec 15 (ds_bi_valid s1)) as [C2|C2].
  - exact (r36f regs m0 m s1 n c nl cnt HC HX Hn Hc Hnl Hcnt ltac:(lia) ltac:(lia)).
  - exact (r36k regs m0 m s1 n c nl cnt HC HX Hn Hc Hnl Hcnt ltac:(lia)).
Qed.

Lemma e_arm : forall regs m0 m s n pl c nl k mx mn,
  CI m0 m s -> DREGS regs n pl c nl k mx mn -> 0 <= n <= mc -> 1 <= c <= 15 -> 0 <= nl < 65536 ->
  0 <= k -> mn <= k + 1 -> k + 1 <= 138 -> 0 <= mn < 10 -> 0 <= mx <= 138 -> (pl = -1 \/ 0 <= pl <= 15) ->
  (c <> pl -> 3 <= k) -> (c = pl -> 2 <= k) ->
  let cs := (if negb (c =? pl) then [(BC c, BL c)] else [])
              ++ [(BC 16, BL 16); ((if negb (c =? pl) then k else k + 1) - 3, 2)] in
  sbs_ok PBL s cs ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1e374 : word) m s6u_rom) (mkst R (TGT nl) m' s6u_rom)
    /\ CI m0 m' (sbs_run s cs)
    /\ GREGS R n c nl
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m0 m s n pl c nl k mx mn HC HD Hn Hc Hnl Hk Hkm Hk1 Hmn Hmx Hpl Hk3 Hk2. cbv zeta.
  destruct (Z.eqb_spec c pl) as [Ecp|Ecp]; cbn [negb app sbs_ok sbs_run]; intros Hok.
  - specialize (Hk2 Ecp). subst pl. destruct Hok as (_ & Hr1 & _ & Hr2 & _).
    destruct (ep_blk regs m0 m s n c nl k mx mn HC HD Hn Hc Hnl Hk Hkm Hk1 Hmn Hmx) as (R1 & Hms1 & HM1 & Hfr1).
    destruct (r36a R1 m0 m s n c nl (k + 1) HC HM1 Hn ltac:(lia) Hnl ltac:(lia) Hr1) as (R2 & m2 & Hms2 & HC2 & HX2 & Hfr2).
    destruct (r36b R2 m0 m2 _ n c nl (k + 1) HC2 HX2 Hn ltac:(lia) Hnl ltac:(lia) Hr2) as (R3 & m3 & Hms3 & HC3 & HG3 & Hfr3).
    exists R3, m3. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms3]. }
    split; [exact HC3|]. split; [exact HG3|]. frc3 Hfr3 Hfr2 Hfr1.
  - specialize (Hk3 Ecp). destruct Hok as (_ & Hr0 & _ & Hr1 & _ & Hr2 & _).
    destruct (ec_blk regs m0 m s n pl c nl k mx mn HC HD Hn Hc Hnl Hk Hkm Hk1 Hmn Hmx Hpl ltac:(lia) Hr0)
      as (R1 & m1 & Hms1 & HC1 & HM1 & Hfr1).
    destruct (r36a R1 m0 m1 _ n c nl k HC1 HM1 Hn ltac:(lia) Hnl ltac:(lia) Hr1) as (R2 & m2 & Hms2 & HC2 & HX2 & Hfr2).
    destruct (r36b R2 m0 m2 _ n c nl k HC2 HX2 Hn ltac:(lia) Hnl ltac:(lia) Hr2) as (R3 & m3 & Hms3 & HC3 & HG3 & Hfr3).
    exists R3, m3. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms3]. }
    split; [exact HC3|]. split; [exact HG3|]. frc3 Hfr3 Hfr2 Hfr1.
Qed.
End Walk.
End FXG.

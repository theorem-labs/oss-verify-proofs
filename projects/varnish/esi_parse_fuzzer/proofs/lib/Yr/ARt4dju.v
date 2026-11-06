(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtSoqz ARtSnjd ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt4z85.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt4z85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)

Definition keep (P : Prop) : Prop := P.

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac eqz := first [ reflexivity | lia | cbn; rewrite ?Nat.sub_0_r; first [reflexivity | plia] ].

(* [comment removed for export] *)
Ltac cells_by H :=
  first [ exact H
        | try unfold recycle_frame; lazymatch goal with |- rw_cells _ _ ?A ?cs =>
            lazymatch type of H with rw_cells _ _ ?A' ?cs' =>
              (replace A with A' by lia || idtac); replace cs with cs'; [exact H | repeat first [reflexivity | f_equal; try lia] ]
            end end ].

Section Rec.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (sp ra gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (q qmin hi gl gqb lo : Z) (bs : list (Z * Z)) (Q : machine_state -> Prop) (k0 : nat).
  Let usp := bv_unsigned sp.
  Let gn := Z.of_nat (length bs).
  Let L := (usp - 80, usp) :: (q + 152, q + 156) :: (q + 160, q + 192) :: bivls (firstn k0 bs).

  Hypotheses (LOLE : lo <= usp - 80) (CEIL : alloc_ceiling <= lo) (LO0 : 0 <= lo) (USP : usp < 2^64) (UAL : usp mod 16 = 0)
             (Q0 : 0x10000 <= q) (Q1 : q + 192 <= 0x60a000) (QAL : q mod 8 = 0)
             (HIR : 0 <= hi < 2^15) (QMN : 0 <= qmin < 2^64) (GQ0 : 0 <= gqb) (GQH : gqb * 100 < 2^64) (GNH : gn < 2^24) (GLR : 0 <= gl < 2^64)
             (SUMLE : lsum bs <= gqb) (SUMSTOP : gqb - lsum bs <= qmin) (WF : bwf bs)
             (EQk : k0 = npop qmin gqb bs).
  Hypothesis KK : forall (t0' t1' t2' a4' a5' a6' a7' : word) (m' : word -> option byte),
        rw_cells rsegs m' (usp + -80)
                 (recycle_frame (Z.of_nat k0) (if (k0 =? 0)%nat then 0 else baddr bs 0) (if (k0 =? 0)%nat then 0 else baddr bs (k0 - 1))
                                (lsum (firstn k0 bs)) s4 s3 s2 s1 s0 ra) ->
        rw_cells rsegs m' (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 hi)] ->
        rw_cells rsegs m' (q + 160) [C8 (Z_to_bv 64 (gn - Z.of_nat k0)); C8 (Z_to_bv 64 (baddr bs k0));
                                     C8 (Z_to_bv 64 (if ((k0 =? length bs)%nat && (0 <? k0)%nat)%bool then 0 else gl));
                                     C8 (Z_to_bv 64 (gqb - lsum (firstn k0 bs)))] ->
        bchain_cut m' bs k0 ->
        munch L m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (usp - 80) ->
        evt rsegs Q (MS (mkR (Z_to_bv 64 recycle_ret) (Z_to_bv 64 (usp + -80)) gp tp t0' t1' t2' s0 s1
                            (Z_to_bv 64 q) (Z_to_bv 64 (usp + -80)) a2 a3 a4' a5' a6' a7'
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 dorec_entry) fc None m' (seg_rom rsegs)).

  Definition tfj (j : nat) : Z := if (j =? 0)%nat then 0 else baddr bs 0.
  Definition tlj (j : nat) : Z := if (j =? 0)%nat then 0 else baddr bs (j - 1).

  (* [comment removed for export] *)
  Definition lst (t0z a4z a5z a6z : Z) (a7 t1 t2 : word) (mj : word -> option byte) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (usp + -80)) gp tp (Z_to_bv 64 t0z) t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 qmin) a2 a3
            (Z_to_bv 64 a4z) (Z_to_bv 64 a5z) (Z_to_bv 64 a6z) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x39130) fc None mj (seg_rom rsegs).

  (* [comment removed for export] *)
  #[using="KK EQk WF GLR QMN HIR Q1 Q0 CEIL LOLE Clg"] Lemma rec_tail : forall (t0 t1 t2 a4 a5 a6 a7 : word) (mj : word -> option byte),
    mem_inv rsegs mj -> stk rsegs mj lo (usp - 80) ->
    rw_cells rsegs mj (usp + -80)
             (recycle_frame (Z.of_nat k0) (if (k0 =? 0)%nat then 0 else baddr bs 0) (if (k0 =? 0)%nat then 0 else baddr bs (k0 - 1))
                            (lsum (firstn k0 bs)) s4 s3 s2 s1 s0 ra) ->
    rw_cells rsegs mj (q + 152) [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C2 (Z_to_bv 64 hi)] ->
    rw_cells rsegs mj (q + 160) [C8 (Z_to_bv 64 (gn - Z.of_nat k0)); C8 (Z_to_bv 64 (baddr bs k0));
                                 C8 (Z_to_bv 64 (if ((k0 =? length bs)%nat && (0 <? k0)%nat)%bool then 0 else gl));
                                 C8 (Z_to_bv 64 (gqb - lsum (firstn k0 bs)))] ->
    bchain_cut mj bs k0 -> munch L m mj -> wmono rsegs m mj ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 qmin) a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3918c) fc None mj (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 mj MI ST FR LCK GL BCH MUA WMA.
    pose proof alloc_ceiling_val as CV. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
    change (munch L m mj) with (keep (munch L m mj)) in MUA. change (wmono rsegs m mj) with (keep (wmono rsegs m mj)) in WMA.
    pose proof (munch_refl [(usp - 80, usp); (q + 152, q + 156); (q + 160, q + 192)] mj) as MU. pose proof (wmono_refl rsegs mj) as WM.
    unfold recycle_frame in FR.
    amz. amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    unfold keep in MUA, WMA.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MUL : munch L m mm) by (eapply munch_trans; [exact MUA | eapply munch_weaken; [| exact MU]; unfold L; intros x Hx; cbn in Hx |- *; tauto]);
      assert (WML : wmono rsegs m mm) by (eapply wmono_trans; [exact WMA | exact WM]) end.
    eapply KK; [cells_by FR | eassumption | cells_by GL | | exact MUL | exact WML | assumption | exact ST].
    (* [comment removed for export] *)
    intros i Hi. specialize (BCH i Hi). destruct WF as [W1 _]. specialize (W1 i Hi).
    eapply rw_cells_transport; [exact BCH | exact MU | exact WM |]. cbn [cells_size csize Nat.add disjoint_from]. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma munch_acc : forall W extra mj m',
    W = [(usp - 80, usp); (q + 152, q + 156); (q + 160, q + 192)] ++ extra ->
    (forall iv, In iv extra -> exists i, (i < k0)%nat /\ (i < length bs)%nat /\ iv = (baddr bs i, baddr bs i + 8)) ->
    munch L m mj -> munch W mj m' -> munch L m m'.
  Proof.
    intros W extra mj m' -> HE MUA MU. eapply munch_trans; [exact MUA|].
    eapply munch_weaken; [| exact MU]. unfold L.
    change ((usp - 80, usp) :: (q + 152, q + 156) :: (q + 160, q + 192) :: bivls (firstn k0 bs))
      with ([(usp - 80, usp); (q + 152, q + 156); (q + 160, q + 192)] ++ bivls (firstn k0 bs)).
    apply (sub_fp_iter _ bs k0 0%nat extra HE).
  Qed.

  (* [comment removed for export] *)
  #[using="EQk WF Q1 Q0 CEIL LOLE gn k0 lo gqb qmin Clg"] Lemma batch_disjoint : forall i extra,
    (i < length bs)%nat ->
    (forall iv, In iv extra -> exists i', (i' < length bs)%nat /\ i' <> i /\ iv = (baddr bs i', baddr bs i' + 8)) ->
    disjoint_from ([(usp - 80, usp); (q + 152, q + 156); (q + 160, q + 192)] ++ extra) (baddr bs i) 16.
  Proof.
    intros i extra Hi HE. pose proof alloc_ceiling_val as CV. destruct WF as [W1 W2].
    pose proof (W1 i Hi) as R. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
    cbn [app disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|].
    induction extra as [|[lo' hi'] extra IHe]; cbn; [exact I|]. split.
    - destruct (HE (lo', hi') (or_introl eq_refl)) as (i' & Hi' & NE & E). injection E; intros E1 E2. subst lo' hi'.
      destruct (W2 i i' Hi Hi' ltac:(lia)); lia.
    - apply IHe. intros iv Hiv. apply HE. right. exact Hiv.
  Qed.

  (* [comment removed for export] *)
  #[using="KK EQk WF SUMSTOP SUMLE GLR GNH GQH GQ0 QMN HIR Q1 Q0 USP LO0 CEIL LOLE Clg"] Lemma rec_loop : forall (fuel j : nat) (t0z a4z a5z a6z : Z) (a7 t1 t2 : word) (mj : word -> option byte),
    (fuel = length bs - j)%nat -> (j < length bs)%nat -> qmin < gqb - lsum (firstn j bs) ->
    (k0 = j + npop_from qmin gqb bs j)%nat ->
    t0z = baddr bs j -> a4z = Z.of_nat j -> a5z = tlj j -> a6z = gn - Z.of_nat j ->
    mem_inv rsegs mj -> stk rsegs mj lo (usp - 80) ->
    rw_cells rsegs mj (usp + -80) (recycle_frame 0 (tfj j) 0 (lsum (firstn j bs)) s4 s3 s2 s1 s0 ra) ->
    rw_cells rsegs mj (q + 152) [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C2 (Z_to_bv 64 hi)] ->
    rw_cells rsegs mj (q + 160) [C8 (Z_to_bv 64 (gn - Z.of_nat j)); C8 (Z_to_bv 64 (baddr bs j)); C8 (Z_to_bv 64 gl);
                                 C8 (Z_to_bv 64 (gqb - lsum (firstn j bs)))] ->
    bchain_cut mj bs j -> munch L m mj -> wmono rsegs m mj ->
    evt rsegs Q (lst t0z a4z a5z a6z a7 t1 t2 mj).
  Proof.
    induction fuel as [|fuel IH]; intros j t0z a4z a5z a6z a7 t1 t2 mj FUEL JL SZ NP E0 E4 E5 E6 MI ST FR LCK GL BCH MUA WMA; [lia|].
    subst t0z a4z a5z a6z.
    pose proof alloc_ceiling_val as CV. unfold lst, tlj, tfj. unfold tfj in FR. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
    change (munch L m mj) with (keep (munch L m mj)) in MUA. change (wmono rsegs m mj) with (keep (wmono rsegs m mj)) in WMA.
    pose proof WF as WF'. destruct WF' as [W1 W2].
    pose proof (W1 j JL) as BJR. unfold kHighMemBeg in BJR. aobj_lin_all.
    pose proof (BCH j JL) as CJ. replace (S j =? j)%nat with false in CJ by (symmetry; apply Nat.eqb_neq; lia).
    pose proof (lsum_firstn_le bs (S j) WF) as SLE. rewrite (lsum_firstn_S bs j JL) in SLE.
    pose proof (lsum_firstn_nonneg bs j WF) as SNN.
    assert (GNJ : Z.of_nat j < gn) by (unfold gn; lia).
    (* [comment removed for export] *)
    rewrite (npop_from_step qmin gqb bs j JL SZ) in NP.
    remember (lsum (firstn j bs)) as ps eqn:Hps.
    assert (PS1 : lsum (firstn (S j) bs) = ps + bsz bs j) by (rewrite lsum_firstn_S, <- Hps by exact JL; reflexivity).
    remember (baddr bs j) as bj eqn:Hbj.
    (* [comment removed for export] *)
    assert (NX : (S j < length bs)%nat /\ 17594333495296 <= baddr bs (S j) /\ baddr bs (S j) + 24 <= alloc_ceiling
                 \/ (S j = length bs)%nat /\ baddr bs (S j) = 0).
    { destruct (Nat.eq_dec (S j) (length bs)) as [E|NE].
      - right. split; [exact E|]. apply baddr_ge. lia.
      - left. pose proof (W1 (S j) ltac:(lia)) as R. unfold kHighMemBeg in R. aobj_lin_all. split; [lia|]. lia. }
    destruct j as [|j'].
    - (* [comment removed for export] *)
      cbn [Nat.eqb] in FR |- *. rewrite firstn_O in Hps. cbn [lsum] in Hps. subst ps.
      change (Z.of_nat 0) with 0 in GL |- *. rewrite ?Z.sub_0_r in GL. rewrite ?Z.sub_0_r in SZ. rewrite ?Z.sub_0_r in PS1. rewrite ?Z.sub_0_r.
      pose proof (munch_refl ([(usp - 80, usp); (q + 152, q + 156); (q + 160, q + 192)] ++ [(bj, bj + 8)]) mj) as MU.
      cbn [app] in MU.
      pose proof (wmono_refl rsegs mj) as WM.
      unfold recycle_frame in FR.
      amz. br_not_taken. (* [comment removed for export] *)
      amz. (* [comment removed for export] *)
      amz. (* [comment removed for export] *)
      destruct NX as [(NXL & NXlo & NXhi) | (NXL & NX0)].
      + (* [comment removed for export] *)
        amz. br_taken. (* [comment removed for export] *)
        amz. amz. (* [comment removed for export] *)
        amz. amz. amz. amz. (* [comment removed for export] *)
        amz. amz. (* [comment removed for export] *)
        amz. if_false. (* [comment removed for export] *)
        amz. (* [comment removed for export] *)
        amz. (* [comment removed for export] *)
        amz. (* [comment removed for export] *)
        amz. amz. amz. amz. (* [comment removed for export] *)
        amz. (* [comment removed for export] *)
        amz. amz. amz. (* [comment removed for export] *)
        amz. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
        * (* [comment removed for export] *)
          rewrite (npop_from_stop qmin gqb bs 1) in NP by (rewrite PS1; lia). cbn in NP.
          amz. amz. (* [comment removed for export] *)
          unfold keep in MUA, WMA.
          eapply rec_tail; rewrite ?NP.
          -- assumption.
          -- exact ST.
          -- cbn [Nat.eqb Nat.sub]. rewrite PS1, <- Hbj. cells_by FR.
          -- exact LCK.
          -- replace ((1 =? length bs)%nat && (0 <? 1)%nat)%bool with false by (symmetry; apply andb_false_intro1; apply Nat.eqb_neq; lia).
             rewrite PS1. cells_by GL.
          -- eapply (bchain_cut_step _ mj); [exact WF | exact JL | exact BCH | exact MU | exact WM | | rewrite <- Hbj; cells_by CJ | intros i Hi; lia].
             intros i Hi NE1 NE2. change ([?a; ?b; ?c; ?d]) with ([a; b; c] ++ [d]).
             apply batch_disjoint; [exact Hi|]. intros iv [<-|[]]. exists 0%nat. rewrite <- Hbj. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
          -- eapply (munch_acc _ [(bj, bj + 8)] mj); [reflexivity | | exact MUA | exact MU].
             intros iv [<-|[]]. exists 0%nat. rewrite <- Hbj. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
          -- eapply wmono_trans; [exact WMA | exact WM].
        * (* [comment removed for export] *)
          unfold keep in MUA, WMA. subst bj.
          eapply (IH 1%nat); [lia | exact NXL | rewrite PS1; lia | exact NP | eqz | eqz | eqz | eqz
                             | assumption | exact ST | | exact LCK | | | | ].
          -- unfold recycle_frame, tfj. cbn [Nat.eqb]. rewrite PS1. cells_by FR.
          -- rewrite PS1. cells_by GL.
          -- eapply (bchain_cut_step _ mj); [exact WF | exact JL | exact BCH | exact MU | exact WM | | cells_by CJ | intros i Hi; lia].
             intros i Hi NE1 NE2. change ([?a; ?b; ?c; ?d]) with ([a; b; c] ++ [d]).
             apply batch_disjoint; [exact Hi|]. intros iv [<-|[]]. exists 0%nat. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
          -- eapply (munch_acc _ [(baddr bs 0, baddr bs 0 + 8)] mj); [reflexivity | | exact MUA | exact MU].
             intros iv [<-|[]]. exists 0%nat. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
          -- eapply wmono_trans; [exact WMA | exact WM].
      + (* [comment removed for export] *)
        rewrite NX0 in *.
        amz. if_false. amz. (* [comment removed for export] *)
        amz. amz.
        amz. amz. amz. amz.
        amz. amz.
        amz. if_false.
        amz.
        amz.
        amz.
        amz. amz. amz. amz.
        amz.
        amz. amz. amz.
        amz. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
        * rewrite (npop_from_stop qmin gqb bs 1) in NP by (rewrite PS1; lia). cbn in NP.
          amz. amz.
          unfold keep in MUA, WMA.
          eapply rec_tail; rewrite ?NP.
          -- assumption.
          -- exact ST.
          -- cbn [Nat.eqb Nat.sub]. rewrite PS1, <- Hbj. cells_by FR.
          -- exact LCK.
          -- replace ((1 =? length bs)%nat && (0 <? 1)%nat)%bool with true by (symmetry; rewrite <- NXL; reflexivity).
             rewrite PS1, NX0. cells_by GL.
          -- eapply (bchain_cut_step _ mj); [exact WF | exact JL | exact BCH | exact MU | exact WM | | rewrite <- Hbj; cells_by CJ | intros i Hi; lia].
             intros i Hi NE1 NE2. change ([?a; ?b; ?c; ?d]) with ([a; b; c] ++ [d]).
             apply batch_disjoint; [exact Hi|]. intros iv [<-|[]]. exists 0%nat. rewrite <- Hbj. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
          -- eapply (munch_acc _ [(bj, bj + 8)] mj); [reflexivity | | exact MUA | exact MU].
             intros iv [<-|[]]. exists 0%nat. rewrite <- Hbj. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
          -- eapply wmono_trans; [exact WMA | exact WM].
        * (* [comment removed for export] *)
          exfalso. assert (EB : lsum bs = 0 + bsz bs 0) by (rewrite <- PS1, firstn_all2 by lia; reflexivity). lia.
    - (* [comment removed for export] *)
      cbn [Nat.eqb] in FR |- *. replace (S j' - 1)%nat with j' by lia.
      assert (JL' : (j' < length bs)%nat) by lia.
      pose proof (BCH j' JL') as CP. rewrite Nat.eqb_refl in CP.
      pose proof (W1 j' JL') as BPR. unfold kHighMemBeg in BPR. aobj_lin_all.
      pose proof (W2 j' (S j') JL' JL ltac:(lia)) as DJ. rewrite <- Hbj in DJ.
      remember (baddr bs j') as bp eqn:Hbp.
      pose proof (munch_refl ([(usp - 80, usp); (q + 152, q + 156); (q + 160, q + 192)] ++ [(bj, bj + 8); (bp, bp + 8)]) mj) as MU.
      cbn [app] in MU.
      pose proof (wmono_refl rsegs mj) as WM.
      unfold recycle_frame in FR.
      assert (ZJ : 0 < Z.of_nat (S j') < 2^24) by lia.
      amz. br_not_taken. (* [comment removed for export] *)
      amz. (* [comment removed for export] *)
      amz. (* [comment removed for export] *)
      destruct NX as [(NXL & NXlo & NXhi) | (NXL & NX0)].
      + (* [comment removed for export] *)
        amz. br_taken. (* [comment removed for export] *)
        amz. amz. (* [comment removed for export] *)
        amz. amz. amz. amz. (* [comment removed for export] *)
        amz. amz. (* [comment removed for export] *)
        amz. br_taken. (* [comment removed for export] *)
        amz. (* [comment removed for export] *)
        amz. amz. amz. amz. (* [comment removed for export] *)
        amz. (* [comment removed for export] *)
        amz. amz. amz. (* [comment removed for export] *)
        amz. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
        * (* [comment removed for export] *)
          rewrite (npop_from_stop qmin gqb bs (S (S j'))) in NP by (rewrite PS1; lia). rewrite Nat.add_1_r in NP.
          amz. amz. (* [comment removed for export] *)
          unfold keep in MUA, WMA.
          eapply rec_tail; rewrite ?NP.
          -- assumption.
          -- exact ST.
          -- cbn [Nat.eqb Nat.sub]. rewrite ?Nat.sub_0_r, PS1, <- Hbj. cells_by FR.
          -- exact LCK.
          -- replace ((S (S j') =? length bs)%nat && (0 <? S (S j'))%nat)%bool with false
               by (symmetry; apply andb_false_intro1; apply Nat.eqb_neq; lia).
             rewrite PS1. cells_by GL.
          -- eapply (bchain_cut_step _ mj); [exact WF | exact JL | exact BCH | exact MU | exact WM | | rewrite <- Hbj; cells_by CJ | ].
             ++ intros i Hi NE1 NE2. change ([?a; ?b; ?c; ?d; ?e]) with ([a; b; c] ++ [d; e]).
                apply batch_disjoint; [exact Hi|]. intros iv [<-|[<-|[]]]; [exists (S j') | exists j']; rewrite <- ?Hbj, <- ?Hbp; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
             ++ intros i Hi. replace i with j' by lia. rewrite <- Hbp, <- Hbj. cells_by CP.
          -- eapply (munch_acc _ [(bj, bj + 8); (bp, bp + 8)] mj); [reflexivity | | exact MUA | exact MU].
             intros iv [<-|[<-|[]]]; [exists (S j') | exists j']; rewrite <- ?Hbj, <- ?Hbp; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
          -- eapply wmono_trans; [exact WMA | exact WM].
        * (* [comment removed for export] *)
          unfold keep in MUA, WMA. subst bj.
          eapply (IH (S (S j'))); [lia | exact NXL | rewrite PS1; lia | rewrite Nat.add_succ_r in NP; exact NP
                                  | eqz | eqz | eqz | eqz
                                  | assumption | exact ST | | exact LCK | | | | ].
          -- unfold recycle_frame, tfj. cbn [Nat.eqb]. rewrite PS1. cells_by FR.
          -- rewrite PS1. cells_by GL.
          -- eapply (bchain_cut_step _ mj); [exact WF | exact JL | exact BCH | exact MU | exact WM | | cells_by CJ | ].
             ++ intros i Hi NE1 NE2. change ([?a; ?b; ?c; ?d; ?e]) with ([a; b; c] ++ [d; e]).
                apply batch_disjoint; [exact Hi|]. intros iv [<-|[<-|[]]]; [exists (S j') | exists j']; rewrite <- ?Hbp; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
             ++ intros i Hi. replace i with j' by lia. rewrite <- Hbp. cells_by CP.
          -- eapply (munch_acc _ [(baddr bs (S j'), baddr bs (S j') + 8); (bp, bp + 8)] mj); [reflexivity | | exact MUA | exact MU].
             intros iv [<-|[<-|[]]]; [exists (S j') | exists j']; rewrite <- ?Hbp; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
          -- eapply wmono_trans; [exact WMA | exact WM].
      + (* [comment removed for export] *)
        rewrite NX0 in *.
        amz. if_false. amz. (* [comment removed for export] *)
        amz. amz.
        amz. amz. amz. amz.
        amz. amz.
        amz. br_taken.
        amz.
        amz. amz. amz. amz.
        amz.
        amz. amz. amz.
        amz. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
        * rewrite (npop_from_stop qmin gqb bs (S (S j'))) in NP by (rewrite PS1; lia). rewrite Nat.add_1_r in NP.
          amz. amz.
          unfold keep in MUA, WMA.
          eapply rec_tail; rewrite ?NP.
          -- assumption.
          -- exact ST.
          -- cbn [Nat.eqb Nat.sub]. rewrite ?Nat.sub_0_r, PS1, <- Hbj. cells_by FR.
          -- exact LCK.
          -- replace ((S (S j') =? length bs)%nat && (0 <? S (S j'))%nat)%bool with true
               by (symmetry; rewrite <- NXL, Nat.eqb_refl; reflexivity).
             rewrite PS1, NX0. cells_by GL.
          -- eapply (bchain_cut_step _ mj); [exact WF | exact JL | exact BCH | exact MU | exact WM | | rewrite <- Hbj; cells_by CJ | ].
             ++ intros i Hi NE1 NE2. change ([?a; ?b; ?c; ?d; ?e]) with ([a; b; c] ++ [d; e]).
                apply batch_disjoint; [exact Hi|]. intros iv [<-|[<-|[]]]; [exists (S j') | exists j']; rewrite <- ?Hbj, <- ?Hbp; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
             ++ intros i Hi. replace i with j' by lia. rewrite <- Hbp, <- Hbj. cells_by CP.
          -- eapply (munch_acc _ [(bj, bj + 8); (bp, bp + 8)] mj); [reflexivity | | exact MUA | exact MU].
             intros iv [<-|[<-|[]]]; [exists (S j') | exists j']; rewrite <- ?Hbj, <- ?Hbp; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
          -- eapply wmono_trans; [exact WMA | exact WM].
        * exfalso. assert (EB : lsum bs = ps + bsz bs (S j')) by (rewrite <- PS1, firstn_all2 by lia; reflexivity). lia.
  Qed.

End Rec.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem recycle_pre_ok : recycle_pre_stmt.
Proof.
  unfold recycle_pre_stmt. intros until Q. cbv zeta.
  intros MI ST LOLE CEIL A0 A1 Q0 Q1 QAL HIR QMN GQ0 GQH GNH GLR CHK NOMERGE SUMLE SUMSTOP WF BC LCK GL K.
  pose proof alloc_ceiling_val as CV. unfold recycle_entry, dorec_entry, recycle_ret in *. subst a0 a1.
  pose proof Q1 as Q1'. unfold kHighMemBeg in Q1'. aobj_lin_all.
  set (qq := q / 8) in *. assert (QQ : q = 8 * qq) by (subst qq; rewrite (Z_div_mod_eq_full q 8) at 1; rewrite QAL; lia). clearbody qq.
  assert (QM4 : (q + 152) mod 4 = 0) by (rewrite QQ; replace (8 * qq + 152) with ((2 * qq + 38) * 4) by lia; apply Z_mod_mult).
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  remember (npop qmin gqb bs) as k0 eqn:EQk.
  (* [comment removed for export] *)
  pose proof (munch_refl ((bv_unsigned sp - 80, bv_unsigned sp) :: (q + 152, q + 156) :: (q + 160, q + 192) :: bivls (firstn k0 bs)) m) as MUA.
  change (munch ?W m m) with (keep (munch W m m)) in MUA.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q + 152, q + 156); (q + 160, q + 192)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (GN0 : 0 <= Z.of_nat (length bs)) by lia.
  pose proof (lsum_firstn_nonneg bs (length bs) WF) as SNN. rewrite firstn_all in SNN.
  carve_frame 80%nat ST.
  do 7 amz. (* [comment removed for export] *)
  do 4 amz. (* [comment removed for export] *)
  amz. amz. amz. rewrite (land_m4 (q + 152)) by first [exact QM4 | plia]. amz. (* [comment removed for export] *)
  apply (hdr4_join _ _ 0 1 hi) in LCK; [| lia | lia | lia | cbn; tauto].
  replace (0 + 256 * 1 + 65536 * hi) with (256 * (1 + 256 * hi)) in LCK by lia.
  amz. rewrite sx32_small by lia. (* [comment removed for export] *)
  amz. amz. amz. amz. rewrite (cas_set_low0 1 (1 + 256 * hi)) by lia.
  scstep; zsimp. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  amz. rewrite (land255_low0 (1 + 256 * hi)) by lia. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  replace (1 + 256 * (1 + 256 * hi)) with (1 + 256 * 1 + 65536 * hi) in LCK by lia.
  apply (hdr4_split _ _ 1 1 hi) in LCK; [| lia | lia | lia | cbn; tauto].
  amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 _ 13) by lia. change (2^13) with 8192.
  amz. br_not_taken. (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (REST : forall (t0x t1x a4 a5 a7 : word) (mx : word -> option byte),
    mem_inv rsegs mx -> stk rsegs mx lo (bv_unsigned sp - 80) ->
    rw_cells rsegs mx (bv_unsigned sp + -80) (recycle_frame 0 0 0 0 s4 s3 s2 s1 s0 ra) ->
    rw_cells rsegs mx (q + 152) [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C2 (Z_to_bv 64 hi)] ->
    rw_cells rsegs mx (q + 160) [C8 (Z_to_bv 64 (Z.of_nat (length bs))); C8 (Z_to_bv 64 (baddr bs 0)); C8 (Z_to_bv 64 gl); C8 (Z_to_bv 64 gqb)] ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp); (q + 152, q + 156); (q + 160, q + 192)] m mx -> wmono rsegs m mx ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0x t1x t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 qmin) a2 a3
                         a4 a5 (Z_to_bv 64 (Z.of_nat (length bs))) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x390f0) fc None mx (seg_rom rsegs))).
  { intros t0x t1x a4' a5' a7' mx MI0 ST0 FR0 LCK0 GL0 MU0 WM0.
    clear MU WM. unfold recycle_frame in FR0.
    assert (MUL : munch ((bv_unsigned sp - 80, bv_unsigned sp) :: (q + 152, q + 156) :: (q + 160, q + 192) :: bivls (firstn k0 bs)) m mx).
    { eapply munch_weaken; [| exact MU0]. intros x Hx. cbn in Hx |- *. tauto. }
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q + 152, q + 156); (q + 160, q + 192)] mx) as MU.
    pose proof (wmono_refl rsegs mx) as WM.
    change (munch ?W m mx) with (keep (munch W m mx)) in MUL. change (wmono rsegs m mx) with (keep (wmono rsegs m mx)) in WM0.
    amz. amz. amz. (* [comment removed for export] *)
    amz. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
    - (* [comment removed for export] *)
      assert (K00 : k0 = 0%nat) by (rewrite EQk, <- npop_from_0; apply npop_from_stop; rewrite firstn_O; cbn; lia).
      unfold keep in MUL, WM0.
      eapply (rec_tail sp ra gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q qmin hi gl gqb lo bs Q k0);
        rewrite ?K00; try eassumption; try lia.
      all: lazymatch goal with
           | |- rw_cells _ _ (_ + 160) _ => rewrite firstn_O, Bool.andb_false_r; cbn [lsum Z.of_nat]; rewrite !Z.sub_0_r; cells_by GL0
           | |- rw_cells _ _ _ _ => unfold recycle_frame; rewrite ?firstn_O; cbn [lsum Z.of_nat Nat.eqb]; cells_by FR0
           | |- bchain_cut _ _ _ =>
               apply bchain_cut_0; intros i Hi; specialize (BC i Hi); destruct WF as [W1 _]; specialize (W1 i Hi); unfold kHighMemBeg in W1;
               eapply rw_cells_transport; [exact BC | exact MU0 | exact WM0 |]; cbn [cells_size csize Nat.add disjoint_from]; lia
           | |- _ => intros; eapply K; rewrite ?K00; try eassumption
           end.
    - (* [comment removed for export] *)
      amz. (* [comment removed for export] *)
      amz. (* [comment removed for export] *)
      assert (JL : (0 < length bs)%nat).
      { destruct bs as [|b0 bs']; [| cbn; lia]. exfalso. cbn in SUMSTOP. lia. }
      unfold keep in MUL, WM0.
      eapply (rec_loop sp ra gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q qmin hi gl gqb lo bs Q k0)
        with (j := 0%nat); try eassumption; try lia.
      all: lazymatch goal with
           | |- rw_cells _ _ (_ + 160) _ => rewrite firstn_O; cbn [lsum Z.of_nat]; rewrite !Z.sub_0_r; cells_by GL0
           | |- rw_cells _ _ _ _ => unfold recycle_frame, tfj; rewrite ?firstn_O; cbn [lsum Z.of_nat Nat.eqb]; cells_by FR0
           | |- bchain_cut _ _ _ =>
               apply bchain_cut_0; intros i Hi; specialize (BC i Hi); destruct WF as [W1 _]; specialize (W1 i Hi); unfold kHighMemBeg in W1;
               eapply rw_cells_transport; [exact BC | exact MU0 | exact WM0 |]; cbn [cells_size csize Nat.add disjoint_from]; lia
           | |- _ = (0 + npop_from _ _ _ 0)%nat => rewrite EQk, <- npop_from_0; reflexivity
           | |- _ < _ => rewrite ?firstn_O; cbn [lsum]; lia
           | |- _ = _ => first [reflexivity | lia | cbn; reflexivity]
           | |- _ => intros; eapply K; try eassumption
           end. }
  amz. if_cases KM; zify_cond KM; rewrite ?Z.mod_small in KM by lia.
  - (* [comment removed for export] *)
    unfold keep in MUA. eapply REST; try eassumption.
  - amz. amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. br_taken. (* [comment removed for export] *)
    eapply REST; try eassumption.
Qed.

End CEIL.

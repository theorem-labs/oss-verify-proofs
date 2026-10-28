(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AQConst ABytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ F_apoison F_aenqueue F_adrain F_aput F_afree_tail F_afreeC_iface F_adrainC.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import LiaTuningK.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
Local Ltac with_sclr tac := idtac; match goal with H : sclr ?a ?n |- _ => with_band H tac | _ => tac end.
Local Ltac iclr_of H := clear -H; unfold iclr, AIMG_LO, AIMG_HI in *; lia.
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6443008 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6443008 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
Theorem put_torec : put_torec_stmt.
Proof.
  unfold put_torec_stmt.
  intros until sjunk. intros ST CEIL LO MI -> -> -> -> -> QK GF FLG PC HD N B1 AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT EK DK RIMG RSTK RT RH RSH TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int T0.   (* [comment removed for export] *)
  assert (SHB : 2148256256 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in N. Z.div_mod_to_equations. lia. }
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (unfold rup; Z.div_mod_to_equations; lia).
  assert (SHL : 0 < shlen (rup n 8) < 0x10000000) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; unfold Q_MAX in N; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
              (0xcca08, 0xcca08 + 4); (0xcca10, 0xcca10 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  box DHT.
  (* [comment removed for export] *)
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0];
  [ destruct EK as (NB1 & LB & CNT & BSZ & BSZN & NX & LA & LEN & [junkt LJ] & L0 & L1 & DTL & DHL & CR' & STS' & RL); box DTL; box DHL
  | destruct EK as (FULL & SB & CR & CH & LCH & CNT & NTH & IXS & STS & HB & [junkb BJ] & SBP & B0 & BL1 & DTB & DTL & DBL & DHB & DHL & RB);
    box DTB; box DTL; box DBL; box DHB; box DHL;
    destruct full; [destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1 & LA0 & LEN0 & RL) | destruct FULL as [NB0 LST0]] ];
  unfold dk_glst in *; cbn [ek_pre dk_preC ek_b ek_nb ek_fst ek_lst ek_delta] in *;
  destruct DK as (EGD & MX & GC & GNB & GQB & GFST & GLST & QB1 & GQ & GQ63 & GFULL);
  (destruct (g_full g) eqn:EGF;
     [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); box G5; box G6; box G7; box G8 | destruct GFULL as [GNB0 GLST0]]);
  rewrite ?EGD in *; cbn [ek_pre dk_preC ek_b ek_nb ek_fst ek_lst ek_delta dk_glst] in *; unfold AIMG_HI in *.
  all: first [assert (QZE : qsz lst = 8192) by (apply qsz_pos; generalize L0; clear; intros; lia) | assert (QZE : qsz lst = 8) by (apply qsz_eq0; exact LST0)]; rewrite QZE in *.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box SH'. box GLB. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; lia_keep2). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; lia_keep2). carry CR' MUe WMe ltac:(ub DTL; lia_keep1). carry STS' MUe WMe ltac:(ub DTL; lia_keep1). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xcca08, 0xcca08 + 4); (0xcca10, 0xcca10 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia_keep1| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia_keep2). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia_keep2). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; lia_keep2). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia_keep2). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box SH'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80 + 24, t + 80 + 32); (lst + 8, lst + 24); (lst + 24 + 8 * cnt, lst + 24 + 8 * cnt + 8)]%Z MUe WMe.
    box LJ. box LB. box QC. box LA.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_append_spec (t + 80) lst cnt RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz lo hs);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_MAX in *; lia| lia| lia| lia
      | unboxed LB| exact CNT| lia| unfold Q_MAX in *; lia| lia| unboxed LA| exact LEN| exists junkt; unboxed LJ
      | iclr_of TI| atop_facts; lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear LJ LB QC LA.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; lia_keep2). carry SH' MUe WMe ltac:(lia). carry CR' MUe WMe ltac:(ub DTL; lia_keep1). carry STS' MUe WMe ltac:(ub DTL; lia_keep1). clear MUe WMe.
    rename POST into LJ'. rename PC1 into LB'. rename PC2 into LA'. rename PC0 into QC'. destruct LJ' as [junkt' LJ'].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box LB'. box LA'. box LJ'. box CR'. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xcca08, 0xcca08 + 4); (0xcca10, 0xcca10 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 lst (qb + n) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia_keep1). carry LB' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia_keep2). carry LA' MUd WMd ltac:(rewrite length_app, LEN; cbn [length]; ub DTL; first [ub G7 | pose proof GLST0]; lia_keep2). carry LJ' MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia_keep2). carry CR' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box CH. box SH'. box GLB. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia_keep3). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia_keep2). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia_keep2). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia_keep3). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xcca08, 0xcca08 + 4); (0xcca10, 0xcca10 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia_keep1| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia_keep2). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia_keep2). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia_keep2). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box CH. box SH'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box LB. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec true t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | split; [lia|]; split; [unboxed LB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try assumption; lia
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia|].
    try clear ST.
    clear BJ STS CR LB QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia_keep3). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia_keep2). carry SH' MUe WMe ltac:(lia). carry LA0 MUe WMe ltac:(rewrite LEN0; ub DTL; ub DBL; lia_keep2). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box POST. box PC1. box STS'. box LA0.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xcca08, 0xcca08 + 4); (0xcca10, 0xcca10 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) fst0 b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia_keep1). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry POST MUd WMd ltac:(ub DTL; first [ub G7 | pose proof GLST0]; lia_keep2). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). carry LA0 MUd WMd ltac:(rewrite LEN0; ub DTL; first [ub G7 | pose proof GLST0]; lia_keep2). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box CH. box SH'. box GLB.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia_keep3). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia_keep2). carry SH' MUe WMe ltac:(lia). carry GLB MUe WMe ltac:(ub G5; ub G7; ub G8; lia_keep3). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xcca08, 0xcca08 + 4); (0xcca10, 0xcca10 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GLB. box GC. box MX. box CH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_torec true t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| split; [lia|]; split; [unboxed GLB|]; unfold AIMG_HI, Q_BATCH_BYTES; repeat split; try lia; ub G5; lia_keep1| exact TI| atop_facts; lia|].
    try clear ST.
    clear QC' GLB GC MX CH.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT; ub G6; lia_keep2). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
  - (* [comment removed for export] *)
    box ST.   (* [comment removed for export] *)
    call (putA_spec t hm n); try unboxed ST; try eassumption; try reflexivity; try (unfold Q_MAX, AIMG_HI in *; lia).
    try clear ST.
    rename POST into FRP.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end. try rename MI0 into MI.
    box SH.   (* [comment removed for export] *)
    box ST.
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (hm + 16) (rup n 8) 253 lo sjunk);
      [unboxed ST| exact CEIL| lia| exact MI| repeat (split; [assumption|]); assumption| reflexivity| reflexivity| reflexivity
      | Z.div_mod_to_equations; lia| lia| lia| first [assumption | (eapply ablk_sub; [exact HLO| clear; lia| clear; lia]) | unfold ablk; right; lia | unfold ablk; left; lia]| lia| lia| lia| unboxed SH|].
    try clear ST.
    clear SH.   (* [comment removed for export] *)
    try rename MI0 into MI. clear P1 P2 P3 P4 P5 P6 P7.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    match goal with H : rw_cells bsegs ?mm (shad (hm + 16)) _ |- _ => rename H into SH' end.
    do 5 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    box HD. box CH. box SH'.
    snapshot [(bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z MUe WMe.
    box BJ. box STS. box CR. box QC.   (* [comment removed for export] *)
    box ST.
    call_sp (enqueue_new_spec false t lst b RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ nb fst0 qb hm n nx bsz cnt24 spacebeg lo maxc csz stj idxw chunks);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| unboxed QC| lia| lia| unfold Q_BATCH_BYTES, Q_MAX in *; lia
      | lia| lia| lia| lia
      | exact NB0
      | exact SB| unboxed CR| ub CH; exact Y| exact LCH| exact CNT| exact NTH| exact IXS| unboxed STS| unfold K_BATCH_CLASS; lia| exists junkb; unboxed BJ
      | exact TI| atop_facts; lia| exact TAL| lia| unfold AIMG_HI; lia| unfold Q_BATCH_BYTES; lia
      | ub DTB; unfold Q_BATCH_BYTES; lia| ub DTL; unfold Q_BATCH_BYTES; lia| ub DBL; unfold Q_BATCH_BYTES; lia| exact I|].
    try clear ST.
    clear BJ STS CR QC.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUe WMe ltac:(ub DHT; ub DHL; ub DHB; lia_keep3). carry CH MUe WMe ltac:(rewrite LCH; ub DTL; ub DTB; lia_keep2). carry SH' MUe WMe ltac:(lia). clear MUe WMe.
    rename PC0 into QC'. destruct PC2 as [stj' STS']. destruct PC5 as [junkb' PC5].
    (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases KD; zify_cond KD; [|exfalso; unfold Q_CACHE in *; lia].   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    box HD.  box PC3. box PC4. box PC5. box PC1. box STS'.
    snapshot [(bv_unsigned sp + -80 - 48, bv_unsigned sp + -80); (t + 80, t + 112); (0xcca08, 0xcca08 + 4); (0xcca10, 0xcca10 + 32); (g_lst g, g_lst g + 8)]%Z MUd WMd.
    box QC'. box GC. box MX.   (* [comment removed for export] *)
    box ST.
    step. call_sp (drain_torec false t (g_lst g) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (nb + 1) b b (qb + (n + 8192)) (g_nb g) (g_fst g) (g_qb g) (g_nx g) lo);
      [unboxed ST| exact CEIL| lia| exact MI| reflexivity| reflexivity| unboxed QC'| lia| lia| lia| lia| unboxed MX| unboxed GC| lia| lia| unfold Q_MAX in *; lia| unfold Q_MAX in *; lia| lia| lia
      | exact QK| exact GNB0| exact TI| atop_facts; lia| exact I|].
    try clear ST.
    clear QC' GC MX.   (* [comment removed for export] *)
    try rename MI0 into MI.
    match goal with H : stk bsegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
    carry HD MUd WMd ltac:(ub DHT;  lia_keep1). carry PC3 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry PC4 MUd WMd ltac:(cbn [length]; ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry PC5 MUd WMd ltac:(ub DTB; first [ub G8 | pose proof GLST0]; lia_keep2). carry PC1 MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). carry STS' MUd WMd ltac:(first [ub G5 | pose proof GLST0]; lia_keep1). clear MUd WMd.
    unfold put_torec_post. rewrite ?QZE. unfold put_frame, dk_postC, dk_glst. rewrite ?EGD. rewrite ?EGF. cbn [ek_post ek_nb ek_fst ek_lst ek_delta ek_b]. finish.
    all: try assumption. all: try exact I. all: try (lazymatch goal with |- exists _, rw_cells _ ?mq ?Aq _ => match goal with Hq : rw_cells _ mq Aq _ |- _ => eexists; exact Hq end end).   (* [comment removed for export] *)  all: try (eexists; eassumption).
Qed.
End CANSEC1.

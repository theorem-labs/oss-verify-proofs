(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif1dq.v (a working branch ced28ed2383, file sha256 dc55271604eb) onto omx-clap-core/fuzz_state's asan-ubsan image (fuzz_state.asan-ubsan, pinned sha256 5ac5ce0954f8; addresses read from its unstripped build b1566a1ca816); module paths changed; its 3 image addresses moved by code-verified function pairs (13 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: the released drain's re-establishment of AR at its cuts (YFet.FIN_a / YFet.DRPRE
   over YFey.drain_fin_ARm) restated from the cut memory relation DMiface.dmem_q instead of the walk's frame: the
   changed bytes outside YFey's window D (the batch cells) are shown unchanged by value, from the entry state's cells and
   the cut state's cells. *)
(* AR at a drain cut, for cgif_file (DGif1d's di_requar_x / di_requar_r).

   The cut state is YFey.S' X P R (the transfer, then the batches P dequeued, R kept); the memory [mem'] at the cut is
   given by DMiface.dmem_q relative to the entry memory [mem], and the batch cells of P hold in [mem'] (the temp list's
   cells).  [requar_AR] is AR at the cut state over [mem'], by YFey.drain_fin_ARm; its hypotheses are discharged as
   YFet.FIN_a does, except YFey's frame AG on the batch cells, which dmem_q lets change: there both the entry state's
   cells (ARm) and the cut state's cells (dmem_q / the temp list) hold, and they are the same cells. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YFeq YFex YFf2 YFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFew YFff YFeu YFey YFgj YB13 YFev YFet.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma combine_seq_in : forall (l : list chunk) s i x, nth_error l i = Some x -> In ((s + i)%nat, x) (combine (seq s (length l)) l).
Proof.
induction l as [|y t IH]; intros s i x H; [destruct i; discriminate|].
destruct i as [|i]; cbn in H |- *.
- injection H as ->. left. f_equal. lia.
- right. replace (s + S i)%nat with (S s + i)%nat by lia. apply IH. exact H.
Qed.

Section q.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (W : world tfibsegs) (mem mem' : word -> option byte) (md : Model) (sp0 : Z) (P R : list batch).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).
Local Notation rd := (aview tfibsegs (w_H W) mem).
Local Notation rd' := (aview tfibsegs (w_H W) mem').
Local Notation S' := (YFey.S' X P R).
Hypothesis HAR : AR tfibsegs B ly X W mem md.
Hypothesis HTB : kQuarantineCacheMax < qc_bytes (st_qthread X).
Hypothesis HL : G ++ Tq = P ++ R.
Hypothesis HSP : ly_stk_lo ly + DSTACK <= sp0 <= ly_stk_hi ly.
Hypothesis DQ : dmem_q B W TFIB_INST ly sp0 X S' P mem mem'.
Hypothesis PLC : Forall (cell_holds B ly rd') (batch_cells P).

Lemma qM : ARm B ly X rd. Proof. exact (proj1 HAR). Qed.
Lemma qLED : ALedger tfibsegs ly X md. Proof. exact (proj1 (proj2 HAR)). Qed.
Lemma qIMG : img_cover ly. Proof. exact (img_cover_of_ledger ly X md qLED). Qed.
Lemma qLO : layout_ok ly. Proof. exact (am_layout B ly X rd qM). Qed.
Lemma qWF : Wf (as_universe B) X. Proof. exact (am_wf B ly X rd qM). Qed.
Lemma qEI : as_inst B = TFIB_INST. Proof. exact (ts_inst _ TB). Qed.

(* YFev.GEO, from the layout. *)
Lemma qGEO :
(ly_prim ly + kPrimResvSize <= T \/ T + kThreadObjSize <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_C ly \/ ly_C ly + 256 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_D ly \/ ly_D ly + 4096 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_prim ly) /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\
(T + kThreadObjSize <= ly_D ly \/ ly_D ly + 4096 <= T) /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= T) /\
(ly_C ly + 256 <= ly_D ly \/ ly_D ly + 4096 <= ly_C ly) /\
(ly_C ly + 256 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_C ly) /\
(ly_D ly + 4096 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_D ly) /\
zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096.
Proof.
pose proof qLO as LO. pose proof qIMG as IMG.
pose proof (lo_disj ly LO) as HD.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(clear; lia) (Forall_nth_f _ _ 6 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
pose proof (zone3_intro ly (ly_D ly) 4096 IMG ltac:(clear; lia) (Forall_nth_f _ _ 7 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 7 1 _ _ HD eq_refl eq_refl)) as ZD.
unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _ & DT & _ & _ & _ & DC & DD & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [PD DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [TD DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DC as [CD DC]. apply Forall_cons_iff in DC as [CSTK _]. apply Forall_cons_iff in DD as [DSTK _].
unfold zdisjoint in PT, PC, PD, PSTK, TC, TD, TSTK, CD, CSTK, DSTK. cbn [fst snd] in PT, PC, PD, PSTK, TC, TD, TSTK, CD, CSTK, DSTK.
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma qHIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
(forall b2, In b2 (all_batches X) -> ly_prim ly <= YFey.addr ly b2 /\ YFey.addr ly b2 + kBatchBytes <= ly_space ly + kSpaceSize) /\
4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd.
Proof. exact (YFey.HIGH B ly X rd qM sp0 HSP qIMG). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Cells.                                                                                                           *)
Lemma ch_get : forall (rd0 : reader) e (w : nat) v (k : nat), cell_holds B ly rd0 (ACell e w (AV v)) -> (k < w)%nat ->
rd0 (aeval B ly e + Z.of_nat k) = Some (YG0f.le_byte (aeval B ly v) w k).
Proof. intros rd0 e w v k H Hk. unfold cell_holds in H. cbn [c_at c_w c_val] in H. exact (H k Hk). Qed.
Lemma ch_some : forall (rd0 : reader) e (w : nat) v a, cell_holds B ly rd0 (ACell e w (AV v)) ->
aeval B ly e <= a < aeval B ly e + Z.of_nat w -> rd0 a <> None.
Proof.
intros rd0 e w v a H Ha. replace a with (aeval B ly e + Z.of_nat (Z.to_nat (a - aeval B ly e))) by lia.
rewrite (ch_get rd0 e w v _ H) by lia. discriminate.
Qed.
Lemma ch_both : forall (rd1 rd2 : reader) e (w : nat) v (k : nat), cell_holds B ly rd1 (ACell e w (AV v)) -> cell_holds B ly rd2 (ACell e w (AV v)) ->
(k < w)%nat -> rd2 (aeval B ly e + Z.of_nat k) = rd1 (aeval B ly e + Z.of_nat k).
Proof. intros rd1 rd2 e w v k H1 H2 Hk. rewrite (ch_get rd1 e w v k H1 Hk), (ch_get rd2 e w v k H2 Hk). reflexivity. Qed.

(* The cut state's quarantine cells. *)
Lemma qcells : Forall (cell_holds B ly rd')
(z1 (AInst o_q_cmutex) 0 :: z1 (AInst o_q_rmutex) 0 :: qc_cells (AT t_qc) qc0 ++
 qc_cells (AInst o_q_size) (mkQC R (qc_bytes (st_qglobal X) + qc_bytes (st_qthread X) - sum_bytes P))).
Proof. destruct DQ as (_ & D2 & _). exact D2. Qed.
Lemma qcells_parts :
cell_holds B ly rd' (z1 (AInst o_q_cmutex) 0) /\ cell_holds B ly rd' (z1 (AInst o_q_rmutex) 0) /\
cell_holds B ly rd' (z8 (AT t_qc) 0) /\ cell_holds B ly rd' (c8 (aoff (AT t_qc) 8) (ANum 0)) /\
cell_holds B ly rd' (c8 (aoff (AT t_qc) 16) (ANum 0)) /\ cell_holds B ly rd' (z8 (aoff (AT t_qc) 24) 0) /\
cell_holds B ly rd' (z8 (AInst o_q_size) (Z.of_nat (length R))) /\
cell_holds B ly rd' (c8 (aoff (AInst o_q_size) 8) (match R with [] => ANum 0 | b :: _ => batch_exp b end)) /\
cell_holds B ly rd' (c8 (aoff (AInst o_q_size) 16) (match rev R with [] => ANum 0 | b :: _ => batch_exp b end)) /\
cell_holds B ly rd' (z8 (aoff (AInst o_q_size) 24) (qc_bytes (st_qglobal X) + qc_bytes (st_qthread X) - sum_bytes P)) /\
Forall (cell_holds B ly rd') (batch_cells R).
Proof.
pose proof qcells as Q. unfold qc_cells in Q. cbn [qc_list qc_bytes qc0 length rev batch_cells Z.of_nat app] in Q.
apply Forall_cons_iff in Q as [Q0 Q]. apply Forall_cons_iff in Q as [Q1 Q].
apply Forall_cons_iff in Q as [Q2 Q]. apply Forall_cons_iff in Q as [Q3 Q]. apply Forall_cons_iff in Q as [Q4 Q]. apply Forall_cons_iff in Q as [Q5 Q].
apply Forall_cons_iff in Q as [Q6 Q]. apply Forall_cons_iff in Q as [Q7 Q]. apply Forall_cons_iff in Q as [Q8 Q]. apply Forall_cons_iff in Q as [Q9 Q].
splits; assumption.
Qed.
(* The entry state's quarantine cells. *)
Lemma oldq : Forall (cell_holds B ly rd) (quar_cells X).
Proof.
apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells B ly X rd qM)).
unfold acells. rewrite !in_app_iff. do 4 right; left. exact Hc.
Qed.
Lemma oldq_batches : Forall (cell_holds B ly rd) (batch_cells Tq) /\ Forall (cell_holds B ly rd) (batch_cells G).
Proof.
pose proof oldq as Q. unfold quar_cells, qc_cells in Q.
apply Forall_cons_iff in Q as [_ Q]. apply Forall_cons_iff in Q as [_ Q]. apply Forall_app in Q as [OT OG].
do 4 (apply Forall_cons_iff in OT as [_ OT]). do 4 (apply Forall_cons_iff in OG as [_ OG]).
split; assumption.
Qed.

Lemma In_PRX : forall b, In b (all_batches X) <-> In b P \/ In b R.
Proof.
intros b. change (all_batches X) with (Tq ++ G). rewrite <- in_app_iff, <- HL, !in_app_iff. tauto.
Qed.
Lemma blen : forall b, In b (all_batches X) -> (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Proof. intros b Hb. exact (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ qWF)) b Hb). Qed.

(* A batch cell word past the next pointer lies in one of the batch's own cells after the first. *)
Lemma own_cover : forall b nx a, SB + b_self b + 8 <= a < SB + b_self b + 24 + 8 * Z.of_nat (length (b_items b)) ->
exists e (w : nat) v (k : nat), In (ACell e w (AV v)) (tl (batch_own_cells b nx)) /\ (k < w)%nat /\ a = aeval B ly e + Z.of_nat k.
Proof.
intros b nx a Ha. cbn [tl batch_own_cells].
assert (EB : forall d, aeval B ly (aoff (batch_exp b) d) = SB + b_self b + d) by (intros d; cbn; lia).
destruct (Z_lt_le_dec a (SB + b_self b + 16)) as [L1|L1].
{ exists (aoff (batch_exp b) 8), 8%nat, (ANum (b_bytes b)), (Z.to_nat (a - (SB + b_self b + 8))). splits; [left; reflexivity | lia | rewrite EB; lia]. }
destruct (Z_lt_le_dec a (SB + b_self b + 24)) as [L2|L2].
{ exists (aoff (batch_exp b) 16), 8%nat, (ANum (Z.of_nat (length (b_items b)))), (Z.to_nat (a - (SB + b_self b + 16))). splits; [right; left; reflexivity | lia | rewrite EB; lia]. }
set (o := a - (SB + b_self b + 24)).
assert (O1 : 0 <= o / 8 < Z.of_nat (length (b_items b))) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (Z.div_mod o 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound o 8 ltac:(lia)) as MB.
destruct (nth_error (b_items b) (Z.to_nat (o / 8))) as [x|] eqn:Ex.
2: { apply nth_error_None in Ex. lia. }
exists (aoff (batch_exp b) (24 + 8 * Z.of_nat (Z.to_nat (o / 8)))), 8%nat, (sptr_exp (ck_hdr x)), (Z.to_nat (o mod 8)). splits.
- right; right. apply in_map_iff. exists (Z.to_nat (o / 8), x). split; [reflexivity|]. exact (combine_seq_in (b_items b) 0 _ x Ex).
- lia.
- rewrite EB. rewrite !Z2Nat.id by lia. subst o. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* YFey's hypotheses.                                                                                               *)
Lemma bcellw_dec : forall l a, bcellw ly l a \/ ~ bcellw ly l a.
Proof.
induction l as [|b t IH]; intros a.
- right. intros (b & [] & _).
- destruct (IH a) as [(b' & Hb' & Rg)|N].
  + left. exists b'. split; [right; exact Hb' | exact Rg].
  + destruct (Z_le_gt_dec (SB + b_self b) a) as [L1|L1];
    [destruct (Z_lt_le_dec a (SB + b_self b + 24 + 8 * Z.of_nat (length (b_items b)))) as [L2|L2]|].
    * left. exists b. split; [left; reflexivity | lia].
    * right. intros (b2 & [<-|Hb2] & Rg); [lia | exact (N (ex_intro _ b2 (conj Hb2 Rg)))].
    * right. intros (b2 & [<-|Hb2] & Rg); [lia | exact (N (ex_intro _ b2 (conj Hb2 Rg)))].
Qed.
Lemma dwin_dec : forall a, dwin_q TFIB_INST ly sp0 X S' P a \/ ~ dwin_q TFIB_INST ly sp0 X S' P a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
unfold dwin_q, qhdr.
destruct (EM (sp0 - DSTACK) sp0) as [C|C0]; [left; left; exact C|].
destruct (EM (TFIB_INST + o_quar + 152) (TFIB_INST + o_quar + 156)) as [C|C1]; [left; right; left; left; exact C|].
destruct (EM (TFIB_INST + o_quar + 160) (TFIB_INST + o_quar + 192)) as [C|C2]; [left; right; left; right; left; exact C|].
destruct (EM (T + t_qc) (T + t_qc + 32)) as [C|C3]; [left; right; left; right; right; exact C|].
destruct (bcellw_dec (all_batches X ++ all_batches S' ++ P) a) as [C|C4]; [left; right; right; exact C|].
right. intros [Y|[[Y|[Y|Y]]|Y]]; [exact (C0 Y) | exact (C1 Y) | exact (C2 Y) | exact (C3 Y) | exact (C4 Y)].
Qed.
Lemma bcellw_X : forall a, bcellw ly (all_batches X ++ all_batches S' ++ P) a ->
exists b, In b (all_batches X) /\ SB + b_self b <= a < SB + b_self b + 24 + 8 * Z.of_nat (length (b_items b)).
Proof.
intros a (b & Hb & Rg). exists b. split; [|exact Rg].
apply in_app_iff in Hb as [Hb|Hb]; [exact Hb|]. apply In_PRX.
apply in_app_iff in Hb as [Hb|Hb]; [right; exact Hb | left; exact Hb].
Qed.
Lemma dwin_zone : forall a, dwin_q TFIB_INST ly sp0 X S' P a ->
(ly_stk_lo ly <= a < ly_stk_hi ly) \/ (as_inst B + o_q_cmutex <= a < as_inst B + o_q_cmutex + 4 \/ as_inst B + o_q_size <= a < as_inst B + o_q_size + 32) \/
(T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize).
Proof.
intros a Hw. pose proof qEI as EI. pose proof qHIGH as (_ & _ & _ & _ & _ & _ & H7 & H8 & H9 & _).
unfold dwin_q, qhdr in Hw. destruct Hw as [Y|[[Y|[Y|Y]]|Y]].
- left. unfold YFeuC.DSTACK, DSTACK in *. lia.
- right; left. left. rewrite EI. unfold o_quar, o_q_cmutex in *. lia.
- right; left. right. rewrite EI. unfold o_quar, o_q_size in *. lia.
- right; right; left. unfold t_qc, kThreadObjSize in *. lia.
- do 3 right. destruct (bcellw_X a Y) as (b & Hb & Rg). destruct (H9 b Hb) as [L1 L2]. pose proof (blen b Hb) as BL.
  unfold YFey.addr, kBatchBytes, kSpaceSize, kPrimResvSize, kBatchSlots in *. cbn in BL. lia.
Qed.
Lemma raw_out : forall a, 0 <= a < 2 ^ 64 -> ~ dwin_q TFIB_INST ly sp0 X S' P a -> rd' a = rd a.
Proof. intros a Ha Hn. apply aview_same. destruct DQ as (D1 & _). apply D1. rewrite unsigned_lit_small by exact Ha. exact Hn. Qed.

(* The thread header, the mutex word and the global header after the cut. *)
Lemma qNEW_t : forall j i, 0 <= j < 4 -> (i < 8)%nat -> rd' (T + t_qc + 8 * j + Z.of_nat i) = Some (YG0f.le_byte 0 8 i).
Proof.
intros j i Hj Hi. pose proof qcells_parts as (_ & _ & C0 & C8 & C16 & C24 & _).
assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
destruct J as [-> | [-> | [-> | ->]]].
- replace (T + t_qc + 8 * 0 + Z.of_nat i) with (aeval B ly (AT t_qc) + Z.of_nat i) by (cbn; lia). exact (ch_get _ _ _ _ i C0 Hi).
- replace (T + t_qc + 8 * 1 + Z.of_nat i) with (aeval B ly (aoff (AT t_qc) 8) + Z.of_nat i) by (cbn; lia). exact (ch_get _ _ _ _ i C8 Hi).
- replace (T + t_qc + 8 * 2 + Z.of_nat i) with (aeval B ly (aoff (AT t_qc) 16) + Z.of_nat i) by (cbn; lia). exact (ch_get _ _ _ _ i C16 Hi).
- replace (T + t_qc + 8 * 3 + Z.of_nat i) with (aeval B ly (aoff (AT t_qc) 24) + Z.of_nat i) by (cbn; lia). exact (ch_get _ _ _ _ i C24 Hi).
Qed.
Lemma qNEW_mx : forall i, 0 <= i < 4 -> rd' (as_inst B + o_q_cmutex + i) = Some 0.
Proof.
intros i Hi. pose proof qcells_parts as (M0 & M1 & _). destruct DQ as (_ & _ & _ & D4).
assert (J : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
destruct J as [-> | [-> | [-> | ->]]].
- replace (as_inst B + o_q_cmutex + 0) with (aeval B ly (AInst o_q_cmutex) + Z.of_nat 0) by (cbn; lia). rewrite (ch_get _ _ _ _ 0 M0) by lia. reflexivity.
- replace (as_inst B + o_q_cmutex + 1) with (aeval B ly (AInst o_q_rmutex) + Z.of_nat 0) by (cbn; unfold o_q_rmutex, o_q_cmutex; lia). rewrite (ch_get _ _ _ _ 0 M1) by lia. reflexivity.
- rewrite qEI. exact (YFet.val_mem_aview (w_H W) mem' (TFIB_INST + o_q_cmutex + 2) 2%nat 0 0%nat D4 ltac:(lia)).
- rewrite qEI. exact (YFet.val_mem_aview (w_H W) mem' (TFIB_INST + o_q_cmutex + 2) 2%nat 0 1%nat D4 ltac:(lia)).
Qed.
Lemma qNEW_qs : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_size + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length R)) 8 i).
Proof. intros i Hi. pose proof qcells_parts as (_ & _ & _ & _ & _ & _ & C & _). exact (ch_get _ _ _ _ i C Hi). Qed.
Lemma qNEW_qf : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_first + Z.of_nat i) = Some (YG0f.le_byte (YFey.RFv ly R) 8 i).
Proof.
intros i Hi. pose proof qcells_parts as (_ & _ & _ & _ & _ & _ & _ & C & _).
replace (as_inst B + o_q_first) with (aeval B ly (aoff (AInst o_q_size) 8)) by (cbn; unfold o_q_size, o_q_first; lia).
rewrite (ch_get _ _ _ _ i C Hi). unfold YFey.RFv, YFey.addr. destruct R; reflexivity.
Qed.
Lemma qNEW_ql : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_last + Z.of_nat i) = Some (YG0f.le_byte (YFey.RLv ly R) 8 i).
Proof.
intros i Hi. pose proof qcells_parts as (_ & _ & _ & _ & _ & _ & _ & _ & C & _).
replace (as_inst B + o_q_last) with (aeval B ly (aoff (AInst o_q_size) 16)) by (cbn; unfold o_q_size, o_q_last; lia).
rewrite (ch_get _ _ _ _ i C Hi). unfold YFey.RLv, YFey.addr. destruct (rev R); reflexivity.
Qed.
Lemma qNEW_qb : forall i, (i < 8)%nat ->
rd' (as_inst B + o_q_bytes + Z.of_nat i) = Some (YG0f.le_byte (qc_bytes (st_qglobal X) + qc_bytes (st_qthread X) - sum_bytes P) 8 i).
Proof.
intros i Hi. pose proof qcells_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & C & _).
replace (as_inst B + o_q_bytes) with (aeval B ly (aoff (AInst o_q_size) 24)) by (cbn; unfold o_q_size, o_q_bytes; lia).
exact (ch_get _ _ _ _ i C Hi).
Qed.

(* Positions in R and in the concatenated list. *)
Lemma R_pos : forall i b, nth_error R i = Some b -> nth_error (G ++ Tq) (length P + i) = Some b /\ next_exp R i = next_exp (G ++ Tq) (length P + i).
Proof.
intros i b Hi. rewrite HL. split.
- rewrite nth_error_app2 by lia. replace (length P + i - length P)%nat with i by lia. exact Hi.
- unfold next_exp. rewrite nth_error_app2 by lia. replace (S (length P + i) - length P)%nat with (S i) by lia. reflexivity.
Qed.
Lemma new_cell_R : forall i b c, nth_error R i = Some b -> In c (batch_own_cells b (next_exp R i)) -> cell_holds B ly rd' c.
Proof.
intros i b c Hi Hc. pose proof qcells_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
apply (proj1 (Forall_forall _ _) QR). apply In_batch_cells. exists i, b. split; [exact Hi | exact Hc].
Qed.
Lemma new_cell_P : forall i b c, nth_error P i = Some b -> In c (batch_own_cells b (next_exp P i)) -> cell_holds B ly rd' c.
Proof. intros i b c Hi Hc. apply (proj1 (Forall_forall _ _) PLC). apply In_batch_cells. exists i, b. split; [exact Hi | exact Hc]. Qed.
Lemma old_cell : forall b nx c, In b (all_batches X) -> In c (tl (batch_own_cells b nx)) -> cell_holds B ly rd c.
Proof.
intros b nx c Hb Hc. pose proof oldq_batches as [OT OG]. cbn [tl batch_own_cells] in Hc.
change (all_batches X) with (Tq ++ G) in Hb. apply in_app_iff in Hb as [Hb|Hb].
- apply In_nth_error in Hb as [i Hi]. apply (proj1 (Forall_forall _ _) OT). apply In_batch_cells. exists i, b. split; [exact Hi|]. right. exact Hc.
- apply In_nth_error in Hb as [i Hi]. apply (proj1 (Forall_forall _ _) OG). apply In_batch_cells. exists i, b. split; [exact Hi|]. right. exact Hc.
Qed.

(* The batch cell words outside YFey's window D are unchanged. *)
Lemma bval : forall b a, In b (all_batches X) -> SB + b_self b <= a < SB + b_self b + 24 + 8 * Z.of_nat (length (b_items b)) ->
~ YFey.D B ly X P sp0 a -> rd' a = rd a.
Proof.
intros b a Hb Rg ND. pose proof (proj1 (In_PRX b) Hb) as HPR.
destruct (Z_lt_le_dec a (SB + b_self b + 8)) as [N8|N8].
- destruct HPR as [HP|HR].
  + exfalso. apply ND. unfold YFey.D. right; right; right; left. exists b. split; [exact HP | unfold YFey.addr; lia].
  + apply In_nth_error in HR as [i Hi]. destruct (R_pos i b Hi) as [Hj NX].
    pose proof (new_cell_R i b _ Hi (or_introl eq_refl)) as NC. rewrite NX in NC.
    set (j := (length P + i)%nat) in *.
    assert (OC : cell_holds B ly rd (c8 (batch_exp b) (next_exp (G ++ Tq) j))).
    { pose proof oldq_batches as [OT OG]. destruct (Nat.lt_ge_cases j (length G)) as [LT|GE].
      - rewrite nth_error_app1 in Hj by exact LT. destruct (Nat.eq_dec (S j) (length G)) as [EJ|NJ].
        + exfalso. apply ND. unfold YFey.D. right; right; left. unfold YFey.DL.
          destruct (nth_error_split _ _ Hj) as (l1 & l2 & E0 & Ll1).
          assert (l2 = []) as -> by (apply (f_equal (@length _)) in E0; rewrite length_app in E0; cbn in E0; destruct l2; [reflexivity | cbn in E0; lia]).
          split; [rewrite E0; intros E1; destruct l1; discriminate|].
          unfold YFey.GLv. rewrite E0, rev_app_distr. cbn [rev app]. unfold YFey.addr. lia.
        + replace (next_exp (G ++ Tq) j) with (next_exp G j) by (unfold next_exp; rewrite nth_error_app1 by lia; reflexivity).
          apply (proj1 (Forall_forall _ _) OG). apply In_batch_cells. exists j, b. split; [exact Hj | left; reflexivity].
      - rewrite nth_error_app2 in Hj by exact GE.
        replace (next_exp (G ++ Tq) j) with (next_exp Tq (j - length G))
          by (unfold next_exp; rewrite nth_error_app2 by lia; replace (S j - length G)%nat with (S (j - length G)) by lia; reflexivity).
        apply (proj1 (Forall_forall _ _) OT). apply In_batch_cells. exists (j - length G)%nat, b. split; [exact Hj | left; reflexivity]. }
    replace a with (aeval B ly (batch_exp b) + Z.of_nat (Z.to_nat (a - (SB + b_self b)))) by (cbn; lia).
    apply (ch_both _ _ _ _ _ _ OC NC). lia.
- destruct (own_cover b (ANum 0) a ltac:(lia)) as (e & w & v & k & Hc & Hk & ->).
  pose proof (old_cell b (ANum 0) _ Hb Hc) as OC.
  assert (NC : cell_holds B ly rd' (ACell e w (AV v))).
  { cbn [tl batch_own_cells] in Hc. destruct HPR as [HP|HR].
    - apply In_nth_error in HP as [i Hi]. apply (new_cell_P i b _ Hi). cbn [batch_own_cells]. right. exact Hc.
    - apply In_nth_error in HR as [i Hi]. apply (new_cell_R i b _ Hi). cbn [batch_own_cells]. right. exact Hc. }
  exact (ch_both _ _ _ _ _ _ OC NC Hk).
Qed.

Lemma qAG : forall a, 0 <= a < 2 ^ 64 -> ~ YFey.D B ly X P sp0 a -> rd' a = rd a.
Proof.
intros a Ha ND. destruct (dwin_dec a) as [Dw|NDw]; [|exact (raw_out a Ha NDw)].
pose proof Dw as Dw'. unfold dwin_q in Dw'. destruct Dw' as [Hs|[Hq|Hb]].
- exfalso. apply ND. unfold YFey.D. do 4 right. unfold YFey.DS. exact Hs.
- exfalso. apply ND. unfold YFey.D, YFey.DT, YFey.DQ. rewrite qEI. unfold qhdr in Hq. unfold o_quar, o_q_cmutex, o_q_size in *.
  destruct Hq as [Hq|[Hq|Hq]]; [right; left; left; lia | right; left; right; lia | left; exact Hq].
- destruct (bcellw_X a Hb) as (b & HbX & Rg). exact (bval b a HbX Rg ND).
Qed.

Lemma vm_nz : forall (a : Z) (w : nat) (v x : Z), val_mem tfibsegs (mrestrict (w_H W) mem') a w v ->
a <= x < a + Z.of_nat w -> rd' x <> None.
Proof.
intros a w v x H Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (YFet.val_mem_aview (w_H W) mem' a w v (Z.to_nat (x - a)) H ltac:(lia)). discriminate.
Qed.
Lemma qhdr_dec : forall a, qhdr TFIB_INST ly a \/ ~ qhdr TFIB_INST ly a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia). unfold qhdr.
destruct (EM (TFIB_INST + o_quar + 152) (TFIB_INST + o_quar + 156)) as [C|C1]; [left; left; exact C|].
destruct (EM (TFIB_INST + o_quar + 160) (TFIB_INST + o_quar + 192)) as [C|C2]; [left; right; left; exact C|].
destruct (EM (T + t_qc) (T + t_qc + 32)) as [C|C3]; [left; right; right; exact C|].
right. intros [Y|[Y|Y]]; [exact (C1 Y) | exact (C2 Y) | exact (C3 Y)].
Qed.
Lemma qhdr_vis : forall a, qhdr TFIB_INST ly a -> rd' a <> None.
Proof.
intros a Hq. pose proof qcells_parts as (M0 & M1 & C0 & C8 & C16 & C24 & G0 & G8 & G16 & G24 & _). destruct DQ as (_ & _ & _ & D4).
pose proof qEI as EI. unfold qhdr in Hq. destruct Hq as [Hq|[Hq|Hq]].
- destruct (Z.eq_dec a (TFIB_INST + o_quar + 152)) as [E|N1]; [apply (ch_some _ _ _ _ a M0); cbn; rewrite EI; unfold o_quar, o_q_cmutex in *; lia|].
  destruct (Z.eq_dec a (TFIB_INST + o_quar + 153)) as [E|N2]; [apply (ch_some _ _ _ _ a M1); cbn; rewrite EI; unfold o_quar, o_q_rmutex in *; lia|].
  apply (vm_nz (TFIB_INST + o_q_cmutex + 2) 2%nat 0 a D4). unfold o_quar, o_q_cmutex in *. lia.
- destruct (Z_lt_le_dec a (TFIB_INST + o_quar + 168)) as [L1|L1]; [apply (ch_some _ _ _ _ a G0); cbn; rewrite EI; unfold o_quar, o_q_size in *; lia|].
  destruct (Z_lt_le_dec a (TFIB_INST + o_quar + 176)) as [L2|L2]; [apply (ch_some _ _ _ _ a G8); cbn; rewrite EI; unfold o_quar, o_q_size in *; lia|].
  destruct (Z_lt_le_dec a (TFIB_INST + o_quar + 184)) as [L3|L3]; [apply (ch_some _ _ _ _ a G16); cbn; rewrite EI; unfold o_quar, o_q_size in *; lia|].
  apply (ch_some _ _ _ _ a G24); cbn; rewrite EI; unfold o_quar, o_q_size in *; lia.
- destruct (Z_lt_le_dec a (T + t_qc + 8)) as [L1|L1]; [apply (ch_some _ _ _ _ a C0); cbn; lia|].
  destruct (Z_lt_le_dec a (T + t_qc + 16)) as [L2|L2]; [apply (ch_some _ _ _ _ a C8); cbn; lia|].
  destruct (Z_lt_le_dec a (T + t_qc + 24)) as [L3|L3]; [apply (ch_some _ _ _ _ a C16); cbn; lia|].
  apply (ch_some _ _ _ _ a C24); cbn; lia.
Qed.

Lemma qVIS : forall a, rd a <> None -> rd' a <> None.
Proof.
intros a Hv HN. destruct DQ as (_ & _ & D3 & _).
unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem' x); discriminate|].
destruct (mem' x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
destruct (qhdr_dec a') as [Hq|Hq].
- apply (qhdr_vis a' Hq). unfold aview, mbyte, mrestrict. cbv beta. rewrite Ex, Hx, E', ROM. reflexivity.
- assert (AP : apresent (w_H W) mem a') by (unfold apresent; rewrite Ex; split; [exact Hx | exists b0; exact E0]).
  destruct (D3 a' Hq AP) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
Qed.

(* The last batch of the global list now points at the thread list's first batch. *)
Lemma qNEW_J : forall lb initr, rev G = lb :: initr -> (length P < length G)%nat ->
forall kk, (kk < 8)%nat -> rd' (YFey.addr ly lb + Z.of_nat kk) = Some (YG0f.le_byte (YFey.TFv ly X) 8 kk).
Proof.
intros lb initr Hrev LT kk Hkk.
assert (EG : G = rev initr ++ [lb]) by (rewrite <- (rev_involutive G), Hrev; reflexivity).
set (k0 := length (rev initr)).
assert (LG : length G = S k0) by (rewrite EG, length_app; cbn [length]; subst k0; lia).
assert (HP : nth_error (P ++ R) k0 = Some lb).
{ rewrite <- HL, EG, <- app_assoc, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
rewrite nth_error_app2 in HP by lia.
pose proof (new_cell_R (k0 - length P) lb _ HP (or_introl eq_refl)) as NC.
destruct (R_pos _ _ HP) as [_ NX]. rewrite NX in NC.
replace (length P + (k0 - length P))%nat with k0 in NC by lia.
replace (YFey.addr ly lb) with (aeval B ly (batch_exp lb)) by (cbn; unfold YFey.addr; lia).
rewrite (ch_get _ _ _ _ kk NC Hkk). f_equal. f_equal.
unfold next_exp. rewrite nth_error_app2 by lia. rewrite LG, Nat.sub_diag.
unfold YFey.TFv, YFey.addr. destruct (qc_list (st_qthread X)); reflexivity.
Qed.

Lemma qHTSD : ly_tsd ly = TFIB_TSD.
Proof. rewrite (am_tsd B ly X rd qM). apply (ts_tsd _ TB). Qed.

(* The image's constant cells: the two bytes after the mutex word are 0 at the cut (dmem_q); the others lie
   outside the cut window (YFev.Tfib_const_locd, as YFev.CONST_OUT). *)
Lemma qCONST : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (am_const B ly X rd qM) c Hc) as OLDc.
rewrite (ts_const _ TB) in Hc.
pose proof (proj1 (forallb_forall _ _) (YFev.Tfib_const_locd ly) c Hc) as K. unfold YFev.const_loc_okd in K.
pose proof qHIGH as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _ & _ & _ & hI1 & hI2).
pose proof qGEO as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & ZC & ZD).
pose proof qEI as EI. pose proof qHTSD as HTSD. destruct DQ as (_ & _ & _ & D4).
assert (ZN : forall a, ~ ((ly_stk_lo ly <= a < ly_stk_hi ly) \/
  (as_inst B + o_q_cmutex <= a < as_inst B + o_q_cmutex + 4 \/ as_inst B + o_q_size <= a < as_inst B + o_q_size + 32) \/
  (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ dwin_q TFIB_INST ly sp0 X S' P a).
{ intros a Hn Hw. exact (Hn (dwin_zone a Hw)). }
assert (LOW : forall a i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> YFev.low_okd a (Z.max 1 (Z.of_nat (c_w c))) = true ->
  ~ dwin_q TFIB_INST ly sp0 X S' P (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a i Hi L. unfold YFev.low_okd in L.
  split; [apply ZN|]; clear - L Hi hP1 hT1 hS1 EI; rewrite ?EI; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize, DSTACK, TFIB_INST, o_q_cmutex, o_q_size, o_q_bytes in *;
  change (65536 / 8) with 8192 in *; change (6279168 / 8) with 784896 in *; lia. }
assert (CASE : (c_at c = ANum 0xa514a /\ c_w c = 2%nat) \/
  (forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + i) = rd (aeval B ly (c_at c) + i))).
{ destruct (c_at c) as [z|z|z|z|z|z|z|z|r z|z|z|z|z|z|z|z|z|z|e] eqn:EC; try discriminate K; cbn [aeval].
  - apply Bool.orb_prop in K as [K|K]; [right; intros i Hi; destruct (LOW z i Hi K) as [N R0]; exact (raw_out _ R0 N)|].
    apply Bool.orb_prop in K as [K|K]; apply andb_prop in K as [K1 K2]; apply Z.eqb_eq in K1; apply Z.eqb_eq in K2; subst z.
    + left. split; [reflexivity | lia].
    + right. intros i Hi. apply raw_out; [lia|]. apply ZN. clear - K2 Hi hP1 hT1 hS1 EI. rewrite EI.
      unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, TFIB_INST, o_q_cmutex, o_q_size in *. lia.
  - right. intros i Hi. apply raw_out; [|apply ZN]; clear - K Hi hT1 hT2 hS1 hS2 G_PT G_TS hI1 hI2 EI; rewrite ?EI; ceil;
    unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, kLowMemEnd, TFIB_INST, o_q_cmutex, o_q_size, o_q_bytes in *; lia.
  - right. intros i Hi. apply raw_out; [|apply ZN]; clear - K Hi ZC hS1 hS2 G_PC G_TC G_CS hI1 hI2 EI; rewrite ?EI; ceil;
    unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, kLowMemEnd, TFIB_INST, o_q_cmutex, o_q_size, o_q_bytes in *; lia.
  - right. intros i Hi. rewrite HTSD. destruct (LOW _ i Hi K) as [N R0]. exact (raw_out _ R0 N).
  - right. intros i Hi. rewrite EI. destruct (LOW _ i Hi K) as [N R0]. exact (raw_out _ R0 N).
  - right. intros i Hi. rewrite (ts_tp _ TB). destruct (LOW _ i Hi K) as [N R0]. exact (raw_out _ R0 N).
  - right. intros i Hi. apply raw_out; [|apply ZN]; clear - K Hi ZD hS1 hS2 G_PD G_TD G_DS hI1 hI2 EI; rewrite ?EI; ceil;
    unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, kLowMemEnd, TFIB_INST, o_q_cmutex, o_q_size, o_q_bytes in *; lia. }
destruct CASE as [[EC EW]|AGR].
- unfold cell_holds in OLDc |- *. destruct c as [e w v]; cbn [c_at c_w c_val] in *. subst e w.
  assert (Hv : v = AV (ANum 0)).
  { clear - Hc. cbv [Tfib_const Tfib_const_sym Tfib_const_abs Tfib_const_shadow app In z8 z4 z2 z1 c8 c4 c2 c1] in Hc.
    repeat (destruct Hc as [Hc|Hc]; [first [congruence | discriminate] |]). destruct Hc. }
  subst v. intros k Hk. cbn [aeval].
  exact (YFet.val_mem_aview (w_H W) mem' (TFIB_INST + o_q_cmutex + 2) 2%nat 0 k D4 Hk).
- eapply (cell_holds_agree B ly rd); [exact OLDc|]. intros i Hi. exact (AGR i Hi).
Qed.

(* Hidden band bytes are outside the cut window. *)
Lemma qHSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a).
Proof.
intros a Hb _. destruct DQ as (D1 & _).
assert (Ha : 0 <= a < 2 ^ 64) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb; lia).
unfold w64. apply D1. rewrite unsigned_lit_small by exact Ha. intros Hw. pose proof (dwin_zone a Hw) as Z3.
pose proof qHIGH as (hP1 & _ & hT1 & _ & hS1 & _ & _ & _ & _ & hI1 & hI2). pose proof qEI as EI.
clear - Z3 Hb hP1 hT1 hS1 hI1 hI2 EI. rewrite EI in *.
unfold in_band_rw, zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kThreadObjSize, kHighMemBeg, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd,
kLowMemEnd, kPrimResvSize, TFIB_INST, o_q_cmutex, o_q_size in *. lia.
Qed.

(* AR at the cut state. *)
Lemma requar_AR : forall md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
AR tfibsegs B ly S' W mem' md'.
Proof.
intros md' Ev El Ee. pose proof HAR as (M & LED & BUD & MW & HSH).
pose proof (YFey.drain_fin_ARm B TB ly X rd rd' M HTB P R HL sp0 HSP qIMG qAG qVIS qNEW_t qNEW_mx qNEW_qs qNEW_qf qNEW_ql qNEW_qb qNEW_J qCONST) as MF.
pose proof qHIGH as (hP1 & _ & hT1 & _ & hS1 & _ & _ & _ & H9 & _ & _). pose proof qEI as EI.
split; [exact MF|]. split; [|split; [|split]].
- eapply ALedger_same; [exact (YFey.ALedger_S' ly X P R tfibsegs md LED) | exact Ev | exact El | exact Ee].
- destruct BUD as [BUD PIN]. split; [| exact (YFey.asecA_S' ly X P R _ PIN)]. rewrite (YFey.abudget_S' X P R). exact BUD.
- exact (amwf_same md md' Ev El MW).
- eapply (ahs_transfer tfibsegs B ly X _ (w_H W) mem mem' (al_img_env tfibsegs ly X md (am_layout B ly X _ M) LED) M HSH qVIS qHSK).
  + eapply (aclient_band_same_frames B ly X); [exact MF | exact (YFey.frames' X P R)].
  + exact (YFey.sec_extents' ly X P R).
  + intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg.
    apply qAG; [clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; lia|].
    intros HD. apply (YFey.D_cases B ly X rd M P R HL sp0 HSP qIMG) in HD.
    unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg.
    destruct HD as [[Y _]|[[Y _]|[(b2 & Hb2 & Y & _)|Y]]].
    * clear - Y SBg hT1. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
    * rewrite EI in Y. clear - Y SBg. unfold TFIB_INST, o_q_cmutex, o_q_bytes in *. lia.
    * destruct (H9 b2 Hb2) as [L4 _]. clear - Y L4 hP1 SBg. unfold YFey.addr, kHighMemBeg in *. lia.
    * clear - Y SBg hS1. unfold kHighMemBeg in *. lia.
Qed.
End q.

(* Merge is vacuous at cgif: qloose and Wf cap the batches at 16384 (YG0m.batches_len_fuel), so with more than
   kQuarantineMax = 2^28 bytes the test bytes < 2 * kBatchBytes * L of Recycle (0x33da0) fails. *)
Lemma merge_vacuous : forall U X, WfP U 0 0 0 X -> qloose X -> kQuarantineMax < qc_bytes (YFeuC.transfer_g X) ->
merge_split_cf (YFeuC.transfer_g X) = (YFeuC.transfer_g X, []).
Proof.
intros U X W QL HB. pose proof (batches_len_fuel U 0 0 0 X W QL) as BL. unfold merge_split_cf. cbv zeta.
assert (LEN : Z.of_nat (length (qc_list (YFeuC.transfer_g X))) <= 16384) by (cbn [YFeuC.transfer_g qc_list]; unfold all_batches in BL; rewrite length_app in *; lia).
replace (qc_bytes (YFeuC.transfer_g X) <? 2 * (kBatchBytes * Z.of_nat (length (qc_list (YFeuC.transfer_g X))))) with false
  by (symmetry; apply Z.ltb_ge; unfold kBatchBytes, kQuarantineMax in *; lia).
rewrite andb_false_r. reflexivity.
Qed.

(* The recycle invariant at DoRecycle's call in the form DRq takes (DGif1d.DRq_cgif). *)
Lemma RI_RIx_flat : forall U s P, RI U 0 0 0 s P -> RIx U 0 0 0 s (flat_map b_items P) [] (map b_self P).
Proof.
intros U s P H. destruct (RI_RIx U 0 0 0 s P H) as (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold RIx. cbn [app flat_map map] in *.
rewrite !app_nil_r. splits; [exact A1 | exact A2 | exact A3 | constructor | exact A5 | exact A6 | exact A7].
Qed.
End c.

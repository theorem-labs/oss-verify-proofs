(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Reusable/DGif0.v, with its module paths and module names changed; 671 of its 717 lines of code are new or changed and 218 lines of the source are left out. *)
(* The AR -> ARU transfer of a Theorem Labs lane's frozen Deallocate interface record DGif0.DIface (a Theorem Labs lane;
   rule 24: no function proved, kind "statement transfer of an interface record").

   [diface_U]: if the AR instance satisfies DIface (ARX = ARXr = [ARX_AR im_segs B I], AOX = [aowned B], the free call
   site's premise [fun _ _ _ _ _ _ => True]), then the ARU instance satisfies it (ARX = ARXr = [ARX_ARU im_segs B I Up],
   AOX = [aowned B], fpre = [fpreU im_segs B Up]), every other parameter the same abstract variable.  The four fields
   that ARE callee contracts (di_enqueue, di_drain, di_rchunk, di_cdealloc) are premises in their ARU form (the
   a Theorem Labs lane decision, 12:13Z): [di_enqueue_t] below is the exact text of DGif0.v's di_enqueue field,
   so the constructor takes each premise by conversion.

   How each field transfers (the kinds of the lane's method):
   - kind 1 (takes ARX, concludes on the model / AOX; applied at the unpoisoned memory): di_inst, di_qowned, di_stack,
     di_owned, di_owned_b, di_owned_i, di_owned_x, di_lpost_d; no ARX at all: di_shape_n, di_shape, di_dpost_aok.
   - kind 2 (views; each fixed cell is off Up): di_view_n ([dview_n_U]), di_view ([dview_U], [dbview_U]: the block's
     header and first word are chunk memory, its shadow is apart from Up by [fpreU]), di_qview ([qview_U]: instance and
     thread cells, batch objects in the primary space), di_rview (the instance's o_space word).
   - kind 3 (callee entry, zones): di_depot (the zones are off Up by [zones_free]).
   - kind 4 (posts; the machine post moves through the unpoisoning, then ARU is rebuilt with ARU_rebuild_raw):
     di_post_c ([dmem_c_U]; the freed block becomes CQuarantined and leaves ablocks: it holds no range of Up by
     [fpreU]; every other block survives in qfin_c), di_post_n ([dmem_n_U]), di_requar_x / di_requar_r ([dmem_q_U]:
     the drain changes only the quarantine, so ablocks is unchanged; its windows are stack, quarantine headers and batch
     cells in the primary space).
   - laws: di_frame / di_frame_r (one proof: FSupoison.ARU_frame with YG0q.AR_laws_ok), di_requar_e (ARXr = ARX on
     the ARU side: the identity).
   - kind 5 (callee contracts, premises): di_enqueue, di_drain, di_rchunk, di_cdealloc.

   The premises and the fs facts that discharge them:
   | [inst_low dg_inst_ok]       | lib/A|B/FSupoisonARX.fs_inst_low (fs's DImg: dg_inst_ok inst := inst = TFIB_INST)   |
   | [zones_free im_segs B dg_dzone (fun ly a => dg_czone ly a /\ ~ dg_izone a)]                                       |
   |                             | lib/A|B/FSupoisonARX.fs_zones_free / zones_free_shape (zones_free is monotone in    |
   |                             | the CZONE argument, so the conjunct [~ dg_izone] only shrinks it)                  |
   | [izone_low]                 | fs's dg_izone = AFgi.IZONE (AFgi.v:486; B: YFgi.v:484) = [TFIB_IAL_LO, TFIB_IAL_HI) |
   |                             | \/ [TFIB_IAL_FLAG, +4): 0xa9140, 0x12a170, 0x1379c8 (AF0m.v:18-19), all below       |
   |                             | SHADOW_OFF = 0x7fff8000                                                              |
   | [ial_local]                 | fs's dg_ial_post = AFgi.IAL_POST (AFgi.v:562-566; B: YFgi.v:560) reads only          |
   |                             | TFIB_IAL_FLAG, +1, TFIB_IAL_W .. +16 and [TFIB_IAL_LO, TFIB_IAL_HI): IZONE cells     |
   |                             | (the argument of AFgi.MEQI_frame, AFgi.v:574)                                        |

   DIfaceR (lib/Reusable/DIfaceR.v): every field is a callee contract (kind 5), so it has no generic transfer; see the
   note at the end of the file.

   Requires only lib/Reusable, lib/A/FSupoison and lib/A/FSupoisonARXm (image-free).  No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG03 YG06 YG0k YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DeallocG ImgBase ImgBaseDG DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonARXm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Helpers: where the cells of the records lie, off Up.                                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section aux. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* An Up byte is not off Up. *)
Lemma ush_not_off : forall segs B ly S Up W mem md s, FSP.ARU segs B ly S Up W mem md ->
FSP.in_ush Up s = true -> ~ off_ush Up s.
Proof.
intros segs B ly S Up W mem md s H Hs HO. unfold off_ush in HO.
pose proof (ush_band segs B ly S Up W mem md s H Hs) as (_ & _ & R).
rewrite (Z.mod_small s _ R) in HO. rewrite HO in Hs. discriminate Hs.
Qed.

(* The converse of the toolkit's [cell_holds_unpoison]. *)
Lemma cell_holds_unpoison_r : forall segs B ly (H : word -> bool) Up m c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> off_ush Up (aeval B ly (c_at c) + k)) ->
cell_holds B ly (aview segs H m) c -> cell_holds B ly (aview segs H (FSP.unpoison Up m)) c.
Proof.
intros segs B ly Hh Up m c HO HC. unfold cell_holds in *. destruct (c_val c) as [e|mask val].
- intros k Hk. rewrite (aview_unpoison_off segs Hh Up m (aeval B ly (c_at c) + Z.of_nat k)) by (apply HO; lia).
  exact (HC k Hk).
- destruct HC as (b & Hb & Hm). exists b. split; [|exact Hm].
  rewrite (aview_unpoison_off segs Hh Up m (aeval B ly (c_at c)));
  [ exact Hb
  | replace (aeval B ly (c_at c)) with (aeval B ly (c_at c) + 0) by lia; apply HO; lia ].
Qed.

Lemma blocks_chunk : forall S p n, In (p, n) (blocks S) ->
exists k, In k (st_chunks S) /\ ck_user k = p /\ ck_req k = n /\ ck_state k = CAllocated.
Proof.
intros S p n H. unfold blocks in H. apply in_map_iff in H as (k & E & Hk). injection E as E1 E2.
apply filter_In in Hk as [Hk Ha]. exists k. split; [exact Hk|]. split; [exact E1|]. split; [exact E2|].
unfold is_alloc in Ha. destruct (ck_state k); [reflexivity | discriminate Ha].
Qed.

Lemma nodup_beg_inj : forall (l : list chunk) a b, List.NoDup (map ck_beg l) -> In a l -> In b l ->
ck_beg a = ck_beg b -> a = b.
Proof.
intros l a b ND Ha Hb E. destruct (In_split_beg l a Ha ND) as (l1 & l2 & -> & N1 & N2).
apply in_app_iff in Hb as [Hb|[Hb|Hb]].
- exfalso. apply N1. rewrite E. apply in_map. exact Hb.
- congruence.
- exfalso. apply N2. rewrite E. apply in_map. exact Hb.
Qed.

(* A live block: its address, and its header and first word are chunk memory (off Up). *)
Lemma blk_geo : forall segs B ly S Up W mem md p n, FSP.ARU segs B ly S Up W mem md -> In (p, n) (blocks S) ->
sptr_addr B ly p mod 16 = 0 /\ sptr_addr B ly p mod 8 = 0 /\ 1 <= req_size n /\ 4112 <= sptr_addr B ly p /\
sptr_addr B ly p + req_size n <= ASAN_CEIL /\
(forall a, sptr_addr B ly p - 16 <= a < sptr_addr B ly p + 8 -> off_ush Up a).
Proof.
intros segs B ly S Up W mem md p n H Hb.
destruct (blocks_chunk S p n Hb) as (k & Hk & Hu & Hn & _). subst p n.
pose proof (FSP.ARU_ARm segs B ly S Up W mem md H) as M.
pose proof (chunk_facts B ly S _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req k) (proj1 G7)) as (_ & Q1 & _).
pose proof ASAN_CEIL_range as [CR _].
rewrite G4.
assert (A16 : (ck_base B ly k + ck_rz k) mod 16 = 0) by (rewrite Z.add_mod by lia; rewrite G3, G6; reflexivity).
assert (A8 : (ck_base B ly k + ck_rz k) mod 8 = 0).
{ apply Z.mod_divide in A16 as [q Hq]; [|lia]. rewrite Hq. replace (q * 16) with ((q * 2) * 8) by lia.
  apply Z.mod_mul. lia. }
unfold in_app in G1.
split; [exact A16|]. split; [exact A8|]. split; [exact Q1|]. split; [lia|]. split; [lia|].
intros a Ha. destruct G1 as [L0 [L1 | [L2 L3]]].
- apply (low_off_ush segs B ly S Up W mem md a H). unfold kLowShadowBeg, SHADOW_OFF in *. lia.
- apply (high_off_ush segs B ly S Up W mem md a H). unfold kHighMemBeg in *. lia.
Qed.

(* The freed block's shadow is apart from Up's: the ranges and the block are disjoint and 8-aligned. *)
Lemma dshadow_off : forall segs B ly S Up W mem md pa nn s, FSP.ARU segs B ly S Up W mem md ->
pa mod 8 = 0 -> 0 <= pa -> 0 <= nn -> pa + nn <= ASAN_CEIL ->
(forall r, In r Up -> fst r + snd r <= pa \/ pa + nn <= fst r) ->
dshadow pa nn s -> off_ush Up s.
Proof.
intros segs B ly S Up W mem md pa nn s H P8 P0 N0 PC FP Hs.
unfold off_ush. destruct (FSP.in_ush Up (s mod 2 ^ 64)) eqn:E; [|reflexivity]. exfalso.
pose proof ASAN_CEIL_range as [CR _].
unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v in Hs.
assert (SR : 0 <= s < 2 ^ 64).
{ clear - Hs P0 N0 PC CR. unfold SHADOW_OFF in *. Z.div_mod_to_equations. lia. }
rewrite (Z.mod_small s _ SR) in E.
apply FSP.in_ush_spec in E as (r & Hr & Hrs).
destruct (FSP.upoison_ok_In B ly S Up r (FSP.ARU_ok segs B ly S Up W mem md H) Hr) as (A8 & L8 & M8 & _).
pose proof (FP r Hr) as D. unfold shadow_addr in Hrs.
clear - Hs Hrs A8 M8 P8 D P0 N0. Z.div_mod_to_equations. lia.
Qed.

(* Every address of the primary space is off Up (it lies in the owned extent (ly_prim, kPrimResvSize)). *)
Lemma space_off : forall segs B ly S Up W mem md a, FSP.ARU segs B ly S Up W mem md ->
ly_space ly <= a < ly_space ly + kSpaceSize -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md a H Ha.
pose proof (am_layout B ly S _ (FSP.ARU_ARm segs B ly S Up W mem md H)) as LO.
pose proof (lo_space_in ly LO) as [S1 S2].
apply (owned_ext_off_ush segs B ly S Up W mem md (ly_prim ly, kPrimResvSize) a H).
- unfold owned_extents. left. reflexivity.
- cbn [fst snd]. assert (E37 : kSpaceSize = 137438953472) by reflexivity.
  rewrite E37 in *. unfold kPrimResvSize in *. lia.
Qed.

(* A batch object of the class-kBatchClass region of the space, with at most kBatchSlots items. *)
Definition bgeo (b : batch) : Prop :=
region_off kBatchClass <= b_self b /\ b_self b + kBatchBytes <= region_off kBatchClass + kFreeArrayOffset /\
Z.of_nat (length (b_items b)) <= kBatchSlots.

Lemma bobj_off : forall segs B ly S Up W mem md b a, FSP.ARU segs B ly S Up W mem md -> bgeo b ->
ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md b a H (G1 & G2 & _) Ha. apply (space_off segs B ly S Up W mem md a H).
assert (R : region_off kBatchClass = 103079215104) by reflexivity.
assert (E37 : kSpaceSize = 137438953472) by reflexivity.
rewrite R in G1, G2. rewrite E37. unfold kFreeArrayOffset, kBatchBytes in *. lia.
Qed.

Lemma bcellw_off : forall segs B ly S Up W mem md l a, FSP.ARU segs B ly S Up W mem md ->
(forall b, In b l -> bgeo b) -> bcellw ly l a -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md l a H G (b & Hb & Ha).
pose proof (G b Hb) as GB. pose proof GB as (_ & _ & G3).
apply (bobj_off segs B ly S Up W mem md b a H GB). unfold kBatchBytes, kBatchSlots in *. lia.
Qed.

(* Where the cells of the quarantine lie. *)
Lemma batch_cells_at : forall B ly l c, In c (batch_cells l) ->
c_w c = 8%nat /\ exists b, In b l /\ ly_space ly + b_self b <= aeval B ly (c_at c) /\
aeval B ly (c_at c) + 8 <= ly_space ly + b_self b + 24 + 8 * Z.of_nat (length (b_items b)).
Proof.
intros B ly l. induction l as [|b t IH]; intros c Hc; [destruct Hc|].
cbn [batch_cells] in Hc.
destruct Hc as [<-|[<-|[<-|Hc]]].
- split; [reflexivity|]. exists b. split; [left; reflexivity|]. cbn [c8 c_at aeval batch_exp]. lia.
- split; [reflexivity|]. exists b. split; [left; reflexivity|]. cbn [z8 c8 c_at aeval aoff batch_exp]. lia.
- split; [reflexivity|]. exists b. split; [left; reflexivity|]. cbn [z8 c8 c_at aeval aoff batch_exp]. lia.
- apply in_app_iff in Hc as [Hc|Hc].
  + apply in_map_iff in Hc as ([i ch] & <- & Hiv). split; [reflexivity|]. exists b. split; [left; reflexivity|].
    apply in_combine_l in Hiv. apply in_seq in Hiv. cbn [c8 c_at aeval aoff batch_exp fst]. lia.
  + destruct (IH c Hc) as (W8 & b' & Hb' & H1 & H2). split; [exact W8|]. exists b'.
    split; [right; exact Hb'|]. lia.
Qed.

Lemma qc_cells_at : forall B ly root q c, (forall e', root <> ASh e') -> In c (qc_cells root q) ->
forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
(aeval B ly root <= aeval B ly (c_at c) + k < aeval B ly root + 32) \/ bcellw ly (qc_list q) (aeval B ly (c_at c) + k).
Proof.
intros B ly root q c NS Hc k Hk. unfold qc_cells in Hc.
destruct Hc as [<-|[<-|[<-|[<-|Hc]]]];
  [ cbn [z8 c8 c_w c_at] in Hk |- *; left; lia
  | cbn [z8 c8 c_w c_at] in Hk |- *; rewrite (aeval_aoff B ly root 8 NS); left; lia
  | cbn [z8 c8 c_w c_at] in Hk |- *; rewrite (aeval_aoff B ly root 16 NS); left; lia
  | cbn [z8 c8 c_w c_at] in Hk |- *; rewrite (aeval_aoff B ly root 24 NS); left; lia
  | ].
destruct (batch_cells_at B ly (qc_list q) c Hc) as (W8 & b & Hb & H1 & H2).
right. exists b. split; [exact Hb|]. rewrite W8 in Hk. lia.
Qed.

Lemma quar_cells_at : forall B ly S c, In c (quar_cells S) ->
forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
(as_inst B + o_q_cmutex <= aeval B ly (c_at c) + k < as_inst B + o_q_size + 32) \/
(ly_T ly + t_qc <= aeval B ly (c_at c) + k < ly_T ly + t_qc + 32) \/
bcellw ly (all_batches S) (aeval B ly (c_at c) + k).
Proof.
intros B ly S c Hc k Hk. unfold quar_cells in Hc.
destruct Hc as [<-|[<-|Hc]].
- left. cbn [z1 c1 c_w c_at aeval] in Hk |- *. unfold o_q_cmutex, o_q_size. lia.
- left. cbn [z1 c1 c_w c_at aeval] in Hk |- *. unfold o_q_rmutex, o_q_cmutex, o_q_size. lia.
- apply in_app_iff in Hc as [Hc|Hc].
  + destruct (qc_cells_at B ly (AT t_qc) (st_qthread S) c ltac:(intros e' E0; discriminate E0) Hc k Hk) as [A|A].
    * right; left. cbn [aeval] in A. exact A.
    * right; right. destruct A as (b & Hb & A). exists b. split; [|exact A].
      unfold all_batches. apply in_or_app. left. exact Hb.
  + destruct (qc_cells_at B ly (AInst o_q_size) (st_qglobal S) c ltac:(intros e' E0; discriminate E0) Hc k Hk)
      as [A|A].
    * left. cbn [aeval] in A. unfold o_q_cmutex, o_q_size in *. lia.
    * right; right. destruct A as (b & Hb & A). exists b. split; [|exact A].
      unfold all_batches. apply in_or_app. right. exact Hb.
Qed.

(* The batches of a drain cut are batch objects of the entry state's region (MergeBatches keeps a batch's self, the
   merged one within kBatchSlots items; pop_batches splits the list). *)
Lemma merge_bgeo : forall fuel l, (forall b, In b l -> bgeo b) ->
(forall b, In b (fst (merge_batches_cf fuel l)) -> bgeo b) /\ (forall b, In b (snd (merge_batches_cf fuel l)) -> bgeo b).
Proof.
induction fuel as [|f IH]; intros l G.
- cbn [merge_batches_cf fst snd]. split; [exact G | intros b []].
- destruct l as [|b1 [|b2 t]];
  [ cbn [merge_batches_cf fst snd]; split; [exact G | intros b []]
  | cbn [merge_batches_cf fst snd]; split; [exact G | intros b []]
  | cbn [merge_batches_cf] ].
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end.
  + apply Nat.leb_le in E.
    assert (GM : forall b, In b (mkBatch (b_self b1) (b_items b1 ++ b_items b2) :: t) -> bgeo b).
    { intros b [<-|Hb]; [|apply G; right; right; exact Hb].
      destruct (G b1 (or_introl eq_refl)) as (A1 & A2 & _). unfold bgeo. cbn [b_self b_items].
      rewrite length_app. unfold kBatchSlots in *. lia. }
    destruct (merge_batches_cf f (mkBatch (b_self b1) (b_items b1 ++ b_items b2) :: t)) as [rest ex] eqn:Em.
    pose proof (IH _ GM) as [R1 R2]. rewrite Em in R1, R2. cbn [fst snd] in R1, R2 |- *.
    split; [exact R1|]. intros b [<-|Hb]; [|exact (R2 b Hb)].
    destruct (G b2 (or_intror (or_introl eq_refl))) as (A1 & A2 & _). unfold bgeo. cbn [b_self b_items length].
    unfold kBatchSlots. lia.
  + assert (GT : forall b, In b (b2 :: t) -> bgeo b) by (intros b Hb; apply G; right; exact Hb).
    destruct (merge_batches_cf f (b2 :: t)) as [rest ex] eqn:Em.
    pose proof (IH _ GT) as [R1 R2]. rewrite Em in R1, R2. cbn [fst snd] in R1, R2 |- *.
    split; [|exact R2]. intros b [<-|Hb]; [apply G; left; reflexivity | exact (R1 b Hb)].
Qed.

Lemma pop_bgeo : forall fuel q acc, (forall b, In b (qc_list q) -> bgeo b) -> (forall b, In b acc -> bgeo b) ->
(forall b, In b (qc_list (fst (pop_batches fuel q acc))) -> bgeo b) /\
(forall b, In b (snd (pop_batches fuel q acc)) -> bgeo b).
Proof.
induction fuel as [|f IH]; intros [ql qb] acc G1 G2; cbn [qc_list qc_bytes] in G1.
- cbn [pop_batches fst snd qc_list]. split; [exact G1 | intros b Hb; apply G2; rewrite in_rev; exact Hb].
- cbn [pop_batches qc_list qc_bytes].
  destruct (qb <=? kQuarantineMin).
  + cbn [fst snd qc_list]. split; [exact G1 | intros b Hb; apply G2; rewrite in_rev; exact Hb].
  + destruct ql as [|b0 t].
    * cbn [fst snd qc_list]. split; [exact G1 | intros b Hb; apply G2; rewrite in_rev; exact Hb].
    * apply IH; cbn [qc_list]; [intros b Hb; apply G1; right; exact Hb|].
      intros b [<-|Hb]; [apply G1; left; reflexivity | apply G2; exact Hb].
Qed.

Lemma xfer_bgeo : forall X S', drain_xfer X S' -> (forall b, In b (all_batches X) -> bgeo b) ->
forall b, In b (all_batches S') -> bgeo b.
Proof.
intros X S' [_ ->] G b Hb. apply G. unfold all_batches in *.
cbn [set_qglobal set_qthread st_qthread st_qglobal qc_list qc0 YFeuC.transfer_g app] in Hb.
apply in_app_iff in Hb as [Hb|Hb]; apply in_or_app; [right|left]; exact Hb.
Qed.

Lemma recyc_bgeo : forall X S' P, drain_recyc X S' P -> (forall b, In b (all_batches X) -> bgeo b) ->
(forall b, In b (all_batches S') -> bgeo b) /\ (forall b, In b P -> bgeo b).
Proof.
intros X S' P (_ & gm & ex & g' & popped & EM & EP & ES & EPP) G.
assert (GT : forall b, In b (qc_list (YFeuC.transfer_g X)) -> bgeo b).
{ intros b Hb. apply G. unfold YFeuC.transfer_g in Hb. cbn [qc_list] in Hb. unfold all_batches.
  apply in_app_iff in Hb as [Hb|Hb]; apply in_or_app; [right|left]; exact Hb. }
assert (GM : (forall b, In b (qc_list gm) -> bgeo b) /\ (forall b, In b ex -> bgeo b)).
{ revert EM. unfold merge_split_cf.
  match goal with |- context [if ?c then _ else _] => destruct c end; intros EM.
  - destruct (merge_batches_cf (length (qc_list (YFeuC.transfer_g X))) (qc_list (YFeuC.transfer_g X)))
      as [l' ex'] eqn:Em.
    injection EM as <- <-. pose proof (merge_bgeo (length (qc_list (YFeuC.transfer_g X))) _ GT) as [R1 R2].
    rewrite Em in R1, R2.
    cbn [fst snd qc_list] in R1, R2 |- *. split; [exact R1 | exact R2].
  - injection EM as <- <-. split; [exact GT | intros b []]. }
destruct GM as [GM1 GM2].
pose proof (pop_bgeo (S (length (qc_list gm))) gm [] GM1 ltac:(intros b [])) as [P1 P2].
rewrite EP in P1, P2. cbn [fst snd] in P1, P2.
subst S' P. split.
- intros b Hb. unfold all_batches in Hb. cbn [set_qglobal set_qthread st_qthread st_qglobal qc_list qc0 app] in Hb.
  exact (P1 b Hb).
- intros b Hb. apply in_app_iff in Hb as [Hb|Hb]; [exact (GM2 b Hb) | exact (P2 b Hb)].
Qed.

(* The chunks of the final state of the arm whose last batch has room. *)
Lemma qfin_chunks : forall S k z tr, st_chunks (qfin_c S k z tr) = upd_chunk (st_chunks S) (qk k).
Proof. intros S k z tr. unfold qfin_c, qx, YFl0C.depot_after, dtick. destruct (z =? 0); reflexivity. Qed.

End aux.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The callee-contract premise and the two image premises.                                                       *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section defs. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* DGif0.v's di_enqueue field (DGif0.v:302-325), word for word, over its parameters: QuarantineCache::Enqueue's
   contract at Put's call.  A callee contract (kind 5): the ARU record takes it as a premise. *)
Definition di_enqueue_t (B : asyms) (U : list Z -> astate -> Prop)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (lpost : astate -> Prop)
(fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop)
(dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop)
(L24 : Z) (QB : astate -> Prop) : Prop :=
  forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) -> U tr S ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
    0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
    dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) mem ->
    YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
    getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
    getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
    getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
    amreal im_segs (enqueue (qk k) (qx S k z tr)) W
      (cfg_at im_segs dg_enqueue regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
      (fun r W' c' => exists regs' mem' md' nb,
        c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
        acall_post_x B ARX AOX inst YFewC.QSTACK ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (fun _ => False)
          ly (snd r) W' regs' mem' md' /\
        st_qthread (snd r) = qc_push (st_qthread (qx S k z tr)) (qk k) nb /\
        match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end /\
        st_chunks (snd r) = st_chunks (qx S k z tr) /\ st_qglobal (snd r) = st_qglobal (qx S k z tr) /\
        (forall a, AOX ly (snd r) a -> AOX ly (qx S k z tr) a) /\
        (* the thread cache's byte count, which Put reads after Enqueue returns *)
        val_mem im_segs (mrestrict (w_H W') mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread (snd r))) /\
        (qc_bytes (st_qthread (snd r)) <= kQuarantineCacheMax -> lpost (snd r)) /\
        (kQuarantineCacheMax < qc_bytes (st_qthread (snd r)) -> QB (snd r) /\ Z.of_nat (length (all_batches (snd r))) <= L24)).

(* The internal allocator's zone lies below the shadow (fs: AFgi.IZONE, AFgi.v:486 / YFgi.v:484: [TFIB_IAL_LO,
   TFIB_IAL_HI) \/ [TFIB_IAL_FLAG, +4), AF0m.v:18-19, all below 0x7fff8000). *)
Definition izone_low : Prop := forall a, dg_izone a -> 0 <= a < SHADOW_OFF.

(* "The internal allocator is initialized" reads only cells of its zone (fs: AFgi.IAL_POST, AFgi.v:562-566 / YFgi.v:560,
   reads TFIB_IAL_FLAG, +1, TFIB_IAL_W .. +16 and [TFIB_IAL_LO, TFIB_IAL_HI), all IZONE; AFgi.MEQI_frame's argument). *)
Definition ial_local : Prop :=
forall (W : world im_segs) (m1 m2 : word -> option byte),
(forall x : word, dg_izone (bv_unsigned x) -> m1 x = m2 x) -> dg_ial_post W m1 -> dg_ial_post W m2.

End defs.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The views and the memory posts, moved across the unpoisoning.                                                  *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section move. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.

Lemma qview_bgeo : forall B W ly inst X mem, qview B W ly inst X mem -> forall b, In b (all_batches X) -> bgeo b.
Proof.
intros B W ly inst X mem QV b Hb.
destruct QV as [_ _ _ _ _ _ _ _ [G0 G] _ (_ & _ & WF & _) _ _].
destruct (G b Hb) as (G1 & G2 & G3).
pose proof (proj1 (Forall_forall _ _) WF b Hb) as [L1 L2].
unfold bgeo. split; [lia|]. split; [lia|]. unfold kBatchSlots in *. lia.
Qed.

Lemma dview_n_U : forall B W ly S Up mem md inst, FSP.ARU im_segs B ly S Up W mem md ->
0 <= inst -> inst + 0xe60 <= SHADOW_OFF -> izone_low -> ial_local ->
dview_n B W ly inst (FSP.unpoison Up mem) -> dview_n B W ly inst mem.
Proof.
intros B W ly S Up mem md inst H I0 I1 IZL IAL [N1 N2 N3 N4 N5 N6 N7].
constructor; try assumption.
- apply Forall_forall. intros c Hc. apply (cell_holds_unpoison im_segs B ly (w_H W) Up mem c).
  + intros k Hk. exact (const_cell_off_ush im_segs B ly S Up W mem md c H Hc k Hk).
  + exact (proj1 (Forall_forall _ _) N4 c Hc).
- destruct N5 as [V1 V2]. split.
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + 0x318) 8 _
      ltac:(intros k Hk; apply (low_off_ush im_segs B ly S Up W mem md _ H); lia)) V1).
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + 0x328) 8 _
      ltac:(intros k Hk; apply (low_off_ush im_segs B ly S Up W mem md _ H); lia)) V2).
- apply (IAL W (FSP.unpoison Up mem) mem); [|exact N6].
  intros x Hx. apply FSP.unpoison_out. apply off_ush_w.
  exact (low_off_ush im_segs B ly S Up W mem md _ H (IZL _ Hx)).
- exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (ly_T ly + t_unwinding) 1 0
    ltac:(intros k Hk; apply (thread_off_ush im_segs B ly S Up W mem md _ H); unfold t_unwinding, kThreadObjSize; lia))
    N7).
Qed.

Lemma dbview_U : forall B W ly S Up mem md q lastb pa nn, FSP.ARU im_segs B ly S Up W mem md ->
dbview W ly (FSP.unpoison Up mem) q lastb pa nn -> dbview W ly mem q lastb pa nn.
Proof.
intros B W ly S Up mem md q lastb pa nn H [D1 D2 D3 D4 D5 D6 D7].
pose proof D4 as (R1 & R2 & _ & _).
assert (SP : forall a, DGgiC.Bv ly lastb <= a < DGgiC.Bv ly lastb + kBatchBytes -> off_ush Up a).
{ intros a Ha. apply (space_off im_segs B ly S Up W mem md a H). lia. }
assert (THR : forall a, ly_T ly + t_qc <= a < ly_T ly + t_qc + 32 -> off_ush Up a).
{ intros a Ha. apply (thread_off_ush im_segs B ly S Up W mem md a H). unfold t_qc, kThreadObjSize in *. lia. }
constructor; try assumption.
- destruct D1 as (V1 & V2 & V3 & V4). split; [|split; [|split]].
  + refine (proj1 (val_mem_unpoison im_segs (w_H W) Up mem _ _ _ _) V1). intros k Hk; apply THR; lia.
  + refine (proj1 (val_mem_unpoison im_segs (w_H W) Up mem _ _ _ _) V2). intros k Hk; apply THR; lia.
  + refine (proj1 (val_mem_unpoison im_segs (w_H W) Up mem _ _ _ _) V3). intros k Hk; apply THR; lia.
  + refine (proj1 (val_mem_unpoison im_segs (w_H W) Up mem _ _ _ _) V4). intros k Hk; apply THR; lia.
- destruct D2 as (V1 & V2). split.
  + refine (proj1 (val_mem_unpoison im_segs (w_H W) Up mem _ _ _ _) V1). intros k Hk; apply SP; unfold kBatchBytes; lia.
  + refine (proj1 (val_mem_unpoison im_segs (w_H W) Up mem _ _ _ _) V2). intros k Hk; apply SP; unfold kBatchBytes; lia.
- intros a Ha. apply (apresent_unpoison_bwd (w_H W) Up mem a); [|exact (D3 a Ha)].
  apply SP. destruct Ha as [Ha|(Hc & Ha)]; [unfold kBatchBytes; lia|].
  clear - Ha Hc. unfold DGgiC.SLOTv, DGgiC.BCv in *. unfold kBatchBytes, kBatchSlots in *. lia.
Qed.

Lemma dview_U : forall B W ly S Up mem md inst p n, FSP.ARU im_segs B ly S Up W mem md ->
0 <= inst -> inst + 0xe60 <= SHADOW_OFF -> izone_low -> ial_local ->
fpreU im_segs B Up ly S W mem p n -> In (p, n) (blocks S) ->
dview B W ly inst (FSP.unpoison Up mem) S p n -> dview B W ly inst mem S p n.
Proof.
intros B W ly S Up mem md inst p n H I0 I1 IZL IAL FP Hb [V1 V2 V3 V4 V5 V6 V7 V8 V9 V10].
destruct (blk_geo im_segs B ly S Up W mem md p n H Hb) as (P16 & P8 & N1 & P4 & PC & HDR).
constructor; try assumption.
- exact (dview_n_U B W ly S Up mem md inst H I0 I1 IZL IAL V1).
- destruct V4 as (hb1 & Hh1 & Hh2 & Hv1 & Hv2). exists hb1. split; [exact Hh1|]. split; [exact Hh2|]. split.
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (sptr_addr B ly p - 16) 4 _
      ltac:(intros k Hk; apply HDR; lia)) Hv1).
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (sptr_addr B ly p - 12) 4 _
      ltac:(intros k Hk; apply HDR; lia)) Hv2).
- intros a Ha. apply (apresent_unpoison_bwd (w_H W) Up mem a); [apply HDR; exact Ha | exact (V5 a Ha)].
- intros a Ha. apply (apresent_unpoison_bwd (w_H W) Up mem a); [|exact (V6 a Ha)].
  exact (dshadow_off im_segs B ly S Up W mem md (sptr_addr B ly p) (req_size n) a H P8 ltac:(lia) ltac:(lia) PC FP Ha).
- intros a Ha. apply (apresent_unpoison_bwd (w_H W) Up mem a); [|exact (V7 a Ha)].
  apply (thread_off_ush im_segs B ly S Up W mem md a H). unfold t_stats, kThreadObjSize in *. lia.
- intros lastb initr Hr. exact (dbview_U B W ly S Up mem md _ lastb _ _ H (V10 lastb initr Hr)).
Qed.

Lemma qview_U : forall B ly X Up W mem md inst, FSP.ARU im_segs B ly X Up W mem md ->
0 <= inst -> inst + 0xe60 <= SHADOW_OFF ->
qview B W ly inst X (FSP.unpoison Up mem) -> qview B W ly inst X mem.
Proof.
intros B ly X Up W mem md inst H I0 I1 QV.
pose proof (qview_bgeo _ _ _ _ _ _ QV) as BG.
destruct QV as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13].
assert (LOW : forall a, inst <= a < inst + 0xe60 -> off_ush Up a).
{ intros a Ha. apply (low_off_ush im_segs B ly X Up W mem md a H). lia. }
assert (THR : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a).
{ intros a Ha. exact (thread_off_ush im_segs B ly X Up W mem md a H Ha). }
constructor; try assumption.
- apply Forall_forall. intros c Hc. apply (cell_holds_unpoison im_segs B ly (w_H W) Up mem c);
  [|exact (proj1 (Forall_forall _ _) Q5 c Hc)].
  intros k Hk. destruct (quar_cells_at B ly X c Hc k Hk) as [A|[A|A]].
  + apply LOW. rewrite <- Q1 in A. unfold o_q_cmutex, o_q_size in A. lia.
  + apply THR. unfold t_qc, kThreadObjSize in *. lia.
  + exact (bcellw_off im_segs B ly X Up W mem md _ _ H BG A).
- destruct Q6 as (V1 & V2 & V3). split; [|split].
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + o_q_max) 8 _
      ltac:(intros k Hk; apply LOW; unfold o_q_max in *; lia)) V1).
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + o_q_min) 8 _
      ltac:(intros k Hk; apply LOW; unfold o_q_min in *; lia)) V2).
  + exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + o_q_cmutex + 2) 2 _
      ltac:(intros k Hk; apply LOW; unfold o_q_cmutex in *; lia)) V3).
- intros a Ha. apply (apresent_unpoison_bwd (w_H W) Up mem a); [|exact (Q7 a Ha)].
  apply THR. unfold t_qc, kThreadObjSize in *. lia.
- intros b a Hb Ha. apply (apresent_unpoison_bwd (w_H W) Up mem a); [|exact (Q8 b a Hb Ha)].
  exact (bobj_off im_segs B ly X Up W mem md b a H (BG b Hb) Ha).
Qed.

(* The memory at Deallocate's return (arm "last batch has room"), moved to the unpoisoned memories. *)
Lemma dmem_c_U : forall B ly S Up W mem0 md sp0 pa nn hb1 q lastb DP mem',
FSP.ARU im_segs B ly S Up W mem0 md ->
zones_free im_segs B dg_dzone (fun ly a => dg_czone ly a /\ ~ dg_izone a) -> izone_low -> ial_local ->
(forall a, pa - 16 <= a < pa + 8 -> off_ush Up a) ->
(forall a, dshadow pa nn a -> off_ush Up a) ->
(forall a, DGgiC.Bv ly lastb <= a < DGgiC.Bv ly lastb + kBatchBytes -> off_ush Up a) ->
DGgiC.BCv lastb < kBatchSlots ->
dmem_c W ly sp0 mem0 pa nn hb1 q lastb DP mem' ->
dmem_c W ly sp0 (FSP.unpoison Up mem0) pa nn hb1 q lastb DP (FSP.unpoison Up mem').
Proof.
intros B ly S Up W mem0 md sp0 pa nn hb1 q lastb DP mem' H ZON IZL IAL HDR SHD BAT BC
  (C1 & C2 & C3 & C4 & C5 & C6 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
pose proof (FSP.ARU_AR im_segs B ly S Up W mem0 md H) as HAR.
assert (OZ : forall a, dg_dzone ly a -> off_ush Up a).
{ intros a Ha. destruct (ZON ly S W _ md a HAR (or_introl Ha)) as [R F].
  exact (ush_free_off im_segs B ly S Up W mem0 md a H R F). }
assert (OI : forall a, dg_izone a -> off_ush Up a).
{ intros a Ha. exact (low_off_ush im_segs B ly S Up W mem0 md a H (IZL a Ha)). }
assert (OT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a).
{ intros a Ha. exact (thread_off_ush im_segs B ly S Up W mem0 md a H Ha). }
assert (VU : forall a w v, (forall k, 0 <= k < Z.of_nat w -> off_ush Up (a + k)) ->
  val_mem im_segs (mrestrict (w_H W) mem') a w v -> val_mem im_segs (mrestrict (w_H W) (FSP.unpoison Up mem')) a w v).
{ intros a w v HO HV. exact (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' a w v HO) HV). }
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
  (conj _ (conj _ (conj _ _))))))))))))))).
- destruct C1 as (memD & D1 & D2 & D3). exists memD. split; [exact D1|]. split.
  + intros a Ha HP. exact (D2 a Ha (apresent_unpoison_bwd (w_H W) Up mem0 a (OZ a Ha) HP)).
  + intros x Hx. rewrite (FSP.unpoison_out Up mem' x (off_ush_w Up x (OZ _ Hx))). exact (D3 x Hx).
- intros x H1 H2 H3 H4. apply unpoison_eq. exact (C2 x H1 H2 H3 H4).
- apply (IAL W mem' (FSP.unpoison Up mem')); [|exact C3].
  intros x Hx. symmetry. apply FSP.unpoison_out. exact (off_ush_w Up x (OI _ Hx)).
- intros x Hx. rewrite (FSP.unpoison_out Up mem' x (off_ush_w Up x (SHD _ Hx))). exact (C4 x Hx).
- intros a Ha. exact (apresent_unpoison_fwd (w_H W) Up mem' a (C5 a Ha)).
- intros a Ha. exact (apresent_unpoison_fwd (w_H W) Up mem' a (C6 a Ha)).
- apply VU; [intros k Hk; apply HDR; lia | exact V1].
- apply VU; [intros k Hk; apply HDR; lia | exact V2].
- apply VU; [intros k Hk; apply OT; unfold t_qc, kThreadObjSize; lia | exact V3].
- apply VU; [intros k Hk; apply OT; unfold t_qc, kThreadObjSize; lia | exact V4].
- apply VU; [intros k Hk; apply OT; unfold t_qc, kThreadObjSize; lia | exact V5].
- apply VU; [intros k Hk; apply OT; unfold t_qc, kThreadObjSize; lia | exact V6].
- apply VU; [intros k Hk; apply OT; unfold t_unwinding, kThreadObjSize; lia | exact V7].
- apply VU; [intros k Hk; apply BAT; unfold kBatchBytes; lia | exact V8].
- apply VU; [intros k Hk; apply BAT; unfold kBatchBytes; lia | exact V9].
- apply VU; [|exact V10]. intros k Hk. apply BAT. clear - Hk BC.
  unfold DGgiC.SLOTv, DGgiC.BCv in *. unfold kBatchBytes, kBatchSlots in *. lia.
Qed.

(* The memory at Deallocate's early return (the NULL arm), moved to the unpoisoned memories. *)
Lemma dmem_n_U : forall B ly S Up W mem0 md sp0 mem', FSP.ARU im_segs B ly S Up W mem0 md -> izone_low -> ial_local ->
dmem_n W ly sp0 mem0 mem' -> dmem_n W ly sp0 (FSP.unpoison Up mem0) (FSP.unpoison Up mem').
Proof.
intros B ly S Up W mem0 md sp0 mem' H IZL IAL (C1 & C2 & C3 & C4).
split; [|split; [|split]].
- intros x H1 H2 H3. apply unpoison_eq. exact (C1 x H1 H2 H3).
- apply (IAL W mem' (FSP.unpoison Up mem')); [|exact C2].
  intros x Hx. symmetry. apply FSP.unpoison_out. apply off_ush_w.
  exact (low_off_ush im_segs B ly S Up W mem0 md _ H (IZL _ Hx)).
- exact (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' (ly_T ly + t_unwinding) 1 0
    ltac:(intros k Hk; apply (thread_off_ush im_segs B ly S Up W mem0 md _ H); unfold t_unwinding, kThreadObjSize; lia))
    C3).
- intros a Ha. exact (apresent_unpoison_fwd (w_H W) Up mem' a (C4 a Ha)).
Qed.

(* The memory at a drain cut, moved to the unpoisoned memories. *)
Lemma dmem_q_U : forall B W inst ly sp0 X S' P Up mem mem',
(forall c, In c (quar_cells S') -> forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> off_ush Up (aeval B ly (c_at c) + k)) ->
(forall k, 0 <= k < Z.of_nat 2 -> off_ush Up (inst + o_q_cmutex + 2 + k)) ->
dmem_q B W inst ly sp0 X S' P mem mem' ->
dmem_q B W inst ly sp0 X S' P (FSP.unpoison Up mem) (FSP.unpoison Up mem').
Proof.
intros B W inst ly sp0 X S' P Up mem mem' OFFC OFFM (Q1 & Q2 & Q3 & Q4).
split; [|split; [|split]].
- intros x Hx. apply unpoison_eq. exact (Q1 x Hx).
- apply Forall_forall. intros c Hc. apply (cell_holds_unpoison_r im_segs B ly (w_H W) Up mem' c (OFFC c Hc)).
  exact (proj1 (Forall_forall _ _) Q2 c Hc).
- intros a Ha. apply apresent_unpoison_mono. exact (Q3 a Ha).
- exact (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' _ 2 0 OFFM) Q4).
Qed.

End move.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The record.                                                                                                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

Theorem diface_U : forall B U ft rpre lpost dpost dbody L24 QB DRq I Up,
inst_low dg_inst_ok ->
zones_free im_segs B dg_dzone (fun ly a => dg_czone ly a /\ ~ dg_izone a) ->
izone_low -> ial_local ->
DIface B U ft (ARX_AR im_segs B I) (ARX_AR im_segs B I) (aowned B) rpre lpost (fun _ _ _ _ _ _ => True) dpost dbody L24 QB DRq ->
di_enqueue_t B U (ARX_ARU im_segs B I Up) (aowned B) rpre lpost (fpreU im_segs B Up) dpost L24 QB ->
drain_spec_cf B (ARX_ARU im_segs B I Up) (aowned B) dbody L24 QB ->
di_rchunk_t B (ARX_ARU im_segs B I Up) (aowned B) DRq ->
di_cdealloc_t B (ARX_ARU im_segs B I Up) (aowned B) DRq ->
DIface B U ft (ARX_ARU im_segs B I Up) (ARX_ARU im_segs B I Up) (aowned B) rpre lpost (fpreU im_segs B Up) dpost dbody L24 QB DRq.
Proof.
intros B U ft rpre lpost dpost dbody L24 QB DRq Iv Up ILOW ZON IZL IAL
  [A_inst A_view_n A_view A_shape_n A_shape A_depot A_dpost_aok A_enqueue A_drain A_lpost_d
   A_qview A_qowned A_requar_x A_requar_r A_requar_e A_rchunk A_cdealloc A_frame_r A_rview
   A_post_c A_post_n A_frame A_stack A_owned A_owned_b A_owned_i A_owned_x]
  HENQ HDRN HRC HCD.
assert (TOAR : forall inst ly S W mem md, ARX_ARU im_segs B Iv Up inst ly S W mem md ->
  ARX_AR im_segs B Iv inst ly S W (FSP.unpoison Up mem) md) by exact (ARX_ARU_AR im_segs B Iv Up).
(* the frame law, for ARX and for ARXr (the same relation on the ARU side) *)
assert (FR : di_frame_t (ARX_ARU im_segs B Iv Up) (aowned B)).
{ intros inst ly S W mem md mem' md' [E H] HO HV E1 E2 E3 HB. split; [exact E|].
  exact (FSP.ARU_frame im_segs B (AR_laws_ok im_segs B) ly S Up W mem md mem' md' H HO HV E1 E2 E3 HB). }
constructor.
- (* di_inst *)
  intros inst ly S W mem md HX. exact (A_inst inst ly S W _ md (TOAR _ _ _ _ _ _ HX)).
- (* di_view_n *)
  intros inst ly S W mem md n HX Hr. pose proof HX as [E HARU].
  pose proof (A_inst _ _ _ _ _ _ (TOAR _ _ _ _ _ _ HX)) as IOK. destruct (ILOW _ IOK) as [I0 I1].
  exact (dview_n_U B W ly S Up mem md inst HARU I0 I1 IZL IAL (A_view_n _ _ _ _ _ _ n (TOAR _ _ _ _ _ _ HX) Hr)).
- (* di_view *)
  intros inst ly S W mem md p n HX Hr Hf Hb. pose proof HX as [E HARU].
  pose proof (A_inst _ _ _ _ _ _ (TOAR _ _ _ _ _ _ HX)) as IOK. destruct (ILOW _ IOK) as [I0 I1].
  exact (dview_U B W ly S Up mem md inst p n HARU I0 I1 IZL IAL Hf Hb
    (A_view _ _ _ _ _ _ p n (TOAR _ _ _ _ _ _ HX) Hr I Hb)).
- (* di_shape_n *)
  exact A_shape_n.
- (* di_shape *)
  exact A_shape.
- (* di_depot *)
  intros inst ly S W mem0 md0 tr regs mem md buf HX Htr HZ. intros.
  pose proof HX as [E HARU]. pose proof (FSP.ARU_AR im_segs B ly S Up W mem0 md0 HARU) as HAR.
  apply (A_depot inst ly S W (FSP.unpoison Up mem0) md0 tr regs mem md buf (TOAR _ _ _ _ _ _ HX) Htr);
    try assumption.
  intros x Hx. destruct (ZON ly S W (FSP.unpoison Up mem0) md0 (bv_unsigned x) HAR Hx) as [HR HF].
  rewrite (FSP.unpoison_out Up mem0 x
    (off_ush_w Up x (ush_free_off im_segs B ly S Up W mem0 md0 (bv_unsigned x) HARU HR HF))).
  exact (HZ x Hx).
- (* di_dpost_aok *)
  exact A_dpost_aok.
- (* di_enqueue: a callee contract, the premise *)
  exact HENQ.
- (* di_drain: a callee contract, the premise *)
  exact HDRN.
- (* di_lpost_d *)
  intros inst ly S W mem md p n tr k z nb X' W' mem' md' trc r HX Hr Hb Htr Hf Hk Hq Hnb Hc Hg HX'.
  exact (A_lpost_d inst ly S W _ md p n tr k z nb X' W' _ md' trc r (TOAR _ _ _ _ _ _ HX) Hr Hb Htr Hf Hk Hq Hnb Hc Hg
    (TOAR _ _ _ _ _ _ HX')).
- (* di_qview *)
  intros inst ly X W mem md HX Hd. pose proof HX as [E HARU].
  pose proof (A_inst _ _ _ _ _ _ (TOAR _ _ _ _ _ _ HX)) as IOK. destruct (ILOW _ IOK) as [I0 I1].
  exact (qview_U B ly X Up W mem md inst HARU I0 I1 (A_qview _ _ _ _ _ _ (TOAR _ _ _ _ _ _ HX) Hd)).
- (* di_qowned *)
  intros inst ly X W mem md a HX. exact (A_qowned inst ly X W _ md a (TOAR _ _ _ _ _ _ HX)).
- (* di_requar_x *)
  intros inst ly X W mem md sp0 S' mem' md' HX Hd Hx Hsp1 Hsp2 HQ E1 E2 E3.
  pose proof HX as [E HARU]. pose proof (TOAR _ _ _ _ _ _ HX) as HXA.
  pose proof (A_inst _ _ _ _ _ _ HXA) as IOK. destruct (ILOW _ IOK) as [I0 I1].
  pose proof (A_qview _ _ _ _ _ _ HXA Hd) as QV.
  pose proof (qview_bgeo _ _ _ _ _ _ QV) as BGX.
  assert (EI : inst = as_inst B) by (destruct QV as [Q1 _ _ _ _ _ _ _ _ _ _ _ _]; exact Q1).
  pose proof (xfer_bgeo X S' Hx BGX) as BGS.
  assert (OFFW : forall a, dwin_q inst ly sp0 X S' [] a -> off_ush Up a).
  { intros a [Ha|[Ha|Ha]].
    - apply (stack_off_ush im_segs B ly X Up W mem md a HARU). unfold YFeuC.DSTACK in *. lia.
    - destruct Ha as [Ha|[Ha|Ha]].
      + apply (low_off_ush im_segs B ly X Up W mem md a HARU). unfold o_quar in *. lia.
      + apply (low_off_ush im_segs B ly X Up W mem md a HARU). unfold o_quar in *. lia.
      + apply (thread_off_ush im_segs B ly X Up W mem md a HARU). unfold t_qc, kThreadObjSize in *. lia.
    - apply (bcellw_off im_segs B ly X Up W mem md (all_batches X ++ all_batches S' ++ []) a HARU); [|exact Ha].
      intros b Hb. apply in_app_iff in Hb as [Hb|Hb]; [exact (BGX b Hb)|].
      apply in_app_iff in Hb as [Hb|[]]. exact (BGS b Hb). }
  assert (OFFC : forall c, In c (quar_cells S') -> forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
    off_ush Up (aeval B ly (c_at c) + k)).
  { intros c Hc k Hk. destruct (quar_cells_at B ly S' c Hc k Hk) as [A|[A|A]].
    - apply (low_off_ush im_segs B ly X Up W mem md _ HARU). rewrite <- EI in A. unfold o_q_cmutex, o_q_size in A. lia.
    - apply (thread_off_ush im_segs B ly X Up W mem md _ HARU). unfold t_qc, kThreadObjSize in *. lia.
    - exact (bcellw_off im_segs B ly X Up W mem md _ _ HARU BGS A). }
  assert (OFFM : forall k, 0 <= k < Z.of_nat 2 -> off_ush Up (inst + o_q_cmutex + 2 + k)).
  { intros k Hk. apply (low_off_ush im_segs B ly X Up W mem md _ HARU). unfold o_q_cmutex in *. lia. }
  destruct (A_requar_x inst ly X W (FSP.unpoison Up mem) md sp0 S' (FSP.unpoison Up mem') md' HXA Hd Hx Hsp1 Hsp2
     (dmem_q_U B W inst ly sp0 X S' [] Up mem mem' OFFC OFFM HQ) E1 E2 E3) as [[E' HAR'] HAOX].
  split; [|exact HAOX]. split; [exact E'|].
  apply (ARU_rebuild_raw im_segs B ly X Up W mem md ly S' mem' md' HARU HAR').
  + intros r p n Hr Hb _ _. destruct Hx as [_ ->]. exact Hb.
  + intros s Hs. destruct HQ as [FRM _]. apply FRM. rewrite (in_ush_w64 im_segs B ly X Up W mem md s HARU Hs).
    intros HW. exact (ush_not_off im_segs B ly X Up W mem md s HARU Hs (OFFW s HW)).
- (* di_requar_r *)
  intros inst ly X W mem md sp0 tmp S' P mem' md' HX Hd Hr Hsp1 Hsp2 Ht1 Ht2 HQ HPL E1 E2 E3.
  pose proof HX as [E HARU]. pose proof (TOAR _ _ _ _ _ _ HX) as HXA.
  pose proof (A_inst _ _ _ _ _ _ HXA) as IOK. destruct (ILOW _ IOK) as [I0 I1].
  pose proof (A_qview _ _ _ _ _ _ HXA Hd) as QV.
  pose proof (qview_bgeo _ _ _ _ _ _ QV) as BGX.
  assert (EI : inst = as_inst B) by (destruct QV as [Q1 _ _ _ _ _ _ _ _ _ _ _ _]; exact Q1).
  destruct (recyc_bgeo X S' P Hr BGX) as [BGS BGP].
  assert (OFFW : forall a, dwin_q inst ly sp0 X S' P a -> off_ush Up a).
  { intros a [Ha|[Ha|Ha]].
    - apply (stack_off_ush im_segs B ly X Up W mem md a HARU). unfold YFeuC.DSTACK in *. lia.
    - destruct Ha as [Ha|[Ha|Ha]].
      + apply (low_off_ush im_segs B ly X Up W mem md a HARU). unfold o_quar in *. lia.
      + apply (low_off_ush im_segs B ly X Up W mem md a HARU). unfold o_quar in *. lia.
      + apply (thread_off_ush im_segs B ly X Up W mem md a HARU). unfold t_qc, kThreadObjSize in *. lia.
    - apply (bcellw_off im_segs B ly X Up W mem md (all_batches X ++ all_batches S' ++ P) a HARU); [|exact Ha].
      intros b Hb. apply in_app_iff in Hb as [Hb|Hb]; [exact (BGX b Hb)|].
      apply in_app_iff in Hb as [Hb|Hb]; [exact (BGS b Hb) | exact (BGP b Hb)]. }
  assert (OFFC : forall c, In c (quar_cells S') -> forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
    off_ush Up (aeval B ly (c_at c) + k)).
  { intros c Hc k Hk. destruct (quar_cells_at B ly S' c Hc k Hk) as [A|[A|A]].
    - apply (low_off_ush im_segs B ly X Up W mem md _ HARU). rewrite <- EI in A. unfold o_q_cmutex, o_q_size in A. lia.
    - apply (thread_off_ush im_segs B ly X Up W mem md _ HARU). unfold t_qc, kThreadObjSize in *. lia.
    - exact (bcellw_off im_segs B ly X Up W mem md _ _ HARU BGS A). }
  assert (OFFM : forall k, 0 <= k < Z.of_nat 2 -> off_ush Up (inst + o_q_cmutex + 2 + k)).
  { intros k Hk. apply (low_off_ush im_segs B ly X Up W mem md _ HARU). unfold o_q_cmutex in *. lia. }
  assert (HPL' : Forall (cell_holds B ly (aview im_segs (w_H W) (FSP.unpoison Up mem'))) (YFeuC.plist_cells tmp P)).
  { apply Forall_forall. intros c Hc. apply (cell_holds_unpoison_r im_segs B ly (w_H W) Up mem' c);
      [|exact (proj1 (Forall_forall _ _) HPL c Hc)].
    intros k Hk. unfold YFeuC.plist_cells in Hc.
    destruct (qc_cells_at B ly (ANum tmp) (mkQC P (sum_bytes P)) c ltac:(intros e' E0; discriminate E0) Hc k Hk)
      as [A|A].
    - cbn [aeval] in A. apply (stack_off_ush im_segs B ly X Up W mem md _ HARU). unfold YFeuC.DSTACK in *. lia.
    - exact (bcellw_off im_segs B ly X Up W mem md _ _ HARU BGP A). }
  destruct (A_requar_r inst ly X W (FSP.unpoison Up mem) md sp0 tmp S' P (FSP.unpoison Up mem') md' HXA Hd Hr
     Hsp1 Hsp2 Ht1 Ht2 (dmem_q_U B W inst ly sp0 X S' P Up mem mem' OFFC OFFM HQ) HPL' E1 E2 E3)
    as ([E' HAR'] & HDR & HAOX).
  split; [|split; [exact HDR | exact HAOX]]. split; [exact E'|].
  apply (ARU_rebuild_raw im_segs B ly X Up W mem md ly S' mem' md' HARU HAR').
  + intros r p n Hr0 Hb _ _. destruct Hr as (_ & gm & ex & g' & popped & _ & _ & -> & _). exact Hb.
  + intros s Hs. destruct HQ as [FRM _]. apply FRM. rewrite (in_ush_w64 im_segs B ly X Up W mem md s HARU Hs).
    intros HW. exact (ush_not_off im_segs B ly X Up W mem md s HARU Hs (OFFW s HW)).
- (* di_requar_e: ARXr is ARX on the ARU side *)
  intros inst ly S W mem md HX _. exact HX.
- (* di_rchunk: a callee contract, the premise *)
  exact HRC.
- (* di_cdealloc: a callee contract, the premise *)
  exact HCD.
- (* di_frame_r *)
  exact FR.
- (* di_rview *)
  intros inst ly X W mem md its zs HX Hq. pose proof HX as [E HARU].
  pose proof (A_inst _ _ _ _ _ _ (TOAR _ _ _ _ _ _ HX)) as IOK. destruct (ILOW _ IOK) as [I0 I1].
  destruct (A_rview _ _ _ _ _ _ its zs (TOAR _ _ _ _ _ _ HX) Hq) as [V R]. split; [|exact R].
  exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem (inst + o_space) 8 _
    ltac:(intros k Hk; apply (low_off_ush im_segs B ly X Up W mem md _ HARU); unfold o_space in *; lia)) V).
- (* di_post_c *)
  intros inst ly S W mem0 md0 p n tr k lastb initr hb1 z sp0 mem' mat HX Hr Hf Hb Htr Hk Hst Hrev Hlen Hqb
    Hsp1 Hsp2 Hsp3 Hsp4 Hhb Hhv HM Hpath.
  pose proof HX as [E HARU]. pose proof (TOAR _ _ _ _ _ _ HX) as HXA.
  pose proof (FSP.ARU_ARm im_segs B ly S Up W mem0 md0 HARU) as M.
  destruct (blk_geo im_segs B ly S Up W mem0 md0 p n HARU Hb) as (P16 & P8 & N1 & P4 & PC & HDR).
  pose proof (A_view _ _ _ _ _ _ p n HXA Hr I Hb) as DV.
  destruct DV as [_ _ DVc _ _ _ _ _ _ DVb].
  destruct (DVb lastb initr Hrev) as [_ _ _ DBr _ _ _]. destruct DBr as (R1 & R2 & _ & _).
  destruct DVc as (k' & Hk' & _ & _ & Hn'). rewrite Hk in Hk'. injection Hk' as Ek'. subst k'.
  assert (BAT : forall a, DGgiC.Bv ly lastb <= a < DGgiC.Bv ly lastb + kBatchBytes -> off_ush Up a).
  { intros a Ha. apply (space_off im_segs B ly S Up W mem0 md0 a HARU). lia. }
  assert (SHD : forall a, dshadow (sptr_addr B ly p) (req_size n) a -> off_ush Up a).
  { intros a Ha. exact (dshadow_off im_segs B ly S Up W mem0 md0 (sptr_addr B ly p) (req_size n) a HARU P8
      ltac:(lia) ltac:(lia) PC Hf Ha). }
  assert (HM' : dmem_c W ly sp0 (FSP.unpoison Up mem0) (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) lastb
    (dpost inst ly S W tr z) (FSP.unpoison Up mem')).
  { apply (dmem_c_U B ly S Up W mem0 md0 sp0 _ _ hb1 _ lastb _ mem' HARU ZON IZL IAL HDR SHD BAT); [|exact HM].
    unfold DGgiC.BCv. exact Hlen. }
  assert (Hhv' : val_mem im_segs (mrestrict (w_H W) (FSP.unpoison Up mem0)) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1)).
  { refine (proj2 (val_mem_unpoison im_segs (w_H W) Up mem0 _ _ _ _) Hhv). intros j Hj; apply HDR; lia. }
  destruct (A_post_c inst ly S W (FSP.unpoison Up mem0) md0 p n tr k lastb initr hb1 z sp0 (FSP.unpoison Up mem') mat
     HXA Hr I Hb Htr Hk Hst Hrev Hlen Hqb Hsp1 Hsp2 Hsp3 Hsp4 Hhb Hhv' HM' Hpath) as [[E' HAR'] Hlp].
  split; [|exact Hlp]. split; [exact E'|].
  apply (ARU_rebuild_raw im_segs B ly S Up W mem0 md0 ly (qfin_c S k z tr) mem' _ HARU HAR').
  + (* every block that holds a range of Up survives: the freed block holds none (fpreU) *)
    intros r p' n' Hr' Hb' Hp1 Hp2.
    unfold ablocks in Hb' |- *. apply in_map_iff in Hb' as ([q m] & Eq & Hq). cbn [fst snd] in Eq.
    injection Eq as Eq1 Eq2. subst p' n'.
    destruct (blocks_chunk S q m Hq) as (k0 & Hk0 & Hu0 & Hm0 & Hs0).
    apply in_map_iff. exists (q, m). split; [reflexivity|].
    unfold blocks. apply in_map_iff. exists k0. split; [rewrite Hu0, Hm0; reflexivity|].
    apply filter_In. split; [| unfold is_alloc; rewrite Hs0; reflexivity].
    rewrite qfin_chunks.
    destruct (sptr_eqb (ck_beg k0) (ck_beg k)) eqn:Eb.
    * apply sptr_eqb_spec in Eb. exfalso.
      destruct (find_user_spec _ _ _ Hk) as [Hkin Hku].
      pose proof (nodup_beg_inj (st_chunks S) k0 k (wf_chunks_nodup _ _ _ _ _ (am_wf _ _ _ _ M)) Hk0 Hkin Eb) as Ek.
      subst k0. rewrite Hku in Hu0. subst q. rewrite Hn' in Hm0. subst m.
      destruct (FSP.upoison_ok_In B ly S Up r (FSP.ARU_ok im_segs B ly S Up W mem0 md0 HARU) Hr') as (_ & L8 & _).
      pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)) as RD.
      destruct (Hf r Hr') as [D|D]; lia.
    * apply upd_chunk_keeps; [exact Hk0|]. intros Eb'. cbn [qk ck_beg] in Eb'.
      rewrite Eb', sptr_eqb_refl in Eb. discriminate Eb.
  + (* Up's bytes are outside every window of the post *)
    intros s Hs. destruct HM as (_ & FRM & _).
    pose proof (ush_band im_segs B ly S Up W mem0 md0 s HARU Hs) as (SB1 & SB2 & SB3).
    assert (NO : forall a, off_ush Up a -> a <> s).
    { intros a Ha ->. exact (ush_not_off im_segs B ly S Up W mem0 md0 s HARU Hs Ha). }
    apply FRM; rewrite (in_ush_w64 im_segs B ly S Up W mem0 md0 s HARU Hs); intros HW.
    * destruct HW as [HW|[HW|HW]].
      -- apply (NO s); [|reflexivity]. apply (stack_off_ush im_segs B ly S Up W mem0 md0 s HARU).
         unfold DGbaseC.DFSTACK in *. lia.
      -- apply (NO s); [|reflexivity]. apply (thread_off_ush im_segs B ly S Up W mem0 md0 s HARU).
         unfold DGgiC.WINT, t_qc, t_unwinding, t_stats, kThreadObjSize in *. lia.
      -- apply (NO s); [|reflexivity]. unfold DGgiC.WINB in HW.
         destruct HW as [HW|[HW|[HW|HW]]]; [apply HDR; lia | apply HDR; lia | apply BAT; unfold kBatchBytes; lia |].
         apply BAT. unfold DGgiC.SLOTv, DGgiC.BCv, kBatchBytes, kBatchSlots in *. lia.
    * apply (NO s); [|reflexivity].
      destruct (ZON ly S W _ md0 s (FSP.ARU_AR im_segs B ly S Up W mem0 md0 HARU) (or_introl HW)) as [HR HF].
      exact (ush_free_off im_segs B ly S Up W mem0 md0 s HARU HR HF).
    * pose proof (IZL s HW). lia.
    * exact (NO s (SHD s HW) eq_refl).
- (* di_post_n *)
  intros inst ly S W mem0 md0 n tr sp0 mem' mat HX Hr Hf Htr Hsp1 Hsp2 Hsp3 Hsp4 HM Hpath.
  pose proof HX as [E HARU].
  destruct (A_post_n inst ly S W (FSP.unpoison Up mem0) md0 n tr sp0 (FSP.unpoison Up mem') mat
     (TOAR _ _ _ _ _ _ HX) Hr I Htr Hsp1 Hsp2 Hsp3 Hsp4 (dmem_n_U B ly S Up W mem0 md0 sp0 mem' HARU IZL IAL HM) Hpath)
    as [[E' HAR'] Hlp].
  split; [|exact Hlp]. split; [exact E'|].
  apply (ARU_rebuild_raw im_segs B ly S Up W mem0 md0 ly (dtick S) mem' _ HARU HAR').
  + intros r p n' _ Hb _ _. exact Hb.
  + intros s Hs. destruct HM as (FRM & _).
    pose proof (ush_band im_segs B ly S Up W mem0 md0 s HARU Hs) as (SB1 & SB2 & SB3).
    assert (NO : forall a, off_ush Up a -> a <> s).
    { intros a Ha ->. exact (ush_not_off im_segs B ly S Up W mem0 md0 s HARU Hs Ha). }
    apply FRM; rewrite (in_ush_w64 im_segs B ly S Up W mem0 md0 s HARU Hs); intros HW.
    * apply (NO s); [|reflexivity]. apply (stack_off_ush im_segs B ly S Up W mem0 md0 s HARU).
      unfold DGbaseC.DFSTACK in *. lia.
    * apply (NO s); [|reflexivity]. apply (thread_off_ush im_segs B ly S Up W mem0 md0 s HARU).
      unfold t_unwinding, kThreadObjSize in *. lia.
    * pose proof (IZL s HW). lia.
- (* di_frame *)
  exact FR.
- (* di_stack *)
  intros inst ly S W mem md a HX. exact (A_stack inst ly S W _ md a (TOAR _ _ _ _ _ _ HX)).
- (* di_owned *)
  intros inst ly S W mem md p n k a HX. exact (A_owned inst ly S W _ md p n k a (TOAR _ _ _ _ _ _ HX)).
- (* di_owned_b *)
  intros inst ly S W mem md lastb initr a HX. exact (A_owned_b inst ly S W _ md lastb initr a (TOAR _ _ _ _ _ _ HX)).
- (* di_owned_i *)
  intros inst ly S W mem md a HX. exact (A_owned_i inst ly S W _ md a (TOAR _ _ _ _ _ _ HX)).
- (* di_owned_x *)
  intros inst ly S W mem md p n k z tr a HX. exact (A_owned_x inst ly S W _ md p n k z tr a (TOAR _ _ _ _ _ _ HX)).
Qed.

End main.

(* DIfaceR (lib/Reusable/DIfaceR.v) has no generic AR -> ARU transfer: each of its four fields (dr_enqueue,
   dr_drain, dr_rchunk, dr_cdealloc: Enqueue, Drain, Recycle and CacheDealloc with the raw frame) is a callee contract
   (kind 5 of the lane's method: the callee runs on the poisoned memory, so its ARU form cannot be read off the AR
   form).  An ARU DIfaceR is exactly the record of the ARU callee specs, which fs builds from its ARU twins of the
   released callee specs (FSupoisonAllocFeq / FSupoisonAllocFdn / FSupoisonAllocFrs / FSupoisonAllocFcd;
   a Theorem Labs lane decision, 12:13Z).  This file states nothing for it. *)

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainV1.v (commit 67deba317dfb, blob 16d462a7612e) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 4 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMdrainK DMdrainQ DMdrainG1 DMdrainG3 DMdrainG4 DMdrainT1 DMdrainTA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMsegDA DMdeq DMseg_rj DMseg_rjL DMdrainL DMmergeL DMdrainU2 DMdrainU9.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMdrainM DMdrainB DMdrainS DMdrainT3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition MWIN (ly : alayout) (regs0 : bvmap 5 word) (X : astate) (gm : qcache) (ex : list batch) (a : Z) : Prop :=
AFgj.WIN ly regs0 (st_qglobal X) a \/
(bv_unsigned (getr regs0 2) - 96 <= a < bv_unsigned (getr regs0 2) - 80) \/
(exists b, In b (qc_list (AFeu.transfer_g X) ++ qc_list gm ++ ex) /\ bcells_of ly b a).

Definition deq_pre_merge_t : Prop :=
forall (W : world tfibsegs) (ly : alayout) (regs1 : bvmap 5 word) (mem0 mem1 : word -> option byte)
  (L0 : list batch) (iw : chunk -> Z),
let Lk := fst (MB L0) in let ex := snd (MB L0) in
let sp1 := bv_unsigned (getr regs1 2) in
let m0 := mrestrict (w_H W) mem0 in let m1 := mrestrict (w_H W) mem1 in

layout_ok ly ->
(forall b, In b L0 ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\ addrb ly b mod 8192 = 0) ->
(forall k, In k (flat_map b_items L0) -> 0 <= ck_n k) ->
List.NoDup (map b_self L0) ->
sum_bytes L0 <= 2 ^ 31 ->

ly_stk_lo ly + DRSTACK <= sp1 /\ sp1 + LFRAME <= ly_stk_hi ly ->
sp1 mod 16 = 0 ->
(forall a, sp1 - DRSTACK <= a < sp1 + LFRAME -> apresent (w_H W) mem1 a) ->
getr regs1 4 = w64 TFIB_TP ->
YK0s.ret_ok (getr regs1 1) ->

getr regs1 10 = w64 A_QUAR -> getr regs1 11 = w64 kQuarantineMin ->
getr regs1 14 = w64 (zl ex) -> getr regs1 15 = w64 (la ly ex) ->
getr regs1 16 = w64 (zl Lk) -> getr regs1 5 = w64 (fa ly Lk 0) ->
val_mem tfibsegs m1 (A_QUAR + 152) 1 1 -> val_mem tfibsegs m1 (A_QUAR + 153) 1 1 ->
(forall a, A_QUAR + 154 <= a < A_QUAR + 156 -> mbyte tfibsegs m1 a = Some (Z_to_bv 8 0)) ->
(forall x : word, ~ DMdrainL.QW (bv_unsigned x) -> mem1 x = mem0 x) ->

val_mem tfibsegs m0 (A_QUAR + 160) 8 (zl Lk) -> val_mem tfibsegs m0 (A_QUAR + 168) 8 (fa ly Lk 0) ->
val_mem tfibsegs m0 (A_QUAR + 176) 8 (la ly Lk) ->
val_mem tfibsegs m0 (A_QUAR + 184) 8 (sum_bytes L0 - kBatchBytes * zl ex) ->
val_mem tfibsegs m0 (sp1 + 8) 8 (fa ly ex 0) -> val_mem tfibsegs m0 (sp1 + 24) 8 (kBatchBytes * zl ex) ->
lcn ly iw m0 Lk 0 -> lcn ly iw m0 ex 0 ->
DMdeq.deq_pre W ly regs1 mem1 ex Lk.

Lemma vm_mod64 : forall m a v, val_mem tfibsegs m a 8 (v mod 2 ^ 64) <-> val_mem tfibsegs m a 8 v.
Proof.
intros m a v. split; intros H k Hk; rewrite (H k Hk); do 2 f_equal;
rewrite <- (AF0x.le_byte_eq v), <- (AF0x.le_byte_eq (v mod 2 ^ 64)); unfold YG0f.le_byte;
replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity; rewrite Z.mod_mod by lia; reflexivity.
Qed.

Lemma lcn_to_mod : forall ly iw m l z, lcn ly iw m l z -> lcn ly (fun k => iw k mod 2 ^ 64) m l z.
Proof.
intros ly iw m l. induction l as [|b t IH]; intros z H; [exact I|].
cbn [lcn] in H |- *. destruct H as [(V0 & V8 & V16 & VS) HT]. split; [|exact (IH z HT)].
unfold bcell. split; [exact V0|]. split; [exact V8|]. split; [exact V16|].
intros j k Hj. cbv beta. apply (proj2 (vm_mod64 _ _ _)). exact (VS j k Hj).
Qed.

Lemma lcn_of_mod : forall ly iw m l z, lcn ly (fun k => iw k mod 2 ^ 64) m l z -> lcn ly iw m l z.
Proof.
intros ly iw m l. induction l as [|b t IH]; intros z H; [exact I|].
cbn [lcn] in H |- *. destruct H as [(V0 & V8 & V16 & VS) HT]. split; [|exact (IH z HT)].
unfold bcell. split; [exact V0|]. split; [exact V8|]. split; [exact V16|].
intros j k Hj. apply (proj1 (vm_mod64 _ _ _)). exact (VS j k Hj).
Qed.

Lemma pop_list : forall f q, qc_list q = snd (pop_batches f q []) ++ qc_list (fst (pop_batches f q [])).
Proof.
induction f as [|f IH]; intros q; cbn [pop_batches]; [reflexivity|].
destruct (qc_bytes q <=? kQuarantineMin); [reflexivity|].
destruct (qc_list q) as [|b t] eqn:E; cbn [fst snd rev app]; [rewrite E; reflexivity|].
rewrite DMdeq.pop_acc. cbn [fst snd rev app]. f_equal. exact (IH (mkQC t (qc_bytes q - b_bytes b))).
Qed.

Lemma pop_inv : forall f q acc, qc_bytes q = sum_bytes (qc_list q) ->
qc_bytes (fst (pop_batches f q acc)) = sum_bytes (qc_list (fst (pop_batches f q acc))).
Proof.
induction f as [|f IH]; intros q acc HQ; cbn [pop_batches]; [exact HQ|].
destruct (qc_bytes q <=? kQuarantineMin); [exact HQ|].
destruct (qc_list q) as [|b t] eqn:E; cbv beta iota.
- cbn [fst]. rewrite E. exact HQ.
- apply IH. cbn [qc_bytes qc_list]. rewrite HQ, AFey.sum_bytes_cons. lia.
Qed.

Lemma lcn_cells : forall ly iw m l z b, lcn ly iw m l z -> In b l ->
val_mem tfibsegs m (addrb ly b + 8) 8 (b_bytes b) /\ val_mem tfibsegs m (addrb ly b + 16) 8 (zl (b_items b)) /\
(forall j k, nth_error (b_items b) j = Some k -> val_mem tfibsegs m (addrb ly b + 24 + 8 * Z.of_nat j) 8 (iw k)).
Proof.
intros ly iw m l. induction l as [|b0 t IH]; intros z b HL Hb; [destruct Hb|].
cbn [lcn] in HL. destruct HL as [(V0 & V8 & V16 & VS) HT].
destruct Hb as [<-|Hb]; [split; [exact V8|]; split; [exact V16 | exact VS] | exact (IH _ b HT Hb)].
Qed.

Lemma vkeep : forall (Win : Z -> Prop) (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall x : word, ~ Win (bv_unsigned x) -> m' x = m x) ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, 0 <= i < Z.of_nat n -> ~ Win (a + i)) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros Win H m m' a n v HM A1 A2 HN HV. apply (val_mem_frame H m m' a n v); [|exact HV].
intros k Hk. apply HM. rewrite unsigned_lit_small by lia. apply HN. lia.
Qed.

Lemma qw_keep : forall (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall x : word, ~ DMseg_rjL.WIN (bv_unsigned x) -> m' x = m x) ->
(A_QUAR + 156 <= a \/ a + Z.of_nat n <= A_QUAR + 152) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros H m m' a n v HM HA A1 A2 HV. apply (vkeep DMseg_rjL.WIN H m m' a n v HM A1 A2); [|exact HV].
intros i Hi. unfold DMseg_rjL.WIN. lia.
Qed.

Lemma qw_lcn : forall ly iw (H : word -> bool) (m m' : word -> option byte) l z,
(forall x : word, ~ DMseg_rjL.WIN (bv_unsigned x) -> m' x = m x) ->
(forall b, In b l -> A_QUAR + 156 <= addrb ly b /\ addrb ly b + 24 + 8 * zl (b_items b) <= 2 ^ 64) ->
lcn ly iw (mrestrict H m) l z -> lcn ly iw (mrestrict H m') l z.
Proof.
intros ly iw H m m' l z HM HB. apply (DMdrainT3.lcn_keep ly iw H DMseg_rjL.WIN m m' l z HM).
intros b Hb. destruct (HB b Hb) as [B1 B2]. assert (HZ : 0 <= zl (b_items b)) by (unfold zl; lia).
split; [unfold A_QUAR, A_ALLOCATOR, o_quar in B1; lia|]. split; [exact B2|].
intros a Ha. unfold DMseg_rjL.WIN. lia.
Qed.

Lemma cells_dec : forall ly (l : list batch) a,
{exists b, In b l /\ bcells_of ly b a} + {~ exists b, In b l /\ bcells_of ly b a}.
Proof.
intros ly l a. induction l as [|b t IH].
- right. intros (b & [] & _).
- destruct (DMdrainU2.zrange_dec (addrb ly b) a (addrb ly b + 24 + 8 * zl (b_items b))) as [H|H].
  + left. exists b. split; [left; reflexivity | exact H].
  + destruct IH as [HE|N].
    * left. destruct HE as (b' & Hb' & H'). exists b'. split; [right; exact Hb' | exact H'].
    * right. intros (b' & [<-|Hb'] & H'); [exact (H H') | exact (N (ex_intro _ b' (conj Hb' H')))].
Qed.

Lemma sum_bytes_empties : forall l : list batch, (forall b, In b l -> b_items b = []) ->
sum_bytes l = kBatchBytes * zl l.
Proof.
induction l as [|b t IH]; intros HE; unfold zl in *; cbn [length].
- rewrite AFey.sum_bytes_nil. lia.
- rewrite AFey.sum_bytes_cons, (IH (fun b' Hb' => HE b' (or_intror Hb'))).
  unfold b_bytes. rewrite (HE b (or_introl eq_refl)). cbn [fold_right]. rewrite Nat2Z.inj_succ.
  unfold kBatchBytes. lia.
Qed.

Lemma ret_ok_331a4 : YK0s.ret_ok (w64 0x34418).
Proof. vm_compute. reflexivity. Qed.

Lemma atdr_of_cells : forall (W : world tfibsegs) ly md regs' mem' mat (P R : list batch) (iw : chunk -> Z),
let sp1 := bv_unsigned (getr regs' 2) in let m := mrestrict (w_H W) mem' in
getr regs' 10 = w64 A_QUAR -> getr regs' 11 = w64 sp1 -> getr regs' 1 = w64 0x344e0 ->
(forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m a = Some (Z_to_bv 8 0)) ->
val_mem tfibsegs m (A_QUAR + 160) 8 (zl R) -> val_mem tfibsegs m (A_QUAR + 168) 8 (fa ly R 0) ->
val_mem tfibsegs m (A_QUAR + 176) 8 (la ly R) -> val_mem tfibsegs m (A_QUAR + 184) 8 (sum_bytes R) ->
lcn ly iw m P 0 -> lcn ly iw m R 0 ->
val_mem tfibsegs m sp1 8 (zl P) -> val_mem tfibsegs m (sp1 + 8) 8 (fa ly P 0) ->
val_mem tfibsegs m (sp1 + 16) 8 (la ly P) -> val_mem tfibsegs m (sp1 + 24) 8 (sum_bytes P) ->
DMdeq.ATDR W ly md regs' mem' P R W
  (mkCfg (mkst regs' (w64 A_DoRecycle) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)).
Proof.
intros W ly md regs' mem' mat P R iw sp1 m H10 H11 H1 HQW CS CF CL CB LP LR T0 T8 T16 T24.
unfold DMdeq.ATDR. cbv zeta. split; [reflexivity|]. exists regs', mem', mat. splits.
- reflexivity.
- unfold DMdeq.sp1, w64. symmetry. apply Z_to_bv_bv_unsigned.
- exact H10.
- exact H11.
- reflexivity.
- reflexivity.
- exact H1.
- intros r _. reflexivity.
- intros x _. reflexivity.
- intros a _ HP _. exact HP.
- exact HQW.
- exact CS.
- exact CF.
- exact CL.
- exact CB.
- intros i b Hi. exact (DMdrainQ.lcn_next ly iw m P i b LP Hi).
- intros i b Hi. split; [exact (DMdrainQ.lcn_next ly iw m R i b LR Hi) | exact (DMdrainQ.lcn_size ly iw m R 0 i b LR Hi)].
- exact T0.
- exact T8.
- exact T16.
- exact T24.
Qed.

Lemma deq_pre_merge : deq_pre_merge_t.
Proof.
unfold deq_pre_merge_t. cbv zeta.
intros W ly regs1 mem0 mem1 L0 iw HLY HB0 HN0 HND0 HS0 HSP HAL HPRS Htp Hra R10 R11 R14 R15 R16 R5 L152 L153 L154
  HMEQ CQS CQF CQL CQB CT8 CT24 CLK CEX.
pose proof (DMmergeL.mb_model_facts_ok L0) as (MF1 & MF2 & MF3 & MF4 & MF5 & _).
pose proof (DMdrainG1.LYB2 ly HLY) as (Y1 & Y2 & Y3 & Y4 & _ & _ & _ & Y8 & Y9).
assert (HEX : forall b, In b (snd (MB L0)) -> b_items b = [])
  by (intros b Hb; exact (proj1 (Forall_forall _ _) MF3 b Hb)).
assert (HNk : forall b, In b (fst (MB L0)) -> forall k, In k (b_items b) -> 0 <= ck_n k).
{ intros b Hb k Hk. apply HN0. rewrite <- MF2. apply in_flat_map. exists b. split; [exact Hb | exact Hk]. }
assert (HBF : forall b, In b (snd (MB L0) ++ fst (MB L0)) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\ addrb ly b mod 8192 = 0 /\
  kBatchBytes <= b_bytes b).
{ intros b Hb.
  assert (Hs : In (b_self b) (map b_self L0)).
  { apply MF4. rewrite <- map_app. apply in_map. apply in_app_iff. apply in_app_iff in Hb as [Hb|Hb]; [right | left]; exact Hb. }
  apply in_map_iff in Hs as (b0 & E & Hb0). destruct (HB0 b0 Hb0) as (A1 & A2 & A3).
  unfold addrb in *. rewrite <- E. splits; try assumption.
  apply DMdrainQ.b_bytes_lb. intros k Hk. apply in_app_iff in Hb as [Hb|Hb].
  - rewrite (HEX b Hb) in Hk. destruct Hk.
  - exact (HNk b Hb k Hk). }
pose proof (DMdrainQ.nodup_app_of_in L0 (fst (MB L0)) (snd (MB L0)) HND0 MF4 MF5) as HND.
pose proof (DMdrainQ.sum_split L0 (fst (MB L0)) (snd (MB L0)) MF1 HEX HS0 HNk) as HSUM.
assert (HPR : kHighMemBeg <= ly_prim ly /\ ly_space ly + kSpaceSize <= ASAN_CEIL) by lia.
assert (HspR : kHighMemBeg + DRSTACK <= bv_unsigned (getr regs1 2) /\ bv_unsigned (getr regs1 2) + LFRAME <= kHighMemEnd)
  by lia.
replace (sum_bytes L0 - kBatchBytes * zl (snd (MB L0))) with (sum_bytes (fst (MB L0))) in CQB by lia.
rewrite <- (sum_bytes_empties _ HEX) in CT24.
eapply DMdrainL.deq_pre_merge; eassumption.
Qed.

Section g.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
Hypothesis TB : TfibSyms B.
Hypothesis QV : di_qview_t B ARX L24 QB.
Hypothesis QBB : forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29.

Definition merge_to_call_t : Prop := forall inst ly X W regs mem md mat,
drain_pre_cf B ARX L24 QB inst ly X W regs mem md ->
kQuarantineMax < AFgj.LBv (st_qglobal X) (st_qthread X) ->
DMsegDA.merge_test (st_qglobal X) (st_qthread X) = true ->
SRr tfibsegs W (mkCfg (mkst regs (w64 0x341cc) mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
(fun W' c' => exists F1 regs1 mem1 gk P,
   DMdrainU9.recyc_cut_in B ARX L24 QB inst ly X W regs mem md F1 regs1 mem1 gk P W' c').

Local Notation L0x X := (qc_list (st_qglobal X) ++ qc_list (st_qthread X)).
Local Notation Lkx X := (fst (MB (L0x X))).
Local Notation exx X := (snd (MB (L0x X))).
Local Notation gmx X := (mkQC (Lkx X) (qc_bytes (DMdrainM.gxf X) - kBatchBytes * Z.of_nat (length (exx X)))).

Theorem merge_to_call : merge_to_call_t.
Proof.
unfold merge_to_call_t. intros inst ly X W regs mem md mat PRE HGT HMT.

pose proof PRE as (HAR & HTB0 & HQB & HL24 & Hra & Hra4 & Hal & Hsp1 & Hsp2 & Hpres & Hgp & Htp & Ha0 & Ha1 & Ha2).
unfold spZ, raZ in *.
pose proof (QV inst ly X W mem md HAR (conj HTB0 (conj HQB HL24))) as QVX.
destruct QVX as [Qinst Qly Qimg Qtsd Qcells Qconst Qhpres Qbpres Qgeom Qnodup Qwf Qbytes Qinited].
pose proof (entry_free_hyps B ARX L24 QB TB QV QBB inst ly X W regs mem md PRE) as FH.
pose proof (DMdrainG1.STKR ly Qly) as [K1 K2].
pose proof (u64_range (getr regs 2)) as U2.
pose proof (@YG0f.ASAN_CEIL_range _) as CR.
assert (AQ : as_inst B + o_quar = A_QUAR) by (rewrite (ts_inst _ TB); reflexivity).
assert (AQi : inst + o_quar = A_QUAR) by (rewrite Qinst; exact AQ).
pose proof (DMdrainG1.LYB2 ly Qly) as (Y1 & Y2 & Y3 & Y4 & _).
assert (LYBj : zone3 (ly_T ly) kThreadObjSize /\ ly_T ly + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\
  ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
  ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly /\
  ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\
  (ly_T ly + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= ly_T ly) /\
  (ly_T ly + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_T ly) /\
  (ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly))
  by (eapply AFgj.LYB; exact FH).
destruct LYBj as (Z3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ATP & ATS & APS).
unfold YFeuC.DSTACK in Hsp1, Hpres.
assert (HNN : forall k, In k (flat_map b_items (L0x X)) -> 0 <= ck_n k).
{ intros k Hk. destruct Qwf as (_ & _ & _ & W4). apply (proj1 (Forall_forall _ _) W4).
  unfold q_items. apply in_flat_map in Hk as (b & Hb & Hk). apply in_flat_map. exists b. split; [|exact Hk].
  unfold all_batches. apply in_app_iff. apply in_app_iff in Hb as [Hb|Hb]; [right; exact Hb | left; exact Hb]. }
assert (HinL : forall b, In b (L0x X) -> In b (all_batches X)).
{ intros b Hb. unfold all_batches. apply in_app_iff. apply in_app_iff in Hb as [Hb|Hb]; [right; exact Hb | left; exact Hb]. }
pose proof (DMdrainG3.T_count X Qwf Qbytes HTB0) as HTcnt.
assert (HTne : qc_list (st_qthread X) <> []).
{ intros E. unfold AFgj.TSZv in HTcnt. rewrite E in HTcnt. cbn [length] in HTcnt. lia. }
pose proof (DMdrainG3.G_lcn B ly X W mem Qcells) as HLG.
assert (HLT : lcn ly (DMdrainK.iwB B ly) (mrestrict (w_H W) mem) (qc_list (st_qthread X)) 0).
{ apply (DMdrainK.lcn_of_cells B ly (w_H W) mem). apply Forall_forall. intros c Hc.
  apply (proj1 (Forall_forall _ _) Qcells). unfold quar_cells. right; right.
  apply in_app_iff. left. unfold qc_cells. do 4 right. exact Hc. }
pose proof (DMdrainG3.baddr ly X Qly Qgeom) as BADDR.
assert (HSLOT : forall b, In b (all_batches X) -> (length (b_items b) <= Z.to_nat kBatchSlots)%nat).
{ intros b Hb. destruct Qwf as (_ & _ & W3 & _). exact (proj2 (proj1 (Forall_forall _ _) W3 b Hb)). }
assert (HNDa : List.NoDup (map b_self (all_batches X))) by (apply DMdrainQ.nodup_of_stdpp; exact Qnodup).
assert (HNDl : List.NoDup (map b_self (L0x X))).
{ rewrite map_app. unfold all_batches in HNDa. rewrite map_app in HNDa.
  apply (Permutation_NoDup (l := map b_self (qc_list (st_qthread X)) ++ map b_self (qc_list (st_qglobal X))));
  [apply Permutation_app_comm | exact HNDa]. }
assert (HSUM : sum_bytes (L0x X) <= 2 ^ 31).
{ rewrite DMdrainQ.sum_bytes_app_q. destruct Qwf as (W1 & W2 & _). rewrite <- W1, <- W2. lia. }
assert (QBX : qc_bytes (DMdrainM.gxf X) = sum_bytes (L0x X)).
{ rewrite DMdrainM.gxf_bytes, DMdrainQ.sum_bytes_app_q. destruct Qwf as (W1 & W2 & _). lia. }
assert (HGL0 : forall lastb initr, rev (qc_list (st_qglobal X)) = lastb :: initr ->
  AFgj.GLv ly (st_qglobal X) = ly_space ly + b_self lastb /\ In lastb (all_batches X)).
{ intros lastb initr ER. unfold AFgj.GLv. rewrite ER. split; [reflexivity|].
  unfold all_batches. apply in_app_iff. right.
  apply (proj2 (in_rev (qc_list (st_qglobal X)) lastb)). rewrite ER. left. reflexivity. }
pose proof FH as FH2.
destruct FH2 as [fLY fIMG fHtp fHra fHra4 fHsp fHal fHpres fHg fHt fHglast fSEED].

assert (WHI : forall a, AFgj.WIN ly regs (st_qglobal X) a -> ~ qhdr inst ly a -> kHighMemBeg <= a).
{ intros a HW HQ. unfold AFgj.WIN, AFgj.WINF, AFgj.WINA in HW.
  destruct HW as [HW | [[HW | [HW | HW]] | [Hne HW]]].
  - unfold kHighMemBeg in *. lia.
  - exfalso. apply HQ. unfold qhdr. rewrite AQi. left. exact HW.
  - exfalso. apply HQ. unfold qhdr. rewrite AQi. right; left. exact HW.
  - exfalso. apply HQ. unfold qhdr. right; right. exact HW.
  - destruct (rev (qc_list (st_qglobal X))) as [|lastb initr] eqn:ER.
    + exfalso. apply Hne. rewrite <- (rev_involutive (qc_list (st_qglobal X))), ER. reflexivity.
    + destruct (HGL0 lastb initr eq_refl) as [EG HIN]. rewrite EG in HW. destruct (BADDR lastb HIN) as (A1 & _). lia. }

pose proof (DMmergeL.mb_model_facts_ok (L0x X)) as (MF1 & MF2 & MF3 & MF4 & MF5 & MF6 & _).
assert (HEX : forall b, In b (exx X) -> b_items b = []) by (intros b Hb; exact (proj1 (Forall_forall _ _) MF3 b Hb)).
assert (HSL0 : Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) (L0x X)).
{ apply Forall_forall. intros b Hb. exact (HSLOT b (HinL b Hb)). }
pose proof (MF6 HSL0) as HSLk.
assert (HSELF : forall b, In b (Lkx X ++ exx X) -> exists b0, In b0 (L0x X) /\ b_self b0 = b_self b).
{ intros b Hb. assert (Hs : In (b_self b) (map b_self (L0x X))).
  { apply MF4. rewrite <- map_app. apply in_map. exact Hb. }
  apply in_map_iff in Hs as (b0 & E & Hb0). exists b0. split; [exact Hb0 | exact E]. }
assert (HBall : forall b, In b (L0x X ++ Lkx X ++ exx X) ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\ addrb ly b mod 8192 = 0 /\
  0 <= addrb ly b < ASAN_CEIL /\ (length (b_items b) <= Z.to_nat kBatchSlots)%nat).
{ intros b Hb. apply in_app_iff in Hb as [Hb|Hb].
  - destruct (BADDR b (HinL b Hb)) as (A1 & A2 & A3 & A4). unfold addrb. splits; try assumption; try lia.
    exact (HSLOT b (HinL b Hb)).
  - destruct (HSELF b Hb) as (b0 & Hb0 & E). destruct (BADDR b0 (HinL b0 Hb0)) as (A1 & A2 & A3 & A4).
    unfold addrb. rewrite <- E. splits; try assumption; try lia.
    apply in_app_iff in Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) HSLk b Hb) | rewrite (HEX b Hb); cbn [length]; lia]. }
assert (HBH : forall b, In b (L0x X ++ Lkx X ++ exx X) ->
  A_QUAR + 156 <= addrb ly b /\ addrb ly b + 24 + 8 * zl (b_items b) <= 2 ^ 64 /\
  kHighMemBeg <= addrb ly b /\ addrb ly b + 24 + 8 * zl (b_items b) <= ly_space ly + kSpaceSize).
{ intros b Hb. destruct (HBall b Hb) as (A1 & A2 & _ & _ & A5).
  change (Z.to_nat kBatchSlots) with 1021%nat in A5. unfold zl.
  assert (Z.of_nat (length (b_items b)) <= 1021) by lia.
  unfold kBatchBytes, kHighMemBeg, A_QUAR, A_ALLOCATOR, o_quar in *. lia. }

assert (HLEB : (AFgj.LBv (st_qglobal X) (st_qthread X) <=? kQuarantineMax) = false) by (apply Z.leb_gt; exact HGT).
eapply SRr_bind;
[ exact (drain_entry_run W ly regs mem md (st_qglobal X) (st_qthread X) mat FH
    (proj1 (proj2 Qwf)) (proj1 Qwf) HNN) | ].
intros W1 c1 _ HPost.
unfold DMsegDA.postDm in HPost. rewrite HLEB, HMT in HPost.
destruct HPost as (-> & rB & mB & matB & -> & B2 & B1 & B10 & B11 & B12 & B13 & B8 & B9 & B18 & B19 & B20 & BS
  & BM & BPR & CQW & CQS & CQF & CQL & CQB & CT0 & CT8 & CT16 & CT24 & HLINK
  & V80 & V72 & V64 & V56 & V48 & V40 & V32 & V24 & V16 & V8).
assert (ESP : bv_unsigned (getr rB 2) = bv_unsigned (getr regs 2) - 80).
{ rewrite B2. unfold w64. apply unsigned_lit_small. unfold kHighMemBeg, kHighMemEnd in *. lia. }
pose proof (DMdrainTA.GT_lcn B W ly X regs mem mB BM HLINK HLG HLT HTne Qly (conj Hsp1 Hsp2)
  BADDR HSLOT HNDa (conj (proj1 Qwf) (proj1 (proj2 Qwf)))) as CLK.

pose (iw' := fun k => DMdrainK.iwB B ly k mod 2 ^ 64).
pose proof (DMmergeL.mb_ok W ly rB mB md matB iw' (L0x X)) as MBOK. unfold mb_ok_t in MBOK.
lazymatch type of MBOK with ?A -> _ => assert (MBP : A) end.
{ constructor.
  - exact Qly.
  - rewrite ESP. unfold kHighMemBeg, kHighMemEnd in *. lia.
  - rewrite ESP. replace (bv_unsigned (getr regs 2) - 80) with (bv_unsigned (getr regs 2) + (-5) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal.
  - exact B1.
  - exact B10.
  - rewrite ESP. exact B11.
  - exact B8.
  - exact B9.
  - exact B18.
  - unfold DMsegDA.merge_test in HMT. apply andb_prop in HMT as [_ HM2]. apply Z.ltb_lt in HM2.
    rewrite DMdrainU2.lsz_len in HM2. unfold AFgj.LBv, AFgj.GBv, AFgj.TBv in HM2, HGT.
    unfold kQuarantineMax, kBatchBytes in *. lia.
  - intros b Hb. destruct (BADDR b (HinL b Hb)) as (A1 & A2 & A3 & A4).
    destruct Qwf as (_ & _ & W3 & _). pose proof (proj1 (Forall_forall _ _) W3 b (HinL b Hb)) as HIT.
    unfold addrb. rewrite ESP. unfold kBatchBytes in *.
    splits; try assumption; try lia.
  - exact HNDl.
  - exact HNN.
  - intros k _. unfold iw'. apply Z.mod_pos_bound. lia.
  - exact HSUM.
  - split; [|split; [|split]].
    + rewrite DMdrainU2.lsz_len in CQS. exact CQS.
    + rewrite DMdrainU2.lf_fa in CQF. exact CQF.
    + rewrite (DMdrainU2.tl_la ly (st_qglobal X) (st_qthread X) HTne) in CQL. exact CQL.
    + rewrite (DMdrainU2.lb_sum (st_qglobal X) (st_qthread X) (proj1 (proj2 Qwf)) (proj1 Qwf)) in CQB. exact CQB.
  - rewrite ESP. split; [exact V80|]. split.
    + replace (bv_unsigned (getr regs 2) - 80 + 8) with (bv_unsigned (getr regs 2) - 72) by lia. exact V72.
    + split.
      * replace (bv_unsigned (getr regs 2) - 80 + 16) with (bv_unsigned (getr regs 2) - 64) by lia. exact V64.
      * replace (bv_unsigned (getr regs 2) - 80 + 24) with (bv_unsigned (getr regs 2) - 56) by lia. exact V56.
  - exact CQW.
  - exact (lcn_to_mod ly (DMdrainK.iwB B ly) _ _ 0 CLK).
  - intros a Ha. rewrite ESP in Ha.
    assert (HA0 : bv_unsigned (getr regs 2) - 4096 <= a < bv_unsigned (getr regs 2)) by lia.
    pose proof (Hpres a HA0) as P0.
    destruct (DMdrainU2.win_dec ly regs (st_qglobal X) a) as [HW|HW].
    + apply (BPR a HW). unfold kHighMemBeg in *. lia.
    + apply (AF0x.apresent_same (w_H W) mem mB a); [|exact P0].
      apply BM. rewrite unsigned_lit_small; [exact HW|]. unfold kHighMemBeg, kHighMemEnd in *. lia.
  - intros b a Hb Hob. pose proof (Qbpres b a (HinL b Hb) Hob) as P0.
    destruct (BADDR b (HinL b Hb)) as (A1 & A2 & A3 & A4). unfold bobj_of, addrb in Hob.
    destruct (DMdrainU2.win_dec ly regs (st_qglobal X) a) as [HW|HW].
    + apply (BPR a HW). lia.
    + apply (AF0x.apresent_same (w_H W) mem mB a); [|exact P0].
      apply BM. rewrite unsigned_lit_small; [exact HW|]. unfold kBatchBytes in *. lia. }
eapply SRr_bind; [exact (MBOK MBP) | ].
intros W2 c2 _ HMP.
destruct HMP as (-> & rP & mP & matP & -> & P2 & P1 & PS & PF & PPR & PQS & PQF & PQL & PQB & PT0 & PT8 & PT16 & PT24
  & PQW & PLK & PLX).
assert (ESPP : bv_unsigned (getr rP 2) = bv_unsigned (getr regs 2) - 80).
{ rewrite P2, ESP. unfold w64. apply unsigned_lit_small. unfold kHighMemBeg, kHighMemEnd in *. lia. }
rewrite ESP in PT0, PT8, PT16, PT24.
pose proof (lcn_of_mod ly (DMdrainK.iwB B ly) _ _ 0 PLK) as LKP.
pose proof (lcn_of_mod ly (DMdrainK.iwB B ly) _ _ 0 PLX) as LXP.

assert (PRES2 : forall a, 0 <= a < 2 ^ 64 -> ~ qhdr inst ly a -> apresent (w_H W) mem a -> apresent (w_H W) mP a).
{ intros a HA HQ HP.
  assert (PB : apresent (w_H W) mB a).
  { destruct (DMdrainU2.win_dec ly regs (st_qglobal X) a) as [HW|HW].
    - exact (BPR a HW (WHI a HW HQ)).
    - apply (AF0x.apresent_same (w_H W) mem mB a); [|exact HP]. apply BM. rewrite unsigned_lit_small by lia. exact HW. }
  destruct (DMdrainU2.zrange_dec (bv_unsigned (getr regs 2) - 96) a (bv_unsigned (getr regs 2) - 48)) as [HS|HS].
  - apply PPR; [unfold mbwin; rewrite ESP; left; lia | unfold kHighMemBeg in *; lia].
  - destruct (cells_dec ly (L0x X ++ Lkx X ++ exx X) a) as [HC|HC].
    + apply PPR; [unfold mbwin; right; right; exact HC |].
      destruct HC as (b & Hb & HC). destruct (HBH b Hb) as (_ & _ & H3 & _). unfold bcells_of in HC. lia.
    + apply (AF0x.apresent_same (w_H W) mB mP a); [|exact PB]. apply PF. rewrite unsigned_lit_small by lia.
      unfold mbwin. rewrite ESP. intros [H|[H|H]].
      * lia.
      * apply HQ. unfold qhdr. rewrite AQi. right; left. exact H.
      * exact (HC H). }

assert (KSP : forall off v, 8 <= off <= 48 ->
  val_mem tfibsegs (mrestrict (w_H W) mB) (bv_unsigned (getr regs 2) - off) 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) mP) (bv_unsigned (getr regs 2) - off) 8 v).
{ intros off v Ho HV.
  apply (vkeep _ (w_H W) mB mP _ 8 v PF); [unfold kHighMemBeg in *; lia | cbn; unfold kHighMemEnd in *; lia | | exact HV].
  intros i Hi HM. cbn in Hi. unfold mbwin in HM. rewrite ESP in HM.
  destruct HM as [HM | [HM | (b & Hb & HC)]].
  - lia.
  - unfold A_QUAR, A_ALLOCATOR, o_quar, kHighMemBeg in *. lia.
  - destruct (HBH b Hb) as (_ & _ & H3 & H4). destruct (HBall b Hb) as (A1 & _).
    unfold bcells_of in HC. destruct APS as [APS|APS]; lia. }
assert (KTP : forall off v, 0 <= off <= 24 ->
  val_mem tfibsegs (mrestrict (w_H W) mB) (ly_T ly + t_qc + off) 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) mP) (ly_T ly + t_qc + off) 8 v).
{ intros off v Ho HV. pose proof Z3 as (Z3a & Z3b & _).
  apply (vkeep _ (w_H W) mB mP _ 8 v PF); [unfold t_qc; lia | cbn; unfold t_qc, kThreadObjSize in *; lia | | exact HV].
  intros i Hi HM. cbn in Hi. unfold mbwin in HM. rewrite ESP in HM.
  pose proof (AF0x.zone3_off_img (ly_T ly) kThreadObjSize (ly_T ly + t_qc + off + i) Z3
    ltac:(unfold t_qc, kThreadObjSize; lia)) as OI.
  destruct HM as [HM | [HM | (b & Hb & HC)]].
  - unfold t_qc, kThreadObjSize in *. destruct ATS as [ATS|ATS]; lia.
  - unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END, A_QUAR, A_ALLOCATOR, o_quar in *. lia.
  - destruct (HBH b Hb) as (_ & _ & H3 & H4). destruct (HBall b Hb) as (A1 & _).
    unfold bcells_of in HC. unfold t_qc, kThreadObjSize in *. destruct ATP as [ATP|ATP]; lia. }

assert (MT : DMdrainM.mtest (DMdrainM.gxf X) = true).
{ unfold DMdrainM.mtest. rewrite DMdrainM.gxf_list, DMdrainM.gxf_bytes, <- DMdrainU2.lsz_len. exact HMT. }
assert (ESPLIT : merge_split_cf (DMdrainM.gxf X) = (gmx X, exx X)).
{ rewrite (DMdrainM.merge_split_cf_MB _ MT). rewrite DMdrainM.gxf_list. reflexivity. }
assert (HBX : kQuarantineMax < qc_bytes (DMdrainM.gxf X)) by (rewrite DMdrainM.gxf_bytes; exact HGT).
assert (EB : qc_bytes (gmx X) = sum_bytes (Lkx X)).
{ cbn [qc_bytes]. rewrite QBX. unfold zl in MF1. unfold kBatchBytes in *. lia. }

assert (Q8 : getr rP 8 = w64 (A_QUAR + 160)) by (rewrite (PS 8%bv) by (unfold SREGSX; cbn [In]; tauto); exact B8).
assert (Q9 : getr rP 9 = w64 kQuarantineMin) by (rewrite (PS 9%bv) by (unfold SREGSX; cbn [In]; tauto); exact B9).
assert (Q18 : getr rP 18 = w64 A_QUAR) by (rewrite (PS 18%bv) by (unfold SREGSX; cbn [In]; tauto); exact B18).
assert (HspP : kHighMemBeg <= bv_unsigned (getr rP 2) /\ bv_unsigned (getr rP 2) + 32 <= kHighMemEnd)
  by (rewrite ESPP; unfold kHighMemBeg, kHighMemEnd in *; lia).
assert (HalP : bv_unsigned (getr rP 2) mod 16 = 0).
{ rewrite ESPP. replace (bv_unsigned (getr regs 2) - 80) with (bv_unsigned (getr regs 2) + (-5) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal. }
assert (HB0 : forall b, In b (L0x X) ->
  kHighMemBeg <= addrb ly b /\ addrb ly b + kBatchBytes <= ASAN_CEIL /\ addrb ly b mod 8192 = 0 /\
  (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat).
{ intros b Hb. destruct (BADDR b (HinL b Hb)) as (A1 & A2 & A3 & A4).
  destruct Qwf as (_ & _ & W3 & _). pose proof (proj1 (Forall_forall _ _) W3 b (HinL b Hb)) as HIT.
  unfold addrb. split; [lia|]. split; [lia|]. split; [exact A3 | exact HIT]. }
assert (HIN : forall b, In b (Lkx X ++ exx X) -> In (b_self b) (map b_self (L0x X))).
{ intros b Hb. apply MF4. rewrite <- map_app. apply in_map. exact Hb. }
assert (Hl : 0 <= Z.of_nat (length (Lkx X)) <= 2 ^ 40 /\ 0 <= fa ly (Lkx X) 0 < ASAN_CEIL /\
  fa ly (Lkx X) 0 mod 8192 = 0 /\ 0 <= sum_bytes (L0x X) - kBatchBytes * Z.of_nat (length (exx X)) <= 2 ^ 31)
  by (eapply DMdrainS.rj_Hl; eassumption).
assert (Ht : 0 <= Z.of_nat (length (exx X)) <= 2 ^ 40 /\ 0 <= la ly (exx X) < ASAN_CEIL /\ la ly (exx X) mod 8192 = 0)
  by (eapply DMdrainS.rj_Ht; eassumption).
assert (VT0 : val_mem tfibsegs (mrestrict (w_H W) mP) (bv_unsigned (getr rP 2)) 8 (zl (exx X)))
  by (rewrite ESPP; exact PT0).
assert (VT16 : val_mem tfibsegs (mrestrict (w_H W) mP) (bv_unsigned (getr rP 2) + 16) 8 (la ly (exx X)))
  by (rewrite ESPP; exact PT16).
assert (FHR0 : DMseg_rj.free_hyps W rP mP (zl (Lkx X)) (fa ly (Lkx X) 0)
  (sum_bytes (L0x X) - kBatchBytes * zl (exx X)) (zl (exx X)) (la ly (exx X)))
  by (eapply DMdrainB.rj_free_hyps; eassumption).
assert (FHR : DMseg_rjL.free_hyps W rP mP (zl (Lkx X)) (fa ly (Lkx X) 0)
  (sum_bytes (L0x X) - kBatchBytes * zl (exx X)) (zl (exx X)) (la ly (exx X))).
{ destruct FHR0 as [f1 f2 f3 f4 f5]. constructor; assumption. }

assert (HBk : forall b, In b (Lkx X) -> A_QUAR + 156 <= addrb ly b /\ addrb ly b + 24 + 8 * zl (b_items b) <= 2 ^ 64).
{ intros b Hb. destruct (HBH b ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hb)) as (H1 & H2 & _). split; assumption. }
assert (HBx : forall b, In b (exx X) -> A_QUAR + 156 <= addrb ly b /\ addrb ly b + 24 + 8 * zl (b_items b) <= 2 ^ 64).
{ intros b Hb. destruct (HBH b ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb)) as (H1 & H2 & _). split; assumption. }
assert (HSTK : A_QUAR + 156 <= bv_unsigned (getr regs 2) - 80 /\ 0 <= bv_unsigned (getr regs 2) - 80 /\
  bv_unsigned (getr regs 2) + 8 <= 2 ^ 64)
  by (unfold A_QUAR, A_ALLOCATOR, o_quar, kHighMemBeg, kHighMemEnd in *; lia).
assert (HQ : SRr tfibsegs W (mkCfg (mkst rP (w64 0x34418) mP (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) matP md))
  (fun W' c' => exists rL mL g' popped,
     bv_unsigned (getr rL 2) = bv_unsigned (getr rP 2) /\
     (forall r : bv 5, In r DMseg_rjL.SREGS -> getr rL r = getr rP r) /\
     getr rL 12 = getr rP 20 /\
     (forall x : word, ~ DMseg_rjL.WIN (bv_unsigned x) -> mL x = mP x) /\
     pop_batches (S (length (qc_list (gmx X)))) (gmx X) [] = (g', popped) /\
     DMdeq.ATDR W ly md rL mL (exx X ++ popped) (qc_list g') W' c')).
{ eapply SRr_bind; [eapply DMseg_rjL.segR; exact FHR |].
  intros W3 c3 _ HR. revert HR. unfold DMseg_rjL.postR.
  destruct (kQuarantineMin <? sum_bytes (L0x X) - kBatchBytes * zl (exx X)); intros HR.
  -
    destruct HR as (-> & HLB & rL & mL & matL & -> & L2 & LS & L8 & L9 & L18 & L10 & L11 & L12 & L13 & L14 & L15 & L16
      & L5 & L1 & LM & L152 & L153 & L154).
    pose proof (deq_pre_merge W ly rL mP mL (L0x X) iw') as DPM. cbv zeta in DPM.
    assert (DP : DMdeq.deq_pre W ly rL mL (exx X) (Lkx X)).
    { apply DPM.
      - exact Qly.
      - intros b Hb. destruct (BADDR b (HinL b Hb)) as (A1 & A2 & A3 & _). unfold addrb. splits; assumption.
      - exact HNN.
      - exact HNDl.
      - exact HSUM.
      - rewrite L2, ESPP. unfold DRSTACK, LFRAME. lia.
      - rewrite L2, ESPP. replace (bv_unsigned (getr regs 2) - 80) with (bv_unsigned (getr regs 2) + (-5) * 16) by lia.
        rewrite Z_mod_plus_full. exact Hal.
      - intros a Ha. rewrite L2, ESPP in Ha. unfold DRSTACK, LFRAME in Ha.
        assert (HA0 : bv_unsigned (getr regs 2) - 4096 <= a < bv_unsigned (getr regs 2)) by lia.
        pose proof Z3 as (Z3a & Z3b & _).
        assert (HQa : ~ qhdr inst ly a).
        { unfold qhdr. rewrite AQi. intros H.
          unfold A_QUAR, A_ALLOCATOR, o_quar, kHighMemBeg, t_qc, kThreadObjSize in *. destruct ATS as [ATS|ATS]; lia. }
        apply (AF0x.apresent_same (w_H W) mP mL a).
        + apply LM. rewrite unsigned_lit_small by (unfold kHighMemBeg, kHighMemEnd in *; lia).
          unfold DMseg_rjL.WIN. unfold A_QUAR, A_ALLOCATOR, o_quar, kHighMemBeg in *. lia.
        + apply PRES2; [unfold kHighMemBeg, kHighMemEnd in *; lia | exact HQa | exact (Hpres a HA0)].
      - rewrite (LS 4%bv) by (unfold DMseg_rjL.SREGS; cbn [In]; tauto).
        rewrite (PS 4%bv) by (unfold SREGSX; cbn [In]; tauto).
        rewrite (BS 4%bv) by (unfold DMsegDA.SREGS_M; cbn [In]; tauto). exact fHtp.
      - rewrite L1, P1. exact ret_ok_331a4.
      - exact L10.
      - exact L11.
      - exact L14.
      - exact L15.
      - exact L16.
      - exact L5.
      - exact L152.
      - exact L153.
      - exact L154.
      - exact LM.
      - exact PQS.
      - exact PQF.
      - exact PQL.
      - exact PQB.
      - rewrite L2, ESPP. exact PT8.
      - rewrite L2, ESPP. exact PT24.
      - exact PLK.
      - exact PLX. }
    assert (GT : kQuarantineMin < qc_bytes (gmx X)).
    { rewrite EB. unfold zl in *. unfold kBatchBytes in *. lia. }
    eapply SRr_mono; [exact (DMdeq.tfib_deq_ok W ly md rL mL matL (exx X) (Lkx X) (gmx X) DP eq_refl EB GT) |].
    intros W5 c5 _ (g' & popped & HPB & HAT).
    exists rL, mL, g', popped. splits; [rewrite L2; reflexivity | exact LS | exact L12 | exact LM | exact HPB | exact HAT].
  -
    destruct HR as (-> & HLE & rX & mX & matX & -> & X2 & XS & X10 & X11 & X12 & X13 & X1 & XM & X152).
    apply SRr_ret. exists rX, mX, (gmx X), []. splits.
    + rewrite X2. reflexivity.
    + exact XS.
    + exact X12.
    + exact XM.
    + rewrite DMdeq.pop_stop; [reflexivity|]. rewrite QBX. unfold zl in *. unfold kBatchBytes in *. lia.
    + rewrite app_nil_r. cbn [qc_list].
      assert (SX : bv_unsigned (getr rX 2) = bv_unsigned (getr regs 2) - 80) by (rewrite X2; exact ESPP).
      apply (atdr_of_cells W ly md rX mX matX (exx X) (Lkx X) (DMdrainK.iwB B ly)).
      * exact X10.
      * rewrite X11, X2. unfold w64. symmetry. apply Z_to_bv_bv_unsigned.
      * exact X1.
      * exact X152.
      * apply (qw_keep _ mP mX _ 8 _ XM); [left; lia | unfold A_QUAR, A_ALLOCATOR, o_quar; lia | cbn; unfold A_QUAR, A_ALLOCATOR, o_quar; lia | exact PQS].
      * apply (qw_keep _ mP mX _ 8 _ XM); [left; lia | unfold A_QUAR, A_ALLOCATOR, o_quar; lia | cbn; unfold A_QUAR, A_ALLOCATOR, o_quar; lia | exact PQF].
      * apply (qw_keep _ mP mX _ 8 _ XM); [left; lia | unfold A_QUAR, A_ALLOCATOR, o_quar; lia | cbn; unfold A_QUAR, A_ALLOCATOR, o_quar; lia | exact PQL].
      * replace (sum_bytes (Lkx X)) with (sum_bytes (L0x X) - kBatchBytes * zl (exx X)) by (unfold zl in *; lia).
        apply (qw_keep _ mP mX _ 8 _ XM); [left; lia | unfold A_QUAR, A_ALLOCATOR, o_quar; lia | cbn; unfold A_QUAR, A_ALLOCATOR, o_quar; lia | exact PQB].
      * exact (qw_lcn ly _ (w_H W) mP mX _ 0 XM HBx LXP).
      * exact (qw_lcn ly _ (w_H W) mP mX _ 0 XM HBk LKP).
      * rewrite SX. apply (qw_keep _ mP mX _ 8 _ XM); [left; lia | lia | cbn; lia | exact PT0].
      * rewrite SX. apply (qw_keep _ mP mX _ 8 _ XM); [left; lia | lia | cbn; lia | exact PT8].
      * rewrite SX. apply (qw_keep _ mP mX _ 8 _ XM); [left; lia | lia | cbn; lia | exact PT16].
      * rewrite SX, (sum_bytes_empties _ HEX). apply (qw_keep _ mP mX _ 8 _ XM); [left; lia | lia | cbn; lia | exact PT24]. }
eapply SRr_mono; [exact HQ |].
intros W4 c4 _ (rL & mL & g' & popped & QL2 & QLS & QL12 & QLM & HPB & HAT).

pose proof (pop_list (S (length (qc_list (gmx X)))) (gmx X)) as PS0. rewrite HPB in PS0. cbn [fst snd qc_list] in PS0.
assert (HCUT : forall b, In b ((exx X ++ popped) ++ qc_list g') -> In b (exx X ++ Lkx X)).
{ intros b Hb. rewrite <- app_assoc, <- PS0 in Hb. exact Hb. }
pose proof (qw_lcn ly _ (w_H W) mP mL _ 0 QLM HBk LKP) as LKL.
pose proof (qw_lcn ly _ (w_H W) mP mL _ 0 QLM HBx LXP) as LXL.
assert (KSL : forall off v, 8 <= off <= 48 ->
  val_mem tfibsegs (mrestrict (w_H W) mB) (bv_unsigned (getr regs 2) - off) 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) mL) (bv_unsigned (getr regs 2) - off) 8 v).
{ intros off v Ho HV. apply (qw_keep _ mP mL _ 8 v QLM); [left; lia | lia | cbn; lia | exact (KSP off v Ho HV)]. }
assert (KTL : forall off v, 0 <= off <= 24 ->
  val_mem tfibsegs (mrestrict (w_H W) mB) (ly_T ly + t_qc + off) 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) mL) (ly_T ly + t_qc + off) 8 v).
{ intros off v Ho HV. pose proof Z3 as (Z3a & Z3b & _).
  pose proof (AF0x.zone3_off_img (ly_T ly) kThreadObjSize (ly_T ly + t_qc + off) Z3
    ltac:(unfold t_qc, kThreadObjSize; lia)) as OI.
  apply (qw_keep _ mP mL _ 8 v QLM); [| unfold t_qc; lia | cbn; unfold t_qc, kThreadObjSize in *; lia | exact (KTP off v Ho HV)].
  unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in OI. unfold A_QUAR, A_ALLOCATOR, o_quar. cbn [Z.of_nat]. lia. }
exists (MWIN ly regs X (gmx X) (exx X)), rL, mL, g', (exx X ++ popped).
unfold DMdrainU9.recyc_cut_in. cbv zeta. splits.
- exact PRE.
- exact (DMdrainM.drain_recyc_intro X (gmx X) (exx X) g' popped HBX ESPLIT HPB).
-
  intros x HX.
  assert (N3 : ~ AFgj.WIN ly regs (st_qglobal X) (bv_unsigned x)) by (intros HW; apply HX; left; exact HW).
  rewrite (QLM x).
  + rewrite (PF x).
    * exact (BM x N3).
    * intros HM. apply HX. unfold mbwin in HM. rewrite ESP in HM. unfold MWIN.
      destruct HM as [HM | [HM | HC]].
      -- destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned (getr regs 2) - 80)) as [Hlt|Hge].
         ++ right; left. lia.
         ++ left. unfold AFgj.WIN. left. lia.
      -- left. unfold AFgj.WIN, AFgj.WINF. right; left; right; left. exact HM.
      -- right; right. exact HC.
  + unfold DMseg_rjL.WIN. intros HW. apply HX. left. unfold AFgj.WIN, AFgj.WINF. right; left; left. exact HW.
-
  intros a HA. unfold MWIN in HA. unfold dwin_q, qhdr, bcellw.
  destruct HA as [HW | [HS | (b & Hb & HC)]].
  + unfold AFgj.WIN, AFgj.WINF, AFgj.WINA in HW.
    destruct HW as [HW | [[HW | [HW | HW]] | [Hne HW]]].
    * left. unfold YFeuC.DSTACK. lia.
    * right; left; left. rewrite AQi. lia.
    * right; left; right; left. rewrite AQi. lia.
    * right; left; right; right. lia.
    * destruct (rev (qc_list (st_qglobal X))) as [|lastb initr] eqn:ER.
      -- exfalso. apply Hne. rewrite <- (rev_involutive (qc_list (st_qglobal X))), ER. reflexivity.
      -- destruct (HGL0 lastb initr eq_refl) as [EG HIN0]. right; right. exists lastb. split.
         ++ apply in_app_iff. left. exact HIN0.
         ++ rewrite EG in HW. lia.
  + left. unfold YFeuC.DSTACK. lia.
  + right; right. exists b. split; [| unfold bcells_of, addrb, zl in HC; exact HC].
    apply in_app_iff in Hb as [Hb | Hb].
    * apply in_app_iff. left. apply HinL. exact Hb.
    * apply in_app_iff in Hb as [Hb | Hb].
      -- change (In b (Lkx X)) in Hb. rewrite PS0 in Hb. apply in_app_iff in Hb as [Hb | Hb].
         ++ apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hb.
         ++ apply in_app_iff. right. apply in_app_iff. left. unfold all_batches. apply in_app_iff. right. exact Hb.
      -- apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. exact Hb.
-
  intros a HA HQa HP. apply (AF0x.apresent_same (w_H W) mP mL a); [|exact (PRES2 a HA HQa HP)].
  apply QLM. rewrite unsigned_lit_small by lia. unfold DMseg_rjL.WIN. intros HW. apply HQa.
  unfold qhdr. rewrite AQi. left. exact HW.
-
  intros b Hb. apply HCUT in Hb.
  destruct (HSELF b ltac:(apply in_app_iff; apply in_app_iff in Hb as [Hb|Hb]; [right | left]; exact Hb)) as (b0 & Hb0 & E).
  destruct (BADDR b0 (HinL b0 Hb0)) as (A1 & A2 & A3 & A4). unfold addrb. rewrite <- E.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3 | exact A4].
-
  intros b Hb. apply HCUT in Hb.
  destruct (HBall b ltac:(apply in_app_iff; right; apply in_app_iff; apply in_app_iff in Hb as [Hb|Hb]; [right | left]; exact Hb))
    as (_ & _ & _ & _ & A5). exact A5.
-
  rewrite <- app_assoc, <- PS0. exact (DMdrainQ.nodup_app_of_in (L0x X) (Lkx X) (exx X) HNDl MF4 MF5).
-
  intros b Hb. apply HCUT in Hb.
  destruct (HSELF b ltac:(apply in_app_iff; apply in_app_iff in Hb as [Hb|Hb]; [right | left]; exact Hb)) as (b0 & Hb0 & E).
  exists b0. split; [exact (HinL b0 Hb0) | exact E].
-
  intros b Hb. apply HCUT in Hb. apply in_app_iff in Hb as [Hb|Hb].
  + exact (lcn_cells _ _ _ _ _ b LXL Hb).
  + exact (lcn_cells _ _ _ _ _ b LKL Hb).
- exact (KSL 8 _ ltac:(lia) V8).
- exact (KSL 16 _ ltac:(lia) V16).
- exact (KSL 24 _ ltac:(lia) V24).
- exact (KSL 32 _ ltac:(lia) V32).
- exact (KSL 40 _ ltac:(lia) V40).
- exact (KSL 48 _ ltac:(lia) V48).
- pose proof (KTL 0 0 ltac:(lia) ltac:(rewrite Z.add_0_r; exact CT0)) as K. rewrite Z.add_0_r in K. exact K.
- exact (KTL 8 0 ltac:(lia) CT8).
- exact (KTL 16 0 ltac:(lia) CT16).
- exact (KTL 24 0 ltac:(lia) CT24).
- rewrite QL2. exact ESPP.
- intros r Hr.
  assert (Hr1 : In r DMseg_rjL.SREGS) by (unfold DMsegDA.SREGS_M in Hr; unfold DMseg_rjL.SREGS; cbn [In] in Hr |- *; tauto).
  assert (Hr2 : In r SREGSX) by (unfold DMsegDA.SREGS_M in Hr; unfold SREGSX; cbn [In] in Hr |- *; tauto).
  rewrite (QLS r Hr1), (PS r Hr2). exact (BS r Hr).
- rewrite QL12, (PS 20%bv) by (unfold SREGSX; cbn [In]; tauto). exact B20.
- pose proof (pop_inv (S (length (qc_list (gmx X)))) (gmx X) [] EB) as PI. rewrite HPB in PI. exact PI.
- exact HAT.
Qed.
End g.
End f.

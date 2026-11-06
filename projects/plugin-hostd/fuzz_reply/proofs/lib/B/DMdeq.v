(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdeq.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 74a3254b72b5) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 7 image addresses moved by code-verified function pairs (6 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 1 code pcs the tool read as sizes, by funcpair.py), and 7 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdeq.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (14 numerals; per-numeral report). *)
(* The dequeue loop of Quarantine::Recycle AFTER MergeBatches (the real-merge drain, DMspec.v): from the loop head
   0x33ae4 to Recycle's call of DoRecycle (pc A_DoRecycle, ra 0x33b58).

   Ported from proofs/cgif/cgif_file_fuzzer/lib/YFer.v (the released loop): the pop iteration is YFgl's shell and
   YFh0.segL, unchanged (both are general in the temp list: the temp count np, last lp, first tfi and bytes tby are
   parameters), and the invariant has YFer's shape, restated
   - over the memory [mem1] at the loop's entry (after MergeBatches, DMseg_rj.at_RJL), not over the drain-entry
     memory: the frame clause and the presence clause are relative to [mem1]. So the thread cache's header, the
     saved registers on Recycle's frame and the old tail cell of the global list (YFer's VQ0..VQ24, VS32..VS72, VG)
     are kept by the frame and leave the invariant; the registers are relative to the entry registers [regs1];
   - over the whole list [L = ex ++ Lk]: [ex] are the batches MergeBatches extracted (emptied); at the loop's entry
     they are already the temp list at Recycle's sp (count in a4, last in a5, first at sp + 8, bytes at sp + 24).
     [Lk] is the kept list, the loop pops from it. The temp list at a loop cut is [ex ++ popped]; the global
     list's tail cell holds [lastaddr L] (= lastaddr Lk) until the last pop;
   - the batch facts (placement in the primary space, 8192-alignment, distinct offsets, the byte bound) are
     hypotheses on [L], not read from drain_pre / AR (the composition derives them from DMiface.qview and
     merge_batches_cf). Two batch objects are apart because their offsets are distinct multiples of 8192, so
     YFey.batches_apart is not needed; the length bound (YFer.len_L) follows from the byte bound.
   The end state [ATDR P R] is Recycle's call of DoRecycle with the temp list [P] at sp (P = ex ++ popped,
   DMiface.drain_recyc's P, which DMrec.v consumes) and the kept global list [R].
   Main result: [tfib_deq_ok] (end of file). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0l YG0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFex YFf2 YFfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFew YFff YFeu YFey YFgj YFgl YFh0 YFev YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YFer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize,
TFIB_IMG_END, kBatchBytes, DRSTACK, LFRAME, A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMin in *.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma apart8192 : forall x y, x mod 8192 = 0 -> y mod 8192 = 0 -> x <> y -> x + 8192 <= y \/ y + 8192 <= x.
Proof.
intros x y Hx Hy NE. pose proof (Z.div_mod x 8192 ltac:(lia)) as Ex. pose proof (Z.div_mod y 8192 ltac:(lia)) as Ey.
rewrite Hx in Ex. rewrite Hy in Ey. lia.
Qed.
(* pop_batches with a non-empty accumulator: the accumulated batches come first. *)
Lemma pop_acc : forall f q acc, pop_batches f q acc = (fst (pop_batches f q []), rev acc ++ snd (pop_batches f q [])).
Proof.
induction f as [|f IH]; intros q acc; cbn [pop_batches].
- cbn. rewrite app_nil_r. reflexivity.
- destruct (qc_bytes q <=? kQuarantineMin); [cbn; rewrite app_nil_r; reflexivity|].
  destruct (qc_list q) as [|b t]; [cbn; rewrite app_nil_r; reflexivity|].
  rewrite (IH _ (b :: acc)), (IH _ [b]). cbn [fst snd rev app]. rewrite <- app_assoc. reflexivity.
Qed.
(* YFer.pop_step / pop_stop (YFer states them inside its drain_pre section, so they carry its section variables) *)
Lemma pop_step : forall f b R' s acc, kQuarantineMin < s ->
pop_batches (S f) (mkQC (b :: R') s) acc = pop_batches f (mkQC R' (s - b_bytes b)) (b :: acc).
Proof. intros f b R' s acc H. cbn [pop_batches qc_bytes qc_list]. destruct (Z.leb_spec s kQuarantineMin); [lia | reflexivity]. Qed.
Lemma pop_stop : forall f R' s acc, s <= kQuarantineMin -> pop_batches f (mkQC R' s) acc = (mkQC R' s, rev acc).
Proof. intros f R' s acc H. destruct f; cbn [pop_batches qc_bytes qc_list]; [reflexivity|]. destruct (Z.leb_spec s kQuarantineMin); [reflexivity | lia]. Qed.
Section d.
Variables (W : world tfibsegs) (ly : alayout) (md : Model).
(* the registers and the memory at the loop's entry 0x33ae4 *)
Variables (regs1 : bvmap 5 word) (mem1 : word -> option byte).
(* the extracted batches (the temp list at the entry) and the kept list *)
Variables (ex Lk : list batch).
Local Notation H0 := (w_H W).
Local Notation SB := (ly_space ly).
Definition sp1 : Z := bv_unsigned (getr regs1 2).
Definition L : list batch := ex ++ Lk.
Definition addr (b : batch) : Z := SB + b_self b.
Definition firstaddr (l : list batch) : Z := match l with [] => 0 | b :: _ => addr b end.
Definition lastaddr (l : list batch) : Z := match rev l with [] => 0 | b :: _ => addr b end.
Definition zlen (l : list batch) : Z := Z.of_nat (length l).
Hypothesis LY : layout_ok ly.
Hypothesis BF : forall b, In b L ->
  ly_prim ly <= addr b /\ addr b + kBatchBytes <= SB + kSpaceSize /\ addr b mod 8192 = 0 /\ kBatchBytes <= b_bytes b.
Hypothesis ND : List.NoDup (map b_self L).
Hypothesis SUM : sum_bytes L <= 2 ^ 31.
Hypothesis Hsp1 : ly_stk_lo ly + DRSTACK <= sp1 /\ sp1 + LFRAME <= ly_stk_hi ly.
Hypothesis HAL : sp1 mod 16 = 0.
Hypothesis PRS1 : forall a, sp1 - DRSTACK <= a < sp1 + LFRAME -> apresent H0 mem1 a.
Hypothesis Htp : getr regs1 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs1 1).
Lemma LYB :
kHighMemBeg <= ly_prim ly /\ ly_prim ly <= SB /\
SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly /\ ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly).
Proof.
pose proof (lo_high ly LY) as HI. unfold owned_extents in HI.
repeat match type of HI with Forall _ (_ :: _) => apply Forall_cons_iff in HI as [? HI] end.
pose proof (lo_space_in ly LY) as HSP. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
unfold zdisjoint in PT, PSTK. unfold in_high in *. cbn [fst snd] in *.
repeat split; try lia.
Qed.
Lemma Usp1 : kHighMemBeg + DRSTACK <= sp1 /\ sp1 + LFRAME <= kHighMemEnd /\ ly_stk_lo ly + DRSTACK <= sp1 /\ sp1 + LFRAME <= ly_stk_hi ly /\ 0 <= sp1 < 2 ^ 64.
Proof.
pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & K4 & K5 & _). pose proof Hsp1 as [S1 S2].
assert (U : 0 <= sp1 < 2 ^ 64) by (unfold sp1; apply u64_range). unfold DRSTACK, LFRAME in *. lia.
Qed.
Lemma bfacts : forall b, In b L ->
ly_prim ly <= addr b /\ addr b + kBatchBytes <= SB + kSpaceSize /\ addr b mod 8192 = 0 /\
kHighMemBeg <= addr b /\ addr b + kBatchBytes <= ASAN_CEIL /\ kBatchBytes <= b_bytes b.
Proof. intros b Hb. pose proof LYB as (P1 & _ & P3 & P4 & _). destruct (BF b Hb) as (B1 & B2 & B3 & B4). splits; try assumption; lia. Qed.
Lemma L_apart : forall l1 b1 l2 b2 l3, L = l1 ++ b1 :: l2 ++ b2 :: l3 -> addr b1 + kBatchBytes <= addr b2 \/ addr b2 + kBatchBytes <= addr b1.
Proof.
intros l1 b1 l2 b2 l3 E. pose proof ND as ND0. rewrite E, map_app in ND0. cbn [map] in ND0. rewrite map_app in ND0. cbn [map] in ND0.
apply NoDup_app_iff in ND0 as (_ & ND0 & _). inversion ND0 as [|x l N1 N2]; subst.
assert (NE : b_self b1 <> b_self b2) by (intros EQ; apply N1; rewrite EQ; apply in_app_iff; right; left; reflexivity).
assert (I1 : In b1 L) by (rewrite E; apply in_app_iff; right; left; reflexivity).
assert (I2 : In b2 L) by (rewrite E; apply in_app_iff; right; right; apply in_app_iff; right; left; reflexivity).
destruct (BF b1 I1) as (_ & _ & M1 & _). destruct (BF b2 I2) as (_ & _ & M2 & _).
unfold kBatchBytes. apply apart8192; [exact M1 | exact M2 |]. unfold addr. lia.
Qed.
Lemma sum_lb : forall l, (forall b, In b l -> In b L) -> 0 <= sum_bytes l.
Proof.
intros l Hl. induction l as [|b2 l IH]; [cbn; lia|]. rewrite sum_bytes_cons.
destruct (BF b2 (Hl b2 (or_introl eq_refl))) as (_ & _ & _ & B4).
pose proof (IH ltac:(intros b3 Hb3; apply Hl; right; exact Hb3)). unfold kBatchBytes in *. lia.
Qed.
Lemma len_sum : forall l, (forall b, In b l -> In b L) -> 8192 * zlen l <= sum_bytes l.
Proof.
intros l Hl. induction l as [|b2 l IH]; [unfold zlen; rewrite sum_bytes_nil; cbn [length Z.of_nat]; lia|]. rewrite sum_bytes_cons.
destruct (BF b2 (Hl b2 (or_introl eq_refl))) as (_ & _ & _ & B4).
pose proof (IH ltac:(intros b3 Hb3; apply Hl; right; exact Hb3)) as IH'. unfold zlen, kBatchBytes in *. cbn [length]. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma len_L : zlen L <= 2 ^ 18.
Proof. pose proof (len_sum L (fun b H => H)) as E. pose proof SUM. lia. Qed.
Lemma first_range : forall l, (forall b, In b l -> In b L) -> 0 <= firstaddr l < ASAN_CEIL /\ firstaddr l mod 8192 = 0 /\ (l <> [] -> kHighMemBeg <= firstaddr l).
Proof.
intros l Hl. unfold firstaddr. destruct l as [|b2 t]; [ceil; unfold ASAN_CEIL; splits; [lia | lia | reflexivity | intros NE; exfalso; exact (NE eq_refl)]|].
destruct (bfacts b2 (Hl b2 (or_introl eq_refl))) as (L1 & L2 & L3 & L4 & L5 & _). unfold zone3, TFIB_IMG_LO, kLowShadowBeg, addr, kBatchBytes, kHighMemBeg in *. splits; try lia; try exact L3.
Qed.
Lemma last_range : forall l, (forall b, In b l -> In b L) -> 0 <= lastaddr l < ASAN_CEIL /\ lastaddr l mod 8192 = 0 /\
(l <> [] -> exists lb ini, rev l = lb :: ini /\ l = rev ini ++ [lb] /\ lastaddr l = addr lb /\ In lb l).
Proof.
intros l Hl. unfold lastaddr. destruct (rev l) as [|lb ini] eqn:ER.
- ceil; unfold ASAN_CEIL. splits; [lia | lia | reflexivity |]. intros NE. exfalso. apply NE. rewrite <- (rev_involutive l), ER. reflexivity.
- assert (EP : l = rev ini ++ [lb]) by (rewrite <- (rev_involutive l), ER; reflexivity).
assert (IN : In lb l) by (rewrite EP; apply in_app_iff; right; left; reflexivity).
destruct (bfacts lb (Hl lb IN)) as (L1 & L2 & L3 & L4 & L5 & _).
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, addr, kBatchBytes, kHighMemBeg in *. splits; [lia | lia | exact L3 |]. intros _. exists lb, ini. splits; [reflexivity | exact EP | reflexivity | exact IN].
Qed.
Lemma lastaddr_app : forall l1 l2, l2 <> [] -> lastaddr (l1 ++ l2) = lastaddr l2.
Proof.
intros l1 l2 NE. unfold lastaddr. rewrite rev_app_distr. destruct (rev l2) as [|x t] eqn:E.
- exfalso. apply NE. rewrite <- (rev_involutive l2), E. reflexivity.
- reflexivity.
Qed.
Lemma pgl_facts : 0 <= lastaddr L < ASAN_CEIL /\ lastaddr L mod 8192 = 0.
Proof. destruct (last_range L (fun b H => H)) as (A1 & A2 & _). split; [exact A1 | exact A2]. Qed.
(* the quarantine header words the loop writes (the mutex word and the global list's header) *)
Definition HDR (a : Z) : Prop := A_QUAR + 152 <= a < A_QUAR + 192.
(* the words a loop cut may have changed since the entry: Recycle's temp-list header, the quarantine header, and
   the next words of the temp list's batches [P] (the popped ones and the last extracted one) *)
Definition DW (P : list batch) (a : Z) : Prop :=
(sp1 <= a < sp1 + 32) \/ (A_QUAR + 152 <= a < A_QUAR + 156) \/ (A_QUAR + 160 <= a < A_QUAR + 192) \/
(exists b, In b P /\ addr b <= a < addr b + 8).
(* The loop invariant at 0x33ae4: [P1] is the temp list (ex ++ popped), [R] the rest of the kept list. *)
Definition LST (P1 R : list batch) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33ae4) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
getr regs' 2 = w64 sp1 /\ getr regs' 10 = w64 A_QUAR /\ getr regs' 11 = w64 kQuarantineMin /\ getr regs' 12 = getr regs1 12 /\
getr regs' 13 = getr regs1 13 /\ getr regs' 14 = w64 (zlen P1) /\ getr regs' 15 = w64 (lastaddr P1) /\ getr regs' 16 = w64 (zlen R) /\
getr regs' 5 = w64 (firstaddr R) /\ getr regs' 1 = getr regs1 1 /\ (forall r : bv 5, In r YFgl.SREGS -> getr regs' r = getr regs1 r) /\
(forall x : word, ~ DW P1 (bv_unsigned x) -> mem' x = mem1 x) /\
(forall a, 0 <= a < 2 ^ 64 -> apresent H0 mem1 a -> ~ HDR a -> apresent H0 mem' a) /\
let m := mrestrict H0 mem' in
val_mem tfibsegs m (A_QUAR + 152) 4 257 /\
val_mem tfibsegs m (A_QUAR + 160) 8 (zlen R) /\ val_mem tfibsegs m (A_QUAR + 168) 8 (firstaddr R) /\
val_mem tfibsegs m (A_QUAR + 176) 8 (lastaddr L) /\ val_mem tfibsegs m (A_QUAR + 184) 8 (sum_bytes R) /\
(forall i b, nth_error P1 i = Some b -> val_mem tfibsegs m (addr b) 8 (next_addr ly P1 i)) /\
(forall i b, nth_error R i = Some b -> val_mem tfibsegs m (addr b) 8 (next_addr ly R i) /\ val_mem tfibsegs m (addr b + 8) 8 (b_bytes b)) /\
val_mem tfibsegs m (sp1 + 8) 8 (firstaddr P1) /\ val_mem tfibsegs m (sp1 + 24) 8 (sum_bytes P1).
(* Recycle's call of DoRecycle (0x33b54 jal, pc A_DoRecycle): the temp list [P] at sp (a1 = sp), the kept list [R]. *)
Definition ATDR (P R : list batch) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 A_DoRecycle) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
getr regs' 2 = w64 sp1 /\ getr regs' 10 = w64 A_QUAR /\ getr regs' 11 = w64 sp1 /\ getr regs' 12 = getr regs1 12 /\
getr regs' 13 = getr regs1 13 /\ getr regs' 1 = w64 0x33b58 /\ (forall r : bv 5, In r YFgl.SREGS -> getr regs' r = getr regs1 r) /\
(forall x : word, ~ DW P (bv_unsigned x) -> mem' x = mem1 x) /\
(forall a, 0 <= a < 2 ^ 64 -> apresent H0 mem1 a -> ~ HDR a -> apresent H0 mem' a) /\
let m := mrestrict H0 mem' in
(forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m a = Some (Z_to_bv 8 0)) /\
val_mem tfibsegs m (A_QUAR + 160) 8 (zlen R) /\ val_mem tfibsegs m (A_QUAR + 168) 8 (firstaddr R) /\
val_mem tfibsegs m (A_QUAR + 176) 8 (lastaddr R) /\ val_mem tfibsegs m (A_QUAR + 184) 8 (sum_bytes R) /\
(forall i b, nth_error P i = Some b -> val_mem tfibsegs m (addr b) 8 (next_addr ly P i)) /\
(forall i b, nth_error R i = Some b -> val_mem tfibsegs m (addr b) 8 (next_addr ly R i) /\ val_mem tfibsegs m (addr b + 8) 8 (b_bytes b)) /\
val_mem tfibsegs m sp1 8 (zlen P) /\ val_mem tfibsegs m (sp1 + 8) 8 (firstaddr P) /\ val_mem tfibsegs m (sp1 + 16) 8 (lastaddr P) /\
val_mem tfibsegs m (sp1 + 24) 8 (sum_bytes P).
Section e.
(* one iteration: the temp list [P1], the head [b] of the rest, the tail [R'] *)
Variables (P1 R' : list batch) (b : batch) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word).
Hypothesis HL : L = P1 ++ b :: R'.
Let R : list batch := b :: R'.
Hypothesis Q2 : getr regs' 2 = w64 sp1.
Hypothesis Q10 : getr regs' 10 = w64 A_QUAR.
Hypothesis Q11 : getr regs' 11 = w64 kQuarantineMin.
Hypothesis Q12 : getr regs' 12 = getr regs1 12.
Hypothesis Q13 : getr regs' 13 = getr regs1 13.
Hypothesis Q14 : getr regs' 14 = w64 (zlen P1).
Hypothesis Q15 : getr regs' 15 = w64 (lastaddr P1).
Hypothesis Q16 : getr regs' 16 = w64 (zlen R).
Hypothesis Q5 : getr regs' 5 = w64 (firstaddr R).
Hypothesis Q1 : getr regs' 1 = getr regs1 1.
Hypothesis QS : forall r : bv 5, In r YFgl.SREGS -> getr regs' r = getr regs1 r.
Hypothesis FRM : forall x : word, ~ DW P1 (bv_unsigned x) -> mem' x = mem1 x.
Hypothesis PRS : forall a, 0 <= a < 2 ^ 64 -> apresent H0 mem1 a -> ~ HDR a -> apresent H0 mem' a.
Let m := mrestrict H0 mem'.
Hypothesis VQW : val_mem tfibsegs m (A_QUAR + 152) 4 257.
Hypothesis VQS : val_mem tfibsegs m (A_QUAR + 160) 8 (zlen R).
Hypothesis VQF : val_mem tfibsegs m (A_QUAR + 168) 8 (firstaddr R).
Hypothesis VQL : val_mem tfibsegs m (A_QUAR + 176) 8 (lastaddr L).
Hypothesis VQB : val_mem tfibsegs m (A_QUAR + 184) 8 (sum_bytes R).
Hypothesis VPL : forall i b2, nth_error P1 i = Some b2 -> val_mem tfibsegs m (addr b2) 8 (next_addr ly P1 i).
Hypothesis VRL : forall i b2, nth_error R i = Some b2 -> val_mem tfibsegs m (addr b2) 8 (next_addr ly R i) /\ val_mem tfibsegs m (addr b2 + 8) 8 (b_bytes b2).
Hypothesis VT8 : val_mem tfibsegs m (sp1 + 8) 8 (firstaddr P1).
Hypothesis VT24 : val_mem tfibsegs m (sp1 + 24) 8 (sum_bytes P1).
Hypothesis Q4 : getr regs' 4 = w64 TFIB_TP.
Definition pb : Z := addr b.
Definition pnx : Z := firstaddr R'.
Definition pbs : Z := b_bytes b.
Definition pqb : Z := sum_bytes R.
Definition pnr : Z := zlen R.
Definition pnp : Z := zlen P1.
Definition plp : Z := lastaddr P1.
Definition ptby : Z := sum_bytes P1.
Definition ptfi : Z := firstaddr P1.
Definition pgl : Z := lastaddr L.
Lemma InL_b : In b L. Proof. rewrite HL. apply in_app_iff. right. left. reflexivity. Qed.
Lemma InL_P1 : forall b2, In b2 P1 -> In b2 L. Proof. intros b2 Hb2. rewrite HL. apply in_app_iff. left. exact Hb2. Qed.
Lemma InL_R' : forall b2, In b2 R' -> In b2 L. Proof. intros b2 Hb2. rewrite HL. apply in_app_iff. right. right. exact Hb2. Qed.
Lemma PRSs : forall a, sp1 - DRSTACK <= a < sp1 + LFRAME -> apresent H0 mem' a.
Proof.
intros a Ha. pose proof Usp1 as (U1 & U2 & _ & _ & _). apply PRS; [| apply PRS1; exact Ha |].
- clear - Ha U1 U2. numconst. lia.
- unfold HDR. clear - Ha U1. numconst. lia.
Qed.
Lemma b_facts : ly_prim ly <= pb /\ pb + kBatchBytes <= SB + kSpaceSize /\ pb mod 8192 = 0 /\ kHighMemBeg <= pb /\ pb + kBatchBytes <= ASAN_CEIL /\ kBatchBytes <= pbs /\ pbs <= pqb /\ pqb <= sum_bytes L.
Proof.
destruct (bfacts b InL_b) as (L1 & L2 & L3 & L4 & L5 & L7). unfold pb, pbs, pqb.
pose proof (sum_lb R' InL_R') as S1. pose proof (sum_lb P1 InL_P1) as S2.
assert (E : sum_bytes L = sum_bytes P1 + (b_bytes b + sum_bytes R')) by (rewrite HL, sum_bytes_app, sum_bytes_cons; lia).
unfold R. rewrite sum_bytes_cons. splits; try assumption; lia.
Qed.
Lemma nx_facts : 0 <= pnx < ASAN_CEIL /\ pnx mod 8192 = 0.
Proof. destruct (first_range R' InL_R') as (A1 & A2 & _). unfold pnx. split; [exact A1 | exact A2]. Qed.
Lemma lp_facts : 0 <= plp < ASAN_CEIL /\ plp mod 8192 = 0 /\
(pnp <> 0 -> exists lb ini, rev P1 = lb :: ini /\ plp = addr lb /\ ly_prim ly <= plp /\ plp + kBatchBytes <= SB + kSpaceSize /\ (plp + kBatchBytes <= pb \/ pb + kBatchBytes <= plp) /\ In lb P1).
Proof.
destruct (last_range P1 InL_P1) as (A1 & A2 & A3). unfold plp. splits; [lia | lia | exact A2 |]. intros NE.
destruct (A3 ltac:(intros E; apply NE; unfold pnp, zlen; rewrite E; reflexivity)) as (lb & ini & ER & EP & EL & IN).
destruct (bfacts lb (InL_P1 lb IN)) as (L1 & L2 & L3 & L4 & L5 & _).
exists lb, ini. rewrite EL. splits; try reflexivity; try assumption.
pose proof (L_apart (rev ini) lb [] b R' ltac:(rewrite HL, EP, <- app_assoc; reflexivity)) as D. unfold pb. exact D.
Qed.
Lemma tfi_facts : 0 <= ptfi < ASAN_CEIL.
Proof. destruct (first_range P1 InL_P1) as (A1 & _). exact A1. Qed.
Lemma cnt_facts : 1 <= pnr < 2 ^ 40 /\ 0 <= pnp < 2 ^ 40.
Proof. pose proof len_L as LL. unfold pnr, pnp, zlen, R in *. rewrite HL, length_app in LL. cbn [length] in LL |- *. lia. Qed.
Local Notation E1 := (YFgl.E0 regs' pb pnx pbs pqb pnr pnp plp ptby ptfi pgl).
Lemma E1r (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E1 k = getr regs' r.
Proof. intros Hk. exact (YFgl.Er regs' pb pnx pbs pqb pnr pnp plp ptby ptfi pgl k r Hk). Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Lemma chunk_atom1 : forall base a (w : BinNums.N) k0 x, ew E1 k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfibsegs m (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E1 m base (YP09.mkChunk a (CVal w (SOff k0 0))).
Proof.
intros base a w k0 x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Lemma REG1_ok : Forall (region_ok tfibsegs E1 m) YFgl.REG0.
Proof.
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). pose proof SUM as SBD.
pose proof nx_facts as [N1 N2]. pose proof cnt_facts as [C1 C2]. pose proof tfi_facts as F1. pose proof (sum_lb P1 InL_P1) as SP1.
pose proof pgl_facts as (Te & Tf).
assert (EP : sum_bytes L = sum_bytes P1 + sum_bytes R) by (rewrite HL, sum_bytes_app; reflexivity).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kBatchBytes, DRSTACK, LFRAME, kLowMemEnd in U1, U2, B4, B5, B6, N1, F1, Te.
assert (BV2 : bv_unsigned (ew E1 2) = sp1) by (rewrite (E1r 2 2%bv eq_refl), Q2; apply unsigned_lit_small; lia).
assert (SR : 0 <= sum_bytes R') by (apply sum_lb; exact InL_R').
unfold pb, pnx, pbs, pqb, pnr, pnp, plp, ptby, ptfi, pgl in *. unfold R in *. rewrite ?sum_bytes_cons in *.
unfold YFgl.REG0, YFgl.R_STK, YFgl.R_QW, YFgl.R_QG, YFgl.R_B.
apply Forall_cons.
{   reg_intro. rewrite BV2. unfold LFRAME. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply apresent_writable; [unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; lia|]. apply PRSs. unfold DRSTACK, LFRAME in *. lia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom1 _ _ 8 40%nat (firstaddr P1)); [reflexivity | lia | exact VT8 | r8 | cbn; lia].
- apply (chunk_atom1 _ _ 8 39%nat (sum_bytes P1)); [reflexivity | lia | exact VT24 | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split.
{ intros o Ho. apply rw_writable. unfold A_QUAR, A_ALLOCATOR, o_quar in Ho. lia. }
pose proof (proj1 (val_mem4_bytes _ _ _) VQW) as (W0 & W1 & W2 & W3).
change (YO0f.le_byte 257 4 0) with 1 in W0. change (YO0f.le_byte 257 4 1) with 1 in W1. change (YO0f.le_byte 257 4 2) with 0 in W2. change (YO0f.le_byte 257 4 3) with 0 in W3.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | apply (proj2 (val_mem1_byte _ _ _)); rewrite Z.add_0_l; exact W0].
- eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | apply (proj2 (val_mem1_byte _ _ _)); rewrite Z.add_0_l; replace (A_QUAR + 153) with (A_QUAR + 152 + 1) by lia; exact W1].
- apply chunk_ok_zero_mb. intros i Hi. rewrite Z.add_0_l.
assert (C : i = 0 \/ i = 1) by lia. destruct C as [-> | ->]; [replace (A_QUAR + 154 + 0) with (A_QUAR + 152 + 2) by lia; exact W2 | replace (A_QUAR + 154 + 1) with (A_QUAR + 152 + 3) by lia; exact W3]. }
apply Forall_cons.
{   reg_intro. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split; [unfold A_QUAR, A_ALLOCATOR, o_quar; lia|]. split.
{ intros o Ho. apply rw_writable. unfold A_QUAR, A_ALLOCATOR, o_quar in Ho. lia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom1 0 _ 8 36%nat (zlen (b :: R'))); [reflexivity | lia | rewrite Z.add_0_l; exact VQS | r8 | cbn; lia].
- apply (chunk_atom1 0 _ 8 32%nat (addr b)); [reflexivity | lia | rewrite Z.add_0_l; exact VQF | r8 | cbn; lia].
- apply (chunk_atom1 0 _ 8 41%nat (lastaddr L)); [reflexivity | lia | rewrite Z.add_0_l; exact VQL | r8 | cbn; lia].
- apply (chunk_atom1 0 _ 8 35%nat (b_bytes b + sum_bytes R')); [reflexivity | lia | rewrite Z.add_0_l; exact VQB | r8 | cbn; lia]. }
apply Forall_cons; [|apply Forall_nil].
{
destruct (VRL 0%nat b eq_refl) as [V0 V8]. unfold next_addr in V0. cbn [nth_error] in V0.
reg_intro. rewrite YFgl.EqB. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. pose proof (V0 (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. eapply mbyte_high_writable; [unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; lia | exact E]. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom1 _ _ 8 33%nat (firstaddr R')); [reflexivity | lia | | r8 | cbn; lia].
rewrite Z.add_0_r. replace (firstaddr R') with (match nth_error R' 0 with Some b3 => SB + b_self b3 | None => 0 end); [exact V0|].
unfold firstaddr, addr. destruct R'; reflexivity.
- apply (chunk_atom1 _ _ 8 34%nat (b_bytes b)); [reflexivity | lia | exact V8 | r8 | cbn; lia]. }
Qed.
Lemma PAIRS1_ok : pairwise_disjoint E1 YFgl.REG0.
Proof.
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & _).
pose proof LYB as (hP1 & hSB1 & hSB2 & hPA & hK1 & hK2 & hK3 & hK4 & hK5 & G_PS).
apply pairwise_disjoint_of_extents. unfold YFgl.REG0, YFgl.R_STK, YFgl.R_QW, YFgl.R_QG, YFgl.R_B, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite (E1r 2 2%bv eq_refl), Q2, YFgl.EqB. unfold w64. unfold pb in *.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kBatchBytes, DRSTACK, LFRAME, kLowMemEnd, kSpaceSize, kPrimResvSize in *.
rewrite !unsigned_lit_small by lia. unfold A_QUAR, A_ALLOCATOR, o_quar.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
Qed.
Lemma FACTS1_ok : atoms_ok E1 (f_atoms YFgl.FFL).
Proof.
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). pose proof SUM as SBD.
pose proof nx_facts as [N1 N2]. pose proof cnt_facts as [C1 C2]. pose proof tfi_facts as F1. pose proof (sum_lb P1 InL_P1) as SP1. pose proof (sum_lb R' InL_R') as SR.
pose proof lp_facts as (P1a & P2a & _). pose proof pgl_facts as (Te & Tf).
assert (EP : sum_bytes L = sum_bytes P1 + sum_bytes R) by (rewrite HL, sum_bytes_app; reflexivity).
pose proof HAL as SAL.
unfold pb, pnx, pbs, pqb, pnr, pnp, plp, ptby, ptfi, pgl in *. unfold R in *. rewrite ?sum_bytes_cons in *.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kBatchBytes, DRSTACK, LFRAME, kSpaceSize, kPrimResvSize in U1, U2, B4, B5, B6, N1, F1, Te, P1a.
assert (AF : forall k0 Xv lo hi al, ew E1 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E1 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
assert (E2' : ew E1 2 = w64 sp1) by (rewrite (E1r 2 2%bv eq_refl), Q2; reflexivity).
cbn [YFgl.FFL f_atoms atoms_ok]. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, LFRAME.
split. { apply (AF 2%nat sp1); [exact E2'| | | |]. all: clear - CR0 U1 U2 U5 SAL; first [lia | change (2 ^ 4) with 16; exact SAL]. }
split. { apply (AF 32%nat (addr b)); [reflexivity| | | |]. all: clear - CR0 B3 B4 B5; first [lia | change (2 ^ 13) with 8192; exact B3]. }
split. { apply (AF 33%nat (firstaddr R')); [reflexivity| | | |]. all: clear - CR0 N1 N2; first [lia | change (2 ^ 13) with 8192; exact N2]. }
split. { apply (AF 34%nat (b_bytes b)); [reflexivity| | | |]. all: clear - CR0 B6 B7 B8 SBD SP1 SR EP; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 35%nat (b_bytes b + sum_bytes R')); [reflexivity| | | |]. all: clear - CR0 B6 B7 B8 SBD SP1 SR EP; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 36%nat (zlen (b :: R'))); [reflexivity| | | |]. all: clear - C1; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 37%nat (zlen P1)); [reflexivity| | | |]. all: clear - C2; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 38%nat (lastaddr P1)); [reflexivity| | | |]. all: clear - CR0 P1a P2a; first [lia | change (2 ^ 13) with 8192; exact P2a]. }
split. { apply (AF 39%nat (sum_bytes P1)); [reflexivity| | | |]. all: clear - CR0 B6 SBD SP1 SR EP; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 40%nat (firstaddr P1)); [reflexivity| | | |]. all: clear - CR0 F1; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 41%nat (lastaddr L)); [reflexivity| | | |]. all: clear - CR0 Te Tf; first [lia | change (2 ^ 13) with 8192; exact Tf]. }
Qed.
Lemma SEED1_ok : st_ok tfibsegs E1 YFgl.SS0 (restrict H0 (mkst regs' (w64 0x33ae4) mem' (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold YFgl.SS0, YFgl.SR0, sr_set. cbn [bv_eqb]. unfold YFgl.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Q4] | intros XX; discriminate | cbn [sv_denot]; exact Q10] | intros XX; discriminate | cbn [sv_denot]; exact Q11] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |].
+ cbn [sv_denot]. fold E1. rewrite YFgl.EqB, Q5. unfold w64, R, firstaddr, pb. rewrite Zbv_add_unsigned, Z.add_0_r. reflexivity.
+ cbn [sv_denot]. fold E1. rewrite YFgl.EqNP, Q14. unfold w64, pnp. rewrite Zbv_add_unsigned, Z.add_0_r. reflexivity.
+ cbn [sv_denot]. fold E1. rewrite YFgl.EqLP, Q15. unfold w64, plp. rewrite Zbv_add_unsigned, Z.add_0_r. reflexivity.
+ cbn [sv_denot]. fold E1. rewrite YFgl.EqNR, Q16. unfold w64, pnr, R. rewrite Zbv_add_unsigned, Z.add_0_r. reflexivity.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG1_ok.
- exact PAIRS1_ok.
- split; [exact FACTS1_ok | split; exact I].
Qed.
Theorem FHL_ok : YFgl.free_hyps W ly regs' mem' pb pnx pbs pqb pnr pnp plp ptby ptfi pgl.
Proof.
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). pose proof SUM as SBD.
pose proof nx_facts as [N1 N2]. pose proof cnt_facts as [C1 C2]. pose proof tfi_facts as F1. pose proof (sum_lb P1 InL_P1) as SP1. pose proof (sum_lb R' InL_R') as SR.
pose proof lp_facts as (P1a & P2a & P3a). pose proof pgl_facts as (Te & Tf).
assert (EP : sum_bytes L = sum_bytes P1 + sum_bytes R) by (rewrite HL, sum_bytes_app; reflexivity). unfold R in EP. rewrite sum_bytes_cons in EP.
constructor.
- exact LY.
- exact Q4.
- rewrite Q1. exact Hra.
- rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. split; [exact U3 | exact U4].
- rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. exact HAL.
- rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. exact PRSs.
- splits; [exact B1 | exact B2 | exact B3].
- exact nx_facts.
- exact cnt_facts.
- unfold pbs, pqb, ptby, R in *. rewrite sum_bytes_cons in *. clear - B6 B7 B8 SBD SP1 SR EP. unfold kBatchBytes in *. splits; lia.
- unfold pgl. split; [exact Te | exact Tf].
- exact F1.
- splits; [lia | lia | exact P2a |]. intros NE. destruct (P3a NE) as (lb & ini & ER & EL & L1 & L2 & L3 & IN). splits; [exact L1 | exact L2 | exact L3 |].
intros a Ha. assert (EP1 : P1 = rev ini ++ [lb]) by (rewrite <- (rev_involutive P1), ER; reflexivity).
pose proof (VPL (length (rev ini)) lb ltac:(rewrite EP1; apply YFer.nth_error_last)) as V. rewrite <- EL in V.
pose proof (V (Z.to_nat (a - plp)) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. replace (plp + (a - plp)) with a in E by lia.
destruct (bfacts lb (InL_P1 lb IN)) as (_ & _ & _ & L4 & L5 & _). rewrite <- EL in L4, L5.
eapply mbyte_high_apresent; [| exact E]. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL, kBatchBytes in *. lia.
- exact SEED1_ok.
Qed.
Local Notation WINL := (YFgl.WIN regs' pb pnp plp).
Lemma ND3 : (forall x, In x P1 -> b_self x <> b_self b) /\ (forall y, In y R' -> b_self y <> b_self b) /\
(forall x y, In x P1 -> In y R' -> b_self x <> b_self y) /\ List.NoDup (map b_self P1) /\ List.NoDup (map b_self R').
Proof.
pose proof ND as ND0. rewrite HL, map_app in ND0. cbn [map] in ND0. apply NoDup_app_iff in ND0 as (N1 & N2 & N3). inversion N2 as [|y l N4 N5]; subst.
splits.
- intros x Hx E. apply (N3 (b_self x)); [apply in_map; exact Hx | left; symmetry; exact E].
- intros y Hy E. apply N4. rewrite <- E. apply in_map. exact Hy.
- intros x y Hx Hy E. apply (N3 (b_self x)); [apply in_map; exact Hx | right; rewrite E; apply in_map; exact Hy].
- exact N1.
- exact N5.
Qed.
Lemma NW_batch : forall b2 k, In b2 L -> b_self b2 <> b_self b -> (forall lb ini, rev P1 = lb :: ini -> b_self b2 <> b_self lb) ->
0 <= k < kBatchBytes -> ~ WINL (addr b2 + k).
Proof.
intros b2 k Hb2 NEb NEl Hk. pose proof LYB as (hP1 & hSB1 & hSB2 & hPA & hK1 & hK2 & hK3 & hK4 & hK5 & G_PS). pose proof lp_facts as (_ & _ & P3a).
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof b_facts as (B1 & B2 & B3 & _).
destruct (bfacts b2 Hb2) as (L1 & L2 & L3 & L4 & L5 & _).
unfold YFgl.WIN, YFgl.WINF, YFgl.WINA. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia.
intros [Y|[[Y|[Y|Y]]|[NE Y]]].
- unfold DRSTACK, LFRAME, kBatchBytes in *. lia.
- clear - Y L4 Hk. numconst. lia.
- clear - Y L4 Hk. numconst. lia.
- assert (D : addr b2 + kBatchBytes <= pb \/ pb + kBatchBytes <= addr b2) by (unfold kBatchBytes; apply apart8192; [exact L3 | exact B3 | unfold pb, addr; lia]).
unfold kBatchBytes in *. lia.
- destruct (P3a NE) as (lb & ini & ER & EL & _ & _ & _ & IN). rewrite EL in Y.
destruct (bfacts lb (InL_P1 lb IN)) as (_ & _ & M3 & _).
assert (D : addr b2 + kBatchBytes <= addr lb \/ addr lb + kBatchBytes <= addr b2)
  by (unfold kBatchBytes; apply apart8192; [exact L3 | exact M3 | pose proof (NEl lb ini ER); unfold addr; lia]).
unfold kBatchBytes in *. lia.
Qed.
Lemma WINL_dec : forall a, WINL a \/ ~ WINL a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
unfold YFgl.WIN, YFgl.WINF, YFgl.WINA. set (s := bv_unsigned (getr regs' 2)).
destruct (EM s (s + 32)) as [C|C0]; [left; left; exact C|].
destruct (EM (A_QUAR + 152) (A_QUAR + 156)) as [C|C1]; [left; right; left; left; exact C|].
destruct (EM (A_QUAR + 160) (A_QUAR + 192)) as [C|C2]; [left; right; left; right; left; exact C|].
destruct (EM pb (pb + 8)) as [C|C3]; [left; right; left; right; right; exact C|].
destruct (Z.eq_dec pnp 0) as [Z0|NZ].
- right. intros [X0|[[X1|[X2|X3]]|[X5 _]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (X5 Z0)].
- destruct (EM plp (plp + 8)) as [C|C4]; [left; right; right; split; [exact NZ | exact C]|].
right. intros [X0|[[X1|[X2|X3]]|[_ X5]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (C4 X5)].
Qed.
Lemma keep : forall mem'' a (n : nat) v, (forall x : word, ~ WINL (bv_unsigned x) -> mem'' x = mem' x) ->
(forall i, 0 <= i < Z.of_nat n -> ~ WINL (a + i) /\ 0 <= a + i < 2 ^ 64) ->
val_mem tfibsegs m a n v -> val_mem tfibsegs (mrestrict H0 mem'') a n v.
Proof.
intros mem'' a n v HM Hn Hv. eapply val_mem_frame; [|exact Hv]. intros k Hk. destruct (Hn (Z.of_nat k) ltac:(lia)) as [N1 N2].
apply HM. rewrite unsigned_lit_small by exact N2. exact N1.
Qed.
Lemma DW_mono : forall a, DW P1 a -> DW (P1 ++ [b]) a.
Proof. intros a [Y|[Y|[Y|(b2 & Hb2 & Y)]]]; unfold DW; [tauto | tauto | tauto |]. do 3 right. exists b2. split; [apply in_app_iff; left; exact Hb2 | exact Y]. Qed.
Lemma WINL_DW : forall a, WINL a -> DW (P1 ++ [b]) a.
Proof.
intros a Hw. pose proof lp_facts as (_ & _ & P3a). pose proof Usp1 as (U1 & U2 & U3 & U4 & U5).
unfold YFgl.WIN, YFgl.WINF, YFgl.WINA in Hw. rewrite Q2 in Hw. unfold w64 in Hw. rewrite unsigned_lit_small in Hw by lia.
unfold DW. destruct Hw as [Y|[[Y|[Y|Y]]|[NE Y]]].
- left. exact Y.
- right; left. exact Y.
- right; right; left. exact Y.
- do 3 right. exists b. split; [apply in_app_iff; right; left; reflexivity | unfold pb in Y; exact Y].
- destruct (P3a NE) as (lb & ini & ER & EL & _ & _ & _ & IN). do 3 right. exists lb. split; [apply in_app_iff; left; exact IN | rewrite <- EL; exact Y].
Qed.
(* presence: the shell gives it for the written words above kHighMemBeg; the rest is kept by the frame *)
Lemma PRS_step : forall mem2, (forall x : word, ~ WINL (bv_unsigned x) -> mem2 x = mem' x) ->
(forall a, WINL a -> kHighMemBeg <= a -> apresent H0 mem2 a) ->
forall a, 0 <= a < 2 ^ 64 -> apresent H0 mem1 a -> ~ HDR a -> apresent H0 mem2 a.
Proof.
intros mem2 MQ PRES2 a Ha HP HH. destruct (WINL_dec a) as [Hw|Hw].
- apply PRES2; [exact Hw|].
destruct (YFgl.WIN_cases W ly regs' mem' pb pnx pbs pqb pnr pnp plp ptby ptfi pgl FHL_ok a Hw) as [C|C]; [exfalso; apply HH; exact C | exact C].
- apply (apresent_same H0 mem'); [apply MQ; rewrite unsigned_lit_small by exact Ha; exact Hw | exact (PRS a Ha HP HH)].
Qed.
Lemma zlen_snoc : zlen (P1 ++ [b]) = pnp + 1.
Proof. unfold pnp, zlen. rewrite length_app. cbn [length]. lia. Qed.
Lemma lastaddr_snoc : lastaddr (P1 ++ [b]) = pb.
Proof. unfold lastaddr. rewrite YFer.rev_last. reflexivity. Qed.
Lemma firstaddr_snoc : firstaddr (P1 ++ [b]) = YFgl.TFIn pb pnp ptfi.
Proof.
unfold YFgl.TFIn, pnp, ptfi, zlen, firstaddr. destruct P1 as [|x t]; cbn [app length Z.of_nat]; [reflexivity|].
destruct (Z.eqb_spec (Z.pos (Pos.of_succ_nat (length t))) 0); [lia | reflexivity].
Qed.
Lemma sum_snoc : sum_bytes (P1 ++ [b]) = ptby + pbs.
Proof. unfold ptby, pbs. rewrite sum_bytes_app, sum_bytes_cons, sum_bytes_nil. lia. Qed.
Lemma zlen_R' : zlen R' = pnr - 1.
Proof. unfold pnr, zlen, R. cbn [length]. lia. Qed.
Lemma sum_R' : sum_bytes R' = pqb - pbs.
Proof. unfold pqb, pbs, R. rewrite sum_bytes_cons. lia. Qed.
Lemma R'_ne : kQuarantineMin < pqb - pbs -> R' <> [].
Proof. rewrite <- sum_R'. intros H E. rewrite E in H. cbn in H. unfold kQuarantineMin in H. lia. Qed.
Lemma GLn_cont : R' <> [] -> YFgl.GLn pnx pgl = pgl.
Proof.
intros NE. unfold YFgl.GLn. destruct (Z.eqb_spec pnx 0) as [E|_]; [|reflexivity]. exfalso.
destruct (first_range R' InL_R') as (_ & _ & A3). unfold pnx in E. pose proof (A3 NE). unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma GLn_exit : YFgl.GLn pnx pgl = lastaddr R'.
Proof.
unfold YFgl.GLn, pgl, pnx. destruct (Z.eqb_spec (firstaddr R') 0) as [E|NE].
- destruct (first_range R' InL_R') as (_ & _ & A3).
assert (CASES : R' = [] \/ R' <> []) by (clear; destruct R'; [left; reflexivity | right; discriminate]).
destruct CASES as [E0|NE0]; [rewrite E0; reflexivity|]. exfalso. pose proof (A3 NE0). unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. lia.
- assert (RN : R' <> []) by (intros E; apply NE; rewrite E; reflexivity).
rewrite HL. replace (P1 ++ b :: R') with ((P1 ++ [b]) ++ R') by (rewrite <- app_assoc; reflexivity). apply lastaddr_app. exact RN.
Qed.
(* the next words of the temp list after the pop (the popped batch's is 0, the old last's points at it) *)
Lemma VPL_next : forall mem2, (forall x : word, ~ WINL (bv_unsigned x) -> mem2 x = mem' x) ->
val_mem tfibsegs (mrestrict H0 mem2) pb 8 0 -> (pnp <> 0 -> val_mem tfibsegs (mrestrict H0 mem2) plp 8 pb) ->
forall i b2, nth_error (P1 ++ [b]) i = Some b2 -> val_mem tfibsegs (mrestrict H0 mem2) (addr b2) 8 (next_addr ly (P1 ++ [b]) i).
Proof.
intros mem2 MQ Cb Clp i b2 Hi. pose proof ND3 as (D1 & D2 & D3 & D4 & D5). destruct (Nat.lt_ge_cases i (length P1)) as [LT|GE].
- rewrite nth_error_app1 in Hi by exact LT. pose proof (nth_error_In _ _ Hi) as IN1.
destruct (Nat.eq_dec (S i) (length P1)) as [LAST|NL].
+
assert (NE0 : pnp <> 0) by (unfold pnp, zlen; lia). pose proof lp_facts as (_ & _ & P3a). destruct (P3a NE0) as (lb & ini & ER & EL & _ & _ & _ & _).
assert (EP1 : P1 = rev ini ++ [lb]) by (rewrite <- (rev_involutive P1), ER; reflexivity).
assert (Eb2 : b2 = lb). { rewrite EP1 in Hi. rewrite nth_error_app2 in Hi by (rewrite EP1, length_app in LAST; cbn [length] in LAST; lia).
replace (i - length (rev ini))%nat with 0%nat in Hi by (rewrite EP1, length_app in LAST; cbn [length] in LAST; lia). cbn in Hi. congruence. }
subst b2. unfold next_addr. rewrite nth_error_app2 by lia. rewrite <- LAST, Nat.sub_diag. cbn [nth_error]. fold (addr b). fold pb. rewrite <- EL. exact (Clp NE0).
+
unfold next_addr. rewrite nth_error_app1 by lia. pose proof (VPL i b2 Hi) as V. unfold next_addr in V.
destruct (bfacts b2 (InL_P1 _ IN1)) as (_ & _ & _ & L4 & L5 & _).
apply (keep _ _ _ _ MQ); [| exact V]. intros j Hj. split; [apply (NW_batch b2 j (InL_P1 _ IN1) (D1 _ IN1)); [|unfold kBatchBytes; lia] | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia].
intros lb ini ER E. assert (EP1 : P1 = rev ini ++ [lb]) by (rewrite <- (rev_involutive P1), ER; reflexivity).
pose proof D4 as ND'. rewrite EP1, map_app in ND'. cbn [map] in ND'. apply NoDup_app_iff in ND' as (_ & _ & ND'). apply (ND' (b_self b2)); [|left; symmetry; exact E].
apply in_map. rewrite EP1 in Hi. rewrite nth_error_app1 in Hi by (rewrite EP1, length_app in NL, LT; cbn [length] in NL, LT; lia). eapply nth_error_In. exact Hi.
-
rewrite nth_error_app2 in Hi by exact GE. destruct (i - length P1)%nat as [|k] eqn:EK; [|cbn in Hi; destruct k; discriminate]. cbn in Hi. injection Hi as <-.
unfold next_addr. rewrite nth_error_app2 by lia. replace (S i - length P1)%nat with 1%nat by lia. cbn [nth_error]. exact Cb.
Qed.
(* the cells of the rest of the kept list are not written *)
Lemma VRL_next : forall mem2, (forall x : word, ~ WINL (bv_unsigned x) -> mem2 x = mem' x) ->
forall i b2, nth_error R' i = Some b2 ->
val_mem tfibsegs (mrestrict H0 mem2) (addr b2) 8 (next_addr ly R' i) /\ val_mem tfibsegs (mrestrict H0 mem2) (addr b2 + 8) 8 (b_bytes b2).
Proof.
intros mem2 MQ i b2 Hi. pose proof ND3 as (D1 & D2 & D3 & D4 & D5).
pose proof (nth_error_In _ _ Hi) as IN2. destruct (VRL (S i) b2 Hi) as [V1 V2].
assert (EN : next_addr ly R (S i) = next_addr ly R' i) by reflexivity. rewrite EN in V1.
destruct (bfacts b2 (InL_R' _ IN2)) as (_ & _ & _ & L4 & L5 & _).
assert (NWb : forall j, 0 <= j < 16 -> ~ WINL (addr b2 + j) /\ 0 <= addr b2 + j < 2 ^ 64).
{ intros j Hj. split; [apply (NW_batch b2 j (InL_R' _ IN2) (D2 _ IN2)); [|unfold kBatchBytes; lia] | ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia].
intros lb ini ER E. apply (D3 lb b2); [rewrite <- (rev_involutive P1), ER; cbn; apply in_app_iff; right; left; reflexivity | exact IN2 | symmetry; exact E]. }
split; [apply (keep _ _ _ _ MQ); [intros j Hj; apply NWb; lia | exact V1] | apply (keep _ _ _ _ MQ); [intros j Hj; replace (addr b2 + 8 + j) with (addr b2 + (8 + j)) by lia; apply NWb; lia | exact V2]].
Qed.
Lemma LST_cont : forall W' c', YFgl.at_CONT W regs' mem' md pb pnx pbs pqb pnr pnp plp ptby ptfi pgl W' c' -> LST (P1 ++ [b]) R' W' c'.
Proof.
intros W' c' (-> & HLT & regs2 & mem2 & mat2 & -> & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R5 & R1 & RS & MQ & PRES2 & CELLS).
cbv zeta in CELLS. destruct CELLS as (C152 & C153 & C154 & C160 & C168 & C176 & C184 & Cb & Clp & Ct8 & Ct24).
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5). pose proof (R'_ne HLT) as RNE.
split; [reflexivity|]. exists regs2, mem2, mat2. split; [reflexivity|].
split; [rewrite R2; exact Q2|]. split; [exact R10|]. split; [exact R11|]. split; [rewrite R12; exact Q12|]. split; [rewrite R13; exact Q13|].
split; [rewrite R14, zlen_snoc; reflexivity|]. split; [rewrite R15, lastaddr_snoc; reflexivity|]. split; [rewrite R16, zlen_R'; reflexivity|].
split; [rewrite R5; reflexivity|]. split; [rewrite R1; exact Q1|]. split; [intros r Hr; rewrite (RS r Hr); apply QS; exact Hr|].
split. { intros x Hx. rewrite (MQ x ltac:(intros Hw; exact (Hx (WINL_DW _ Hw)))). apply FRM. intros HD. exact (Hx (DW_mono _ HD)). }
split. { exact (PRS_step mem2 MQ PRES2). }
cbv zeta.
split. { apply (proj2 (val_mem4_bytes _ _ _)). change (YO0f.le_byte 257 4 0) with 1. change (YO0f.le_byte 257 4 1) with 1. change (YO0f.le_byte 257 4 2) with 0. change (YO0f.le_byte 257 4 3) with 0.
pose proof (proj1 (val_mem1_byte _ _ _) C152) as E0. pose proof (proj1 (val_mem1_byte _ _ _) C153) as E1'.
splits; [exact E0 | replace (A_QUAR + 152 + 1) with (A_QUAR + 153) by lia; exact E1' | apply C154; lia | apply C154; lia]. }
split; [rewrite zlen_R'; exact C160|]. split; [exact C168|]. split; [rewrite (GLn_cont RNE) in C176; exact C176|]. split; [rewrite sum_R'; exact C184|].
split; [exact (VPL_next mem2 MQ Cb Clp)|].
split; [exact (VRL_next mem2 MQ)|].
split; [rewrite firstaddr_snoc; rewrite Q2 in Ct8; unfold w64 in Ct8; rewrite unsigned_lit_small in Ct8 by lia; exact Ct8|].
rewrite sum_snoc; rewrite Q2 in Ct24; unfold w64 in Ct24; rewrite unsigned_lit_small in Ct24 by lia; exact Ct24.
Qed.
Lemma LST_exit : forall W' c', YFgl.at_EXIT W regs' mem' md pb pnx pbs pqb pnr pnp plp ptby ptfi pgl W' c' -> ATDR (P1 ++ [b]) R' W' c'.
Proof.
intros W' c' (-> & HLE & regs2 & mem2 & mat2 & -> & R2 & R10 & R11 & R12 & R13 & R1 & RS & MQ & PRES2 & CELLS).
cbv zeta in CELLS. destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cb & Clp & Ct0 & Ct8 & Ct16 & Ct24).
pose proof Usp1 as (U1 & U2 & U3 & U4 & U5).
split; [reflexivity|]. exists regs2, mem2, mat2. split; [reflexivity|].
split; [rewrite R2; exact Q2|]. split; [exact R10|]. split; [rewrite R11; exact Q2|]. split; [rewrite R12; exact Q12|]. split; [rewrite R13; exact Q13|].
split; [exact R1|]. split; [intros r Hr; rewrite (RS r Hr); apply QS; exact Hr|].
split. { intros x Hx. rewrite (MQ x ltac:(intros Hw; exact (Hx (WINL_DW _ Hw)))). apply FRM. intros HD. exact (Hx (DW_mono _ HD)). }
split. { exact (PRS_step mem2 MQ PRES2). }
cbv zeta.
split; [exact C152|].
split; [rewrite zlen_R'; exact C160|]. split; [exact C168|]. split; [rewrite <- GLn_exit; exact C176|]. split; [rewrite sum_R'; exact C184|].
split; [exact (VPL_next mem2 MQ Cb Clp)|].
split; [exact (VRL_next mem2 MQ)|].
rewrite Q2 in Ct0, Ct8, Ct16, Ct24. unfold w64 in Ct0, Ct8, Ct16, Ct24. rewrite unsigned_lit_small in Ct0, Ct8, Ct16, Ct24 by lia.
split; [rewrite zlen_snoc; exact Ct0|]. split; [rewrite firstaddr_snoc; exact Ct8|]. split; [rewrite lastaddr_snoc; exact Ct16|]. rewrite sum_snoc; exact Ct24.
Qed.
(* one pop iteration from the loop head (YFh0.segL, unchanged) *)
Theorem ITER_step :
SRr tfibsegs W (mkCfg (mkst regs' (w64 0x33ae4) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
(fun W' c' => if kQuarantineMin <? pqb - pbs then LST (P1 ++ [b]) R' W' c' else ATDR (P1 ++ [b]) R' W' c').
Proof.
eapply SRr_mono; [exact (YFh0.segL W ly regs' mem' md pb pnx pbs pqb pnr pnp plp ptby ptfi pgl mat FHL_ok)|].
intros W' c' _ HP. unfold YFgl.postL in HP. destruct (kQuarantineMin <? pqb - pbs); [exact (LST_cont W' c' HP) | exact (LST_exit W' c' HP)].
Qed.
End e.
(* The loop: from a cut with the temp list [P1] and the rest [R] of the kept list, to Recycle's call of DoRecycle with
   the temp list [P1 ++ the batches pop_batches takes]. *)
Theorem LOOP : forall R P1 fuel W' c',
LST P1 R W' c' -> L = P1 ++ R -> kQuarantineMin < sum_bytes R -> (length R < fuel)%nat ->
SRr tfibsegs W' c' (fun W'' c'' => let gp := pop_batches fuel (mkQC R (sum_bytes R)) (rev P1) in ATDR (snd gp) (qc_list (fst gp)) W'' c'').
Proof.
induction R as [|b R' IH]; intros P1 fuel W' c' HLST HLR HGT Hfuel.
- exfalso. cbn in HGT. unfold kQuarantineMin in HGT. lia.
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. rewrite (pop_step f b R' _ _ HGT).
destruct HLST as (-> & regs' & mem' & mat & -> & Q2 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q5 & Q1 & QS & FRM & PRS & CELLS).
cbv zeta in CELLS. destruct CELLS as (VQW & VQS & VQF & VQL & VQB & VPL & VRL & VT8 & VT24).
assert (Q4 : getr regs' 4 = w64 TFIB_TP) by (rewrite (QS 4%bv ltac:(cbn; tauto)); exact Htp).
pose proof (ITER_step P1 R' b regs' mem' mat) as STEP.
repeat match type of STEP with ?A -> _ => specialize (STEP ltac:(assumption)) end.
unfold pqb, pbs in STEP. rewrite sum_bytes_cons in STEP |- *. replace (b_bytes b + sum_bytes R' - b_bytes b) with (sum_bytes R') in STEP |- * by lia.
destruct (Z.ltb_spec kQuarantineMin (sum_bytes R')) as [GT|LE].
+
eapply SRr_bind; [exact STEP|]. intros W2 c2 _ HL2. cbn beta in HL2.
pose proof (IH (P1 ++ [b]) f W2 c2 HL2 ltac:(rewrite <- app_assoc; exact HLR) GT ltac:(cbn in Hfuel; lia)) as K.
rewrite YFer.rev_last in K. exact K.
+
rewrite (pop_stop f R' _ _ LE). cbn [fst snd qc_list rev]. rewrite rev_involutive. exact STEP.
Qed.
Section entry.
Variable mat1 : list word.
(* the loop head's registers (DMseg_rj.at_RJL: a4 / a5 = the temp list's count / last, a6 / t0 = the kept list's
   count / first) and the cells at the entry *)
Hypothesis E10 : getr regs1 10 = w64 A_QUAR.
Hypothesis E11 : getr regs1 11 = w64 kQuarantineMin.
Hypothesis E14 : getr regs1 14 = w64 (zlen ex).
Hypothesis E15 : getr regs1 15 = w64 (lastaddr ex).
Hypothesis E16 : getr regs1 16 = w64 (zlen Lk).
Hypothesis E5 : getr regs1 5 = w64 (firstaddr Lk).
Let m1 := mrestrict H0 mem1.
Hypothesis CQW : val_mem tfibsegs m1 (A_QUAR + 152) 4 257.
Hypothesis CQS : val_mem tfibsegs m1 (A_QUAR + 160) 8 (zlen Lk).
Hypothesis CQF : val_mem tfibsegs m1 (A_QUAR + 168) 8 (firstaddr Lk).
Hypothesis CQL : val_mem tfibsegs m1 (A_QUAR + 176) 8 (lastaddr Lk).
Hypothesis CQB : val_mem tfibsegs m1 (A_QUAR + 184) 8 (sum_bytes Lk).
Hypothesis CEX : forall i b, nth_error ex i = Some b -> val_mem tfibsegs m1 (addr b) 8 (next_addr ly ex i).
Hypothesis CLK : forall i b, nth_error Lk i = Some b -> val_mem tfibsegs m1 (addr b) 8 (next_addr ly Lk i) /\ val_mem tfibsegs m1 (addr b + 8) 8 (b_bytes b).
Hypothesis CT8 : val_mem tfibsegs m1 (sp1 + 8) 8 (firstaddr ex).
Hypothesis CT24 : val_mem tfibsegs m1 (sp1 + 24) 8 (sum_bytes ex).
Lemma LST_entry : Lk <> [] -> LST ex Lk W (mkCfg (mkst regs1 (w64 0x33ae4) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat1 md)).
Proof.
intros NE. split; [reflexivity|]. exists regs1, mem1, mat1. split; [reflexivity|].
split; [unfold sp1, w64; symmetry; apply Z_to_bv_bv_unsigned|].
split; [exact E10|]. split; [exact E11|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact E14|]. split; [exact E15|]. split; [exact E16|]. split; [exact E5|]. split; [reflexivity|].
split; [intros r _; reflexivity|]. split; [intros x _; reflexivity|]. split; [intros a _ HP _; exact HP|].
cbv zeta. fold m1.
split; [exact CQW|]. split; [exact CQS|]. split; [exact CQF|]. split; [unfold L; rewrite lastaddr_app by exact NE; exact CQL|].
split; [exact CQB|]. split; [exact CEX|]. split; [exact CLK|]. split; [exact CT8 | exact CT24].
Qed.
Theorem deq_ok : forall gm, qc_list gm = Lk -> qc_bytes gm = sum_bytes Lk -> kQuarantineMin < qc_bytes gm ->
SRr tfibsegs W (mkCfg (mkst regs1 (w64 0x33ae4) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => exists g' popped, pop_batches (S (length (qc_list gm))) gm [] = (g', popped) /\ ATDR (ex ++ popped) (qc_list g') W' c').
Proof.
intros gm EL EB GT. destruct gm as [l s]. cbn [qc_list qc_bytes] in EL, EB, GT |- *. subst l s.
assert (NE : Lk <> []) by (intros E; rewrite E in GT; cbn in GT; unfold kQuarantineMin in GT; lia).
eapply SRr_mono; [exact (LOOP Lk ex (S (length Lk)) W _ (LST_entry NE) eq_refl GT ltac:(lia))|].
intros W' c' _ HP. cbv zeta in HP. rewrite pop_acc in HP. cbn [fst snd] in HP. rewrite rev_involutive in HP.
exists (fst (pop_batches (S (length Lk)) (mkQC Lk (sum_bytes Lk)) [])), (snd (pop_batches (S (length Lk)) (mkQC Lk (sum_bytes Lk)) [])).
split; [apply surjective_pairing | exact HP].
Qed.
End entry.
End d.

(* The dequeue loop's pre at 0x33ae4 after MergeBatches: the batch facts on [ex ++ Lk], Recycle's frame, the loop
   head's registers and the cells of the quarantine header, the temp list [ex] and the kept list [Lk]. *)
Record deq_pre (W : world tfibsegs) (ly : alayout) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (ex Lk : list batch) : Prop := DeqPre {
dq_LY : layout_ok ly;
dq_BF : forall b, In b (L ex Lk) ->
  ly_prim ly <= addr ly b /\ addr ly b + kBatchBytes <= ly_space ly + kSpaceSize /\ addr ly b mod 8192 = 0 /\ kBatchBytes <= b_bytes b;
dq_ND : List.NoDup (map b_self (L ex Lk));
dq_SUM : sum_bytes (L ex Lk) <= 2 ^ 31;
dq_Hsp : ly_stk_lo ly + DRSTACK <= sp1 regs1 /\ sp1 regs1 + LFRAME <= ly_stk_hi ly;
dq_HAL : sp1 regs1 mod 16 = 0;
dq_PRS : forall a, sp1 regs1 - DRSTACK <= a < sp1 regs1 + LFRAME -> apresent (w_H W) mem1 a;
dq_Htp : getr regs1 4 = w64 TFIB_TP;
dq_Hra : YK0s.ret_ok (getr regs1 1);
dq_E10 : getr regs1 10 = w64 A_QUAR;
dq_E11 : getr regs1 11 = w64 kQuarantineMin;
dq_E14 : getr regs1 14 = w64 (zlen ex);
dq_E15 : getr regs1 15 = w64 (lastaddr ly ex);
dq_E16 : getr regs1 16 = w64 (zlen Lk);
dq_E5 : getr regs1 5 = w64 (firstaddr ly Lk);
dq_CQW : val_mem tfibsegs (mrestrict (w_H W) mem1) (A_QUAR + 152) 4 257;
dq_CQS : val_mem tfibsegs (mrestrict (w_H W) mem1) (A_QUAR + 160) 8 (zlen Lk);
dq_CQF : val_mem tfibsegs (mrestrict (w_H W) mem1) (A_QUAR + 168) 8 (firstaddr ly Lk);
dq_CQL : val_mem tfibsegs (mrestrict (w_H W) mem1) (A_QUAR + 176) 8 (lastaddr ly Lk);
dq_CQB : val_mem tfibsegs (mrestrict (w_H W) mem1) (A_QUAR + 184) 8 (sum_bytes Lk);
dq_CEX : forall i b, nth_error ex i = Some b -> val_mem tfibsegs (mrestrict (w_H W) mem1) (addr ly b) 8 (next_addr ly ex i);
dq_CLK : forall i b, nth_error Lk i = Some b ->
  val_mem tfibsegs (mrestrict (w_H W) mem1) (addr ly b) 8 (next_addr ly Lk i) /\ val_mem tfibsegs (mrestrict (w_H W) mem1) (addr ly b + 8) 8 (b_bytes b);
dq_CT8 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp1 regs1 + 8) 8 (firstaddr ly ex);
dq_CT24 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp1 regs1 + 24) 8 (sum_bytes ex)
}.

(* The dequeue loop after MergeBatches: from the loop head 0x33ae4 (kept quarantine [gm], extracted batches [ex] on
   the temp list) to Recycle's call of DoRecycle with the kept quarantine [g'] and the temp list [ex ++ popped], where
   (g', popped) = pop_batches (S |gm|) gm [] as in drain_body_cf / DMiface.drain_recyc. *)
Theorem tfib_deq_ok : forall W ly md regs1 mem1 mat1 ex Lk gm,
deq_pre W ly regs1 mem1 ex Lk -> qc_list gm = Lk -> qc_bytes gm = sum_bytes Lk -> kQuarantineMin < qc_bytes gm ->
SRr tfibsegs W (mkCfg (mkst regs1 (w64 0x33ae4) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => exists g' popped, pop_batches (S (length (qc_list gm))) gm [] = (g', popped) /\ ATDR W ly md regs1 mem1 (ex ++ popped) (qc_list g') W' c').
Proof.
intros W ly md regs1 mem1 mat1 ex Lk gm PRE EL EB GT. destruct PRE.
eapply deq_ok; eassumption.
Qed.
End c.

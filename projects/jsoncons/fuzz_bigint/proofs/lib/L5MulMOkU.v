(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5Core L5CoreSpecsU L5Words L5ReduceU L5ReduceGU L5MulMU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsOps.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5MULMOKU.
Import L5CSU. Import L5W. Import L5MULMU.

Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma r1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq; reflexivity. Qed.
Lemma r2 : (2%bv : bv 5) = reg 2. Proof. apply bv_eq; reflexivity. Qed.
Lemma r4 : (4%bv : bv 5) = reg 4. Proof. apply bv_eq; reflexivity. Qed.
Lemma r10 : (10%bv : bv 5) = reg 10. Proof. apply bv_eq; reflexivity. Qed.
Lemma r11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Definition cs_pass : list nat := [3; 4]%nat.
Lemma pass_of_preserved R R' : regs_preserved R R' -> forall i, In i cs_pass -> getr R' (reg i) = getr R (reg i).
Proof.
  intros RP i Hi. apply RP. unfold callee_saved_idx. cbn in Hi.
  repeat (destruct Hi as [<-|Hi]; [cbn; tauto|]). destruct Hi.
Qed.
Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index (R R' : bvmap 5 word) : (forall i, In i cs_all -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof.
  intros K x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply K.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
Lemma preserved_of_ret (R R' : bvmap 5 word) sp o :
  getr R (reg 2) = Z_to_bv 64 sp -> at_ret R R' sp o -> (forall i, In i cs_pass -> getr R' (reg i) = getr R (reg i)) ->
  regs_preserved R R'.
Proof.
  intros H2 (T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & _) K. apply preserved_by_index. intros i Hi. cbn in Hi.
  repeat (destruct Hi as [<-|Hi]; [first [rewrite T2, H2; reflexivity | assumption | apply K; cbn; tauto] |]). destruct Hi.
Qed.

(* [comment removed for export] *)
Lemma kept_not_scratch L LB sp scr W a :
  L5C.kept L LB sp scr W a -> (hl_sptop L - 8388608) + scr <= sp -> hl_img_hi L <= (hl_sptop L - 8388608) ->
  (forall b, In b LB -> fst b + snd b <= (hl_sptop L - 8388608)) -> ~ (sp - scr <= a < sp).
Proof.
  intros (Ha & CA & NE & OW) Hs Hi HLB. destruct CA as [(b & Hb & Hr)|[[S1 S2]|[IM _]]].
  - pose proof (HLB b Hb). lia. - exact S2. - lia.
Qed.
Lemma kept_outside L LB sp scr W a x n : L5C.kept L LB sp scr W a -> In (x, n) W -> ~ (x <= a < x + n).
Proof. intros (_ & _ & _ & OW) Hin. specialize (OW (x, n) Hin). unfold L5.in_rng in OW. cbn in OW. exact OW. Qed.

(* [comment removed for export] *)
Lemma obj_limbs_at M o b ws : L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> L5.limbs_at RSEGS M (L5.bo_data o b) ws.
Proof.
  intros OB (Lw & Rw & V). destruct b as [fb len [v0 v1|cap q]]; cbn [L5.bo_st L5.bo_data L5.bo_len] in *.
  - destruct OB as (_ & _ & _ & _ & O16 & O24 & Hl2 & _). subst ws.
    intros i Hi. rewrite length_firstn in Hi. cbn [length] in Hi.
    destruct len as [|[|[|len]]]; cbn; try lia.
    + destruct i; [|lia]. cbn -[Z.add Z.mul Z.of_nat]. rewrite Z.add_0_r. exact O16.
    + destruct i as [|[|i]]; try lia; cbn -[Z.add Z.mul Z.of_nat]. rewrite Z.add_0_r. exact O16. replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by lia. exact O24.
    + exfalso. cbn [L5.bo_len] in Hl2. lia.
  - exact V.
Qed.

(* [comment removed for export] *)
Lemma u64_at_agree1 M M' a v : (forall i, a <= i < a + 8 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v.
Proof. intros HA Ha H8 Hu. eapply (L5C.u64_at_agree RSEGS M M'). intros i Hi. apply HA. exact Hi. lia. lia. exact Hu. Qed.

Lemma two_words (l : list Z) : length l = 2%nat -> l = [nth_w l 0; nth_w l 1].
Proof. intros H. destruct l as [|a [|b [|c l]]]; cbn in H; try lia. reflexivity. Qed.

Local Ltac uSCR := unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in *.
Local Ltac sclia := unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in *; lia.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis RESIZE : resize_spec L HI.

(* [comment removed for export] *)
Lemma mulm_tail (fx3 : FPState) (R R3 : bvmap 5 word) (M M3 : word -> option byte) (model model2 : Model) (K : TSet)
      (LB LB' : list (Z * Z)) (cr cr' : credit) (o sp r y fb : Z) (len : nat) (sto : L5.bstore) (ws : list Z)
      (d fb2 cap2 : Z) (st2 : L5.bstore) (g : growth) (Wf : list L5.range) :
  let b := L5.BO fb len sto in
  m_halted model = None -> m_vm_lazy model = [] -> model_but_vm model model2 -> L5.ra_ok r ->
  getr R (reg 1) = Z_to_bv 64 r -> getr R (reg 2) = Z_to_bv 64 sp ->
  0 <= y < 2 ^ 64 -> (1 <= len <= 300)%nat -> spok sp -> (hl_sptop L - 8388608) + MULM_SCR <= sp -> sp <= o -> o + 32 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> o mod 8 = 0 ->
  hi_heap HI LB' cr' M3 (m_vmmaps model2) -> (forall bb, In bb LB -> fst bb + snd bb <= (hl_sptop L - 8388608)) ->
  (* [comment removed for export] *)
  at_head R3 sp o y d len 0 (nth_w ws 0) 0 (HV y) (LV y) -> view M3 sp o d (Z.of_nat len) -> length ws = len -> words_ok ws ->
  (forall j, (j <= len)%nat -> L5.u64_at RSEGS M3 (d + 8 * Z.of_nat j) (nth_w (ws ++ [0]) j)) ->
  (forall i, In i cs_pass -> getr R3 (reg i) = getr R (reg i)) ->
  saved M3 sp R -> L5.defined M3 (sp - MULM_SCR) MULM_SCR -> L5.defined M3 o 32 ->
  L5.big_at RSEGS M3 o (L5.BO fb2 (S len) st2) -> 0 <= fb2 < 256 ->
  ((st2 = L5.BDyn cap2 d /\ d + 8 * cap2 <= sp - MULM_SCR) \/ (exists v0 v1, st2 = L5.BInl v0 v1 /\ d = o + 16 /\ len = 1%nat /\ cap2 = 2)) ->
  Z.of_nat len + 1 <= cap2 -> 4096 <= d -> d + 8 * cap2 <= 2 ^ 47 -> d mod 8 = 0 -> L5.defined M3 d (8 * cap2) ->
  (forall i, d <= i < d + 8 * cap2 -> ((hl_sptop L - 8388608) <= i < hl_sptop L) \/ in_block LB' i) ->
  (* [comment removed for export] *)
  (forall a, L5C.kept L LB sp MULM_SCR Wf a -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, L5C.kept L LB sp MULM_SCR Wf a -> ~ (d <= a < d + 8 * Z.of_nat len + 8) /\ ~ (o <= a < o + 32)) ->
  (forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp MULM_SCR a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M3 (Z_to_bv 64 a) <> None) ->
  (* [comment removed for export] *)
  match g with
  | Same => (L5.bo_dyn b = true \/ (S len <= 2)%nat) /\ LB' = LB /\ cr' = cr /\ fb2 = fb
            /\ match sto, st2 with L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q | L5.BInl _ _, L5.BInl _ _ => True | _, _ => False end
            /\ Wf = [(o, 32); (L5.bo_data o b, 8 * Z.of_nat (S len))]
  | Grown A cap => L5.bo_dyn b = false /\ (3 <= S len)%nat /\ cap = round_up (Z.of_nat (S len)) /\ LB' = (A, 8 * cap) :: LB /\ cr' = debit L cr (8 * cap)
            /\ block_range L A (8 * cap) /\ blocks_apart A (8 * cap) LB /\ st2 = L5.BDyn cap A /\ fb2 = Z.lor fb 1 /\ A = d /\ cap = cap2 /\ Wf = [(o, 32)]
  end ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        mulm_post L LB cr M M' R R' o sp y b ws g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg R3 LHEAD M3 model2) K.
Proof.
  intros b Mh Ml MBV [Hr He] H1 H2 Hy Hn SP SLO Aso Ohi STOP Ao HH3 LBhi AT VW3 WL WO LIMBS3 PASS3 SV3 DEF3 DEFo3 OB3 Hfb2 ST2 CAP2 Dlo Dhi D8 DEFd DCL KEPT3 KOUT DEFK GF KONT.
  pose proof SP as [S16 Ssp].
  pose proof (L5C.halted_but_vm _ _ MBV) as Mh2. rewrite Mh in Mh2. pose proof (L5C.lazy_but_vm _ _ MBV) as Ml2. rewrite Ml in Ml2.
  unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SLO, DEF3, ST2.
  assert (DAP: d + 8 * cap2 <= sp - (144 + (64 + (48 + (64 + (16 + 8224))))) \/ d = o + 16) by (destruct ST2 as [[_ X]|(v0 & v1 & _ & X & _)]; lia).
  assert (DAPF: apart (sp - 144) 144 d (8 * Z.of_nat len + 8)). { unfold apart. destruct DAP; lia. }
  assert (IMG: hl_img_hi L = 0x92000) by (apply (ly_img_hi L LY)).
  assert (DW3: L5.writable RSEGS M3 d (8 * Z.of_nat len + 8)).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEFd. lia. lia. lia. lia. }
  assert (DNO: forall i, d <= i < d + 8 * cap2 -> ~ (o <= i < o + 16) /\ ~ (sp - 144 <= i < sp)). { intros i Hi. destruct DAP; lia. }
  (* [comment removed for export] *)
  assert (AT': at_head R3 sp o y d len 0 (nth_w ws 0) (mulw_c ws y 0 0) (HV y) (LV y)) by (rewrite mulw_c_0; exact AT).
  destruct (mloop (len - 0) fx3 R R3 M3 sp o y d len 0 ws ltac:(lia) AT' ltac:(lia) ltac:(lia) WL WO Hy VW3 SP DAPF ltac:(lia) ltac:(lia)
              Dlo ltac:(lia) D8 DW3 ltac:(intros j Hj; lia) ltac:(intros j Hj; apply LIMBS3; lia))
    as (fx5 & R5 & M5 & MS5 & K5 & (C1 & C2 & C8 & C10) & LIMBS5 & FR4 & G5).
  set (rw := mulw_words ws y) in *.
  assert (RWL: length rw = S len). { subst rw. rewrite mulw_words_length, WL. reflexivity. }
  assert (RWO: words_ok rw). { subst rw. apply mulw_words_ok. exact WO. exact Hy. }
  assert (FR45: forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * Z.of_nat len + 8) -> M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR4. rewrite BG.unsigned_lit by lia. exact Hna. }
  (* [comment removed for export] *)
  set (st5 := match st2 with L5.BDyn c q => L5.BDyn c q | L5.BInl _ _ => L5.BInl (nth_w rw 0) (nth_w rw 1) end).
  assert (OB5: L5.big_at RSEGS M5 o (L5.BO fb2 (S len) st5)).
  { destruct OB3 as (P0 & _ & P8 & PST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in P0, P8, PST.
    unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
    split. { eapply (L5C.u8_at_agree RSEGS M3 M5). intros i Hi. apply FR45. lia. pose proof (DNO d ltac:(lia)). lia. lia. lia. exact P0. }
    split. exact Hfb2.
    split. { eapply u64_at_agree1. intros i Hi. apply FR45. lia. destruct DAP; lia. lia. lia. exact P8. }
    destruct ST2 as [[-> DB] | (v0 & v1 & -> & Dd & L1 & C2')]; subst st5.
    - destruct PST as (T0 & P16 & P24 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6). split. exact T0.
      split. { eapply u64_at_agree1. intros i Hi. apply FR45. lia. lia. lia. lia. exact P16. }
      split. { eapply u64_at_agree1. intros i Hi. apply FR45. lia. lia. lia. lia. exact P24. }
      repeat split; first [assumption | lia].
    - destruct PST as (T0 & _ & _ & _). split. exact T0.
      pose proof (words_ok_nth rw 0 RWO). pose proof (words_ok_nth rw 1 RWO).
      split. { subst d. replace (o + 16) with (o + 16 + 8 * Z.of_nat 0) by lia. apply LIMBS5. lia. }
      split. { subst d. replace (o + 24) with (o + 16 + 8 * Z.of_nat 1) by lia. apply LIMBS5. lia. }
      repeat split; lia. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS5.
  eapply (L5REDGU.reduce_ok fx5 R5 M5 model2 K o AFTER_REDUCE (L5.BO fb2 (S len) st5) rw Mh2 Ml2).
  + rewrite r10. exact C10.
  + rewrite r1. exact C1.
  + split. unfold AFTER_REDUCE. lia. reflexivity.
  + exact OB5.
  + exact Ao. + lia. + lia.
  + eapply L5.writable_grows. exact G5. eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEFo3. lia. lia. lia. lia.
  + assert (E: L5.bo_data o (L5.BO fb2 (S len) st5) = d /\ L5.bo_cap (L5.BO fb2 (S len) st5) = cap2).
    { destruct ST2 as [[-> DB] | (v0 & v1 & -> & Dd & L1 & C2')]; subst st5; cbn; split; congruence. }
    destruct E as [-> ->]. eapply L5.defined_grows. exact G5. exact DEFd.
  + replace (L5.bo_data o (L5.BO fb2 (S len) st5)) with d. exact LIMBS5.
    destruct ST2 as [[-> DB] | (v0 & v1 & -> & Dd & L1 & C2')]; subst st5; cbn; congruence.
  + cbn [L5.bo_len]. exact RWL.
  + exact RWO.
  + intros cap q Hst. left. destruct ST2 as [[E2 DB] | (v0 & v1 & E2 & Dd & L1 & C2')]; subst st5; rewrite E2 in Hst. 2: discriminate.
    inversion Hst; subst. lia.
  + (* [comment removed for export] *)
    intros fx6 R6 M6 (OB6 & RP6 & B10 & FR6 & G6). cbn [L5.bo_fb L5.bo_st] in OB6.
    assert (FR6z: forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 16) -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
    { intros a Ha Hna. apply FR6. intros rg [<-|[]]. unfold L5.in_rng. cbn. rewrite BG.unsigned_lit by lia. lia. }
    assert (E2: getr R6 (reg 2) = Z_to_bv 64 (sp - 144)). { rewrite <- r2, (RP6 2%bv ltac:(cbn; tauto)), r2. exact C2. }
    assert (E8: getr R6 (reg 8) = Z_to_bv 64 o). { rewrite (RP6 (reg 8) ltac:(cbn; tauto)). exact C8. }
    assert (CH: forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * Z.of_nat len + 8) -> ~ (o <= a < o + 16) -> M6 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
    { intros a Ha X Y. rewrite FR6z by lia. apply FR45; lia. }
    assert (SV6: saved M6 sp R).
    { destruct SV3 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13). pose proof (DNO d ltac:(lia)) as [_ ND].
      repeat split; (eapply u64_at_agree1; [intros i Hi; apply CH; [lia | destruct DAP; lia | lia] | lia | lia | assumption]). }
    assert (G36: mem_grows M3 M6). { eapply mem_grows_trans. exact G5. exact G6. }
    assert (WR6: L5.writable RSEGS M6 (sp - 144) 144).
    { eapply L5.writable_grows. exact G36. eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF3. lia. lia. lia. lia. }
    destruct (mmE_conc fx6 R R6 M6 sp o SP WR6 SV6 ltac:(lia) E2 E8) as (fx7 & R7 & M7 & MS7 & K7 & RET7 & MM7 & G7).
    pose proof RET7 as (T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & T10).
    pose proof (ret_23488 fx7 R7 M7 r ltac:(rewrite T1; exact H1) Hr He) as MS8.
    unfold L5REDU.cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. eapply msteps_trans. exact MS7. exact MS8.
    assert (CH7: forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 8 * Z.of_nat len + 8) -> ~ (o <= a < o + 16) -> M7 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
    { intros a Ha X Y. rewrite MM7. apply CH; lia. }
    assert (G37: mem_grows M3 M7) by (eapply mem_grows_trans; [exact G36 | exact G7]).
    apply (KONT fx7 R7 M7 model2 g LB' cr').
    * (* [comment removed for export] *)
      unfold mulm_post. subst b. cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_data] in GF |- *. fold rw.
      split. { apply (preserved_of_ret R R7 sp o H2 RET7). intros i Hi. rewrite (K7 i) by (apply (L5K.incl_b cs_pass KSE ltac:(vm_compute; reflexivity)); exact Hi).
               rewrite (pass_of_preserved R5 R6 RP6 i Hi). rewrite (K5 i) by (apply (L5K.incl_b cs_pass KSL ltac:(vm_compute; reflexivity)); exact Hi).
               apply PASS3. exact Hi. }
      split. { rewrite r10. exact T10. }
      split. exact RWL. split. exact RWO.
      assert (FB: match g with Same => fb | Grown _ _ => Z.lor fb 1 end = fb2). { destruct g; [destruct GF as (_ & _ & _ & E & _) | destruct GF as (_ & _ & _ & _ & _ & _ & _ & _ & E & _)]; congruence. }
      rewrite FB.
      exists st5.
      split. { eapply (L5C.big_at_agree RSEGS M6 M7). intros i Hi. apply MM7. lia. lia. exact OB6. }
      split. { split. cbn [L5.bo_len]. exact RWL. split. exact RWO. cbn [L5.bo_st L5.bo_len].
               destruct ST2 as [[-> DB] | (v0 & v1 & -> & Dd & L1 & C2')]; subst st5.
               - eapply (L5C.limbs_at_agree RSEGS M5 M7). { intros i Hi. rewrite MM7. apply FR6z. lia. rewrite RWL in Hi. pose proof (DNO i ltac:(lia)). lia. }
                 lia. rewrite RWL. lia. exact LIMBS5.
               - clear WL. subst len. etransitivity. apply (two_words rw RWL). reflexivity. }
      split. { rewrite <- RWL. apply rlen_le. }
      destruct g as [|A cap].
      -- destruct GF as (G1 & G2 & G3 & G4' & G5' & G6'). subst Wf. split. exact G1. split. exact G2. split. exact G3.
         split. { destruct sto as [v0 v1|cap q]; destruct ST2 as [[-> DB] | (v0' & v1' & -> & Dd & L1 & C2')]; subst st5; cbn in G5' |- *; try exact G5'; try contradiction; try exact I. }
         (* [comment removed for export] *)
         split; [|split].
         ++ intros a KA. pose proof KA as (Ha & _). rewrite CH7. apply KEPT3. exact KA. exact Ha. apply (proj1 (KOUT a KA)). pose proof (proj2 (KOUT a KA)). lia.
         ++ eapply L5.defined_grows. exact G37. exact DEF3.
         ++ intros a Ha CLa NEa Hd. apply G37. apply DEFK; assumption.
      -- destruct GF as (G1 & G2 & G3 & G4' & G5' & BR & BA & G8' & G9' & -> & -> & GW). subst Wf. split. exact G1. split. exact G2. split. exact G3. split. exact G4'. split. exact G5'.
         split. { split. exact BR. split. exact BA. eapply L5.defined_grows. exact G37. replace (8 * cap2) with (8 * cap2) by lia. exact DEFd. }
         split. { destruct ST2 as [[-> DB] | (v0 & v1 & E & Dd & L1 & C2')]; subst st5. reflexivity. rewrite G8' in E. discriminate. }
         split; [|split].
         ++ intros a KA. pose proof KA as (Ha & _). rewrite CH7. apply KEPT3. exact KA. exact Ha. apply (proj1 (KOUT a KA)). pose proof (proj2 (KOUT a KA)). lia.
         ++ eapply L5.defined_grows. exact G37. exact DEF3.
         ++ intros a Ha CLa NEa Hd. apply G37. apply DEFK; assumption.
    * exact MBV.
    * eapply (L5C.hi_heap_client L SCFG HI LB' cr' M3 M7). exact HIok. exact HH3. exact (ly_ro L LY). rewrite IMG; lia. lia.
      { intros a Ha.
        destruct (Z_lt_le_dec a d) as [X|X]; [|destruct (Z_lt_le_dec a (d + 8 * Z.of_nat len + 8)) as [X'|X']; [right; apply DCL; lia|]].
        all: destruct (Z_lt_le_dec a o) as [Y|Y]; [left; apply CH7; lia|].
        all: destruct (Z_lt_le_dec a (o + 16)) as [Y'|Y']; [right; left; lia|].
        all: left; apply CH7; lia. }
      exact G37.
Qed.

(* [comment removed for export] *)
Theorem mulm_ok : mulm_spec L HI.
Proof.
  unfold mulm_spec. intros fx R M model K LB cr o sp r y b ws HH MOK HK0 H10 H11 Hy H1 RA H2 H4 STK OB OL Hn Ao Aso Ohi DEFo CAP CR BLK KONT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF). pose proof RA as [Hr He].
  unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in *.
  rewrite r10 in H10. rewrite r11 in H11. rewrite r1 in H1. rewrite r2 in H2. rewrite r4 in H4.
  assert (LBhi: forall bb, In bb LB -> fst bb + snd bb <= (hl_sptop L - 8388608)).
  { intros bb Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) bb Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
  assert (LBdef: forall A n, In (A, n) LB -> L5.defined M A n).
  { intros A n Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) (A, n) Hb) as (_ & D & _). exact D. }
  assert (IMG: hl_img_hi L = 0x92000) by (apply (ly_img_hi L LY)).
  assert (SP: spok sp). { split. exact A16. lia. }
  assert (WR48: L5.writable RSEGS M (sp - 144) 144).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  destruct b as [fb len sto]. pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap L5.bo_data] in *.
  pose proof OL as (Lws & Rws & Vws). cbn [L5.bo_len L5.bo_st] in Lws, Vws.
  assert (LIMBS: L5.limbs_at RSEGS M (L5.bo_data o (L5.BO fb len sto)) ws) by (apply obj_limbs_at; [exact OB | exact OL]).
  cbn [L5.bo_data L5.bo_st] in LIMBS.
  assert (Hlen: Z.of_nat len <= 2 ^ 27).
  { destruct sto as [v0 v1|cap q]. destruct OST as (_ & _ & _ & Hl2 & _). lia. destruct OST as (_ & _ & _ & Hlc & Hc & _). lia. }
  (* [comment removed for export] *)
  assert (HCL: forall LBx crx M1 M2 VM, hi_heap HI LBx crx M1 VM ->
     (forall a, 0 <= a < 2 ^ 64 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a) \/ ((hl_sptop L - 8388608) <= a < hl_sptop L) \/ in_block LBx a) ->
     mem_grows M1 M2 -> hi_heap HI LBx crx M2 VM).
  { intros LBx crx M1 M2 VM HHx CH GR. eapply (L5C.hi_heap_client L SCFG HI LBx crx M1 M2). exact HIok. exact HHx. exact (ly_ro L LY). rewrite IMG; lia. lia. exact CH. exact GR. }
  (* [comment removed for export] *)
  set (dd := L5.bo_data o (L5.BO fb len sto)) in *. set (cc := L5.bo_cap (L5.BO fb len sto)) in *.
  assert (DFACTS: L5.defined M dd (8 * cc) /\ Z.of_nat len <= cc /\ 4096 <= dd /\ dd + 8 * cc <= 2 ^ 47 /\ dd mod 8 = 0
                  /\ (forall i, dd <= i < dd + 8 * cc -> ~ (sp - 144 <= i < sp)) /\ (dd + 8 * cc <= o \/ o + 32 <= dd \/ dd = o + 16)
                  /\ (forall i, dd <= i < dd + 8 * cc -> ((hl_sptop L - 8388608) <= i < hl_sptop L) \/ in_block LB i)).
  { subst dd cc. destruct sto as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_cap L5.bo_st L5.bo_len].
    - destruct OST as (_ & _ & _ & Hl2 & _). split. eapply L5.defined_sub. exact DEFo. lia. lia.
      split. lia. split. lia. split. lia. split. rewrite <- Zplus_mod_idemp_l, Ao. reflexivity.
      split. intros; lia. split. lia. intros i Hi. left. lia.
    - destruct OST as (B0 & O16 & O24 & Hlc & Hc & Q8 & QLO & QHI & HAP). pose proof (BLK cap q eq_refl) as IN. pose proof (LBhi _ IN) as BH. cbn in BH.
      split. apply LBdef. exact IN. split. exact Hlc. split. exact QLO. split. exact QHI. split. exact Q8.
      split. intros; lia. split. lia. intros i Hi. right. exists (q, 8 * cap). split. exact IN. cbn. lia. }
  destruct DFACTS as (DEFD & LC & DLO & DHI & D8 & DNS & DAP & DCL).
    assert (DNS2: forall i, dd + 8 * Z.of_nat len <= i < dd + 8 * Z.of_nat len + 8 -> ~ (sp - 144 <= i < sp)).
    { subst dd cc. destruct sto as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_cap L5.bo_st L5.bo_len L5.bo_dyn L5.bo_fb] in CAP, DNS |- *. intros; lia.
      destruct OST as (B0 & _). specialize (CAP B0). intros i Hi. apply DNS. lia. }
    pose proof (words_ok_nth ws 0 Rws) as Rdg.
    assert (X0: L5.u64_at RSEGS M dd (nth_w ws 0)). { replace dd with (dd + 8 * Z.of_nat 0) by lia. apply LIMBS. lia. }
    assert (ENTRY: exists fx1 R1 M1, msteps RSEGS (st fx R MULM M) (st fx1 R1 L5CSU.RESIZE M1)
        /\ (forall x, In x KSA -> getr R1 (reg x) = getr R (reg x)) /\ at_resize R1 sp o y (Z.of_nat len) (nth_w ws 0) /\ saved M1 sp R
        /\ (forall a : word, ~ (sp - 144 <= bv_unsigned a < sp) -> M1 a = M a) /\ mem_grows M M1).
    { subst dd. destruct sto as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_st] in X0.
      - destruct OST as (B0 & _). exact (mmAi_conc fx R M sp o y (Z.of_nat len) fb (nth_w ws 0) SP WR48 ltac:(unfold apart; lia) ltac:(lia) ltac:(lia) Ao O0 Hfb B0
                 X0 Rdg O8 ltac:(lia) Hy H2 H10 H11).
      - destruct OST as (B0 & O16 & O24 & Hlc & Hc & Q8 & QLO & QHI & HAP). pose proof (LBhi _ (BLK cap q eq_refl)) as BH. cbn in BH.
        exact (mmAd_conc fx R M sp o y (Z.of_nat len) fb q (nth_w ws 0) SP WR48 ltac:(unfold apart; lia) ltac:(lia) ltac:(lia) Ao O0 Hfb B0 O24 QLO ltac:(lia) Q8
                 X0 Rdg ltac:(unfold apart; lia) O8 ltac:(lia) Hy H2 H10 H11). }
    destruct ENTRY as (fx1 & R1 & M1 & MS1 & K1 & (A1 & A2 & A8 & A19 & A10 & A11 & A21 & A23) & SV1 & FR1 & G1).
    assert (FR1z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 144 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hna. apply FR1. rewrite BG.unsigned_lit by lia. exact Hna. }
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
    eapply (RESIZE fx1 R1 M1 model K LB cr o (sp - 144) AFTER_RESIZE (S len) (L5.BO fb len sto) ws).
    + apply (HCL LB cr M M1 (m_vmmaps model) HH). 2: exact G1.
      intros a Ha. destruct (Z_lt_le_dec a (sp - 144)) as [X|X]. left; apply FR1z; lia.
      destruct (Z_lt_le_dec a sp) as [X'|X']. right; left; lia. left; apply FR1z; lia.
    + exact MOK. + exact HK0.
    + rewrite r10. exact A10.
    + rewrite r11. rewrite A11. f_equal. lia.
    + lia.
    + cbn [L5.bo_dyn L5.bo_cap L5.bo_fb]. intros Hd. fold cc. specialize (CAP Hd). lia.
    + cbn [L5.bo_dyn L5.bo_fb]. intros H3 Hd. replace (Z.of_nat (S len)) with 3. apply CR. 2: exact Hd.
      all: destruct sto as [v0 v1|cap q]; [destruct OST as (_ & _ & _ & Hl2 & _); lia | destruct OST as (B0 & _); unfold L5.bo_dyn in Hd; cbn [L5.bo_fb] in Hd; congruence].
    + rewrite r1. exact A1.
    + split. unfold AFTER_RESIZE. lia. reflexivity.
    + rewrite r2. exact A2.
    + rewrite r4. rewrite (K1 4%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H4.
    + split. { replace (sp - 144) with (sp + (-9) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
      unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. split. lia. split. lia. split. lia.
      eapply L5.defined_grows. exact G1. eapply L5.defined_sub. exact DEF. lia. lia.
    + eapply (L5C.big_at_agree RSEGS M M1). intros i Hi. apply FR1z; lia. lia. lia. exact OB.
    + split. exact Lws. split. exact Rws. cbn [L5.bo_st L5.bo_len]. destruct sto as [v0 v1|cap q]. exact Vws.
      cbn [L5.bo_data L5.bo_st] in dd. subst dd. eapply (L5C.limbs_at_agree RSEGS M M1). { intros i Hi. apply FR1z. lia. apply DNS. lia. } lia. lia. exact Vws.
    + exact Ao. + lia. + exact Ohi.
    + eapply L5.writable_grows. exact G1. apply (L5C.writable_of_defined RSEGS). exact DEFo. lia. lia.
    + intros cap q Hst. apply BLK. exact Hst.
    + (* [comment removed for export] *)
      intros fx2 R2 M2 model2 g LB' cr' [RP POST] MBV HH2.
      pose proof (L5C.halted_but_vm _ _ MBV) as Mh2. rewrite Mh in Mh2. pose proof (L5C.lazy_but_vm _ _ MBV) as Ml2. rewrite Ml in Ml2.
      (* [comment removed for export] *)
      assert (B2: getr R2 (reg 2) = Z_to_bv 64 (sp - 144)). { rewrite (RP (reg 2) ltac:(cbn; tauto)). exact A2. }
      assert (B8: getr R2 (reg 8) = Z_to_bv 64 o). { rewrite (RP (reg 8) ltac:(cbn; tauto)). exact A8. }
      assert (B19: getr R2 (reg 19) = Z_to_bv 64 y). { rewrite (RP (reg 19) ltac:(cbn; tauto)). exact A19. }
      assert (B21: getr R2 (reg 21) = Z_to_bv 64 (Z.of_nat len)). { rewrite (RP (reg 21) ltac:(cbn; tauto)). exact A21. }
      assert (B23: getr R2 (reg 23) = Z_to_bv 64 (nth_w ws 0)). { rewrite (RP (reg 23) ltac:(cbn; tauto)). exact A23. }
      assert (PASS2: forall i, In i cs_pass -> getr R2 (reg i) = getr R (reg i)).
      { intros i Hi. rewrite (pass_of_preserved R1 R2 RP i Hi). apply K1. apply (L5K.incl_b cs_pass KSA ltac:(vm_compute; reflexivity)). exact Hi. }
      (* [comment removed for export] *)
      set (thirdW := match g with Same => True | Grown _ _ => False end).
      assert (HP: exists W2, L5C.hpres L LB (sp - 144) RESIZE_SCR W2 M1 M2 /\ (forall a, L5.outside W2 a \/ (o <= a < o + 32) \/ (thirdW /\ dd + 8 * Z.of_nat len <= a < dd + 8 * Z.of_nat len + 8))).
      { subst thirdW. destruct g as [|A cap].
        - destruct POST as (_ & _ & _ & _ & HP). exists [(o, 32); (dd + 8 * Z.of_nat len, 8 * Z.max 0 (Z.of_nat (S len) - Z.of_nat len))]. split. exact HP.
          intros a. destruct (Z_lt_le_dec a o) as [X|X]; [|destruct (Z_lt_le_dec a (o + 32)) as [X'|X']; [right; left; lia|]].
          all: destruct (Z_lt_le_dec a (dd + 8 * Z.of_nat len)) as [Y|Y]; [|destruct (Z_lt_le_dec a (dd + 8 * Z.of_nat len + 8)) as [Y'|Y']; [right; right; split; [exact I|lia]|]].
          all: left; apply L5C.outside_cons; [unfold L5.in_rng; cbn; lia|]; apply L5C.outside_cons; [unfold L5.in_rng; cbn; lia|]; apply L5C.outside_nil.
        - destruct POST as (_ & _ & _ & _ & _ & _ & _ & _ & HP). exists [(o, 32)]. split. exact HP.
          intros a. destruct (Z_lt_le_dec a o) as [X|X]; [|destruct (Z_lt_le_dec a (o + 32)) as [X'|X']; [right; left; lia|]].
          all: left; apply L5C.outside_cons; [unfold L5.in_rng; cbn; lia|]; apply L5C.outside_nil. }
      destruct HP as (W2 & HP2 & HW2). pose proof HP2 as (PRES & SDEF & PDEF). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in PRES, SDEF, PDEF.
      (* [comment removed for export] *)
      assert (CL2: forall a, (hl_sptop L - 8388608) <= a < hl_sptop L -> ~ (sp - 144 - (64 + (48 + (64 + (16 + 8224)))) <= a < sp - 144) ->
                   ~ (o <= a < o + 32) -> ~ (dd + 8 * Z.of_nat len <= a < dd + 8 * Z.of_nat len + 8) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha Hns Hno Hnd. apply PRES. split. lia. split. { right. left. lia. }
        split. { unfold in_errno. rewrite (ly_errno L LY). lia. } destruct (HW2 a) as [Wa|[Wa|[_ Wa]]]; [exact Wa | exfalso; lia | exfalso; lia]. }
      assert (SV2: saved M2 sp R).
      { destruct SV1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
        repeat split; (eapply u64_at_agree1; [intros i Hi; apply CL2; [lia|lia|lia| intros C; apply (DNS2 i); lia] | lia | lia | assumption]). }
      assert (DEF2: L5.defined M2 (sp - MULM_SCR) MULM_SCR).
      { unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. intros i Hi.
        destruct (Z_lt_le_dec (sp - (144 + (64 + (48 + (64 + (16 + 8224))))) + i) (sp - 144)) as [X|X].
        - replace (sp - (144 + (64 + (48 + (64 + (16 + 8224))))) + i) with (sp - 144 - (64 + (48 + (64 + (16 + 8224)))) + (i)) by lia. apply SDEF. lia.
        - apply PDEF. lia. right; left. lia. unfold in_errno. rewrite (ly_errno L LY). lia.
          apply G1. apply DEF. lia. }
      assert (DEFo2: L5.defined M2 o 32).
      { intros i Hi. apply PDEF. lia. right; left. lia. unfold in_errno. rewrite (ly_errno L LY). lia. apply G1. apply DEFo. lia. }
      (* [comment removed for export] *)
      assert (KEPT2: forall Wf a, L5C.kept L LB sp MULM_SCR Wf a -> (L5.outside Wf a -> ~ (o <= a < o + 32)) ->
                 (L5.outside Wf a -> thirdW -> ~ (dd + 8 * Z.of_nat len <= a < dd + 8 * Z.of_nat len + 8)) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros Wf a KA NO ND. pose proof KA as (Ha & CA & NE & OW). rewrite PRES. apply FR1z. exact Ha.
        pose proof (kept_not_scratch L LB sp _ _ a KA ltac:(unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia) ltac:(rewrite IMG; lia) LBhi) as NS.
        unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in NS. lia.
        eapply L5C.kept_inner. exact KA. unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia. lia.
        intros OWa. destruct (HW2 a) as [Wa|[Wa|[TW Wa]]]. exact Wa. exfalso; exact (NO OWa Wa). exfalso; exact (ND OWa TW Wa). }
      assert (DEFK2: forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp MULM_SCR a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None).
      { intros a Ha CA NE Hd. apply PDEF. exact Ha.
        destruct CA as [IB|[[S1 S2]|IM]]. left; exact IB. right; left. split. exact S1. unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in S2 |- *. lia. right; right; exact IM.
        exact NE. apply G1. exact Hd. }
      assert (LBhi2: forall bb, In bb LB' -> fst bb + snd bb <= (hl_sptop L - 8388608)).
      { intros bb Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB' cr' M2 _ HH2) bb Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
      uSCR.
      destruct g as [|A cap]; cbn in thirdW; subst thirdW.
      * (* [comment removed for export] *)
        destruct POST as (SM1 & -> & -> & (st' & OB2 & OL2 & STM) & _).
        assert (RSL: resize_limbs ws (S len) = ws ++ [0]).
        { unfold resize_limbs. rewrite firstn_all2 by lia. rewrite Lws. replace (S len - len)%nat with 1%nat by lia. reflexivity. }
        rewrite RSL in OL2.
        destruct sto as [v0 v1|cap q]; destruct st' as [v0' v1'|cap' q']; try contradiction.
        -- (* [comment removed for export] *)
           destruct SM1 as [SM1|SM1]. { destruct OST as (B0 & _). unfold L5.bo_dyn in SM1. cbn [L5.bo_fb] in SM1. congruence. }
           assert (L1: len = 1%nat) by lia. revert Lws. subst len. intros Lws.
           cbn [L5.bo_data L5.bo_st L5.bo_cap] in dd, cc. subst dd cc.
           pose proof OL2 as (_ & _ & VE). cbn [L5.bo_st L5.bo_len] in VE.
           destruct ws as [|w0 [|w1 ws']]; cbn in Lws; try lia. cbn in VE. injection VE as E0 E1.
           pose proof OB2 as (P0 & _ & P8 & B0' & P16 & P24 & _ & R0' & R1'). cbn [L5.bo_fb L5.bo_len L5.bo_st] in P0, P8, B0', P16, P24.
           destruct (mmBi_conc fx2 R R2 M2 sp o y fb (nth_w [w0] 0) SP ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF2|lia|lia]|lia|lia])
                       ltac:(unfold apart; lia) ltac:(lia) ltac:(lia) Ao P0 Hfb B0' ltac:(exact P8) Hy Rdg B2 B8 B19 ltac:(rewrite B21; reflexivity) B23)
             as (fx3 & R3 & M3 & MS3 & K3 & AT3 & VW3 & MM3 & G3).
           eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
           assert (FR3z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 136 <= a < sp - 104) -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)). { intros a Ha Hna. apply MM3. rewrite BG.unsigned_lit by lia. exact Hna. }
           eapply (mulm_tail fx3 R R3 M M3 model model2 K LB LB cr cr o sp r y fb 1%nat (L5.BInl v0 v1) [w0] (o + 16) fb 2 (L5.BInl v0' v1') Same
                     [(o, 32); (o + 16, 8 * Z.of_nat 2)] Mh Ml MBV RA H1 H2 Hy ltac:(lia) SP ltac:(sclia) Aso Ohi STOP Ao).
           ++ apply (HCL LB cr M2 M3 (m_vmmaps model2) HH2). 2: exact G3. intros a Ha. destruct (Z_lt_le_dec a (sp - 136)) as [X|X]; [left; apply FR3z; lia|]. destruct (Z_lt_le_dec a (sp - 104)) as [X'|X']; [right; left; lia| left; apply FR3z; lia].
           ++ exact LBhi.
           ++ exact AT3. ++ exact VW3.
           ++ reflexivity. ++ exact Rws.
           ++ intros j Hj. eapply u64_at_agree1. { intros i Hi. apply FR3z. lia. pose proof (DNS i). lia. } lia. lia.
              destruct j as [|[|j]]; cbn [nth_w nth app]. replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by lia. rewrite E0. exact P16.
              replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by lia. rewrite E1. exact P24. lia.
           ++ intros i Hi. rewrite (K3 i) by (apply (L5K.incl_b cs_pass KSBi ltac:(vm_compute; reflexivity)); exact Hi). apply PASS2. exact Hi.
           ++ destruct SV2 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13). repeat split; (eapply u64_at_agree1; [intros i Hi; apply FR3z; lia; lia | lia | lia | assumption]).
           ++ eapply L5.defined_grows. exact G3. exact DEF2.
           ++ eapply L5.defined_grows. exact G3. exact DEFo2.
           ++ eapply (L5C.big_at_agree RSEGS M2 M3). intros i Hi. apply FR3z; lia. lia. lia. exact OB2.
           ++ exact Hfb.
           ++ right. exists v0', v1'. repeat split; reflexivity.
           ++ lia. ++ lia. ++ lia.
           ++ rewrite <- Zplus_mod_idemp_l, Ao. reflexivity.
           ++ eapply L5.defined_grows. exact G3. eapply L5.defined_sub. exact DEFo2. lia. lia.
           ++ intros i Hi. left. lia.
           ++ intros a KA. pose proof (kept_outside L LB sp _ _ a o 32 KA ltac:(left; reflexivity)) as NO. pose proof KA as (Ha & _).
              pose proof (kept_not_scratch L LB sp _ _ a KA ltac:(sclia) ltac:(rewrite IMG; lia) LBhi) as NS. unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in NS.
              rewrite FR3z by lia. apply (KEPT2 _ a KA). intros _. exact NO. intros _ _. cbn [L5.bo_data L5.bo_st]. lia.
           ++ intros a KA. pose proof (kept_outside L LB sp _ _ a o 32 KA ltac:(left; reflexivity)) as NO. split; lia.
           ++ intros a Ha CA NE Hd. apply G3. apply DEFK2; assumption.
           ++ cbn [L5.bo_dyn L5.bo_fb L5.bo_data L5.bo_st]. split. right; lia. split. reflexivity. split. reflexivity. split. reflexivity. split. exact I. reflexivity.
           ++ exact KONT.
        -- (* [comment removed for export] *)
           destruct STM as [-> ->].
           destruct OST as (B0 & O16 & O24 & Hlc & Hc & Q8 & QLO & QHI & HAP). cbn [L5.bo_data L5.bo_st L5.bo_cap] in dd, cc. subst dd cc.
           pose proof (BLK cap q eq_refl) as IN. pose proof (LBhi _ IN) as BH. cbn in BH.
           cbn [L5.bo_dyn L5.bo_fb L5.bo_cap] in CAP. specialize (CAP B0).
           pose proof OB2 as (P0 & _ & P8 & _ & P16 & P24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in P0, P8, P16, P24.
           pose proof OL2 as (LL2 & LR2 & LV2). cbn [L5.bo_st L5.bo_len] in LV2.
           assert (BDEF2: L5.defined M2 q (8 * cap)). { pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M2 _ HH2) (q, 8 * cap) IN) as (_ & D & _). exact D. }
           destruct (mmBd_conc fx2 R R2 M2 sp o y fb q (nth_w ws 0) len SP ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF2|lia|lia]|lia|lia])
                       ltac:(unfold apart; lia) ltac:(lia) ltac:(lia) Ao P0 Hfb B0 ltac:(replace (Z.of_nat len + 1) with (Z.of_nat (S len)) by lia; exact P8) P24 ltac:(lia) Hy Rdg
                       QLO ltac:(lia) Q8 B2 B8 B19 B21 B23)
             as (fx3 & R3 & M3 & MS3 & K3 & AT3 & VW3 & MM3 & G3).
           eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
           assert (FR3z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 136 <= a < sp - 104) -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)). { intros a Ha Hna. apply MM3. rewrite BG.unsigned_lit by lia. exact Hna. }
           eapply (mulm_tail fx3 R R3 M M3 model model2 K LB LB cr cr o sp r y fb len (L5.BDyn cap q) ws q fb cap (L5.BDyn cap q) Same
                     [(o, 32); (q, 8 * Z.of_nat (S len))] Mh Ml MBV RA H1 H2 Hy ltac:(lia) SP ltac:(sclia) Aso Ohi STOP Ao).
           ++ apply (HCL LB cr M2 M3 (m_vmmaps model2) HH2). 2: exact G3. intros a Ha. destruct (Z_lt_le_dec a (sp - 136)) as [X|X]; [left; apply FR3z; lia|]. destruct (Z_lt_le_dec a (sp - 104)) as [X'|X']; [right; left; lia| left; apply FR3z; lia].
           ++ exact LBhi.
           ++ exact AT3. ++ exact VW3.
           ++ exact Lws. ++ exact Rws.
           ++ intros j Hj. eapply u64_at_agree1. { intros i Hi. apply FR3z. lia. pose proof (DNS i). lia. } lia. lia. unfold nth_w. apply LV2. rewrite length_app, Lws. cbn. lia.
           ++ intros i Hi. rewrite (K3 i) by (apply (L5K.incl_b cs_pass KSBd ltac:(vm_compute; reflexivity)); exact Hi). apply PASS2. exact Hi.
           ++ destruct SV2 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13). repeat split; (eapply u64_at_agree1; [intros i Hi; apply FR3z; lia; lia | lia | lia | assumption]).
           ++ eapply L5.defined_grows. exact G3. exact DEF2.
           ++ eapply L5.defined_grows. exact G3. exact DEFo2.
           ++ eapply (L5C.big_at_agree RSEGS M2 M3). intros i Hi. apply FR3z; lia. lia. lia. exact OB2.
           ++ exact Hfb.
           ++ left. split. reflexivity. sclia.
           ++ lia. ++ exact QLO. ++ exact QHI. ++ exact Q8.
           ++ eapply L5.defined_grows. exact G3. exact BDEF2.
           ++ intros i Hi. right. exists (q, 8 * cap). split. exact IN. cbn. lia.
           ++ intros a KA. pose proof (kept_outside L LB sp _ _ a o 32 KA ltac:(left; reflexivity)) as NO.
              pose proof (kept_outside L LB sp _ _ a q (8 * Z.of_nat (S len)) KA ltac:(right; left; reflexivity)) as NQ. pose proof KA as (Ha & _).
              pose proof (kept_not_scratch L LB sp _ _ a KA ltac:(sclia) ltac:(rewrite IMG; lia) LBhi) as NS. unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in NS.
              rewrite FR3z by lia. apply (KEPT2 _ a KA). intros _. exact NO. intros _ _. lia.
           ++ intros a KA. pose proof (kept_outside L LB sp _ _ a o 32 KA ltac:(left; reflexivity)) as NO.
              pose proof (kept_outside L LB sp _ _ a q (8 * Z.of_nat (S len)) KA ltac:(right; left; reflexivity)) as NQ. split; lia.
           ++ intros a Ha CA NE Hd. apply G3. apply DEFK2; assumption.
           ++ cbn [L5.bo_dyn L5.bo_fb L5.bo_data L5.bo_st]. split. left; exact B0. split. reflexivity. split. reflexivity. split. reflexivity. split. split; reflexivity. reflexivity.
           ++ exact KONT.
      * (* [comment removed for export] *)
        destruct POST as (SM1 & L3 & CAPE & -> & -> & FB & OB2 & OL2 & _).
        destruct FB as (BR & BA & BDEF2).
        assert (RSL: resize_limbs ws (S len) = ws ++ [0]).
        { unfold resize_limbs. rewrite firstn_all2 by lia. rewrite Lws. replace (S len - len)%nat with 1%nat by lia. reflexivity. }
        rewrite RSL in OL2.
        destruct sto as [v0 v1|capx qx]. 2:{ destruct OST as (B0 & _). unfold L5.bo_dyn in SM1. cbn [L5.bo_fb] in SM1. congruence. }
        destruct OST as (B0 & O16 & O24 & Hl2 & _). assert (L2: len = 2%nat) by lia.
        cbn [L5.bo_data L5.bo_st L5.bo_cap] in dd, cc. subst dd cc.
        pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4). rewrite IMG in BR1.
        assert (CAP8: cap = 8). { rewrite CAPE, L2. reflexivity. }
        pose proof OB2 as (P0 & Hfb1 & P8 & B1 & P16 & P24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in P0, Hfb1, P8, B1, P16, P24.
        pose proof OL2 as (LL2 & LR2 & LV2). cbn [L5.bo_st L5.bo_len] in LV2.
        assert (AM8: A mod 8 = 0). { apply Z.mod_divide. lia. apply Z.mod_divide in BR2. 2: lia. destruct BR2 as [m Hm]. exists (m * 2). lia. }
        assert (IN': In (A, 8 * cap) ((A, 8 * cap) :: LB)) by (left; reflexivity).
        destruct (mmBd_conc fx2 R R2 M2 sp o y (Z.lor fb 1) A (nth_w ws 0) len SP ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DEF2|lia|lia]|lia|lia])
                    ltac:(unfold apart; lia) ltac:(lia) ltac:(lia) Ao P0 Hfb1 B1 ltac:(replace (Z.of_nat len + 1) with (Z.of_nat (S len)) by lia; exact P8) P24 ltac:(lia) Hy Rdg
                    ltac:(lia) ltac:(lia) AM8 B2 B8 B19 B21 B23)
          as (fx3 & R3 & M3 & MS3 & K3 & AT3 & VW3 & MM3 & G3).
        eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
        assert (FR3z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 136 <= a < sp - 104) -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)). { intros a Ha Hna. apply MM3. rewrite BG.unsigned_lit by lia. exact Hna. }
        assert (Hfb1': 0 <= Z.lor fb 1 < 256) by exact Hfb1.
        eapply (mulm_tail fx3 R R3 M M3 model model2 K LB ((A, 8 * cap) :: LB) cr (debit L cr (8 * cap)) o sp r y fb len (L5.BInl v0 v1) ws A (Z.lor fb 1) cap (L5.BDyn cap A) (Grown A cap)
                  [(o, 32)] Mh Ml MBV RA H1 H2 Hy ltac:(lia) SP ltac:(sclia) Aso Ohi STOP Ao).
        ++ apply (HCL ((A, 8 * cap) :: LB) (debit L cr (8 * cap)) M2 M3 (m_vmmaps model2) HH2). 2: exact G3. intros a Ha. destruct (Z_lt_le_dec a (sp - 136)) as [X|X]; [left; apply FR3z; lia|]. destruct (Z_lt_le_dec a (sp - 104)) as [X'|X']; [right; left; lia| left; apply FR3z; lia].
        ++ exact LBhi.
        ++ exact AT3. ++ exact VW3.
        ++ exact Lws. ++ exact Rws.
        ++ intros j Hj. eapply u64_at_agree1. { intros i Hi. apply FR3z. lia. lia. } lia. lia. unfold nth_w. apply LV2. rewrite length_app, Lws. cbn. lia.
        ++ intros i Hi. rewrite (K3 i) by (apply (L5K.incl_b cs_pass KSBd ltac:(vm_compute; reflexivity)); exact Hi). apply PASS2. exact Hi.
        ++ destruct SV2 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13). repeat split; (eapply u64_at_agree1; [intros i Hi; apply FR3z; lia; lia | lia | lia | assumption]).
        ++ eapply L5.defined_grows. exact G3. exact DEF2.
        ++ eapply L5.defined_grows. exact G3. exact DEFo2.
        ++ eapply (L5C.big_at_agree RSEGS M2 M3). intros i Hi. apply FR3z; lia. lia. lia. exact OB2.
        ++ exact Hfb1'.
        ++ left. split. reflexivity. sclia.
        ++ lia. ++ lia. ++ lia. ++ exact AM8.
        ++ eapply L5.defined_grows. exact G3. exact BDEF2.
        ++ intros i Hi. right. exists (A, 8 * cap). split. exact IN'. cbn. lia.
        ++ intros a KA. pose proof (kept_outside L LB sp _ _ a o 32 KA ltac:(left; reflexivity)) as NO. pose proof KA as (Ha & _).
           pose proof (L5C.kept_not_fresh L LB sp _ _ a A (8 * cap) KA BA ltac:(rewrite IMG; lia) ltac:(lia) LBhi) as NF.
           pose proof (kept_not_scratch L LB sp _ _ a KA ltac:(sclia) ltac:(rewrite IMG; lia) LBhi) as NS. unfold MULM_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in NS.
           rewrite FR3z by lia. apply (KEPT2 _ a KA). intros _. exact NO. intros _ F. destruct F.
        ++ intros a KA. pose proof (kept_outside L LB sp _ _ a o 32 KA ltac:(left; reflexivity)) as NO.
           pose proof (L5C.kept_not_fresh L LB sp _ _ a A (8 * cap) KA BA ltac:(rewrite IMG; lia) ltac:(lia) LBhi) as NF. split; lia.
        ++ intros a Ha CA NE Hd. apply G3. apply DEFK2; assumption.
        ++ cbn [L5.bo_dyn L5.bo_fb L5.bo_data L5.bo_st]. split. exact B0. split. lia. split. exact CAPE. split. reflexivity. split. reflexivity.
           split. exact BR. split. exact BA. repeat split; reflexivity.
        ++ exact KONT.
Qed.

End WithHeap.
End SCFG_1.

End L5MULMOKU.

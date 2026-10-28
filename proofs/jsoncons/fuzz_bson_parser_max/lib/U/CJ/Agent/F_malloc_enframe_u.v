(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u F_malloc_free_u F_malloc_fast_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition smear (s : Z) : Z :=
  let m1 := Z.lor s (Z.shiftr s 1) in
  let m2 := Z.lor m1 (Z.shiftr m1 2) in
  Z.lor m2 (Z.shiftr m2 4).

Lemma fold_off_eq off slack :
  fold_off off slack =
  (if slack <? off then
     let x := Z.land off (smear slack) in if slack <? x then x - (slack + 1) else x
   else off).
Proof. reflexivity. Qed.

Lemma smear_nonneg s : 0 <= s -> 0 <= smear s.
Proof.
  intros. unfold smear.
  repeat (apply Z.lor_nonneg; split); repeat apply Z.shiftr_nonneg; repeat (apply Z.lor_nonneg; split);
    repeat apply Z.shiftr_nonneg; try lia; repeat (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
  all: try (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
Qed.

Lemma land_le_l a b : 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros. rewrite <- (Z.lor_ldiff_and a b) at 2.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia).
  assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia).
  assert (Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by assumption. lia.
Qed.

(* [comment removed for export] *)
Definition zseq (a n : Z) : list Z := map Z.of_nat (seq (Z.to_nat a) (Z.to_nat n)).

(* [comment removed for export] *)
Definition fold_fn1 (s off : Z) : bool :=
  let x := Z.land off (smear s) in (negb (s <? x)) || (x - (s + 1) <=? s).
Definition fold_fn (s : Z) : bool := forallb (fold_fn1 s) (zseq 0 256).
Definition fold_check : bool := forallb fold_fn (zseq 0 128).

Lemma fold_check_true : forallb fold_fn (zseq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma forallb_zseq (f : Z -> bool) a n x : forallb f (zseq a n) = true -> 0 <= a -> a <= x < a + n -> f x = true.
Proof.
  intros H Ha Hx. unfold zseq in H. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma fold_assert_ok off slack : 0 <= off < 256 -> 0 <= slack ->
  slack < Z.land off (smear slack) -> Z.land off (smear slack) - (slack + 1) <= slack.
Proof.
  intros Ho Hs Hlt.
  pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  destruct (Z.lt_ge_cases slack 128).
  - pose proof (forallb_zseq fold_fn 0 128 slack fold_check_true ltac:(lia) ltac:(lia)) as H1. unfold fold_fn in H1.
    pose proof (forallb_zseq (fold_fn1 slack) 0 256 off H1 ltac:(lia) ltac:(lia)) as H2. unfold fold_fn1 in H2. cbv zeta in H2.
    apply orb_prop in H2. destruct H2 as [H2|H2].
    + apply negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
    + apply Z.leb_le in H2. exact H2.
  - lia.
Qed.

Lemma fold_off_range off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= Z.max slack off /\ fold_off off slack < 256.
Proof.
  intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
  destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
  destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
  pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.

Lemma fold_off_le_slack off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= slack.
Proof.
  intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
  destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
  destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
  pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.

Lemma land_126 y : Z.land y 126 = 2 * Z.land (Z.shiftr y 1) 63.
Proof.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|].
  - rewrite Z.testbit_even_0. change 126 with (2 * 63). rewrite Z.testbit_even_0. apply andb_false_r.
  - replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ by lia.
    change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
    replace (i - 1 + 1) with i by lia. replace (Z.succ (i - 1)) with i by lia. reflexivity.
Qed.

Lemma mword_sc last_idx freeable sc maplen :
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen ->
  Z.land (Z.shiftr (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) 5) 126 = 2 * sc.
Proof.
  intros. rewrite land_126. rewrite Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. change (2 ^ (5 + 1)) with 64.
  change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2^6) with 64.
  replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) / 64) with (sc + 64 * maplen) by (Z.div_mod_to_equations; lia).
  replace ((sc + 64 * maplen) mod 64) with sc by (Z.div_mod_to_equations; lia). reflexivity.
Qed.
End CEIL_WRAP_1.



(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sdk :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (try lazymatch goal with
     | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
     end);
    transport_chunks segs m E bs;
    repeat match goal with
    | STq : stk segs m ?loq ?hiq |- _ =>
        first [ apply (stk_write segs m loq hiq E bs) in STq; [ | lia | simpl_sizes; slia ]
              | fail 100 "sdk: cannot transport stk hypothesis" STq ]
    | MU : munch ?Wq ?mq m |- _ =>
        first [ apply (munch_write Wq mq m E bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
              | fail 100 "sdk: store outside the declared footprint" ]
    | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa E) bs) in WMo
    end;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    let m' := fresh "m" in let Eq := fresh "EQ" m' in
    remember (write_to_mem m (wa E) bs) as m' eqn:Eq
  end.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.


Lemma le1_wz v : 0 <= v < 256 -> le1 (wz v) = [b8 v].
Proof. intros. cbn. rewrite (wz_unsigned v) by lia. reflexivity. Qed.

Lemma le1_neg32 : le1 (Z_to_bv 64 (-32)) = [b8 224].
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition enframe_tail_mem (m : word -> option byte) (P E n k q : Z) : word -> option byte :=
  let m1 := write_to_mem m (wa (P - 2)) (le2 (wz q)) in
  let m2 := write_to_mem m1 (wa (P - 3)) [b8 k] in
  let r := E - P - n in
  let m3 := if r =? 0 then m2 else write_to_mem m2 (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 4)) (le4 (wz r))) (wa (E - 5)) [b8 0], 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

Definition en3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : word -> option byte) (P E n k q : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 pw a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ m' = enframe_tail_mem m P E n k q
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition enframe_off_mem (m : word -> option byte) (P0 off : Z) : word -> option byte :=
  if off =? 0 then m
  else write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 2)) (le2 (wz off))) (wa (P0 - 3)) [b8 224])
                    (wa (P0 + 16 * off - 4)) [b8 0].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition mfw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : word -> option byte) (G avail k P0 stride B n off : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 m3 m4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P0 + 16 * off)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    (* [comment removed for export] *)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
    /\ m3 = write_to_mem m1 (wa (G + 24)) (le4 (wz (avail - 2 ^ k)))
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m3 m4 /\ wmono asegs m3 m4
    (* [comment removed for export] *)
    /\ m' = enframe_tail_mem (enframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FASTMODEL.
Context {O : Type}.
Variable pans : O -> aptr -> Z -> Z -> Z.
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Let pupd : O -> ev -> Z -> O := fun o _ _ => o.
Local Notation prun := (prun pans pupd).

(* [comment removed for export] *)
Definition rdv (o : O) (st : mstate) (q : aptr) : Z :=
  match cell_read (get_shadow st (fst q)) (snd q) with
  | Known v => v
  | Unknown h => pans o q (conc st q) h
  end.

Lemma rd8_oracle {R} o st q (k : Z -> M R) : prun o (rd8 st q k) = prun o (k (rdv o st q)).
Proof.
  unfold rd8, rdv. destruct (cell_read _ _) as [v|h]; [reflexivity|].
  unfold MallocCtrl.prun. cbn [eruns psel].
  pose proof (Hpans o q (conc st q) h).
  replace (peek_answer_ok (pans o q (conc st q) h)) with true.
  2:{ symmetry. unfold peek_answer_ok. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  reflexivity.
Qed.

Lemma rd16_oracle {R} o st q (k : Z -> M R) :
  prun o (rd16 st q k) = prun o (k (rdv o st q + 256 * rdv o st (aadd q 1))).
Proof. unfold rd16. rewrite rd8_oracle, rd8_oracle. reflexivity. Qed.

Lemma land_opp_pow2' k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
  intros Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k i); cbn [andb]; [|reflexivity].
  subst. replace (i <? i) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? i); reflexivity.
Qed.
Lemma ctz32_pow2' k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2' by lia. apply Z.log2_pow2. lia. Qed.

Lemma get_meta_rec_upd_same st g f : get_meta_rec (upd_meta g f st) g = f (get_meta_rec st g).
Proof. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn. rewrite lookup_insert_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma malloc_core_fast st n g k :
  let sc := size_to_class n in
  let mr := get_meta_rec st g in
  size_overflows n = false -> n < MMAP_THRESHOLD ->
  active st sc = Some g -> 0 < m_avail mr -> 0 <= k -> lowbit (m_avail mr) = 2 ^ k ->
  malloc_core full_lay st n = ret (upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st, Some (g, k)).
Proof.
  intros sc mr OV TH ACT AV K0 LB.
  unfold malloc_core. rewrite OV. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
  unfold malloc_small_ctrl. fold sc. rewrite ACT. rewrite ACT. fold mr. rewrite LB.
  assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  replace (2 ^ k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite ctz32_pow2' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma malloc_fast_model o st n g k :
  let sc := size_to_class n in
  let st1 := set_tick (N.succ (s_tick st)) st in
  let mr := get_meta_rec st1 g in
  let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1 in
  let stride := get_stride mr in
  let slack := (stride - IB - n) / UNIT in
  let p0 := slot_start' mr k in
  let ctr := c_mmap_counter (ctx st) in
  let b3 := rdv o st2 (aadd p0 (-3)) in
  let v16 := rdv o st2 (aadd p0 (-2)) + 256 * rdv o st2 (aadd (aadd p0 (-2)) 1) in
  let off0 := (if b3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255) in
  let off := fold_off off0 slack in
  size_overflows n = false -> n < MMAP_THRESHOLD ->
  active st sc = Some g -> 0 < m_avail mr -> 0 <= k -> lowbit (m_avail mr) = 2 ^ k ->
  prun o (malloc st n) = SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)),
                                   Some (snd (enframe_at st2 g k n off)))).
Proof.
  intros sc st1 mr st2 stride slack p0 ctr b3 v16 off0 off OV TH ACT AV K0 LB.
  unfold malloc. fold st1.
  rewrite (malloc_core_fast st1 n g k OV TH ACT AV K0 LB). unfold Malloc.ret. rewrite sbind_ret_l.
  unfold enframe_full, enframe_read_off. fold st2. rewrite (get_meta_rec_upd_same st1 g). fold mr.
  set (K := fun off' : Z => let '(st3, p) := enframe_at st2 g k n off' in @SRet ev Z _ (havoc p n st3, Some p)).
  change (prun o (rd8 st2 (aadd p0 (-3)) (fun b => if negb (b =? 0)
             then rd16 st2 (aadd p0 (-2)) (fun o16 => K (fold_off (Z.land (o16 + 1) 255) slack))
             else K (fold_off (Z.land ctr 255) slack)))
          = SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)), Some (snd (enframe_at st2 g k n off))))).
  rewrite rd8_oracle. cbv beta. fold b3.
  assert (FIN : forall off', off' = off -> prun o (K off') = SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)), Some (snd (enframe_at st2 g k n off))))).
  { intros off' ->. unfold K. destruct (enframe_at st2 g k n off) as [st3 p]. reflexivity. }
  destruct (Z.eqb_spec b3 0) as [E|NE]; cbn [negb].
  - apply FIN. unfold off, off0. replace (b3 =? 0) with true by (symmetry; apply Z.eqb_eq; exact E). reflexivity.
  - rewrite rd16_oracle. cbv beta. apply FIN. unfold off, off0. replace (b3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
Qed.
End FASTMODEL.
End CEIL_WRAP_2.

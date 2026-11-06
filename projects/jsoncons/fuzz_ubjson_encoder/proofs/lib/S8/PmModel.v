(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PM.

Definition zeros_at (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

Section Model.
Variable segs : list Segment. Context {bmK : BMode}.
Variable A : pm_addrs.
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.

Inductive vstr : Type := VShort (n : Z) | VLong (cnt n p : Z).
Definition vs_size (s : vstr) : Z := match s with VShort n => n | VLong _ n _ => n end.
Definition vs_cap (s : vstr) : Z := match s with VShort _ => 22 | VLong c _ _ => c - 1 end.
Definition vs_data (o : Z) (s : vstr) : Z := match s with VShort _ => o + 1 | VLong _ _ p => p end.
Definition vs_own (s : vstr) : list (Z * Z) := match s with VShort _ => [] | VLong c _ p => [(p, c)] end.

Definition vstr_at (M : word -> option byte) (o : Z) (s : vstr) : Prop :=
  L5.defined M o 24 /\ acc M o 24 /\
  match s with
  | VShort n => 0 <= n <= 22 /\ L5.u8_at segs M o (2 * n)
  | VLong c n p => L5.u64_at segs M o (c + 1) /\ L5.u64_at segs M (o + 8) n /\ L5.u64_at segs M (o + 16) p
                   /\ 0 <= n < c /\ 26 <= c <= 2 ^ 27 /\ c mod 2 = 0 /\ L5.defined M p c /\ acc M p c
  end.

Record pstate : Type := PS { ps_mode : Z; ps_len : Z; ps_type : Z; ps_idx : Z }.
Definition ps_root : pstate := PS 0 0 0 0.
Definition MAX_ITEMS : Z := 2 ^ 24.
Definition MAX_DEPTH : Z := 1024.

Definition mode_counted (m : Z) : Prop := m = 2 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8.
Definition mode_indef (m : Z) : Prop := m = 3 \/ m = 9 \/ m = 10.
Definition mode_bottom (m : Z) : Prop := m = 0 \/ m = 1.

Definition mode_flag (m : Z) : Z := if (Z.eqb m 0 || Z.eqb m 6 || Z.eqb m 8 || Z.eqb m 10)%bool then 1 else 0.

Definition pstate_ok (s : pstate) : Prop :=
  0 <= ps_type s < 256 /\
  (   (mode_counted (ps_mode s) /\ 0 <= ps_idx s <= ps_len s /\ ps_len s <= MAX_ITEMS)
   \/ (mode_indef (ps_mode s) /\ ps_len s = 0 /\ 0 <= ps_idx s <= MAX_ITEMS)
   \/ (mode_bottom (ps_mode s) /\ ps_len s = 0 /\ ps_idx s = 0)).

Definition pstate_at (M : word -> option byte) (a : Z) (s : pstate) : Prop :=
  L5.u32_at segs M a (ps_mode s) /\ L5.u64_at segs M (a + 8) (ps_len s) /\ L5.u8_at segs M (a + 16) (ps_type s) /\ L5.u64_at segs M (a + 24) (ps_idx s).

Definition vec_at (M : word -> option byte) (v b k : Z) (stk : list pstate) : Prop :=
  L5.u64_at segs M v b /\ L5.u64_at segs M (v + 8) (b + 32 * Z.of_nat (length stk)) /\ L5.u64_at segs M (v + 16) (b + 32 * 2 ^ k)
  /\ 0 <= k <= 11 /\ Z.of_nat (length stk) <= 2 ^ k /\ b mod 16 = 0
  /\ L5.defined M b (32 * 2 ^ k) /\ acc M b (32 * Z.of_nat (length stk)) /\ ann M b (32 * Z.of_nat (length stk)) (32 * 2 ^ k)
  /\ (forall i, (i < length stk)%nat -> pstate_at M (b + 32 * Z.of_nat i) (nth i stk ps_root)).
Definition vec_own (b k : Z) : list (Z * Z) := [(b, 32 * 2 ^ k)].

Definition CHUNK : Z := 16384.
Record srcst : Type := SRC { sr_qc : Z; sr_de : Z; sr_rem : Z }.
Definition src_fields_at (M : word -> option byte) (os isp sbp : Z) (s : srcst) : Prop :=
  L5.u64_at segs M (os + 240) isp /\ L5.u64_at segs M (os + 248) sbp /\ L5.defined M (os + 256) 8
  /\ L5.u64_at segs M (os + 264) (sr_qc s) /\ L5.u64_at segs M (os + 272) CHUNK
  /\ L5.u64_at segs M (os + 280) (sr_de s) /\ L5.u64_at segs M (os + 288) (sr_rem s)
  /\ sr_qc s <= sr_de s /\ 0 <= sr_rem s /\ sr_de s + sr_rem s <= sr_qc s + CHUNK
  /\ sr_qc s mod 16 = 0 /\ L5.defined M (sr_qc s) CHUNK /\ acc M (sr_qc s) CHUNK /\ acc M (os + 240) 56.
Definition src_own (s : srcst) : list (Z * Z) := [(sr_qc s, CHUNK)].

Definition iosb_at (M : word -> option byte) (o vp rdb st : Z) : Prop :=
  L5.u64_at segs M o vp /\ L5.u32_at segs M (o + 32) st /\ L5.u32_at segs M (o + 36) 0 /\ L5.u64_at segs M (o + 40) rdb
  /\ L5.u64_at segs M (o + 48) (pa_classic_imp A) /\ zeros_at M (o + 56) 80 /\ L5.defined M o 152 /\ acc M o 152
  /\ (st = 0 \/ st = 2).

Record strm : Type := STRM { sm_g : Z; sm_eg : Z; sm_st : Z }.
Definition iss_at (M : word -> option byte) (ois : Z) (str : vstr) (s : strm) : Prop :=
  L5.u64_at segs M ois (pa_vp_iss A) /\ L5.defined M ois 120 /\ acc M ois 120
  /\ L5.u64_at segs M (ois + 16) (pa_vp_strbuf A)
  /\ L5.u64_at segs M (ois + 24) (pa_classic_imp A)
  /\ L5.u64_at segs M (ois + 32) (vs_data (ois + 80) str) /\ L5.u64_at segs M (ois + 40) (sm_g s) /\ L5.u64_at segs M (ois + 48) (sm_eg s)
  /\ L5.u64_at segs M (ois + 64) 0
  /\ vstr_at M (ois + 80) str
  /\ L5.u64_at segs M (ois + 104) (sm_eg s) /\ L5.u32_at segs M (ois + 112) 8
  /\ iosb_at M (ois + 120) (pa_vp_iss_ios A) (ois + 16) (sm_st s)
  /\ sm_eg s = vs_data (ois + 80) str + vs_size str /\ vs_data (ois + 80) str <= sm_g s <= sm_eg s.

Definition nullis_at (M : word -> option byte) (o : Z) : Prop :=
  L5.u64_at segs M o (pa_vp_nullis A) /\ L5.defined M o 80 /\ acc M o 80
  /\ L5.u64_at segs M (o + 16) (pa_vp_nullbuf A) /\ L5.u64_at segs M (o + 24) (pa_classic_imp A)
  /\ iosb_at M (o + 80) (pa_vp_nullis_ios A) (o + 16) 0.

Definition unread (src : srcst) (sm : strm) : Z := sr_rem src + (sm_eg sm - sm_g sm).

Record pst : Type := PST {
  p_more : Z; p_done : Z; p_depth : Z;
  p_src : srcst;
  p_tb : vstr;
  p_tg : Z;
  p_b : Z; p_k : Z; p_stk : list pstate
}.

Definition parser_at (M : word -> option byte) (op ois : Z) (s : pst) : Prop :=
  L5.u64_at segs M op (pa_vp_parser A) /\ L5.defined M op 384 /\ acc M op 24
  /\ L5.u8_at segs M (op + 8) (p_more s) /\ L5.u8_at segs M (op + 9) (p_done s) /\ L5.u32_at segs M (op + 12) (p_depth s)
  /\ L5.u8_at segs M (op + 16) 0 /\ L5.u32_at segs M (op + 20) 0
  /\ nullis_at M (op + 32)
  /\ src_fields_at M (op + 24) ois (ois + 16) (p_src s)
  /\ L5.u32_at segs M (op + 320) MAX_DEPTH /\ L5.u64_at segs M (op + 328) MAX_ITEMS /\ acc M (op + 320) 64
  /\ vstr_at M (op + 336) (p_tb s)
  /\ vec_at M (op + 360) (p_b s) (p_k s) (p_stk s)
  /\ (p_more s = 0 \/ p_more s = 1) /\ (p_done s = 0 \/ p_done s = 1) /\ 0 <= p_depth s <= MAX_DEPTH + 1.

Definition parser_own (s : pst) : list (Z * Z) := src_own (p_src s) ++ vec_own (p_b s) (p_k s) ++ vs_own (p_tb s).

Definition tb_law (c : Z) : Prop :=
  exists j, 0 <= j <= 13 /\ c < 2 ^ (15 + j) /\ (j = 0 \/ 2 ^ (14 + j) <= c) /\ c mod 2 ^ (3 + j) = 0.
Definition tb_ok (s : vstr) (tg : Z) : Prop :=
  0 <= tg <= 23 /\ 21 * 2 ^ tg <= vs_cap s /\
  match s with VShort _ => tg = 0 | VLong c _ _ => tb_law c /\ 1 <= tg end.

Definition stack_shape (stk : list pstate) : Prop :=
  (1 <= length stk)%nat /\ Z.of_nat (length stk) <= MAX_DEPTH + 1
  /\ mode_bottom (ps_mode (nth 0 stk ps_root))
  /\ (forall i, (1 <= i < length stk)%nat -> ~ mode_bottom (ps_mode (nth i stk ps_root)))
  /\ (forall i, (i < length stk)%nat -> pstate_ok (nth i stk ps_root)).

Definition inv (s : pst) : Prop :=
  p_more s = 1 /\ p_done s = 0 /\ p_depth s = Z.of_nat (length (p_stk s)) - 1 /\ stack_shape (p_stk s) /\ tb_ok (p_tb s) (p_tg s).

Definition inv_d (d : Z) (s : pst) : Prop :=
  p_more s = 1 /\ p_done s = 0 /\ p_depth s = Z.of_nat (length (p_stk s)) - 1 + d /\ stack_shape (p_stk s) /\ tb_ok (p_tb s) (p_tg s).
Lemma inv_d0 s : inv s <-> inv_d 0 s.
Proof. unfold inv, inv_d. rewrite Z.add_0_r. reflexivity. Qed.

Definition ps_weight (s : pstate) : Z := ps_len s - ps_idx s.
Definition stk_weight (stk : list pstate) : Z := fold_right (fun s w => ps_weight s + w) 0 stk.
Definition top_flag (stk : list pstate) : Z := mode_flag (ps_mode (last stk ps_root)).
Definition mu (s : pst) (sm : strm) : Z :=
  (unread (p_src s) sm * 2 ^ 35 + stk_weight (p_stk s)) * 4096 + 2 * Z.of_nat (length (p_stk s)) + top_flag (p_stk s).

Definition mu_src (src : srcst) (sm : strm) : Z := 2 * unread src sm + (if Z.eqb (sm_st sm) 0 then 1 else 0).

Definition pot_stack (L : heap_layout) (k : Z) : credit :=
  (hl_k_per_malloc L * (11 - k), 32 * (2 ^ 12 - 2 ^ (k + 1)) + (11 - k) * hl_b_overhead L).
Definition pot_text (L : heap_layout) (s : vstr) (tg : Z) : credit :=
  (hl_k_per_malloc L * (23 - tg), (2 ^ 28 + 64 - 2 * vs_cap s - tg) + (23 - tg) * hl_b_overhead L).
Definition credit_add (c d : credit) : credit := (fst c + fst d, snd c + snd d).
Definition pot_parser (L : heap_layout) (s : pst) : credit := credit_add (pot_stack L (p_k s)) (pot_text L (p_tb s) (p_tg s)).

Definition cost1 (L : heap_layout) (n : Z) : credit := (hl_k_per_malloc L, n + hl_b_overhead L).

Definition pot_call (L : heap_layout) (n : Z) : credit :=
  credit_add (credit_add (cost1 L (n + 16)) (cost1 L (n + 32)))
    (credit_add (credit_add (cost1 L CHUNK) (cost1 L 32)) (credit_add (pot_stack L 0) (pot_text L (VShort 0) 0))).

End Model.

Lemma pow2_pos k : 0 <= k -> 0 < 2 ^ k.
Proof. intros H. apply Z.pow_pos_nonneg; lia. Qed.

Lemma tb_law_request c need :
  tb_law c -> 26 <= c -> c - 1 < need -> need < 2 ^ 26 + 16384 -> need <= c - 1 + 16384 ->
  Z.max (2 * (c - 1)) need < 2 ^ 27.
Proof.
  intros (j & Hj & Hlt & Hlo & Hmod) Hc Hgrow Hneed Hstep.
  assert (Hc26 : c <= 2 ^ 26).
  { destruct (Z_le_gt_dec c (2 ^ 26)) as [Hle|Hgt]; [exact Hle|exfalso].
    assert (Hj12 : 12 <= j).
    { destruct (Z_le_gt_dec 12 j) as [H|H]; [exact H|exfalso].
      assert (2 ^ (15 + j) <= 2 ^ 26) by (apply Z.pow_le_mono_r; lia). lia. }
    assert (Hd : (2 ^ 15 | 2 ^ (3 + j))).
    { exists (2 ^ (j - 12)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Hm15 : c mod 2 ^ 15 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.divide_trans with (2 ^ (3 + j)); [exact Hd|]. apply Z.mod_divide; [pose proof (pow2_pos (3 + j)); lia| exact Hmod]. }
    apply Z.mod_divide in Hm15; [|lia]. destruct Hm15 as (q & Hq).
    change (2 ^ 15) with 32768 in Hq. change (2 ^ 26) with 67108864 in *. lia. }
  change (2 ^ 26) with 67108864 in *. change (2 ^ 27) with 134217728. lia.
Qed.

End PM.

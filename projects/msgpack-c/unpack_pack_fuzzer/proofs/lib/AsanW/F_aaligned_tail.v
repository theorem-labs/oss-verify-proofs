(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase ABytes ADepot_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKit AKit2 AModelFacts APrimFacts.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc_s.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aunwind.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc F_amalloc_iseg F_amalloc_icpt.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aaligned_iseg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module F_aaligned_tail.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1_16.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2g_16.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3g_16. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_iseg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

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
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Section CANSEC1. Context {rc : runConstT}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.

Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148261376 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
Lemma hdr_b1_mid16_range : forall b1, 0 <= b1 -> 0 <= hdr_b1_mid16 b1 < 256.
Proof.
  intros b1 Hb. unfold hdr_b1_mid16.
  set (x := Z.lor (Z.land b1 18446744073709551612) 1).
  assert (X0 : 0 <= x) by (subst x; apply Z.lor_nonneg; split; [apply Z.land_nonneg; left; lia| lia]).
  assert (A0 : 0 <= Z.land x 143) by (apply Z.land_nonneg; right; lia).
  split. { apply Z.lor_nonneg. lia. }
  change 256 with (2^8). apply lt_pow2_of_log2. { apply Z.lor_nonneg; lia. }
  rewrite Z.log2_lor by lia.
  pose proof (Z.log2_land x 143 X0 ltac:(lia)) as L1.
  replace (Z.log2 143) with 7 in L1 by reflexivity. replace (Z.log2 32) with 5 by reflexivity. lia.
Qed.
Section WithDepot.
Variable DI : ADepotIface.

Notation malloc_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (t + 3168, t + 3169); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition aligned_post_gen16 (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word) (stj' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (malloc_W L sp t c AB UB PG pgw n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ rw_cells asegs m' (t + 2784) [C8 stj']
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land (hdr_b1_mid16 b1) 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Lemma aligned_tail_gen16 : forall (L : alayout) RNG (ra sp gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s6A s0i s1i s2i : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 junk0 junk2 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  bv_unsigned spA = bv_unsigned sp - 2176 ->
  stk asegs m lo (bv_unsigned sp - 2304) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary16 n = true ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xd730d [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xd2170 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m 0x60cc90 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x16b580 [C8 (Z_to_bv 64 0)] ->

  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  class_id (needed16 n) = c ->
  rw_cells asegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz] ->
  rw_cells asegs m (t + 2784) [C8 stj] ->

  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed16 n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed16 n <= size_of_class (class_id (needed16 n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->

  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->

  rw_cells asegs m (bv_unsigned sp - 2304)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 32); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6A; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x3d8a8)] ->
  rw_cells asegs m (bv_unsigned sp + -2176) [C8 s2i; C8 s1i; C8 s0i; C8 (Z_to_bv 64 0x5ec68)] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [CB 8 junk0] ->
  rw_cells asegs m (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (bv_unsigned sp + -2136 + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = AALIGNED_PC :: tr ->
  In (AALIGNED_PC :: tr) (al_U L) -> bv_unsigned sp < 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ADEPOT DI L m ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
  evtF asegs RNG (aligned_post_gen16 L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m)
    (MS (mkR (Z_to_bv 64 0x3cf68) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 16) (Z_to_bv 64 (needed16 n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (-16)) (Z_to_bv 64 15) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x3cf68) fc None m (seg_rom asegs)).
Proof.
  intros until tr. cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS DTN DTS DCN DCS N0 N1 R0 R1 FRa FR16 FRP0 SS SZ SZB TB LTB TRF TRU S47 FRS DEP
         RIMG RSTK RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.
  unfold AIMG_HI in CX0, NI, SI.
  destruct (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) as (kT & TBND & TBNDa & TBNDb).
  destruct (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) as (kC & CBND & CBNDa & CBNDb).
  destruct (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) as (kN & NBND & NBNDa & NBNDb).
  destruct (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) as (kR & SBND & SBNDa & SBNDb).
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  pose proof (prim16_facts' n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts16 n c N PRIM HC) as (C16 & NSZ2 & SM16 & SMALL & MC2).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, AALIGNED_PC in *.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.

  replace (bv_unsigned sp - 2304) with (bv_unsigned spA + -128) in ST, FRa by lia.

  eapply evtF_cut.
  { eapply (allocBC_gen16 DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n (bv_unsigned sp + -2136) t AB UB PG pgw lo b0 b1 szh szl ctxj sz 388088 pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- poison_cells _ => exact PC
         | |- ADEPOT _ _ _ => exact DEP
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP
         | |- _ -> rw_cells _ _ _ _ => exact LH
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_postG16 in PB.
  destruct PB as (id & raB & t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & s6b & t3b & t4b & t5b & t6b & m2
                  & -> & MUb & WMb & MIb & STb & IDR & HDRb & SHUb & SHPb & DEPb).
  rewrite ?HspA in MUb.

  xport FRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport STATS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport TI MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport T88 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TSD MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport CT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJC; ub DCN; ub DCS; lia).
  xport FLG MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport HK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport MCS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport CF34 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  pose proof PC as PC'. destruct PC' as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  xport GOT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport GOT80 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport REAL MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport PC4 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport PC5 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport UJ MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJN; ub DJS; lia).
  xport CRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia). xport STSa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport UW MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport FR16 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport SS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport FRS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport FRP0 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport TB MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs m2 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). pose proof (rz_size_cases n) as RZC.
    xport LH MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS RZ RZC; ub DJN; ub DJS; lia). exact LH. }
  clear LH SHP.
  pose proof (hdr_b1_mid16_range b1 ltac:(lia)) as B1M.

  eapply evtF_cut.
  { eapply (allocD_gen16 L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid16 b1) id (bv_unsigned sp + -2136) sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  destruct PD as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m3 & sj3
                  & -> & MUd & WMd & MId & STd & STATSd & LSJd & UFd & HDRd & LHd).
  rewrite ?HspA in MUd.
  xport CRa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia). xport STSa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport SHUb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport UW MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport FR16 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport SS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport FRS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TB MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  xport FRP0 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells asegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }

  replace (ret_pc (Z_to_bv 64 0x3d8a8)) with (Z_to_bv 64 0x3d8a8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2176)).
  { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2176)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
    apply Z_to_bv_eqm. rewrite HspA. zeq. }
  rewrite EspA. rewrite HspA in STd. replace (bv_unsigned sp - 2176) with (bv_unsigned sp + -2176) in STd by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { eapply (icptC16_spec RNG sp gp tp); [exact STd | atop_facts; lia | lia | exact MId | atop_facts; lia | exact FR16
      | eexists; split; [exact FRP0 | reflexivity]
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | solve_rng ]. }
  cbv beta. intros ms5 PCC. destruct PCC as (m5 & -> & MUc & WMc & MIc & STc).

  xport CRa MUc WMc ltac:(exact I). xport STSa MUc WMc ltac:(exact I). xport STATSd MUc WMc ltac:(exact I).
  xport HDRd MUc WMc ltac:(exact I). xport UFd MUc WMc ltac:(exact I). xport SHUb MUc WMc ltac:(exact I). xport UW MUc WMc ltac:(exact I).
  assert (LH5 : 16 < rz_size n -> rw_cells asegs m5 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. specialize (LH4 RZ). xport LH4 MUc WMc ltac:(exact I). exact LH4. }
  assert (SHP5 : n mod 8 <> 0 -> rw_cells asegs m5 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(exact I). exact SHPd. }
  assert (DEP5 : ADEPOT DI L m5). { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (malloc_W L sp t c AB UB PG pgw n) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01 HspA; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }
  assert (WM : wmono asegs m m5).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  unfold aligned_post_gen16. exists id. do 14 eexists. exists m5, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LH5|]. split; [exact SHUb|]. split; [exact SHP5|]. exact DEP5.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End WithDepot.
End CANSEC1.

End F_aaligned_tail.

Module F_amalloc_tailg.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3g.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

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
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Section CANSEC1. Context {rc : runConstT}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.

Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148261376 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
Section WithDepot.
Variable DI : ADepotIface.

Notation malloc_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (t + 3168, t + 3169); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition malloc_post_gen (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word) (stj' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (malloc_W L sp t c AB UB PG pgw n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ rw_cells asegs m' (t + 2784) [C8 stj']
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land (hdr_b1_mid b1) 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Lemma malloc_tail_gen : forall (L : alayout) RNG (ra sp gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 junk2 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  bv_unsigned spA = bv_unsigned sp - 2144 ->
  stk asegs m lo (bv_unsigned sp - 2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xd730d [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xd2170 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m 0x60cc90 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x16b580 [C8 (Z_to_bv 64 0)] ->

  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  class_id (needed_size n) = c ->
  rw_cells asegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz] ->
  rw_cells asegs m (t + 2784) [C8 stj] ->

  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->

  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->

  rw_cells asegs m (bv_unsigned sp - 2272)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x3cc98)] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x5e728)] ->
  rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = AMALLOC_PC :: tr ->
  In (AMALLOC_PC :: tr) (al_U L) -> bv_unsigned sp < 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ADEPOT DI L m ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
  evtF asegs RNG (malloc_post_gen L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m)
    (MS (mkR (Z_to_bv 64 0x3cf68) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x3cf68) fc None m (seg_rom asegs)).
Proof.
  intros until tr. cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS DTN DTS DCN DCS N0 N1 R0 R1 FRa FR16 SS SZ SZB TB LTB TRF TRU S47 FRS DEP
         RIMG RSTK RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.
  unfold AIMG_HI in CX0, NI, SI.
  destruct (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) as (kT & TBND & TBNDa & TBNDb).
  destruct (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) as (kC & CBND & CBNDa & CBNDb).
  destruct (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) as (kN & NBND & NBNDa & NBNDb).
  destruct (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) as (kR & SBND & SBNDa & SBNDb).
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N PRIM HC) as (C16 & NSZ2 & SM16 & SMALL & MC2).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, AMALLOC_PC in *.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.

  replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in ST, FRa by lia.

  eapply evtF_cut.
  { eapply (allocBC_gen DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n (bv_unsigned sp + -2128) t AB UB PG pgw lo b0 b1 szh szl ctxj sz 386748 pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- poison_cells _ => exact PC
         | |- ADEPOT _ _ _ => exact DEP
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP
         | |- _ -> rw_cells _ _ _ _ => exact LH
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_postG in PB.
  destruct PB as (id & raB & t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & s6b & t3b & t4b & t5b & t6b & m2
                  & -> & MUb & WMb & MIb & STb & IDR & HDRb & SHUb & SHPb & DEPb).
  rewrite ?HspA in MUb.

  xport FRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport STATS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport TI MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport T88 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TSD MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport CT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJC; ub DCN; ub DCS; lia).
  xport FLG MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport HK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport MCS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport CF34 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  pose proof PC as PC'. destruct PC' as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  xport GOT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport GOT80 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport REAL MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport PC4 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport PC5 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport UJ MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJN; ub DJS; lia).
  xport CRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia). xport STSa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport UW MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport FR16 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport SS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport FRS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport TB MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs m2 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). pose proof (rz_size_cases n) as RZC.
    xport LH MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS RZ RZC; ub DJN; ub DJS; lia). exact LH. }
  clear LH SHP.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.

  eapply evtF_cut.
  { eapply (allocD_gen L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid b1) id (bv_unsigned sp + -2128) sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  destruct PD as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m3 & sj3
                  & -> & MUd & WMd & MId & STd & STATSd & LSJd & UFd & HDRd & LHd).
  rewrite ?HspA in MUd.
  xport CRa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia). xport STSa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport SHUb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport UW MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport FR16 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport SS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport FRS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TB MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells asegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }

  replace (ret_pc (Z_to_bv 64 0x3cc98)) with (Z_to_bv 64 0x3cc98) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2144)).
  { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2144)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
    apply Z_to_bv_eqm. rewrite HspA. zeq. }
  rewrite EspA. rewrite HspA in STd. replace (bv_unsigned sp - 2144) with (bv_unsigned sp + -2144) in STd by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { eapply (icptC_spec RNG sp gp tp); [exact STd | atop_facts; lia | lia | exact MId | atop_facts; lia | exact FR16
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | solve_rng ]. }
  cbv beta. intros ms5 PCC. destruct PCC as (m5 & -> & MUc & WMc & MIc & STc).

  xport CRa MUc WMc ltac:(exact I). xport STSa MUc WMc ltac:(exact I). xport STATSd MUc WMc ltac:(exact I).
  xport HDRd MUc WMc ltac:(exact I). xport UFd MUc WMc ltac:(exact I). xport SHUb MUc WMc ltac:(exact I). xport UW MUc WMc ltac:(exact I).
  assert (LH5 : 16 < rz_size n -> rw_cells asegs m5 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. specialize (LH4 RZ). xport LH4 MUc WMc ltac:(exact I). exact LH4. }
  assert (SHP5 : n mod 8 <> 0 -> rw_cells asegs m5 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(exact I). exact SHPd. }
  assert (DEP5 : ADEPOT DI L m5). { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (malloc_W L sp t c AB UB PG pgw n) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01 HspA; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }
  assert (WM : wmono asegs m m5).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  unfold malloc_post_gen. exists id. do 14 eexists. exists m5, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LH5|]. split; [exact SHUb|]. split; [exact SHP5|]. exact DEP5.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End WithDepot.
End CANSEC1.

End F_amalloc_tailg.

Module F_aallocate_tailg.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3g.
Import F_amalloc_tailg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

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
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Section CANSEC1. Context {rc : runConstT}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.

Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148261376 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
Section WithDepot.
Variable DI : ADepotIface.

Notation malloc_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (t + 3168, t + 3169); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Lemma alloc_tail_D : forall (L : alayout) RNG (ra gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz S pc : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  stk asegs m lo (bv_unsigned spA + -128) -> ATOP <= lo -> lo <= bv_unsigned spA - 1952 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xd730d [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xd2170 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m 0x60cc90 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x16b580 [C8 (Z_to_bv 64 0)] ->

  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  class_id (needed_size n) = c ->
  rw_cells asegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz] ->
  rw_cells asegs m (t + 2784) [C8 stj] ->

  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->

  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->

  rw_cells asegs m (bv_unsigned spA + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5;
      C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned spA < 2^47 ->
  bv_unsigned spA <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned spA - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  rng RNG S 2056 ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
  evtF asegs RNG (malloc_post_gen DI L ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m)
    (MS (mkR (Z_to_bv 64 0x3cf68) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x3cf68) fc None m (seg_rom asegs)).
Proof.
  intros until tr. cbv zeta.
  intros ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS DTN DTS DCN DCS N0 N1 R0 R1 FRa SS SZ SZB TB LTB TRF TRU S47 SPS STOP DEP
         RIMG RSTK RCTX RT RNO RST RU RAB RSA RSU RSP RS NI SI. band_lin.
  unfold AIMG_HI in CX0, NI, SI.
  destruct (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) as (kT & TBND & TBNDa & TBNDb).
  destruct (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) as (kC & CBND & CBNDa & CBNDb).
  destruct (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) as (kN & NBND & NBNDa & NBNDb).
  destruct (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) as (kR & SBND & SBNDa & SBNDb).
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N PRIM HC) as (C16 & NSZ2 & SM16 & SMALL & MC2).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM in *.
  word_range spA SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.

  eapply evtF_cut.
  { eapply (allocBC_gen DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- poison_cells _ => exact PC
         | |- ADEPOT _ _ _ => exact DEP
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP
         | |- _ -> rw_cells _ _ _ _ => exact LH
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_postG in PB.
  destruct PB as (id & raB & t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & s6b & t3b & t4b & t5b & t6b & m2
                  & -> & MUb & WMb & MIb & STb & IDR & HDRb & SHUb & SHPb & DEPb).

  xport FRa MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport STATS MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport TI MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TK MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport T88 MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TSD MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport CT MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJC; ub DCN; ub DCS; lia).
  xport FLG MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport HK MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport MCS MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport CF34 MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  pose proof PC as PC'. destruct PC' as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  xport GOT MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport GOT80 MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport REAL MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport PC4 MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport PC5 MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport UJ MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJN; ub DJS; lia).
  xport CRa MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia). xport STSa MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport UW MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs m2 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). pose proof (rz_size_cases n) as RZC.
    xport LH MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS RZ RZC; ub DJN; ub DJS; lia). exact LH. }
  clear LH SHP.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.

  eapply evtF_cut.
  { eapply (allocD_gen L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid b1) id S sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  destruct PD as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m3 & sj3
                  & -> & MUd & WMd & MId & STd & STATSd & LSJd & UFd & HDRd & LHd).
  xport CRa MUd WMd ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia). xport STSa MUd WMd ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport SHUb MUd WMd ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport UW MUd WMd ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells asegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }

  apply evtF_done.
  assert (MU : munch (malloc_W L spA t c AB UB PG pgw n) m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }
  assert (WM : wmono asegs m m3) by (eapply wmono_trans; [exact WMb| exact WMd]).
  unfold malloc_post_gen. exists id. do 14 eexists. exists m3, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LH4|]. split; [exact SHUb|]. split; [exact SHPd|]. exact DEPd.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End WithDepot.
End CANSEC1.
End F_aallocate_tailg.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.

Module F_aaligned_tail.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1_16.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2g_16.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3g_16. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_iseg.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

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
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Section CANSEC1. Context {rc : runConstT}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.

Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148262400 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
Lemma hdr_b1_mid16_range : forall b1, 0 <= b1 -> 0 <= hdr_b1_mid16 b1 < 256.
Proof.
  intros b1 Hb. unfold hdr_b1_mid16.
  set (x := Z.lor (Z.land b1 18446744073709551612) 1).
  assert (X0 : 0 <= x) by (subst x; apply Z.lor_nonneg; split; [apply Z.land_nonneg; left; lia| lia]).
  assert (A0 : 0 <= Z.land x 143) by (apply Z.land_nonneg; right; lia).
  split. { apply Z.lor_nonneg. lia. }
  change 256 with (2^8). apply lt_pow2_of_log2. { apply Z.lor_nonneg; lia. }
  rewrite Z.log2_lor by lia.
  pose proof (Z.log2_land x 143 X0 ltac:(lia)) as L1.
  replace (Z.log2 143) with 7 in L1 by reflexivity. replace (Z.log2 32) with 5 by reflexivity. lia.
Qed.
Section WithDepot.
Variable DI : ADepotIface.

Notation malloc_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (t + 3168, t + 3169); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition aligned_post_gen16 (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word) (stj' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (malloc_W L sp t c AB UB PG pgw n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells bsegs m' (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ rw_cells bsegs m' (t + 2784) [C8 stj']
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land (hdr_b1_mid16 b1) 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
    /\ (16 < rz_size n -> rw_cells bsegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Lemma aligned_tail_gen16 : forall (L : alayout) RNG (ra sp gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s6A s0i s1i s2i : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 junk0 junk2 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  bv_unsigned spA = bv_unsigned sp - 2176 ->
  stk bsegs m lo (bv_unsigned sp - 2304) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary16 n = true ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0xd94cd [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0xd4288 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x60ee50 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x16d740 [C8 (Z_to_bv 64 0)] ->

  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  class_id (needed16 n) = c ->
  rw_cells bsegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz] ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->

  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed16 n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed16 n <= size_of_class (class_id (needed16 n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells bsegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells bsegs m AB [C8 j1; C8 j2]) ->
  rw_cells bsegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells bsegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells bsegs m PG [C1 pj]) ->

  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->

  rw_cells bsegs m (bv_unsigned sp - 2304)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 32); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6A; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x3e238)] ->
  rw_cells bsegs m (bv_unsigned sp + -2176) [C8 s2i; C8 s1i; C8 s0i; C8 (Z_to_bv 64 0x5f5f8)] ->
  rw_cells bsegs m (bv_unsigned sp + -2144) [CB 8 junk0] ->
  rw_cells bsegs m (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr bsegs m (bv_unsigned sp + -2136 + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = AALIGNED_PC :: tr ->
  In (AALIGNED_PC :: tr) (al_U L) -> bv_unsigned sp < 2^47 ->
  rw_cells bsegs m (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ADEPOT DI L m ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
  evtF bsegs RNG (aligned_post_gen16 L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m)
    (MS (mkR (Z_to_bv 64 0x3d8f8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 16) (Z_to_bv 64 (needed16 n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (-16)) (Z_to_bv 64 15) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d8f8) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS DTN DTS DCN DCS N0 N1 R0 R1 FRa FR16 FRP0 SS SZ SZB TB LTB TRF TRU S47 FRS DEP
         RIMG RSTK RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.
  unfold AIMG_HI in CX0, NI, SI.
  destruct (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) as (kT & TBND & TBNDa & TBNDb).
  destruct (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) as (kC & CBND & CBNDa & CBNDb).
  destruct (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) as (kN & NBND & NBNDa & NBNDb).
  destruct (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) as (kR & SBND & SBNDa & SBNDb).
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  pose proof (prim16_facts' n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts16 n c N PRIM HC) as (C16 & NSZ2 & SM16 & SMALL & MC2).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, AALIGNED_PC in *.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.

  replace (bv_unsigned sp - 2304) with (bv_unsigned spA + -128) in ST, FRa by lia.

  eapply evtF_cut.
  { eapply (allocBC_gen16 DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n (bv_unsigned sp + -2136) t AB UB PG pgw lo b0 b1 szh szl ctxj sz 390536 pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- poison_cells _ => exact PC
         | |- ADEPOT _ _ _ => exact DEP
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP
         | |- _ -> rw_cells _ _ _ _ => exact LH
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_postG16 in PB.
  destruct PB as (id & raB & t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & s6b & t3b & t4b & t5b & t6b & m2
                  & -> & MUb & WMb & MIb & STb & IDR & HDRb & SHUb & SHPb & DEPb).
  rewrite ?HspA in MUb.

  xport FRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport STATS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport TI MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport T88 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TSD MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport CT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJC; ub DCN; ub DCS; lia).
  xport FLG MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport HK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport MCS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport CF34 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  pose proof PC as PC'. destruct PC' as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  xport GOT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport GOT80 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport REAL MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport PC4 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport PC5 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport UJ MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJN; ub DJS; lia).
  xport CRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia). xport STSa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport UW MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport FR16 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport SS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport FRS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport FRP0 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport TB MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells bsegs m2 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). pose proof (rz_size_cases n) as RZC.
    xport LH MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS RZ RZC; ub DJN; ub DJS; lia). exact LH. }
  clear LH SHP.
  pose proof (hdr_b1_mid16_range b1 ltac:(lia)) as B1M.

  eapply evtF_cut.
  { eapply (allocD_gen16 L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid16 b1) id (bv_unsigned sp + -2136) sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  destruct PD as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m3 & sj3
                  & -> & MUd & WMd & MId & STd & STATSd & LSJd & UFd & HDRd & LHd).
  rewrite ?HspA in MUd.
  xport CRa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia). xport STSa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport SHUb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport UW MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport FR16 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport SS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport FRS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TB MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  xport FRP0 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells bsegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells bsegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }

  replace (ret_pc (Z_to_bv 64 0x3e238)) with (Z_to_bv 64 0x3e238) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2176)).
  { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2176)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
    apply Z_to_bv_eqm. rewrite HspA. zeq. }
  rewrite EspA. rewrite HspA in STd. replace (bv_unsigned sp - 2176) with (bv_unsigned sp + -2176) in STd by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { eapply (icptC16_spec RNG sp gp tp); [exact STd | atop_facts; lia | lia | exact MId | atop_facts; lia | exact FR16
      | eexists; split; [exact FRP0 | reflexivity]
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | solve_rng ]. }
  cbv beta. intros ms5 PCC. destruct PCC as (m5 & -> & MUc & WMc & MIc & STc).

  xport CRa MUc WMc ltac:(exact I). xport STSa MUc WMc ltac:(exact I). xport STATSd MUc WMc ltac:(exact I).
  xport HDRd MUc WMc ltac:(exact I). xport UFd MUc WMc ltac:(exact I). xport SHUb MUc WMc ltac:(exact I). xport UW MUc WMc ltac:(exact I).
  assert (LH5 : 16 < rz_size n -> rw_cells bsegs m5 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. specialize (LH4 RZ). xport LH4 MUc WMc ltac:(exact I). exact LH4. }
  assert (SHP5 : n mod 8 <> 0 -> rw_cells bsegs m5 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(exact I). exact SHPd. }
  assert (DEP5 : ADEPOT DI L m5). { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (malloc_W L sp t c AB UB PG pgw n) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01 HspA; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }
  assert (WM : wmono bsegs m m5).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  unfold aligned_post_gen16. exists id. do 14 eexists. exists m5, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LH5|]. split; [exact SHUb|]. split; [exact SHP5|]. exact DEP5.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End WithDepot.
End CANSEC1.

End F_aaligned_tail.

Module F_amalloc_tailg.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3g.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

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
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Section CANSEC1. Context {rc : runConstT}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.

Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148262400 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
Section WithDepot.
Variable DI : ADepotIface.

Notation malloc_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (t + 3168, t + 3169); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition malloc_post_gen (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word) (stj' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (malloc_W L sp t c AB UB PG pgw n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells bsegs m' (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ rw_cells bsegs m' (t + 2784) [C8 stj']
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land (hdr_b1_mid b1) 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
    /\ (16 < rz_size n -> rw_cells bsegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Lemma malloc_tail_gen : forall (L : alayout) RNG (ra sp gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 junk2 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  bv_unsigned spA = bv_unsigned sp - 2144 ->
  stk bsegs m lo (bv_unsigned sp - 2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0xd94cd [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0xd4288 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x60ee50 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x16d740 [C8 (Z_to_bv 64 0)] ->

  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  class_id (needed_size n) = c ->
  rw_cells bsegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz] ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->

  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells bsegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells bsegs m AB [C8 j1; C8 j2]) ->
  rw_cells bsegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells bsegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells bsegs m PG [C1 pj]) ->

  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->

  rw_cells bsegs m (bv_unsigned sp - 2272)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x3d628)] ->
  rw_cells bsegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x5f0b8)] ->
  rw_cells bsegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr bsegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = AMALLOC_PC :: tr ->
  In (AMALLOC_PC :: tr) (al_U L) -> bv_unsigned sp < 2^47 ->
  rw_cells bsegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ADEPOT DI L m ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
  evtF bsegs RNG (malloc_post_gen L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m)
    (MS (mkR (Z_to_bv 64 0x3d8f8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d8f8) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS DTN DTS DCN DCS N0 N1 R0 R1 FRa FR16 SS SZ SZB TB LTB TRF TRU S47 FRS DEP
         RIMG RSTK RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.
  unfold AIMG_HI in CX0, NI, SI.
  destruct (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) as (kT & TBND & TBNDa & TBNDb).
  destruct (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) as (kC & CBND & CBNDa & CBNDb).
  destruct (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) as (kN & NBND & NBNDa & NBNDb).
  destruct (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) as (kR & SBND & SBNDa & SBNDb).
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N PRIM HC) as (C16 & NSZ2 & SM16 & SMALL & MC2).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, AMALLOC_PC in *.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.

  replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in ST, FRa by lia.

  eapply evtF_cut.
  { eapply (allocBC_gen DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n (bv_unsigned sp + -2128) t AB UB PG pgw lo b0 b1 szh szl ctxj sz 389196 pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- poison_cells _ => exact PC
         | |- ADEPOT _ _ _ => exact DEP
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP
         | |- _ -> rw_cells _ _ _ _ => exact LH
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_postG in PB.
  destruct PB as (id & raB & t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & s6b & t3b & t4b & t5b & t6b & m2
                  & -> & MUb & WMb & MIb & STb & IDR & HDRb & SHUb & SHPb & DEPb).
  rewrite ?HspA in MUb.

  xport FRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport STATS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport TI MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport T88 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TSD MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport CT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJC; ub DCN; ub DCS; lia).
  xport FLG MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport HK MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport MCS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport CF34 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  pose proof PC as PC'. destruct PC' as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  xport GOT MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport GOT80 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport REAL MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport PC4 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport PC5 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport UJ MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJN; ub DJS; lia).
  xport CRa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia). xport STSa MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport UW MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport FR16 MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport SS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport FRS MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport TB MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells bsegs m2 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). pose proof (rz_size_cases n) as RZC.
    xport LH MUb WMb ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS RZ RZC; ub DJN; ub DJS; lia). exact LH. }
  clear LH SHP.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.

  eapply evtF_cut.
  { eapply (allocD_gen L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid b1) id (bv_unsigned sp + -2128) sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  destruct PD as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m3 & sj3
                  & -> & MUd & WMd & MId & STd & STATSd & LSJd & UFd & HDRd & LHd).
  rewrite ?HspA in MUd.
  xport CRa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia). xport STSa MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport SHUb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport UW MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport FR16 MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport SS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport FRS MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TB MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; rewrite LTB; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells bsegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells bsegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha HspA SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }

  replace (ret_pc (Z_to_bv 64 0x3d628)) with (Z_to_bv 64 0x3d628) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2144)).
  { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2144)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
    apply Z_to_bv_eqm. rewrite HspA. zeq. }
  rewrite EspA. rewrite HspA in STd. replace (bv_unsigned sp - 2144) with (bv_unsigned sp + -2144) in STd by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { eapply (icptC_spec RNG sp gp tp); [exact STd | atop_facts; lia | lia | exact MId | atop_facts; lia | exact FR16
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG | solve_rng ]. }
  cbv beta. intros ms5 PCC. destruct PCC as (m5 & -> & MUc & WMc & MIc & STc).

  xport CRa MUc WMc ltac:(exact I). xport STSa MUc WMc ltac:(exact I). xport STATSd MUc WMc ltac:(exact I).
  xport HDRd MUc WMc ltac:(exact I). xport UFd MUc WMc ltac:(exact I). xport SHUb MUc WMc ltac:(exact I). xport UW MUc WMc ltac:(exact I).
  assert (LH5 : 16 < rz_size n -> rw_cells bsegs m5 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. specialize (LH4 RZ). xport LH4 MUc WMc ltac:(exact I). exact LH4. }
  assert (SHP5 : n mod 8 <> 0 -> rw_cells bsegs m5 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(exact I). exact SHPd. }
  assert (DEP5 : ADEPOT DI L m5). { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (malloc_W L sp t c AB UB PG pgw n) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01 HspA; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }
  assert (WM : wmono bsegs m m5).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  unfold malloc_post_gen. exists id. do 14 eexists. exists m5, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LH5|]. split; [exact SHUb|]. split; [exact SHP5|]. exact DEP5.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End WithDepot.
End CANSEC1.

End F_amalloc_tailg.

Module F_aallocate_tailg.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc_s.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3g.
Import F_amalloc_tailg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

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
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Section CANSEC1. Context {rc : runConstT}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.

Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148262400 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
Section WithDepot.
Variable DI : ADepotIface.

Notation malloc_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (t + 3168, t + 3169); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Lemma alloc_tail_D : forall (L : alayout) RNG (ra gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t c cnt AB UB PG pgw lo b0 b1 szh szl ctxj sz S pc : Z) (maxc csz stj j1 j2 : word) (pj : byte)
    (sj : list word) (sjunk uj fr0 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  stk bsegs m lo (bv_unsigned spA + -128) -> ATOP <= lo -> lo <= bv_unsigned spA - 1952 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->

  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0xd94cd [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0xd4288 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x60ee50 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x16d740 [C8 (Z_to_bv 64 0)] ->

  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->

  class_id (needed_size n) = c ->
  rw_cells bsegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz] ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->

  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells bsegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells bsegs m AB [C8 j1; C8 j2]) ->
  rw_cells bsegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells bsegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells bsegs m PG [C1 pj]) ->

  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->

  rw_cells bsegs m (bv_unsigned spA + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5;
      C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr bsegs m (S + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned spA < 2^47 ->
  bv_unsigned spA <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned spA - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  rng RNG S 2056 ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
  evtF bsegs RNG (malloc_post_gen DI L ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m)
    (MS (mkR (Z_to_bv 64 0x3d8f8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d8f8) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. cbv zeta.
  intros ST CEIL LO MI TP N PRIM AC PC PP FLG HK MCS CF34 CX8 TT0 UW STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CRa STSa HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS DTN DTS DCN DCS N0 N1 R0 R1 FRa SS SZ SZB TB LTB TRF TRU S47 SPS STOP DEP
         RIMG RSTK RCTX RT RNO RST RU RAB RSA RSU RSP RS NI SI. band_lin.
  unfold AIMG_HI in CX0, NI, SI.
  destruct (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) as (kT & TBND & TBNDa & TBNDb).
  destruct (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) as (kC & CBND & CBNDa & CBNDb).
  destruct (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) as (kN & NBND & NBNDa & NBNDb).
  destruct (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) as (kR & SBND & SBNDa & SBNDb).
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N PRIM HC) as (C16 & NSZ2 & SM16 & SMALL & MC2).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM in *.
  word_range spA SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.

  eapply evtF_cut.
  { eapply (allocBC_gen DI L RNG spA gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- poison_cells _ => exact PC
         | |- ADEPOT _ _ _ => exact DEP
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP
         | |- _ -> rw_cells _ _ _ _ => exact LH
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_postG in PB.
  destruct PB as (id & raB & t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & s6b & t3b & t4b & t5b & t6b & m2
                  & -> & MUb & WMb & MIb & STb & IDR & HDRb & SHUb & SHPb & DEPb).

  xport FRa MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport STATS MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport TI MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TK MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport T88 MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport TSD MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport CT MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJC; ub DCN; ub DCS; lia).
  xport FLG MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport HK MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport MCS MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport CF34 MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  pose proof PC as PC'. destruct PC' as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  xport GOT MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport GOT80 MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport REAL MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport PC4 MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport PC5 MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia).
  xport UJ MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJN; ub DJS; lia).
  xport CRa MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia). xport STSa MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  xport UW MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; ub DTN; ub DTS; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells bsegs m2 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). pose proof (rz_size_cases n) as RZC.
    xport LH MUb WMb ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS RZ RZC; ub DJN; ub DJS; lia). exact LH. }
  clear LH SHP.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.

  eapply evtF_cut.
  { eapply (allocD_gen L RNG spA gp tp F fc m2 n t c AB UB lo b0 (hdr_b1_mid b1) id S sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  destruct PD as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m3 & sj3
                  & -> & MUd & WMd & MId & STd & STATSd & LSJd & UFd & HDRd & LHd).
  xport CRa MUd WMd ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia). xport STSa MUd WMd ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  xport SHUb MUd WMd ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; lia). xport UW MUd WMd ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS; ub DJT; lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells bsegs m3 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb CX0 CX1 CBND CBNDa CBNDb NBND NBNDa NBNDb SBND SBNDa SBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RZE RZM RLR RSR RSM NSR C16 NSZ2 HPG HPW PW01 SB1 SB2 SB3 SB4 HC LTB LSJ N B1 DJT DJC DJN DJS DTN DTS DCN DCS NE; lia). exact SHPb. }
  assert (LH4 : 16 < rz_size n -> rw_cells bsegs m3 AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
  { intros RZ. exact (LHd RZ). }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha SPR S47 CEIL LO T0 T1 TAL TBND TBNDa TBNDb NI SI N1 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }

  apply evtF_done.
  assert (MU : munch (malloc_W L spA t c AB UB PG pgw n) m m3).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: first [clear -N C16 PW01; unfold sub_fp; cbn [outside]; intros q Hq; lia | fp_cover8 | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }
  assert (WM : wmono bsegs m m3) by (eapply wmono_trans; [exact WMb| exact WMd]).
  unfold malloc_post_gen. exists id. do 14 eexists. exists m3, sj3, stj. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|]. split; [exact UW|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LH4|]. split; [exact SHUb|]. split; [exact SHPd|]. exact DEPd.
  Unshelve. all: try exact STb; try exact ST.
Qed.
End WithDepot.
End CANSEC1.
End F_aallocate_tailg.
End TwinB.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AKit ShadowTac ADepot_iface ADepot ADepotKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition imemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(D, D + Z.of_nat (length src))]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' D [CB (length src) src].

Section Memcpy.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (src rest junk : list byte).
  Notation D := (bv_unsigned a0).
  Notation n := (Z.of_nat (length src)).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis SRC : bytes_at bsegs m S (src ++ rest).
  Hypothesis DST : rw_cells bsegs m D [CB (length src) junk].
  Hypothesis A1 : a1 = Z_to_bv 64 S.
  Hypothesis A2 : a2 = Z_to_bv 64 n.
  Hypothesis SEP : (S + Z.of_nat (length (src ++ rest)) <= D \/ D + n <= S)%Z.
  Hypothesis DSMALL : (D + n < 2^63)%Z.
  Hypothesis SSMALL : (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z.
  Hypothesis RS : rng RNG S n.
  Hypothesis RD : rng RNG D n.
  Notation POST := (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 D src m).

  (* [comment removed for export] *)
  Lemma imemcpy_loop : forall (k : nat) (i : Z) (mc : word -> option byte) (bs : list byte) x14,
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z ->
    u8arr bsegs mc D bs -> length bs = length src -> (forall j, (j < Z.to_nat i)%nat -> nth_error bs j = nth_error src j) ->
    munch [(D, D + n)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    evtF bsegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (S + i)) (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + i)) x14 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x65e90) fc None mc (seg_rom bsegs)).
  Proof.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB.
    induction k as [|k IH]; intros i mc bs x14 Hk Hi ARR LBS DONE MU WM MI1; [exfalso; lia|].
    destruct (nth_error src (Z.to_nat i)) as [b|] eqn:NB. 2:{ exfalso. apply nth_error_None in NB. lia. }
    assert (SRC1 : bytes_at bsegs mc S (src ++ rest)).
    { eapply bytes_at_transport; [exact SRC | exact MU |]. cbn [disjoint_from]. clear - SEP Hi SB DB. lia. }
    pose proof (u8ro_read bsegs mc S (src ++ rest) i b (wa (S + i)) SRC1 ltac:(rewrite nth_error_app1 by lia; exact NB) ltac:(lia) eq_refl) as RDb.
    zstep. cbv beta.
    pose proof (u8arr_store_ok bsegs mc D bs i (wa (D + i)) ARR ltac:(rewrite LBS; lia) eq_refl) as SOK.
    zstep.
    pose proof (u8arr_write bsegs mc D bs i b ARR ltac:(rewrite LBS; lia)) as ARR'.
    change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
    store_done.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia | lia | exact ARR' | rewrite Arr.upd_length; exact LBS | | assumption | assumption | assumption].
      + intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
        * subst j. rewrite Arr.nth_error_upd_same by (rewrite LBS; lia). symmetry; exact NB.
        * rewrite Arr.nth_error_upd_other by lia. apply DONE. lia.
    - zstep.
      assert (E : upd bs (Z.to_nat i) b = src).
      { apply nth_error_ext. intros j. destruct (Nat.eq_dec j (Z.to_nat i)).
        * subst j. rewrite Arr.nth_error_upd_same by (rewrite LBS; lia). symmetry; exact NB.
        * rewrite Arr.nth_error_upd_other by lia. destruct (Nat.lt_ge_cases j (Z.to_nat i)); [apply DONE; lia|].
          rewrite (proj2 (nth_error_None _ _)) by (rewrite LBS; lia). rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity. }
      rewrite E in ARR'. apply rw_cells_of_u8arr in ARR'. finish.
  Qed.

  Lemma imemcpy_body : (1 <= n < 2^64)%Z ->
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x65e84) fc None m (seg_rom bsegs)).
  Proof.
    intros N1. pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB.
    pose proof (munch_refl [(D, D + n)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM. subst a1 a2.
    zstep. if_cases K; zify_cond K. { exfalso. revert K N1 DB. clear. intros K N1 DB. Z.div_mod_to_equations. lia. }
    zstep. zstep.
    replace a0 with (Z_to_bv 64 (D + 0)) at 3 by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
    eapply (imemcpy_loop (Z.to_nat n) 0 m junk); try assumption; try lia.
    - eapply u8arr_of_rw_cells. exact DST.
    - pose proof DST as [[WF _] _]. cbn in WF. destruct WF as [WF _]. exact WF.
  Qed.
End Memcpy.

Lemma imemcpy_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S : Z) (src rest junk : list byte),
  mem_inv bsegs m -> bytes_at bsegs m S (src ++ rest) -> rw_cells bsegs m (bv_unsigned a0) [CB (length src) junk] ->
  (S + Z.of_nat (length (src ++ rest)) <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length src) <= S)%Z ->
  (bv_unsigned a0 + Z.of_nat (length src) < 2^63)%Z -> (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z ->
  (1 <= Z.of_nat (length src) < 2^64)%Z ->
  rng RNG S (Z.of_nat (length src)) -> rng RNG (bv_unsigned a0) (Z.of_nat (length src)) ->
  evtF bsegs RNG (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length src))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x65e84) fc None m (seg_rom bsegs)).
Proof. intros. eapply imemcpy_body; try eassumption; reflexivity. Qed.

(* [comment removed for export] *)
Definition imemcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(D, D + Z.of_nat (length src))]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' D [CB (length src) src].

Lemma imemcpy_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src rest junk : list byte),
  mem_inv bsegs m -> bytes_at bsegs m S (src ++ rest) -> rw_cells bsegs m D [CB (length src) junk] ->
  n = Z.of_nat (length src) ->
  (S + Z.of_nat (length (src ++ rest)) <= D \/ D + n <= S)%Z ->
  (D + n < 2^63)%Z -> (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z -> (1 <= n)%Z ->
  rng RNG S n -> rng RNG D n ->
  evtF bsegs RNG (imemcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 D src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x65e84) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI SRC DST -> SEP DS SS N1 RS RD.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  assert (U : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  eapply evtF_mono.
  { eapply (imemcpy_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S src rest junk);
      rewrite ?U; try eassumption; try reflexivity; lia. }
  intros ms' P. unfold imemcpy_post in P. rewrite !U in P. exact P.
Qed.

(* [comment removed for export] *)
Lemma amo_add_w_le4 : forall tf cnt, (0 <= tf)%Z -> (0 <= cnt)%Z -> (tf + cnt < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) (low32 (Z_to_bv 64 cnt))))
  = le4 (Z_to_bv 64 (tf + cnt)).
Proof.
  intros tf cnt H0 H1 H2. unfold le4 at 2. rewrite unsigned_lit by lia. f_equal.
  cbn [amo_val]. rewrite bv_add_unsigned.
  assert (E1 : bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) = tf).
  { rewrite bv_extract_unsigned. rewrite le_bytes_to_word_le4. rewrite unsigned_lit by lia.
    rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite !Z.mod_small by lia. reflexivity. }
  assert (E2 : bv_unsigned (low32 (Z_to_bv 64 cnt)) = cnt).
  { unfold low32. rewrite bv_extract_unsigned. rewrite unsigned_lit by lia. rewrite Z.shiftr_0_r.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity. }
  rewrite E1, E2. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac amo_stepW4 :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; rewrite amo_add_w_le4 by lia; mem_after_store_opt ]
    end end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Section Lock.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo B v : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 48)%Z.
  Hypothesis ALO : (AIMG_HI <= lo)%Z.
  Hypothesis A0 : a0 = Z_to_bv 64 B.
  Hypothesis CELL : rw_cells bsegs m B [C4 (Z_to_bv 64 v)].
  Hypothesis BV : (0 <= v < 2^31)%Z.
  Hypothesis BA : (B mod 4 = 0 /\ TAB <= B /\ B + 4 <= NUNIQ)%Z.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG B 4.

  Definition lock_post : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' lw,
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 4)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' B [C4 lw].

  Lemma lock_body : evtF bsegs RNG lock_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x751dc) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (B, B + 4)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold AIMG_HI, TAB, NUNIQ in *.
    assert (RSTK' : rng RNG (bv_unsigned sp + -48) 48) by (eapply rng_sub'; [exact RSTK| lia]).
    subst a0. carve_frame 48%nat ST.
    do 10 zstep. zstep. rewrite sx32_lit by lia.
    zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear - BV K1. lia. }
    zstep.
    assert (AMO : amo_aligned AW (Z_to_bv 64 B) = true) by (apply amo_alignedW_intro; [lia| lia]).
    amo_stepA AMO. rewrite sx32_lit by lia.
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
    amo_stepA AMO.
    zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. }
    zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. lia. }
    do 7 zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold lock_post.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. all: match goal with H : rw_cells bsegs _ B ?c |- _ => idtac c; exact H end.
  Qed.
End Lock.

(* [comment removed for export] *)
End CANSEC2.
Ltac shr0 :=
  repeat match goal with |- context [Z.shiftr ?x ?k] =>
    replace (Z.shiftr x k) with 0%Z by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia) end.


Section CANSEC3. Context {rc : runConstT}.
Section NStoreFile.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NStore.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (lo NDp AR T sz tf STORE : Z) (HW : word) (tb : list word) (jn jl js jh jf : list byte).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 112)%Z.
  Hypothesis ALO : (ATOP <= lo)%Z.
  Hypothesis A0 : a0 = Z_to_bv 64 NDp.
  Hypothesis A2 : a2 = Z_to_bv 64 AR.
  Hypothesis A3 : a3 = HW.
  Hypothesis ARGS : rw_cells bsegs m AR [C8 (Z_to_bv 64 T); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)].
  Hypothesis ARB : (bv_unsigned sp <= AR /\ AR + 16 <= 2^47)%Z.
  Hypothesis NODE : rw_cells bsegs m NDp [CB 8 jn; CB 4 jl; CB 4 js].
  Hypothesis CTF : rw_cells bsegs m SSTF [C8 (Z_to_bv 64 tf)].
  Hypothesis CPTR : rw_cells bsegs m SSPTR [C8 (Z_to_bv 64 STORE)].
  Hypothesis CST : rw_cells bsegs m SSST [C4 (Z_to_bv 64 tf)].
  Hypothesis FRAMES : rw_cells bsegs m (STORE + 8 * tf) [CB 8 jh; CB (Z.to_nat (8 * sz)) jf].
  Hypothesis TB : u64arr bsegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis SZ : (1 <= sz <= 255)%Z.
  Hypothesis TF : (0 <= tf /\ tf + sz + 1 < 1048576)%Z.
  Hypothesis TBB : (bv_unsigned sp <= T /\ T + 2040 <= 2^47)%Z.
  Hypothesis NDB : (AIMG_HI <= NDp /\ NDp + 16 <= ATOP /\ NDp mod 16 = 0)%Z.
  Hypothesis STOB : (AIMG_HI <= STORE /\ STORE + 8388608 <= ATOP /\ STORE mod 4096 = 0)%Z.
  Hypothesis SEPNS : (NDp + 16 <= STORE + 8 * tf \/ STORE + 8 * (tf + sz + 1) <= NDp)%Z.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RAR : rng RNG AR 16.
  Hypothesis RND : rng RNG NDp 16.
  Hypothesis RFR : rng RNG (STORE + 8 * tf) (8 * (sz + 1)).
  Hypothesis RT : rng RNG T 2040.

  Definition nstore_post : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (NDp, NDp + 16); (SSTF, SSTF + 8); (SSST, SSST + 4); (STORE + 8 * tf, STORE + 8 * tf + 8 * (sz + 1))]%Z m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' NDp [C8 HW; CB 4 jl; C4 (Z_to_bv 64 (tf + 1))]
      /\ rw_cells bsegs m' SSTF [C8 (Z_to_bv 64 (tf + sz + 1))]
      /\ rw_cells bsegs m' SSST [C4 (Z_to_bv 64 (tf + sz + 1))]
      /\ rw_cells bsegs m' (STORE + 8 * tf) [C8 (Z_to_bv 64 sz); CB (Z.to_nat (8 * sz)) (firstn (Z.to_nat (8 * sz)) (u64s tb))]
      /\ rw_cells bsegs m' AR [C8 (Z_to_bv 64 T); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)].

  Lemma nstore_body : evtF bsegs RNG nstore_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x74760) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (NDp, NDp + 16); (SSTF, SSTF + 8); (SSST, SSST + 4); (STORE + 8 * tf, STORE + 8 * tf + 8 * (sz + 1))]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold AIMG_HI, SSTF, SSPTR, SSST in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -112) 112) by (eapply rng_sub'; [exact RSTK| lia]).
    subst a0 a2 a3.
    change (?P) with (sf_hide P) in SEPNS.
    pose proof FRAMES as FRM. change (?P) with (sf_hide P) in FRAMES. pose proof NODE as NDC. change (?P) with (sf_hide P) in NODE.
    pose proof ARGS as ARGC. change (?P) with (sf_hide P) in ARGS.
    carve_frame 32%nat ST.
    do 10 zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    do 9 zstep. zstep. rewrite sx32_lit by lia. zstep. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zstep. fold_lits.
    rewrite Z.lor_0_r. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear -K1 SZ. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
    zstep. zstep.
    (* [comment removed for export] *)
    let x1 := reg_val 1%Z in let x2 := reg_val 2%Z in let x5 := reg_val 5%Z in let x6 := reg_val 6%Z in let x7 := reg_val 7%Z in
    let x8 := reg_val 8%Z in let x9 := reg_val 9%Z in let x11 := reg_val 11%Z in let x12 := reg_val 12%Z in let x13 := reg_val 13%Z in
    let x14 := reg_val 14%Z in let x15 := reg_val 15%Z in let x16 := reg_val 16%Z in let x17 := reg_val 17%Z in let x18 := reg_val 18%Z in
    let x19 := reg_val 19%Z in let x20 := reg_val 20%Z in let x21 := reg_val 21%Z in let x28 := reg_val 28%Z in let x29 := reg_val 29%Z in
    let x30 := reg_val 30%Z in let x31 := reg_val 31%Z in
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (REST : forall x10, evtF bsegs RNG nstore_post (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x724a4) fc None mc (seg_rom bsegs)))
    end.
    2:{ zstep. if_cases K3; zify_cond K3; [apply REST|]. zstep. replace (Z_to_bv 64 255) with (Z_to_bv 64 sz) by (f_equal; clear -K3 SZ; lia). apply REST. }
    intros x10.
    zstep. zstep. zstep. do 4 zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 5 zstep. amo_step.
    zstep. zstep. shr0. zstep. zstep. shr0.
    zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4. lia. }
    zstep. shr0.
    zstep. if_cases K5; zify_cond K5. 2:{ exfalso. clear -K5. lia. }
    zstep. zstep. zstep. zstep. zstep. if_cases K6; zify_cond K6. { exfalso. clear -K6 STOB. unfold AIMG_HI in STOB. lia. }
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    match goal with |- context [Z.shiftr ?e 41] =>
      replace (Z.shiftr e 41) with (8 * tf)%Z
        by (rewrite Z.shiftl_mul_pow2 by lia;
            first [ change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia
                  | change 18446744073709551616%Z with (2^64)%Z ];
            rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia;
            change (2^44)%Z with (8 * 2^41)%Z; rewrite Z.mul_assoc, Z.div_mul by lia; lia)
    end.
    do 3 zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K7; zify_cond K7. { exfalso. clear -K7 STOB TF. unfold AIMG_HI in STOB. lia. }
    zstep. zstep. zstep. rewrite Z.lor_0_l.
    apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRM. destruct FRM as [FRM FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR2.
    remember (STORE + 8 * tf)%Z as FA eqn:EFA.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    set (SRC := firstn (Z.to_nat (8 * sz)) (u64s tb)).
    assert (LSRC : length SRC = Z.to_nat (8 * sz)) by (subst SRC; rewrite firstn_length, u64s_length, LTB; lia).
    replace (Z.shiftl sz 3) with (Z.of_nat (length SRC)) by (rewrite LSRC, Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (TBc : bytes_at bsegs mc T (SRC ++ skipn (Z.to_nat (8 * sz)) (u64s tb)))
        by (subst SRC; rewrite firstn_skipn; match goal with H : u64arr bsegs mc T tb |- _ => exact (proj1 H) end);
      assert (DSTc : rw_cells bsegs mc (FA + 8) [CB (length SRC) jf]) by (rewrite LSRC; assumption)
    end.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (imemcpy_specZ RNG) with (src := SRC) (rest := skipn (Z.to_nat (8 * sz)) (u64s tb)) (junk := jf);
        [ eassumption | exact TBc | exact DSTc | reflexivity
        | rewrite length_app, skipn_length, u64s_length, LTB, LSRC; unfold sf_hide in *; lia
        | rewrite LSRC; lia | rewrite length_app, skipn_length, u64s_length, LTB, LSRC; lia | rewrite LSRC; lia
        | rewrite LSRC; eapply rng_sub'; [exact RT | lia] | rewrite LSRC; eapply rng_sub'; [exact RFR | lia] ]
      | (post_call bsegs mc) ]
    end.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z.land (Z.shiftr tf 16) 18446744073709551600) with 0%Z.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by (shr0; try lia; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
        rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. }
    zstep. zstep. fold_lits. amo_stepW4. rewrite sx32_lit by lia.
    zstep. zstep. zstep. shr0.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    match goal with H : rw_cells bsegs _ (bv_unsigned sp + -96) (C8 (Z_to_bv 64 tf) :: ?rest) |- _ =>
      apply (rw_cells_C8_C4C4 bsegs _ _ [] rest tf) in H; [cbn [app] in H | lia] end.
    zstep. rewrite sx32_lit by lia. zstep.
    (* [comment removed for export] *)
    setreg 10%Z (Z_to_bv 64 0)
      ltac:(f_equal; symmetry;
            match goal with |- Z.b2z (Z.lxor ?y 1048576 <? 1)%Z = 0%Z =>
              replace y with (sz + 1 + tf)%Z
                by (try change 4294967295%Z with (Z.ones 32); try change 18446744073709551615%Z with (Z.ones 64);
                    rewrite ?Z.land_ones by lia; try change (2^32)%Z with 4294967296%Z; try change (2^64)%Z with 18446744073709551616%Z;
                    symmetry; Z.div_mod_to_equations; lia) end;
            change 1048576%Z with (2^20)%Z; rewrite zb_lxor_pow2_small by lia;
            replace (_ <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    zstep. zstep. zstep. try rewrite sx32_lit by lia.
    (* [comment removed for export] *)
    do 9 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K8; zify_cond K8. { exfalso. clear -K8. lia. }
    do 4 zstep.
    match goal with FR1 : rw_cells bsegs _ (bv_unsigned sp + -112) _, ST : stk bsegs _ lo _ |- _ => release_frame FR1 ST (bv_unsigned sp + -96)%Z end.
    match goal with FR0 : rw_cells bsegs _ (bv_unsigned sp + -96) _, ST : stk bsegs _ lo _ |- _ => release_frame FR0 ST (bv_unsigned sp + -32)%Z end.
    match goal with FR : rw_cells bsegs _ (bv_unsigned sp + -32) _, ST : stk bsegs _ lo _ |- _ => release_frame FR ST (bv_unsigned sp) end.
    match goal with CTF : rw_cells bsegs _ 1711048 _ |- _ => cbn [amo_val] in CTF; rewrite lit_add_lit in CTF end.
    apply evtF_done. unfold nstore_post. subst FA. unfold sf_hide in *.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
    replace (tf + (sz + 1))%Z with (tf + sz + 1)%Z in * by lia.
    do 16 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - match goal with H : rw_cells bsegs _ NDp _ |- _ =>
        rewrite bv_swrap_small in H by (change (bv_half_modulus 32) with 2147483648%Z; lia); exact H end.
    - fold SRC. apply (proj2 (rw_cells_app bsegs _ _ [_] _)). split; [assumption|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- LSRC. assumption.
  Qed.
End NStore.
End NStoreFile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HashLoop.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (T sz : Z) (tb : list word).
  Hypothesis TB : u64arr bsegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis SZ : (1 <= sz <= 255)%Z.
  Hypothesis TBB : (0 <= T /\ T + 2040 <= 2^47)%Z.
  Hypothesis RT : rng RNG T 2040.

  Lemma hash_loop : forall (k : nat) (i h : Z) x15 x16 (Q : machine_state -> Prop),
    Z.to_nat (sz - i) = k -> (0 <= i < sz)%Z -> (0 <= h < 2^64)%Z ->
    (forall x15' x16',
       evtF bsegs RNG Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (T + 8 * sz))
                  (Z_to_bv 64 (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))))
                  a3 (Z_to_bv 64 (T + 8 * sz)) x15' x16' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x74b1c) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (T + 8 * i)) (Z_to_bv 64 h)
               a3 (Z_to_bv 64 (T + 8 * sz)) x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x74af8) fc None m (seg_rom bsegs)).
  Proof.
    induction k as [|k IH]; intros i h x15 x16 Q Hk Hi Hh K; [exfalso; lia|].
    destruct (nth_error tb (Z.to_nat i)) as [w|] eqn:NTH. 2:{ exfalso. apply nth_error_None in NTH. rewrite LTB in NTH. lia. }
    pose proof (u64arr_read bsegs m T tb i w (wa (T + 8 * i)) TB NTH ltac:(lia) eq_refl) as RD.
    do 8 zstep.
    lazymatch goal with |- context [Z_to_bv 64 (Z.lxor ?a h * ?M)%Z] =>
      replace (Z_to_bv 64 (Z.lxor a h * M)%Z) with (Z_to_bv 64 (mz_add h (bv_unsigned w)))
        by (unfold mz_add, mz_mix; apply Z_to_bv_mod64) end.
    pose proof (mz_add_range h (bv_unsigned w)) as Hh'.
    assert (SK : skipn (Z.to_nat i) tb = w :: skipn (Z.to_nat (i + 1)) tb).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      clear - NTH. revert NTH. generalize (Z.to_nat i) as n. intros n NTH.
      revert tb NTH. induction n as [|n IHn]; intros [|x l] NTH; cbn in *; try discriminate.
      - injection NTH as ->. reflexivity.
      - apply IHn. exact NTH. }
    zstep. if_cases KB; zify_cond KB.
    - replace (T + 8 * i + 8)%Z with (T + 8 * (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia | lia | exact Hh' |].
      intros x15' x16'.
      replace (mz_adds (mz_add h (bv_unsigned w)) (map bv_unsigned (firstn (Z.to_nat (sz - (i + 1))) (skipn (Z.to_nat (i + 1)) tb))))
        with (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))); [apply K|].
      rewrite SK. replace (Z.to_nat (sz - i)) with (S (Z.to_nat (sz - (i + 1)))) by lia. cbn [firstn map mz_adds fold_left]. reflexivity.
    - replace (T + 8 * i + 8)%Z with (T + 8 * sz)%Z by lia.
      replace (mz_add h (bv_unsigned w)) with (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))); [apply K|].
      rewrite SK. replace (Z.to_nat (sz - i)) with 1%nat by lia. cbn. reflexivity.
  Qed.
End HashLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FindFile.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Section FindLoop.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (hsh NODES N : Z) (hs lk sid : Z -> Z).
  Hypothesis Hh : (0 <= hsh < 2^64)%Z.
  Hypothesis HN : (1 <= N < 65536)%Z.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis CMAP : rw_cells bsegs m MAP1 [C8 (Z_to_bv 64 NODES)].
  Hypothesis CN : forall i, (1 <= i <= N)%Z ->
    rw_cells bsegs m (NODES + 16 * i) [C8 (Z_to_bv 64 (hs i)); C4 (Z_to_bv 64 (lk i)); C4 (Z_to_bv 64 (sid i))].
  Hypothesis NB : (AIMG_HI <= NODES /\ NODES + 1048576 <= ATOP /\ NODES mod 4096 = 0)%Z.
  Hypothesis LK : lk_ok lk N.
  Hypothesis HS : forall i, (1 <= i <= N)%Z -> (0 <= hs i < 2^64)%Z.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RNODES : rng RNG NODES 1048576.

  #[warnings="-notation-for-abbreviation"] Notation ST_AT pc x10 x11 x12 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 hsh) s4 s5 (Z_to_bv 64 0xffff) s7 (Z_to_bv 64 MAP1) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma find_loop : forall (k : nat) (j : Z) x10 x12 (Q : machine_state -> Prop),
    (Z.to_nat j <= k)%nat -> (0 <= j <= N)%Z ->
    (forall j' x11 x12', (1 <= j' <= N)%Z -> hs j' = hsh -> In j' (chain lk j) ->
       evtF bsegs RNG Q (ST_AT 0x74c8c (Z_to_bv 64 j') x11 x12')) ->
    (forall x10' x12', Forall (fun j' => hs j' <> hsh) (chain lk j) ->
       evtF bsegs RNG Q (ST_AT 0x74be0 x10' (Z_to_bv 64 0) x12')) ->
    evtF bsegs RNG Q (ST_AT 0x74b88 x10 (Z_to_bv 64 j) x12).
  Proof.
    unfold AIMG_HI, MAP1 in *.
    induction k as [|k IH]; intros j x10 x12 Q Hk Hj FOUND ABSENT.
    - assert (j = 0%Z) by lia. subst j.
      zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear -K0. lia. }
      apply ABSENT. rewrite chain_0. constructor.
    - destruct (Z.eq_dec j 0) as [->|NZ].
      { zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear -K0. lia. } apply ABSENT. rewrite chain_0. constructor. }
      pose proof (CN j ltac:(lia)) as NODE. pose proof (LK j ltac:(lia)) as LKj. pose proof (HS j ltac:(lia)) as HSj.
      pose proof (chain_cons lk N j LK ltac:(lia)) as CC.
      zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
      zstep. zstep.
      replace (bv_swrap 32 (Z.shiftr (bv_wrap 32 j) 16)) with 0%Z
        by (rewrite bv_wrap_small by (change (bv_modulus 32) with 4294967296%Z; lia); rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
      do 3 zstep.
      zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
      do 5 zstep.
      setreg 11%Z (Z_to_bv 64 (NODES + 16 * j))
        ltac:(f_equal; rewrite Z.mod_small by lia; change 65535%Z with (Z.ones 16); rewrite Z.land_ones by lia;
              rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
      remember (NODES + 16 * j)%Z as NA eqn:ENA.
      zstep. zstep. rewrite sx32_lit by lia.
      subst NA.
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply (IH (lk j)); [lia | lia | |].
        * intros j' x11 x12' H1 H2 H3. apply FOUND; [exact H1 | exact H2 |]. rewrite CC. right. exact H3.
        * intros x10' x12' FA. apply ABSENT. rewrite CC. constructor; [| exact FA]. clear -K2. intros E. apply K2. rewrite E. reflexivity.
      + (* [comment removed for export] *)
        zstep. apply FOUND; [lia | | rewrite CC; left; reflexivity]. clear -K2 Hh HSj. first [exact K2 | symmetry; exact K2 | lia].
  Qed.
End FindLoop.
End FindFile.
End CANSEC3.

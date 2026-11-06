(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Ported from, release commit 1aeda8ab8602, projects/leptonica/fhmtgen_fuzzer/proofs/lib/K5/B10/:
     I_strcmp.v   sha256 aa55d27bdd18  (istrcmp_post, the prologue, the whole walk and its epilogue)
     I_strcmpw.v  sha256 47bad47bee2a  (the byte-compare loop)
   Code match: see I_strcmpw.v (fuzz_reply.asan-ubsan 0x42ac4.. is the donor's 0x51b5c.. moved down by 0xf098, with
   TryAsanInitFromRtl at 0x5ae48 and the weak hook, a bare `ret`, at 0x42ac0).  The walk here enters at the
   exported wrapper 0x421f0, whose only instruction is `j 0x42ac4`.
   Statement: the strings are given up to and including the stop byte (length S idx, the bytes before idx equal
   and not NUL, the byte at idx different or NUL); the intercept_strcmp byte is a premise of its own; the stack
   bound is kHighShadowEnd < lo.
   Proof plan: the compare loop is one iteration (what the two loads see at an index up to the stop, and where the
   two branches go) counted down over the bytes left.  The whole walk keeps the caller's string facts packed until
   the loop head, and carries every fact about the caller's memory across the frame writes with one agreement
   fact for the addresses outside the frame.  The tests between the two range checks are walked in the callers of
   the checks. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit IcptSpec D_kit
  I_ikit I_strcmpw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* A value below 2^64 written as a 64-bit literal reads back as itself. *)
Local Ltac lit64 z :=
  let Hlit := fresh "Hu" in assert (Hlit : bv_unsigned (Z_to_bv 64 z) = z) by (apply unsigned_lit; lia).

(* A premise of a called walk: one of our hypotheses, or arithmetic on the bounds. *)
Local Ltac close_side := first [eassumption | lia | unfold kHighShadowEnd; lia].

(* An agreement goal whose addresses all lie outside the frame, given the frame fact Hout. *)
Local Ltac off_frame Hout :=
  let q := fresh "q" in let Hq := fresh "Hq" in apply Hout; intros q Hq; cbv beta in Hq; lia.

(* What the caller sees on return: result r in a0, callee-saved registers, sp and ra as on entry. *)
Definition istrcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2272, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

(* The compare loop, from byte k to the stop byte idx: s2 = p1, s1 = p2, s4 = the index.  It leaves with
   s4 = idx + 1 and the two stop bytes in s9 / s10. *)
Lemma strcmp_cmp_loop : forall (r k idx : nat) (p1 p2 : Z) (b1 b2 : list byte) (x y : byte)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  idx = (k + r)%nat -> Z.of_nat idx + 1 < 2^64 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> sc_pre b1 b2 idx ->
  nth_error b1 idx = Some x -> nth_error b2 idx = Some y -> (bv_unsigned x <> bv_unsigned y \/ bv_unsigned x = 0) ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (a0' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p2) a0' a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 p1) s3 (Z_to_bv 64 (Z.of_nat idx + 1)) s5 s6 s7 s8
                    (Z_to_bv 64 (bv_unsigned x)) (Z_to_bv 64 (bv_unsigned y)) s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x42b40) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p2) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p1) s3 (Z_to_bv 64 (Z.of_nat k)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42b24) fc None m (seg_rom asegs)).
Proof.
  intros r k idx p1 p2 b1 b2 x y ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hcount Hroom Hstr1 Hstr2 Hsame Hstop1 Hstop2 Hdiffer Hinv.
  pose proof (bytes_at_bound _ _ _ _ Hstr1) as Hfit1. pose proof (bytes_at_bound _ _ _ _ Hstr2) as Hfit2.
  assert (Hin1 : (idx < length b1)%nat) by (apply nth_error_Some; rewrite Hstop1; discriminate).
  assert (Hin2 : (idx < length b2)%nat) by (apply nth_error_Some; rewrite Hstop2; discriminate).
  (* a byte of a string, as the one-byte cell a load reads *)
  assert (Hcell : forall bs base j c, bytes_at asegs m base bs -> nth_error bs j = Some c ->
                    ro_cells asegs m (base + Z.of_nat j) [C1 c]).
  { intros bs base j c Hb Hj. split; [cbn; tauto|]. cbn [cells_bytes cbytes app].
    exact (bytes_at_nth1 asegs m base bs j c Hb Hj). }
  (* the two bytes at an index up to the stop: the stop bytes, or one shared byte that is not NUL *)
  assert (Hpair : forall j, (j <= idx)%nat -> exists c1 c2, nth_error b1 j = Some c1 /\ nth_error b2 j = Some c2 /\
                    ((j = idx /\ c1 = x /\ c2 = y) \/ ((j < idx)%nat /\ c1 = c2 /\ bv_unsigned c1 <> 0))).
  { intros j Hj. destruct (Nat.eq_dec j idx) as [Hjeq|Hjne].
    - subst j. exists x, y. split; [exact Hstop1|]. split; [exact Hstop2|]. left. auto.
    - destruct (Hsame j ltac:(lia)) as (c & Hc1 & Hc2 & Hcnz). exists c, c.
      split; [exact Hc1|]. split; [exact Hc2|]. right. split; [lia|]. split; [reflexivity| exact Hcnz]. }
  lit64 p1. lit64 p2.
  (* one pass of the loop body from index j: the exit at the stop byte, or the loop head again at j + 1 *)
  match goal with |- evt _ ?Post _ =>
    assert (Hone : forall (j : nat) (w0 w9 w10 : word), (j <= idx)%nat ->
      ((j < idx)%nat -> forall v0 v9 v10 : word,
         evt asegs Post (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p2) v0 a1 a2 a3 a4 a5 a6 a7
                               (Z_to_bv 64 p1) s3 (Z_to_bv 64 (Z.of_nat (S j))) s5 s6 s7 s8 v9 v10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0x42b24) fc None m (seg_rom asegs))) ->
      evt asegs Post (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p2) w0 a1 a2 a3 a4 a5 a6 a7
                            (Z_to_bv 64 p1) s3 (Z_to_bv 64 (Z.of_nat j)) s5 s6 s7 s8 w9 w10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x42b24) fc None m (seg_rom asegs)))
  end.
  { intros j w0 w9 w10 Hj Hnext.
    destruct (Hpair j Hj) as (c1 & c2 & Hc1 & Hc2 & Hwhich).
    pose proof (Hcell b1 p1 j c1 Hstr1 Hc1) as Hld1. pose proof (Hcell b2 p2 j c2 Hstr2 Hc2) as Hld2.
    pose proof (bv_unsigned_in_range 8 c1) as Hrg1. pose proof (bv_unsigned_in_range 8 c2) as Hrg2.
    unfold bv_modulus in Hrg1, Hrg2. change (2 ^ Z.of_N 8) with 256 in Hrg1, Hrg2.
    lit64 (Z.of_nat j). lit64 (Z.of_nat j + 1). lit64 (bv_unsigned c1). lit64 (bv_unsigned c2).
    (* the two load addresses, kept as names so the loads find their cells *)
    remember (p1 + Z.of_nat j) as q1 eqn:Hq1 in Hld1. remember (p2 + Z.of_nat j) as q2 eqn:Hq2 in Hld2.
    (* add, load from the first string; add, load from the second; the index increment *)
    lstep. rewrite <- Hq1. lstep.
    lstep. rewrite <- Hq2. lstep.
    lstep.
    (* beqz s9: the first string ends here *)
    lstep. if_cases Hnul; zify_cond Hnul; rewrite ?unsigned_lit in Hnul by lia.
    - destruct Hwhich as [(Hjeq & Hx & Hy) | (_ & _ & Hnz)]; [| exfalso; lia].
      subst j c1 c2. apply evt_done. eexists. reflexivity.
    - (* beq s9, s10: the same byte, round again *)
      lstep. if_cases Hbeq; zify_cond Hbeq; rewrite ?unsigned_lit in Hbeq by lia.
      + destruct Hwhich as [(Hjeq & Hx & Hy) | (Hlt & Heq & _)].
        * exfalso. subst c1 c2. destruct Hdiffer; lia.
        * subst c2. replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia. apply Hnext. exact Hlt.
      + destruct Hwhich as [(Hjeq & Hx & Hy) | (_ & Heq & _)]; [| subst c2; exfalso; lia].
        subst j c1 c2. apply evt_done. eexists. reflexivity. }
  (* count down the bytes left before the stop *)
  clear Hpair Hcell.
  revert Hcount. revert k a0 s9 s10.
  induction r as [|r' IHr]; intros k a0 s9 s10 Hcount.
  - (* no byte left before the stop: the pass exits *)
    apply Hone; [lia | intros Hlt; exfalso; lia].
  - (* a byte left: the loop head again, one index on *)
    apply Hone; [lia | intros Hlt v0 v9 v10; apply IHr; lia].
Qed.

(* Frame set-up: 2192 bytes, the thirteen callee-saved registers and ra at the top, s0 the frame pointer. *)
Lemma strcmp_prologue : forall (sp p1 p2 : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo sp -> lo <= sp - 2272 -> kHighShadowEnd < lo -> sp < 2^63 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (junk : list byte),
      ms' = MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 p2)
                    (Z_to_bv 64 p1) (Z_to_bv 64 p2) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p1) ra s4
                    s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x42b10) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2192, sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m' (sp + -2192) [CB 2088 junk]
      /\ stk asegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42ac4) fc None m (seg_rom asegs)).
Proof.
  intros sp p1 p2 ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    Hstk Hlo Hlo_shadow Hsp_hi Hinv.
  unfold kHighShadowEnd in Hlo_shadow.
  pose proof (munch_refl [(sp - 2192, sp)] m) as Hfoot. pose proof (wmono_refl asegs m) as Hgrow.
  lit64 sp.
  (* the save area at the top, the scratch area below it *)
  carve_frame 104%nat Hstk. rename FR into Hsaved.
  carve_frame 2088%nat Hstk. rename FR into Hscratch.
  (* two sp adjustments, thirteen stores, s0 and the three argument copies *)
  xsteps_to 0x42b10.
  apply evt_done. eexists _, _.
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end.
  eassumption.
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* From the second range check to the return: check (p2, sz), the result cmpx x1 x2, the weak hook, the frame
   restored. *)
Lemma strcmp_tail2 : forall (usp p2 sz x1 x2 : Z)
    (ra ra' gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0' s2' s3' s6' s7' s8' s11' : word) F fc (m0 m : mem) (lo : Z) (junk : list byte),
  stk asegs m lo (usp + -2192) -> lo <= usp - 2272 -> kHighShadowEnd < lo -> usp < 2^63 ->
  rw_cells asegs m (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (usp + -2192) [CB 2088 junk] ->
  munch [(usp - 2272, usp)] m0 m -> wmono asegs m0 m ->
  0 <= p2 -> 1 <= sz -> p2 + sz <= 2^47 -> 0 <= x1 < 256 -> 0 <= x2 < 256 ->
  chk_ok m p2 sz -> m2s_cells m -> icells_sc m -> mem_inv asegs m ->
  evt asegs (istrcmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (cmpx x1 x2) lo m0)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2192)) gp tp t0 t1 t2 s0' (Z_to_bv 64 p2) a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' (Z_to_bv 64 sz) (Z_to_bv 64 (sz - 1)) s6' s7' s8' (Z_to_bv 64 x1) (Z_to_bv 64 x2) s11' t3 t4 t5 t6)
        F (Z_to_bv 64 0x42bbc) fc None m (seg_rom asegs)).
Proof using RIP.
  intros usp p2 sz x1 x2 ra ra' gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    s0' s2' s3' s6' s7' s8' s11' F fc m0 m lo junk
    Hstk Hlo Hlo_shadow Hsp_hi Hsaved Hscratch Hfoot Hgrow Hp2 Hsz Hend2 Hx1 Hx2 Hchk2 Hm2s Hcells Hinv.
  pose proof Hlo_shadow as Hlo_num. unfold kHighShadowEnd in Hlo_num.
  (* the second range check *)
  call (strcmp_chk2 RIP usp p2 sz); try close_side.
  rename POST into Hstk.
  match goal with H : mem_inv asegs _ |- _ => rename H into Hinv end.
  lit64 usp. lit64 x1. lit64 x2.
  (* sltu, sltu, sub: the sign of x1 - x2 *)
  xsteps_to 0x42c08.
  rewrite cmpx_b2z.
  (* the weak hook, the result into a0, the saved registers back, sp up *)
  xsteps_to 0x42c5c.
  release_frame Hscratch Hstk (usp + -104). release_frame Hsaved Hstk usp.
  (* ret *)
  lstep.
  unfold istrcmp_post. sys_finish.
  all: rewrite unsigned_lit by lia.
  - exact Hfoot.
  - exact Hstk.
Qed.

(* From the first range check: check (p1, sz), the flag and wrap tests before the second check, then the rest. *)
Lemma strcmp_tail : forall (usp p1 p2 sz x1 x2 : Z)
    (ra ra' gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0' s3' s7' s11' : word) F fc (m0 m : mem) (lo : Z) (junk : list byte),
  stk asegs m lo (usp + -2192) -> lo <= usp - 2272 -> kHighShadowEnd < lo -> usp < 2^63 ->
  rw_cells asegs m (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (usp + -2192) [CB 2088 junk] ->
  munch [(usp - 2272, usp)] m0 m -> wmono asegs m0 m ->
  0 <= p1 -> 0 <= p2 -> 1 <= sz -> p1 + sz <= 2^47 -> p2 + sz <= 2^47 -> 0 <= x1 < 256 -> 0 <= x2 < 256 ->
  chk_ok m p1 sz -> chk_ok m p2 sz -> m2s_cells m -> icells_sc m -> mem_inv asegs m ->
  evt asegs (istrcmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (cmpx x1 x2) lo m0)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2192)) gp tp t0 t1 t2 s0' (Z_to_bv 64 p2) (Z_to_bv 64 (sz - 1)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p1) s3' (Z_to_bv 64 sz) (Z_to_bv 64 (sz - 1)) (Z_to_bv 64 sz) s7' (Z_to_bv 64 0x138168)
             (Z_to_bv 64 x1) (Z_to_bv 64 x2) s11' t3 t4 t5 t6)
        F (Z_to_bv 64 0x42b6c) fc None m (seg_rom asegs)).
Proof using RIP.
  intros usp p1 p2 sz x1 x2 ra ra' gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    s0' s3' s7' s11' F fc m0 m lo junk
    Hstk Hlo Hlo_shadow Hsp_hi Hsaved Hscratch Hfoot Hgrow Hp1 Hp2 Hsz Hend1 Hend2 Hx1 Hx2 Hchk1 Hchk2 Hm2s Hcells Hinv.
  pose proof Hlo_shadow as Hlo_num. unfold kHighShadowEnd in Hlo_num.
  pose proof (munch_refl [(usp - 2272, usp)] m) as Hwin. pose proof (wmono_refl asegs m) as Hwin_grow.
  (* the first range check *)
  call (strcmp_chk1 RIP usp p1 sz); try close_side.
  rename POST into Hstk.
  match goal with H : mem_inv asegs _ |- _ => rename H into Hinv end.
  (* the check wrote only inside the frame: what the second check needs still holds *)
  lazymatch type of Hwin with munch _ _ ?m1 =>
    assert (Hout : forall P : Z -> Prop, (forall q, P q -> q < usp - 2272) -> agree_on P m m1)
      by (intros P HP; apply (agree_of_munch _ _ _ _ Hwin); intros q Hq; cbn [outside];
          split; [specialize (HP q Hq); lia | exact I]);
    assert (Hchk2' : chk_ok m1 p2 sz) by (apply (chk_ok_agree m); [exact Hchk2 | lia | lia | off_frame Hout]);
    assert (Hm2s' : m2s_cells m1) by (apply (m2s_cells_agree m m1 Hm2s); [off_frame Hout | exact Hwin_grow]);
    assert (Hcells' : icells_sc m1) by (apply (icells_sc_agree m m1 Hcells); [off_frame Hout | exact Hwin_grow])
  end.
  clear Hchk1 Hchk2 Hm2s Hcells Hout.
  pose proof Hcells' as (_ & _ & _ & _ & Hflag_f5).
  pose proof (lxor_ones64 p2 ltac:(lia)) as Hnot2.
  lit64 p2. lit64 sz. lit64 (18446744073709551615 - p2).
  (* the 0xf5 flag byte is clear *)
  lstep. lstep. if_false.
  (* p2 + sz does not wrap *)
  lstep. rewrite Hnot2. lstep. if_false.
  eapply (strcmp_tail2 usp p2 sz x1 x2);
    [ exact Hstk | exact Hlo | exact Hlo_shadow | exact Hsp_hi | exact Hsaved | exact Hscratch | exact Hfoot
    | exact Hgrow | exact Hp2 | exact Hsz | exact Hend2 | exact Hx1 | exact Hx2 | exact Hchk2' | exact Hm2s'
    | exact Hcells' | exact Hinv ].
Qed.

(* The walk from the exported wrapper to the return, for two strings given up to their stop byte. *)
Theorem istrcmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : Z) (b1 b2 : list byte) (idx : nat) (x y : byte) (lo : Z),
  a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2272 -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> length b1 = S idx -> length b2 = S idx ->
  sc_pre b1 b2 idx -> nth_error b1 idx = Some x -> nth_error b2 idx = Some y ->
  (bv_unsigned x <> bv_unsigned y \/ bv_unsigned x = 0) ->
  p1 + (Z.of_nat idx + 1) <= 2^47 -> p2 + (Z.of_nat idx + 1) <= 2^47 ->
  (p1 + (Z.of_nat idx + 1) <= bv_unsigned sp - 2272 \/ bv_unsigned sp <= p1) ->
  (p2 + (Z.of_nat idx + 1) <= bv_unsigned sp - 2272 \/ bv_unsigned sp <= p2) ->
  chk_ok m p1 (Z.of_nat idx + 1) -> chk_ok m p2 (Z.of_nat idx + 1) -> m2s_cells m -> icells_sc m ->
  ro_cells asegs m 0x138262 [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (istrcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (cmpx (bv_unsigned x) (bv_unsigned y)) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x421f0) fc None m (seg_rom asegs)).
Proof using RIP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p1 p2 b1 b2 idx x y lo Harg1 Harg2 Hstk Hlo Hlo_shadow Hsp_hi Hstr1 Hstr2 Hlen1 Hlen2 Hsame Hstop1 Hstop2 Hdiffer
    Hend1 Hend2 Hsep1 Hsep2 Hchk1 Hchk2 Hm2s Hcells Hflag Hinv.
  subst a0 a1.
  pose proof Hlo_shadow as Hlo_num. unfold kHighShadowEnd in Hlo_num.
  pose proof (bytes_at_bound _ _ _ _ Hstr1) as Hfit1. pose proof (bytes_at_bound _ _ _ _ Hstr2) as Hfit2.
  pose proof (bv_unsigned_in_range 8 x) as Hxr. pose proof (bv_unsigned_in_range 8 y) as Hyr.
  unfold bv_modulus in Hxr, Hyr. change (2 ^ Z.of_N 8) with 256 in Hxr, Hyr.
  (* the two strings, set aside until the compare loop reads them *)
  assert (Hstrings : keep (bytes_at asegs m p1 b1 /\ bytes_at asegs m p2 b2)) by (split; assumption).
  clear Hstr1 Hstr2.
  set (usp := bv_unsigned sp) in *.
  replace sp with (Z_to_bv 64 usp) by (first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned]).
  lit64 usp. lit64 (usp + -2192).
  pose proof (munch_refl [(usp - 2272, usp)] m) as Hfoot. pose proof (wmono_refl asegs m) as Hgrow.
  (* writes confined to the frame leave every other address as it was *)
  assert (Hoff : forall m1 m2, munch [(usp - 2272, usp)] m1 m2 -> forall P : Z -> Prop,
            (forall q, P q -> q < usp - 2272 \/ usp <= q) -> agree_on P m1 m2).
  { intros m1 m2 Hmu P HP. apply (agree_of_munch _ _ _ _ Hmu). intros q Hq. cbn [outside].
    split; [specialize (HP q Hq); lia | exact I]. }
  (* the wrapper's jump, then the frame *)
  lstep.
  call (strcmp_prologue usp p1 p2); try close_side.
  rename PC into Hsaved, PC0 into Hscratch, POST into Hstk.
  match goal with H : mem_inv asegs _ |- _ => rename H into Hinv end.
  (* the start-up flag, for TryAsanInitFromRtl *)
  lazymatch type of Hfoot with munch _ _ ?m1 =>
    assert (Hcells1 : icells_sc m1)
      by (apply (icells_sc_agree m m1 Hcells); [off_frame (Hoff m m1 Hfoot) | exact Hgrow])
  end.
  destruct Hcells1 as (_ & _ & _ & Hstarted & _).
  lstep.
  rewrite <- (unsigned_lit (usp + -2192)) in Hstk by lia.
  call try_init_spec; try close_side.
  match goal with H : stk asegs _ lo _ |- _ => rewrite unsigned_lit in H by lia; rename H into Hstk end.
  match goal with H : mem_inv asegs _ |- _ => rename H into Hinv end.
  (* to the loop head: index 0, s11 the scratch area *)
  xsteps_to 0x42b24.
  (* the caller's facts, moved to the memory at the loop head *)
  lazymatch type of Hfoot with munch _ _ ?mh =>
    pose proof (Hoff m mh Hfoot) as Hkeep_out;
    destruct Hstrings as (Hstr1 & Hstr2);
    assert (Hstr1h : bytes_at asegs mh p1 b1) by (apply (bytes_at_agree asegs m mh _ _ Hstr1); off_frame Hkeep_out);
    assert (Hstr2h : bytes_at asegs mh p2 b2) by (apply (bytes_at_agree asegs m mh _ _ Hstr2); off_frame Hkeep_out);
    assert (Hchk1h : chk_ok mh p1 (Z.of_nat idx + 1)) by (apply (chk_ok_agree m); [exact Hchk1 | lia | lia | off_frame Hkeep_out]);
    assert (Hchk2h : chk_ok mh p2 (Z.of_nat idx + 1)) by (apply (chk_ok_agree m); [exact Hchk2 | lia | lia | off_frame Hkeep_out]);
    assert (Hm2sh : m2s_cells mh) by (apply (m2s_cells_agree m mh Hm2s); [off_frame Hkeep_out | exact Hgrow]);
    assert (Hcellsh : icells_sc mh) by (apply (icells_sc_agree m mh Hcells); [off_frame Hkeep_out | exact Hgrow])
  end.
  clear Hstr1 Hstr2 Hchk1 Hchk2 Hm2s Hcells Hkeep_out.
  (* the loop, from index 0 to the stop byte *)
  eapply evt_cut;
    [ exact (strcmp_cmp_loop idx 0 idx p1 p2 b1 b2 x y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _
               eq_refl ltac:(lia) Hstr1h Hstr2h Hsame Hstop1 Hstop2 Hdiffer Hinv) | ].
  intros ms_loop (a0_loop & ->).
  pose proof Hcellsh as (Hgot_flags & Hgot_shadow & Hshadow_off & _ & Hflag_f5).
  pose proof (lxor_ones64 p1 ltac:(lia)) as Hnot1.
  lit64 p1. lit64 (Z.of_nat idx + 1). lit64 (18446744073709551615 - p1).
  (* intercept_strcmp is set *)
  do 4 lstep. if_false.
  (* the 0xf5 flag byte is clear; s5 and a0 get idx, s6 gets idx + 1 *)
  do 5 lstep. if_false.
  (* p1 + idx + 1 does not wrap *)
  lstep. rewrite Hnot1. lstep. if_false.
  (* both checks have size sz = idx + 1; a0 and s5 hold sz - 1 *)
  set (sz := Z.of_nat idx + 1) in *.
  assert (Hsz : 1 <= sz) by (unfold sz; lia).
  assert (Hidx : Z.of_nat idx = sz - 1) by (unfold sz; lia).
  rewrite Hidx.
  eapply (strcmp_tail usp p1 p2 sz);
    [ exact Hstk | exact Hlo | exact Hlo_shadow | exact Hsp_hi | exact Hsaved | exact Hscratch | exact Hfoot
    | exact Hgrow | lia | lia | exact Hsz | exact Hend1 | exact Hend2 | exact Hxr | exact Hyr | exact Hchk1h
    | exact Hchk2h | exact Hm2sh | exact Hcellsh | exact Hinv ].
Qed.

End WithRIP.

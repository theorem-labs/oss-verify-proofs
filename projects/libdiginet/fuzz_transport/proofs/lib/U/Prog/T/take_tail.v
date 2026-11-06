(* take (transport/src/diginet_session.c:353-386) in the ubsan image, part 1 of its walk (U/Prog/T/take.v holds
   take_holds): the exit state at 0x17c04, the copy loop of :378-379 (0x17ba0 .. 0x17bf4), the break of :377-380
   (0x17b58 .. 0x17b9c), the loop head state at 0x17a5c and the end of a turn (0x17b30 .. 0x17b54). Every UBSan
   check of these paths branches to the unimp at 0x17c58 and is decided false from the model's Some: an index
   below 512 (take_tail_m is None at 512), kept below 513, and no address of g_s.queue wrapping. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TSess0 TTake.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Ltac solve_load ::= first [ tk_solve_load_world | wk_solve_load_world | solve_load_base | solve_load_image ].
Ltac solve_store ::= first [ tk_solve_store_world | wk_solve_store_world | wk_solve_store_kit ].
Ltac mem_after_store_opt ::=
  try fix_lit_store; first [ tk_world_after_store | wk_world_after_store | wk_mem_after_store_opt_kit ].

(** * Register arithmetic of the ubsan code *)

(* not of a register (the pointer-overflow bounds ~bp and ~&s->queue[0]) *)
Lemma tku_not : forall x, 0 <= x < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615) = Z_to_bv 64 (18446744073709551615 - x).
Proof. intros x Hx. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. reflexivity. Qed.

(* the alignment checks: andi of an aligned pointer *)
Lemma tku_land3 : forall t, 0 <= t < 2 ^ 64 -> t mod 4 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 t)) 3 = 0.
Proof. intros t Ht H4. rewrite unsigned_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H4. Qed.

Lemma tku_land7 : forall t, 0 <= t < 2 ^ 64 -> t mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 t)) 7 = 0.
Proof. intros t Ht H8. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H8. Qed.

(* subw / negw of the register s0 = -i (the loop counts i down in s0) *)
Lemma tku_swrap_sub_neg : forall a i, bv_swrap 32 (a - bv_unsigned (Z_to_bv 64 (- i))) = bv_swrap 32 (a + i).
Proof.
  intros a i. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  f_equal. rewrite (Z.mod_eq (- i) (2 ^ 64)) by lia.
  replace (a - (- i - 2 ^ 64 * (- i / 2 ^ 64)) + 2 ^ 31)
    with ((a + i + 2 ^ 31) + (2 ^ 32 * (- i / 2 ^ 64)) * 2 ^ 32) by lia.
  apply Z_mod_plus_full.
Qed.

(* the mask of the copy loop's index check: sltiu a4,a3,514 with a3 = 513 - kept *)
Lemma tku_sltiu1 : forall x, 0 <= x < 514 -> v_sltiu (Z_to_bv 64 x) 514 = Z_to_bv 64 1.
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 514) with 514.
  replace (x <? 514) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* and of the mask -1 (the step folds bv_unsigned of the closed -1) *)
Lemma tku_land_m1 : forall x, 0 <= x < 2 ^ 64 ->
  Z.land 18446744073709551615 (bv_unsigned (Z_to_bv 64 x)) = x.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(** * The frame *)

(* own frame of 160 bytes at sp - 160, by offset: 0 never written; 8 has_display (stored at 0x17a2c); 16 ~body
   (0x17a54); 24 body_len (0x17a14); 32 the slot that keeps taken across the calls of the fit path; 40
   allow_display; 48 body; 56 .. 144 s11 .. s0; 152 ra *)
Abbreviation tku_fr j0 hdw nbw blpw j32 allw bpw r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra :=
  [CB 8 j0; C8 hdw; C8 nbw; C8 blpw; CB 8 j32; C8 allw; C8 bpw; C8 r11; C8 r10; C8 r9; C8 r8; C8 r7; C8 r6;
   C8 r5; C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra].
(* the frame at the exit 0x17c04: slots 0 .. 23 and 32 as bytes (the queued = 0 path never writes 8 and 16) *)
Abbreviation tku_frx jA blpw jB allw bpw r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra :=
  [CB 24 jA; C8 blpw; CB 8 jB; C8 allw; C8 bpw; C8 r11; C8 r10; C8 r9; C8 r8; C8 r7; C8 r6;
   C8 r5; C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra].

Lemma tku_fold24 : forall (segs : list Segment) m A j0 h n rest,
  rw_cells segs m A (CB 8 j0 :: C8 h :: C8 n :: rest) -> rw_cells segs m A (CB 24 (j0 ++ le8 h ++ le8 n) :: rest).
Proof.
  intros segs m A j0 h n rest H. eapply tk_rebytes; [exact H| |].
  - destruct H as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf |- *. destruct Hwf as (L0 & _ & _ & W).
    split; [rewrite !length_app, L0, !length_le8; reflexivity | exact W].
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

(* the slot at offset 32 after the fit path read taken back from it: bytes again *)
Lemma tku_slot32 : forall (segs : list Segment) m A j0 h n b w rest,
  rw_cells segs m A (CB 8 j0 :: C8 h :: C8 n :: C8 b :: C8 w :: rest) ->
  rw_cells segs m A (CB 8 j0 :: C8 h :: C8 n :: C8 b :: CB 8 (le8 w) :: rest).
Proof.
  intros segs m A j0 h n b w rest H. eapply tk_rebytes; [exact H| |].
  - destruct H as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf |- *. destruct Hwf as (L0 & _ & _ & _ & _ & W).
    split; [exact L0|]. split; [exact I|]. split; [exact I|]. split; [exact I|].
    split; [exact (length_le8 w) | exact W].
  - reflexivity.
Qed.

(** * The walk *)

Section Walk.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (lo bp blp hdp allow : Z) (JL : list byte)
  (rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra : word).
Hypotheses (HAL : - 2 ^ 31 <= allow < 2 ^ 31)
  (BP0 : 0 < bp) (BP1 : bp + 1484 < 2 ^ 64)
  (BP2 : bp + 1484 <= W_BASE_UBSAN \/ W_BASE_UBSAN + W_LEN <= bp)
  (BP3 : bp + 1484 <= bv_unsigned sp - 304 \/ bv_unsigned sp <= bp)
  (BL0 : 0 < blp) (BL1 : blp + 8 < 2 ^ 64)
  (BL2 : blp + 8 <= W_BASE_UBSAN \/ W_BASE_UBSAN + W_LEN <= blp)
  (BL3 : blp + 8 <= bv_unsigned sp - 304 \/ bv_unsigned sp <= blp)
  (BH0 : 0 < hdp) (BH1 : hdp + 4 < 2 ^ 64)
  (BH2 : hdp + 4 <= W_BASE_UBSAN \/ W_BASE_UBSAN + W_LEN <= hdp)
  (BH3 : hdp + 4 <= bv_unsigned sp - 304 \/ bv_unsigned sp <= hdp)
  (S1 : bp + 1484 <= blp \/ blp + 8 <= bp) (S2 : bp + 1484 <= hdp \/ hdp + 4 <= bp)
  (S3 : blp + 8 <= hdp \/ hdp + 4 <= blp)
  (LO : lo + 304 <= bv_unsigned sp) (WO : W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 304)
  (Rsp : 0 <= bv_unsigned sp < 2 ^ 64) (Hlo : 0 <= lo)
  (SPm : tk_keep ((bv_unsigned sp + -160) mod 8 = 0)) (HA4 : tk_keep (hdp mod 4 = 0))
  (HA8 : tk_keep (blp mod 8 = 0))
  (Ew : W_LEN = 65616) (Ew0 : W_BASE_UBSAN = 209664) (Ew1 : OFF_g_s = 1648).

Local Abbreviation FRL j0 j32 := (tku_fr j0 (Z_to_bv 64 hdp) (Z_to_bv 64 (18446744073709551615 - bp))
  (Z_to_bv 64 blp) j32 (Z_to_bv 64 allow) (Z_to_bv 64 bp) rs11 rs10 rs9 rs8 rs7 rs6 rs5 rs4 rs3 rs2 rs1 rs0 rra).
Local Abbreviation FRX jA jB := (tku_frx jA (Z_to_bv 64 blp) jB (Z_to_bv 64 allow) (Z_to_bv 64 bp)
  rs11 rs10 rs9 rs8 rs7 rs6 rs5 rs4 rs3 rs2 rs1 rs0 rra).
Local Abbreviation TW := [(bv_unsigned sp - 304, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
                      (bp, bp + 1484); (blp, blp + 8); (hdp, hdp + 4)].

(* The state at 0x17c04 (s->queued = kept; *body_len = len; return taken), with the memory facts the epilogue
   needs. *)
Definition tku_exit (Q : machine_state -> Prop) (B2 bodyF : list byte) (lenF hdF takenF keptF : Z) : Prop :=
  forall (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s10' s11' t3' t4' t5' t6' : word)
         (m' : word -> option byte) (JF jA jB : list byte),
    wmem rsegs m' B2 -> g_fail_next B2 <= 1 ->
    rw_cells rsegs m' bp [CB 1484 JF] -> firstn (Z.to_nat lenF) JF = bodyF ->
    rw_cells rsegs m' hdp [C4 (Z_to_bv 64 hdF)] -> rw_cells rsegs m' blp [CB 8 JL] ->
    rw_cells rsegs m' (bv_unsigned sp + -160) (FRX jA jB) -> stk rsegs m' lo (bv_unsigned sp + -160) ->
    mem_inv rsegs m' ->
    munch TW m0 m' -> wmono rsegs m0 m' ->
    0 <= lenF <= 1484 -> 0 <= takenF <= 512 -> 0 <= keptF <= 512 ->
    evt rsegs Q (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' s0' (Z_to_bv 64 takenF)
                         a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                         (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 18144)) (Z_to_bv 64 lenF) (Z_to_bv 64 keptF)
                         s10' s11' t3' t4' t5' t6')
                    F (Z_to_bv 64 0x17c04) fc None m' (seg_rom rsegs)).

(* The loop of :378-379 at 0x17ba0 .. 0x17bf4: s->queue[kept++] = s->queue[j] for j < s->queued, an inline copy
   of the 32 bytes by four ld / sd pairs, after four UBSan checks: kept = 513 (a3 = 513 + j - kept is the same
   every turn), &s->queue[kept] wrapping, j - 1 > 511, &s->queue[j] wrapping. *)
Lemma tku_tail : forall (Q : machine_state -> Prop) (n : nat) (j0 j32 : list byte)
    (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B J : list byte) (taken kept len hd j : Z) (body B2 : list byte) (kept2 : Z),
  s2 = Z_to_bv 64 j -> s9 = Z_to_bv 64 kept ->
  a0 = Z_to_bv 64 (j - 1) -> a1 = Z_to_bv 64 (32 * j) ->
  a2 = Z_to_bv 64 (W_BASE_UBSAN + (OFF_g_s + 1760 + 32 * j)) -> a3 = Z_to_bv 64 (513 + j - kept) ->
  a4 = Z_to_bv 64 511 ->
  wmem rsegs m B -> g_fail_next B <= 1 ->
  rw_cells rsegs m bp [CB 1484 J] -> firstn (Z.to_nat len) J = body ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd)] -> rw_cells rsegs m blp [CB 8 JL] ->
  rw_cells rsegs m (bv_unsigned sp + -160) (FRL j0 j32) -> stk rsegs m lo (bv_unsigned sp + -160) ->
  mem_inv rsegs m -> munch TW m0 m -> wmono rsegs m0 m ->
  0 <= len <= 1484 -> 0 <= taken <= 512 -> 0 <= kept <= j -> 1 <= j -> j < S_queued B ->
  Z.to_nat (S_queued B - j) = S n ->
  take_tail_m B kept j (S n) = Some (B2, kept2) ->
  tku_exit Q B2 body len hd taken kept2 ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 s0 (Z_to_bv 64 taken)
                       a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 18144))
                       (Z_to_bv 64 len) s9 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 1760))
                       (Z_to_bv 64 18446744073709338543) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x17ba0) fc None m (seg_rom rsegs)).
Proof using All.
  intros Q n. induction n as [|n IH]; intros j0 j32 ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9
    t3 t4 t5 t6 m B J taken kept len hd j body B2 kept2 E2 E9 E0 E1 Ea2 E3 E4 WM GF BJ HJ BH BL FR ST MI MU WMO
    HL HT HK HJ1 HJQ HN HM K; subst a0 a1 a2 a3 a4 s2 s9.
  all: clear BP3 BL3 BH3 S1 S2 S3 SPm HA4 HA8 HAL.
  all: lazymatch type of HN with Z.to_nat _ = ?k => assert (HN' : S_queued B - j = Z.of_nat k) by lia end;
    clear HN.
  all: rewrite tk_tail_S in HM.
  all: destruct ((S_queue_N <=? j) || (S_queue_N <=? kept)) eqn:EB; [discriminate HM|].
  all: apply orb_false_iff in EB; destruct EB as [EB1 EB2]; apply Z.leb_gt in EB1, EB2;
    unfold S_queue_N in EB1, EB2.
  all: tk_lens.
  all: pose proof (u_at_range B A_S_queued 4) as RQ; change (u_at B A_S_queued 4) with (S_queued B) in RQ;
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RQ.
  all: unfold A_S_queue_bytes in HM; rewrite !Z.add_0_r in HM.
  (* 0x17ba0 beq a3,s2: the check of kept = 513 *)
  all: step. all: tk_cond false.
  (* 0x17ba4 slli a5,s9,5; 0x17ba8 bltu s11,a5 *)
  all: step. all: rewrite (unsigned_lit kept) by lia. all: rewrite Z.shiftl_mul_pow2 by lia.
  all: step. all: tk_cond false.
  (* 0x17bac bltu a4,a0; 0x17bb0 bltu s11,a1 *)
  all: step. all: tk_cond false.
  all: step. all: tk_cond false.
  (* 0x17bb4 ld a6,24(a2); 0x17bb8 add a5,s10,a5 *)
  all: step. all: step.
  all: replace (W_BASE_UBSAN + OFF_g_s + 1760 + kept * 2 ^ 5) with (W_BASE_UBSAN + (OFF_g_s + 1760 + 32 * kept))
         by lia.
  (* the four sd / ld pairs, offsets 24, 16, 8, 0 *)
  all: step.
  all: step. all: tk_rd.
  all: step.
  all: step. all: tk_rd.
  all: step.
  all: step. all: tk_rd.
  all: step.
  (* 0x17bd8 addi s2,s2,1; 0x17bdc lwu a5,0(s7) *)
  all: step. all: step. all: tk_rd.
  all: change (u_at B 19792 4) with (S_queued B).
  all: lazymatch goal with W : wmem rsegs _ (upd _ _ _) |- _ =>
         rewrite (tk_copy32 B (OFF_g_s + 1760 + 32 * kept) (OFF_g_s + 1760 + 32 * j)) in W by lia end.
  (* 0x17be0 .. 0x17bf0: a0, a2, a1, kept++, the loop test *)
  all: do 5 step.
  all: rewrite (unsigned_lit (j - 1)) by lia. all: rewrite (tk_swrap32_small (j - 1 + 1)) by lia.
  all: rewrite (unsigned_lit kept) by lia. all: rewrite (tk_swrap32_small (kept + 1)) by lia.
  - (* j + 1 = s->queued: 0x17bf4 j 0x17c04 *)
    tk_cond false. step.
    cbn [take_tail_m] in HM. injection HM as <- <-.
    apply tku_fold24 in FR.
    unfold tku_exit in K. eapply K; tk_prem.
    tk_upd_facts. exact GF.
  - (* the next entry *)
    tk_cond true.
    eapply (IH j0 j32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ taken (kept + 1) len hd (j + 1) body
              B2 kept2);
    [ reflexivity | reflexivity | (f_equal; lia) | (f_equal; lia) | (f_equal; lia) | (f_equal; lia) | reflexivity
    | eassumption | | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
    | eassumption | eassumption | eassumption | lia | lia | lia | lia | | | exact HM | exact K ].
    all: tk_upd_facts; first [exact GF | lia].
Qed.

(* 0x17b58 .. 0x17b9c: the break of :377-380. i + 1 >= s->queued ends the call at 0x17c04; else the copy loop
   starts with j = i + 1 and a3 = 513 + j - kept (sltiu / negw / and leave 513 - kept as it is while kept <= 513). *)
Lemma tku_break : forall (Q : machine_state -> Prop) (j0 j32 : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s2 s3 s6 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B1 J1 body1 : list byte) (i taken1 kept1 len1 hd1 : Z)
    (B2 bodyF : list byte) (lenF hdF takenF keptF : Z),
  s0 = Z_to_bv 64 (- i) -> s2 = Z_to_bv 64 i -> s3 = Z_to_bv 64 (32 * i) ->
  wmem rsegs m B1 -> g_fail_next B1 <= 1 ->
  rw_cells rsegs m bp [CB 1484 J1] -> firstn (Z.to_nat len1) J1 = body1 ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd1)] -> rw_cells rsegs m blp [CB 8 JL] ->
  rw_cells rsegs m (bv_unsigned sp + -160) (FRL j0 j32) -> stk rsegs m lo (bv_unsigned sp + -160) ->
  mem_inv rsegs m -> munch TW m0 m -> wmono rsegs m0 m ->
  0 <= len1 <= 1484 -> 0 <= taken1 <= 512 -> 0 <= kept1 <= i + 1 -> 0 <= i < 512 -> i < S_queued B1 ->
  match take_tail_m B1 kept1 (i + 1) (Z.to_nat (S_queued B1 - (i + 1))) with
  | None => None
  | Some (B3, kept2) => Some (B3, (body1, len1, hd1, taken1, kept2))
  end = Some (B2, (bodyF, lenF, hdF, takenF, keptF)) ->
  tku_exit Q B2 bodyF lenF hdF takenF keptF ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 s0 (Z_to_bv 64 taken1)
                       a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (W_BASE_UBSAN + (OFF_g_s + 32 * i)))
                       (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) s6 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 18144))
                       (Z_to_bv 64 len1) (Z_to_bv 64 kept1) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 1760))
                       (Z_to_bv 64 18446744073709338543) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x17b58) fc None m (seg_rom rsegs)).
Proof using All.
  intros Q j0 j32 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s2 s3 s6 t3 t4 t5 t6 m B1 J1 body1 i taken1 kept1 len1 hd1
    B2 bodyF lenF hdF takenF keptF E0 E2 E3 WM GF BJ HJ BH BL FR ST MI MU WMO HL HT HK HI HQ HM K.
  subst s0 s2 s3.
  tk_hide BP2. tk_hide BP3. tk_hide BL2. tk_hide BL3. tk_hide BH2. tk_hide BH3.
  tk_hide S1. tk_hide S2. tk_hide S3. tk_hide HAL.
  tk_lens.
  pose proof (u_at_range B1 A_S_queued 4) as RQ.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RQ.
  change (u_at B1 A_S_queued 4) with (S_queued B1) in RQ.
  (* 0x17b58 lw a0,0(s7); 0x17b5c li a1,1; 0x17b60 subw a1,a1,s0: a1 = i + 1 *)
  step. change (s32_at B1 19792) with (s32_at B1 A_S_queued).
  step. step.
  rewrite ?(unsigned_lit 1) by lia. rewrite tku_swrap_sub_neg. rewrite (tk_swrap32_small (1 + i)) by lia.
  (* 0x17b64 bgeu a1,a0 *)
  step.
  rewrite (tk_ltu_s32 (1 + i) B1 A_S_queued) by lia.
  change (u_at B1 A_S_queued 4) with (S_queued B1).
  destruct (Z.ltb_spec (1 + i) (S_queued B1)) as [Cq|Cq]; cbn [negb]; cbv iota.
  - (* the copy loop of :378-379 *)
    destruct (Z.to_nat (S_queued B1 - (i + 1))) as [|nt] eqn:Ent; [lia|].
    destruct (take_tail_m B1 kept1 (i + 1) (S nt)) as [[B3 kept2]|] eqn:ET; [|discriminate HM].
    injection HM as <- <- <- <- <- <-.
    (* 0x17b68 negw a0,s0 *)
    step.
    rewrite ?(unsigned_lit 0) by lia. rewrite tku_swrap_sub_neg. rewrite (tk_swrap32_small (0 + i)) by lia.
    (* 0x17b6c addi a1,s3,32; addi a2,s4,1792; addi s2,s2,1; li a3,513 *)
    do 4 step.
    (* 0x17b7c subw a3,a3,s9 *)
    step.
    rewrite ?(unsigned_lit 513) by lia. rewrite (unsigned_lit kept1) by lia.
    rewrite (tk_swrap32_small (513 - kept1)) by lia.
    (* 0x17b80 sltiu a4,a3,514 *)
    step. rewrite (tku_sltiu1 (513 - kept1)) by lia.
    (* 0x17b84 negw a4,a4 *)
    step.
    rewrite ?(unsigned_lit 0) by lia. rewrite ?(unsigned_lit 1) by lia. change (bv_swrap 32 (0 - 1)) with (-1).
    (* 0x17b88 and a3,a4,a3 *)
    step. rewrite (tku_land_m1 (513 - kept1)) by lia.
    (* 0x17b8c subw a3,a3,s0 *)
    step.
    rewrite (unsigned_lit (513 - kept1)) by lia. rewrite tku_swrap_sub_neg.
    rewrite (tk_swrap32_small (513 - kept1 + i)) by lia.
    (* 0x17b90 addi a3,a3,1; slli a3,a3,32; srli a3,a3,32 *)
    step. step. step. rewrite (tk_zext32 (513 - kept1 + i + 1)) by lia.
    (* 0x17b9c li a4,511 *)
    step.
    eapply (tku_tail Q nt j0 j32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ taken1 kept1 len1 hd1 (i + 1)
              body1 B3 kept2);
    [ (f_equal; lia) | reflexivity | (f_equal; lia) | (f_equal; lia) | (f_equal; lia) | (f_equal; lia)
    | reflexivity
    | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST | exact MI | exact MU
    | exact WMO | lia | lia | lia | lia | lia | exact Ent | exact ET | exact K ].
  - (* i + 1 = s->queued: the copy loop does not run *)
    replace (Z.to_nat (S_queued B1 - (i + 1))) with 0%nat in HM by lia.
    cbn [take_tail_m] in HM. injection HM as <- <- <- <- <- <-.
    apply tku_fold24 in FR.
    unfold tku_exit in K. eapply K;
    [ exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
    | exact MI | exact MU | exact WMO | lia | lia | lia ].
Qed.

(* The state at the loop head 0x17a5c of :358-382, with the turn i of take_loop_m still to run: s0 = -i, s2 = i,
   s3 = 32 i, s11 = ~&s->queue[0]. *)
Definition tku_head (Q : machine_state -> Prop) (n : nat) (B : list byte) (i taken kept len hd : Z)
    (body B2 bodyF : list byte) (lenF hdF takenF keptF : Z) : Prop :=
  forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 t3 t4 t5 t6 : word) (m : word -> option byte)
         (J j0 j32 : list byte),
    s0 = Z_to_bv 64 (- i) -> s2 = Z_to_bv 64 i -> s3 = Z_to_bv 64 (32 * i) ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    rw_cells rsegs m bp [CB 1484 J] -> firstn (Z.to_nat len) J = body ->
    rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd)] -> rw_cells rsegs m blp [CB 8 JL] ->
    rw_cells rsegs m (bv_unsigned sp + -160) (FRL j0 j32) -> stk rsegs m lo (bv_unsigned sp + -160) ->
    mem_inv rsegs m ->
    munch TW m0 m -> wmono rsegs m0 m ->
    0 <= len <= 1484 -> 0 <= hd < 256 -> 0 <= taken <= 512 -> 0 <= kept -> taken + kept = i ->
    i < S_queued B -> Z.to_nat (S_queued B - i) = n ->
    take_loop_m B allow i taken kept len hd body n = Some (B2, (bodyF, lenF, hdF, takenF, keptF)) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 s0 (Z_to_bv 64 taken)
                         a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) s6
                         (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 18144)) (Z_to_bv 64 len) (Z_to_bv 64 kept)
                         (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 1760)) (Z_to_bv 64 18446744073709338543)
                         t3 t4 t5 t6)
                    F (Z_to_bv 64 0x17a5c) fc None m (seg_rom rsegs)).

(* 0x17b30 .. 0x17b54: the end of a turn (:377, :381), either the next turn, the break, or the exit. *)
Lemma tku_bottom : forall (Q : machine_state -> Prop) (n : nat) (j0 j32 : list byte)
    (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B1 J1 body1 : list byte) (i taken1 kept1 len1 hd1 : Z)
    (B2 bodyF : list byte) (lenF hdF takenF keptF : Z),
  s0 = Z_to_bv 64 (- i) -> s2 = Z_to_bv 64 i -> s3 = Z_to_bv 64 (32 * i) ->
  wmem rsegs m B1 -> g_fail_next B1 <= 1 ->
  rw_cells rsegs m bp [CB 1484 J1] -> firstn (Z.to_nat len1) J1 = body1 ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd1)] -> rw_cells rsegs m blp [CB 8 JL] ->
  rw_cells rsegs m (bv_unsigned sp + -160) (FRL j0 j32) -> stk rsegs m lo (bv_unsigned sp + -160) ->
  mem_inv rsegs m -> munch TW m0 m -> wmono rsegs m0 m ->
  0 <= len1 <= 1484 -> 0 <= hd1 < 256 -> 0 <= taken1 <= 512 -> 0 <= kept1 -> taken1 + kept1 = i + 1 ->
  0 <= i < 512 -> i < S_queued B1 -> Z.to_nat (S_queued B1 - i) = S n ->
  (if (taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1) then
     match take_tail_m B1 kept1 (i + 1) (Z.to_nat (S_queued B1 - (i + 1))) with
     | None => None
     | Some (B3, kept2) => Some (B3, (body1, len1, hd1, taken1, kept2))
     end
   else take_loop_m B1 allow (i + 1) taken1 kept1 len1 hd1 body1 n)
  = Some (B2, (bodyF, lenF, hdF, takenF, keptF)) ->
  tku_head Q n B1 (i + 1) taken1 kept1 len1 hd1 body1 B2 bodyF lenF hdF takenF keptF ->
  tku_exit Q B2 bodyF lenF hdF takenF keptF ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 s0 (Z_to_bv 64 taken1)
                       a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (W_BASE_UBSAN + (OFF_g_s + 32 * i)))
                       (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) s6 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 18144))
                       (Z_to_bv 64 len1) (Z_to_bv 64 kept1) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 1760))
                       (Z_to_bv 64 18446744073709338543) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x17b30) fc None m (seg_rom rsegs)).
Proof using All.
  intros Q n j0 j32 ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 t3 t4 t5 t6 m B1 J1 body1 i taken1 kept1 len1
    hd1 B2 bodyF lenF hdF takenF keptF E0 E2 E3 WM GF BJ HJ BH BL FR ST MI MU WMO HL HH HT HK HI HI512 HQ HN HM
    HD K.
  subst s0 s2 s3.
  tk_hide BP2. tk_hide BP3. tk_hide BL2. tk_hide BL3. tk_hide BH2. tk_hide BH3.
  tk_hide S1. tk_hide S2. tk_hide S3. tk_hide HAL.
  tk_lens.
  pose proof (u_at_range B1 A_S_cfg_max_cmds 4) as RMC. pose proof (u_at_range B1 A_S_cfg_max_body 4) as RMB.
  pose proof (u_at_range B1 A_S_queued 4) as RQ.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RMC, RMB, RQ.
  change (u_at B1 A_S_cfg_max_cmds 4) with (S_cfg_max_cmds B1) in RMC.
  change (u_at B1 A_S_cfg_max_body 4) with (S_cfg_max_body B1) in RMB.
  change (u_at B1 A_S_queued 4) with (S_queued B1) in RQ.
  assert (HN' : S_queued B1 - i = Z.of_nat (S n)) by lia. clear HN.
  (* 0x17b30 lw a0,52(s5); 0x17b34 beq s1,a0 *)
  step. change (s32_at B1 1700) with (s32_at B1 A_S_cfg_max_cmds). step.
  rewrite (tk_eqb_s32 taken1 B1 A_S_cfg_max_cmds) by lia.
  change (u_at B1 A_S_cfg_max_cmds 4) with (S_cfg_max_cmds B1).
  destruct (Z.eqb_spec taken1 (S_cfg_max_cmds B1)) as [Emc|Emc]; cbv iota.
  - (* taken = max_cmds: the break *)
    replace ((taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1)) with true in HM
      by (symmetry; apply orb_true_intro; left; apply Z.eqb_eq; exact Emc).
    cbv iota in HM.
    eapply (tku_break Q j0 j32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m B1 J1 body1 i taken1 kept1 len1 hd1
              B2 bodyF lenF hdF takenF keptF);
    [ reflexivity | reflexivity | reflexivity
    | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
    | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | exact HM | exact K ].
  - (* 0x17b38 lwu a0,56(s5); 0x17b3c beq s8,a0 *)
    step. change (u_at B1 1704 4) with (S_cfg_max_body B1). step.
    rewrite (tk_eqb_lits len1 (S_cfg_max_body B1)) by lia.
    destruct (Z.eqb_spec len1 (S_cfg_max_body B1)) as [Emb|Emb]; cbv iota.
    + (* len = max_body: the break *)
      replace ((taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1)) with true in HM
        by (symmetry; apply orb_true_intro; right; apply Z.eqb_eq; exact Emb).
      cbv iota in HM.
      eapply (tku_break Q j0 j32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m B1 J1 body1 i taken1 kept1 len1 hd1
                B2 bodyF lenF hdF takenF keptF);
      [ reflexivity | reflexivity | reflexivity
      | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
      | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | exact HM | exact K ].
    + (* neither: 0x17b40 .. 0x17b50, the next turn or the exit *)
      replace ((taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1)) with false in HM
        by (symmetry; apply orb_false_intro; apply Z.eqb_neq; assumption).
      cbv iota in HM.
      step. change (u_at B1 19792 4) with (S_queued B1).
      do 4 step.
      rewrite (tk_ltu_lits (i + 1) (S_queued B1)) by lia.
      destruct (Z.ltb_spec (i + 1) (S_queued B1)) as [Cq|Cq]; cbv iota.
      * (* back to the loop head *)
        unfold tku_head in HD. eapply HD;
        [ (f_equal; lia) | reflexivity | (f_equal; lia)
        | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
        | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HM ].
      * (* i + 1 = s->queued: the model's fuel runs out; 0x17b54 j 0x17c04 *)
        replace n with 0%nat in HM by lia.
        cbn [take_loop_m] in HM. injection HM as <- <- <- <- <- <-.
        step.
        apply tku_fold24 in FR.
        unfold tku_exit in K. eapply K;
        [ exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
        | exact MI | exact MU | exact WMO | lia | lia | lia ].
Qed.

End Walk.

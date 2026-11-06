From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TSess0 TTake.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memcpy_c diginet_body_check_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TContract TSessC take_c.
Import ListNotations.
Open Scope Z_scope.

Ltac solve_load ::= first [ tk_solve_load_world | wk_solve_load_world | solve_load_base | solve_load_image ].
Ltac solve_store ::= first [ tk_solve_store_world | wk_solve_store_world | wk_solve_store_kit ].
Ltac mem_after_store_opt ::=
  try fix_lit_store; first [ tk_world_after_store | wk_world_after_store | wk_mem_after_store_opt_kit ].

(** * The walk *)

Abbreviation tk_fr j blpw allw r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra :=
  [CB 8 j; C8 blpw; C8 allw; C8 r11; C8 r10; C8 r9; C8 r8; C8 r7; C8 r6; C8 r5; C8 r4; C8 r3; C8 r2;
   C8 r1; C8 r0; C8 rra].

Section Walk.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (lo bp blp hdp allow : Z) (JL : list byte)
  (rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra : word).
Hypotheses (HAL : - 2 ^ 31 <= allow < 2 ^ 31)
  (BP0 : 0 < bp) (BP1 : bp + 1484 < 2 ^ 64)
  (BP2 : bp + 1484 <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= bp)
  (BP3 : bp + 1484 <= bv_unsigned sp - 272 \/ bv_unsigned sp <= bp)
  (BL0 : 0 < blp) (BL1 : blp + 8 < 2 ^ 64)
  (BL2 : blp + 8 <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= blp)
  (BL3 : blp + 8 <= bv_unsigned sp - 272 \/ bv_unsigned sp <= blp)
  (BH0 : 0 < hdp) (BH1 : hdp + 4 < 2 ^ 64)
  (BH2 : hdp + 4 <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= hdp)
  (BH3 : hdp + 4 <= bv_unsigned sp - 272 \/ bv_unsigned sp <= hdp)
  (S1 : bp + 1484 <= blp \/ blp + 8 <= bp) (S2 : bp + 1484 <= hdp \/ hdp + 4 <= bp)
  (S3 : blp + 8 <= hdp \/ hdp + 4 <= blp)
  (LO : lo + 272 <= bv_unsigned sp) (WO : W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 272)
  (Rsp : 0 <= bv_unsigned sp < 2 ^ 64) (Hlo : 0 <= lo)
  (Ew : W_LEN = 65616) (Ew0 : W_BASE_PLAIN = 206736) (Ew1 : OFF_g_s = 1648).

Local Abbreviation FRC jf := (tk_fr jf (Z_to_bv 64 blp) (Z_to_bv 64 allow) rs11 rs10 rs9 rs8 rs7 rs6 rs5 rs4 rs3 rs2
                         rs1 rs0 rra).
Local Abbreviation TW := [(bv_unsigned sp - 272, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN);
                      (bp, bp + 1484); (blp, blp + 8); (hdp, hdp + 4)].

(* The state at 0x17358 (s->queued = kept; *body_len = len; return taken), with the memory facts the epilogue
   needs. *)
Definition tk_exit (Q : machine_state -> Prop) (jf : list byte) (B2 bodyF : list byte)
    (lenF hdF takenF keptF : Z) : Prop :=
  forall (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s9' s11' t3' t4' t5' t6' : word)
         (m' : word -> option byte) (JF : list byte),
    wmem rsegs m' B2 -> g_fail_next B2 <= 1 ->
    rw_cells rsegs m' bp [CB 1484 JF] -> firstn (Z.to_nat lenF) JF = bodyF ->
    rw_cells rsegs m' hdp [C4 (Z_to_bv 64 hdF)] -> rw_cells rsegs m' blp [CB 8 JL] ->
    rw_cells rsegs m' (bv_unsigned sp + -128) (FRC jf) -> stk rsegs m' lo (bv_unsigned sp + -128) ->
    mem_inv rsegs m' ->
    munch TW m0 m' -> wmono rsegs m0 m' ->
    0 <= lenF <= 1484 -> 0 <= takenF <= 512 -> 0 <= keptF <= 512 ->
    evt rsegs Q (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' s0' (Z_to_bv 64 takenF)
                         a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6'
                         (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) (Z_to_bv 64 lenF) s9' (Z_to_bv 64 keptF) s11'
                         t3' t4' t5' t6')
                    F (Z_to_bv 64 0x17358) fc None m' (seg_rom rsegs)).

(* The loop of :378-379 at 0x17318 .. 0x17354: s->queue[kept++] = s->queue[j] for j < s->queued, an inline copy
   of the 32 bytes by four ld / sd pairs. *)
Lemma tk_tail : forall (Q : machine_state -> Prop) (n : nat) (jf : list byte)
    (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B J : list byte) (taken kept len hd j : Z) (body B2 : list byte) (kept2 : Z),
  s0 = Z_to_bv 64 j -> s9 = Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 1760) -> s10 = Z_to_bv 64 kept ->
  s11 = Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * j)) ->
  wmem rsegs m B -> g_fail_next B <= 1 ->
  rw_cells rsegs m bp [CB 1484 J] -> firstn (Z.to_nat len) J = body ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd)] -> rw_cells rsegs m blp [CB 8 JL] ->
  rw_cells rsegs m (bv_unsigned sp + -128) (FRC jf) -> stk rsegs m lo (bv_unsigned sp + -128) -> mem_inv rsegs m ->
  munch TW m0 m -> wmono rsegs m0 m ->
  0 <= len <= 1484 -> 0 <= taken <= 512 -> 0 <= kept <= j -> j < S_queued B -> Z.to_nat (S_queued B - j) = S n ->
  take_tail_m B kept j (S n) = Some (B2, kept2) ->
  tk_exit Q jf B2 body len hd taken kept2 ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0 (Z_to_bv 64 taken)
                       a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144))
                       (Z_to_bv 64 len) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x17318) fc None m (seg_rom rsegs)).
Proof.
  intros Q n. induction n as [|n IH]; intros jf ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11
    t3 t4 t5 t6 m B J taken kept len hd j body B2 kept2 E0 E9 E10 E11 WM GF BJ HJ BH BL FR ST MI MU WMO
    HL HT HK HJQ HN HM K; subst s0 s9 s10 s11.
  all: clear BP3 BL3 BH3 S1 S2 S3.
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
  (* 0x17318 .. 0x17324: ld a0, 24(s11); a1 = &s->queue[kept] *)
  all: do 4 step.
  all: rewrite (tk_zext_shl5 kept) by lia.
  all: replace (W_BASE_PLAIN + OFF_g_s + 1760 + 32 * kept) with (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * kept))
         by lia.
  (* the four ld / sd pairs *)
  all: step.
  all: step. all: tk_rd.
  all: step.
  all: step. all: tk_rd.
  all: step.
  all: step. all: tk_rd.
  all: step.
  (* 0x17344: lwu a0, 0(s7) = s->queued *)
  all: step. all: tk_rd.
  all: change (u_at B 19792 4) with (S_queued B).
  all: lazymatch goal with W : wmem rsegs _ (upd _ _ _) |- _ =>
         rewrite (tk_copy32 B (OFF_g_s + 1760 + 32 * kept) (OFF_g_s + 1760 + 32 * j)) in W by lia end.
  (* 0x17348 .. 0x17354: kept++, j++, the entry pointer, the loop test *)
  all: do 4 step.
  - (* j + 1 = s->queued: the loop ends at 0x17358 *)
    tk_cond false.
    cbn [take_tail_m] in HM. injection HM as <- <-.
    unfold tk_exit in K. eapply K; tk_prem.
    tk_upd_facts. exact GF.
  - (* the next entry *)
    tk_cond true.
    eapply IH; [ reflexivity | reflexivity | reflexivity | f_equal; lia | eassumption | | eassumption
               | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
               | eassumption | eassumption | lia | lia | lia | | | exact HM | exact K ].
    all: tk_upd_facts; first [exact GF | lia].
Qed.

(* The state at the loop head 0x17240 of :358-382, with the turn i of take_loop_m still to run. *)
Definition tk_head (Q : machine_state -> Prop) (n : nat) (jf B : list byte) (i taken kept len hd : Z)
    (body B2 bodyF : list byte) (lenF hdF takenF keptF : Z) : Prop :=
  forall (ra t0 t1 t2 s0 a1 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word) (m : word -> option byte) (J : list byte),
    wmem rsegs m B -> g_fail_next B <= 1 ->
    rw_cells rsegs m bp [CB 1484 J] -> firstn (Z.to_nat len) J = body ->
    rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd)] -> rw_cells rsegs m blp [CB 8 JL] ->
    rw_cells rsegs m (bv_unsigned sp + -128) (FRC jf) -> stk rsegs m lo (bv_unsigned sp + -128) ->
    mem_inv rsegs m ->
    munch TW m0 m -> wmono rsegs m0 m ->
    0 <= len <= 1484 -> 0 <= hd < 256 -> 0 <= taken <= 512 -> 0 <= kept -> taken + kept = i ->
    i < S_queued B -> Z.to_nat (S_queued B - i) = n ->
    take_loop_m B allow i taken kept len hd body n = Some (B2, (bodyF, lenF, hdF, takenF, keptF)) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0 (Z_to_bv 64 taken)
                         (Z_to_bv 64 (s32_at B A_S_cfg_max_cmds)) a1 (Z_to_bv 64 (i + 1)) a3 a4 a5 a6 a7
                         (Z_to_bv 64 hdp) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
                         (Z_to_bv 64 bp) s6 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) (Z_to_bv 64 len)
                         (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 1760)) (Z_to_bv 64 kept)
                         (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * (i + 1)))) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x17240) fc None m (seg_rom rsegs)).

(* 0x172d4 .. 0x172f8 and 0x1730c .. 0x17314: the end of a turn (:377-381), either the next turn, the loop of
   :378-379, or the exit. *)
Lemma tk_bottom : forall (Q : machine_state -> Prop) (n : nat) (jf : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s6 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B1 J1 body1 : list byte) (i taken1 kept1 len1 hd1 : Z)
    (B2 bodyF : list byte) (lenF hdF takenF keptF : Z),
  s0 = Z_to_bv 64 (i + 1) ->
  wmem rsegs m B1 -> g_fail_next B1 <= 1 ->
  rw_cells rsegs m bp [CB 1484 J1] -> firstn (Z.to_nat len1) J1 = body1 ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd1)] -> rw_cells rsegs m blp [CB 8 JL] ->
  rw_cells rsegs m (bv_unsigned sp + -128) (FRC jf) -> stk rsegs m lo (bv_unsigned sp + -128) ->
  mem_inv rsegs m ->
  munch TW m0 m -> wmono rsegs m0 m ->
  0 <= len1 <= 1484 -> 0 <= hd1 < 256 -> 0 <= taken1 <= 512 -> 0 <= kept1 -> taken1 + kept1 = i + 1 ->
  0 <= i < 512 -> i < S_queued B1 -> Z.to_nat (S_queued B1 - i) = S n ->
  (if (taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1) then
     match take_tail_m B1 kept1 (i + 1) (Z.to_nat (S_queued B1 - (i + 1))) with
     | None => None
     | Some (B3, kept2) => Some (B3, (body1, len1, hd1, taken1, kept2))
     end
   else take_loop_m B1 allow (i + 1) taken1 kept1 len1 hd1 body1 n)
  = Some (B2, (bodyF, lenF, hdF, takenF, keptF)) ->
  tk_head Q n jf B1 (i + 1) taken1 kept1 len1 hd1 body1 B2 bodyF lenF hdF takenF keptF ->
  tk_exit Q jf B2 bodyF lenF hdF takenF keptF ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0 (Z_to_bv 64 taken1)
                       a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 hdp) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
                       (Z_to_bv 64 bp) s6 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) (Z_to_bv 64 len1)
                       (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 1760)) (Z_to_bv 64 kept1)
                       (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * (i + 1)))) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x172d4) fc None m (seg_rom rsegs)).
Proof.
  intros Q n jf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s6 t3 t4 t5 t6 m B1 J1 body1 i taken1 kept1 len1 hd1
    B2 bodyF lenF hdF takenF keptF E0 WM GF BJ HJ BH BL FR ST MI MU WMO HL HH HT HK HI HI512 HQ HN HM HD K.
  subst s0.
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
  (* 0x172d4: lw a0,52(s4); 0x172d8: beq s1,a0 *)
  step. change (s32_at B1 1700) with (s32_at B1 A_S_cfg_max_cmds). step.
  rewrite (tk_eqb_s32 taken1 B1 A_S_cfg_max_cmds) by lia.
  change (u_at B1 A_S_cfg_max_cmds 4) with (S_cfg_max_cmds B1).
  destruct (Z.eqb_spec taken1 (S_cfg_max_cmds B1)) as [Emc|Emc]; cbv iota.
  - (* taken = max_cmds: 0x1730c lw a1,0(s7); 0x17310 sext.w a1,a1; 0x17314 bgeu s3,a1 *)
    replace ((taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1)) with true in HM
      by (symmetry; apply orb_true_intro; left; apply Z.eqb_eq; exact Emc).
    cbv iota in HM.
    step. change (s32_at B1 19792) with (s32_at B1 A_S_queued). step. rewrite tk_sextw_s32. step.
    rewrite (tk_ltu_s32 (i + 1) B1 A_S_queued) by lia.
    change (u_at B1 A_S_queued 4) with (S_queued B1).
    destruct (Z.ltb_spec (i + 1) (S_queued B1)) as [Cq|Cq]; cbn [negb]; cbv iota.
    + (* the loop of :378-379 *)
      destruct (Z.to_nat (S_queued B1 - (i + 1))) as [|nt] eqn:Ent; [lia|].
      destruct (take_tail_m B1 kept1 (i + 1) (S nt)) as [[B3 kept2]|] eqn:ET; [|discriminate HM].
      injection HM as <- <- <- <- <- <-.
      eapply (tk_tail Q nt jf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m B1 J1 taken1 kept1 len1 hd1 (i + 1) body1 B3 kept2);
        [ reflexivity | reflexivity | reflexivity | reflexivity
        | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
        | exact MI | exact MU | exact WMO | lia | lia | lia | exact Cq | exact Ent | exact ET | exact K ].
    + (* i + 1 = s->queued: the loop does not run *)
      replace (Z.to_nat (S_queued B1 - (i + 1))) with 0%nat in HM by lia.
      cbn [take_tail_m] in HM. injection HM as <- <- <- <- <- <-.
      unfold tk_exit in K. eapply K;
      [ exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
      | exact MI | exact MU | exact WMO | lia | lia | lia ].
  - (* taken <> max_cmds: 0x172dc lwu a2,56(s4); 0x172e0 lwu a1,0(s7); 0x172e4 beq s8,a2 *)
    step. change (u_at B1 1704 4) with (S_cfg_max_body B1).
    step. change (u_at B1 19792 4) with (S_queued B1). step.
    rewrite (tk_eqb_lits len1 (S_cfg_max_body B1)) by lia.
    destruct (Z.eqb_spec len1 (S_cfg_max_body B1)) as [Emb|Emb]; cbv iota.
    + (* len = max_body: 0x17310 *)
      replace ((taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1)) with true in HM
        by (symmetry; apply orb_true_intro; right; apply Z.eqb_eq; exact Emb).
      cbv iota in HM.
      step.
      replace (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (S_queued B1)) + 0)) with (s32_at B1 A_S_queued)
        by (symmetry; apply (tk_sextw_u B1 A_S_queued)).
      step.
      rewrite (tk_ltu_s32 (i + 1) B1 A_S_queued) by lia.
      change (u_at B1 A_S_queued 4) with (S_queued B1).
      destruct (Z.ltb_spec (i + 1) (S_queued B1)) as [Cq|Cq]; cbn [negb]; cbv iota.
      * destruct (Z.to_nat (S_queued B1 - (i + 1))) as [|nt] eqn:Ent; [lia|].
        destruct (take_tail_m B1 kept1 (i + 1) (S nt)) as [[B3 kept2]|] eqn:ET; [|discriminate HM].
        injection HM as <- <- <- <- <- <-.
        eapply (tk_tail Q nt jf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m B1 J1 taken1 kept1 len1 hd1 (i + 1) body1 B3 kept2);
        [ reflexivity | reflexivity | reflexivity | reflexivity
        | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
        | exact MI | exact MU | exact WMO | lia | lia | lia | exact Cq | exact Ent | exact ET | exact K ].
      * replace (Z.to_nat (S_queued B1 - (i + 1))) with 0%nat in HM by lia.
        cbn [take_tail_m] in HM. injection HM as <- <- <- <- <- <-.
        unfold tk_exit in K. eapply K;
        [ exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
        | exact MI | exact MU | exact WMO | lia | lia | lia ].
    + (* neither: 0x172e8 .. 0x172f4, the next turn or the exit *)
      replace ((taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1)) with false in HM
        by (symmetry; apply orb_false_intro; apply Z.eqb_neq; assumption).
      cbv iota in HM.
      step. step. step.
      rewrite (unsigned_lit (i + 1)) by lia. rewrite (tk_swrap32_small (i + 1 + 1)) by lia.
      step.
      rewrite (tk_ltu_lits (i + 1) (S_queued B1)) by lia.
      destruct (Z.ltb_spec (i + 1) (S_queued B1)) as [Cq|Cq]; cbv iota.
      * (* back to the loop head *)
        replace (Z_to_bv 64 (i + 2)) with (Z_to_bv 64 (i + 1 + 1)) by (f_equal; lia).
        replace (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * (i + 1)) + 32))
          with (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * (i + 1 + 1)))) by (f_equal; lia).
        unfold tk_head in HD. eapply HD;
        [ exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
        | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HM ].
      * (* i + 1 = s->queued: the model's fuel runs out *)
        replace n with 0%nat in HM by lia.
        cbn [take_loop_m] in HM. injection HM as <- <- <- <- <- <-.
        step.
        unfold tk_exit in K. eapply K;
        [ exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
        | exact MI | exact MU | exact WMO | lia | lia | lia ].
Qed.

(* 0x172ac .. 0x172d0: the command does not fit (:372-376), s->queue[kept++] = *c unless kept = i. *)
Lemma tk_notfit : memcpy_contract -> forall (Q : machine_state -> Prop) (n : nat) (jf : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B J body : list byte) (i taken kept len hd : Z)
    (B1 B2 bodyF : list byte) (lenF hdF takenF keptF : Z),
  wmem rsegs m B -> g_fail_next B <= 1 ->
  rw_cells rsegs m bp [CB 1484 J] -> firstn (Z.to_nat len) J = body ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd)] -> rw_cells rsegs m blp [CB 8 JL] ->
  rw_cells rsegs m (bv_unsigned sp + -128) (FRC jf) -> stk rsegs m lo (bv_unsigned sp + -128) ->
  mem_inv rsegs m ->
  munch TW m0 m -> wmono rsegs m0 m ->
  0 <= len <= 1484 -> 0 <= hd < 256 -> 0 <= taken <= 512 -> 0 <= kept <= i -> taken + kept = i ->
  0 <= i < 512 -> i < S_queued B -> Z.to_nat (S_queued B - i) = S n ->
  B1 = (if kept =? i then B else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32)) ->
  (if (taken =? S_cfg_max_cmds B1) || (len =? S_cfg_max_body B1) then
     match take_tail_m B1 (kept + 1) (i + 1) (Z.to_nat (S_queued B1 - (i + 1))) with
     | None => None
     | Some (B3, kept2) => Some (B3, (body, len, hd, taken, kept2))
     end
   else take_loop_m B1 allow (i + 1) taken (kept + 1) len hd body n)
  = Some (B2, (bodyF, lenF, hdF, takenF, keptF)) ->
  tk_head Q n jf B1 (i + 1) taken (kept + 1) len hd body B2 bodyF lenF hdF takenF keptF ->
  tk_exit Q jf B2 bodyF lenF hdF takenF keptF ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (i + 1))
                       (Z_to_bv 64 taken) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 hdp) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
                       (Z_to_bv 64 bp) (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * i)))
                       (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) (Z_to_bv 64 len)
                       (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 1760)) (Z_to_bv 64 kept)
                       (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * (i + 1)))) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x172ac) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY Q n jf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m B J body i taken kept len hd
    B1 B2 bodyF lenF hdF takenF keptF WM GF BJ HJ BH BL FR ST MI MU WMO HL HH HT HK HI HI512 HQ HN EQ1 HM HD K.
  tk_lens.
  unfold A_S_queue_bytes in EQ1. rewrite !Z.add_0_r in EQ1.
  (* 0x172ac .. 0x172b8: a1 = i; a0 = kept; beq a1,a0 *)
  do 3 step.
  rewrite (tk_zext32 kept) by lia.
  step.
  lazymatch goal with
  | |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 kept)] =>
      rewrite (tk_eqb_lits x kept) by lia; destruct (Z.eqb_spec x kept) as [Eki|Eki]
  end; cbv iota.
  - (* kept = i: 0x172d0 kept++ *)
    replace (kept =? i) with true in EQ1 by (symmetry; apply Z.eqb_eq; lia). cbv iota in EQ1. subst B1.
    step.
    eapply tk_bottom;
    [ reflexivity | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
    | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HN | exact HM
    | exact HD | exact K ].
  - (* kept < i: 0x172bc .. 0x172cc memcpy (&s->queue[kept], &s->queue[i], 32) *)
    replace (kept =? i) with false in EQ1 by (symmetry; apply Z.eqb_neq; lia). cbv iota in EQ1.
    do 2 step.
    rewrite (unsigned_lit kept) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    do 3 step.
    assert (UD : bv_unsigned (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 1760 + kept * 2 ^ 5))
                 = W_BASE_PLAIN + OFF_g_s + 1760 + kept * 2 ^ 5) by (apply unsigned_lit; lia).
    assert (US : bv_unsigned (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * i)))
                 = W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * i)) by (apply unsigned_lit; lia).
    assert (U32 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
    eapply evt_cut.
    { eapply MCPY with (src := sub B (OFF_g_s + 1760 + 32 * i) 32).
      - rewrite US.
        apply (wm_src rsegs W_BASE_PLAIN m B (OFF_g_s + 1760 + 32 * i) 32); [exact WM | lia | lia | lia].
      - rewrite U32. apply length_sub; lia.
      - rewrite UD, U32.
        apply (wm_piece rsegs W_BASE_PLAIN m B (OFF_g_s + 1760 + 32 * kept) 32);
          [exact WM | lia | lia | lia | lia].
      - rewrite UD, US, U32. lia.
      - exact MI. }
    intros ms' PO; hnf in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & DSTc &
                    SRCc).
    subst ms'. rewrite UD, U32 in MUc, DSTc.
    rewrite (ret_pc_even 0x172d0) by (first [lia | reflexivity]).
    assert (WM2 : wmem rsegs m2 (upd B (OFF_g_s + 1760 + 32 * kept) (sub B (OFF_g_s + 1760 + 32 * i) 32)))
      by (apply (wm_fill rsegs W_BASE_PLAIN m m2 B (W_BASE_PLAIN + OFF_g_s + 1760 + kept * 2 ^ 5)
                   (OFF_g_s + 1760 + 32 * kept) 32);
          [exact WM | exact MUc | exact WMc | exact DSTc | lia | lia | lia | lia]).
    pose proof (tk_stk_rebuild m m2 lo (bv_unsigned sp + -128) _ 32 _ ST MUc WMc DSTc
                  ltac:(cbn [cells_size csize]; lia)) as ST2.
    clear WM ST DSTc SRCc.
    transport_after_call rsegs m m2 MUc WMc.
    clear MUc WMc MI.
    step.
    subst B1.
    eapply tk_bottom;
    [ reflexivity | exact WM2 | (tk_upd_facts; exact GF) | exact BJ | exact HJ | exact BH | exact BL
    | exact FR | exact ST2 | exact MI2 | exact MU | exact WMO | lia | lia | lia | lia | lia | lia
    | (tk_upd_facts; lia) | (tk_upd_facts; exact HN) | exact HM | exact HD | exact K ].
Qed.

(* 0x17264 .. 0x172a0: the command fits the counters and the pacing (:360-361), so the memcpy of :365 and
   diginet_body_check of :366 run; then either the update of :368-371 or the keep of :372-376. *)
Lemma tk_fit : diginet_body_check_contract -> memcpy_contract ->
  forall (Q : machine_state -> Prop) (n : nat) (jf : list byte)
    (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B J body : list byte) (i taken kept len hd : Z)
    (B2 bodyF : list byte) (lenF hdF takenF keptF : Z),
  wmem rsegs m B -> g_fail_next B <= 1 ->
  rw_cells rsegs m bp [CB 1484 J] -> firstn (Z.to_nat len) J = body ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd)] -> rw_cells rsegs m blp [CB 8 JL] ->
  rw_cells rsegs m (bv_unsigned sp + -128) (FRC jf) -> stk rsegs m lo (bv_unsigned sp + -128) ->
  mem_inv rsegs m ->
  munch TW m0 m -> wmono rsegs m0 m ->
  0 <= len <= 1484 -> 0 <= hd < 256 -> 0 <= taken <= 512 -> 0 <= kept <= i -> taken + kept = i ->
  0 <= i < 512 -> i < S_queued B -> Z.to_nat (S_queued B - i) = S n ->
  (if DIGINET_MAX_BODY_LEN <? len + S_queue_len B i then None
   else
   let '(B1, body1, len1, taken1, hd1, kept1) :=
     if body_check (body ++ sub B (A_S_queue_bytes i) (Z.to_nat (S_queue_len B i))) =? DIGINET_OK
     then (B, body ++ sub B (A_S_queue_bytes i) (Z.to_nat (S_queue_len B i)), len + S_queue_len B i,
           taken + 1, Z.lor hd (S_queue_display B i), kept)
     else ((if kept =? i then B else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32)),
           body, len, taken, hd, kept + 1) in
   if (taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1) then
     match take_tail_m B1 kept1 (i + 1) (Z.to_nat (S_queued B1 - (i + 1))) with
     | None => None
     | Some (B3, kept2) => Some (B3, (body1, len1, hd1, taken1, kept2))
     end
   else take_loop_m B1 allow (i + 1) taken1 kept1 len1 hd1 body1 n)
  = Some (B2, (bodyF, lenF, hdF, takenF, keptF)) ->
  (forall (B1 body1 : list byte) (taken1 kept1 len1 hd1 : Z),
     tk_head Q n jf B1 (i + 1) taken1 kept1 len1 hd1 body1 B2 bodyF lenF hdF takenF keptF) ->
  tk_exit Q jf B2 bodyF lenF hdF takenF keptF ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (i + 1))
                       (Z_to_bv 64 taken) a0 a1 (Z_to_bv 64 (S_queue_len B i)) a3 a4 a5 a6 a7
                       (Z_to_bv 64 hdp) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
                       (Z_to_bv 64 bp) (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * i)))
                       (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18144)) (Z_to_bv 64 len)
                       (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 1760)) (Z_to_bv 64 kept)
                       (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * (i + 1)))) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x17264) fc None m (seg_rom rsegs)).
Proof.
  intros DBC MCPY Q n jf ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 m B J body i taken kept len hd
    B2 bodyF lenF hdF takenF keptF WM GF BJ HJ BH BL FR ST MI MU WMO HL HH HT HK HI HI512 HQ HN HM HD K.
  tk_lens.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128)
    by (apply unsigned_lit; lia).
  pose proof (u_at_range B (A_S_queue_len i) 1) as RCL. pose proof (u_at_range B (A_S_queue_display i) 1) as RDS.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in RCL, RDS.
  change (u_at B (A_S_queue_len i) 1) with (S_queue_len B i) in RCL.
  change (u_at B (A_S_queue_display i) 1) with (S_queue_display B i) in RDS.
  unfold A_S_queue_bytes in HM. rewrite !Z.add_0_r in HM.
  (* the model is Some, so len + c->len <= 1484 (:365 does not write past tick's body[1484]) *)
  unfold DIGINET_MAX_BODY_LEN, DIGINET_OK in HM.
  destruct (Z.ltb_spec 1484 (len + S_queue_len B i)) as [Cbig|Cbig].
  { replace (1484 <? len + S_queue_len B i) with true in HM by (symmetry; apply Z.ltb_lt; lia).
    cbv iota in HM. discriminate HM. }
  replace (1484 <? len + S_queue_len B i) with false in HM by (symmetry; apply Z.ltb_ge; lia).
  cbv iota in HM.
  assert (LJ : length J = 1484%nat) by (destruct BJ as [[[HLj _] _] _]; exact HLj).
  (* the body buffer: the bytes before len, the c->len bytes the memcpy writes, the rest *)
  replace 1484%nat with (Z.to_nat len + Z.to_nat (S_queue_len B i) +
                         (1484 - Z.to_nat len - Z.to_nat (S_queue_len B i)))%nat in BJ by lia.
  destruct (tk_cb_split3 m bp (Z.to_nat len) (Z.to_nat (S_queue_len B i))
              (1484 - Z.to_nat len - Z.to_nat (S_queue_len B i))%nat J BJ) as (P1 & P2 & P3).
  clear BJ; rewrite HJ in P1.
  assert (LBody : length body = Z.to_nat len) by (destruct P1 as [[[HLb _] _] _]; exact HLb).
  (* 0x17264 .. 0x1726c: memcpy (body + len, c->bytes, c->len) *)
  do 3 step.
  assert (UB : bv_unsigned (Z_to_bv 64 (bp + len)) = bp + len) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * i)))
               = W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * i)) by (apply unsigned_lit; lia).
  assert (UC : bv_unsigned (Z_to_bv 64 (S_queue_len B i)) = S_queue_len B i) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply MCPY with (src := sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i))).
    - rewrite US. apply (wm_src rsegs W_BASE_PLAIN m B (OFF_g_s + 1760 + 32 * i)
                           (Z.to_nat (S_queue_len B i))); [exact WM | lia | lia | lia].
    - rewrite UC. apply length_sub; lia.
    - rewrite UB, UC. replace (bp + len) with (bp + Z.of_nat (Z.to_nat len)) by lia. exact P2.
    - rewrite UB, US, UC. lia.
    - exact MI. }
  intros ms' PO; hnf in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & DSTc & SRCc).
  subst ms'; rewrite UB, UC in MUc, DSTc.
  rewrite (ret_pc_even 0x17270) by (first [lia | reflexivity]).
  (* the stack: the memcpy wrote the body buffer, which may lie in it *)
  assert (STn : stk rsegs m2 lo (bv_unsigned sp + -128))
    by (eapply tk_stk_rebuild; [exact ST | exact MUc | exact WMc | exact DSTc | cbn [cells_size csize]; lia]).
  clear ST SRCc; rename STn into ST.
  transport_after_call rsegs m m2 MUc WMc.
  clear MUc WMc MI.
  pose proof (tk_cb_join m2 bp (Z.to_nat len) (Z.to_nat (S_queue_len B i)) body
                (sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i)))
                LBody ltac:(apply length_sub; lia) P1
                ltac:(replace (bp + Z.of_nat (Z.to_nat len)) with (bp + len) by lia; exact DSTc)) as PJ.
  clear P1 DSTc.
  (* 0x17270 .. 0x1727c: diginet_body_check (body, len + c->len) *)
  do 2 step.
  replace (OFF_g_s + 1760 + 32 * (i + 1) + -8) with (A_S_queue_len i) by (unfold A_S_queue_len; lia).
  change (u_at B (A_S_queue_len i) 1) with (S_queue_len B i).
  step. step.
  assert (LCand : Z.of_nat (length (body ++ sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i))))
                  = len + S_queue_len B i)
    by (rewrite length_app, LBody, (length_sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i)))
          by lia; lia).
  replace (Z_to_bv 64 (len + S_queue_len B i))
    with (Z_to_bv 64 (Z.of_nat (length (body ++ sub B (OFF_g_s + 1760 + 32 * i)
                                          (Z.to_nat (S_queue_len B i)))))) by (rewrite LCand; reflexivity).
  eapply evt_cut.
  { eapply DBC.
    - lia.
    - eapply tk_bytes_of_cb. exact PJ.
    - rewrite Hsp. exact ST.
    - rewrite Hsp. lia.
    - rewrite Hsp, LCand. lia.
    - exact MI2. }
  intros ms' PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WMc & MI3 & ST3).
  subst ms'; rewrite Hsp in MUc, ST3.
  rewrite (ret_pc_even 0x17280) by (first [lia | reflexivity]).
  clear ST.
  transport_after_call rsegs m2 m3 MUc WMc.
  clear MUc WMc MI2.
  (* the body buffer as one cell again *)
  pose proof (tk_cb_join m3 bp (Z.to_nat len + Z.to_nat (S_queue_len B i))
                (1484 - Z.to_nat len - Z.to_nat (S_queue_len B i))%nat
                (body ++ sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i)))
                (skipn (Z.to_nat (S_queue_len B i)) (skipn (Z.to_nat len) J))
                ltac:(rewrite length_app, LBody,
                        (length_sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i))) by lia; lia)
                ltac:(rewrite !length_skipn, LJ; lia) PJ
                ltac:(replace (bp + Z.of_nat (Z.to_nat len + Z.to_nat (S_queue_len B i)))
                        with (bp + Z.of_nat (Z.to_nat len) + Z.of_nat (Z.to_nat (S_queue_len B i)))
                        by lia; exact P3)) as RWJ.
  clear PJ P3.
  rewrite <- app_assoc in RWJ.
  replace (Z.to_nat len + Z.to_nat (S_queue_len B i) +
           (1484 - Z.to_nat len - Z.to_nat (S_queue_len B i)))%nat with 1484%nat in RWJ by lia.
  (* 0x17280: the code of diginet_body_check *)

  rewrite body_check_spec in HM |- *.
  lazymatch goal with |- context [system_at ?bb] => destruct (system_at bb) eqn:SA end.
  all: cbv iota in HM |- *.
  all: step.
  - (* a body the frame builder refuses: the command is kept (:372-376) *)
    replace (-10 =? 0) with false in HM by reflexivity. cbv iota in HM.
    rewrite (tk_eqb0 (-10)) by lia. cbn [Z.eqb negb]. cbv iota.
    eapply tk_notfit;
    [ exact MCPY | exact WM | exact GF | exact RWJ | (apply tk_firstn_app1; exact LBody) | exact BH
    | exact BL | exact FR | exact ST3 | exact MI3 | exact MU | exact WMO | lia | lia | lia | lia | lia
    | lia | lia | exact HN | reflexivity
    | (unfold A_S_queue_bytes; rewrite ?Z.add_0_r; exact HM)
    | apply (HD (if kept =? i then B else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32))
               body taken (kept + 1) len hd)
    | exact K ].
  - (* the command is taken (:368-371) *)
    replace (0 =? 0) with true in HM by reflexivity. cbv iota in HM.
    rewrite (tk_eqb0 0) by lia. cbn [Z.eqb negb]. cbv iota.
    (* 0x17284 .. 0x1729c: len += c->len; taken++; *has_display |= c->display *)
    step.
    replace (OFF_g_s + 1760 + 32 * (i + 1) + -8) with (A_S_queue_len i) by (unfold A_S_queue_len; lia).
    change (u_at B (A_S_queue_len i) 1) with (S_queue_len B i).
    step.
    replace (OFF_g_s + 1760 + 32 * (i + 1) + -7) with (A_S_queue_display i)
      by (unfold A_S_queue_display; lia).
    change (u_at B (A_S_queue_display i) 1) with (S_queue_display B i).
    step.
    rewrite (tk_sx32_small hd) by lia.
    step. step.
    rewrite (unsigned_lit taken) by lia. rewrite (tk_swrap32_small (taken + 1)) by lia.
    step.
    rewrite (unsigned_lit hd) by lia. rewrite (unsigned_lit (S_queue_display B i)) by lia.
    step. step.
    eapply tk_bottom;
    [ reflexivity | exact WM | exact GF | exact RWJ
    | (replace (Z.to_nat (len + S_queue_len B i))
         with (Z.to_nat len + Z.to_nat (S_queue_len B i))%nat by lia;
       apply tk_firstn_app2; [exact LBody | apply length_sub; lia]) | exact BH | exact BL | exact FR
    | exact ST3 | exact MI3 | exact MU | exact WMO | lia | (apply tk_lor_256; lia) | lia | lia | lia
    | lia | lia | exact HN | (unfold A_S_queue_bytes; rewrite ?Z.add_0_r; exact HM)
    | apply (HD B (body ++ sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i)))
               (taken + 1) kept (len + S_queue_len B i) (Z.lor hd (S_queue_display B i)))
    | exact K ].
Qed.


(* 0x17240 .. 0x172a0: a turn of the loop of :358-382 and the turns after it. *)
Lemma tk_loop : diginet_body_check_contract -> memcpy_contract ->
  forall (Q : machine_state -> Prop) (n : nat) (jf B body B2 bodyF : list byte)
         (i taken kept len hd lenF hdF takenF keptF : Z),
  tk_exit Q jf B2 bodyF lenF hdF takenF keptF ->
  tk_head Q n jf B i taken kept len hd body B2 bodyF lenF hdF takenF keptF.
Proof.
  intros DBC MCPY Q n. induction n as [|n IH];
    intros jf B body B2 bodyF i taken kept len hd lenF hdF takenF keptF K;
    unfold tk_head; intros ra t0 t1 t2 s0 a1 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 m J
      WM GF BJ HJ BH BL FR ST MI MU WMO HL HH HT HK HI HQ HN HM.
  { exfalso. lia. }
  rewrite tk_loop_S in HM.
  destruct (S_queue_N <=? i) eqn:EI; [discriminate HM|].
  apply Z.leb_gt in EI. unfold S_queue_N in EI.
  cbv zeta in HM.
  tk_lens.
  assert (HN' : S_queued B - i = Z.of_nat (S n)) by lia.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128)
    by (apply unsigned_lit; lia).
  pose proof (u_at_range B A_S_cfg_max_cmds 4) as RMC. pose proof (u_at_range B A_S_cfg_max_body 4) as RMB.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RMC, RMB.
  change (u_at B A_S_cfg_max_cmds 4) with (S_cfg_max_cmds B) in RMC.
  change (u_at B A_S_cfg_max_body 4) with (S_cfg_max_body B) in RMB.
  pose proof (u_at_range B (A_S_queue_len i) 1) as RCL. pose proof (u_at_range B (A_S_queue_display i) 1) as RDS.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in RCL, RDS.
  change (u_at B (A_S_queue_len i) 1) with (S_queue_len B i) in RCL.
  change (u_at B (A_S_queue_display i) 1) with (S_queue_display B i) in RDS.
  (* 0x17240 .. 0x17248: s0 = i + 1; s6 = &s->queue[i]; bgeu s1,a0 *)
  do 3 step.
  replace (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * (i + 1)) + -32)
    with (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * i)) by lia.
  rewrite (tk_ltu_s32 taken B A_S_cfg_max_cmds) by lia.
  change (u_at B A_S_cfg_max_cmds 4) with (S_cfg_max_cmds B).
  destruct (Z.ltb_spec taken (S_cfg_max_cmds B)) as [Cmc|Cmc]; cbn [negb]; cbv iota;
    [ replace (taken <? S_cfg_max_cmds B) with true in HM by (symmetry; apply Z.ltb_lt; lia)
    | replace (taken <? S_cfg_max_cmds B) with false in HM by (symmetry; apply Z.ltb_ge; lia) ];
    cbn [andb] in HM; cbv iota in HM.
  2: { (* taken = max_cmds: the command is kept *)
eapply tk_notfit;
       [ exact MCPY | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
       | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HN | reflexivity
       | exact HM
       | apply (IH jf (if kept =? i then B
                       else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32))
                  body B2 bodyF (i + 1) taken (kept + 1) len hd lenF hdF takenF keptF K)
       | exact K ]. }
  (* 0x1724c .. 0x17258: c->len; max_body; len + c->len; bltu a0,a1 *)
  do 2 step.
  replace (OFF_g_s + 1760 + 32 * (i + 1) + -8) with (A_S_queue_len i) by (unfold A_S_queue_len; lia).
  change (u_at B (A_S_queue_len i) 1) with (S_queue_len B i).
  step. change (u_at B 1704 4) with (S_cfg_max_body B). step.
  rewrite (tk_ltu_lits (S_cfg_max_body B) (len + S_queue_len B i)) by lia.
  destruct (Z.ltb_spec (S_cfg_max_body B) (len + S_queue_len B i)) as [Cmb|Cmb]; cbv iota;
    [ replace (len + S_queue_len B i <=? S_cfg_max_body B) with false in HM by (symmetry; apply Z.leb_gt; lia)
    | replace (len + S_queue_len B i <=? S_cfg_max_body B) with true in HM by (symmetry; apply Z.leb_le; lia) ];
    cbn [andb] in HM; cbv iota in HM.
  { (* len + c->len > max_body: the command is kept *)
eapply tk_notfit;
       [ exact MCPY | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
       | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HN | reflexivity
       | exact HM
       | apply (IH jf (if kept =? i then B
                       else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32))
                  body B2 bodyF (i + 1) taken (kept + 1) len hd lenF hdF takenF keptF K)
       | exact K ]. }
  (* 0x1725c: allow_display *)
  do 2 step.
  rewrite (tk_eqb0 allow) by lia.
  destruct (Z.eqb_spec allow 0) as [Ca|Ca]; cbv iota;
    [ replace (negb (allow =? 0)) with false in HM by (symmetry; apply negb_false_iff, Z.eqb_eq; exact Ca)
    | replace (negb (allow =? 0)) with true in HM by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Ca) ];
    cbn [orb andb] in HM.
  - (* allow_display = 0: 0x172a4 the display flag *)
    step.
    replace (OFF_g_s + 1760 + 32 * (i + 1) + -7) with (A_S_queue_display i) by (unfold A_S_queue_display; lia).
    change (u_at B (A_S_queue_display i) 1) with (S_queue_display B i).
    step.
    rewrite (tk_eqb_lits (S_queue_display B i) 0) by lia.
    destruct (Z.eqb_spec (S_queue_display B i) 0) as [Cd|Cd]; cbv iota;
      [ replace (S_queue_display B i =? 0) with true in HM by (symmetry; apply Z.eqb_eq; exact Cd)
      | replace (S_queue_display B i =? 0) with false in HM by (symmetry; apply Z.eqb_neq; exact Cd) ];
      cbn [andb] in HM; cbv iota in HM.
    2: { (* a display write the pacing refuses: the command is kept *)
eapply tk_notfit;
       [ exact MCPY | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
       | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HN | reflexivity
       | exact HM
       | apply (IH jf (if kept =? i then B
                       else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32))
                  body B2 bodyF (i + 1) taken (kept + 1) len hd lenF hdF takenF keptF K)
       | exact K ]. }
    all: eapply tk_fit;
         [ exact DBC | exact MCPY | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL
         | exact FR | exact ST | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia
         | exact HN | exact HM
         | (intros B1 body1 taken1 kept1 len1 hd1;
            apply (IH jf B1 body1 B2 bodyF (i + 1) taken1 kept1 len1 hd1 lenF hdF takenF keptF K))
         | exact K ].
  - eapply tk_fit;
         [ exact DBC | exact MCPY | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL
         | exact FR | exact ST | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia
         | exact HN | exact HM
         | (intros B1 body1 taken1 kept1 len1 hd1;
            apply (IH jf B1 body1 B2 bodyF (i + 1) taken1 kept1 len1 hd1 lenF hdF takenF keptF K))
         | exact K ].
Qed.

(* 0x171bc .. 0x17240 and 0x172fc, then 0x17358 .. 0x173a0: the prologue, the first turn and the epilogue. *)
Lemma take_body : diginet_body_check_contract -> memcpy_contract ->
  forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (B B' body J JH : list byte) (len hd taken : Z),
  rw_cells rsegs m0 bp [CB 1484 J] -> rw_cells rsegs m0 blp [CB 8 JL] -> rw_cells rsegs m0 hdp [CB 4 JH] ->
  wmem rsegs m0 B -> g_fail_next B <= 1 ->
  take_m B allow = Some (B', (body, len, hd, taken)) ->
  bv_unsigned sp mod 16 = 0 -> stk rsegs m0 lo (bv_unsigned sp) -> mem_inv rsegs m0 ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (X : list byte)
                       (m' : word -> option byte),
       ms' = MS (mkR rra sp gp tp t0' t1' t2' rs0 rs1 (Z_to_bv 64 (bv_swrap 32 taken)) a1' a2' a3' a4' a5' a6'
                     a7' rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 t3' t4' t5' t6')
                F (ret_pc rra) fc None m' (seg_rom rsegs) /\
       munch TW m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
       wmem rsegs m' B' /\ g_fail_next B' <= 1 /\
       rw_cells rsegs m' bp [CB 1484 X] /\ firstn (Z.to_nat len) X = firstn (Z.to_nat len) body /\
       rw_cells rsegs m' blp [CB 8 (put 8 len)] /\ rw_cells rsegs m' hdp [CB 4 (put 4 hd)])
    (MS (mkR rra sp gp tp t0 t1 t2 rs0 rs1 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 bp)
             (Z_to_bv 64 blp) (Z_to_bv 64 allow) (Z_to_bv 64 hdp) a5 a6 a7
             rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171bc) fc None m0 (seg_rom rsegs)).
Proof.
  intros DBC MCPY t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 B B' body J JH len hd taken BJ BL BH WM GF HM SP16 ST MI.
  pose proof ST as (Hlo2 & Hhi2 & _).
  wk_facts. tk_lens.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128)
    by (apply unsigned_lit; lia).
  pose proof (munch_refl TW m0) as MU.
  pose proof (wmono_refl rsegs m0) as WMO.
  (* the model: the loop of :358-382, then s->queued = kept *)
  unfold take_m in HM.
  destruct (take_loop_m B allow 0 0 0 0 0 [] (Z.to_nat (S_queued B)))
    as [[B2 [[[[bodyF lenF] hdF] takenF] keptF]]|] eqn:EL; [|discriminate HM].
  injection HM as <- <- <- <- <-.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* the prologue 0x171bc .. 0x171fc *)
  carve_frame 128%nat ST.
  do 17 step.
  (* 0x17200: *has_display = 0 *)
  step.
  (* 0x17204 .. 0x17210: a0 = s->queued *)
  do 4 step.
  change (s32_at B 19792) with (s32_at B A_S_queued).
  (* the epilogue 0x17358 .. 0x173a0, for either exit *)
  assert (K : forall jf', tk_exit QQ jf' B2 bodyF lenF hdF takenF keptF).
  { intros jf'. unfold tk_exit.
    intros ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s9' s11' t3' t4' t5' t6'
      m' JF WMF GFF BJF HJF BHF BLF FRF STF MIF MUF WMOF HLF HTF HKF.
    tk_lens.
    (* 0x17358: s->queued = kept; 0x1735c .. 0x17360: *body_len = len *)
    do 3 step.
    (* 0x17364 .. 0x1739c: the return value and the saved registers *)
    do 14 step.
    release_frame FRF STF (bv_unsigned sp).
    try (rewrite Hsp in STF).
    try (replace (bv_unsigned sp + -128 + 128) with (bv_unsigned sp) in STF by lia).
    do 2 step.
    apply evt_done. unfold QQ.
    rewrite (tk_swrap32_small takenF) by lia.
    try (rewrite Hsp). try (replace (bv_unsigned sp + -128 + 128) with (bv_unsigned sp) by lia).
    try (rewrite Z_to_bv_lit_self).
    do 16 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact STF|].
    split; [change (set_S_queued B2 keptF) with (upd B2 19792 (put 4 keptF)); assumption|].
    split; [change (set_S_queued B2 keptF) with (upd B2 19792 (put 4 keptF));
            rewrite tk_fail_queued by assumption; exact GFF|].
    split; [eassumption|].
    split; [rewrite HJF; symmetry; apply firstn_all2;
            rewrite <- HJF, length_firstn; lia|].
    split.
    - lazymatch goal with H : rw_cells rsegs ?mm blp _ |- _ =>
        eapply (tk_rebytes mm blp); [exact H | | ] end.
      + cbn [cells_wf cell_wf]. rewrite length_put. split; [reflexivity | exact I].
      + cbn [cells_bytes cbytes]. rewrite le8_put. reflexivity.
    - lazymatch goal with H : rw_cells rsegs ?mm hdp _ |- _ =>
        eapply (tk_rebytes mm hdp); [exact H | | ] end.
      + cbn [cells_wf cell_wf]. rewrite length_put. split; [reflexivity | exact I].
      + cbn [cells_bytes cbytes]. rewrite le4_put. reflexivity. }
  (* 0x17214: s->queued = 0? *)
  step.
  rewrite (tk_eqb0 (s32_at B A_S_queued)) by (pose proof (s32_range B A_S_queued); lia).
  rewrite tk_s32_eq0. change (u_at B A_S_queued 4) with (S_queued B).
  pose proof (u_at_range B A_S_queued 4) as RQ.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RQ.
  change (u_at B A_S_queued 4) with (S_queued B) in RQ.
  destruct (Z.eqb_spec (S_queued B) 0) as [Q0|Q0]; cbv iota.
  - (* no command queued: 0x172fc *)
    replace (Z.to_nat (S_queued B)) with 0%nat in EL by lia.
    cbn [take_loop_m] in EL. injection EL as <- <- <- <- <- <-.
    do 4 step.
    eapply K;
    [ eassumption | exact GF | eassumption | reflexivity | eassumption | eassumption | eassumption
    | eassumption | eassumption | eassumption | eassumption | lia | lia | lia ].
  - (* 0x17218 .. 0x1723c, then the loop *)
    do 10 step.
    change (s32_at B 1700) with (s32_at B A_S_cfg_max_cmds).
    replace (Z_to_bv 64 1) with (Z_to_bv 64 (0 + 1)) by (f_equal; lia).
    replace (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 1792))
      with (Z_to_bv 64 (W_BASE_PLAIN + (OFF_g_s + 1760 + 32 * (0 + 1)))) by (f_equal; lia).
    epose proof (tk_loop DBC MCPY QQ (Z.to_nat (S_queued B)) _ B [] B2 bodyF 0 0 0 0 0
                  lenF hdF takenF keptF (K _)) as HL0.
    unfold tk_head in HL0.
    eapply HL0;
    [ eassumption | exact GF | eassumption | reflexivity | eassumption | eassumption | eassumption
    | eassumption | eassumption | eassumption | eassumption | lia | lia | lia | lia | lia | lia | lia
    | exact EL ].
Qed.

End Walk.

Theorem take_holds : diginet_body_check_contract -> memcpy_contract -> take_contract.
Proof.
  intros DBC MCPY. unfold take_contract, take_ENTRY, take_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    bp blp hdp allow len hd taken J JL JH body B B'
    A0 A1 A2 A3 A4 HAL BJ ABP BL ABL BL8 BH ABH BH4 S1 S2 S3 WM GF HM SP16 ST LO WO MI.
  subst a0 a1 a2 a3 a4.
  destruct ABP as (BP0 & BP1 & BP2 & BP3). destruct ABL as (BL0 & BL1 & BL2 & BL3).
  destruct ABH as (BH0 & BH1 & BH2 & BH3).
  unfold off_world, off_window, blk_sep, w_off_stack in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (Z.of_N 64) with 64 in Rsp.
  pose proof ST as (Hlo & _ & _).
  eapply (take_body sp gp tp F fc m lo bp blp hdp allow JL s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra);
    try eassumption; try reflexivity; try lia.
Qed.

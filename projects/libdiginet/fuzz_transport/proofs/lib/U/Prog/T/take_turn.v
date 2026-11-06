(* take (transport/src/diginet_session.c:353-386) in the ubsan image, part 2 of its walk (U/Prog/T/take.v holds
   take_holds): the command that does not fit (:372-376, 0x17b00 .. 0x17b2c). Its UBSan checks (kept > 512 at
   0x17b10, &s->queue[kept] wrapping at 0x17b18) are decided false from kept < i < 512, which the model's Some
   gives. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TSess0 TTake.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c diginet_body_check_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TContract TSessC take_tail.
Import ListNotations.
Open Scope Z_scope.

Ltac solve_load ::= first [ tk_solve_load_world | wk_solve_load_world | solve_load_base | solve_load_image ].
Ltac solve_store ::= first [ tk_solve_store_world | wk_solve_store_world | wk_solve_store_kit ].
Ltac mem_after_store_opt ::=
  try fix_lit_store; first [ tk_world_after_store | wk_world_after_store | wk_mem_after_store_opt_kit ].

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
Local Abbreviation TW := [(bv_unsigned sp - 304, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
                      (bp, bp + 1484); (blp, blp + 8); (hdp, hdp + 4)].
(* the program points of part 1, at this section's values *)
Local Abbreviation EXIT := (tku_exit sp gp tp F fc m0 lo bp blp hdp allow JL
  rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra).
Local Abbreviation HEAD := (tku_head sp gp tp F fc m0 lo bp blp hdp allow JL
  rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra).
Local Abbreviation BOTTOM := (tku_bottom sp gp tp F fc m0 lo bp blp hdp allow JL
  rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra
  HAL BP0 BP1 BP2 BP3 BL0 BL1 BL2 BL3 BH0 BH1 BH2 BH3 S1 S2 S3 LO WO Rsp Hlo SPm HA4 HA8 Ew Ew0 Ew1).

(* 0x17b00 .. 0x17b2c: the command does not fit (:372-376), s->queue[kept++] = *c unless kept = i. *)
Lemma tku_notfit : memcpy_contract -> forall (Q : machine_state -> Prop) (n : nat) (j0 j32 : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B J body : list byte) (i taken kept len hd : Z)
    (B1 B2 bodyF : list byte) (lenF hdF takenF keptF : Z),
  wmem rsegs m B -> g_fail_next B <= 1 ->
  rw_cells rsegs m bp [CB 1484 J] -> firstn (Z.to_nat len) J = body ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd)] -> rw_cells rsegs m blp [CB 8 JL] ->
  rw_cells rsegs m (bv_unsigned sp + -160) (FRL j0 j32) -> stk rsegs m lo (bv_unsigned sp + -160) ->
  mem_inv rsegs m -> munch TW m0 m -> wmono rsegs m0 m ->
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
  HEAD Q n B1 (i + 1) taken (kept + 1) len hd body B2 bodyF lenF hdF takenF keptF ->
  EXIT Q B2 bodyF lenF hdF takenF keptF ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 (- i))
                       (Z_to_bv 64 taken) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 i) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (W_BASE_UBSAN + (OFF_g_s + 32 * i)))
                       (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s))
                       (Z_to_bv 64 (W_BASE_UBSAN + (OFF_g_s + 1760 + 32 * i)))
                       (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 18144)) (Z_to_bv 64 len) (Z_to_bv 64 kept)
                       (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 1760)) (Z_to_bv 64 18446744073709338543)
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x17b00) fc None m (seg_rom rsegs)).
Proof using All.
  intros MCPY Q n j0 j32 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m B J body i taken kept len hd
    B1 B2 bodyF lenF hdF takenF keptF WM GF BJ HJ BH BL FR ST MI MU WMO HL HH HT HK HI HI512 HQ HN EQ1 HM HD K.
  tk_lens.
  unfold A_S_queue_bytes in EQ1. rewrite !Z.add_0_r in EQ1.
  (* 0x17b00 slli a0,s9,32; 0x17b04 srli a0,a0,32; 0x17b08 beq s2,a0 *)
  step. step. rewrite (tk_zext32 kept) by lia.
  step.
  rewrite (tk_eqb_lits i kept) by lia.
  destruct (Z.eqb_spec i kept) as [Eki|Eki]; cbv iota.
  - (* kept = i: 0x17b2c kept++ *)
    replace (kept =? i) with true in EQ1 by (symmetry; apply Z.eqb_eq; lia). cbv iota in EQ1. subst B1.
    step. rewrite (unsigned_lit kept) by lia. rewrite (tk_swrap32_small (kept + 1)) by lia.
    eapply (BOTTOM Q n j0 j32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m B J body i taken (kept + 1) len hd
              B2 bodyF lenF hdF takenF keptF);
    [ reflexivity | reflexivity | reflexivity | exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL
    | exact FR | exact ST | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HN
    | exact HM | exact HD | exact K ].
  - (* kept < i: 0x17b0c li a1,512; 0x17b10 bltu a1,s9 (kept > 512) *)
    replace (kept =? i) with false in EQ1 by (symmetry; apply Z.eqb_neq; lia). cbv iota in EQ1.
    step. step. tk_cond false.
    (* 0x17b14 slli a0,a0,5; 0x17b18 bltu s11,a0 (&s->queue[kept] wraps) *)
    step. rewrite (unsigned_lit kept) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    step. tk_cond false.
    (* 0x17b1c add a0,s10,a0; li a2,32; mv a1,s6; 0x17b28 jal memcpy (&s->queue[kept], &s->queue[i], 32) *)
    do 4 step.
    assert (UD : bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 1760 + kept * 2 ^ 5))
                 = W_BASE_UBSAN + OFF_g_s + 1760 + kept * 2 ^ 5) by (apply unsigned_lit; lia).
    assert (US : bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + (OFF_g_s + 1760 + 32 * i)))
                 = W_BASE_UBSAN + (OFF_g_s + 1760 + 32 * i)) by (apply unsigned_lit; lia).
    assert (U32 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
    eapply evt_cut.
    { eapply MCPY with (src := sub B (OFF_g_s + 1760 + 32 * i) 32).
      - rewrite US.
        apply (wm_src rsegs W_BASE_UBSAN m B (OFF_g_s + 1760 + 32 * i) 32); [exact WM | lia | lia | lia].
      - rewrite U32. apply length_sub; lia.
      - rewrite UD, U32.
        apply (wm_piece rsegs W_BASE_UBSAN m B (OFF_g_s + 1760 + 32 * kept) 32);
          [exact WM | lia | lia | lia | lia].
      - rewrite UD, US, U32. lia.
      - exact MI. }
    intros ms' PO; hnf in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & DSTc &
                    SRCc).
    subst ms'. rewrite UD, U32 in MUc, DSTc.
    rewrite (ret_pc_even 0x17b2c) by (first [lia | reflexivity]).
    assert (WM2 : wmem rsegs m2 (upd B (OFF_g_s + 1760 + 32 * kept) (sub B (OFF_g_s + 1760 + 32 * i) 32)))
      by (apply (wm_fill rsegs W_BASE_UBSAN m m2 B (W_BASE_UBSAN + OFF_g_s + 1760 + kept * 2 ^ 5)
                   (OFF_g_s + 1760 + 32 * kept) 32);
          [exact WM | exact MUc | exact WMc | exact DSTc | lia | lia | lia | lia]).
    pose proof (tk_stk_rebuild m m2 lo (bv_unsigned sp + -160) _ 32 _ ST MUc WMc DSTc
                  ltac:(cbn [cells_size csize]; lia)) as ST2.
    clear WM ST DSTc SRCc.
    transport_after_call rsegs m m2 MUc WMc.
    clear MUc WMc MI.
    (* 0x17b2c addiw s9,s9,1 *)
    step. rewrite (unsigned_lit kept) by lia. rewrite (tk_swrap32_small (kept + 1)) by lia.
    subst B1.
    eapply (BOTTOM Q n j0 j32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 _ J body i taken (kept + 1) len hd
              B2 bodyF lenF hdF takenF keptF);
    [ reflexivity | reflexivity | reflexivity | exact WM2 | (tk_upd_facts; exact GF) | exact BJ | exact HJ
    | exact BH | exact BL | exact FR | exact ST2 | exact MI2 | exact MU | exact WMO | lia | lia | lia | lia | lia
    | lia | (tk_upd_facts; lia) | (tk_upd_facts; exact HN) | exact HM | exact HD | exact K ].
Qed.

End Walk.

(* take (transport/src/diginet_session.c:353-386) in the ubsan image, part 3 of its walk (U/Prog/T/take.v holds
   take_holds): the command that fits (:365-371, 0x17a90 .. 0x17af4). The UBSan check of this path (body + len
   wrapping at 0x17a94) is decided false from len + c->len <= 1484, which the model's Some gives. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TSess0 TTake.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c diginet_body_check_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import take_tail take_turn.
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
(* the program points and the paths of parts 1 and 2, at this section's values *)
Local Abbreviation EXIT := (tku_exit sp gp tp F fc m0 lo bp blp hdp allow JL
  rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra).
Local Abbreviation HEAD := (tku_head sp gp tp F fc m0 lo bp blp hdp allow JL
  rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra).
Local Abbreviation BOTTOM := (tku_bottom sp gp tp F fc m0 lo bp blp hdp allow JL
  rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra
  HAL BP0 BP1 BP2 BP3 BL0 BL1 BL2 BL3 BH0 BH1 BH2 BH3 S1 S2 S3 LO WO Rsp Hlo SPm HA4 HA8 Ew Ew0 Ew1).
Local Abbreviation NOTFIT := (tku_notfit sp gp tp F fc m0 lo bp blp hdp allow JL
  rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra
  HAL BP0 BP1 BP2 BP3 BL0 BL1 BL2 BL3 BH0 BH1 BH2 BH3 S1 S2 S3 LO WO Rsp Hlo SPm HA4 HA8 Ew Ew0 Ew1).

(* 0x17a90 .. 0x17af4: the command fits the counters and the pacing (:360-361), so the memcpy of :365 and
   diginet_body_check of :366 run (taken parked in the frame slot 32, s7 / s10 shuffled through s1); then either
   the update of :368-371 or the keep of :372-376. diginet_body_check gets the stack from sp - 304, which lies
   above the world (w_off_stack), so its 0 < lo holds. *)
Lemma tku_fit : diginet_body_check_contract -> memcpy_contract ->
  forall (Q : machine_state -> Prop) (n : nat) (j0 j32 : list byte)
    (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m : word -> option byte) (B J body : list byte) (i taken kept len hd : Z)
    (B2 bodyF : list byte) (lenF hdF takenF keptF : Z),
  wmem rsegs m B -> g_fail_next B <= 1 ->
  rw_cells rsegs m bp [CB 1484 J] -> firstn (Z.to_nat len) J = body ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd)] -> rw_cells rsegs m blp [CB 8 JL] ->
  rw_cells rsegs m (bv_unsigned sp + -160) (FRL j0 j32) -> stk rsegs m lo (bv_unsigned sp + -160) ->
  mem_inv rsegs m -> munch TW m0 m -> wmono rsegs m0 m ->
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
     HEAD Q n B1 (i + 1) taken1 kept1 len1 hd1 body1 B2 bodyF lenF hdF takenF keptF) ->
  EXIT Q B2 bodyF lenF hdF takenF keptF ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 (- i))
                       (Z_to_bv 64 taken) a0 a1 (Z_to_bv 64 (S_queue_len B i)) a3 a4 a5 a6 a7
                       (Z_to_bv 64 i) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (W_BASE_UBSAN + (OFF_g_s + 32 * i)))
                       (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s))
                       (Z_to_bv 64 (W_BASE_UBSAN + (OFF_g_s + 1760 + 32 * i)))
                       (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 18144)) (Z_to_bv 64 len) (Z_to_bv 64 kept)
                       (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 1760)) (Z_to_bv 64 18446744073709338543)
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x17a90) fc None m (seg_rom rsegs)).
Proof using All.
  intros DBC MCPY Q n j0 j32 ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 m B J body i taken kept len hd
    B2 bodyF lenF hdF takenF keptF WM GF BJ HJ BH BL FR ST MI MU WMO HL HH HT HK HI HI512 HQ HN HM HD K.
  tk_lens.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160)
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
  (* 0x17a90 ld a0,16(sp); 0x17a94 bltu a0,s8: body + len does not wrap *)
  step. step. tk_cond false.
  (* 0x17a98 sd s1,32(sp) *)
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m end.
  (* the body buffer: the bytes before len, the c->len bytes the memcpy writes, the rest *)
  replace 1484%nat with (Z.to_nat len + Z.to_nat (S_queue_len B i) +
                         (1484 - Z.to_nat len - Z.to_nat (S_queue_len B i)))%nat in BJ by lia.
  destruct (tk_cb_split3 m bp (Z.to_nat len) (Z.to_nat (S_queue_len B i))
              (1484 - Z.to_nat len - Z.to_nat (S_queue_len B i))%nat J BJ) as (P1 & P2 & P3).
  clear BJ; rewrite HJ in P1.
  assert (LBody : length body = Z.to_nat len) by (destruct P1 as [[[HLb _] _] _]; exact HLb).
  (* 0x17a9c .. 0x17ab0: mv s1,s7; mv s7,s10; ld s10,48(sp); add a0,s10,s8; mv a1,s6;
     jal memcpy (body + len, c->bytes, c->len) *)
  do 6 step.
  assert (UB : bv_unsigned (Z_to_bv 64 (bp + len)) = bp + len) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + (OFF_g_s + 1760 + 32 * i)))
               = W_BASE_UBSAN + (OFF_g_s + 1760 + 32 * i)) by (apply unsigned_lit; lia).
  assert (UC : bv_unsigned (Z_to_bv 64 (S_queue_len B i)) = S_queue_len B i) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply MCPY with (src := sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i))).
    - rewrite US. apply (wm_src rsegs W_BASE_UBSAN m B (OFF_g_s + 1760 + 32 * i)
                           (Z.to_nat (S_queue_len B i))); [exact WM | lia | lia | lia].
    - rewrite UC. apply length_sub; lia.
    - rewrite UB, UC. replace (bp + len) with (bp + Z.of_nat (Z.to_nat len)) by lia. exact P2.
    - rewrite UB, US, UC. lia.
    - exact MI. }
  intros ms' PO; hnf in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & DSTc & SRCc).
  subst ms'; rewrite UB, UC in MUc, DSTc.
  rewrite (ret_pc_even 0x17ab4) by (first [lia | reflexivity]).
  (* the stack: the memcpy wrote the body buffer, which may lie in it *)
  assert (STn : stk rsegs m2 lo (bv_unsigned sp + -160))
    by (eapply tk_stk_rebuild; [exact ST | exact MUc | exact WMc | exact DSTc | cbn [cells_size csize]; lia]).
  clear ST SRCc; rename STn into ST.
  transport_after_call rsegs m m2 MUc WMc.
  clear MUc WMc MI.
  pose proof (tk_cb_join m2 bp (Z.to_nat len) (Z.to_nat (S_queue_len B i)) body
                (sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i)))
                LBody ltac:(apply length_sub; lia) P1
                ltac:(replace (bp + Z.of_nat (Z.to_nat len)) with (bp + len) by lia; exact DSTc)) as PJ.
  clear P1 DSTc.
  (* 0x17ab4 lbu a1,1784(s4); add a1,s8,a1; mv a0,s10; mv s10,s7; mv s7,s1; ld s1,32(sp);
     0x17acc jal diginet_body_check (body, len + c->len) *)
  step.
  replace (OFF_g_s + 32 * i + 1784) with (A_S_queue_len i) by (unfold A_S_queue_len; lia).
  change (u_at B (A_S_queue_len i) 1) with (S_queue_len B i).
  do 6 step.
  assert (LCand : Z.of_nat (length (body ++ sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i))))
                  = len + S_queue_len B i)
    by (rewrite length_app, LBody, (length_sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i)))
          by lia; lia).
  replace (Z_to_bv 64 (len + S_queue_len B i))
    with (Z_to_bv 64 (Z.of_nat (length (body ++ sub B (OFF_g_s + 1760 + 32 * i)
                                          (Z.to_nat (S_queue_len B i)))))) by (rewrite LCand; reflexivity).
  (* the callee's stack is [sp - 304, sp - 160); below it the stack is kept *)
  destruct (stk_split rsegs m2 lo (bv_unsigned sp + -304) (bv_unsigned sp + -160) ST ltac:(lia)) as [STlo STh].
  clear ST.
  eapply evt_cut.
  { eapply DBC with (lo := bv_unsigned sp + -304).
    - lia.
    - eapply tk_bytes_of_cb. exact PJ.
    - rewrite Hsp. exact SPm.
    - rewrite Hsp. exact STh.
    - lia.
    - rewrite Hsp. lia.
    - rewrite Hsp, LCand. lia.
    - exact MI2. }
  intros ms' PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & Eq & MUc & WMc & MI3 & ST3).
  subst ms'; rewrite Hsp in MUc, ST3.
  rewrite (ret_pc_even 0x17ad0) by (first [lia | reflexivity]).
  lazymatch type of MUc with munch ?W _ _ =>
    apply (stk_transport_disjoint rsegs W m2 m3 lo (bv_unsigned sp + -304)) in STlo;
      [ | exact MUc | exact WMc | cbn [disjoint_from]; split; [lia | exact I] ] end.
  transport_after_call rsegs m2 m3 MUc WMc.
  clear MUc WMc MI2.
  pose proof (stk_merge rsegs m3 lo (bv_unsigned sp + -304) (bv_unsigned sp + -160) STlo ST3 ltac:(lia)) as ST4.
  clear STlo ST3.
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
  (* 0x17ad0 bnez a0: the code of diginet_body_check *)
  rewrite body_check_spec in HM |- *.
  lazymatch goal with |- context [system_at ?bb] => destruct (system_at bb) eqn:SA end.
  all: cbv iota in HM |- *.
  all: step.
  - (* a body the frame builder refuses: the command is kept (:372-376) *)
    replace (-10 =? 0) with false in HM by reflexivity. cbv iota in HM.
    rewrite (tk_eqb0 (-10)) by lia. cbn [Z.eqb negb]. cbv iota.
    apply tku_slot32 in FR.
    eapply (NOTFIT MCPY Q n j0 (le8 (Z_to_bv 64 taken)));
    [ exact WM | exact GF | exact RWJ | (apply tk_firstn_app1; exact LBody) | exact BH
    | exact BL | exact FR | exact ST4 | exact MI3 | exact MU | exact WMO | lia | lia | lia | lia | lia
    | lia | lia | exact HN | reflexivity
    | (unfold A_S_queue_bytes; rewrite ?Z.add_0_r; exact HM)
    | apply (HD (if kept =? i then B else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32))
               body taken (kept + 1) len hd)
    | exact K ].
  - (* the command is taken (:368-371) *)
    replace (0 =? 0) with true in HM by reflexivity. cbv iota in HM.
    rewrite (tk_eqb0 0) by lia. cbn [Z.eqb negb]. cbv iota.
    (* 0x17ad4 .. 0x17af4: len += c->len; taken++; *has_display |= c->display *)
    step.
    replace (OFF_g_s + 32 * i + 1784) with (A_S_queue_len i) by (unfold A_S_queue_len; lia).
    change (u_at B (A_S_queue_len i) 1) with (S_queue_len B i).
    step.
    replace (OFF_g_s + 32 * i + 1785) with (A_S_queue_display i) by (unfold A_S_queue_display; lia).
    change (u_at B (A_S_queue_display i) 1) with (S_queue_display B i).
    step. step.
    rewrite (tk_sx32_small hd) by lia.
    step. step.
    rewrite (unsigned_lit taken) by lia. rewrite (tk_swrap32_small (taken + 1)) by lia.
    step.
    rewrite (unsigned_lit hd) by lia. rewrite (unsigned_lit (S_queue_display B i)) by lia.
    step. step.
    apply tku_slot32 in FR.
    eapply (BOTTOM Q n j0 (le8 (Z_to_bv 64 taken)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (body ++ sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i))) i (taken + 1) kept
              (len + S_queue_len B i) (Z.lor hd (S_queue_display B i)) B2 bodyF lenF hdF takenF keptF);
    [ reflexivity | reflexivity | reflexivity | exact WM | exact GF | exact RWJ
    | (replace (Z.to_nat (len + S_queue_len B i))
         with (Z.to_nat len + Z.to_nat (S_queue_len B i))%nat by lia;
       apply tk_firstn_app2; [exact LBody | apply length_sub; lia]) | exact BH | exact BL | exact FR
    | exact ST4 | exact MI3 | exact MU | exact WMO | lia | (apply tk_lor_256; lia) | lia | lia | lia
    | lia | lia | exact HN | (unfold A_S_queue_bytes; rewrite ?Z.add_0_r; exact HM)
    | apply (HD B (body ++ sub B (OFF_g_s + 1760 + 32 * i) (Z.to_nat (S_queue_len B i)))
               (taken + 1) kept (len + S_queue_len B i) (Z.lor hd (S_queue_display B i)))
    | exact K ].
Qed.

End Walk.

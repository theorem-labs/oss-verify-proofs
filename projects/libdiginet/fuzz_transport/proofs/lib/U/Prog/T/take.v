(* take (transport/src/diginet_session.c:353-386) in the ubsan image: the loop of :358-382 (0x17a5c .. 0x17a8c and
   0x17af8 .. 0x17afc), the prologue (0x179bc .. 0x17a58), the queued = 0 exit (0x17bf8) and the epilogue
   (0x17c04 .. 0x17c54), and take_holds. The walk's other paths are in take_tail.v, take_turn.v and take_fit.v.
   The UBSan checks here: has_display 4-aligned (0x17a00) and body_len 8-aligned (0x17c10) are premises of the
   contract, s = &g_s 8-aligned (0x17a10) holds of the image, and i = 513 (0x17a60) and &s->queue[i] wrapping
   (0x17a64) are decided false from the model's Some (i < 512). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TSess0 TTake.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c diginet_body_check_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TContract TSessC take_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import take_tail take_turn take_fit.
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

Local Abbreviation TW := [(bv_unsigned sp - 304, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
                      (bp, bp + 1484); (blp, blp + 8); (hdp, hdp + 4)].
(* the program points and the paths of the other parts, at this section's values *)
Local Abbreviation EXIT := (tku_exit sp gp tp F fc m0 lo bp blp hdp allow JL
  rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra).
Local Abbreviation HEAD := (tku_head sp gp tp F fc m0 lo bp blp hdp allow JL
  rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra).
Local Abbreviation NOTFIT := (tku_notfit sp gp tp F fc m0 lo bp blp hdp allow JL
  rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra
  HAL BP0 BP1 BP2 BP3 BL0 BL1 BL2 BL3 BH0 BH1 BH2 BH3 S1 S2 S3 LO WO Rsp Hlo SPm HA4 HA8 Ew Ew0 Ew1).
Local Abbreviation FIT := (tku_fit sp gp tp F fc m0 lo bp blp hdp allow JL
  rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rra
  HAL BP0 BP1 BP2 BP3 BL0 BL1 BL2 BL3 BH0 BH1 BH2 BH3 S1 S2 S3 LO WO Rsp Hlo SPm HA4 HA8 Ew Ew0 Ew1).

(* 0x17a5c .. 0x17a8c and 0x17af8 .. 0x17afc: the tests of a turn of the loop of :358-382, and the turns after it. *)
Lemma tku_loop : diginet_body_check_contract -> memcpy_contract ->
  forall (Q : machine_state -> Prop) (n : nat) (B body B2 bodyF : list byte)
         (i taken kept len hd lenF hdF takenF keptF : Z),
  EXIT Q B2 bodyF lenF hdF takenF keptF ->
  HEAD Q n B i taken kept len hd body B2 bodyF lenF hdF takenF keptF.
Proof using All.
  intros DBC MCPY Q n. induction n as [|n IH];
    intros B body B2 bodyF i taken kept len hd lenF hdF takenF keptF K;
    unfold tku_head; intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 t3 t4 t5 t6 m J j0 j32
      E0 E2 E3 WM GF BJ HJ BH BL FR ST MI MU WMO HL HH HT HK HI HQ HN HM.
  { exfalso. lia. }
  subst s0 s2 s3.
  rewrite tk_loop_S in HM.
  destruct (S_queue_N <=? i) eqn:EI; [discriminate HM|].
  apply Z.leb_gt in EI. unfold S_queue_N in EI.
  cbv zeta in HM.
  tk_lens.
  assert (HN' : S_queued B - i = Z.of_nat (S n)) by lia.
  pose proof (u_at_range B A_S_cfg_max_cmds 4) as RMC. pose proof (u_at_range B A_S_cfg_max_body 4) as RMB.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RMC, RMB.
  change (u_at B A_S_cfg_max_cmds 4) with (S_cfg_max_cmds B) in RMC.
  change (u_at B A_S_cfg_max_body 4) with (S_cfg_max_body B) in RMB.
  pose proof (u_at_range B (A_S_queue_len i) 1) as RCL. pose proof (u_at_range B (A_S_queue_display i) 1) as RDS.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in RCL, RDS.
  change (u_at B (A_S_queue_len i) 1) with (S_queue_len B i) in RCL.
  change (u_at B (A_S_queue_display i) 1) with (S_queue_display B i) in RDS.
  (* 0x17a5c li a0,513; 0x17a60 beq s2,a0 (i = 513); 0x17a64 bltu s11,s3 (&s->queue[i] wraps) *)
  step. step. tk_cond false.
  step. tk_cond false.
  (* 0x17a68 lw a0,52(s5); 0x17a6c add s4,s5,s3; 0x17a70 addi s6,s4,1760; 0x17a74 bgeu s1,a0 *)
  step. change (s32_at B 1700) with (s32_at B A_S_cfg_max_cmds).
  step. replace (W_BASE_UBSAN + OFF_g_s + 32 * i) with (W_BASE_UBSAN + (OFF_g_s + 32 * i)) by lia.
  step.
  replace (W_BASE_UBSAN + (OFF_g_s + 32 * i) + 1760) with (W_BASE_UBSAN + (OFF_g_s + 1760 + 32 * i)) by lia.
  step.
  rewrite (tk_ltu_s32 taken B A_S_cfg_max_cmds) by lia.
  change (u_at B A_S_cfg_max_cmds 4) with (S_cfg_max_cmds B).
  destruct (Z.ltb_spec taken (S_cfg_max_cmds B)) as [Cmc|Cmc]; cbn [negb]; cbv iota;
    [ replace (taken <? S_cfg_max_cmds B) with true in HM by (symmetry; apply Z.ltb_lt; lia)
    | replace (taken <? S_cfg_max_cmds B) with false in HM by (symmetry; apply Z.ltb_ge; lia) ];
    cbn [andb] in HM; cbv iota in HM.
  2: { (* taken = max_cmds: the command is kept *)
       eapply (NOTFIT MCPY Q n j0 j32);
       [ exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
       | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HN | reflexivity
       | exact HM
       | apply (IH (if kept =? i then B else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32))
                  body B2 bodyF (i + 1) taken (kept + 1) len hd lenF hdF takenF keptF K)
       | exact K ]. }
  (* 0x17a78 lbu a2,1784(s4); 0x17a7c lwu a0,56(s5); 0x17a80 add a1,s8,a2; 0x17a84 bltu a0,a1 *)
  step.
  replace (OFF_g_s + 32 * i + 1784) with (A_S_queue_len i) by (unfold A_S_queue_len; lia).
  change (u_at B (A_S_queue_len i) 1) with (S_queue_len B i).
  step. change (u_at B 1704 4) with (S_cfg_max_body B).
  step. step.
  rewrite (tk_ltu_lits (S_cfg_max_body B) (len + S_queue_len B i)) by lia.
  destruct (Z.ltb_spec (S_cfg_max_body B) (len + S_queue_len B i)) as [Cmb|Cmb]; cbv iota;
    [ replace (len + S_queue_len B i <=? S_cfg_max_body B) with false in HM by (symmetry; apply Z.leb_gt; lia)
    | replace (len + S_queue_len B i <=? S_cfg_max_body B) with true in HM by (symmetry; apply Z.leb_le; lia) ];
    cbn [andb] in HM; cbv iota in HM.
  { (* len + c->len > max_body: the command is kept *)
    eapply (NOTFIT MCPY Q n j0 j32);
    [ exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
    | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HN | reflexivity
    | exact HM
    | apply (IH (if kept =? i then B else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32))
               body B2 bodyF (i + 1) taken (kept + 1) len hd lenF hdF takenF keptF K)
    | exact K ]. }
  (* 0x17a88 ld a0,40(sp); 0x17a8c beqz a0: allow_display *)
  step. step.
  rewrite (tk_eqb0 allow) by lia.
  destruct (Z.eqb_spec allow 0) as [Ca|Ca]; cbv iota;
    [ replace (negb (allow =? 0)) with false in HM by (symmetry; apply negb_false_iff, Z.eqb_eq; exact Ca)
    | replace (negb (allow =? 0)) with true in HM by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Ca) ];
    cbn [orb andb] in HM.
  - (* allow_display = 0: 0x17af8 lbu a0,1785(s4); 0x17afc beqz a0, the display flag *)
    step.
    replace (OFF_g_s + 32 * i + 1785) with (A_S_queue_display i) by (unfold A_S_queue_display; lia).
    change (u_at B (A_S_queue_display i) 1) with (S_queue_display B i).
    step.
    rewrite (tk_eqb_lits (S_queue_display B i) 0) by lia.
    destruct (Z.eqb_spec (S_queue_display B i) 0) as [Cd|Cd]; cbv iota;
      [ replace (S_queue_display B i =? 0) with true in HM by (symmetry; apply Z.eqb_eq; exact Cd)
      | replace (S_queue_display B i =? 0) with false in HM by (symmetry; apply Z.eqb_neq; exact Cd) ];
      cbn [andb] in HM; cbv iota in HM.
    2: { (* a display write the pacing refuses: the command is kept *)
         eapply (NOTFIT MCPY Q n j0 j32);
         [ exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST
         | exact MI | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HN | reflexivity
         | exact HM
         | apply (IH (if kept =? i then B else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32))
                    body B2 bodyF (i + 1) taken (kept + 1) len hd lenF hdF takenF keptF K)
         | exact K ]. }
    eapply (FIT DBC MCPY Q n j0 j32);
    [ exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST | exact MI
    | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HN | exact HM
    | (intros B1 body1 taken1 kept1 len1 hd1;
       apply (IH B1 body1 B2 bodyF (i + 1) taken1 kept1 len1 hd1 lenF hdF takenF keptF K))
    | exact K ].
  - eapply (FIT DBC MCPY Q n j0 j32);
    [ exact WM | exact GF | exact BJ | exact HJ | exact BH | exact BL | exact FR | exact ST | exact MI
    | exact MU | exact WMO | lia | lia | lia | lia | lia | lia | lia | exact HN | exact HM
    | (intros B1 body1 taken1 kept1 len1 hd1;
       apply (IH B1 body1 B2 bodyF (i + 1) taken1 kept1 len1 hd1 lenF hdF takenF keptF K))
    | exact K ].
Qed.

(* 0x179bc .. 0x17a58 and 0x17bf8, then 0x17c04 .. 0x17c54: the prologue, the first turn and the epilogue. *)
Lemma take_body : diginet_body_check_contract -> memcpy_contract ->
  forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (B B' body J JH : list byte) (len hd taken : Z),
  rw_cells rsegs m0 bp [CB 1484 J] -> rw_cells rsegs m0 blp [CB 8 JL] -> rw_cells rsegs m0 hdp [CB 4 JH] ->
  wmem rsegs m0 B -> g_fail_next B <= 1 ->
  take_m B allow = Some (B', (body, len, hd, taken)) ->
  stk rsegs m0 lo (bv_unsigned sp) -> mem_inv rsegs m0 ->
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
    (MS (mkR rra sp gp tp t0 t1 t2 rs0 rs1 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 bp)
             (Z_to_bv 64 blp) (Z_to_bv 64 allow) (Z_to_bv 64 hdp) a5 a6 a7
             rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x179bc) fc None m0 (seg_rom rsegs)).
Proof using All.
  intros DBC MCPY t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 B B' body J JH len hd taken BJ BL BH WM GF HM ST MI.
  pose proof ST as (Hlo2 & Hhi2 & _).
  wk_facts. tk_lens.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160)
    by (apply unsigned_lit; lia).
  pose proof (munch_refl TW m0) as MU.
  pose proof (wmono_refl rsegs m0) as WMO.
  (* the model: the loop of :358-382, then s->queued = kept *)
  unfold take_m in HM.
  destruct (take_loop_m B allow 0 0 0 0 0 [] (Z.to_nat (S_queued B)))
    as [[B2 [[[[bodyF lenF] hdF] takenF] keptF]]|] eqn:EL; [|discriminate HM].
  injection HM as <- <- <- <- <-.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* the prologue 0x179bc .. 0x179f8 *)
  carve_frame 160%nat ST.
  do 16 step.
  (* 0x179fc andi a1,a4,3; 0x17a00 bnez a1: has_display is 4-aligned *)
  step. rewrite (tku_land3 hdp) by (first [exact HA4 | lia]).
  step. tk_cond false.
  (* 0x17a04 mv s5,a0; 0x17a08 andi a0,a0,7: s = &g_s is 8-aligned *)
  step. step.
  replace (Z.land (bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s))) 7) with 0 by reflexivity.
  (* 0x17a0c sw zero,0(a4): *has_display = 0 *)
  step.
  (* 0x17a10 bnez a0 *)
  step. tk_cond false.
  (* 0x17a14 sd a2,24(sp); 0x17a18 .. 0x17a20 s7 = &s->queued; 0x17a24 lw a0,0(s7) *)
  do 5 step.
  change (s32_at B 19792) with (s32_at B A_S_queued).
  (* the epilogue 0x17c04 .. 0x17c54, for either exit *)
  assert (K : EXIT QQ B2 bodyF lenF hdF takenF keptF).
  { unfold tku_exit.
    intros ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s10' s11' t3' t4' t5' t6'
      m' JF jA jB WMF GFF BJF HJF BHF BLF FRF STF MIF MUF WMOF HLF HTF HKF.
    tk_lens.
    (* 0x17c04 ld a1,24(sp); 0x17c08 andi a0,a1,7 *)
    step. step. rewrite (tku_land7 blp) by (first [exact HA8 | lia]).
    (* 0x17c0c sw s9,0(s7): s->queued = kept *)
    step.
    (* 0x17c10 bnez a0: body_len is 8-aligned *)
    step. tk_cond false.
    (* 0x17c14 sd s8,0(a1): *body_len = len *)
    step.
    (* 0x17c18 .. 0x17c4c: the return value and the saved registers *)
    do 14 step.
    release_frame FRF STF (bv_unsigned sp).
    try (rewrite Hsp in STF).
    try (replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) in STF by lia).
    do 2 step.
    apply evt_done. unfold QQ.
    rewrite (tk_swrap32_small takenF) by lia.
    try (rewrite Hsp). try (replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) by lia).
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
  (* 0x17a28 beqz a0: s->queued = 0? *)
  step.
  rewrite (tk_eqb0 (s32_at B A_S_queued)) by (pose proof (s32_range B A_S_queued); lia).
  rewrite tk_s32_eq0. change (u_at B A_S_queued 4) with (S_queued B).
  pose proof (u_at_range B A_S_queued 4) as RQ.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RQ.
  change (u_at B A_S_queued 4) with (S_queued B) in RQ.
  destruct (Z.eqb_spec (S_queued B) 0) as [Q0|Q0]; cbv iota.
  - (* no command queued: 0x17bf8 li s9,0; li s8,0; li s1,0 *)
    replace (Z.to_nat (S_queued B)) with 0%nat in EL by lia.
    cbn [take_loop_m] in EL. injection EL as <- <- <- <- <- <-.
    do 3 step.
    unfold tku_exit in K. eapply K;
    [ eassumption | exact GF | eassumption | reflexivity | eassumption | eassumption | eassumption
    | eassumption | eassumption | eassumption | eassumption | lia | lia | lia ].
  - (* 0x17a2c .. 0x17a58: sd a4,8(sp); i = taken = kept = len = 0; s10, ~body to slot 16, s11; then the loop *)
    do 9 step.
    step. rewrite (tku_not bp) by lia.
    step.
    step.
    replace (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 1760))) 18446744073709551615))
      with (Z_to_bv 64 18446744073709338543) by (apply bv_eq; reflexivity).
    epose proof (tku_loop DBC MCPY QQ (Z.to_nat (S_queued B)) B [] B2 bodyF 0 0 0 0 0
                  lenF hdF takenF keptF K) as HL0.
    unfold tku_head in HL0.
    eapply HL0;
    [ reflexivity | reflexivity | reflexivity
    | eassumption | exact GF | eassumption | reflexivity | eassumption | eassumption | eassumption
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
  assert (SPm : tk_keep ((bv_unsigned sp + -160) mod 8 = 0))
    by (unfold tk_keep; clear - SP16; Z.div_mod_to_equations; lia).
  assert (HA4 : tk_keep (hdp mod 4 = 0)) by exact BH4.
  assert (HA8 : tk_keep (blp mod 8 = 0)) by exact BL8.
  exact (take_body sp gp tp F fc m lo bp blp hdp allow JL s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra
           HAL BP0 BP1 BP2 BP3 BL0 BL1 BL2 BL3 BH0 BH1 BH2 BH3 S1 S2 S3 LO WO Rsp Hlo SPm HA4 HA8
           eq_refl eq_refl eq_refl DBC MCPY t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 B B' body J JH len hd taken
           BJ BL BH WM GF HM ST MI).
Qed.

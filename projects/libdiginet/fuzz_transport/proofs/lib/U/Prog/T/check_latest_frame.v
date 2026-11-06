(* check_latest_frame (fuzz/fuzz_transport.c:582-597), entry 0x15668, 23 instructions, FRAME 16.
   The walk of the contract in U/Prog/T/check_latest_frame_c.v against the ubsan binary. The paths that
   return use no stack (the 16 bytes of FRAME are what the abort path's prologue allocates), so the memory
   is not written at all. abort (0x18ff8) and the misalignment trap (`unimp` at 0x156c0) are unreachable:
   the trap by the 8-alignment of sframe_at, the four abort branches by exfalso from the model premise
   check_latest_frame_m B frame cmds = Some (B, tt). No callee contract is used. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract check_latest_frame_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the 32-bit sign extension of the RV64 psABI (an unsigned int argument, an int32 load) ---- *)

Lemma swrap32_cases : forall x, 0 <= x < 2 ^ 32 ->
  (x < 2 ^ 31 /\ bv_swrap 32 x = x) \/ (2 ^ 31 <= x /\ bv_swrap 32 x = x - 2 ^ 32).
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  destruct (Z_lt_le_dec x (2 ^ 31)) as [L|L].
  - left. split; [lia|]. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|].
    rewrite <- (Z.mod_add (x + 2 ^ 31) (-1) (2 ^ 32)) by (vm_compute; discriminate).
    rewrite Z.mod_small by lia. lia.
Qed.

(* the sign extension depends on the value mod 2 ^ 32 only *)
Lemma swrap32_cong : forall x y k, x = y + k * 2 ^ 32 -> bv_swrap 32 x = bv_swrap 32 y.
Proof.
  intros x y k ->. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32). f_equal.
  replace (y + k * 2 ^ 32 + bv_half_modulus 32) with (y + bv_half_modulus 32 + k * 2 ^ 32) by lia.
  apply Z.mod_add. vm_compute. discriminate.
Qed.

Lemma swrap32_modx : forall x, bv_swrap 32 (x mod 2 ^ 32) = bv_swrap 32 x.
Proof.
  intros x. apply (swrap32_cong _ _ (- (x / 2 ^ 32))).
  rewrite Z.mod_eq by (vm_compute; discriminate). lia.
Qed.

(* n bytes of a struct the caller gave as bytes_at (disco Prog/disco_table.v:38) *)
Lemma rd_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) n = Some (sub bs k n).
Proof. intros m a bs k n H Hk Hn. apply (bytes_at_read rsegs m a bs k n H Hk). lia. Qed.

Theorem check_latest_frame_holds : check_latest_frame_contract.
Proof.
  unfold check_latest_frame_contract, check_latest_frame_ENTRY, check_latest_frame_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo B B' fp fa frame cmds Ha0 Ha1 Hcmds SF OWF WM MODEL SP16 ST LO WOS MI.
  subst a0 a1.
  (* ---- the model premise: the world is unchanged, and every abort branch is impossible ---- *)
  assert (HB : B' = B) by (unfold check_latest_frame_m in MODEL;
    destruct ((Cfg_max_body B <? sf_body_len (rf frame)) || (Cfg_max_cmds B <? sf_ncmds (rf frame))
              || (negb (truth (g_raw B)) && negb (sf_ncmds (rf frame) =? cmds))); [discriminate MODEL|];
    destruct (negb (sf_send (rf frame) =? u32 (M_host_counter B + sf_ncmds (rf frame)))); [discriminate MODEL|];
    congruence).
  subst B'.
  unfold check_latest_frame_m in MODEL.
  destruct ((Cfg_max_body B <? sf_body_len (rf frame)) || (Cfg_max_cmds B <? sf_ncmds (rf frame))
            || (negb (truth (g_raw B)) && negb (sf_ncmds (rf frame) =? cmds))) eqn:C1; [discriminate MODEL|].
  destruct (negb (sf_send (rf frame) =? u32 (M_host_counter B + sf_ncmds (rf frame)))) eqn:C2;
    [discriminate MODEL|].
  clear MODEL.
  apply orb_false_iff in C1 as [C1a Craw]. apply orb_false_iff in C1a as [Cbody Ccmds].
  apply Z.ltb_ge in Cbody. apply Z.ltb_ge in Ccmds.
  apply negb_false_iff, Z.eqb_eq in C2.
  (* ---- struct spec_frame at fp ---- *)
  destruct SF as (FP0 & FP8 & SB & HSB & LSB & Fcode & Fdst & Fsrc & Feth & Fnum & Fsum & Fretry & Fsend &
                  Fack & Fcmd & Fncmds & Fbody & Fblen & Fpad & Fbsum).
  unfold off_window in OWF. unfold w_off_stack in WOS.
  pose proof HSB as HSB'. destruct HSB' as (FPlo & FPhi & _). rewrite LSB in FPhi.
  (* the 8-alignment of the struct: the ubsan build traps a misaligned member access *)
  assert (HA : Z.land fp 7 = 0).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. exact FP8. }
  (* ---- the ranges the branches need, in the model's language ---- *)
  assert (Rmb : 0 <= Cfg_max_body B < 2 ^ 32).
  { pose proof (u_at_range B A_Cfg_max_body 4) as H. change (8 * Z.of_nat 4) with 32 in H. exact H. }
  assert (Rmc : 0 <= Cfg_max_cmds B < 2 ^ 32).
  { pose proof (u_at_range B A_Cfg_max_cmds 4) as H. change (8 * Z.of_nat 4) with 32 in H. exact H. }
  assert (Rhc : 0 <= M_host_counter B < 2 ^ 32).
  { pose proof (u_at_range B A_M_host_counter 4) as H. change (8 * Z.of_nat 4) with 32 in H. exact H. }
  assert (Rnc : 0 <= sf_ncmds (rf frame) < 2 ^ 8).
  { pose proof (u_at_range SB 41 1) as H. change (8 * Z.of_nat 1) with 8 in H. rewrite Fncmds in H. exact H. }
  assert (Rbl : 0 <= sf_body_len (rf frame) < 2 ^ 64).
  { pose proof (u_at_range SB 56 8) as H. change (8 * Z.of_nat 8) with 64 in H. rewrite Fblen in H. exact H. }
  assert (Rsd : 0 <= sf_send (rf frame) < 2 ^ 32).
  { pose proof (u_at_range SB 32 4) as H. change (8 * Z.of_nat 4) with 32 in H. rewrite Fsend in H. exact H. }
  assert (Dmc : (Cfg_max_cmds B < 2 ^ 31 /\ bv_swrap 32 (Cfg_max_cmds B) = Cfg_max_cmds B) \/
                (2 ^ 31 <= Cfg_max_cmds B /\ bv_swrap 32 (Cfg_max_cmds B) = Cfg_max_cmds B - 2 ^ 32))
    by (apply swrap32_cases; lia).
  assert (Dhc : (M_host_counter B < 2 ^ 31 /\ bv_swrap 32 (M_host_counter B) = M_host_counter B) \/
                (2 ^ 31 <= M_host_counter B /\ bv_swrap 32 (M_host_counter B) = M_host_counter B - 2 ^ 32))
    by (apply swrap32_cases; lia).
  assert (Dcm : (cmds < 2 ^ 31 /\ bv_swrap 32 cmds = cmds) \/
                (2 ^ 31 <= cmds /\ bv_swrap 32 cmds = cmds - 2 ^ 32)) by (apply swrap32_cases; lia).
  assert (Rraw : 0 <= u_at B OFF_g_raw 4 < 2 ^ 32).
  { pose proof (u_at_range B OFF_g_raw 4) as H. change (8 * Z.of_nat 4) with 32 in H. exact H. }
  assert (Draw : (u_at B OFF_g_raw 4 < 2 ^ 31 /\ g_raw B = u_at B OFF_g_raw 4) \/
                 (2 ^ 31 <= u_at B OFF_g_raw 4 /\ g_raw B = u_at B OFF_g_raw 4 - 2 ^ 32))
    by (apply swrap32_cases; lia).
  (* ---- the machine: no path that returns writes memory ---- *)
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  wk_facts.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  step.                                      (* 15668 andi  a2,a0,7 *)
  step.                                      (* 1566c bnez  a2,trap (a misaligned struct spec_frame) *)
  if_cases E0; cbv iota;
    [ exfalso; zify_cond E0; rewrite ?unsigned_lit_wrap in E0; rewrite HA in E0; lia | ].
  pose proof (rd_sub _ fp SB 56 8 HSB ltac:(lia) ltac:(rewrite LSB; cbn; lia)) as RD56.
  step.                                      (* 15670 ld    a2,56(a0) = f->body_len *)
  rewrite wm_ld, Fblen.
  step. step.                                (* 15674 auipc a3; 15678 addi a3 -> &g_fail_next *)
  step.                                      (* 1567c lwu   a4,112(a3) = g_cfg.max_body *)
  change (u_at B 65080 4) with (Cfg_max_body B).
  step.                                      (* 15680 bltu  a4,a2,abort (:589 f->body_len > max_body) *)
  if_cases E1; cbv iota;
    [ exfalso; zify_cond E1; rewrite ?unsigned_lit_wrap in E1; lia | ].
  pose proof (rd_sub _ fp SB 41 1 HSB ltac:(lia) ltac:(rewrite LSB; cbn; lia)) as RD41.
  step.                                      (* 15684 lbu   a2,41(a0) = f->ncmds *)
  rewrite wm_lbu, Fncmds.
  step.                                      (* 15688 lw    a4,108(a3) = g_cfg.max_cmds *)
  change (s32_at B 65076) with (bv_swrap 32 (Cfg_max_cmds B)).
  step.                                      (* 1568c bltu  a4,a2,abort (:589 f->ncmds > max_cmds) *)
  if_cases E2; cbv iota;
    [ exfalso; zify_cond E2; rewrite ?unsigned_lit_wrap in E2; lia | ].
  step.                                      (* 15690 beq   a1,a2,1569c (:590 f->ncmds == cmds) *)
  if_cases E3; cbv iota;
    [ | assert (RAW : g_raw B <> 0);
        [ apply andb_false_iff in Craw as [Cr|Cr];
          [ apply negb_false_iff in Cr; unfold truth in Cr;
            apply negb_true_iff, Z.eqb_neq in Cr; exact Cr
          | exfalso; apply negb_false_iff, Z.eqb_eq in Cr;
            zify_cond E3; rewrite ?unsigned_lit_wrap in E3; lia ]
        | ];
        step;                                (* 15694 lw    a1,4(a3) = g_raw *)
        change (s32_at B 64972) with (g_raw B);
        step;                                (* 15698 beqz  a1,abort (:590 !g_raw) *)
        if_cases E4; cbv iota;
          [ exfalso; zify_cond E4; rewrite ?unsigned_lit_wrap in E4; lia | ] ].
  (* both paths are at 1569c *)
  all: step; step.                           (* 1569c auipc a1; 156a0 lw a1,-840(a1) = M.host_counter *)
  all: change (s32_at B 84) with (bv_swrap 32 (M_host_counter B)).
  all: pose proof (rd_sub _ fp SB 32 4 HSB ltac:(lia) ltac:(rewrite LSB; cbn; lia)) as RD32.
  all: step.                                 (* 156a4 lw    a0,32(a0) = f->send *)
  all: rewrite wm_lw.
  all: change (s32_at SB 32) with (bv_swrap 32 (u_at SB 32 4)).
  all: rewrite Fsend.
  all: step.                                 (* 156a8 addw  a1,a1,a2 = host_counter + ncmds *)
  (* the model (:595-596) says f->send is host_counter + ncmds mod 2^32, so the two registers agree *)
  all: replace (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (M_host_counter B))) +
                                         bv_unsigned (Z_to_bv 64 (sf_ncmds (rf frame))))))
          with (Z_to_bv 64 (bv_swrap 32 (sf_send (rf frame))))
          by (f_equal; rewrite (unsigned_lit (sf_ncmds (rf frame))) by lia;
              rewrite C2; unfold u32; rewrite swrap32_modx;
              destruct Dhc as [[Hlt Hq]|[Hge Hq]]; rewrite Hq;
              [ rewrite unsigned_lit by lia; reflexivity
              | rewrite unsigned_lit_wrap;
                rewrite <- (Z.mod_add (M_host_counter B - 2 ^ 32) 1 (2 ^ 64)) by (vm_compute; discriminate);
                rewrite (Z.mod_small (M_host_counter B - 2 ^ 32 + 1 * 2 ^ 64)) by lia;
                symmetry; apply (swrap32_cong _ _ (2 ^ 32 - 1)); lia ]).
  all: step.                                 (* 156ac bne   a0,a1,abort (:595 f->send != expected) *)
  all: if_false.
  all: step.                                 (* 156b0 ret *)
  all: apply evt_done; unfold QQ; hnf; do 16 eexists; split; [reflexivity|];
       split; [exact MU|]; split; [exact WMo|]; split; [exact MI|]; split; [exact ST|];
       split; [reflexivity|]; exact WM.
Qed.

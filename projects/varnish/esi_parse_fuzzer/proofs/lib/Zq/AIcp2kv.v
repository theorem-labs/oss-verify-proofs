(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@REALR; @AFB; @AFA; @N1; @RSTK80; @Hc; @Hj; @CEIL; @SB; @ESL; @LOLE; @SPR; @CV; @HS2; @LB; @ESF; @LOLE'; @SFB; @H; @A3R; @LBR; @N32; @K; @K3; @REALE; @SEPA; @SEPB; @K1; @K4; @HS1; @LBB; @LB1; @SHhi; @K8])).
Ltac hot_lia_full := tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
(* [comment removed for export] *)
Local Ltac hs_lbr X :=
  first [ match goal with H : (X = 0 \/ ?m < X <= 7)%Z |- _ =>
            clear - H; lazymatch m with (?a mod ?b)%Z => pose proof (Z.mod_pos_bound a b ltac:(reflexivity)) | _ => idtac end; lia end
        | lia ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)

Definition mic_entry : Z := 0x486b0.
Definition MIC_FRAME : Z := 2192.

(* [comment removed for export] *)
Definition mic_cells (m : word -> option byte) : Prop :=
     ro_cells rsegs m 0xa8b60 [C8 (Z_to_bv 64 0x1466e8)]            (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x1467e6 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]   (* [comment removed for export] *)
  /\ asan_inited_cell m                                               (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xaa8c0 [C8 (Z_to_bv 64 0xa1b5c)]            (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xaa8c8 [C8 (Z_to_bv 64 0xa1a8c)]            (* [comment removed for export] *)
  /\ map_cells m.

(* [comment removed for export] *)
Definition mic_real_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (ls rs : list byte) (v lo rstk : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - rstk, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) ls /\ bytes_at rsegs m' (bv_unsigned a1) rs.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition mic_real_contract (real rstk : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v : Z) (lo : Z),
  bytes_at rsegs m (bv_unsigned a0) ls -> bytes_at rsegs m (bv_unsigned a1) rs ->
  memcmp_model ls rs (Z.to_nat (bv_unsigned a2)) = Some v ->
  mem_inv rsegs m -> mic_cells m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + rstk <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (bv_unsigned a0 + Z.of_nat (length ls) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + Z.of_nat (length rs) <= lo \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a2 < 2^32)%Z ->
  (bv_unsigned a2 = 0%Z \/ (range_ok m (bv_unsigned a0) (bv_unsigned a2) /\ range_ok m (bv_unsigned a1) (bv_unsigned a2))) ->
  evt rsegs (mic_real_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v lo rstk m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 real) fc None m (seg_rom rsegs)).

End CEIL.

(* [comment removed for export] *)
Definition mic_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a2 a3 : word) (ls rs : list byte) (v lo rstk : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - (2192 + rstk), bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a2) ls /\ bytes_at rsegs m' (bv_unsigned a3) rs.

Ltac solve_mic_cells := unfold mic_cells, asan_inited_cell, map_cells; repeat (split; [assumption|]); assumption.

Ltac open_mic_cells H :=
  let G := fresh "Gcf" in let C := fresh "Ccf" in let I := fresh "CI" in let R1 := fresh "Crm" in let R2 := fresh "Crb" in let MC := fresh "MC" in
  destruct H as (G & C & I & R1 & R2 & MC); pose proof MC as MC'; open_map_cells MC'; unfold asan_inited_cell in I.

Section MIC.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (real RSTK : Z).
  Hypothesis REALR : (0 <= real < 2^64)%Z.
  Hypothesis REALE : (real mod 2 = 0)%Z.
  Hypothesis RSTK80 : (80 <= RSTK)%Z.
  Hypothesis REALC : mic_real_contract real RSTK.

  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v lo : Z).
  Notation A := (bv_unsigned a2).
  Notation B := (bv_unsigned a3).
  Notation N := (bv_unsigned a4).
  Notation POST := (mic_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a2 a3 ls rs v lo RSTK m).
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -104)
                          [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2192) [CB 2088 fjunk]).
  Hypothesis LOLE : (lo + (2192 + RSTK) <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis HM : memcmp_model ls rs (Z.to_nat N) = Some v.
  Hypothesis N32 : (N < 2^32)%Z.
  Notation SEPAt := ((A + Z.of_nat (length ls) <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).
  Notation SEPBt := ((B + Z.of_nat (length rs) <= lo \/ bv_unsigned sp <= B)%Z) (only parsing).

  (* [comment removed for export] *)
  #[using="N32 HM CEIL LOLE REALC RSTK80 REALE REALR Clg"] Lemma mic_tail : forall m1 fjunk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x26 x28 x29 x30 x31,
    SEPAt -> SEPBt ->
    (N = 0%Z \/ (range_ok m1 A N /\ range_ok m1 B N)) ->
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - (2192 + RSTK), bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -2192) -> FRAME m1 -> FRAMEB m1 fjunk ->
    bytes_at rsegs m1 A ls -> bytes_at rsegs m1 B rs -> mic_cells m1 ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a4
               x10 x11 x12 x13 x14 x15 x16 x17 a3 ra a2 (Z_to_bv 64 real) x22 (Z_to_bv 64 (bv_unsigned sp + -2176))
               (Z_to_bv 64 0x1466e8) x25 x26 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x487c0) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros SEPA SEPB RNG1 MI1 MU1 WM1 ST1 FR1 FRB1 LS1 RS1 CELLS1.
    pose proof CELLS1 as CELLS1'. open_mic_cells CELLS1'.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
    pose proof (zr_word a3) as A3R; unfold inr64 in A3R. pose proof (zr_word a4) as A4R; unfold inr64 in A4R.
    pose proof (zr_word ra) as RAR; unfold inr64 in RAR. pose proof alloc_ceiling_val as CV.
    pose proof (bytes_at_bound _ _ _ _ LS1) as LB. pose proof (bytes_at_bound _ _ _ _ RS1) as RB.
    zstep. zstep. zstep.
    zstep. rewrite (ret_pc_even real) by lia.
    call_lit REALC by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ (bv_unsigned a2) _ => exact LS1
      | |- bytes_at _ _ (bv_unsigned a3) _ => exact RS1
      | |- memcmp_model _ _ _ = _ => rewrite ?unsigned_lit by lia; exact HM
      | |- mem_inv _ _ => exact MI1
      | |- mic_cells _ => exact CELLS1
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
      | |- (_ = 0%Z \/ _) => exact RNG1
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zstep. zstep.
    do 5 zstep. zstep. (* [comment removed for export] *) zstep. (* [comment removed for export] *)
    zstep. zstep.
    do 13 zstep. zstep. zstep.
    lazymatch goal with ST : stk rsegs _ lo _ |- _ =>
      release_frame FRB1 ST (bv_unsigned sp + -104)%Z; release_frame FR1 ST (bv_unsigned sp) end.
    finish.
  Qed.

  Section Facts.
    (* [comment removed for export] *)
    Variables (ngA ngB : nat) (lastbA lastbB : Z) (w1A w2A w1B w2B : word).
    Notation LBAt := ((lastbA = 0 \/ ((A + N - 1) mod 8 < lastbA <= 7))%Z) (only parsing).
    Notation LBBt := ((lastbB = 0 \/ ((B + N - 1) mod 8 < lastbB <= 7))%Z) (only parsing).
    Hypothesis AFA : (0 <= A /\ A + N + 8 <= 0x800000000000)%Z.
    Hypothesis AFB : (0 <= B /\ B + N + 8 <= 0x800000000000)%Z.
    Hypothesis IRA : inmem_range A N.
    Hypothesis IRB : inmem_range B N.
    Hypothesis NGA : ((A + N - 1) / 8 - A / 8 = Z.of_nat ngA)%Z.
    Hypothesis NGB : ((B + N - 1) / 8 - B / 8 = Z.of_nat ngB)%Z.
    Hypothesis N1 : (1 <= N)%Z.

    Section Phase2.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(bv_unsigned sp - (2192 + RSTK), bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2192).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis LS1 : bytes_at rsegs m1 A ls.
      Hypothesis RS1 : bytes_at rsegs m1 B rs.
      Hypothesis Gcf : ro_cells rsegs m1 0xa8b60 [C8 (Z_to_bv 64 0x1466e8)].
      Hypothesis Ccf : ro_cells rsegs m1 0x1467e6 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
      Hypothesis CI : ro_cells rsegs m1 0xb5898 [C1 (Z_to_bv 8 1)].
      Hypothesis Crm : ro_cells rsegs m1 0xaa8c0 [C8 (Z_to_bv 64 0xa1b5c)].
      Hypothesis Crb : ro_cells rsegs m1 0xaa8c8 [C8 (Z_to_bv 64 0xa1a8c)].
      Hypothesis Gsh : ro_cells rsegs m1 0xa8b70 [C8 (Z_to_bv 64 0xb4bb8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa8b78 [C8 (Z_to_bv 64 0xb58a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb58a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa8b80 [C8 (Z_to_bv 64 0xb58b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb58b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa8b88 [C8 (Z_to_bv 64 0xb58a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SHA1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ngA ++ [Z_to_bv 8 lastbA]).
      Hypothesis QBA1 : bytes_at rsegs m1 (sha A - sha A mod 8) (le8 w1A).
      Hypothesis QBA2 : bytes_at rsegs m1 (sha (A + N + -1) - sha (A + N + -1) mod 8) (le8 w2A).
      Hypothesis SHB1 : bytes_at rsegs m1 (B / 8 + shadow_off) (zeros ngB ++ [Z_to_bv 8 lastbB]).
      Hypothesis QBB1 : bytes_at rsegs m1 (sha B - sha B mod 8) (le8 w1B).
      Hypothesis QBB2 : bytes_at rsegs m1 (sha (B + N + -1) - sha (B + N + -1) mod 8) (le8 w2B).

      (* [comment removed for export] *)
      #[using="QBB2 QBB1 SHB1 QBA2 QBA1 SHA1 N1 NGB NGA IRB IRA AFB AFA w2B w1B w2A w1A ngB ngA real"] Lemma mic_rng1 : LBAt -> LBBt -> (N = 0%Z \/ (range_ok m1 A N /\ range_ok m1 B N)).
      Proof.
        intros LBA LBB. right.
        pose proof (bytes_at_bound _ _ _ _ QBA1) as Q1. pose proof (bytes_at_bound _ _ _ _ QBA2) as Q2.
        pose proof (bytes_at_bound _ _ _ _ QBB1) as Q3. pose proof (bytes_at_bound _ _ _ _ QBB2) as Q4.
        split; (split; [assumption|]); split.
        - exists ngA, lastbA. split; [exact NGA|]. split; [exact SHA1| exact LBA].
        - split; [eapply bytes_at_mapped8; [exact QBA1| unfold sha, shadow_off; mlia]|].
          replace (A + N - 1)%Z with (A + N + -1)%Z by lia.
          eapply bytes_at_mapped8; [exact QBA2| unfold sha, shadow_off; mlia].
        - exists ngB, lastbB. split; [exact NGB|]. split; [exact SHB1| exact LBB].
        - split; [eapply bytes_at_mapped8; [exact QBB1| unfold sha, shadow_off; mlia]|].
          replace (B + N - 1)%Z with (B + N + -1)%Z by lia.
          eapply bytes_at_mapped8; [exact QBB2| unfold sha, shadow_off; mlia].
      Qed.

      Section SlowB.
        Variables (sf sl : Z) (x1 x5 x6 x7 x10 x15 x16 x17 x22 x26 x28 x29 x30 x31 : word).
        Hypothesis SEPA : SEPAt. Hypothesis SEPB : SEPBt. Hypothesis LBA : LBAt. Hypothesis LBB : LBBt.
        Hypothesis ESF : (sf = B / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ngB)%Z.
        Notation AT pc x11 x13 x14 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a4
                   x10 x11 (Z_to_bv 64 sl) x13 x14 x15 x16 x17 a3 ra a2 (Z_to_bv 64 real) x22 (Z_to_bv 64 (bv_unsigned sp + -2176))
                   (Z_to_bv 64 0x1466e8) (Z_to_bv 64 (N + -65)) x26 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        (* [comment removed for export] *)
        #[using="LBB LBA SEPB SEPA QBB2 QBB1 SHB1 QBA2 QBA1 SHA1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Crb Crm CI Ccf Gcf RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 NGB NGA IRB IRA AFB AFA w2B w1B w2A w1A lastbB lastbA ngB ngA N32 HM CEIL LOLE REALC RSTK80 REALE REALR Clg"] Lemma mic_slowB_end : forall x11 x14, evt rsegs POST (AT 0x48c48 x11 (Z_to_bv 64 0) x14).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
          zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val. cbv in K. lia. }
          eapply mic_tail; try eassumption; try solve_mic_cells. apply mic_rng1; assumption.
        Qed.

        (* [comment removed for export] *)
        #[using="ESL ESF LBB LBA SEPB SEPA QBB2 QBB1 SHB1 QBA2 QBA1 SHA1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Crb Crm CI Ccf Gcf RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 NGB NGA IRB IRA AFB AFA w2B w1B w2A w1A lastbB lastbA ngA N32 HM CEIL LOLE REALC RSTK80 REALE REALR Clg"] Lemma mic_slowB_loop : forall (c : nat) (j : Z) x11 x14,
          Z.to_nat (Z.of_nat ngB - j) = c -> (0 <= j < Z.of_nat ngB)%Z -> x11 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x48c38 x11 (Z_to_bv 64 0) x14).
        Proof.
          induction c as [|c IH]; intros j x11 x14 Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SHB1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (B / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SHB1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ngB lastbB (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ngB)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep.
          zstep. if_cases K; zify_cond K.
          - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
          - apply mic_slowB_end.
        Qed.
      End SlowB.

      (* [comment removed for export] *)
      #[using="QBB2 QBB1 SHB1 QBA2 QBA1 SHA1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Crb Crm CI Ccf Gcf RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 NGB NGA IRB IRA AFB AFA w2B w1B w2A w1A ngB ngA N32 HM CEIL LOLE REALC RSTK80 REALE REALR Clg"] Lemma mic_p2 : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x28 x29 x30 x31,
        SEPAt -> SEPBt -> LBAt -> LBBt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a4
                   x10 x11 x12 x13 x14 x15 x16 x17 a3 ra a2 (Z_to_bv 64 real) x22 (Z_to_bv 64 (bv_unsigned sp + -2176))
                   (Z_to_bv 64 0x1466e8) (Z_to_bv 64 (N + -65)) x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x48774) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros SEPA SEPB LBA LBB. pose proof LOLE as LOLE'.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a2) as A2R; unfold inr64 in A2R. pose proof (zr_word a3) as A3R; unfold inr64 in A3R.
        pose proof (zr_word a4) as A4R; unfold inr64 in A4R. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
        pose proof (bytes_at_bound _ _ _ _ LS1) as LB. pose proof (bytes_at_bound _ _ _ _ RS1) as RB.
        assert (QH1 : (sha B - sha B mod 8 + Z.of_nat (length (le8 w1B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (B + N + -1) - sha (B + N + -1) mod 8 + Z.of_nat (length (le8 w2B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH3 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH4 : (sha (A + N + -1) - sha (A + N + -1) mod 8 + Z.of_nat (length (le8 w2A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SHB1 as SH. remember (zeros ngB ++ [Z_to_bv 8 lastbB]) as sbs eqn:Esbs.
        assert (SHhi : (B / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof SHA1 as SHA. remember (zeros ngA ++ [Z_to_bv 8 lastbA]) as sbsA eqn:EsbsA.
        assert (SHAhi : (A / 8 + shadow_off + Z.of_nat (length sbsA) <= 0x100080000000)%Z).
        { subst sbsA. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QBB1 as QB1. pose proof QBB2 as QB2. pose proof QBA1 as QB3. pose proof QBA2 as QB4.
        zstep. rewrite zb_lxor_ones by lia.
        zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        zstep.
        zstep. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
          do 3 zstep.
          zstep. call_lit region_is_poisoned_spec by (idtac;
            lazymatch goal with
            | |- map_cells _ => repeat (split; [assumption|]); assumption
            | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
            | |- mem_inv _ _ => eassumption
            | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IRB
            | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ngB, lastbB; subst sbs; split; [exact NGB| split; [exact SH| exact LBB]]
            | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
            end).
          zstep.
          zstep. if_cases K4; zify_cond K4. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K4; try pose proof alloc_ceiling_val. cbv in K4. lia. }
          subst sbs sbsA. eapply mic_tail; try eassumption; try solve_mic_cells.
          right. split; (split; [assumption|]); split.
          + exists ngA, lastbA. split; [exact NGA|]. split; [assumption| exact LBA].
          + split; [eapply bytes_at_mapped8; [exact QB3| unfold sha, shadow_off; mlia]|].
            replace (A + N - 1)%Z with (A + N + -1)%Z by lia. eapply bytes_at_mapped8; [exact QB4| unfold sha, shadow_off; mlia].
          + exists ngB, lastbB. split; [exact NGB|]. split; [assumption| exact LBB].
          + split; [eapply bytes_at_mapped8; [exact QB1| unfold sha, shadow_off; mlia]|].
            replace (B + N - 1)%Z with (B + N + -1)%Z by lia. eapply bytes_at_mapped8; [exact QB2| unfold sha, shadow_off; mlia].
        - (* [comment removed for export] *)
          assert (HS1 : (0 <= Z.shiftr B 3 <= B)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (B + N + -1) 3 <= B + N - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 11 zstep.
          pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
          zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + (* [comment removed for export] *)
            subst sbs.
            assert (LBR : (0 <= lastbB < 128)%Z) by (hs_lbr lastbB).
            pose proof (u8ro_read rsegs _ (B / 8 + shadow_off) _ (Z.of_nat ngB) (Z_to_bv 8 lastbB)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (B + N + -1) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ngB lastbB ngB), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (B + N + -1) lastbB) by
              (first [destruct LBB as [LB0|LB1]; [left; exact LB0| right;
                 replace (B + N + -1)%Z with (B + N - 1)%Z by (clear - LB1; lia); (clear - LB1; lia)] | lia]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + B / 8)%Z). set (sl := (2147450880 + (B + N + -1) / 8)%Z).
            assert (ESF : (sf = B / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ngB)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl. subst sbsA.
            zstep. if_cases K8; zify_cond K8.
            * eapply mic_slowB_end; eassumption.
            * eapply mic_slowB_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + subst sbs sbsA. eapply mic_tail; try eassumption; try solve_mic_cells. apply mic_rng1; assumption.
      Qed.
    End Phase2.
  End Facts.
End MIC.


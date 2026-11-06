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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.

Module AIcpa3z.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA RA_m08t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hs_lbr X :=
  first [ match goal with H : (X = 0 \/ ?m < X <= 7)%Z |- _ =>
            clear - H; lazymatch m with (?a mod ?b)%Z => pose proof (Z.mod_pos_bound a b ltac:(reflexivity)) | _ => idtac end; lia end
        | lia ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].

Definition memchr_icpt_entry : Z := 0x47a14.
Definition MEMCHR_ICPT_STACK : Z := 2208.

Definition memchr_icpt_cells (m : word -> option byte) : Prop :=
     asan_inited_cell m
  /\ ro_cells rsegs m 0xaaef0 [C8 (Z_to_bv 64 0xa20c8)]      (* [comment removed for export] *)
  /\ map_cells m.

(* [comment removed for export] *)
Definition memchr_len (c n : Z) (buf : list byte) : Z :=
  match find_byte c (firstn (Z.to_nat n) buf) with Some i => Z.of_nat i + 1 | None => n end.

Lemma memchr_len_bound : forall c n buf, (0 <= n)%Z -> (0 <= memchr_len c n buf <= n)%Z.
Proof.
  intros c n buf Hn. unfold memchr_len. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [|lia].
  destruct (find_byte_Some _ _ _ E) as (Hi & _ & _). rewrite firstn_length in Hi. lia.
Qed.

Definition memchr_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (c n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res (bv_unsigned a0) c n buf)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - MEMCHR_ICPT_STACK, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) buf.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte) (lo c n v L : Z).
  Notation A := (bv_unsigned a0).
  Hypothesis HV : v = memchr_res A c n buf.
  Hypothesis HL : L = memchr_len c n buf.
  Notation POST := (memchr_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 c n buf lo m).
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2128) [CB 2072 fjunk]).
  Hypothesis LOLE : (lo + MEMCHR_ICPT_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis L32 : (0 <= L < 2^32)%Z.
  Hypothesis VR : (0 <= v < 2^64)%Z.
  Notation SEPt := ((A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).

  (* [comment removed for export] *)
  #[using="LOLE HV"] Lemma mr_exit : forall m1 fjunk x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    mem_inv rsegs m1 -> munch [(bv_unsigned sp - MEMCHR_ICPT_STACK, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -2128) -> FRAME m1 -> FRAMEB m1 fjunk -> bytes_at rsegs m1 A buf ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9
               (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x49298) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros MI1 MU1 WM1 ST1 FR1 FRB1 B1. unfold MEMCHR_ICPT_STACK in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    do 10 zstep.
    release_frame FRB1 ST1 (bv_unsigned sp + -56)%Z. release_frame FR1 ST1 (bv_unsigned sp). rewrite HV. finish.
  Qed.

  Section Facts.
    Variables (ng : nat) (lastb : Z) (w1 w2 : word).
    Notation LBt := ((lastb = 0 \/ ((A + L - 1) mod 8 < lastb <= 7))%Z) (only parsing).
    Hypothesis AF : (0 <= A /\ A + L + 8 <= 0x800000000000)%Z.
    Hypothesis IR : inmem_range A L.
    Hypothesis NG : ((A + L - 1) / 8 - A / 8 = Z.of_nat ng)%Z.
    Hypothesis L1 : (1 <= L)%Z.

    Section Phase.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(bv_unsigned sp - MEMCHR_ICPT_STACK, bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2128).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis B1 : bytes_at rsegs m1 A buf.
      Hypothesis Gsh : ro_cells rsegs m1 0xa9190 [C8 (Z_to_bv 64 0xb53b8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb53b8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa9198 [C8 (Z_to_bv 64 0xb60a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb60a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa91a0 [C8 (Z_to_bv 64 0xb60b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb60b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa91a8 [C8 (Z_to_bv 64 0xb60a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb60a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SH1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]).
      Hypothesis QB1 : bytes_at rsegs m1 (sha A - sha A mod 8) (le8 w1).
      Hypothesis QB2 : bytes_at rsegs m1 (sha (A + L + -1) - sha (A + L + -1) mod 8) (le8 w2).

      Section Slow.
        Variables (sf sl : Z) (x1 x5 x6 x7 x9 x15 x16 x17 x18 x19 x21 x28 x29 x30 x31 : word).
        Hypothesis SEP : SEPt.
        Hypothesis ESF : (sf = A / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ng)%Z.
        Notation AT pc x11 x13 x14 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp (Z_to_bv 64 L)
                   (Z_to_bv 64 v) x11 (Z_to_bv 64 sl) x13 x14 x15 x16 x17 a0 x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        #[using="B1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk ng LOLE HV"] Lemma mr_slow_end : forall x11 x14, evt rsegs POST (AT 0x493b8 x11 (Z_to_bv 64 0) x14).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
          zstep. zstep. if_cases K; zify_cond K. all: try (deadK K).
          eapply mr_exit; try eassumption.
        Qed.

        #[using="ESL ESF SH1 B1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk L1 AF lastb LOLE HV"] Lemma mr_slow_loop : forall (cc : nat) (j : Z) x11 x14,
          Z.to_nat (Z.of_nat ng - j) = cc -> (0 <= j < Z.of_nat ng)%Z -> x11 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x493a8 x11 (Z_to_bv 64 0) x14).
        Proof.
          induction cc as [|cc IH]; intros j x11 x14 Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SH1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (A / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SH1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ng lastb (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ng)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep.
          zstep. if_cases K; zify_cond K.
          - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
          - apply mr_slow_end.
        Qed.
      End Slow.

      (* [comment removed for export] *)
      #[using="QB2 QB1 SH1 Che Ghe Cme Gme Cmb Gmb Csh Gsh B1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk L1 NG IR AF w2 w1 ng L32 CEIL LOLE HV Clg"] Lemma mr_phase : forall (xs1 : word) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x28 x29 x30 x31,
        xs1 = Z_to_bv 64 L -> SEPt -> LBt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp xs1
                   (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 a0 x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x49250) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros -> SEP LB. pose proof LOLE as LOLE'. unfold MEMCHR_ICPT_STACK in LOLE'.
        unfold MEMCHR_ICPT_STACK in MU1.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a0) as A0R; unfold inr64 in A0R.
        pose proof (bytes_at_bound _ _ _ _ B1) as LBd.
        assert (QH1 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (A + L + -1) - sha (A + L + -1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SH1 as SH. remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
        assert (SHhi : (A / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QB1 as QB1'. pose proof QB2 as QB2'.
        zstep. zstep.
        zstep. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
          zstep. zstep. zstep.
          zstep. call_lit region_is_poisoned_spec by (idtac;
            lazymatch goal with
            | |- map_cells _ => repeat (split; [assumption|]); assumption
            | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
            | |- mem_inv _ _ => eassumption
            | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IR
            | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ng, lastb; subst sbs; split; [exact NG| split; [exact SH| exact LB]]
            | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
            end).
          zstep. zstep.
          zstep. if_cases K4; zify_cond K4. all: try (deadK K4).
          subst sbs. eapply mr_exit; try eassumption.
        - (* [comment removed for export] *)
          assert (HS1 : (0 <= Z.shiftr A 3 <= A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (A + L + -1) 3 <= A + L - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 11 zstep.
          pose proof (qc_read _ _ _ QB1' ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2' ltac:(lia)) as RD2.
          zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + subst sbs.
            assert (LBR : (0 <= lastb < 128)%Z) by (hs_lbr lastb).
            pose proof (u8ro_read rsegs _ (A / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (A + L + -1) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (A + L + -1) lastb) by
              (first [destruct LB as [LB0|LB1]; [left; exact LB0| right; replace (A + L + -1)%Z with (A + L - 1)%Z by (clear - LB1; lia); (clear - LB1; lia)] | lia]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + A / 8)%Z). set (sl := (2147450880 + (A + L + -1) / 8)%Z).
            assert (ESF : (sf = A / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ng)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl.
            zstep. if_cases K8; zify_cond K8.
            * eapply mr_slow_end; eassumption.
            * eapply mr_slow_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + subst sbs. eapply mr_exit; try eassumption.
      Qed.
    End Phase.
  End Facts.
End S.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma memchr_icpt_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  let A := bv_unsigned a0 in let c := ((bv_unsigned a1) mod 256)%Z in let n := bv_unsigned a2 in
  bytes_at rsegs m A buf ->
  memchr_ok A c n buf ->
  mem_inv rsegs m -> memchr_icpt_cells m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + MEMCHR_ICPT_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A)%Z ->
  (0 < A)%Z -> (n < 2^32)%Z ->
  (memchr_len c n buf = 0%Z \/ range_ok m A (memchr_len c n buf)) ->
  evt rsegs (memchr_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 c n buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47a14) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. cbv zeta. intros B OK MI CELLS ST LOLE CEIL SEP APOS N32 RNG.
  pose proof LOLE as LOLE'. unfold MEMCHR_ICPT_STACK in LOLE'.
  destruct CELLS as (CI & Creal & MC). unfold asan_inited_cell in CI. pose proof MC as MC'. open_map_cells MC'. clear MC.
  pose proof (munch_refl [(bv_unsigned sp - MEMCHR_ICPT_STACK, bv_unsigned sp)]%Z m) as MU. unfold MEMCHR_ICPT_STACK in MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
  pose proof (zr_word a2) as A2R; unfold inr64 in A2R. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
  pose proof (bytes_at_bound _ _ _ _ B) as LB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (Z.mod_pos_bound (bv_unsigned a1) 256 ltac:(lia)) as CB.
  set (c := ((bv_unsigned a1) mod 256)%Z) in *.
  set (L := memchr_len c (bv_unsigned a2) buf) in *.
  pose proof (memchr_len_bound c (bv_unsigned a2) buf ltac:(lia)) as LBND. fold L in LBND.
  (* [comment removed for export] *)
  assert (RES : (memchr_res (bv_unsigned a0) c (bv_unsigned a2) buf = 0%Z /\ L = bv_unsigned a2)
              \/ (exists i, memchr_res (bv_unsigned a0) c (bv_unsigned a2) buf = bv_unsigned a0 + Z.of_nat i /\ L = Z.of_nat i + 1
                             /\ Z.of_nat i < Z.of_nat (length buf))%Z).
  { unfold memchr_res. subst L. unfold memchr_len. destruct (find_byte c (firstn (Z.to_nat (bv_unsigned a2)) buf)) as [i|] eqn:E.
    - right. exists i. destruct (find_byte_Some _ _ _ E) as (Hi & _ & _). rewrite firstn_length in Hi. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - left. split; reflexivity. }
  destruct (Z.eq_dec L 0) as [L0 | LNZ].
  { (* [comment removed for export] *)
    destruct RES as [[RV HL] | [i [RV [HL Hi]]]]; [| exfalso; lia].
    zstep. (* [comment removed for export] *)
    freeze B; freeze CI; freeze Creal; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb; freeze Gme; freeze Cme; freeze Ghe; freeze Che.
    pose proof (munch_refl [(bv_unsigned sp - 2128, bv_unsigned sp)]%Z m) as MUp.
    carve_frame 56%nat ST. carve_frame 2072%nat ST.
    do 10 zstep.
    thaw B MUp WM; thaw CI MUp WM; thaw Creal MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM; thaw Gmb MUp WM; thaw Cmb MUp WM;
    thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM. clear MUp.
    zstep. zstep. zstep.
    zstep. call asan_inited_spec. 1:{ exact CI. } 1:{ eassumption. }
    zstep. if_cases K0; zify_cond K0. { deadK K0. }
    zstep. call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => exact CI
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. call memchr_spec. 1:{ exact B. } 1:{ exact OK. } 1:{ eassumption. }
    fold c.
    zstep. if_cases K1; zify_cond K1. { deadK K1. }
    rewrite RV.
    zstep. if_cases K2; zify_cond K2. all: try (deadK K2).
    zstep. zstep. zstep. rewrite zb_lxor_ones by lia.
    zstep. if_cases K3; zify_cond K3. { exfalso. lia. }
    zstep. zstep.
    zstep. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite <- HL, L0 in K4. clear -K4; try pose proof alloc_ceiling_val. cbv in K4. first [lia | discriminate]. }
    zstep. if_cases K5; zify_cond K5. { exfalso. lia. }
    zstep. eapply mr_exit; try eassumption; try reflexivity; rewrite ?RV; try reflexivity; try lia. }
  (* [comment removed for export] *)
  destruct RNG as [L0 | RA]; [exfalso; lia|].
  destruct RA as (IR & SOK & QW1 & QW2).
  assert (AF : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + L + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
  replace (bv_unsigned a0 + L - 1)%Z with (bv_unsigned a0 + L + -1)%Z in QW2 by lia.
  destruct (mapped8_le8 _ _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
  destruct (mapped8_le8 _ _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
  assert (QH1 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH2 : (sha (bv_unsigned a0 + L + -1) - sha (bv_unsigned a0 + L + -1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  destruct SOK as (ng & lastb & NG & SH & LBl).
  remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
  assert (SHhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
  { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  freeze SH; freeze QB1; freeze QB2.
    zstep. (* [comment removed for export] *)
    freeze B; freeze CI; freeze Creal; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb; freeze Gme; freeze Cme; freeze Ghe; freeze Che.
    pose proof (munch_refl [(bv_unsigned sp - 2128, bv_unsigned sp)]%Z m) as MUp.
    carve_frame 56%nat ST. carve_frame 2072%nat ST.
    do 10 zstep.
    thaw B MUp WM; thaw CI MUp WM; thaw Creal MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM; thaw Gmb MUp WM; thaw Cmb MUp WM;
    thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM; thaw SH MUp WM; thaw QB1 MUp WM; thaw QB2 MUp WM. clear MUp.
    zstep. zstep. zstep.
    zstep. call asan_inited_spec. 1:{ exact CI. } 1:{ eassumption. }
    zstep. if_cases K0; zify_cond K0. { deadK K0. }
    zstep. call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => exact CI
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. call memchr_spec. 1:{ exact B. } 1:{ exact OK. } 1:{ eassumption. }
    fold c.
    zstep. if_cases K1; zify_cond K1. { deadK K1. }
    subst sbs.
    (* [comment removed for export] *)
    destruct RES as [[RV HL] | [i [RV [HL Hi]]]]; rewrite RV.
    - zstep. if_cases K2; zify_cond K2. all: try (deadK K2).
      zstep. zstep. zstep. rewrite zb_lxor_ones by lia.
      zstep. if_cases K3; zify_cond K3. { exfalso. lia. }
      eapply mr_phase; try eassumption; try reflexivity; try lia.
      all: first [rewrite RV; reflexivity | rewrite HL; symmetry; apply Z_to_bv_bv_unsigned | idtac].
    - zstep. if_cases K2; zify_cond K2. 2:{ deadK K2. }
      zstep. zstep.
      zstep. rewrite zb_lxor_ones by lia. zstep. zstep.
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
      eapply mr_phase; try eassumption; try reflexivity; try lia.
      all: first [rewrite RV; reflexivity | f_equal; lia | idtac].
Qed.

End CEIL.
End AIcpa3z.


Module AIcpesd.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpa3z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac icpt_consts_in H ::= unfold MEMCHR_ICPT_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].

Definition mstrnlen_entry : Z := 0xa2b38.
Definition MSTRNLEN_STACK : Z := 2240.

Definition mstrnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - MSTRNLEN_STACK, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) buf.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma mstrnlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  let A := bv_unsigned a0 in let n := bv_unsigned a1 in
  bytes_at rsegs m A buf ->
  memchr_ok A 0 n buf ->
  mem_inv rsegs m -> memchr_icpt_cells m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + MSTRNLEN_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A)%Z ->
  (0 < A)%Z -> (n < 2^32)%Z ->
  (memchr_len 0 n buf = 0%Z \/ range_ok m A (memchr_len 0 n buf)) ->
  evt rsegs (mstrnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 n buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa2b38) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. cbv zeta. intros B OK MI CELLS ST LOLE CEIL SEP APOS N32 RNG.
  unfold MSTRNLEN_STACK in LOLE.
  pose proof CELLS as CELLS'. (first [ dand3 CELLS' as CI Creal MC | destruct CELLS' as (CI & Creal & MC) ]). unfold asan_inited_cell in CI. open_map_cells MC.
  pose proof (munch_refl [(bv_unsigned sp - MSTRNLEN_STACK, bv_unsigned sp)]%Z m) as MU. unfold MSTRNLEN_STACK in MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
  pose proof (bytes_at_bound _ _ _ _ B) as LB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  assert (RNGX : exists (ng : nat) (lastb : Z) (w1 w2 : word),
    memchr_len 0 (bv_unsigned a1) buf = 0%Z \/
    (inmem_range (bv_unsigned a0) (memchr_len 0 (bv_unsigned a1) buf) /\
     ((bv_unsigned a0 + memchr_len 0 (bv_unsigned a1) buf - 1) / 8 - bv_unsigned a0 / 8 = Z.of_nat ng)%Z /\
     (lastb = 0 \/ ((bv_unsigned a0 + memchr_len 0 (bv_unsigned a1) buf - 1) mod 8 < lastb <= 7))%Z /\
     bytes_at rsegs m (bv_unsigned a0 / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]) /\
     bytes_at rsegs m (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8) (le8 w1) /\
     bytes_at rsegs m (sha (bv_unsigned a0 + memchr_len 0 (bv_unsigned a1) buf + -1) - sha (bv_unsigned a0 + memchr_len 0 (bv_unsigned a1) buf + -1) mod 8) (le8 w2))).
  { destruct RNG as [L0 | (IR & (ng & lastb & NG & SH & LBl) & QW1 & QW2)].
    - exists 0%nat, 0%Z, (Z_to_bv 64 0), (Z_to_bv 64 0). left. exact L0.
    - assert (AF : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + memchr_len 0 (bv_unsigned a1) buf + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
      pose proof (memchr_len_bound 0 (bv_unsigned a1) buf ltac:(lia)) as LBND.
      destruct (mapped8_le8 _ _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
      destruct (mapped8_le8 _ _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
      exists ng, lastb, w1, w2. right.
      replace (bv_unsigned a0 + memchr_len 0 (bv_unsigned a1) buf + -1)%Z with (bv_unsigned a0 + memchr_len 0 (bv_unsigned a1) buf - 1)%Z by lia.
      repeat (split; [assumption|]). assumption. }
  clear RNG. (first [ dex4 RNGX as ng lastb w1 w2 | dand5 RNGX as ng lastb w1 w2 RNGX | destruct RNGX as (ng & lastb & w1 & w2 & RNGX) ]).
  set (L := memchr_len 0 (bv_unsigned a1) buf) in *.
  pose proof (memchr_len_bound 0 (bv_unsigned a1) buf ltac:(lia)) as LBND. fold L in LBND.
  assert (RES : (memchr_res (bv_unsigned a0) 0 (bv_unsigned a1) buf = 0%Z /\ strnlen_res (bv_unsigned a1) buf = bv_unsigned a1)
              \/ (exists i, memchr_res (bv_unsigned a0) 0 (bv_unsigned a1) buf = bv_unsigned a0 + Z.of_nat i
                             /\ strnlen_res (bv_unsigned a1) buf = Z.of_nat i /\ Z.of_nat i < Z.of_nat (length buf))%Z).
  { unfold memchr_res, strnlen_res. destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:E.
    - right. exists i. (first [ pose proof ((find_byte_Some _ _ _ E)) as dR_3; dand3 dR_3 as Hi _ _ | destruct (find_byte_Some _ _ _ E) as (Hi & _ & _) ]). rewrite firstn_length in Hi. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - left. split; reflexivity. }
  destruct RNGX as [L0 | (IR & NG & LBl & SH & QB1 & QB2)].
  - (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 8 zstep.
    zstep. call_icpt memchr_icpt_spec by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ _ _ => exact B
      | |- memchr_ok _ _ _ _ => rewrite ?unsigned_lit by lia; exact OK
      | |- mem_inv _ _ => eassumption
      | |- memchr_icpt_cells _ => unfold memchr_icpt_cells, asan_inited_cell, map_cells; repeat (split; [assumption|]); assumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- (_ = 0%Z \/ _) => left; rewrite ?unsigned_lit by lia; exact L0
      | |- _ => unfold MEMCHR_ICPT_STACK; rewrite ?unsigned_lit by lia; lia
      end).
    change ((0 mod 256)%Z) with 0%Z.
    destruct RES as [[RV SV] | [i (RV & SV & Hi)]]; rewrite RV.
    + zstep. if_cases K; zify_cond K. all: try (exfalso; lia).
      do 5 zstep. zstep.
      lazymatch goal with ST' : stk rsegs _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp) end.
      unfold mstrnlen_post. rewrite SV. replace a1 with (Z_to_bv 64 (bv_unsigned a1)) at 1 by (apply Z_to_bv_bv_unsigned). finish.
    + zstep. if_cases K; zify_cond K. all: try (exfalso; lia).
      zstep. replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (Z.of_nat i) by lia.
      do 5 zstep. zstep.
      lazymatch goal with ST' : stk rsegs _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp) end.
      unfold mstrnlen_post. rewrite SV. finish.
  - assert (AF : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + L + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
    pose proof (bytes_at_bound _ _ _ _ QB1) as Q1. pose proof (bytes_at_bound _ _ _ _ QB2) as Q2. rewrite length_le8 in Q1, Q2.
    assert (QH1 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH2 : (sha (bv_unsigned a0 + L + -1) - sha (bv_unsigned a0 + L + -1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
    assert (SHhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
    { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
    carve_frame 32%nat ST.
    do 8 zstep.
    subst sbs.
    zstep. call_icpt memchr_icpt_spec by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ _ _ => exact B
      | |- memchr_ok _ _ _ _ => rewrite ?unsigned_lit by lia; exact OK
      | |- mem_inv _ _ => eassumption
      | |- memchr_icpt_cells _ => unfold memchr_icpt_cells, asan_inited_cell, map_cells; repeat (split; [assumption|]); assumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- (_ = 0%Z \/ _) => rewrite ?unsigned_lit by lia; change ((0 mod 256)%Z) with 0%Z;
             destruct (Z.eq_dec L 0) as [E0|NZ];
             [ left; exact E0
             | right; eapply (range_ok_repack _ _ _ ng lastb w1 w2); try eassumption; lia ]
      | |- _ => unfold MEMCHR_ICPT_STACK; rewrite ?unsigned_lit by lia; lia
      end).
    all: try (change ((0 mod 256)%Z) with 0%Z).
    all: destruct RES as [[RV SV] | [i (RV & SV & Hi)]]; rewrite ?RV.
    + zstep. if_cases K; zify_cond K. all: try (exfalso; lia).
      do 5 zstep. zstep.
      lazymatch goal with ST' : stk rsegs _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp) end.
      unfold mstrnlen_post. rewrite SV. replace a1 with (Z_to_bv 64 (bv_unsigned a1)) at 1 by (apply Z_to_bv_bv_unsigned). finish.
    + zstep. if_cases K; zify_cond K. all: try (exfalso; lia).
      zstep. replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (Z.of_nat i) by lia.
      do 5 zstep. zstep.
      lazymatch goal with ST' : stk rsegs _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp) end.
      unfold mstrnlen_post. rewrite SV. finish.
Qed.

End CEIL.
End AIcpesd.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpesd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac icpt_consts_in H ::= unfold MSTRNLEN_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].

Definition strnlen_icpt_entry : Z := 0x47a00.
Definition STRNLEN_ICPT_STACK : Z := 4384.

Definition strnlen_icpt_cells (m : word -> option byte) : Prop :=
     asan_inited_cell m                                          (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xaafe0 [C8 (Z_to_bv 64 0xa2b38)]      (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa9180 [C8 (Z_to_bv 64 0x146ee8)]      (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x146fe3 [C1 (Z_to_bv 8 1)]              (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xaaef0 [C8 (Z_to_bv 64 0xa20c8)]      (* [comment removed for export] *)
  /\ map_cells m.

(* [comment removed for export] *)

Definition strnlen_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - STRNLEN_ICPT_STACK, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) buf.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte) (lo n v L : Z).
  Notation A := (bv_unsigned a0).
  Hypothesis HV : v = strnlen_res n buf.
  Hypothesis HL : L = memchr_len 0 n buf.
  Notation POST := (strnlen_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 n buf lo m).
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2144) [CB 2080 fjunk]).
  Hypothesis LOLE : (lo + STRNLEN_ICPT_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis L32 : (0 <= L < 2^32)%Z.
  Hypothesis VR : (0 <= v < 2^64)%Z.
  Notation SEPt := ((A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).

  (* [comment removed for export] *)
  #[using="LOLE HV"] Lemma sn_exit : forall m1 fjunk x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    mem_inv rsegs m1 -> munch [(bv_unsigned sp - STRNLEN_ICPT_STACK, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -2144) -> FRAME m1 -> FRAMEB m1 fjunk -> bytes_at rsegs m1 A buf ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
               (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x47de8) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros MI1 MU1 WM1 ST1 FR1 FRB1 B1. unfold STRNLEN_ICPT_STACK in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    do 11 zstep.
    release_frame FRB1 ST1 (bv_unsigned sp + -64)%Z. release_frame FR1 ST1 (bv_unsigned sp). rewrite HV. finish.
  Qed.

  Section Facts.
    Variables (ng : nat) (lastb : Z) (w1 w2 : word).
    Notation LBt := ((lastb = 0 \/ ((A + L - 1) mod 8 < lastb <= 7))%Z) (only parsing).
    Hypothesis AF : (0 <= A /\ A + L + 8 <= 0x800000000000)%Z.
    Hypothesis IR : inmem_range A L.
    Hypothesis NG : ((A + L - 1) / 8 - A / 8 = Z.of_nat ng)%Z.
    Hypothesis L1 : (1 <= L)%Z.

    Section Phase.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(bv_unsigned sp - STRNLEN_ICPT_STACK, bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2144).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis B1 : bytes_at rsegs m1 A buf.
      Hypothesis Gsh : ro_cells rsegs m1 0xa9190 [C8 (Z_to_bv 64 0xb53b8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb53b8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa9198 [C8 (Z_to_bv 64 0xb60a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb60a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa91a0 [C8 (Z_to_bv 64 0xb60b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb60b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa91a8 [C8 (Z_to_bv 64 0xb60a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb60a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SH1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]).
      Hypothesis QB1 : bytes_at rsegs m1 (sha A - sha A mod 8) (le8 w1).
      Hypothesis QB2 : bytes_at rsegs m1 (sha (A + L + -1) - sha (A + L + -1) mod 8) (le8 w2).

      Section Slow.
        Variables (sf sl : Z) (x1 x5 x6 x7 x9 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word).
        Hypothesis SEP : SEPt.
        Hypothesis ESF : (sf = A / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ng)%Z.
        Notation AT pc x11 x13 x14 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp (Z_to_bv 64 L)
                   (Z_to_bv 64 v) x11 (Z_to_bv 64 sl) x13 x14 x15 x16 x17 a0 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        #[using="B1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk ng LOLE HV"] Lemma sn_slow_end : forall x11 x14, evt rsegs POST (AT 0x47ecc x11 (Z_to_bv 64 0) x14).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
          zstep. zstep. if_cases K; zify_cond K. all: try (deadK K).
          eapply sn_exit; try eassumption.
        Qed.

        #[using="ESL ESF SH1 B1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk L1 AF lastb LOLE HV"] Lemma sn_slow_loop : forall (cc : nat) (j : Z) x11 x14,
          Z.to_nat (Z.of_nat ng - j) = cc -> (0 <= j < Z.of_nat ng)%Z -> x11 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x47ebc x11 (Z_to_bv 64 0) x14).
        Proof.
          induction cc as [|cc IH]; intros j x11 x14 Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SH1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (A / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SH1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ng lastb (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ng)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep.
          zstep. if_cases K; zify_cond K.
          - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
          - apply sn_slow_end.
        Qed.
      End Slow.

      (* [comment removed for export] *)
      #[using="QB2 QB1 SH1 Che Ghe Cme Gme Cmb Gmb Csh Gsh B1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk L1 NG IR AF w2 w1 ng L32 CEIL LOLE HV Clg"] Lemma sn_phase : forall (xs1 xa0 : word) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
        xs1 = Z_to_bv 64 L -> xa0 = Z_to_bv 64 v -> SEPt -> LBt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp xs1
                   xa0 x11 x12 x13 x14 x15 x16 x17 a0 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x47da0) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros -> -> SEP LB. pose proof LOLE as LOLE'. unfold STRNLEN_ICPT_STACK in LOLE'.
        unfold STRNLEN_ICPT_STACK in MU1.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a0) as A0R; unfold inr64 in A0R.
        pose proof (bytes_at_bound _ _ _ _ B1) as LBd.
        assert (QH1 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (A + L + -1) - sha (A + L + -1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SH1 as SH. remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
        assert (SHhi : (A / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QB1 as QB1'. pose proof QB2 as QB2'.
        zstep. zstep.
        zstep. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
          zstep. zstep. zstep.
          zstep. call_lit region_is_poisoned_spec by (idtac;
            lazymatch goal with
            | |- map_cells _ => repeat (split; [assumption|]); assumption
            | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
            | |- mem_inv _ _ => eassumption
            | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IR
            | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ng, lastb; subst sbs; split; [exact NG| split; [exact SH| exact LB]]
            | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
            end).
          zstep. zstep.
          zstep. if_cases K4; zify_cond K4. all: try (deadK K4).
          subst sbs. eapply sn_exit; try eassumption.
        - (* [comment removed for export] *)
          assert (HS1 : (0 <= Z.shiftr A 3 <= A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (A + L + -1) 3 <= A + L - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 11 zstep.
          pose proof (qc_read _ _ _ QB1' ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2' ltac:(lia)) as RD2.
          zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + subst sbs.
            assert (LBR : (0 <= lastb < 128)%Z) by lia.
            pose proof (u8ro_read rsegs _ (A / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (A + L + -1) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (A + L + -1) lastb) by
              (first [lia | destruct LB as [LB0|LB1]; [left; exact LB0| right; replace (A + L + -1)%Z with (A + L - 1)%Z by lia; lia]]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + A / 8)%Z). set (sl := (2147450880 + (A + L + -1) / 8)%Z).
            assert (ESF : (sf = A / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ng)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl.
            zstep. if_cases K8; zify_cond K8.
            * eapply sn_slow_end; eassumption.
            * eapply sn_slow_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + subst sbs. eapply sn_exit; try eassumption.
      Qed.
    End Phase.
  End Facts.
End S.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma strnlen_icpt_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  let A := bv_unsigned a0 in let n := bv_unsigned a1 in
  bytes_at rsegs m A buf ->
  memchr_ok A 0 n buf ->
  mem_inv rsegs m -> strnlen_icpt_cells m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + STRNLEN_ICPT_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A)%Z ->
  (0 < A)%Z -> (n < 2^32)%Z ->
  (memchr_len 0 n buf = 0%Z \/ range_ok m A (memchr_len 0 n buf)) ->
  evt rsegs (strnlen_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 n buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47a00) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. cbv zeta. intros B OK MI CELLS ST LOLE CEIL SEP APOS N32 RNG.
  pose proof LOLE as LOLE'. unfold STRNLEN_ICPT_STACK in LOLE'.
  (first [ dand6 CELLS as CI Creal Gcf Cisc Crm MC | destruct CELLS as (CI & Creal & Gcf & Cisc & Crm & MC) ]). unfold asan_inited_cell in CI. pose proof MC as MC'. open_map_cells MC'. clear MC.
  pose proof (munch_refl [(bv_unsigned sp - STRNLEN_ICPT_STACK, bv_unsigned sp)]%Z m) as MU. unfold STRNLEN_ICPT_STACK in MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
  pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
  pose proof (bytes_at_bound _ _ _ _ B) as LB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  set (L := memchr_len 0 (bv_unsigned a1) buf) in *.
  pose proof (memchr_len_bound 0 (bv_unsigned a1) buf ltac:(lia)) as LBND. fold L in LBND.
  (* [comment removed for export] *)
  assert (RES : (strnlen_res (bv_unsigned a1) buf = bv_unsigned a1 /\ L = bv_unsigned a1)
              \/ (exists i, strnlen_res (bv_unsigned a1) buf = Z.of_nat i /\ L = Z.of_nat i + 1
                             /\ Z.of_nat i < Z.of_nat (length buf) /\ Z.of_nat i + 1 <= bv_unsigned a1)%Z).
  { unfold strnlen_res. subst L. unfold memchr_len. destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:E.
    - right. exists i. (first [ pose proof ((find_byte_Some _ _ _ E)) as dR_2; dand3 dR_2 as Hi _ _ | destruct (find_byte_Some _ _ _ E) as (Hi & _ & _) ]). rewrite firstn_length in Hi. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - left. split; reflexivity. }
  (* [comment removed for export] *)
  assert (RNGX : exists (ng : nat) (lastb : Z) (w1 w2 : word),
    L = 0%Z \/
    (inmem_range (bv_unsigned a0) L /\
     ((bv_unsigned a0 + L - 1) / 8 - bv_unsigned a0 / 8 = Z.of_nat ng)%Z /\
     (lastb = 0 \/ ((bv_unsigned a0 + L - 1) mod 8 < lastb <= 7))%Z /\
     bytes_at rsegs m (bv_unsigned a0 / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]) /\
     bytes_at rsegs m (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8) (le8 w1) /\
     bytes_at rsegs m (sha (bv_unsigned a0 + L + -1) - sha (bv_unsigned a0 + L + -1) mod 8) (le8 w2))).
  { destruct RNG as [L0 | (IR & (ng & lastb & NG & SH & LBl) & QW1 & QW2)].
    - exists 0%nat, 0%Z, (Z_to_bv 64 0), (Z_to_bv 64 0). left. exact L0.
    - assert (AF : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + L + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
      destruct (mapped8_le8 _ _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
      destruct (mapped8_le8 _ _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
      exists ng, lastb, w1, w2. right.
      replace (bv_unsigned a0 + L + -1)%Z with (bv_unsigned a0 + L - 1)%Z by lia.
      repeat (split; [assumption|]). assumption. }
  clear RNG. (first [ dex4 RNGX as ng lastb w1 w2 | dand5 RNGX as ng lastb w1 w2 RNGX | destruct RNGX as (ng & lastb & w1 & w2 & RNGX) ]).
  destruct (Z.eq_dec L 0) as [L0 | LNZ].
  { (* [comment removed for export] *)
    destruct RES as [[RV HL] | [i [RV [HL [Hi Hin]]]]]; [| exfalso; lia].
    assert (N0 : bv_unsigned a1 = 0%Z) by lia.
    zstep. (* [comment removed for export] *)
    freeze B; freeze CI; freeze Creal; freeze Gcf; freeze Cisc; freeze Crm; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb; freeze Gme; freeze Cme; freeze Ghe; freeze Che.
    pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m) as MUp.
    carve_frame 64%nat ST. carve_frame 2080%nat ST.
    do 11 zstep.
    thaw B MUp WM; thaw CI MUp WM; thaw Creal MUp WM; thaw Gcf MUp WM; thaw Cisc MUp WM; thaw Crm MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM;
    thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM. clear MUp.
    zstep. zstep.
    zstep. call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => exact CI
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zstep. zstep. zstep. zstep. zstep.
    zstep. call_icpt mstrnlen_spec by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ _ _ => exact B
      | |- memchr_ok _ _ _ _ => rewrite ?unsigned_lit by lia; exact OK
      | |- mem_inv _ _ => eassumption
      | |- memchr_icpt_cells _ => unfold memchr_icpt_cells, asan_inited_cell, map_cells; repeat (split; [assumption|]); assumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- (_ = 0%Z \/ _) => left; rewrite ?unsigned_lit by lia; exact L0
      | |- _ => unfold MSTRNLEN_STACK; rewrite ?unsigned_lit by lia; lia
      end).
    rewrite RV, N0. clear RNGX.
    zstep. if_cases K1; zify_cond K1. { deadK K1. }
    zstep. zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
    zstep. if_cases Kf; zify_cond Kf. { deadK Kf. }
    zstep.
    zstep. if_cases K2; zify_cond K2. all: try (exfalso; lia).
    zstep. zstep. rewrite zb_lxor_ones by lia. zstep. zstep.
    zstep. if_cases K3; zify_cond K3. all: try (exfalso; lia).
    zstep. zstep.
    zstep. if_cases K4; zify_cond K4. all: try (exfalso; rewrite N0 in K4; try (generalize alloc_ceiling_val); clear -K4; try pose proof alloc_ceiling_val; cbv in K4; first [lia | discriminate]).
    zstep. if_cases K5; zify_cond K5. all: try (exfalso; lia).
    zstep. eapply sn_exit; try eassumption; try reflexivity; rewrite ?RV, ?N0; try reflexivity; try lia. }
  (* [comment removed for export] *)
  destruct RNGX as [L0 | (IR & NG & LBl & SH & QB1 & QB2)]; [exfalso; lia|].
  assert (AF : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + L + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
  assert (QH1 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH2 : (sha (bv_unsigned a0 + L + -1) - sha (bv_unsigned a0 + L + -1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
  assert (SHhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
  { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  assert (VR : (0 <= strnlen_res (bv_unsigned a1) buf < 2^64)%Z) by (destruct RES as [[RV HL] | [i [RV [HL [Hi Hin]]]]]; rewrite RV; lia).
  freeze SH; freeze QB1; freeze QB2.
  zstep. (* [comment removed for export] *)
  freeze B; freeze CI; freeze Creal; freeze Gcf; freeze Cisc; freeze Crm; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb; freeze Gme; freeze Cme; freeze Ghe; freeze Che.
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m) as MUp.
  carve_frame 64%nat ST. carve_frame 2080%nat ST.
  do 11 zstep.
  thaw B MUp WM; thaw CI MUp WM; thaw Creal MUp WM; thaw Gcf MUp WM; thaw Cisc MUp WM; thaw Crm MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM;
  thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM;
  thaw SH MUp WM; thaw QB1 MUp WM; thaw QB2 MUp WM. clear MUp.
  zstep. zstep.
  zstep. call_lit tryinit_spec by (idtac;
    lazymatch goal with
    | |- asan_inited_cell _ => exact CI
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
    | |- mem_inv _ _ => eassumption
    | |- _ => rewrite ?unsigned_lit by lia; lia
    end).
  zstep. zstep. zstep. zstep. zstep.
  zstep. call_icpt mstrnlen_spec by (idtac;
    lazymatch goal with
    | |- bytes_at _ _ _ _ => exact B
    | |- memchr_ok _ _ _ _ => rewrite ?unsigned_lit by lia; exact OK
    | |- mem_inv _ _ => eassumption
    | |- memchr_icpt_cells _ => unfold memchr_icpt_cells, asan_inited_cell, map_cells; repeat (split; [assumption|]); assumption
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
    | |- (_ = 0%Z \/ _) => right; rewrite ?unsigned_lit by lia; subst sbs;
           eapply (range_ok_repack _ _ _ ng lastb w1 w2); try eassumption; lia
    | |- _ => unfold MSTRNLEN_STACK; rewrite ?unsigned_lit by lia; lia
    end).
  zstep. if_cases K1; zify_cond K1. { deadK K1. }
  zstep. zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
  zstep. if_cases Kf; zify_cond Kf. { deadK Kf. }
  zstep.
  subst sbs.
  (* [comment removed for export] *)
  destruct RES as [[RV HL] | [i [RV [HL [Hi Hin]]]]]; rewrite RV in *.
  - (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2. all: try (exfalso; lia).
    zstep. zstep. rewrite zb_lxor_ones by lia. zstep. zstep.
    zstep. if_cases K3; zify_cond K3. all: try (exfalso; lia).
    eapply sn_phase with (v := bv_unsigned a1) (L := L); try eassumption; try reflexivity; try lia.
    all: first [rewrite HL; symmetry; apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned | idtac].
  - (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      assert (HLn : L = bv_unsigned a1) by lia.
      zstep. zstep. rewrite zb_lxor_ones by lia. zstep. zstep.
      zstep. if_cases K3; zify_cond K3. all: try (exfalso; lia).
      eapply sn_phase with (v := Z.of_nat i) (L := L); try eassumption; try reflexivity; try lia.
      all: first [rewrite HLn; symmetry; apply Z_to_bv_bv_unsigned | idtac].
    + zstep. rewrite zb_lxor_ones by lia. zstep. zstep.
      zstep. if_cases K3; zify_cond K3. all: try (exfalso; lia).
      eapply sn_phase with (v := Z.of_nat i) (L := L); try eassumption; try reflexivity; try lia.
      all: first [rewrite HL; reflexivity | f_equal; lia | idtac].
Qed.

End CEIL.

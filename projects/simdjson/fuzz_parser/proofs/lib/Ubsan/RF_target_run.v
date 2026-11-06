(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree Startup_kit STRW_tac Amo_tac Keeps F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg F_syscalls F_memcpy StdioFiles F_printf_iface Stdio_iface Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface PU_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Adapter HarnessP PState ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Definition hidden (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Ltac unhide H := unfold hidden in H.
Ltac clia := atop_facts; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rcT : runConstT}.
Lemma land3_range : forall c, 0 <= c -> 0 <= Z.land c 3 <= 3.
Proof.
  intros c Hc. split; [apply Z.land_nonneg; lia|].
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (Z.ones 2) with 3. pose proof (Z.mod_pos_bound c 4 ltac:(lia)). change (2^2) with 4. lia.
Qed.

Lemma b2z_range : forall b, 0 <= Z.b2z b <= 1.
Proof. intros [|]; cbn; lia. Qed.

Lemma snez_norm : forall rc, -2^63 < rc < 2^63 -> Z.b2z (0 <? Z.land rc 18446744073709551615) = (if rc =? 0 then 0 else 1).
Proof.
  intros rc Hr. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  destruct (Z.eqb_spec rc 0) as [->|NE]; [reflexivity|].
  destruct (Z.ltb_spec0 0 (rc mod 2^64)) as [L|G]; [reflexivity|]. exfalso.
  pose proof (Z.mod_pos_bound rc (2^64) ltac:(lia)). assert (E : rc mod 2^64 = 0) by lia.
  apply Znumtheory.Zmod_divide in E; [| lia]. destruct E as [q E]. assert (q = 0) by lia. subst q. lia.
Qed.

Lemma Forall_skipn' : forall {A} (P : A -> Prop) n (l : list A), Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n. induction n as [|n IH]; intros l H; [exact H|]. destruct l as [|x l]; cbn; [constructor|].
  inversion H; subst. apply IH. assumption.
Qed.

Lemma status_norm : forall b, 0 <= b <= 1 ->
  Z.land (Z.b2z (Z.land b 18446744073709551615 =? 0) + -1) 78 = (if b =? 0 then 0 else 78).
Proof.
  intros b Hb. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  destruct (Z.eqb_spec b 0) as [->|NE]; [reflexivity|]. cbn [Z.b2z]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma magree_of_hpres : forall LB SP m m', harness_pres LB SP m m' ->
  magree usegs (fun a => rclient_addr LB SP a /\ outside client_wr a) m m'.
Proof. intros LB SP m m' H a Ha [Hc Ho]. exact (H a Ha Hc Ho). Qed.
Lemma rin_pstdout_cw : forall a, ~ rin_ivs pstdout_ivs a -> outside client_wr a.
Proof. intros a H. unfold pstdout_ivs, client_wr, PINIT_FLAG, PNEWH in *. cbn in *. lia. Qed.
Ltac ocw := unfold client_wr; cbn [outside fst snd]; lia.

Lemma patx_addr_range : forall a, patx_addr a -> 0xb1e28 <= a < 0xb1f50.
Proof. intros a Ha. unfold patx_addr in Ha. lia. Qed.
Lemma pincb_addr_range : forall a, pincb_addr a -> a = 0x911b4.
Proof. intros a Ha. unfold pincb_addr in Ha. lia. Qed.

Definition atexit1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xb1e28, 0xb2048)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ patexit_reg m'.

Lemma atexit1_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m 0xb2070 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  patexit_main m ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 0x26a80 ->
  lo <= bv_unsigned sp - 48 -> 0xb3000 <= lo ->
  evt usegs (atexit1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6c9a4) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST LIBC (HDR & TBL & A0C) MI -> LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0xb1e28, 0xb2048)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0x7a7f0.
  steps_to 0x6c9d4.
  steps_to 0x6c9f4.
  try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  steps_to 0x7aa78.
  steps_to 0x6ca48.
  do 6 astep.
  release_frame FR ST (bv_unsigned sp).
  astep. astep.
  unfold atexit1_post. apply evt_done.
  do 15 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  unfold patexit_reg, patx_table.
  repeat match goal with |- _ /\ _ => split end; hyp_by_addr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RUN.
  (* [comment removed for export] *)
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FUZZ : fuzz_oneU_stmt ProgP.fuzz_one.   (* [comment removed for export] *)
  Hypothesis EMIT : emit_printf_stmt ps_so set_so_ps.
  Hypothesis FWXO : fwritex_stdout_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem)
            (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (AB lo : Z)
            (sin : PState).   (* [comment removed for export] *)
  Notation cl0 := (ps_fa sin).
  Hypothesis INLB : In (p, A, cap) LB.
  Hypothesis FC : Forall (fun c => 0 <= c < 256) content.
  Hypothesis LC : zlength content <= cap.
  Hypothesis CAP : cap <= 2^26.
  Hypothesis L0 : 0 <= L.
  Hypothesis L6 : 6 + L <= zlength content.
  Hypothesis SPAB : bv_unsigned sp <= AB.
  Hypothesis ABB : AB <= 2^47.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : ATOP <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PTARGET_RUN_STACK.

  Notation usp := (bv_unsigned sp).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).

  (* [comment removed for export] *)
  Definition plen : Z := zlength content - 6 - L.
  Definition PAY : Z := A + 6 + L.
  Definition payload : list Z := skipn (Z.to_nat (6 + L)) content.
  Definition cfg : Z := if 0 <? L then znth content 2 else 0.
  Definition calls : Z := 1 + Z.land cfg 3.

  (* [comment removed for export] *)
  Definition LBT (own : option (bptr * Z)) : list block :=
    match own with None => LB | Some (q, D) => (q, D, plen) :: LB end.
  Definition dptr (own : option (bptr * Z)) : Z := match own with None => PEMPTY | Some (_, D) => D end.
  Definition oreg (own : option (bptr * Z)) : Z := match own with None => 0 | Some (_, D) => D end.
  Definition omodel (own : option (bptr * Z)) : option bptr := match own with None => None | Some (q, _) => Some q end.

  (* [comment removed for export] *)
  Definition FRAME (m : mem) : Prop :=
    exists jb : list byte, rw_cells usegs m (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition INV0 (own : option (bptr * Z)) (st : PState) (m : mem) : Prop :=
    FRAME m /\ bytes_at usegs m (dptr own) (zbytes payload)
    /\ (exists errv : word, rw_cells usegs m RERRNO [C4 errv])
    /\ mem_inv usegs m /\ stk usegs m lo (usp + -80) /\ rauxv_ok m AB
    /\ stdout_file m (ps_so st) /\ pdrv_pres LB usp m0 m
    /\ patexit_reg m /\ pincb 0 m.
  (* [comment removed for export] *)
  Definition CBOK (cb : list block) (st : PState) : Prop :=
    (cb = [] /\ ps_fa st = cl0) \/ (exists pc V, cl0 = None /\ cb = [(pc, V, 8)] /\ ps_fa st = Some pc).
  Definition INV (own : option (bptr * Z)) (st : PState) (m : mem) : Prop :=
    (exists cb, CBOK cb st /\ RHEAP st (cb ++ LBT own) m /\ client_static st (cb ++ LB) m) /\ INV0 own st m.

  Notation DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 rcw k b sm2 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (wz plen) (wz (dptr own)) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (oreg own)) rcw (wz PINIT_FLAG) (wz k) (wz b) sm2 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition SM2 : word := Z_to_bv 64 (0 + -2).
  Lemma SM2_unsigned : bv_unsigned SM2 = 18446744073709551614.
  Proof. reflexivity. Qed.
  Definition RUNST0 (own : option (bptr * Z)) (pc : Z) (k b : Z) (rcw : word) (st : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      ms = DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 rcw k b SM2 t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ INV own st m.
  Definition RUNST (own : option (bptr * Z)) (pc : Z) (k b : Z) (st : PState) (ms : machine_state) : Prop :=
    (exists rcw, RUNST0 own pc k b rcw st ms) /\ 0 <= b <= 1.

  (* [comment removed for export] *)
  Lemma facts : 0 <= plen /\ plen < 2^26 /\ zlength payload = plen /\ 0 <= cfg < 256 /\ 1 <= calls <= 4 /\ PAY = A + 6 + L.
  Proof.
    unfold calls, cfg, plen, payload, PAY. unfold zlength in *. rewrite length_skipn.
    assert (CF : 0 <= (if 0 <? L then znth content 2 else 0) < 256).
    { destruct (0 <? L); [|lia]. unfold znth. destruct (Z.ltb_spec 2 0); [lia|].
      assert (LT : (Z.to_nat 2 < length content)%nat) by lia.
      pose proof (proj1 (Forall_forall _ _) FC _ (nth_In content 0 LT)) as X. cbn beta in X. lia. }
    pose proof (land3_range (if 0 <? L then znth content 2 else 0) ltac:(lia)).
    repeat split; lia.
  Qed.

  Lemma LO' : lo <= usp - 80 - HARNESS_STACK.
  Proof. unfold PTARGET_RUN_STACK in LO. lia. Qed.


  (* [comment removed for export] *)
  Lemma trun_init : forall (Q : machine_state -> Prop) (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (cdt thr sec : byte) (tm1 : word),
    stk usegs m lo usp -> mem_inv usegs m -> trun_cells0 m ->
    rw_cells usegs m 0xb2070 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    (forall (m' : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        FRAME m' -> stk usegs m' lo (usp + -80) ->
        munch [(usp - 128, usp); (PINIT_FLAG, PINIT_FLAG + 1); (0xb1e28, 0xb2048)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
        patexit_reg m' -> pincb 0 m' ->
        evt usegs Q (MS (mkR x1 SPF gp tp x5 x6 x7 a3 a2 x10 x11 x12 x13 x14 x15 x16 x17
                              a1 a0 (wz PINIT_FLAG) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x26970) fc None m' (seg_rom usegs))) ->
    evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 PTARGET_RUN) fc None m (seg_rom usegs)).
  Proof.
    intros until tm1. intros ST MI TR LIBC K. pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    destruct TR as (PI & GFI & (AHDR & ATBL & AA0) & AINCB). unfold pincb in AINCB.
    unfold PINIT_FLAG, PGOT_FUZZ_INIT, PFUZZ_INIT, PNEWH, wz in *.
    pose proof (munch_refl [(usp - 128, usp); (0x911b0, 0x911b0 + 1); (0xb1e28, 0xb2048)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold PTARGET_RUN.
    zstep. carve_frame 80%nat ST.
    do 9 zstep.
    (* [comment removed for export] *)
    do 8 zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    (* [comment removed for export] *)
    do 5 zstep.
    call_sp atexit1_spec.
    all: try unname_sp.
    1: exact ST.
    1: exact LIBC.
    1: { unfold patexit_main, patx_table. repeat match goal with |- _ /\ _ => split end; assumption. }
    1: assumption.
    1: reflexivity.
    1: lia.
    1: lia.
    zstep. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. clear K1.
    zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; revert K2; clear; intros K2; rewrite ?unsigned_lit in K2 by lia; lia]. clear K2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end.
    - lazymatch goal with H : rw_cells usegs _ (usp + -80) _ |- _ => eexists; exact H end.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - unfold pincb. assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma block_facts : forall st cb own m, RHEAP st (cb ++ LBT own) m ->
    0 < A /\ A + cap <= ATOP /\ (A + cap <= 0x10000 \/ 0xb3000 <= A)
    /\ match own with None => True | Some (_, D) => 0 < D /\ D mod 16 = 0 /\ D + plen <= ATOP /\ (D + plen <= 0x10000 \/ 0xb3000 <= D) end.
  Proof.
    intros st cb own m P.
    assert (HB : In (p, A, cap) (cb ++ LBT own)) by (apply in_or_app; right; destruct own as [[q D]|]; [right|]; exact INLB).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P HB) as (B1 & B2 & B3 & B4 & B5). cbn in B1, B2, B3, B4, B5.
    split; [lia|]. split; [lia|]. split; [lia|].
    destruct own as [[q D]|]; [| exact I].
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ (q, D, plen) P ltac:(apply in_or_app; right; left; reflexivity)) as (C1 & C2 & C3 & C4 & C5). cbn in C1, C2, C3, C4, C5.
    pose proof facts. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pdrv_pres_of_heap_sub : forall LB' SP' m m',
    harness_pres LB' SP' m m' -> SP' <= usp -> (forall b, In b LB -> In b LB') -> pdrv_pres LB usp m m'.      (* [comment removed for export] *)
  Proof.
    intros LB' SP' m m' HP HS HL a Ha Hc Hx. apply HP; [exact Ha| | exact (rin_pstdout_cw a Hx)].
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right; exists b; split; [apply HL; exact Hb| exact Hr]].
  Qed.
  Lemma pdrv_pres_of_munch : forall m m' W,
    munch W m m' -> wmono usegs m m' ->
    Forall (fun iv => (snd iv <= usp /\ ATOP <= fst iv) \/ In iv pstdout_ivs) W ->
    (forall b, In b LB -> blk_addr b + blk_size b <= ATOP) ->
    pdrv_pres LB usp m m'.
  Proof.
    intros m m' W MU WM HW HLB a Ha Hc Hx.
    destruct (magree_of_munch usegs _ _ _ MU WM a Ha) as [E V]; [| split; [exact E| exact V]].
    clear MU WM. induction W as [|iv W IH]; cbn; [exact I|].
    inversion HW as [|iv' W' Hiv HW']; subst. destruct iv as [lo' hi']. cbn [fst snd] in Hiv. split; [| apply IH; exact HW'].
    destruct Hiv as [[H1 H2]|Hin].
    - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]].
      + lia.
      + atop_facts. lia.
      + pose proof (HLB b Hb). lia.
    - intros Hr. apply Hx. unfold pstdout_ivs, client_wr, PINIT_FLAG, PNEWH in Hin. cbn in Hin.
      repeat (destruct Hin as [E|Hin]; [injection E; intros <- <-; unfold pstdout_ivs, client_wr; cbn; unfold PINIT_FLAG, PNEWH; lia|]); destruct Hin.   (* [comment removed for export] *)
  Qed.

  Lemma LB_below : forall st cb own m, RHEAP st (cb ++ LBT own) m -> forall b, In b LB -> blk_addr b + blk_size b <= ATOP.
  Proof.
    intros st cb own m P b Hb.
    assert (HB : In b (cb ++ LBT own)) by (apply in_or_app; right; destruct own as [[q D]|]; [right|]; exact Hb).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P HB) as (_ & _ & _ & B4 & _). exact B4.
  Qed.

  (* [comment removed for export] *)
  Lemma pincb_hpres : forall cb LX SP' m m', harness_pres LX SP' m m' -> pincb cb m -> pincb cb m'.
  Proof.
    intros cb LX SP' m m' HP. apply (pincb_agree _ _ _ _ (magree_of_hpres _ _ _ _ HP)). intros a Ha. pose proof (pincb_addr_range a Ha).
    split; [right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *; lia| ocw].
  Qed.
  Lemma patx_hpres : forall LX SP' m m', harness_pres LX SP' m m' -> patexit_reg m -> patexit_reg m'.
  Proof.
    intros LX SP' m m' HP. apply (patx_table_agree _ _ _ _ _ _ _ (magree_of_hpres _ _ _ _ HP)). intros a Ha. pose proof (patx_addr_range a Ha).
    split; [right; left; unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *; lia| ocw].
  Qed.

  Lemma unsigned_wz_mod32 : forall r, bv_unsigned (wz r) mod 2^32 = r mod 2^32.
  Proof.
    intros r. unfold wz. rewrite unsigned_lit_wrap. apply Z.mod_mod_divide. exists (2^32). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma call_body : forall own k b (rcw : word) st ms {B} (K : Z -> @M PState B) (Q : B -> PState -> machine_state -> Prop),
    1 <= k <= 4 -> 0 <= b <= 1 -> match own with None => plen = 0 | Some _ => True end -> RUNST0 own 0x269e0 k b rcw st ms ->
    (forall rc' st' ms', RUNST own (if k =? 1 then 0x26a18 else 0x269e0) (k - 1) (bad_after rc' b) st' ms' -> implM usegs (K rc') st' Q ms') ->
    implM usegs (rc' <- ProgP.fuzz_one payload ;; io_emit ProgP.io rc' ;;; K rc') st Q ms.
  Proof.
    intros own k b rcw st ms B K Q HK HB OWNZ R HKONT.
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & [P IV]).
    destruct P as (cb & CBK & P & CST).
    pose proof IV as (FR & PB & [errv ERR] & MI & ST & AUX & SO & DP & PR & TX).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts _ _ _ _ P) as (BA1 & BA2 & BA3 & BOWN). atop_facts.
    rename TX into AINCB. unfold pincb in AINCB.
    destruct FR as [jb FR]. unfold RERRNO in ERR. unfold PINIT_FLAG, wz.
    pose proof (munch_refl [(0x911b4, 0x911b5)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide PB. hide PR. unfold implM. iprefix. zstep. zstep. unhide PB. unhide PR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (magree_of_munch usegs _ _ _ MU WM) as AG1.
    assert (OUT1 : forall a, a <> 0x911b4 -> (fun a0 : Z => outside [(0x911b4, 0x911b5)] a0) a) by (intros a Ha; cbn; lia).
    assert (P1 : RHEAP st (cb ++ LBT own) m1).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P| exact MU| exact WM|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
    assert (CST1 : client_static st (cb ++ LB) m1).
    { eapply client_static_agree; [exact AG1| | | exact CST].
      - intros a Ha. apply OUT1. unfold cstat_addr in Ha. lia.
      - intros pv Vv a _ HIN Ha. apply OUT1.
        assert (HIN' : In (pv, Vv, 8) (cb ++ LBT own)).
        { apply in_app_or in HIN. apply in_or_app. destruct HIN as [HIN|HIN]; [left; exact HIN| right; destruct own as [[q D]|]; [right|]; exact HIN]. }
        pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P HIN') as (V1 & V2 & V3 & V4 & V5). cbn in V1, V2, V3, V4, V5. atop_facts. lia. }
    assert (AUX1 : rauxv_ok m1 AB).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL, RLIBC in *. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (SO1 : stdout_file m1 (ps_so st)) by (eapply (stdout_file_agree _ _ _ _ AG1); [intros a Ha; apply OUT1; unfold stdout_addr in Ha; lia| exact SO]).
    assert (PB1 : bytes_at usegs m1 (dptr own) (zbytes payload)).
    { eapply bytes_at_magree; [exact AG1| exact PB|]. intros a Ha. apply OUT1. rewrite zbytes_length in Ha. unfold zlength in PLEN.
      destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [lia| unfold PEMPTY in Ha; rewrite OWNZ in PLEN; lia]. }
    assert (DP1 : pdrv_pres LB usp m0 m1).
    { eapply pdrv_pres_trans; [exact DP|]. eapply pdrv_pres_of_munch; [exact MU| exact WM| | apply (LB_below _ _ _ _ P)].
      constructor; [| constructor]. right. unfold pstdout_ivs, PINIT_FLAG, PNEWH. cbn. do 4 right. left. reflexivity. }
    assert (PR1 : patexit_reg m1).
    { eapply (patx_table_agree _ _ _ _ _ _ _ AG1); [| exact PR]. intros a Ha. apply OUT1. pose proof (patx_addr_range a Ha). lia. }
    clear AG1 OUT1 MU WM P CST AUX SO PB DP IV PR.
    zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st Q msx) end.
    eapply implM_bind.
    { (* [comment removed for export] *)
      eapply FUZZ with (lo := lo) (AB := AB) (LB := cb ++ LBT own) (D := dptr own) (payload := payload) (errv := errv);
        rewrite ?(unsigned_lit (usp + -80)) by lia.
      - exact P1.
      - exact PB1.
      - unfold payload. apply Forall_skipn'. exact FC.
      - destruct own as [[q D]|]; cbn [dptr LBT].
        + right; right. exists (q, D, plen). split; [apply in_or_app; right; left; reflexivity|]. cbn. lia.
        + right; left. unfold PEMPTY, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. rewrite PLEN.
          rewrite OWNZ. lia.
      - (* [comment removed for export] *)
        intros a Ha. destruct own as [[q D]|]; cbn [dptr] in Ha.
        + destruct BOWN as (_ & _ & _ & BD). unfold client_wr. cbn [outside]. lia.
        + unfold PEMPTY in Ha. rewrite PLEN, OWNZ in Ha. lia.
      - destruct own as [[q D]|]; cbn [dptr]; [lia| unfold PEMPTY; lia].
      - destruct own as [[q D]|]; cbn [dptr]; [atop_facts; lia| unfold PEMPTY; rewrite PLEN, OWNZ; lia].
      - lia.
      - eapply client_static_lb; [| exact CST1]. intros pv Vv _ HIN. apply in_app_or in HIN. apply in_or_app.
        destruct HIN as [HIN|HIN]; [left; exact HIN| right; destruct own as [[q D]|]; [right|]; exact HIN].
      - exact AUX1.
      - lia.
      - lia.   (* [comment removed for export] *)
      - exact ST.
      - exact CEIL.
      - unfold PHARNESS_STACK. lia.
      - unfold RATP, RERRNO in *. rewrite (unsigned_lit 597472) by lia. exact ERR.
      - exact MI.
      - exact FRM.
      - reflexivity.
      - clear -SP16 SPR L'. Z.div_mod_to_equations. lia.
      - reflexivity.
      - rewrite PLEN. reflexivity.
      - reflexivity. }      (* [comment removed for export] *)
    cbv beta. intros r st1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & errv1 & LB1
                    & -> & RR & MI2 & FRM1 & ST2 & ERR2 & AUX2 & HPR & P2 & CST2 & SOE & ARM).
    rewrite ?(unsigned_lit (usp + -80)) in ST2 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR by lia.
    unfold RATP in ERR2. rewrite ?(unsigned_lit 597472) in ERR2 by lia. change (597472 + -164) with 597308 in ERR2.
    replace (ret_pc (Z_to_bv 64 0x269f4)) with (Z_to_bv 64 0x269f4) by (symmetry; rpc).
    subst r.
    (* [comment removed for export] *)
    assert (CB1 : exists cb1, CBOK cb1 st1 /\ LB1 = cb1 ++ LBT own /\ client_static st1 (cb1 ++ LB) m2).
    { (* [comment removed for export] *)
      destruct ARM as (-> & E1). exists cb. split; [| split; [reflexivity| exact CST2]].
      destruct CBK as [[E0 CL]|(pc & V & C0 & E0 & CL)]; [left; split; [exact E0| rewrite E1; exact CL]| right; exists pc, V; split; [exact C0| split; [exact E0| rewrite E1; exact CL]]]. }
    destruct CB1 as (cb1 & CBK1 & -> & CST2').
    pose proof (magree_of_hpres _ _ _ _ HPR) as AGH.
    apply (rw_cells_magree usegs _ _ _ _ _ AGH) in FR; [| intros a Ha; cbn in Ha; split; [left; lia| ocw]].
    assert (PB2 : bytes_at usegs m2 (dptr own) (zbytes payload)).
    { eapply bytes_at_magree; [exact AGH| exact PB1|]. intros a Ha. rewrite zbytes_length in Ha. unfold zlength in PLEN.
      destruct own as [[q D]|]; cbn [dptr LBT] in Ha |- *.
      - split; [right; right; exists (q, D, plen); split; [apply in_or_app; right; left; reflexivity| cbn; lia]| ocw].
      - exfalso. rewrite OWNZ in PLEN. lia. }
    assert (AINCB2 : pincb 1 m2) by (eapply pincb_hpres; [exact HPR| unfold pincb; exact AINCB]).
    assert (PR2 : patexit_reg m2) by (eapply patx_hpres; [exact HPR| exact PR1]).
    clear AGH PB1 P1 CST1 AUX1 ERR MI ST AINCB CST2 PR1.
    unfold pincb in AINCB2.
    pose proof (munch_refl [(0x911b4, 0x911b5)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    hide PB2. hide PR2. unfold implM. iprefix. zstep. zstep. unhide PB2. unhide PR2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    pose proof (magree_of_munch usegs _ _ _ MU WM) as AG3.
    assert (OUT3 : forall a, a <> 0x911b4 -> (fun a0 : Z => outside [(0x911b4, 0x911b5)] a0) a) by (intros a Ha; cbn; lia).
    assert (P3 : RHEAP st1 (cb1 ++ LBT own) m3).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P2| exact MU| exact WM|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
    assert (CST3 : client_static st1 (cb1 ++ LB) m3).
    { eapply client_static_agree; [exact AG3| | | exact CST2'].
      - intros a Ha. apply OUT3. unfold cstat_addr in Ha. lia.
      - intros pv Vv a _ HIN Ha. apply OUT3.
        assert (HIN' : In (pv, Vv, 8) (cb1 ++ LBT own)).
        { apply in_app_or in HIN. apply in_or_app. destruct HIN as [HIN|HIN]; [left; exact HIN| right; destruct own as [[q D]|]; [right|]; exact HIN]. }
        pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P2 HIN') as (V1 & V2 & V3 & V4 & V5). cbn in V1, V2, V3, V4, V5. atop_facts. lia. }
    assert (AUX3 : rauxv_ok m3 AB).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. unfold RAUXV_CELL, RLIBC in *. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (SO3 : stdout_file m3 (ps_so st1)).
    { rewrite SOE. eapply (stdout_file_agree _ _ _ _ AG3); [intros a Ha; apply OUT3; unfold stdout_addr in Ha; lia|].
      eapply (stdout_file_agree _ _ _ _ (magree_of_hpres _ _ _ _ HPR)); [| exact SO1]. intros a Ha. split.
      - right; left. unfold stdout_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
      - unfold stdout_addr in Ha. ocw. }
    assert (PB3 : bytes_at usegs m3 (dptr own) (zbytes payload)).
    { eapply bytes_at_magree; [exact AG3| exact PB2|]. intros a Ha. apply OUT3. rewrite zbytes_length in Ha. unfold zlength in PLEN.
      destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [lia| unfold PEMPTY in Ha; rewrite OWNZ in PLEN; lia]. }
    assert (DP3 : pdrv_pres LB usp m0 m3).
    { eapply pdrv_pres_trans; [exact DP1|]. eapply pdrv_pres_trans.
      - eapply pdrv_pres_of_heap_sub; [exact HPR| lia| intros bb Hb; apply in_or_app; right; destruct own as [[q D]|]; [right|]; exact Hb].
      - eapply pdrv_pres_of_munch; [exact MU| exact WM| | apply (LB_below _ _ _ _ P2)].
        constructor; [| constructor]. right. unfold pstdout_ivs, PINIT_FLAG, PNEWH. cbn. do 4 right. left. reflexivity. }
    assert (PR3 : patexit_reg m3).
    { eapply (patx_table_agree _ _ _ _ _ _ _ AG3); [| exact PR2]. intros a Ha. apply OUT3. pose proof (patx_addr_range a Ha). lia. }
    clear AG3 OUT3 MU WM P2 CST2' AUX2 SO1 PB2 DP1 HPR PR2.
    (* [comment removed for export] *)
    zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st1 Q msx) end.
    eapply implM_bind.
    { eapply implM_keeps with (f := ps_heap); [| apply s_emit_heap].
      unfold io_emit, ProgP.io, io_S.
      eapply EMIT with (lo := lo) (canary := CAN) (v := 0);
        rewrite ?(unsigned_lit (usp + -80)) by lia.
      - intros; reflexivity.
      - intros; reflexivity.
      - exact FWXO.
      - exact SO3.
      - lia.
      - apply unsigned_wz_mod32.
      - exact ST2.
      - unfold EMIT_DEPTH, HARNESS_STACK in *. lia.
      - unfold GLOBALS_TOP. lia.
      - lia.
      - apply (RHEAP_ssp _ _ _ P3).
      - exact MI2.
      - exact FRM1. }
    cbv beta. intros [] st2 ms2 [PO EH].
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2 & fc2 & m4 & -> & MUc & WMc & MI4 & FRM2 & FEQ & ST4 & SO4 & SSP4).
    rewrite ?(unsigned_lit (usp + -80)) in MUc by lia. rewrite ?(unsigned_lit (usp + -80)) in ST4 by lia.
    replace (ret_pc (Z_to_bv 64 0x26a04)) with (Z_to_bv 64 0x26a04) by (symmetry; rpc).
    pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp + -80 <= a \/ (a < lo /\ (a < 0x10000 \/ 0xb3000 <= a)) \/ (0x10000 <= a < 0xb3000 /\ ~ (0x81058 <= a < 0x81058 + 232) /\ ~ (0xb24b8 <= a < 0xb24b8 + 1024)))
                            -> (fun a0 : Z => outside [(lo, usp + -80); (0x81058, 0x81058 + 232); (0xb24b8, 0xb24b8 + 1024)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (P4 : RHEAP st2 (cb1 ++ LBT own) m4).
    { eapply RHEAP_ext with (s := st1); [| | ]; cycle 1.
      - unfold ps_heap in EH. congruence.
      - unfold ps_heap in EH. congruence.
      - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P3| exact MUc| exact WMc|].
        constructor; [left; cbn [fst snd]; atop_facts; lia|].
        constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|].
        constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
    assert (CST4 : client_static st2 (cb1 ++ LB) m4).
    { eapply (client_static_fa st1); [unfold ps_heap in EH; congruence|].
      eapply client_static_agree; [exact AG| | | exact CST3].
      - intros a Ha. apply OUT. unfold cstat_addr in Ha. lia.
      - intros pv Vv a _ HIN Ha. apply OUT.
        assert (HIN' : In (pv, Vv, 8) (cb1 ++ LBT own)).
        { apply in_app_or in HIN. apply in_or_app. destruct HIN as [HIN|HIN]; [left; exact HIN| right; destruct own as [[q D]|]; [right|]; exact HIN]. }
        pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P3 HIN') as (V1 & V2 & V3 & V4 & V5). cbn in V1, V2, V3, V4, V5. atop_facts. lia. }
    assert (CBK2 : CBOK cb1 st2).
    { assert (EFA : ps_fa st2 = ps_fa st1) by (unfold ps_heap in EH; congruence).
      destruct CBK1 as [[E1 E2]|(pc & V & E0 & E1 & E2)]; [left; split; [exact E1| rewrite EFA; exact E2]| right; exists pc, V; split; [exact E0| split; [exact E1| rewrite EFA; exact E2]]]. }
    assert (IV4 : INV0 own st2 m4).
    { split. { exists jb. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply OUT; cbn in Ha; lia]. }
      split. { eapply bytes_at_magree; [exact AG| exact PB3|]. intros a Ha. apply OUT. rewrite zbytes_length in Ha. unfold zlength in PLEN.
               destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [atop_facts; lia| unfold PEMPTY in *; rewrite OWNZ in PLEN; lia]. }
      split. { exists errv1. eapply rw_cells_magree; [exact AG| exact ERR2| intros a Ha; apply OUT; unfold RERRNO in Ha; cbn in Ha; lia]. }
      split; [exact MI4|]. split; [exact ST4|].
      split. { eapply rauxv_ok_frame; [exact AUX3| exact MUc| exact WMc|]. unfold RAUXV_CELL, RLIBC in *.
               constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
      split; [exact SO4|].
      split. { eapply pdrv_pres_trans; [exact DP3|]. eapply pdrv_pres_of_munch; [exact MUc| exact WMc| | apply (LB_below _ _ _ _ P3)].
               constructor; [left; cbn [fst snd]; lia|]. constructor; [right; cbn; left; reflexivity|]. constructor; [right; cbn; right; left; reflexivity| constructor]. }
      split. { eapply (patx_table_agree _ _ _ _ _ _ _ AG); [intros a Ha; apply OUT; pose proof (patx_addr_range a Ha); lia| exact PR3]. }
      eapply (pincb_agree _ _ _ _ AG); [intros a Ha; apply OUT; pose proof (pincb_addr_range a Ha); lia|].
      unfold pincb. assumption. }
    clear AG OUT MUc WMc.
    (* [comment removed for export] *)
    eapply implM_evt; [| intros ms' H; exact (HKONT _ _ _ H)].
    zstep. change (bv_swrap 32 (0 + -1)) with (-1)%Z.
    zstep. if_cases KB; zify_cond KB; rewrite ?SM2_unsigned in KB; [| exfalso; clear -KB; lia]. clear KB.
    zstep. rewrite (swrap32_small (k + -1)) by lia. zstep. if_cases KK; zify_cond KK.
    - replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      apply evt_done. change (bad_after 0 b) with b. split; [| lia]. exists (Z_to_bv 64 (-1)). unfold RUNST0. do 16 eexists. exists F2, fc2, m4.
      split; [reflexivity|]. split; [exact FRM2|]. split; [exists cb1; split; [exact CBK2| split; [exact P4| exact CST4]]| exact IV4].
    - replace (k =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
      apply evt_done. change (bad_after 0 b) with b. split; [| lia]. exists (Z_to_bv 64 (-1)). unfold RUNST0. do 16 eexists. exists F2, fc2, m4.
      split; [reflexivity|]. split; [exact FRM2|]. split; [exists cb1; split; [exact CBK2| split; [exact P4| exact CST4]]| exact IV4].
  Qed.

  (* [comment removed for export] *)
  Lemma calls_loop : forall (n : nat) own b (rcw : word) st ms,
    (1 <= n <= 4)%nat -> 0 <= b <= 1 -> match own with None => plen = 0 | Some _ => True end ->
    RUNST0 own 0x269e0 (Z.of_nat n) b rcw st ms ->
    implM usegs (run_calls ProgP.fuzz_one (io_emit ProgP.io) n payload b) st (fun b' st' ms' => RUNST own 0x26a18 0 b' st' ms') ms.
  Proof.
    induction n as [|n IH]; intros own b rcw st ms HN HB OWNZ R; [lia|].
    cbn [run_calls].
    eapply (call_body own (Z.of_nat (S n)) b rcw st ms (fun rc' => run_calls ProgP.fuzz_one (io_emit ProgP.io) n payload (bad_after rc' b)));
      [lia| exact HB| exact OWNZ| exact R|].
    intros rc' st' ms' R'. destruct n as [|n'].
    - cbn [run_calls]. replace (Z.of_nat 1 =? 1) with true in R' by reflexivity. apply implM_ret. apply evt_done.
      replace (Z.of_nat 1 - 1) with 0 in R' by lia. exact R'.
    - replace (Z.of_nat (S (S n')) =? 1) with false in R' by (symmetry; apply Z.eqb_neq; lia).
      destruct R' as [[rcw' R'] HB'].
      apply (IH own (bad_after rc' b) rcw'); [lia| exact HB'| exact OWNZ|]. replace (Z.of_nat (S n')) with (Z.of_nat (S (S n')) - 1) by lia. exact R'.
  Qed.

  (* [comment removed for export] *)
  Lemma run_tail : forall own b st ms,
    RUNST own 0x26a18 0 b st ms ->
    implM usegs ((match omodel own with Some q => raw_free q | None => mret tt end) ;;; mret (if b =? 0 then 0 else 78)) st
          (ptarget_run_post ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sin LB AB lo m0) ms.
  Proof.
    intros own b st ms [[rcw R] HB].
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & [P IV]).
    destruct P as (cb & CBK & P & CST).
    pose proof IV as (FR & PB & [errv ERR] & MI & ST & AUX & SO & DP & PR & TX).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts _ _ _ _ P) as (BA1 & BA2 & BA3 & BOWN). atop_facts.
    unfold wz. destruct FR as [jb FR]. unfold RERRNO in ERR.
    (* [comment removed for export] *)
    hide PR. hide TX. unfold implM. iprefix. zstep. zstep. apply evt_done. unhide PR. unhide TX.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm st (ptarget_run_post ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sin LB AB lo m0) msx) end.
    eapply implM_bind with (Q1 := fun _ st' ms' => exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (errv' : word),
        ms' = MS (mkR x1' SPF gp tpv t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 (dptr own)) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 (oreg own)) rcw (Z_to_bv 64 PINIT_FLAG) (Z_to_bv 64 0) (Z_to_bv 64 b) SM2 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x26a20) fc None m' (seg_rom usegs)
        /\ CBOK cb st' /\ RHEAP st' (cb ++ LB) m' /\ client_static st' (cb ++ LB) m'
        /\ rw_cells usegs m' (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells usegs m' RERRNO [C4 errv'] /\ mem_inv usegs m' /\ stk usegs m' lo (usp + -80) /\ rauxv_ok m' AB
        /\ stdout_file m' (ps_so st') /\ pdrv_pres LB usp m0 m' /\ patexit_reg m' /\ pincb 0 m').
    { destruct own as [[q D]|]; cbn [omodel oreg dptr LBT] in *.
      - (* [comment removed for export] *)
        unfold rfree_stmt in FREE.
        eapply implM_mono.
        { eapply FREE with (lo := lo) (B := AB) (p := q) (A := D) (n := plen) (LB := cb ++ (q, D, plen) :: LB); try reflexivity; unfold RATP;
            rewrite ?(unsigned_lit 597472) by lia; rewrite ?(unsigned_lit (usp + -80)) by lia;
            first [ exact P | apply in_or_app; right; left; reflexivity | exact AUX | lia | exact ST | exact CEIL | unfold RFREE_STACK; lia | exact ERR | exact MI ]. }
        cbv beta. intros [] st' ms' PO.
        destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
        rewrite ?(unsigned_lit (usp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR3 by lia.
        unfold RATP in ERR3. rewrite ?(unsigned_lit 597472) in ERR3 by lia. change (597472 + -164) with RERRNO in ERR3.
        replace (ret_pc (Z_to_bv 64 0x26a20)) with (Z_to_bv 64 0x26a20) by (symmetry; rpc).
        pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ P) as ND.
        assert (ELB : lb_remove q (cb ++ (q, D, plen) :: LB) = cb ++ LB).
        { destruct CBK as [[-> _]|(pc & V & _ & -> & _)]; cbn [app] in ND |- *.
          - exact (lb_remove_head (q, D, plen) LB ND).
          - exact (lb_remove_second q (pc, V, 8) (q, D, plen) LB eq_refl ND). }
        rewrite ELB in HPR3, HEAP3.
        do 16 eexists. exists m3, (Z_to_bv 64 (bv_unsigned errv)).
        split; [reflexivity|].
        split. { destruct CBK as [[E1 E2]|(pc & V & E0 & E1 & E2)]; [left; split; [exact E1| rewrite FAE3; exact E2]| right; exists pc, V; split; [exact E0| split; [exact E1| rewrite FAE3; exact E2]]]. }
        split; [exact HEAP3|].
        split. { eapply (client_static_fa st); [exact FAE3|]. eapply (client_static_agree _ _ _ _ _ HPR3); [| | exact CST].
                 - intros a Ha. right; left. unfold cstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
                 - intros pv Vv a _ HIN Ha. right; right. exists (pv, Vv, 8). split; [exact HIN| cbn; lia]. }
        split; [eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia]|].
        split; [replace (Z_to_bv 64 (bv_unsigned errv)) with errv by (symmetry; apply Z_to_bv_bv_unsigned); exact ERR3|].
        split; [exact MI3|]. split; [exact ST3|]. split; [exact AUX3|].
        split; [rewrite SOE3; eapply stdout_file_heap_pres; [exact HPR3| exact SO]|].
        split; [eapply pdrv_pres_trans; [exact DP|]; eapply pdrv_pres_of_heap_sub; [apply harness_pres_of_rheap_pres; exact HPR3| lia| intros bb Hb; apply in_or_app; right; exact Hb]|].
        split; [eapply patx_hpres; [apply harness_pres_of_rheap_pres; exact HPR3| exact PR]| eapply pincb_hpres; [apply harness_pres_of_rheap_pres; exact HPR3| exact TX]].
      - (* [comment removed for export] *)
        apply implM_ret. eapply evt_mono; [apply (rfree_null_spec); reflexivity|].
        cbv beta. intros ms' ->. replace (ret_pc (Z_to_bv 64 0x26a20)) with (Z_to_bv 64 0x26a20) by (symmetry; rpc).
        do 16 eexists. exists m, errv.
        split; [reflexivity|]. split; [exact CBK|]. split; [exact P|]. split; [exact CST|]. split; [exact FR|]. split; [exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [exact AUX|].
        split; [exact SO|]. split; [exact DP|]. split; [exact PR| exact TX]. }
    cbv beta. intros [] st' ms' (x1' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & CBK' & P' & CST' & FR' & ERR' & MI' & ST' & AUX' & SO' & DP' & PR' & TX').
    apply implM_ret.
    (* [comment removed for export] *)
    hide PR'. hide TX'. zstep. zstep. zstep.
    do 9 zstep. release_frame FR' ST' (bv_unsigned sp). zstep. zstep. unhide PR'. unhide TX'.
    first [ lazymatch goal with |- context [Z_to_bv 64 (Z.land ?e 78)] =>
              replace (Z.land e 78) with (if b =? 0 then 0 else 78)
                by (assert (Hb : b = 0 \/ b = 1) by lia; destruct Hb as [Hb|Hb]; rewrite Hb; vm_compute; reflexivity) end
          | rewrite (status_norm b) by lia ].
    apply evt_done. unfold ptarget_run_post. do 16 eexists. exists m', errv', (cb ++ LB).
    split; [reflexivity|].
    split; [destruct (b =? 0); lia|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split; [unfold RATP, RERRNO in *; rewrite unsigned_lit by lia; exact ERR'|].
    split; [exact AUX'|]. split; [exact DP'|]. split; [exact P'|]. split; [exact CST'|].
    split; [| split; [exact SO'| split; [exact PR'| exact TX']]].
    destruct CBK' as [[-> E2]|(pc & V & E0 & -> & E2)]; [left; split; [reflexivity| exact E2]| right; exists pc, V; split; [exact E0| split; [reflexivity| exact E2]]].
  Qed.

  (* [comment removed for export] *)
  Definition PRE1 (s : PState) (m : mem) : Prop :=
    RHEAP s LB m /\ FRAME m /\ bytes_at usegs m A (zbytes content) /\ client_static s LB m /\ ps_fa s = cl0
    /\ (exists errv : word, rw_cells usegs m RERRNO [C4 errv]) /\ mem_inv usegs m /\ stk usegs m lo (usp + -80)
    /\ rauxv_ok m AB /\ stdout_file m (ps_so s) /\ pdrv_pres LB usp m0 m
    /\ patexit_reg m /\ pincb 0 m.

  Notation EST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (Z_to_bv 64 plen) x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 (Z_to_bv 64 PINIT_FLAG) (Z_to_bv 64 calls) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation POST := (ptarget_run_post ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sin LB AB lo m0).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma trun_empty : forall s x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem),
    plen = 0 -> frm0 fc -> PRE1 s m ->
    implM usegs (ProgP.run cfg payload) s POST (EST 0x269d0 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc m).
  Proof.
    intros until m. intros PZ FRM (P & FR & CT & CST & CL & [errv ERR] & MI & ST & AUX & SO & DP & PR & TX).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    unfold ProgP.run, Adapter.target_run. rewrite PLEN. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; exact PZ).
    change (1 + Z.land cfg 3) with calls.
    apply implM_retb. cbv beta iota.
    hide PR. hide TX. unfold implM. iprefix. zstep. zstep. zstep. zstep. apply evt_done. unhide PR. unhide TX.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s POST msx) end.
    eapply implM_bind.
    { eapply (calls_loop (Z.to_nat calls) None 0 x19); [lia| lia| exact PZ|].
      unfold RUNST0. do 16 eexists. exists F, fc, m. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold PEMPTY, PINIT_FLAG, SM2, wz; reflexivity|].
      split; [exact FRM|]. split; [exists []; split; [left; split; [reflexivity| exact CL]| split; [exact P| exact CST]]|].
      split; [exact FR|].
      assert (PE : payload = []). { unfold payload. apply skipn_all2. unfold plen, zlength in PZ. lia. }
      split; [cbn [dptr]; rewrite PE; cbn [zbytes map]; apply bytes_at_nil; unfold PEMPTY; lia|].
      split; [exists errv; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [exact AUX|]. split; [exact SO|]. split; [exact DP|]. split; [exact PR| exact TX]. }
    cbv beta. intros b st' ms' R. apply (run_tail None b st' ms' R).
  Qed.

  (* [comment removed for export] *)
  Lemma pdrv_pres_of_newblock : forall st q D n m m',
    RHEAP st ((q, D, n) :: LB) m -> munch [(D, D + n)] m m' -> wmono usegs m m' -> pdrv_pres LB usp m m'.
  Proof.
    intros st q D n m m' P MU WM a Ha Hc Hx.
    destruct (magree_of_munch usegs _ _ _ MU WM a Ha) as [E V]; [| split; [exact E| exact V]].
    cbn. split; [| exact I].
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ (q, D, n) P ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & B5). cbn in B1, B2, B3, B4, B5.
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L', B4. atop_facts.
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ P) as ND.
    pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (q, D, n) b P ltac:(left; reflexivity) ltac:(right; exact Hb)) as DJ.
    cbn [blk_id blk_addr blk_size fst snd] in DJ.
    assert (NE : q <> blk_id b).
    { cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. intros E. apply NI. rewrite E. apply in_map. exact Hb. }
    specialize (DJ NE). destruct b as [[bi ba] bs]. cbn [blk_addr blk_size blk_id fst snd] in DJ, Hr. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma trun_copy : forall s x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : mem),
    plen <> 0 -> frm0 fc -> PRE1 s m ->
    implM usegs (ProgP.run cfg payload) s POST (EST 0x26984 x1 t0 t1 t2 (Z_to_bv 64 PAY) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc m).
  Proof.
    intros until m. intros PZ FRM (P & FR & CT & CST & CL & [errv ERR] & MI & ST & AUX & SO & DP & PR & TX).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts s [] None m P) as (BA1 & BA2 & BA3 & _). atop_facts.
    pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
    assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
    unfold zlength in LC, L6.
    unfold ProgP.run, Adapter.target_run. rewrite !PLEN.
    replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; exact PZ).
    change (1 + Z.land cfg 3) with calls.
    apply implM_bind_assoc.
    destruct FR as [jb FR]. unfold RERRNO in ERR.
    (* [comment removed for export] *)
    hide PR. hide TX. unfold implM. iprefix. zstep. zstep. apply evt_done. unhide PR. unhide TX.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s POST msx) end.
    eapply implM_bind.
    { unfold rmalloc_stmt in MALLOC.
      eapply MALLOC with (lo := lo) (B := AB); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 597472) by lia; rewrite ?(unsigned_lit (usp + -80)) by lia;
        first [ exact P | exact AUX | lia | exact ST | exact CEIL | unfold RMALLOC_STACK; lia | exact ERR | exact MI ]. }
    cbv beta. intros r s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & FAE & SOE & RR).
    unfold RATP in ERR1. rewrite ?(unsigned_lit 597472) in ERR1 by lia. rewrite ?(unsigned_lit (usp + -80)) in ST1 by lia. rewrite ?(unsigned_lit (usp + -80)) in HPR by lia.
    change (597472 + -164) with 597308 in ERR1.
    replace (ret_pc (Z_to_bv 64 0x2698c)) with (Z_to_bv 64 0x2698c) by (symmetry; rpc).
    assert (FR1 : rw_cells usegs m1 (usp + -80) [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
    assert (CT1 : bytes_at usegs m1 A (zbytes content)).
    { eapply rheap_pres_bytes_at; [exact HPR| exact CT|]. right; right. exists (p, A, cap). split; [exact INLB|]. cbn. rewrite zbytes_length. lia. }
    assert (CST1 : client_static s1' LB m1).
    { eapply (client_static_fa s); [exact FAE|]. eapply (client_static_agree _ _ _ _ _ HPR); [| | exact CST].
      - intros a Ha. right; left. unfold cstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
      - intros pv Vv a _ HIN Ha. right; right. exists (pv, Vv, 8). split; [exact HIN| cbn; lia]. }
    assert (TX1 : pincb 0 m1) by (eapply pincb_hpres; [apply harness_pres_of_rheap_pres; exact HPR| exact TX]).
    assert (PR1 : patexit_reg m1) by (eapply patx_hpres; [apply harness_pres_of_rheap_pres; exact HPR| exact PR]).
    destruct r as [nb|].
    2:{ (* [comment removed for export] *)
        destruct RR as [-> HEAP1].
        apply implM_retb. cbv beta iota. apply implM_ret.
        hide PR1. hide TX1. zstep. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity].
        zstep. zstep. do 9 zstep. release_frame FR1 ST1 (bv_unsigned sp). zstep. zstep. unhide PR1. unhide TX1.
        apply evt_done. unfold ptarget_run_post. do 16 eexists. exists m1, errv1, LB.
        split; [reflexivity|]. split; [lia|]. split; [exact MI1|]. split; [exact FRM|]. split; [exact ST1|].
        split; [unfold RATP, RERRNO in *; rewrite unsigned_lit by lia; exact ERR1|].
        split; [exact AUX1|].
        split; [eapply pdrv_pres_trans; [exact DP| eapply pdrv_pres_of_heap_sub; [apply harness_pres_of_rheap_pres; exact HPR| lia| intros b Hb; exact Hb]]|].
        split; [exact HEAP1|]. split; [exact CST1|]. split; [left; split; [reflexivity| rewrite FAE; exact CL]|].
        split; [rewrite SOE; eapply stdout_file_heap_pres; [exact HPR| exact SO]| split; [exact PR1| exact TX1]]. }
    (* [comment removed for export] *)
    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & _).
    pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). atop_facts.
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HEAP1) as ND.
    assert (DISJ : A' + plen <= A \/ A + cap <= A').
    { pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (nb, A', plen) (p, A, cap) HEAP1 ltac:(left; reflexivity) ltac:(right; exact INLB)) as D.
      cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. intros E. apply NI. rewrite E.
      apply (in_map blk_id) in INLB. exact INLB. }
    (* [comment removed for export] *)
    assert (PB : bytes_at usegs m1 PAY (zbytes payload)).
    { rewrite <- (firstn_skipn (Z.to_nat (6 + L)) (zbytes content)) in CT1. apply bytes_at_app in CT1. destruct CT1 as [_ X].
      rewrite length_firstn, zbytes_length in X. unfold payload, zbytes. rewrite <- skipn_map. unfold zbytes in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length content))) with PAY in X by (rewrite EPAY; lia). exact X. }
    apply implM_retb. cbv beta iota.
    hide PR1. hide TX1. unfold implM. iprefix.
    zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply memcpy_callv with (src := zbytes payload) (junk := junk');
        [exact PB| rewrite zbytes_length; lia| exact NBLK| unfold plen, zlength in *; lia| lia| unfold plen, zlength in *; lia| lia| exact MI1]. }
    cbv beta. intros ms' PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NB2 & _).
    transport_after_call usegs m1 m2 MUc WMc. unhide PR1. unhide TX1.
    replace (ret_pc (Z_to_bv 64 0x269a0)) with (Z_to_bv 64 0x269a0) by (symmetry; rpc).
    assert (P2 : RHEAP s1' ((nb, A', plen) :: LB) m2).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HEAP1| exact MUc| exact WMc|].
      constructor; [| constructor]. right; right. exists (nb, A', plen). split; [left; reflexivity|]. cbn. lia. }
    pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (a < A' \/ A' + plen <= a) -> (fun a0 : Z => outside [(A', A' + plen)] a0) a) by (intros a Ha; cbn; lia).
    assert (CST2 : client_static s1' ([] ++ LB) m2).
    { eapply client_static_agree; [exact AG| | | exact CST1].
      - intros a Ha. apply OUT. unfold cstat_addr in Ha. lia.
      - intros pv Vv a _ HIN Ha. apply OUT.
        pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (nb, A', plen) (pv, Vv, 8) HEAP1 ltac:(left; reflexivity) ltac:(right; exact HIN)) as DJ.
        cbn [blk_id blk_addr blk_size fst snd] in DJ.
        assert (NE : nb <> pv).
        { cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. intros E. apply NI. rewrite E. apply (in_map blk_id) in HIN. exact HIN. }
        specialize (DJ NE). lia. }
    assert (TX2 : pincb 0 m2).
    { eapply (pincb_agree _ _ _ _ AG); [| exact TX1]. intros a Ha. apply OUT. pose proof (pincb_addr_range a Ha). lia. }
    assert (PR2 : patexit_reg m2).
    { eapply (patx_table_agree _ _ _ _ _ _ _ AG); [| exact PR1]. intros a Ha. apply OUT. pose proof (patx_addr_range a Ha). lia. }
    assert (IV2 : INV0 (Some (nb, A')) s1' m2).
    { split; [exists jb; exact FR1|].
      split; [cbn [dptr]; apply (rw_cells_bytes_at usegs) in NB2; cbn [cells_bytes cbytes app] in NB2; rewrite app_nil_r in NB2; exact NB2|].
      split; [exists errv1; exact ERR1|]. split; [exact MI2|]. split; [exact ST1|].
      split. { eapply rauxv_ok_frame; [exact AUX1| exact MUc| exact WMc|]. unfold RAUXV_CELL, RLIBC in *. constructor; [cbn [fst snd]; lia| constructor]. }
      split. { rewrite SOE. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT; unfold stdout_addr in Ha; lia|]. eapply stdout_file_heap_pres; [exact HPR| exact SO]. }
      split; [| split; [exact PR2| exact TX2]].
      eapply pdrv_pres_trans; [exact DP|]. eapply pdrv_pres_trans; [eapply pdrv_pres_of_heap_sub; [apply harness_pres_of_rheap_pres; exact HPR| lia| intros b Hb; exact Hb]|].
      eapply pdrv_pres_of_newblock; [exact HEAP1| exact MUc| exact WMc]. }
    clear AG OUT MUc WMc.
    (* [comment removed for export] *)
    hide PR2. hide TX2. zstep. zstep. zstep. zstep. apply evt_done. unhide PR2. unhide TX2.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1' POST msx) end || idtac.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1' POST msx) end || idtac.
    eapply implM_bind.
    { eapply (calls_loop (Z.to_nat calls) (Some (nb, A')) 0 x19); [lia| lia| exact I|].
      unfold RUNST0. do 16 eexists. exists F, fc, m2. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold PINIT_FLAG, SM2, wz; reflexivity|].
      split; [exact FRM|]. split; [exists []; split; [left; split; [reflexivity| rewrite FAE; exact CL]| split; [exact P2| exact CST2]]| exact IV2]. }
    cbv beta. intros b st' ms'' R. apply (run_tail (Some (nb, A')) b st' ms'' R).
  Qed.

  (* [comment removed for export] *)
  Lemma trun_main : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (s : PState) (errv : word),
    RHEAP s LB m0 -> bytes_at usegs m0 A (zbytes content) -> trun_cells0 m0 -> client_static s LB m0 -> ps_fa s = cl0 -> rauxv_ok m0 AB ->
    stk usegs m0 lo usp -> rw_cells usegs m0 RERRNO [C4 errv] -> mem_inv usegs m0 -> frm0 fc ->
    stdout_file m0 (ps_so s) ->
    tp = tpv -> a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 PAY -> a3 = Z_to_bv 64 plen ->
    implM usegs (ProgP.run cfg payload) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PTARGET_RUN) fc None m0 (seg_rom usegs)).
  Proof.
    intros until errv. intros P0 CT TR0 CST0 CL0 AUX0 ST0 ERR0 MI0 FRM SO0 -> -> -> -> ->.
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    pose proof LO' as L'. pose proof CEIL as CEIL'. unfold HARNESS_STACK in CEIL', L'. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (block_facts s [] None m0 P0) as (BA1 & BA2 & BA3 & _). atop_facts.
    pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
    assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
    unfold zlength in LC, L6. unfold RERRNO in ERR0.
    destruct (RHEAP_libc_head _ _ _ P0) as (cdt & thr & sec & tm1 & LIBC).
    unfold implM. eapply impl_evt; [| intros ms' H; exact H].
    eapply trun_init; [exact ST0| exact MI0| exact TR0| exact LIBC|].
    intros m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR ST1 MU WM MI1 PX1 TX1.
    unfold PINIT_FLAG, PNEWH in MU.
    pose proof (magree_of_munch usegs _ _ _ MU WM) as AG.
    assert (OUT : forall a, ((a < lo /\ (a < 0x10000 \/ 0xb3000 <= a)) \/ (0x10000 <= a < 0xb3000 /\ ~ (0x911b0 <= a < 0x911b0 + 1) /\ ~ (0xb1e28 <= a < 0xb2048)))
                            -> (fun a0 : Z => outside [(usp - 128, usp); (0x911b0, 0x911b0 + 1); (0xb1e28, 0xb2048)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (CT1 : bytes_at usegs m1 A (zbytes content)).
    { eapply bytes_at_magree; [exact AG| exact CT|]. intros a Ha. apply OUT. left. rewrite zbytes_length in Ha. lia. }
    assert (ERR1 : rw_cells usegs m1 RERRNO [C4 errv]).
    { eapply rw_cells_magree; [exact AG| exact ERR0|]. intros a Ha. apply OUT. right. unfold RERRNO in *. cbn in Ha. lia. }
    assert (CST1 : client_static s LB m1).
    { eapply client_static_agree; [exact AG| | | exact CST0].
      - intros a Ha. apply OUT. right. unfold cstat_addr in Ha. lia.
      - intros pv Vv a _ HIN Ha. apply OUT. left.
        pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ P0 HIN) as (V1 & V2 & V3 & V4 & V5). cbn in V1, V2, V3, V4, V5. lia. }
    assert (SO1 : stdout_file m1 (ps_so s)) by (eapply (stdout_file_agree _ _ _ _ AG); [| exact SO0]; intros a Ha; apply OUT; right; unfold stdout_addr in Ha; lia).
    assert (AUX1 : rauxv_ok m1 AB).
    { eapply rauxv_ok_frame; [exact AUX0| exact MU| exact WM|]. unfold RAUXV_CELL, RLIBC in *.
      constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (P1 : RHEAP s LB m1).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P0| exact MU| exact WM|].
      constructor; [left; cbn [fst snd]; atop_facts; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|].
      constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
    assert (DP1 : pdrv_pres LB usp m0 m1).
    { eapply pdrv_pres_of_munch; [exact MU| exact WM| | apply (LB_below s [] None m0 P0)].
      constructor; [left; cbn [fst snd]; lia|]. constructor; [right; cbn; right; right; left; reflexivity|].
      constructor; [right; cbn; do 5 right; left; reflexivity| constructor]. }
    assert (PRE : PRE1 s m1).
    { split; [exact P1|]. split; [exact FR|]. split; [exact CT1|]. split; [exact CST1|]. split; [exact CL0|]. split; [exists errv; exact ERR1|].
      split; [exact MI1|]. split; [exact ST1|]. split; [exact AUX1|]. split; [exact SO1|]. split; [exact DP1|]. split; [exact PX1| exact TX1]. }
    clear AG OUT MU WM CT ERR0 CST0 SO0 AUX0 P0 ST0 MI0 TR0 PX1 TX1 LIBC.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    - (* [comment removed for export] *)
      assert (EC : calls = 1) by (unfold calls, cfg; replace (0 <? L) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      zstep. zstep. if_cases KP; zify_cond KP.
      + (* [comment removed for export] *)
        apply evt_done. rewrite <- EC.
        eapply trun_copy; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
      + apply evt_done. rewrite <- EC.
        eapply trun_empty; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
    - (* [comment removed for export] *)
      destruct (nth_error content 2) as [c2|] eqn:EC2; [| exfalso; apply nth_error_None in EC2; lia].
      pose proof (proj1 (Forall_forall _ _) FC c2 (nth_error_In _ _ EC2)) as C2R. cbn beta in C2R.
      pose proof (u8ro_read usegs m1 A (zbytes content) 2 (Z_to_bv 8 c2) (Z_to_bv 64 (A + 2)) CT1 ltac:(unfold zbytes; rewrite nth_error_map, EC2; reflexivity) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD.
      zstep. zstep.
      assert (EC : calls = Z.land c2 3 + 1).
      { unfold calls, cfg. replace (0 <? L) with true by (symmetry; apply Z.ltb_lt; lia). unfold znth.
        destruct (Z.ltb_spec 2 0); [lia|]. change (Z.to_nat 2) with 2%nat. rewrite (nth_error_nth _ _ _ EC2). lia. }
      replace (bv_unsigned (Z_to_bv 8 c2)) with c2
        by (rewrite Z_to_bv_unsigned; unfold bv_wrap; symmetry; apply Z.mod_small; unfold bv_modulus; cbn; lia).
      replace (Z.land c2 3 + 1) with calls by lia.
      zstep. if_cases KP; zify_cond KP.
      + apply evt_done. eapply trun_empty; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
      + apply evt_done. eapply trun_copy; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
  Qed.
End RUN.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem ptarget_run_proof :
  rmalloc_stmt -> rfree_stmt -> fuzz_oneU_stmt ProgP.fuzz_one -> emit_printf_stmt ps_so set_so_ps -> fwritex_stdout_stmt ->
  ptarget_run_stmt.
Proof.
  intros MALLOC FREE FUZZ EMIT FWXO.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A cap L content AB lo errv.
  intros P0 INLB CT FC LC CAP L0 L6 TR0 CST0 AUX0 SPAB ABB ST0 CEIL LO ERR0 MI0 FRM SO0 -> SP16 -> -> -> ->.
  eapply (trun_main MALLOC FREE FUZZ EMIT FWXO ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m LB p A cap L content AB lo s
            INLB FC LC CAP L0 L6 SPAB ABB SP16 CEIL LO);
    [exact P0| exact CT| exact TR0| exact CST0| reflexivity| exact AUX0| exact ST0| | exact MI0| exact FRM| exact SO0| reflexivity| reflexivity| reflexivity| unfold PAY; reflexivity| unfold plen; reflexivity].
  unfold RATP, RERRNO, wz in ERR0 |- *. rewrite (unsigned_lit 597472) in ERR0 by lia. exact ERR0.
Qed.

End CANSEC1.

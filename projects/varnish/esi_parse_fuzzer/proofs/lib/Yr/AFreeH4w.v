(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtS4t2 ARt_fpo ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_fts.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].

Definition enqueue_ret : Z := 0x3b88c.      (* [comment removed for export] *)
Definition enqueue_spin : Z := 0x3b8c8.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition enqueue_frame (pad : list byte) (s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section CEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enqueue_miss_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c C sto mch size nb fb lb qb nx bsz maxc csz lo : Z) (ks : list word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    a0 = wz c -> a1 = wz C -> a2 = wz sto -> a3 = wz mch -> a4 = wz size ->
    aobj c 32 -> c + 32 <= alloc_ceiling -> aobj C 3888 -> C + 3888 <= alloc_ceiling -> C mod 16 = 0 ->
    (c + 32 <= C + 1920 \/ C + 2584 <= c) ->
    0 <= nb < 2^63 ->
    (nb <> 0 -> kHighMemBeg <= lb /\ lb + 8192 <= alloc_ceiling /\ (c + 32 <= lb \/ lb + 24 <= c) /\ (lb + 24 <= C + 1920 \/ C + 2584 <= lb)) ->
    0 <= maxc < 2^32 -> 0 <= csz < 2^64 -> length ks = 16%nat -> 0 <= size < 2^64 -> 0 <= mch < 2^64 -> 0 <= sto < 2^64 ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    (nb <> 0 -> rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)]) ->
    rw_cells rsegs m (C + 1920) [C4 (wz 0); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)] ->
    (forall (a6' a7' : word) (pad : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -64) (enqueue_frame pad s5 s4 s3 s2 s1 s0 ra) ->
        rw_cells rsegs m' c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
        rw_cells rsegs m' (C + 1920) [C4 (wz 0); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)] ->
        munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 64) ->
        evt rsegs Q (MS (mkR (wz enqueue_ret) (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (C + 1920)) (wz C)
                            (wz C) (wz (C + 1920)) (wz 0xb1d58) (wz 24) (wz size) (wz 0xb1d58) a6' a7'
                            (wz mch) (wz c) (wz sto) (wz size) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz refill_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz enqueue_entry) fc None m (seg_rom rsegs)).

Theorem enqueue_miss_pre_ok : enqueue_miss_pre_stmt.
Proof.
  unfold enqueue_miss_pre_stmt. intros until Q.
  intros MI ST LOLE CEIL A0 A1 A2 A3 A4 CLO CHI PLO PHI PAL DJ0 NBR LBF MCR CSR LKS SZ MCH STO CC LBC PC KK.
  pose proof alloc_ceiling_val as CV.
  unfold enqueue_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a0 a1 a2 a3 a4.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  destruct (Z.eq_dec nb 0) as [NB0|NB1].
  - subst nb. clear LBF LBC.
    carve_frame 64%nat ST.
    do 8 amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. if_true. (* [comment removed for export] *)
    amz. (* [comment removed for export] *) try rewrite sx32_small by lia.
    amz. if_true. (* [comment removed for export] *)
    do 12 amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    eapply KK; [exact FR| exact CC| exact PC| exact MU| exact WM| exact MI| exact ST].
  - destruct (LBF NB1) as (LLO & LHI & DJ4 & DJ5). specialize (LBC NB1). clear LBF.
    carve_frame 64%nat ST.
    do 8 amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. amz. if_false. (* [comment removed for export] *)
    amz. try rewrite sx32_small by lia.
    amz. if_true. (* [comment removed for export] *)
    do 12 amz.
    amz.
    eapply KK; [exact FR| exact CC| exact PC| exact MU| exact WM| exact MI| exact ST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enqueue_miss_oom_stmt : Prop :=
  forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sealed : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m ->
    sealed <> 0 -> 0 <= sealed < 2^64 ->
    ro_cells rsegs m 0xa91d0 [C8 (wz sealed)] ->
    ro_cells rsegs m 0xa91d8 [C8 (wz 0x146edc)] -> ro_cells rsegs m 0x146edc [C4 (wz 0)]   (* [comment removed for export] *) ->
    (forall (a0' : word),
        evt rsegs Q (MS (mkR (wz enqueue_ret) sp gp tp t0 t1 t2 s0 s1 a0' a1 s4 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz enqueue_spin) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz enqueue_ret) sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz enqueue_ret) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enqueue_miss_tail0_stmt : Prop :=
  forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp c C sto mch size fb lb qb r cnt maxc sb lo : Z) (ks : list word) (kw statv : word) (bj0 bj1 bj2 bj3 : word)
         (pad : list byte) (s5v s4v s3v s2v s1v s0v ra0 : word),
    let b := sb + 24 * 2^32 + 16 * bv_unsigned kw in
    mem_inv rsegs m -> stk rsegs m lo (usp - 64) -> lo <= usp - 64 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    r <> 0 -> 0 <= r < 2^64 ->
    aobj c 32 -> c + 32 <= alloc_ceiling -> aobj C 3888 -> C + 3888 <= alloc_ceiling -> C mod 16 = 0 ->
    (c + 32 <= C + 1920 \/ C + 2584 <= c) ->
    0 <= sb -> sb + 2^37 <= 2^47 -> kHighMemBeg <= b -> b + 8192 <= alloc_ceiling ->
    (b + 32 <= c \/ c + 32 <= b) -> (b + 32 <= C + 1920 \/ C + 2584 <= b) ->
    1 <= cnt <= 16 -> length ks = 16%nat -> nth_error ks (Z.to_nat (cnt - 1)) = Some kw -> bv_unsigned kw < 2^32 ->
    0 <= size < 2^64 -> 0 <= mch < 2^64 -> 0 <= sto < 2^64 -> 0 <= maxc < 2^32 ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] ->
    rw_cells rsegs m (usp + -64) (enqueue_frame pad s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m c [C8 (wz 0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m (C + 1920) [C4 (wz cnt); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    rw_cells rsegs m b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 64, usp); (c, c + 32); (C + 1920, C + 1924); (C + 2576, C + 2584); (b, b + 32)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
                 /\ rw_cells rsegs m' c [C8 (wz 1); C8 (wz b); C8 (wz b); C8 (wz (qb + (size + 8192)))]
                 /\ rw_cells rsegs m' (C + 1920) [C4 (wz (cnt - 1)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)]
                 /\ rw_cells rsegs m' (C + 2576) [C8 statv']
                 /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (size + 8192)); C8 (wz 1); C8 (wz mch)])
        (MS (mkR (wz enqueue_ret) (wz (usp + -64)) gp tp t0 t1 t2 (wz (C + 1920)) (wz C) (wz r) a1 a2 a3 a4 a5 a6 a7
                 (wz mch) (wz c) (wz sto) (wz size) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz enqueue_ret) fc None m (seg_rom rsegs)).

Theorem enqueue_miss_tail0_ok : enqueue_miss_tail0_stmt.
Proof.
  unfold enqueue_miss_tail0_stmt. intros until ra0. cbv zeta.
  intros MI ST LOLE CEIL UHI UAL RNZ RR CLO CHI PLO PHI PAL DJ0 SB0 SB1 BLO BHI DJ1 DJ2 CNT LKS KW KWR SZ MCH STO MCR SBC FR CC PC STA BC RA.
  pose proof alloc_ceiling_val as CV.
  unfold enqueue_ret, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  remember (sb + 24 * 2 ^ 32 + 16 * bv_unsigned kw) as b eqn:BE.
  pose proof (zr_word kw) as KW0; unfold inr64 in KW0.
  pose proof (munch_refl [(usp - 64, usp); (c, c + 32); (C + 1920, C + 1924); (C + 2576, C + 2584); (b, b + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) lazymatch goal with |- evt _ ?hotQ0 _ => set (hotQ := hotQ0) end. unfold enqueue_frame in FR.
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *) rewrite sx32_small by lia.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  do 7 amz.
  rewrite slli32_srli30 by lia.
  amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read rsegs mm (C + 1920 + 16) ks (cnt - 1) kw (wa (C + 1920 + 16 + 4 * (cnt - 1))) (pc_chunks_u32arr mm (C + 1920) _ _ _ ks PC LKS) KW ltac:(lia) eq_refl) as HR end.
  amz. (* [comment removed for export] *) rewrite (zx32_word kw KWR). clear HR.
  set (cq := C / 16) in *. assert (CQ : C = 16 * cq) by (subst cq; rewrite (Z_div_mod_eq_full C 16) at 1; rewrite PAL; lia). clearbody cq.
  assert (AL8 : (C + 2576) mod 8 = 0) by (rewrite CQ; replace (16 * cq + 2576) with ((2 * cq + 322) * 8) by lia; apply Z_mod_mult).
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  do 5 amz.
  replace (Z.shiftl (bv_unsigned kw) 4 + (sb + 103079215104)) with b by (rewrite !Z.shiftl_mul_pow2 by lia; lia).
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. if_true. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  do 9 amz.
  release_frame FR ST usp.
  replace (cnt + -1) with (cnt - 1) in PC by lia.
  (subst hotQ; finish).
  all: lazymatch goal with |- rw_cells _ ?mm ?a [C8 _] => lazymatch goal with H : rw_cells _ mm a _ |- _ => exact H end | _ => idtac end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enqueue_miss_tailF_stmt : Prop :=
  forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp c C sto mch size nb fb lb qb nx bsz r cnt maxc sb lo : Z) (ks : list word) (kw statv : word) (bj0 bj1 bj2 bj3 : word)
         (pad : list byte) (s5v s4v s3v s2v s1v s0v ra0 : word),
    let b := sb + 24 * 2^32 + 16 * bv_unsigned kw in
    mem_inv rsegs m -> stk rsegs m lo (usp - 64) -> lo <= usp - 64 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    r <> 0 -> 0 <= r < 2^64 ->
    aobj c 32 -> c + 32 <= alloc_ceiling -> aobj C 3888 -> C + 3888 <= alloc_ceiling -> C mod 16 = 0 ->
    kHighMemBeg <= lb -> lb + 8192 <= alloc_ceiling ->
    (c + 32 <= C + 1920 \/ C + 2584 <= c) -> (c + 32 <= lb \/ lb + 24 <= c) -> (lb + 24 <= C + 1920 \/ C + 2584 <= lb) ->
    0 <= sb -> sb + 2^37 <= 2^47 -> kHighMemBeg <= b -> b + 8192 <= alloc_ceiling ->
    (b + 32 <= c \/ c + 32 <= b) -> (b + 32 <= C + 1920 \/ C + 2584 <= b) -> (b + 32 <= lb \/ lb + 24 <= b) ->
    nb <> 0 -> 0 <= nb < 2^63 ->
    1 <= cnt <= 16 -> length ks = 16%nat -> nth_error ks (Z.to_nat (cnt - 1)) = Some kw -> bv_unsigned kw < 2^32 ->
    0 <= size < 2^64 -> 0 <= mch < 2^64 -> 0 <= sto < 2^64 -> 0 <= maxc < 2^32 ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] ->
    rw_cells rsegs m (usp + -64) (enqueue_frame pad s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz 1021)] ->
    rw_cells rsegs m (C + 1920) [C4 (wz cnt); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    rw_cells rsegs m b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->
    bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 64, usp); (c, c + 32); (lb, lb + 8); (C + 1920, C + 1924); (C + 2576, C + 2584); (b, b + 32)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
                 /\ rw_cells rsegs m' c [C8 (wz (nb + 1)); C8 (wz fb); C8 (wz b); C8 (wz (qb + (size + 8192)))]
                 /\ rw_cells rsegs m' lb [C8 (wz b); C8 (wz bsz); C8 (wz 1021)]
                 /\ rw_cells rsegs m' (C + 1920) [C4 (wz (cnt - 1)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)]
                 /\ rw_cells rsegs m' (C + 2576) [C8 statv']
                 /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (size + 8192)); C8 (wz 1); C8 (wz mch)])
        (MS (mkR (wz enqueue_ret) (wz (usp + -64)) gp tp t0 t1 t2 (wz (C + 1920)) (wz C) (wz r) a1 a2 a3 a4 a5 a6 a7
                 (wz mch) (wz c) (wz sto) (wz size) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz enqueue_ret) fc None m (seg_rom rsegs)).

Theorem enqueue_miss_tailF_ok : enqueue_miss_tailF_stmt.
Proof.
  unfold enqueue_miss_tailF_stmt. intros until ra0. cbv zeta.
  intros MI ST LOLE CEIL UHI UAL RNZ RR CLO CHI PLO PHI PAL LLO LHI DJ0 DJ4 DJ5 SB0 SB1 BLO BHI DJ1 DJ2 DJ3 NB NBR CNT LKS KW KWR SZ MCH STO MCR SBC FR CC LB PC STA BC RA.
  pose proof alloc_ceiling_val as CV.
  unfold enqueue_ret, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  remember (sb + 24 * 2 ^ 32 + 16 * bv_unsigned kw) as b eqn:BE.
  pose proof (zr_word kw) as KW0; unfold inr64 in KW0.
  pose proof (munch_refl [(usp - 64, usp); (c, c + 32); (lb, lb + 8); (C + 1920, C + 1924); (C + 2576, C + 2584); (b, b + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) lazymatch goal with |- evt _ ?hotQ0 _ => set (hotQ := hotQ0) end. unfold enqueue_frame in FR.
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz.
  amz. rewrite sx32_small by lia.
  amz. amz.
  do 7 amz.
  rewrite slli32_srli30 by lia.
  amz.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read rsegs mm (C + 1920 + 16) ks (cnt - 1) kw (wa (C + 1920 + 16 + 4 * (cnt - 1))) (pc_chunks_u32arr mm (C + 1920) _ _ _ ks PC LKS) KW ltac:(lia) eq_refl) as HR end.
  amz. rewrite (zx32_word kw KWR). clear HR.
  set (cq := C / 16) in *. assert (CQ : C = 16 * cq) by (subst cq; rewrite (Z_div_mod_eq_full C 16) at 1; rewrite PAL; lia). clearbody cq.
  assert (AL8 : (C + 2576) mod 8 = 0) by (rewrite CQ; replace (16 * cq + 2576) with ((2 * cq + 322) * 8) by lia; apply Z_mod_mult).
  amz. (* [comment removed for export] *)
  amz. amz.
  do 5 amz.
  replace (Z.shiftl (bv_unsigned kw) 4 + (sb + 103079215104)) with b by (rewrite !Z.shiftl_mul_pow2 by lia; lia).
  amz. br_not_taken.
  amz. amz. amz.
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz.
  amz. amz. amz.
  do 9 amz.
  release_frame FR ST usp.
  replace (cnt + -1) with (cnt - 1) in PC by lia.
  (subst hotQ; finish).
  all: lazymatch goal with |- rw_cells _ ?mm ?a [C8 _] => lazymatch goal with H : rw_cells _ mm a _ |- _ => exact H end | _ => idtac end.
Qed.

End CEIL.

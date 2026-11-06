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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASechs3 ASech8k ASecqib.

Module ASecgji.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASechs3 ASech8k.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASechs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASech8k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@NR; @AABR; @NDE; @ER; @RGE; @NS2; @LO; @K0; @CE0; @SPR; @RLT; @RU1; @H; @CF; @CF1; @ABQ; @ABR; @KL; @Kf; @B1R; @Kq])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.lia0_first := Ltac2.Init.true.
(* [comment removed for export] *)
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.
Ltac aobj_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => exact (proj1 H) end
  | match goal with K : aobjK _ _ |- _ => exact (aobjK_e _ _ K) end
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_sub _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | apply aobj_hi; kun; lia ].
Ltac pz_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_pz_in _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | unfold pz_in, kLowShadowMapBeg, kHighMemBeg; kun; lia ].

Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sides
  | |- _ /\ _ => split; sides
  | |- _ => sides1 end.

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
Section T4A8.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr AB q d e ru : Z) (oldp : byte) (Q : machine_state -> Prop).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 < e < 8.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb240d [C1 (Z_to_bv 8 1)].  (* [comment removed for export] *)
  Hypothesis SHP : rw_cells rsegs m (q + 256 + d + kShadowOffset) [C1 oldp].
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + 1)] m m1 ->
      wmono rsegs m m1 ->
      rw_cells rsegs m1 (q + 256 + d + kShadowOffset) [C1 (Z_to_bv 8 e)] ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (AB + 2048 + 8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x375c8) fc None m1 (seg_rom rsegs)).

  #[using="K SHP AF2 AF1 PCo RU8 ABR ABQ THR ER NDE NR ST MI oldp e q lo Clg"] Lemma sec_seg4_nz_a8 : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37534) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + 1)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_large n ltac:(lia)) as RSL. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    pose proof (needed_size2_secondary n ltac:(unfold kMaxPrimaryUser; lia)) as NS2.
    pose proof (round_up_4096_facts (needed_size2 n) ltac:(lia)) as [RU1 RU2]. rewrite RU8 in RU1, RU2.
    pose proof PCo as PC'. destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps).
    clear PCo. kun. unfold kHighMemEnd in Chivars.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof alloc_ceiling_val as CV.
    amz. br_not_taken. amz. amz. amz. amz. amz. change (Z.b2z (0 <? 1)) with 1.
    amz. amz. first [if_false|if_true]. amz. amz. amz. amz. amz. amz. amz. amz.
    (* [comment removed for export] *)
    assert (TAIL : forall (t0_ t1_ t2_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
      evt rsegs Q
        (MS (mkR (Z_to_bv 64 0x3753c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0_ t1_ t2_ (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 (Z_to_bv 64 2147450880) a1_ a2_ a3_ a4_ a5_ a6_ a7_
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (AB + 2048 + 8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3_ t4_ t5_ t6_)
            F (Z_to_bv 64 0x375a4) fc None m (seg_rom rsegs))).
    { intros.
      amz. amz. amz. amz.
      replace (Z.shiftr (AB + 2048 + 8 * d) 3) with (q + 256 + d).
      2:{ rewrite ABQ. replace (8 * q + 2048 + 8 * d) with (8 * (q + 256 + d)) by lia. rewrite shiftr3_mul8; lia. }
      amz. amz. amz. amz.
      replace (2147450880 + (q + 256 + d)) with (q + 256 + d + 2147450880) by lia.
      rewrite (land_land_ones7 n d e NDE) by lia.
      amz. sb_done.
      eapply K; eassumption. }
    amz. let KL := fresh "KL" in if_cases KL; zify_cond KL.
    - (* [comment removed for export] *) cbv iota. apply TAIL.
    - (* [comment removed for export] *) cbv iota. amz. amz. amz. amz. amz. amz. amz. amz. br_taken.
      amz. amz. amz. amz. amz. amz. br_not_taken. amz. br_not_taken.
      apply TAIL.
  Qed.
End T4A8.

Section T4zA8.
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (n d : Z) (Q : machine_state -> Prop).
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis NDE : n = 8 * d + 0.
  Hypothesis K : evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (8 * d)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x375c8) fc None m (seg_rom rsegs)).
  #[using="K NDE NR"] Lemma sec_seg4_z_a8 : evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (8 * d)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37534) fc None m (seg_rom rsegs)).
  Proof. amz. br_taken. exact K. Qed.
End T4zA8.

(* [comment removed for export] *)
Section T5A8.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr AB ru : Z) (v0 v1 v2 vl : word) (uj : list byte) (Q : machine_state -> Prop).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis SEP_thr : thr + 4096 <= AB \/ AB + 8 * ru <= thr.
  Hypothesis SEP_ctx : ctx + 0x10000 <= AB \/ AB + 8 * ru <= ctx.
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.
  Hypothesis TSDL : 0x10000 <= tsd /\ tsd + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF44 : ro_cells rsegs m 0xb23e4 [C4 (Z_to_bv 64 4096)].   (* [comment removed for export] *)
  Hypothesis AF52 : ro_cells rsegs m 0xb23ec [C4 (Z_to_bv 64 kMallocFillByte)].  (* [comment removed for export] *)
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STL : rw_cells rsegs m (thr + 2904) [C8 vl].
  Hypothesis USR : rw_cells rsegs m (AB + 2048) [CB 4096%nat uj].
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' v0' v1' v2' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (thr + 2800, thr + 2824); (thr + 2904, thr + 2912);
             (AB + 2048, AB + 2048 + 4096)] m m1 ->
      wmono rsegs m m1 ->
      rw_cells rsegs m1 (thr + 2800) [C8 v0'; C8 v1'; C8 v2'] ->
      rw_cells rsegs m1 (thr + 2904) [C8 (Z_to_bv 64 (bv_unsigned vl + 1))] ->
      rw_cells rsegs m1 (AB + 2048) [CB 4096%nat (fill_result canfill uj 4096%nat)] ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x3775c) fc None m1 (seg_rom rsegs)).

  #[using="K USR STL STS AF52 AF44 AF1 PCo TPL TSDL SEP_tc SEP_ctx SEP_thr RU8 ABR TSS TC FR CF NR SPR LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 uj vl v2 v1 v0 ctx tsd canfill lo Clg"] Lemma sec_seg5_a8 : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x375c8) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (thr + 2800, thr + 2824); (thr + 2904, thr + 2912);
             (AB + 2048, AB + 2048 + 4096)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_large n ltac:(lia)) as RSL. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    pose proof (needed_size2_secondary n ltac:(unfold kMaxPrimaryUser; lia)) as NS2.
    pose proof (round_up_4096_facts (needed_size2 n) ltac:(lia)) as [RU1 RU2]. rewrite RU8 in RU1, RU2.
    pose proof PCo as PC'. destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps).
    pose proof TC as TC'. destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds). pose proof Bnds as Bnds_; destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx). aobj_lin1 Bthr. aobj_lin1 Bctx. kun.
    unfold kMallocFillByte in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof alloc_ceiling_val as CV. unfold alloc_s1a_frame in FR.
    amz. callz TSS. all: sides.
    unfold off_th_stats. amz. amz. amz. amz. amz. amz. amz. amz. amz. amz. amz. amz.
    amz. br_not_taken. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    (* [comment removed for export] *)
    amz. destruct (Z.eq_dec canfill 0) as [CF0|CF1].
    - subst canfill. amz. if_false. amz. eapply K; try eassumption.
    - amz. if_cases Kf; zify_cond Kf; [clear Kf| exfalso; lia].
      amz. amz. amz. amz. if_false. amz.
      assert (FRK : fill_result canfill uj 4096%nat = repeat (Z_to_bv 8 (190 mod 256)) (Z.to_nat 4096)).
      { unfold fill_result. replace (canfill =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      amz. br_not_taken. (* [comment removed for export] *)
      amz. amz. amz. amz. amz. amz. amz.
      callz (memset_spec_z _ _ _ _ _ _ _ _ _ (AB + 2048) 190 4096). all: sides.
      rewrite FRK in K. eapply K; eassumption.
  Qed.
End T5A8.

(* [comment removed for export] *)
Section T6A8.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill thr AB ru b1v id : Z) (b0w : byte) (j0 j1 : word) (Q : machine_state -> Prop).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis RAA : bv_unsigned cra mod 2 = 0.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 64 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis LS1 : ro_cells rsegs m 0xa97d0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146680 [C8 (Z_to_bv 64 0)].
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
  Hypothesis B1R : 0 <= b1v < 256.
  Hypothesis ABH : rw_cells rsegs m AB [C8 j0; C8 j1].
  Hypothesis K : forall (m1 : word -> option byte)
                        (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2032, AB + 2034); (AB, AB + 16)] m m1 ->
      wmono rsegs m m1 ->
      rw_cells rsegs m1 (AB + 2032) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land b1v 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
      rw_cells rsegs m1 AB [C8 (Z_to_bv 64 kAllocBegMagic); C8 (Z_to_bv 64 (AB + 2032))] ->
      evt rsegs Q
        (MS (mkR cra sp gp tp t0' t1' t2' cs0 cs1
                 (Z_to_bv 64 (AB + 2048)) a1' a2' a3' a4' a5' a6' a7'
                 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3' t4' t5' t6')
            F (ret_pc cra) fc None m1 (seg_rom rsegs)).

  #[using="K ABH B1R HDR HK LS2 LS1 RU8 ABR THR TPL FR NR SPR LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 j1 j0 b0w id b1v canfill lo Clg"] Lemma sec_seg6_a8 : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3775c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2032, AB + 2034); (AB, AB + 16)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_large n ltac:(lia)) as RSL. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    pose proof (needed_size2_secondary n ltac:(unfold kMaxPrimaryUser; lia)) as NS2.
    pose proof (round_up_4096_facts (needed_size2 n) ltac:(lia)) as [RU1 RU2]. rewrite RU8 in RU1, RU2.
    kun. unfold kAllocBegMagic, CHUNK_ALLOCATED in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof alloc_ceiling_val as CV. unfold alloc_s1a_frame in FR.
    pose proof (zr_word tp) as TPR; unfold inr64 in TPR.
    (* [comment removed for export] *)
    amz. amz. amz. amz. replace (16 + bv_unsigned tp) with (bv_unsigned tp + 16) by lia.
    amz. amz. amz. amz. amz. rewrite (unsigned_lit8 b1v B1R). amz. amz. amz. amz.
    amz. sb_done. amz. amz.
    amz.
    if_cases Kq; zify_cond Kq; [exfalso; lia| clear Kq].
    amz. amz. br_not_taken. amz. amz. amz. amz. amz.
    (* [comment removed for export] *)
    amz. amz. amz.
    carve_frame 32%nat ST.
    arun_to 0x66e7c. amz.
    release_frame FR0 ST (bv_unsigned sp + -128).
    (* [comment removed for export] *)
    arun_to 0x377ec. amz.
    release_frame FR ST (bv_unsigned sp).
    eapply K; try eassumption.
  Qed.
End T6A8.
End ASecgji.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASechs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASech8k OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecqib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecr69.ASecgji.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section PT4A8.

Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr AB q d e ru : Z) (oldp : byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 < e < 8.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb240d [C1 (Z_to_bv 8 1)].  (* [comment removed for export] *)
  Hypothesis SHP : rw_cells rsegs m (q + 256 + d + kShadowOffset) [C1 oldp].
    Definition sec_seg4_nz_a8_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (AB + 2048 + 8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x375c8) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + 1)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    rw_cells rsegs m1 (q + 256 + d + kShadowOffset) [C1 (Z_to_bv 8 e)].

  #[using="SHP AF2 AF1 PCo RU8 ABR ABQ THR ER NDE NR ST MI oldp Clg"] Lemma sec_seg4_nz_a8_spec : evt rsegs sec_seg4_nz_a8_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37534) fc None m (seg_rom rsegs)).
  Proof.
    eapply sec_seg4_nz_a8; try eassumption. intros. subst. apply evt_done. unfold sec_seg4_nz_a8_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PT4A8.

Section PT4zA8.

  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (n d : Z).
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis NDE : n = 8 * d + 0.
    Definition sec_seg4_z_a8_post : machine_state -> Prop := fun ms' => ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (8 * d)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x375c8) fc None m (seg_rom rsegs)).

  #[using="NDE NR"] Lemma sec_seg4_z_a8_spec : evt rsegs sec_seg4_z_a8_post
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (8 * d)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37534) fc None m (seg_rom rsegs)).
  Proof.
    eapply sec_seg4_z_a8; try eassumption. intros. subst. apply evt_done. unfold sec_seg4_z_a8_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PT4zA8.

Section PT5A8.

Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr AB ru : Z) (v0 v1 v2 vl : word) (uj : list byte).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis SEP_thr : thr + 4096 <= AB \/ AB + 8 * ru <= thr.
  Hypothesis SEP_ctx : ctx + 0x10000 <= AB \/ AB + 8 * ru <= ctx.
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.
  Hypothesis TSDL : 0x10000 <= tsd /\ tsd + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF44 : ro_cells rsegs m 0xb23e4 [C4 (Z_to_bv 64 4096)].   (* [comment removed for export] *)
  Hypothesis AF52 : ro_cells rsegs m 0xb23ec [C4 (Z_to_bv 64 kMallocFillByte)].  (* [comment removed for export] *)
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STL : rw_cells rsegs m (thr + 2904) [C8 vl].
  Hypothesis USR : rw_cells rsegs m (AB + 2048) [CB 4096%nat uj].
    Definition sec_seg5_a8_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' v0' v1' v2' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x3775c) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (thr + 2800, thr + 2824); (thr + 2904, thr + 2912);
             (AB + 2048, AB + 2048 + 4096)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    rw_cells rsegs m1 (thr + 2800) [C8 v0'; C8 v1'; C8 v2'] /\
    rw_cells rsegs m1 (thr + 2904) [C8 (Z_to_bv 64 (bv_unsigned vl + 1))] /\
    rw_cells rsegs m1 (AB + 2048) [CB 4096%nat (fill_result canfill uj 4096%nat)].

  #[using="USR STL STS AF52 AF44 AF1 PCo TPL TSDL SEP_tc SEP_ctx SEP_thr RU8 ABR TSS TC FR CF NR SPR LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 v2 v1 v0 ctx tsd Clg"] Lemma sec_seg5_a8_spec : evt rsegs sec_seg5_a8_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x375c8) fc None m (seg_rom rsegs)).
  Proof.
    eapply sec_seg5_a8; try eassumption. intros. subst. apply evt_done. unfold sec_seg5_a8_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PT5A8.

Section PT6A8.

Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill thr AB ru b1v id : Z) (b0w : byte) (j0 j1 : word).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis RAA : bv_unsigned cra mod 2 = 0.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 64 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis LS1 : ro_cells rsegs m 0xa97d0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146680 [C8 (Z_to_bv 64 0)].
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
  Hypothesis B1R : 0 <= b1v < 256.
  Hypothesis ABH : rw_cells rsegs m AB [C8 j0; C8 j1].
    Definition sec_seg6_a8_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR cra sp gp tp t0' t1' t2' cs0 cs1
                 (Z_to_bv 64 (AB + 2048)) a1' a2' a3' a4' a5' a6' a7'
                 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3' t4' t5' t6')
            F (ret_pc cra) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2032, AB + 2034); (AB, AB + 16)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp) /\
    rw_cells rsegs m1 (AB + 2032) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land b1v 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] /\
    rw_cells rsegs m1 AB [C8 (Z_to_bv 64 kAllocBegMagic); C8 (Z_to_bv 64 (AB + 2032))].

  #[using="ABH B1R HDR HK LS2 LS1 RU8 ABR THR TPL FR NR SPR LO ST MI junk0 j1 j0 b0w canfill Clg"] Lemma sec_seg6_a8_spec : evt rsegs sec_seg6_a8_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3775c) fc None m (seg_rom rsegs)).
  Proof.
    eapply sec_seg6_a8; try eassumption. intros. subst. apply evt_done. unfold sec_seg6_a8_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PT6A8.

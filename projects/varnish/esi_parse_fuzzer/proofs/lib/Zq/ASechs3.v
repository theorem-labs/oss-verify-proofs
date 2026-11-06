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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma roundup_page_land : forall x, 0 <= x < 2^62 -> Z.land (x + 4095) 18446744073709547520 = round_up x 4096.
Proof.
  intros x Hx. change 18446744073709547520 with (2^64 - 2^12). rewrite StrFun.land_align_down by lia.
  unfold round_up. change (2^12) with 4096. replace (x + 4096 - 1) with (x + 4095) by lia.
  pose proof (Z_div_mod_eq_full (x + 4095) 4096). lia.
Qed.
Lemma roundup8_land : forall u d e, 0 <= u -> u mod 8 = 0 -> 0 <= d -> 0 <= e < 8 -> u + 8 * d + e + 7 < 2^64 ->
  Z.land (u + 8 * d + e + 7) 18446744073709551608 = u + 8 * (d + (if e =? 0 then 0 else 1)).
Proof.
  intros u d e Hu Hm Hd He Hb. rewrite land_m8 by lia.
  destruct (Z.eqb_spec e 0) as [->|NE].
  - replace (u + 8 * d + 0 + 7) with (7 + (u / 8 + d) * 8) by (pose proof (Z_div_mod_eq_full u 8); lia).
    rewrite Z.mod_add by lia. change (7 mod 8) with 7. pose proof (Z_div_mod_eq_full u 8). lia.
  - replace (u + 8 * d + e + 7) with ((e - 1) + (u / 8 + d + 1) * 8) by (pose proof (Z_div_mod_eq_full u 8); lia).
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (e - 1) 8) by lia. pose proof (Z_div_mod_eq_full u 8). lia.
Qed.
Lemma round_up_4096_facts : forall x, 0 <= x -> x <= round_up x 4096 < x + 4096 /\ round_up x 4096 mod 4096 = 0.
Proof. intros x Hx. split; [split; [apply round_up_ge | apply round_up_lt] | apply round_up_mod]; lia. Qed.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
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
Section T1a.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill : Z) (Q : machine_state -> Prop).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 128.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis NR : 64513 <= n < 2^32.
  Hypothesis SO : 0 < stkobj < 2^64.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis INI : ro_cells rsegs m 0xb5898 [C1 (Z_to_bv 8 1)].
  Hypothesis RSS : ro_cells rsegs m 0x136e22 [C1 (Z_to_bv 8 0)].
  Hypothesis K : forall (r : Z) (m1 : word -> option byte) (junk0 : list byte)
                        (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s4' s8' : word),
      r = rz_log n -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
      rw_cells rsegs m1 (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra junk0) ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 8) (Z_to_bv 64 canfill) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 r) s4' (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj) s8' (Z_to_bv 64 7) (Z_to_bv 64 (0xb1558 + 2047)) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x371e8) fc None m1 (seg_rom rsegs)).

  #[using="K RSS INI SO NR LO ST MI lo Clg"] Lemma sec_seg1a : evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xb1558) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 stkobj) (Z_to_bv 64 1) (Z_to_bv 64 canfill) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3707c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 128%nat ST.
    run_to 0x370dc. amz. br_not_taken.
    run_to 0x37114.
    Ltac rzc := unfold rz_log; repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b); try lia end.
    Ltac fin r := eapply (K r); [ rzc | eassumption | eassumption | eassumption | eassumption | eassumption ].
    (* [comment removed for export] *)
    amz. let K1 := fresh "K" in if_cases K1; zify_cond K1.
    2:{ amz. amz. fin 0. }
    amz. amz. let K2 := fresh "K" in if_cases K2; zify_cond K2.
    2:{ amz. amz. fin 1. }
    amz. amz. let K3 := fresh "K" in if_cases K3; zify_cond K3.
    2:{ amz. amz. fin 2. }
    amz. amz. amz. let K4 := fresh "K" in if_cases K4; zify_cond K4.
    2:{ amz. amz. fin 3. }
    amz. amz. amz. let K5 := fresh "K" in if_cases K5; zify_cond K5.
    2:{ amz. amz. fin 4. }
    amz. amz. amz. let K6 := fresh "K" in if_cases K6; zify_cond K6.
    2:{ amz. amz. fin 5. }
    amz. amz. amz. amz.
    destruct (Z.lt_ge_cases n 64513).
    - rewrite b2z_ltb_true by lia. change (Z.lxor 1 7) with 6. fin 6.
    - rewrite b2z_ltb_false by lia. change (Z.lxor 0 7) with 7. fin 7.
  Qed.
End T1a.

(* [comment removed for export] *)
Section T1b.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill : Z) (Q : machine_state -> Prop).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^32.
  Hypothesis RZm : ro_cells rsegs m 0xb2380 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)].
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis RZL : rzlog_stmt.
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m m1 -> wmono rsegs m m1 ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) (Z_to_bv 64 0x10000) (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj) (Z_to_bv 64 0xffff) (Z_to_bv 64 7) (Z_to_bv 64 (0xb1558 + 2047)) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37230) fc None m1 (seg_rom rsegs)).

  #[using="K RZL FR RZm NR SPR LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 lo Clg"] Lemma sec_seg1b : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 8) (Z_to_bv 64 canfill) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj) s8 (Z_to_bv 64 7) (Z_to_bv 64 (0xb1558 + 2047)) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x371e8) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_log_range n) as RZR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    do 6 amz.
    callz (rzlog_call RZL 0).
    all: sides.
    do 5 amz. callz (rzlog_call RZL 7). all: sides.
    Ltac fin := eapply K; eassumption.
    destruct (Z.eq_dec (rz_log n) 0) as [RZ0|RZ0].
    - (* [comment removed for export] *) rewrite RZ0 in *. amz. br_not_taken. amz. amz. br_not_taken. amz. amz. amz.
      let Kn := fresh "Kn" in if_cases Kn; zify_cond Kn.
      + replace (Z.max n 8) with n in K by lia. fin.
      + amz. replace (Z.max n 8) with 8 in K by lia. fin.
    - amz. br_taken. amz. 
      let K7 := fresh "K7" in if_cases K7; zify_cond K7.
      + (* [comment removed for export] *) amz. amz. amz. let Kn := fresh "Kn" in if_cases Kn; zify_cond Kn.
        * replace (Z.max n 8) with n in K by lia. fin.
        * amz. replace (Z.max n 8) with 8 in K by lia. fin.
      + (* [comment removed for export] *) amz. amz. amz. amz. replace (rz_log n) with 7 in K by lia.
        let Kn := fresh "Kn" in if_cases Kn; zify_cond Kn.
        * amz. replace (Z.max n 8) with 8 in K by lia. fin.
        * amz. replace (Z.max n 8) with n in K by lia. fin.
  Qed.
End T1b.

(* [comment removed for export] *)
Section T1c.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj tsd ctx thr : Z) (Q : machine_state -> Prop).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^32.
  Hypothesis MUM : ro_cells rsegs m 0xb2378 [C8 (Z_to_bv 64 (2^40))].
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis GT : get_thread_stmt.
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m m1 -> wmono rsegs m m1 ->
      evt rsegs Q
        (MS (mkR (Z_to_bv 64 0x3731c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 0xb1558) (Z_to_bv 64 (thr + 208)) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 8) a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x3b7fc) fc None m1 (seg_rom rsegs)).

  #[using="K GT TC MUM NR SPR LO ST MI thr ctx tsd lo Clg"] Lemma sec_seg1c : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) (Z_to_bv 64 0x10000) (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj) (Z_to_bv 64 0xffff) (Z_to_bv 64 7) (Z_to_bv 64 (0xb1558 + 2047)) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37230) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_log_range n) as RZR. pose proof (rz_log_large n ltac:(lia)) as RZS. pose proof (rz_size_large n ltac:(lia)) as RSL.
    pose proof (needed_size2_secondary n ltac:(unfold kMaxPrimaryUser; lia)) as NS2.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr & Bnds). pose proof Bnds as Bnds_; destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx). aobj_lin1 Bthr. aobj_lin1 Bctx. idtac.
    pose proof alloc_ceiling_val as CV.
    do 6 amz.
    replace (Z.land (Z.max n 8 + 7) 18446744073709551608) with (rounded_size n).
    2:{ rewrite land_m8 by lia. unfold rounded_size, round_up. replace (Z.max n 8 + 8 - 1) with (Z.max n 8 + 7) by lia.
        pose proof (Z.div_mod (Z.max n 8 + 7) 8 ltac:(lia)). lia. }
    pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT. pose proof (rounded_size_mod8 n) as RM8.
    do 4 amz.
    replace (Z.land (rounded_size n) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
    br_not_taken. amz. amz. rewrite b2z_ltb_false by lia. amz. amz. rewrite sllw_rz.
    pose proof (rz_size_range n) as RSR.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 65537 <= needed_size n < 2^33) by (unfold needed_size; lia).
    amz. amz. amz. amz. rewrite NS. amz. rewrite b2z_ltb_false by lia.
    amz. change (Z.land 1 0) with 0. amz. amz.
    rewrite (Z.land_comm 18446744073709551615 (rz_size n)). change 18446744073709551615 with (Z.ones 64).
    rewrite Z.land_ones by lia. rewrite (Z.mod_small (rz_size n) (2^64)) by lia.
    amz. amz. replace (rz_size n + needed_size n) with (needed_size2 n) by lia.
    amz. br_not_taken. amz. br_not_taken. amz. amz. br_taken.
    (* [comment removed for export] *)
    amz. callz GT. all: sides.
    amz. amz. br_not_taken. amz. amz. amz. amz.
    amz. (* [comment removed for export] *)
    eapply K; eassumption.
  Qed.
End T1c.

(* [comment removed for export] *)
Section T2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill ctx thr AB : Z) (b0w b1w : byte) (h2 w4 d8 trace sztag : word) (Q : machine_state -> Prop).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^32.
  Hypothesis SO : 0 < stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj AB (needed_size2 n) /\ AB + needed_size2 n <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_thr : thr + 4096 <= AB \/ AB + needed_size2 n <= thr.
  Hypothesis SEP_ctx : ctx + 0x10000 <= AB \/ AB + needed_size2 n <= ctx.
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.
  Hypothesis SOA : bv_unsigned sp <= stkobj.
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 trace; C8 sztag].
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2032, AB + 2048)] m m1 -> wmono rsegs m m1 ->
      rw_cells rsegs m1 (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 (b1_mid (bv_unsigned b1w))); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 d8] ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 n)
                 trace sztag a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032)) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37424) fc None m1 (seg_rom rsegs)).

  #[using="K TRC CTR CT8 TH0 HDR SOA SEP_tc SEP_ctx SEP_thr ABR ABA THR FR NR LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 sztag trace d8 w4 h2 b1w b0w ctx canfill lo Clg"] Lemma sec_seg2 : evt rsegs Q
        (MS (mkR (Z_to_bv 64 0x3731c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3731c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2032, AB + 2048)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_large n ltac:(lia)) as RSL. rewrite RSL.
    pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    pose proof (needed_size2_secondary n ltac:(unfold kMaxPrimaryUser; lia)) as NS2. unfold kHighMemBeg in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof alloc_ceiling_val as CV. unfold alloc_s1a_frame in FR.
    amz. amz. br_not_taken. amz. amz.
    replace (Z.land (AB + 2048) 7) with 0.
    2:{ symmetry. apply land7_of_mod8; [lia|]. apply mod_add_lit; [lia| | reflexivity]. apply (mod0_down AB 4096 8); [exists 512; reflexivity| exact ABA]. }
    amz. amz. br_taken. amz. amz. br_not_taken.
    (* [comment removed for export] *)
    amz. amz. amz. amz.
    amz. replace (Z.shiftr n 32) with 0 by (rewrite Z.shiftr_div_pow2, Z.div_small by lia; lia).
    amz. replace (Z.shiftr n 48) with 0 by (rewrite Z.shiftr_div_pow2, Z.div_small by lia; lia).
    amz. sb_done. amz. amz. amz. if_false. amz. amz. amz. amz. amz. sb_done.
    (* [comment removed for export] *)
    amz. br_not_taken. amz. amz. amz. amz. amz. amz.
    eapply K; eassumption.
  Qed.
End T2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

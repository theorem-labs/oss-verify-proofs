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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtS4t2 ARtSoqz ARtSb8o ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.

Module ARt3_pop.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtS4t2 ARtSoqz ARtSb8o ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_51v OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt25ye OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3_gfa OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
Lemma div_bounds0 : forall x y, 0 <= x -> 1 <= y -> 0 <= x / y <= x.
Proof. intros x y Hx Hy. split; [apply Z.div_pos; lia|]. rewrite <- (Z.div_1_r x) at 2. apply Z.div_le_compat_l; lia. Qed.
Lemma roundup_trick : forall x, 1 <= x < 2^62 ->
  Z.land (x - 1) 18446744073709289472 + 262144 = round_up x 262144.
Proof.
  intros x Hx. change 18446744073709289472 with (2^64 - 2^18). rewrite land_align_down by lia.
  unfold round_up. change (2^18) with 262144.
  replace (x + 262144 - 1) with (x - 1 + 1 * 262144) by lia. rewrite Z.div_add by lia.
  rewrite Z.mul_add_distr_r. pose proof (Z_div_mod_eq_full (x - 1) 262144). lia.
Qed.
Lemma wrap_notadd : forall t mu, 0 <= mu < t -> t < 2^64 -> (t + (18446744073709551615 - mu)) mod 18446744073709551616 = t - mu - 1.
Proof. intros t mu H1 H2. replace (t + (18446744073709551615 - mu)) with ((t - mu - 1) + 1 * 18446744073709551616) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. Qed.
Lemma mul_divu_lit : forall x y, 0 <= x < 2^64 -> 0 < y < 2^64 ->
  mul_div M_DIVU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold mul_div. rewrite unsigned_lit by lia. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_divu_unsigned, !unsigned_lit; try lia.
Qed.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 200.



Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).





Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem pop_fit_ok : pop_fit_stmt.
Proof.
  unfold pop_fit_stmt. intros until Q. cbv zeta. intros MI ST LOLE CEIL A1 A2 A3 A4 SB CR RLO RHI SB0 SB1 STR RQR NFR AU0 FIT MUR NFC AUC MUC K.
  pose proof alloc_ceiling_val as CV. unfold pop_entry, pop_efasret, efas_entry, pop_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a1 a2 a3 a4.
  pose proof (class_size_range c ltac:(lia)) as CSR. unfold kMaxSize in CSR.
  pose proof (div_bounds0 (mu - au) (class_size c) ltac:(lia) ltac:(lia)) as NCR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 64%nat ST.
  do 9 amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (J : forall (a5x a6x s3x : word),
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 stat)
                        (Z_to_bv 64 0xb1558) (Z_to_bv 64 (c ≪ 32)) (Z_to_bv 64 c) (Z_to_bv 64 au) (Z_to_bv 64 req) a5x a6x a7
                        (Z_to_bv 64 (sb + c ≪ 32)) s3x (Z_to_bv 64 mu) (Z_to_bv 64 (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x3c4c8) fc None mm (seg_rom rsegs))) end.
  { intros a5x a6x s3x.
    amz. (* [comment removed for export] *) amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *) rewrite mul_divu_lit by lia.
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    replace (sb + c ≪ 32) with (sb + c * 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^32) with 4294967296; lia).
    eapply K; [exact FR | exact MU | exact WM | assumption | exact ST]. }
  if_cases KC; zify_cond KC.
  - (* [comment removed for export] *)
    amz. replace (c + -16) with (c - 16) by lia. amz. amz. amz. try rewrite (Z.mod_small (c - 16) 18446744073709551616) by lia. amz. amz. amz. amz. amz.
    lazymatch goal with |- context [Z_to_bv 64 (Z.land ?x ?y + ?z)] => change (Z_to_bv 64 (Z.land x y + z)) with (Z_to_bv 64 (icT c)) end.
    rewrite (icT_ok c) by lia.
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    amz. br_taken. (* [comment removed for export] *)
    eapply J.
  - amz. (* [comment removed for export] *) replace (Z.shiftl c 5) with (class_size c) by (rewrite class_size_lin, Z.shiftl_mul_pow2 by lia; lia).
    amz. amz. amz. amz. amz.
    amz. br_not_taken. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    eapply J.
Qed.

Theorem pop_map_ok : pop_map_stmt.
Proof.
  unfold pop_map_stmt. intros until Q. cbv zeta. intros MI ST LOLE CEIL A1 A2 A3 A4 SB ITV PMH CR RLO RHI SB0 SB1 STR RQR NFR AUR NOFIT MUA FITS NFC AUC MUC MMC K.
  pose proof alloc_ceiling_val as CV. unfold pop_entry, pop_mapret, mapcb_entry, pop_name, kUserMap, pop_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a1 a2 a3 a4.
  pose proof (class_size_range c ltac:(lia)) as CSR. unfold kMaxSize in CSR.
  remember (round_up (au + req * class_size c - mu) 262144) as ums eqn:HU.
  assert (UMS : au + req * class_size c - mu <= ums < au + req * class_size c - mu + 262144)
    by (subst ums; split; [apply round_up_ge | apply round_up_lt]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 64%nat ST.
  do 9 amz.
  amz. amz. amz.
  amz. amz.
  amz. br_not_taken.
  amz. amz.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (J : forall (a1x a3x a5x a6x : word),
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 stat)
                        (Z_to_bv 64 0xb1558) a1x (Z_to_bv 64 c) a3x (Z_to_bv 64 req) a5x a6x a7
                        (Z_to_bv 64 (sb + c ≪ 32)) (Z_to_bv 64 (au + class_size c * req)) (Z_to_bv 64 mu) (Z_to_bv 64 (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x3c3f8) fc None mm (seg_rom rsegs))) end.
  { intros a1x a3x a5x a6x.
    amz. (* [comment removed for export] *) rewrite lxor_ones64 by lia.
    amz. amz. amz. amz. (* [comment removed for export] *)
    rewrite wrap_notadd by lia.
    amz. amz. (* [comment removed for export] *)
    replace (au + class_size c * req - mu - 1) with (au + req * class_size c - mu - 1) by lia.
    rewrite roundup_trick by lia. rewrite <- HU.
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. if_true. (* [comment removed for export] *)
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    replace (mu + (sb + c ≪ 32)) with (sb + c * 4294967296 + mu) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^32) with 4294967296; lia).
    replace (sb + c ≪ 32) with (sb + c * 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^32) with 4294967296; lia).
    eapply K; [exact FR | exact MU | exact WM | assumption | exact ST]. }
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (J0 : forall (a5x a6x : word),
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 stat)
                        (Z_to_bv 64 0xb1558) (Z_to_bv 64 (c ≪ 32)) (Z_to_bv 64 c) (Z_to_bv 64 au) (Z_to_bv 64 req) a5x a6x a7
                        (Z_to_bv 64 (sb + c ≪ 32)) (Z_to_bv 64 (au + class_size c * req)) (Z_to_bv 64 mu) (Z_to_bv 64 (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x3c3f4) fc None mm (seg_rom rsegs))) end.
  { intros a5x a6x.
    amz. (* [comment removed for export] *)
    destruct (Z.eq_dec mu 0) as [MZ|MNZ].
    - subst mu. if_true. amz. (* [comment removed for export] *) amz. if_true. (* [comment removed for export] *) amz. amz. (* [comment removed for export] *) eapply J.
    - br_not_taken. eapply J. }
  if_cases KC; zify_cond KC.
  - amz. replace (c + -16) with (c - 16) by lia. amz. amz. amz. try rewrite (Z.mod_small (c - 16) 18446744073709551616) by lia. amz. amz. amz. amz. amz.
    lazymatch goal with |- context [Z_to_bv 64 (Z.land ?x ?y + ?z)] => change (Z_to_bv 64 (Z.land x y + z)) with (Z_to_bv 64 (icT c)) end.
    rewrite (icT_ok c) by lia.
    amz. amz. amz. amz. amz.
    amz. br_not_taken. (* [comment removed for export] *)
    eapply J0.
  - amz. replace (Z.shiftl c 5) with (class_size c) by (rewrite class_size_lin, Z.shiftl_mul_pow2 by lia; lia).
    amz. amz. amz. amz. amz.
    amz. br_taken. (* [comment removed for export] *)
    eapply J0.
Qed.

End CEIL.
End ARt3_pop.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_51v OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt25ye OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3_gfa OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt34mx.ARt3_pop.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac hot_qset := lazymatch goal with |- evt _ ?Q _ => lazymatch Q with (fun _ => _) => set (hotQ := Q) | _ => idtac end | |- _ => idtac end.
Ltac hot_qend := lazymatch goal with |- evt _ ?Q _ => first [ is_var Q; subst Q | idtac ] | |- ?Q _ => first [ is_var Q; subst Q; cbv beta | idtac ] | |- _ => idtac end.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LJ; @LOLE; @NC; @HI; @CV; @SB0; @MA0; @CSR; @FITS; @AU0; @CR; @CEIL; @AUR; @UMS; @HK; @STLO; @HB; @USP; @LO0; @H; @Hi; @LCL; @BQ; @U8; @SHB; @KB; @NF0; @NFR; @NC1; @SZ; @NCM; @SB1; @SHHI; @K0; @K; @Hy; @AU; @ISZ; @DLO; @DHI; @RNZ; @Hx; @IHi; @NY; @AUH; @HNC; @NCR; @FALO; @FAHI; @RR; @TR7; @TPLO; @STAL; @RLO; @TR5])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.lia0_first := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma carve_addr : forall E i, 0 <= i -> 0 <= E - 4 - 4 * i -> E < 2^64 ->
  Z_to_bv 64 (E + Z.shiftl (18446744073709551615 - i) 2) = Z_to_bv 64 (E - 4 - 4 * i).
Proof.
  intros E i H1 H2 H3. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
  replace (E + (18446744073709551615 - i) * 4) with ((E - 4 - 4 * i) + 4 * 18446744073709551616) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma div_ge1 : forall x y, 1 <= y <= x -> 1 <= x / y.
Proof. intros x y H. apply Z.div_le_lower_bound; lia. Qed.
Lemma shr4_div16 : forall x, 0 <= x -> Z.shiftr x 4 = x / 16.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma div_mul_le : forall x y, 0 <= x -> 1 <= y -> 0 <= x / y * y <= x.
Proof. intros x y Hx Hy. pose proof (Z_div_mod_eq_full x y). pose proof (Z.mod_pos_bound x y ltac:(lia)). pose proof (Z.div_pos x y ltac:(lia) ltac:(lia)). nia. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 200.




Definition keep (P : Prop) : Prop := P.
Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac post_call_zx segs m fixup :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  rewrite ?unsigned_lit in MUc by lia;
  try rewrite ?unsigned_lit in PO by lia;
  fixup MUc; try fixup PO;
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "callzx" uconstr(SPEC) tactic3(fixup) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_call_zx segs m fixup ]
  end.

(* [comment removed for export] *)
Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- bytes_at _ _ _ _ => eassumption
  | |- mapped _ _ _ => eassumption
  | |- thread_cells _ _ _ _ _ => unfold thread_cells
  | |- poison_consts _ => unfold poison_consts
  | |- _ /\ _ => split
  | |- _ => first [eassumption | unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; plia] end).

(* [comment removed for export] *)
Ltac sidec := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- _ => first [ eassumption | reflexivity | lia
                  | (rewrite unsigned_lit by lia; first [reflexivity | lia | assumption])
                  | plia | (unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; plia) | (intros; lia) ]
  end.
Ltac post_now :=
  repeat lazymatch goal with |- @ex _ _ => eexists end;
  repeat lazymatch goal with |- _ /\ _ => split; [first [reflexivity | eassumption | apply munch_refl | apply wmono_refl] |] end;
  first [reflexivity | eassumption | apply munch_refl | apply wmono_refl].

Section PopEpi.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pop_epi : forall (ra gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo res : Z) (s6v s5v s4v s3v s2v s1v s0v ra0 : word),
    mem_inv rsegs m -> stk rsegs m lo (usp + -64) -> lo <= usp - 64 -> alloc_ceiling <= lo -> usp <= 2^47 -> 0 <= res < 2^64 ->
    rw_cells rsegs m (usp + -64) (pop_frame s6v s5v s4v s3v s2v s1v s0v ra0) ->
    bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
                 ms' = MS (mkR ra0 (Z_to_bv 64 usp) gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m (seg_rom rsegs)
                 /\ stk rsegs m lo usp)
        (MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 res) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3c564) fc None m (seg_rom rsegs)).
  Proof.
    intros until ra0. intros MI ST LOLE CEIL USP RES FR RA.
    pose proof alloc_ceiling_val as CV. unfold pop_frame in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    hot_qset.
    do 10 amz. release_frame FR ST usp. amz.
    all: hot_qend.
    hot_qend; apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity | exact ST].
  Qed.
End PopEpi.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End CEIL.

Section Carve.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (dst au size nc : Z) (junk : list word) (Q : machine_state -> Prop).
  Hypotheses (LJ : length junk = Z.to_nat nc) (NC : 1 <= nc < 2^27) (SZ : 1 <= size <= 65536) (AU : 0 <= au) (AUH : au + nc * size < 2^40)
             (DLO : kHighMemBeg <= dst) (DHI : dst + 4 * nc <= alloc_ceiling).
  Definition cp (j : Z) : word := Z_to_bv 64 ((au + j * size) / 16).
  Fixpoint tops (i : nat) : list word := match i with O => [] | S i' => cp (Z.of_nat i') :: tops i' end.
  #[using="NC LJ junk nc"] Lemma tops_length : forall i, length (tops i) = i. Proof. induction i; cbn; lia. Qed.
  Definition cl (i : Z) : list word := firstn (Z.to_nat (nc - i)) junk ++ tops (Z.to_nat i).
  #[using="SZ NC LJ"] Lemma cl_length : forall i, 0 <= i <= nc -> length (cl i) = Z.to_nat nc.
  Proof. intros i Hi. unfold cl. rewrite app_length, firstn_length, tops_length. lia. Qed.
  #[using="SZ NC LJ"] Lemma cl_step : forall i, 0 <= i < nc -> upd (cl i) (Z.to_nat (nc - 1 - i)) (cp i) = cl (i + 1).
  Proof.
    intros i Hi. unfold cl.
    destruct (nth_error junk (Z.to_nat (nc - 1 - i))) as [y|] eqn:NY; [| apply nth_error_None in NY; lia].
    replace (Z.to_nat (nc - i)) with (S (Z.to_nat (nc - 1 - i))) by lia.
    rewrite (firstn_S_nth_error junk _ y NY), <- app_assoc. cbn [app].
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. cbn [tops]. rewrite Z2Nat.id by lia.
    replace (Z.to_nat (nc - (i + 1))) with (Z.to_nat (nc - 1 - i)) by lia.
    pose proof (firstn_length_le junk (n:=Z.to_nat (nc - 1 - i)) ltac:(lia)) as LF.
    rewrite <- LF at 2. apply upd_app_len.
  Qed.
  #[using="LJ junk nc"] Lemma tops_map : forall n, tops n = map (fun j => cp (Z.of_nat n - 1 - Z.of_nat j)) (seq 0 n).
  Proof.
    induction n as [|n IH]; [reflexivity|].
    cbn [tops]. rewrite <- cons_seq. cbn [map]. f_equal; [f_equal; lia|].
    rewrite <- seq_shift, map_map, IH. apply map_ext_in. intros j _. f_equal. lia.
  Qed.
  #[using="NC LJ junk"] Lemma tops_carved : tops (Z.to_nat nc) = carved au size nc.
  Proof. unfold carved. rewrite tops_map. apply map_ext_in. intros j _. unfold cp. f_equal. f_equal. f_equal. lia. Qed.

  Definition cst3 (i : Z) (a4 a5 : word) (pc : Z) (m : word -> option byte) : machine_state :=
    MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 (dst + 4 * nc)) (Z_to_bv 64 (au + i * size)) a3 a4 a5 a6 a7
            s2 (Z_to_bv 64 nc) s4 (Z_to_bv 64 size) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).
  #[using="DHI DLO AUH AU SZ NC LJ Clg"] Lemma carve_loop : forall (k : nat) (i : Z) m (a4 a5 : word),
    Z.of_nat k = nc - i -> 0 <= i < nc ->
    mem_inv rsegs m -> u32arr rsegs m dst (cl i) ->
    (forall m' (a4' a5' : word), mem_inv rsegs m' -> u32arr rsegs m' dst (cl nc) ->
        munch [(dst, dst + 4 * nc)] m m' -> wmono rsegs m m' -> evt rsegs Q (cst3 nc a4' a5' 0x3c530 m')) ->
    evt rsegs Q (cst3 i a4 a5 0x3c510 m).
  Proof.
    induction k as [|k IH]; intros i m a4 a5 HK HI MI DA K; [lia|].
    unfold cst3. pose proof alloc_ceiling_val as CV. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
    pose proof (munch_refl [(dst, dst + 4 * nc)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (ISZ : 0 <= i * size <= nc * size - size) by nia.
    amz. (* [comment removed for export] *) rewrite shr4_div16 by lia.
    amz. (* [comment removed for export] *) rewrite lxor_ones64 by lia.
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *) rewrite carve_addr by lia. replace (dst + 4 * nc - 4 - 4 * i) with (dst + 4 * (nc - 1 - i)) by lia.
    pose proof (cl_length i ltac:(lia)) as LCL.
    pose proof (u32arr_store_ok rsegs m dst (cl i) (nc - 1 - i) (Z_to_bv 64 (dst + 4 * (nc - 1 - i))) DA ltac:(rewrite LCL; lia) ltac:(unfold wa; reflexivity)) as SOK.
    amz. (* [comment removed for export] *)
    change (write_to_mem m (Z_to_bv 64 (dst + 4 * (nc - 1 - i))) (le4 (Z_to_bv 64 ((au + i * size) / 16))))
      with (write_to_mem m (wa (dst + 4 * (nc - 1 - i))) (le4 (cp i))).
    pose proof (u32arr_write rsegs m dst (cl i) (nc - 1 - i) (cp i) DA ltac:(rewrite LCL; lia)) as DA2. clear DA.
    rewrite (cl_step i) in DA2 by lia.
    store_done.
    amz. (* [comment removed for export] *) replace (au + i * size + size) with (au + (i + 1) * size) by lia.
    amz. (* [comment removed for export] *)
    lazymatch goal with H : mem_inv rsegs ?mm |- _ => rename H into MI2 end.
    if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
    - apply (IH (i + 1)); [lia | lia | exact MI2 | exact DA2 |].
      intros m' a4' a5' MI' DA' MU' WM'. apply K; [exact MI' | exact DA' | eapply munch_trans; [exact MU | exact MU'] | eapply wmono_trans; [exact WM | exact WM']].
    - unfold cst3 in K. replace (i + 1) with nc by lia. replace (i + 1) with nc in DA2 by lia.
      apply K; [exact MI2 | exact DA2 | exact MU | exact WM].
  Qed.
End Carve.

Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem pop_carve_ok : pop_carve_stmt.
Proof.
  unfold pop_carve_stmt. intros until ra0. cbv zeta.
  intros MI ST LOLE CEIL USP UAL CR RLO RHI SB0 SB1 SBA NF0 NFR AU0 MA0 FITS AUA RNZ RR LJ DJ FR NFC AUC EXC DST RA.
  pose proof alloc_ceiling_val as CV. unfold pop_efasret, pop_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  pose proof (class_size_range c ltac:(lia)) as CSR. unfold kMaxSize in CSR.
  remember (free_array_of sb c) as fa eqn:HFA.
  assert (FAR : sb <= fa + 4 * nf /\ fa + 4 * (nf + ma / class_size c) <= sb + 2^37) by (subst fa; unfold free_array_of; lia).
  destruct FAR as [FALO FAHI].
  pose proof (div_bounds0 ma (class_size c) ltac:(lia) ltac:(lia)) as NCR.
  pose proof (div_mul_le ma (class_size c) ltac:(lia) ltac:(lia)) as NCM.
  remember (ma / class_size c) as nc eqn:HNC.
  replace (usp - 64) with (usp + -64) in ST by lia.
  pose proof (munch_refl [(usp - 64, usp); (R + 16, R + 24); (R + 32, R + 40); (R + 68, R + 69); (fa + 4 * nf, fa + 4 * nf + 4 * nc)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ ?P _ =>
  assert (TL : forall (a0x a1x a2x a4x a5x s1x : word) m1,
    mem_inv rsegs m1 -> u32arr rsegs m1 (fa + 4 * nf) (carved au (class_size c) nc) ->
    munch [(usp - 64, usp); (R + 16, R + 24); (R + 32, R + 40); (R + 68, R + 69); (fa + 4 * nf, fa + 4 * nf + 4 * nc)] m m1 -> wmono rsegs m m1 ->
    rw_cells rsegs m1 (usp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    rw_cells rsegs m1 (R + 16) [C8 (Z_to_bv 64 nf)] ->
    rw_cells rsegs m1 (R + 32) [C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (au + ma)); C8 (Z_to_bv 64 0)] ->
    rw_cells rsegs m1 (R + 68) [C1 ex] -> stk rsegs m1 lo (usp + -64) ->
    evt rsegs P (MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 R) s1x a0x a1x a2x (Z_to_bv 64 (au + 0 * class_size c)) a4x a5x a6 a7
                        (Z_to_bv 64 (sb + c * 4294967296)) (Z_to_bv 64 nc) (Z_to_bv 64 ma) (Z_to_bv 64 (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x3c530) fc None m1 (seg_rom rsegs))) end.
  { intros a0x a1x a2x a4x a5x s1x m1 MI1 DA1 MU1 WM1 FR1 NFC1 AUC1 EXC1 ST1. clear MI FR NFC AUC EXC DST ST MU WM.
    replace (au + 0 * class_size c) with au by lia.
    apply CB_of_u32arr in DA1. unfold carved in DA1 at 1. rewrite map_length, seq_length in DA1.
    replace (4 * Z.to_nat nc)%nat with (Z.to_nat (4 * nc)) in DA1 by lia.
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    eapply evt_mono; [eapply pop_epi; try eassumption; lia |].
    intros ms' PO. destruct_exs PO. destruct PO as [-> ST'].
    apply u32arr_of_CB in DA1. fold (carved au (class_size c) nc) in DA1.
    post_now.
  }
  if_cases KB; zify_cond KB.
  - (* [comment removed for export] *)
    assert (NC0 : nc = 0) by (subst nc; apply Z.div_small; lia).
    rewrite NC0 in *. destruct junk; [| cbn in LJ; lia].
    replace (Z_to_bv 64 au) with (Z_to_bv 64 (au + 0 * class_size c)) by (f_equal; lia).
    eapply TL; try eassumption.
  - (* [comment removed for export] *)
    assert (NC1 : 1 <= nc) by (subst nc; apply div_ge1; lia).
    amz. amz. amz. amz. (* [comment removed for export] *)
    replace (sb + c * 4294967296 + 3758096384) with fa by (subst fa; unfold free_array_of; lia).
    amz. amz. (* [comment removed for export] *)
    replace (fa + (nf + nc) ≪ 2) with (fa + 4 * nf + 4 * nc) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    amz. (* [comment removed for export] *)
    replace (Z_to_bv 64 au) with (Z_to_bv 64 (au + 0 * class_size c)) by (f_equal; lia).
    eapply (carve_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fa + 4 * nf) au (class_size c) nc junk) with (i := 0) (k := Z.to_nat nc);
      try eassumption; try (unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; plia).
    { unfold cl. replace (nc - 0) with nc by lia. cbn [tops Z.to_nat]. rewrite <- LJ, firstn_all, app_nil_r. exact DST. }
    intros m' a4' a5' MI' DA' MU' WM'. unfold cst3.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST); transport_after_call rsegs m m' MU' WM'.
    eapply TL; try eassumption.
    unfold cl in DA'. rewrite Z.sub_diag in DA'. change (Z.to_nat 0) with 0%nat in DA'. cbn [firstn app] in DA'.
    erewrite (tops_carved au (class_size c) nc) in DA'; [exact DA' | try eassumption; lia ..].
Qed.

Theorem pop_mapped_ok : pop_mapped_stmt.
Proof.
  unfold pop_mapped_stmt. intros PS TS. intros until Q. cbv zeta.
  intros MI ST LOLE CEIL USP UAL CR RLO RHI SB0 SB1 SBA STLO STHI STAL RQR NFR AUR BAL UMS UAL8 FITS FIT2 PC TC TPLO TSDLO DJ1 DJ2 DJ3 FR NFC AUC MUC SHC THS STC K.
  pose proof alloc_ceiling_val as CV. unfold pop_mapret, pop_efasret, efas_entry, pop_frame, kUserMap, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, off_th_stats in *. aobj_lin_all. unfold kShadowOffset in TPLO, TSDLO.
  pose proof (class_size_range c ltac:(lia)) as CSR. unfold kMaxSize in CSR.
  remember (sb + c * 4294967296 + mu) as beg eqn:HB.
  (* [comment removed for export] *)
  set (bq := beg / 8) in *. assert (BQ : beg = 8 * bq) by (subst bq; rewrite (Z_div_mod_eq_full beg 8) at 1; rewrite BAL; lia). clearbody bq.
  set (u8 := ums / 8) in *. assert (U8 : ums = 8 * u8) by (subst u8; rewrite (Z_div_mod_eq_full ums 8) at 1; rewrite UAL8; lia). clearbody u8.
  assert (SHB : sh beg = bq + 2147450880) by (unfold sh, kShadowOffset; rewrite BQ, Z.mul_comm, Z.div_mul by lia; lia).
  rewrite SHB in *.
  assert (SHHI : bq + 2147450880 + u8 <= 17594333495296) by lia.
  replace (usp - 64) with (usp + -64) in ST by lia.
  replace (thr + 2800 + 72) with (thr + 2872) in * by lia. replace (thr + 2800 + 88) with (thr + 2888) in * by lia.
  pose proof (munch_refl [(usp - 64 - 64, usp - 64); (bq + 2147450880, bq + 2147450880 + u8); (thr + 2872, thr + 2888);
               (stat + 24, stat + 32); (R + 48, R + 56)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  pose proof TC as TC0. unfold thread_cells in TC. (first [ dand6 TC as T1 T2 T3 T4 T5 TR | destruct TC as (T1 & T2 & T3 & T4 & T5 & TR) ]). unfold kHighMemBeg in TR. aobj_lin_all.
  (first [ dand8 TR as TR1 TR2 TR3 TR4 TR5 TR6 TR7 TR8 | destruct TR as (TR1 & TR2 & TR3 & TR4 & TR5 & TR6 & TR7 & TR8) ]). aobj_lin_all.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  callzx (PS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ beg ums 250 lo old) (fun H => rewrite ?SHB in H; replace (ums / 8) with u8 in H by (rewrite U8, Z.mul_comm, Z.div_mul by lia; reflexivity)).
  all: try (rewrite SHB). all: try sidec.
  1: { replace (ums / 8) with u8 by (rewrite U8, Z.mul_comm, Z.div_mul by lia; reflexivity). exact SHC. }
  (* [comment removed for export] *)
  lazymatch goal with H : bytes_at rsegs ?mm (bq + 2147450880) _ |- _ =>
    rename H into SHP; change (keep ltac:(lazymatch type of SHP with ?t => exact t end)) in SHP || idtac;
    pose proof (munch_refl [(usp - 64 - 64, usp - 64); (thr + 2872, thr + 2888); (stat + 24, stat + 32); (R + 48, R + 56)] mm) as MU2;
    pose proof (wmono_refl rsegs mm) as WM2 end.

  (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  callz (TS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tsd ctx thr lo).
  all: try sidec.
  all: lazymatch goal with |- evt _ _ _ => idtac | _ => rebundle end.
  unfold off_th_stats.
  amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. rewrite mul_divu_lit by lia.
  amz. amz. amz. amz. amz.
  eapply K; try eassumption.
  - unfold keep in SHP. eapply bytes_at_transport; [exact SHP | exact MU2 | cbn [disjoint_from]; rewrite repeat_length; lia].
  - eexists; eassumption.
Qed.

End CEIL2.

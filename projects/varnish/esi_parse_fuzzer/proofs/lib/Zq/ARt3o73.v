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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtS4t2 ARtSoqz ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.

Module ARt25ye.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
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
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition icT (k : Z) : Z :=
  Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl k 63))) 63 mod 18446744073709551616)
         (Z.shiftr ((Z.shiftl 512 ((Z.shiftr (k - 16) 1) mod 64)) mod 18446744073709551616) 1)
  + Z.shiftl 512 ((Z.shiftr (k - 16) 1) mod 64).
Lemma icT_ok : forall k, 17 <= k <= 30 -> icT k = class_size k.
Proof.
  intros k Hk. pose proof (zall_spec 17 30 (fun k => icT k =? class_size k) eq_refl k Hk) as H. apply Z.eqb_eq in H. exact H.
Qed.
Definition icD (k : Z) : Z := 1024 / class_size k.
Lemma divuw_cs : forall k, 1 <= k <= 31 -> v_divuw (Z_to_bv 64 1024) (Z_to_bv 64 (class_size k)) = Z_to_bv 64 (icD k).
Proof.
  intros k Hk. unfold v_divuw, icD. rewrite !Z_to_bv_unsigned.
  pose proof (zall_spec 1 31 (fun k => negb (bv_wrap 32 (bv_wrap 64 (class_size k)) =? 0) &&
     (bv_swrap 32 (bv_wrap 32 (bv_wrap 64 1024) / bv_wrap 32 (bv_wrap 64 (class_size k))) =? 1024 / class_size k)) eq_refl k Hk) as H.
  cbn beta in H. apply andb_prop in H as [H1 H2]. apply negb_true_iff in H1. rewrite H1. apply Z.eqb_eq in H2. rewrite H2. reflexivity.
Qed.
Lemma class_size_lin : forall k, 1 <= k <= 16 -> class_size k = 32 * k.
Proof. intros k Hk. unfold class_size, kBatchClassID, kMidClass, kMinSize. destruct (Z.eqb_spec k 31); [lia|]. destruct (Z.leb_spec k 16); lia. Qed.
Lemma divuw_lin : forall k, 1 <= k <= 16 -> v_divuw (Z_to_bv 64 1024) (Z_to_bv 64 (32 * k)) = Z_to_bv 64 (icD k).
Proof. intros k Hk. rewrite <- class_size_lin by lia. apply divuw_cs. lia. Qed.
Lemma icD_facts : forall k, 1 <= k <= 31 ->
   0 <= icD k <= 32 /\ ((k <= 4 \/ k = 31) /\ 8 <= icD k /\ max_count k = 16 \/
                        5 <= k <= 30 /\ icD k < 8 /\ Z.shiftl ((icD k + Z.b2z (icD k <? 1)) mod 18446744073709551616) 1 = max_count k).
Proof.
  intros k Hk.
  pose proof (zall_spec 1 31 (fun k => (0 <=? icD k) && (icD k <=? 32) &&
     ((((k <=? 4) || (k =? 31)) && (8 <=? icD k) && (max_count k =? 16)) ||
      ((5 <=? k) && (k <=? 30) && (icD k <? 8) && (Z.shiftl ((icD k + Z.b2z (icD k <? 1)) mod 18446744073709551616) 1 =? max_count k)))) eq_refl k Hk) as H.
  cbn beta in H. lia.
Qed.
Lemma Z_to_bv_add_mod : forall z, Z_to_bv 64 (z + 18446744073709551616) = Z_to_bv 64 z.
Proof.
  intros z. rewrite <- (Z_to_bv_mod64 (z + _)). rewrite <- (Z_to_bv_mod64 z). f_equal. change (2^64) with 18446744073709551616.
  rewrite <- Zplus_mod_idemp_r. rewrite Z_mod_same_full. f_equal. lia.
Qed.
(* [comment removed for export] *)
Definition a5of (k : Z) : Z := if k <? 16 then 18446744073709551600 + k else k - 16.
Lemma a5of_spec : forall k, (k < 16 /\ a5of k = 18446744073709551600 + k) \/ (16 <= k /\ a5of k = k - 16).
Proof. intros k. unfold a5of. destruct (Z.ltb_spec k 16); lia. Qed.
Lemma a5of_step : forall k, Z_to_bv 64 (a5of k + 1) = Z_to_bv 64 (a5of (k + 1)).
Proof.
  intros k. unfold a5of. destruct (Z.ltb_spec k 16), (Z.ltb_spec (k + 1) 16); try (f_equal; lia).
  replace (18446744073709551600 + k + 1) with ((k + 1 - 16) + 18446744073709551616) by lia. apply Z_to_bv_add_mod.
Qed.
Lemma a5of_t4 : forall k, Z_to_bv 64 (a5of k + 16) = Z_to_bv 64 k.
Proof.
  intros k. unfold a5of. destruct (Z.ltb_spec k 16); [| f_equal; lia].
  replace (18446744073709551600 + k + 16) with (k + 18446744073709551616) by lia. apply Z_to_bv_add_mod.
Qed.
Lemma max_count_range31 : forall k, 1 <= k <= 31 -> 0 <= max_count k < 2^32.
Proof. intros k Hk. pose proof (zall_spec 1 31 (fun k => (0 <=? max_count k) && (max_count k <? 2^32)) eq_refl k Hk) as H. cbn beta in H. lia. Qed.
Lemma class_size_range31 : forall k, 1 <= k <= 31 -> 0 <= class_size k < 2^64.
Proof. intros k Hk. pose proof (zall_spec 1 31 (fun k => (0 <=? class_size k) && (class_size k <? 2^64)) eq_refl k Hk) as H. cbn beta in H. lia. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition keep (P : Prop) : Prop := P.

Section IC.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (C : Z) (cnt mc0 cs0 : Z -> Z) (ks : Z -> list word) (Q : machine_state -> Prop) (m0 : word -> option byte).
  Hypotheses (CLO : aobj C 3888) (CHI : C + 3888 <= alloc_ceiling).   (* [comment removed for export] *)
  Hypothesis (CELLS : forall i, 1 <= i <= 31 -> 0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (ks i) = 16%nat /\
       rw_cells rsegs m0 (C + 80 * i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 (mc0 i)); C8 (Z_to_bv 64 (cs0 i)); CB 64 (u32s (ks i))]).
  Hypothesis (KEXIT : forall (t3' t4' t5' : word) (m' : word -> option byte),
        (forall i, 1 <= i <= 31 ->
           rw_cells rsegs m' (C + 80 * i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 (max_count i)); C8 (Z_to_bv 64 (class_size i)); CB 64 (u32s (ks i))]) ->
        munch [(C + 80, C + 2560)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' ->
        evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 (C + 2568)) a2 (Z_to_bv 64 1024) a4
                            (Z_to_bv 64 16) (Z_to_bv 64 15) (Z_to_bv 64 1024)
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (Z_to_bv 64 initcache_blk_exit) fc None m' (seg_rom rsegs))).

  Definition icst (k : Z) (t3 t4 t5 : word) (m : word -> option byte) : machine_state :=
    MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 (C + 8 + 80 * k)) a2 (Z_to_bv 64 (32 * k)) a4
            (Z_to_bv 64 (a5of k)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3bff0) fc None m (seg_rom rsegs).
  Definition IC (k : Z) (m : word -> option byte) : Prop :=
    (forall j, 1 <= j < k -> rw_cells rsegs m (C + 80 * j) [C4 (Z_to_bv 64 (cnt j)); C4 (Z_to_bv 64 (max_count j)); C8 (Z_to_bv 64 (class_size j)); CB 64 (u32s (ks j))]) /\
    (forall j, k <= j <= 31 -> rw_cells rsegs m (C + 80 * j) [C4 (Z_to_bv 64 (cnt j)); C4 (Z_to_bv 64 (mc0 j)); C8 (Z_to_bv 64 (cs0 j)); CB 64 (u32s (ks j))]).

  (* [comment removed for export] *)
  #[using="KEXIT CELLS CLO Clg"] Lemma ic_loop : forall (n : nat) k t3 t4 t5 m, n = Z.to_nat (31 - k) -> 1 <= k <= 31 ->
      mem_inv rsegs m -> IC k m -> munch [(C + 80, C + 2560)] m0 m -> wmono rsegs m0 m ->
      evt rsegs Q (icst k t3 t4 t5 m).
  Proof.
    induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf).
    intros k t3 t4 t5 m HN HK MI [ICa ICb] MU WM. unfold icst. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS. pose proof alloc_ceiling_val as CV.
    pose proof (ICb k ltac:(lia)) as PC. (first [ pose proof ((CELLS k ltac:(lia))) as dR_1; dand5 dR_1 as CR MR SR LK _ | pose proof (CELLS k ltac:(lia)) as (CR & MR & SR & LK & _) ]).
    pose proof (max_count_range31 k ltac:(lia)) as MCR. pose proof (class_size_range31 k ltac:(lia)) as CSR.
    remember (C + 80 * k) as ck eqn:CK.
    replace (C + 8 + 80 * k) with (ck + 8) by lia.
    change (IC k m) with (keep (IC k m)) in *.
    assert (ICK : keep (IC k m)) by (split; assumption). clear ICa ICb.
    pose proof (munch_refl [(ck, ck + 80)] m) as MU2. pose proof (wmono_refl rsegs m) as WM2.
    pose proof (icD_facts k ltac:(lia)) as [DR DF]. pose proof (a5of_spec k) as A5.
    (* [comment removed for export] *)
    assert (TAIL : forall (d csv : Z) (t5x : word),
      0 <= d < 2^32 -> csv = class_size k -> Z.shiftl ((d + Z.b2z (d <? 1)) mod 18446744073709551616) 1 = max_count k ->
      evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 (ck + 8)) a2 (Z_to_bv 64 (32 * k)) a4
            (Z_to_bv 64 (a5of k)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 csv) (Z_to_bv 64 d) t5x t6)
            F (Z_to_bv 64 0x3bfcc) fc None m (seg_rom rsegs))).
    { intros d csv t5x DR2 CSV DMC. subst csv.
      amz. amz. amz. rewrite a5of_step. amz. amz. rewrite DMC.
      amz. (* [comment removed for export] *)
      amz. (* [comment removed for export] *)
      amz. (* [comment removed for export] *)
      amz. (* [comment removed for export] *)
      pose proof (a5of_spec (k + 1)) as A5'.
      destruct (Z.eq_dec k 31) as [K31|KN].
      - br_taken. subst k.
        replace (ck + 88) with (C + 2568) by lia. replace (a5of (31 + 1)) with 16 by reflexivity.
        unfold initcache_blk_exit in KEXIT. eapply KEXIT.
        + intros i Hi. unfold keep in ICK. destruct ICK as [ICa ICb].
          destruct (Z.eq_dec i 31) as [->|NE].
          * lazymatch goal with H : rw_cells _ _ ck _ |- _ => rewrite CK in H; exact H end.
          * eapply rw_cells_transport; [eapply ICa; lia | exact MU2 | exact WM2 | cbn; lia].
        + lazymatch goal with H : munch [(C + 80, C + 2560)] m0 _ |- _ => exact H end.
        + lazymatch goal with H : wmono rsegs m0 _ |- _ => exact H end.
        + assumption.
      - br_not_taken.
        replace (ck + 88) with (C + 8 + 80 * (k + 1)) by lia. replace (32 * k + 32) with (32 * (k + 1)) by lia.
        eapply (IH (Z.to_nat (31 - (k + 1)))); [lia | reflexivity | lia | assumption | | | ].
        + unfold keep in ICK. destruct ICK as [ICa ICb]. split; intros j Hj.
          * destruct (Z.eq_dec j k) as [->|NE].
            -- lazymatch goal with H : rw_cells _ _ ck _ |- _ => rewrite CK in H; exact H end.
            -- eapply rw_cells_transport; [eapply ICa; lia | exact MU2 | exact WM2 | cbn; lia].
          * eapply rw_cells_transport; [eapply ICb; lia | exact MU2 | exact WM2 | cbn; lia].
        + lazymatch goal with H : munch [(C + 80, C + 2560)] m0 _ |- _ => exact H end.
        + lazymatch goal with H : wmono rsegs m0 _ |- _ => exact H end. }
    (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    destruct (Z.eq_dec k 31) as [K31|KN31].
    - br_taken. (* [comment removed for export] *)
      amz. amz. replace (Z_to_bv 64 64) with (Z_to_bv 64 (class_size k)) by (subst k; reflexivity). rewrite divuw_cs by lia.
      amz. amz. br_not_taken. amz. amz. amz.
      eapply TAIL; [lia| reflexivity |]. subst k. destruct DF as [(_ & _ & E)|(? & _)]; [rewrite E; reflexivity| plia].
    - br_not_taken.
      amz. rewrite a5of_t4. amz.
      amz. (* [comment removed for export] *)
      destruct (Z.le_gt_cases k 16) as [KS|KB].
      + br_taken. amz. rewrite divuw_lin by lia. amz. amz.
        destruct (Z.le_gt_cases k 4) as [K4|K5].
        * br_not_taken. amz. amz. eapply TAIL; [lia| symmetry; apply class_size_lin; lia |]. destruct DF as [(_ & _ & E)|(? & _)]; [rewrite E; reflexivity| plia].
        * br_taken. eapply TAIL; [lia| symmetry; apply class_size_lin; lia |]. destruct DF as [(? & _)|(_ & _ & E)]; [lia| exact E].
      + br_not_taken.
        amz. replace (Z.shiftr (a5of k) 1) with (Z.shiftr (k - 16) 1) by (f_equal; lia).
        amz. amz. amz. amz. amz. amz.
        lazymatch goal with |- context [Z_to_bv 64 (Z.land ?x ?y + ?z)] => change (Z_to_bv 64 (Z.land x y + z)) with (Z_to_bv 64 (icT k)) end.
        rewrite (icT_ok k) by lia.
        amz. rewrite (divuw_cs k) by lia.
        amz. amz. br_taken.
        eapply TAIL; [lia| reflexivity |]. destruct DF as [(? & _)|(_ & _ & E)]; [lia| exact E].
  Qed.
End IC.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem initcache_blk_ok : initcache_blk_stmt.
Proof.
  unfold initcache_blk_stmt. intros until Q. intros MI CLO CHI CELLS KEXIT.
  unfold initcache_blk_entry in *. pose proof alloc_ceiling_val as CV. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
  do 8 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  replace (C + 88) with (C + 8 + 80 * 1) by lia.
  change (Z_to_bv 64 32) with (Z_to_bv 64 (32 * 1)).
  replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 (a5of 1)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
  eapply ic_loop with (k := 1) (m0 := m) (mc0 := mc0) (cs0 := cs0) (n := Z.to_nat 30).
  all: try (split; intros j Hj; [lia| apply (CELLS j); lia]).
  all: lazymatch goal with
       | |- munch _ _ _ => apply munch_refl
       | |- wmono _ _ _ => apply wmono_refl
       | |- _ => first [eassumption | reflexivity | plia]
       end.
Qed.

End CEIL.
End ARt25ye.


Module ARt3_gfa.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtS4t2 ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_51v OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem gfa_lock_ok : gfa_lock_stmt.
Proof.
  unfold gfa_lock_stmt. intros until Q. intros MI ST LOLE CEIL A0 A2 SB RI CR RLO RHI RAL SB0 SB1 MX K.
  pose proof alloc_ceiling_val as CV. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, gfa_entry, gfa_locked, kMutexWriter, free_array_of, gfa_frame in *. aobj_lin_allS. subst a0 a2.
  remember (ri + 128 * c) as R eqn:HR.
  set (rq := ri / 128) in *. assert (RQ : ri = 128 * rq) by (subst rq; rewrite (Z_div_mod_eq_full ri 128) at 1; rewrite RAL; lia). clearbody rq.
  assert (RAL8 : R mod 8 = 0) by (rewrite HR, RQ; replace (128 * rq + 128 * c) with ((16 * rq + 16 * c) * 8) by lia; apply Z_mod_mult).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (R, R + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 128%nat ST.
  do 30 amz.
  replace (ri + c ≪ 7) with R by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia).
  run_to 0x3c0f4.
  amz. (* [comment removed for export] *)
  amz. br_not_taken.
  scstep; zsimp. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  amz. if_true. (* [comment removed for export] *)
  replace (sb + (c ≪ 32 + 3758096384)) with (sb + c * 4294967296 + 3758096384) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^32) with 4294967296; lia).
  eapply K.
  - exact MX.
  - exact FR.
  - exact MU.
  - exact WM.
  - assumption.
  - exact ST.
Qed.

End CEIL.

Section Tail.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (usp lo R : Z) (scr : list byte) (s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word).
  Hypotheses (LOLE : lo <= usp - 128) (CEIL : alloc_ceiling <= lo) (USP : usp <= 2^47) (UAL : usp mod 16 = 0)
             (RLO : kHighMemBeg <= R) (RHI : R + 128 <= alloc_ceiling) (RAL8 : R mod 8 = 0) (RA : bv_unsigned ra0 mod 2 = 0).

  (* [comment removed for export] *)
  #[using="RAL8 RHI RLO CEIL LOLE Clg"] Lemma gfa_unlock_tail : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (res : Z) m (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp - 128) -> 0 <= res < 2^64 ->
    rw_cells rsegs m (usp + -128) (gfa_frame scr s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m R [C8 (Z_to_bv 64 kMutexWriter)] ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
        rw_cells rsegs m' R [C8 (Z_to_bv 64 0)] ->
        munch [(usp - 128, usp); (R, R + 8)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra0 (Z_to_bv 64 usp) gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7'
                            s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (usp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 res) a0 a1 a2 a3 a4 a5 a6 a7
                         s2 (Z_to_bv 64 2305843009213693952) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x3c1e4) fc None m (seg_rom rsegs)).
  Proof.
    intros until Q. intros MI ST RES FR MX K. replace (usp - 128) with (usp + -128) in ST by lia.
    pose proof alloc_ceiling_val as CV. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, kMutexWriter, gfa_frame in *. aobj_lin_allS.
    pose proof (munch_refl [(usp - 128, usp); (R, R + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    run_to 0x3c220.
    amz. (* [comment removed for export] *)
    amz. br_not_taken.
    scstep; zsimp.
    amz. if_false.
    amz. if_true.
    amz. if_true. (* [comment removed for export] *)
    run_to 0x3c2e8.
    release_frame FR ST usp.
    amz. (* [comment removed for export] *)
    eapply K.
    all: try exact MX; try exact MU; try exact WM; try assumption.
  Qed.
End Tail.

Lemma skipn_S_nth_error : forall {A} (l : list A) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros A l i x H. (first [ pose proof ((nth_error_split l i _ H)) as dR_1; dex2 dR_1 as l1 l2; destruct dR_1 as [E L] | pose proof ((nth_error_split l i _ H)) as dR_1; dand4 dR_1 as l1 l2 E L | destruct (nth_error_split l i _ H) as (l1 & l2 & E & L) ]). rewrite E.
  rewrite !skipn_app. rewrite !(skipn_all2 l1) by lia. rewrite L, Nat.sub_diag. replace (S i - i)%nat with 1%nat by lia. reflexivity.
Qed.
Lemma upd_app_len : forall {X} (l1 l2 : list X) (a b : X), upd (l1 ++ a :: l2) (length l1) b = l1 ++ b :: l2.
Proof. intros X l1; induction l1 as [|y l1 IH]; intros l2 a b; cbn; [reflexivity| f_equal; apply IH]. Qed.
Lemma copy_step : forall {X} (ws ks : list X) i w, nth_error ws i = Some w -> (i < length ks)%nat ->
  upd (firstn i ws ++ skipn i ks) i w = firstn (S i) ws ++ skipn (S i) ks.
Proof.
  intros X ws ks i w NW LI.
  destruct (nth_error ks i) as [kk|] eqn:NK; [| apply nth_error_None in NK; lia].
  rewrite (skipn_S_nth_error ks i kk NK), (firstn_S_nth_error ws i w NW), <- app_assoc. cbn [app].
  (first [ pose proof ((nth_error_split ws i _ NW)) as dR_2; dex2 dR_2 as l1 l2; destruct dR_2 as [E L] | pose proof ((nth_error_split ws i _ NW)) as dR_2; dand4 dR_2 as l1 l2 E L | pose proof (nth_error_split ws i _ NW) as (l1 & l2 & E & L) ]).
  assert (LF : length (firstn i ws) = i) by (apply firstn_length_le; rewrite E, length_app; cbn; lia).
  rewrite <- LF at 3. apply upd_app_len.
Qed.

Lemma mod_mod_pow2 z a b : 0 <= a <= b -> (z mod 2^b) mod 2^a = z mod 2^a.
Proof. intros. apply Z.mod_mod_divide. exists (2^(b-a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.
Lemma swrap32_mod32 z : (bv_swrap 32 z) mod 2^32 = z mod 2^32.
Proof.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
  replace (z + 2^31 - 2^31) with z by lia. reflexivity.
Qed.
Lemma le4_sx32 : forall v : word, le4 (sx32 v) = le4 v.
Proof.
  intros v. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned (sx32 v)) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned v) 32) by (cbn; lia).
  f_equal. unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (mod_mod_pow2 _ 32 64) by lia. apply swrap32_mod32.
Qed.

Section CopyLoop.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (src D n : Z) (ws ks : list word) (Q : machine_state -> Prop).
  Hypotheses (LWS : length ws = Z.to_nat n) (LKS : length ks = 16%nat) (N : 1 <= n <= 16)
             (SLO : kHighMemBeg <= src) (SHI : src + 4 * n <= alloc_ceiling) (DLO : aobj D 64) (DHI : D + 64 <= alloc_ceiling)
             (DJ : src + 4 * n <= D \/ D + 64 <= src).
  Definition cst (i : Z) (a2 : word) (pc : Z) (m : word -> option byte) : machine_state :=
    MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (D + 4 * n)) a2 (Z_to_bv 64 (D + 4 * i)) a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (src + 4 * i)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).
  #[using="DJ DLO SHI SLO N LKS LWS Clg"] Lemma gfa_copy_loop : forall (k : nat) (i : Z) m (a2 : word),
    Z.of_nat k = n - i -> 0 <= i < n ->
    mem_inv rsegs m -> u32arr rsegs m src ws -> u32arr rsegs m D (firstn (Z.to_nat i) ws ++ skipn (Z.to_nat i) ks) ->
    (forall m' (a2' : word), mem_inv rsegs m' -> u32arr rsegs m' src ws -> u32arr rsegs m' D (ws ++ skipn (Z.to_nat n) ks) ->
        munch [(D, D + 64)] m m' -> wmono rsegs m m' -> evt rsegs Q (cst n a2' 0x3c1d4 m')) ->
    evt rsegs Q (cst i a2 0x3c1c0 m).
  Proof.
    induction k as [|k IH]; intros i m a2 HK HI MI SRC DA K; [lia|].
    unfold cst. pose proof alloc_ceiling_val as CV. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
    pose proof (munch_refl [(D, D + 64)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:NW; [| apply nth_error_None in NW; lia].
    assert (LDA : length (firstn (Z.to_nat i) ws ++ skipn (Z.to_nat i) ks) = 16%nat) by (rewrite app_length, firstn_length, skipn_length; lia).
    pose proof (u32arr_read rsegs m src ws i w (Z_to_bv 64 (src + 4 * i)) SRC NW ltac:(lia) ltac:(unfold wa; reflexivity)) as RD.
    amz. (* [comment removed for export] *)
    pose proof (u32arr_store_ok rsegs m D _ i (Z_to_bv 64 (D + 4 * i)) DA ltac:(rewrite LDA; lia) ltac:(unfold wa; reflexivity)) as SOK.
    amz. (* [comment removed for export] *) rewrite le4_sx32.
    change (write_to_mem m (Z_to_bv 64 (D + 4 * i)) (le4 w)) with (write_to_mem m (wa (D + 4 * i)) (le4 w)).
    pose proof (u32arr_write rsegs m D _ i w DA ltac:(rewrite LDA; lia)) as DA2. clear DA.
    store_done.
    amz. amz. amz.
    lazymatch goal with H : mem_inv rsegs ?mm |- _ => rename H into MI2 end.
    rewrite (copy_step ws ks (Z.to_nat i) w NW ltac:(lia)) in DA2.
    replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in DA2 by lia.
    if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
    - (* [comment removed for export] *)
      replace (D + 4 * i + 4) with (D + 4 * (i + 1)) by lia. replace (src + 4 * i + 4) with (src + 4 * (i + 1)) by lia.
      apply (IH (i + 1)); [lia | lia | exact MI2 | exact SRC | exact DA2 |].
      intros m' a2' MI' SRC' DA' MU' WM'. apply K; [exact MI' | exact SRC' | exact DA' | eapply munch_trans; [exact MU | exact MU'] | eapply wmono_trans; [exact WM | exact WM']].
    - (* [comment removed for export] *)
      assert (EI : i + 1 = n) by lia. rewrite <- EI in K. unfold cst in K.
      replace (D + 4 * i + 4) with (D + 4 * (i + 1)) by lia. replace (src + 4 * i + 4) with (src + 4 * (i + 1)) by lia.
      apply K; [exact MI2 | exact SRC | | exact MU | exact WM].
      rewrite <- (firstn_all2 ws (n:=Z.to_nat (i + 1))) at 1 by lia. exact DA2.
  Qed.
End CopyLoop.

Lemma u32arr_of_CB : forall m A n ws, rw_cells rsegs m A [CB n (u32s ws)] -> u32arr rsegs m A ws.
Proof. intros m A n ws H. apply u8arr_of_rw_cells in H. destruct H as [B W]. split; [exact B|]. rewrite u32s_length in W. replace (4 * Z.of_nat (length ws)) with (Z.of_nat (4 * length ws)) by lia. exact W. Qed.
Lemma CB_of_u32arr : forall m A ws, u32arr rsegs m A ws -> rw_cells rsegs m A [CB (4 * length ws) (u32s ws)].
Proof. intros m A ws [B W]. rewrite <- (u32s_length ws). apply rw_cells_of_u8arr. split; [exact B|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact W. Qed.


Section G2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (usp lo R sb c nf n E cnt maxc csz : Z) (na : word) (ws ks : list word) (scr : list byte) (s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word).
  Let fa := free_array_of sb c.
  Hypotheses (LOLE : lo <= usp - 128) (CEIL : alloc_ceiling <= lo) (USP : usp <= 2^47) (UAL : usp mod 16 = 0)
             (RLO : kHighMemBeg <= R) (RHI : R + 128 <= alloc_ceiling) (RAL8 : R mod 8 = 0)
             (ELO : aobj E 80) (EHI : E + 80 <= alloc_ceiling) (EAL : E mod 16 = 0)
             (SB0 : kHighMemBeg <= sb) (SB1 : sb + 2^37 <= alloc_ceiling) (SBA : sb mod 4096 = 0) (CR : 1 <= c <= 31)
             (NR : 1 <= n <= 8) (NF : n <= nf) (NFR : nf < 2^27) (LWS : length ws = Z.to_nat n) (LKS : length ks = 16%nat)
             (CNT : 0 <= cnt < 2^32) (MXC : 0 <= maxc < 2^32) (CSZ : 0 <= csz < 2^64) (DJ : E + 80 <= R \/ R + 128 <= E) (DJ2 : E + 80 <= sb \/ sb + 2^37 <= E) (DJ3 : R + 128 <= sb \/ sb + 2^37 <= R) (RA : bv_unsigned ra0 mod 2 = 0).

  (* [comment removed for export] *)
  #[using="DJ3 DJ2 DJ LKS LWS NFR NF NR CR SB1 SB0 ELO RAL8 RHI RLO CEIL LOLE Clg"] Lemma gfa_copy_tail : forall (ra t0 t1 t2 a0 a1 a2 a6 a7 s1 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m,
    mem_inv rsegs m -> stk rsegs m lo (usp - 128) ->
    rw_cells rsegs m (usp + -128) (gfa_frame scr s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m R [C8 (Z_to_bv 64 kMutexWriter)] ->
    rw_cells rsegs m (R + 16) [C8 (Z_to_bv 64 (nf - n))] ->
    rw_cells rsegs m (R + 72) [C8 na] ->
    u32arr rsegs m (fa + 4 * (nf - n)) ws ->
    rw_cells rsegs m E [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 csz); CB 64 (u32s ks)] ->
    evt rsegs (gfa_post gp tp F fc usp lo R fa (nf - n) n E cnt maxc csz na ws ks s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 m)
        (MS (mkR ra (Z_to_bv 64 (usp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 R) s1 a0 a1 a2 (Z_to_bv 64 (E + 16)) (Z_to_bv 64 n) (Z_to_bv 64 (nf - n)) a6 a7
                 s2 (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 fa) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3c1b0) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI ST FR MX NFC NAC SRC PC.
    pose proof alloc_ceiling_val as CV. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, kMutexWriter in *. aobj_lin_allS.
    assert (FA0 : kHighMemBeg <= fa /\ fa + 4 * nf <= alloc_ceiling) by (unfold fa, free_array_of, kHighMemBeg; plia).
    unfold kHighMemBeg in FA0. aobj_lin_allS. destruct FA0 as [FALO FAHI].
    pose proof (munch_refl [(usp - 128, usp); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80); (E + 16, E + 80)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    apply rw_cells_app_split with (cs1 := [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 csz)]) in PC as [PCH PCT].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PCT. change (Z.of_nat 16) with 16 in PCT.
    apply u32arr_of_CB in PCT.
    amz. amz. amz. amz. (* [comment removed for export] *)
    replace (fa + (nf - n) ≪ 2) with (fa + 4 * (nf - n) + 4 * 0) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (E + 16 + n ≪ 2) with (E + 16 + 4 * n) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (Z_to_bv 64 (E + 16)) with (Z_to_bv 64 (E + 16 + 4 * 0)) by (f_equal; lia).
    eapply gfa_copy_loop with (src := fa + 4 * (nf - n)) (D := E + 16) (ws := ws) (ks := ks) (i := 0) (k := Z.to_nat n).
    all: try eassumption. all: try plia; try (unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, fa, free_array_of in *; lia).
    intros m' a2' MI' SRC' DA' MU' WM'. unfold cst.
    transport_after_call rsegs m m' MU' WM'. clear MI MU' WM'.
    (* [comment removed for export] *)
    apply CB_of_u32arr in DA'. rewrite app_length, skipn_length, LWS, LKS in DA'.
    replace (4 * (Z.to_nat n + (16 - Z.to_nat n)))%nat with 64%nat in DA' by lia.
    pose proof (rw_cells_app_join _ _ _ _ PCH DA') as PC'. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in PC'.
    clear PCH DA'.
    apply CB_of_u32arr in SRC'. rewrite LWS in SRC'. replace (4 * Z.to_nat n)%nat with (Z.to_nat (4 * n)) in SRC' by lia.
    unfold fa, free_array_of in SRC', FALO, FAHI.
    amz. amz. amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    eapply gfa_unlock_tail. all: try eassumption. all: try plia; try (unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; lia).
    intros t0' t1' t2' a1x a2x a3' a4' a5' a6' a7' t3' t4' t5' t6' mm MX' MU2 WM2 MI2 ST2.
    lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call rsegs ma mb MU2 WM2 end. clear MU2 WM2.
    apply u32arr_of_CB in SRC'. fold (free_array_of sb c) in SRC'. fold fa in SRC'.
    finish.
  Qed.
End G2.

Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem gfa_fast_ok : gfa_fast_stmt.
Proof.
  unfold gfa_fast_stmt. intros until ra0. cbv zeta.
  intros MI ST LOLE CEIL USP UAL RLO RHI RAL8 ELO EHI EAL SB0 SB1 SBA CR NR NF NFR LWS LKS CNT MXC CSZ DJ DJ2 DJ3 FR MX NFC NAC SRC PC RA.
  pose proof alloc_ceiling_val as CV. unfold gfa_locked, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
  pose proof (munch_refl [(usp - 128, usp); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80); (E + 16, E + 80)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  apply CB_of_u32arr in SRC. rewrite LWS in SRC. replace (4 * Z.to_nat n)%nat with (Z.to_nat (4 * n)) in SRC by lia. unfold free_array_of in SRC.
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  apply u32arr_of_CB in SRC. fold (free_array_of sb c) in SRC.
  eapply evt_mono; [eapply gfa_copy_tail with (ws := ws) (ks := ks) (scr := scr); first [eassumption | unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; lia] |].
  (* [comment removed for export] *)
  intros ms' PO. unfold gfa_post in *. destruct_exs PO. (first [ dand4 PO as E0 MU1 WM1 REST | destruct PO as (E0 & MU1 & WM1 & REST) ]). subst ms'.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|]. split; [| split; [| exact REST]].
  - eapply munch_trans; [exact MU | exact MU1].
  - eapply wmono_trans; [exact WM | exact WM1].
Qed.

Theorem gfa_popok_ok : gfa_popok_stmt.
Proof.
  unfold gfa_popok_stmt. intros until ra0. cbv zeta.
  intros MI ST LOLE CEIL USP UAL RLO RHI RAL8 ELO EHI EAL SB0 SB1 SBA CR NR NF NFR LWS LKS CNT MXC CSZ RNZ RR DJ DJ2 DJ3 FR MX NFC NAC SRC PC RA.
  pose proof alloc_ceiling_val as CV. unfold gfa_popret, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
  pose proof (munch_refl [(usp - 128, usp); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80); (E + 16, E + 80)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  apply CB_of_u32arr in SRC. rewrite LWS in SRC. replace (4 * Z.to_nat n)%nat with (Z.to_nat (4 * n)) in SRC by lia. unfold free_array_of in SRC.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  apply u32arr_of_CB in SRC. fold (free_array_of sb c) in SRC.
  eapply evt_mono; [eapply gfa_copy_tail with (ws := ws) (ks := ks) (scr := scr); first [eassumption | unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; lia] |].
  intros ms' PO. unfold gfa_post in *. destruct_exs PO. (first [ dand4 PO as E0 MU1 WM1 REST | destruct PO as (E0 & MU1 & WM1 & REST) ]). subst ms'.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|]. split; [| split; [| exact REST]].
  - eapply munch_trans; [exact MU | exact MU1].
  - eapply wmono_trans; [exact WM | exact WM1].
Qed.

(* [comment removed for export] *)

Theorem gfa_popcall_ok : gfa_popcall_stmt.
Proof.
  unfold gfa_popcall_stmt. intros until Q.
  intros MI U0 USP RLO RHI NR NFR THIS DR NFC K.
  pose proof alloc_ceiling_val as CV. unfold gfa_locked, gfa_popret, pop_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
  amz. (* [comment removed for export] *)
  amz. br_taken. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  eapply K.
Qed.

End CEIL2.
End ARt3_gfa.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_51v OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt25ye OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3_gfa.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.

Module ARt3dl2.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtS4t2 ARt2_lib AMTac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt25ye.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
Lemma srliw_half : forall z, 0 <= z < 2^31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 z) 1) = Z.shiftr z 1.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (Z.of_N 32) with 32. change (2 ^ 32 / 2) with (2^31).
  rewrite (Z.mod_small z) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  rewrite Z.mod_small; lia.
Qed.

Lemma max_count_facts : forall c, 1 <= c <= 31 -> 2 <= max_count c <= 16 /\ Z.shiftr (max_count c) 1 = refill_count c /\ 1 <= refill_count c <= 8.
Proof.
  intros c Hc. pose proof (zall_spec 1 31 (fun c => (2 <=? max_count c) && (max_count c <=? 16) && (Z.shiftr (max_count c) 1 =? refill_count c)
     && (1 <=? refill_count c) && (refill_count c <=? 8)) eq_refl c Hc) as H. cbn beta in H. lia.
Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem refill_pre_ok : refill_pre_stmt.
Proof.
  unfold refill_pre_stmt. intros until Q. intros MI ST LOLE CEIL CLO CHI ELO EHI CL CNT MXC CSZ LKS PC K.
  pose proof alloc_ceiling_val as CV. unfold refill_entry, refill_ret, gfa_entry, refill_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 6 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *) rewrite sx32_small by lia.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *) rewrite srliw_half by lia.
  do 7 amz. (* [comment removed for export] *)
  eapply K; [exact FR | exact PC | exact MU | exact WM | assumption | exact ST].
Qed.

Theorem refill_epi_ok : refill_epi_stmt.
Proof.
  unfold refill_epi_stmt. intros until Q. intros MI ST LOLE CEIL USP UAL SP ELO EHI NR RR CNT MXC CSZ LKS FR PC RA K.
  pose proof alloc_ceiling_val as CV. unfold refill_ret, refill_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst sp.
  replace (usp - 32) with (usp + -32) in ST by lia.
  pose proof (munch_refl [(usp - 32, usp); (E, E + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  amz. (* [comment removed for export] *)
  destruct (Z.eq_dec r 0) as [R0|RN].
  - subst r. if_true. rewrite Z.eqb_refl in K.
    do 4 amz. release_frame FR ST usp. amz.
    eapply K; [exact PC | exact MU | exact WM | assumption | exact ST].
  - br_not_taken. replace (r =? 0) with false in K by (symmetry; apply Z.eqb_neq; exact RN).
    amz. (* [comment removed for export] *)
    do 4 amz. release_frame FR ST usp. amz.
    eapply K; [exact PC | exact MU | exact WM | assumption | exact ST].
Qed.

Theorem refill_pre0_ok : refill_pre0_stmt.
Proof.
  unfold refill_pre0_stmt. intros until Q. intros MI ST LOLE CEIL CLO CHI CL MC0 CELLS K.
  pose proof alloc_ceiling_val as CV. unfold refill_entry, refill_ret, gfa_entry, refill_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (C + 80, C + 2560)] m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU2.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (first [ pose proof ((max_count_facts cl ltac:(lia))) as dR_1; dand3 dR_1 as MCR MCH RCR | pose proof (max_count_facts cl ltac:(lia)) as (MCR & MCH & RCR) ]).
  (first [ pose proof ((CELLS cl ltac:(lia))) as dR_2; dand5 dR_2 as CNT MXC CSZ LKS PC | pose proof (CELLS cl ltac:(lia)) as (CNT & MXC & CSZ & LKS & PC) ]). rewrite MC0 in PC.
  remember (C + 80 * cl) as E eqn:HE.
  carve_frame 32%nat ST.
  do 6 amz.
  amz. (* [comment removed for export] *)
  amz. if_true. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply (initcache_blk_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C cnt mc0 cs0 ks);
    [ assumption | unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; plia | lia | | ] end.
  { intros i Hi. (first [ pose proof ((CELLS i Hi)) as dR_3; dand5 dR_3 as A1 A2 A3 A4 A5 | pose proof (CELLS i Hi) as (A1 & A2 & A3 & A4 & A5) ]). repeat (split; [assumption|]).
    eapply rw_cells_transport; [exact A5 | exact MU2 | exact WM | cbn; lia]. }
  clear PC MU2. intros t3' t4' t5' m' CELLS' MU' WM' MI'. unfold initcache_blk_exit.
  transport_after_call rsegs ltac:(lazymatch type of WM' with wmono _ ?a _ => a end) m' MU' WM'. clear MU' WM'.
  pose proof (CELLS' cl ltac:(lia)) as PC. rewrite <- HE in PC.
  amz. (* [comment removed for export] *) rewrite sx32_small by lia.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *) rewrite srliw_half by lia. rewrite MCH.
  do 7 amz.
  subst E. eapply K; [exact FR | exact CELLS' | exact MU | exact WM | assumption | exact ST].
Qed.

End CEIL.

End ARt3dl2.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
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
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
Lemma shr4_mul16 : forall k, 0 <= k -> Z.shiftr (16 * k) 4 = k.
Proof. intros k Hk. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. lia. Qed.
Lemma half_range : forall z, 0 <= z -> 0 <= Z.shiftr z 1 <= z.
Proof. intros z Hz. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. lia. Qed.
Lemma zx32_lit : forall z, 0 <= z < 2^32 -> bv_unsigned (zx32 (Z_to_bv 64 z)) = z.
Proof. intros z Hz. rewrite zx32_small by lia. apply unsigned_lit. lia. Qed.
(* [comment removed for export] *)

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem efas_fast_ok : efas_fast_stmt.
Proof.
  unfold efas_fast_stmt. intros until mfa. intros MI ST LOLE CEIL A1 A3 RLO RHI NUM FIT MFA MF RA.
  pose proof alloc_ceiling_val as CV. unfold efas_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS. subst a1 a3.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 48%nat ST.
  hot_qset.
  do 6 amz.
  amz. amz. amz. (* [comment removed for export] *)
  amz. rewrite (Z.shiftl_mul_pow2 num 2) by lia. change (2^2) with 4. br_taken. (* [comment removed for export] *)
  do 7 amz.
  release_frame FR ST (bv_unsigned sp). amz.
  all: hot_qend.
  finish.
Qed.

Theorem lcdrain_post_ok : lcdrain_post_stmt.
Proof.
  unfold lcdrain_post_stmt. intros until Q. intros MI ST LOLE CEIL USP UAL FR RA K.
  pose proof alloc_ceiling_val as CV. unfold lcdrain_ret, lcdrain_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
  replace (usp - 64) with (usp + -64) in ST by lia.
  pose proof (munch_refl [(usp - 64 - 48, usp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  amz. amz. amz. amz. (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 5 amz. (* [comment removed for export] *)
  amz. if_true. (* [comment removed for export] *)
  do 5 amz. release_frame FR0 ST (usp + -64). amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  release_frame FR ST usp. amz. (* [comment removed for export] *)
  eapply K; [exact MU | exact WM | assumption | exact ST].
Qed.

Theorem lcdrain_pre_ok : lcdrain_pre_stmt.
Proof.
  unfold lcdrain_pre_stmt. intros until Q. cbv zeta. intros MI ST LOLE CEIL CLO CHI ELO EHI CR MXC CNT CSZ LKS PC K.
  pose proof alloc_ceiling_val as CV. unfold lcdrain_entry, lcdrain_ret, rta_entry, lcdrain_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (E, E + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (half_range maxc ltac:(lia)) as HR.
  carve_frame 64%nat ST.
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. rewrite sx32_small by lia. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *) rewrite zx32_lit by lia.
  amz. amz. (* [comment removed for export] *) rewrite (Z.mod_small cnt 4294967296) by lia.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  replace (E + (cnt - maxc ≫ 1) ≪ 2 + 16) with (E + 16 + 4 * (cnt - maxc ≫ 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  eapply K; [exact FR | exact PC | exact MU | exact WM | assumption | exact ST].
Qed.

End CEIL.

Section MR.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mrtos_epi : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (lo : Z) (s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word) (pad : list byte),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - 80 -> alloc_ceiling <= lo ->
    rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra0 sp gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo (bv_unsigned sp))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3a340) fc None m (seg_rom rsegs)).
  Proof.
    intros until pad. intros MI ST LOLE CEIL FR MU WM RA.
    pose proof alloc_ceiling_val as CV.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    hot_qset.
    do 10 amz.
    release_frame FR ST (bv_unsigned sp). amz.
    all: hot_qend. finish.
  Qed.
End MR.

Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem mrtos_ok : mrtos_stmt.
Proof.
  unfold mrtos_stmt. intros until v88. cbv zeta. intros MI ST LOLE CEIL RI ITV GOTP PGS CR RLO RHI RAL V16 V80 RA.
  pose proof alloc_ceiling_val as CV. unfold mrtos_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
  remember (ri + 128 * c) as R eqn:HR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 80%nat ST.
  do 10 amz. (* [comment removed for export] *)
  do 4 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mj _) =>
  assert (J : forall (a0' a2' a3' s2' : word),
    evt rsegs P
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 a1 (Z_to_bv 64 c) a0' (Z_to_bv 64 (c ≪ 7)) a2' a3' a4 a5 a6 a7
               s2' (Z_to_bv 64 726360) s4 (Z_to_bv 64 0) (Z_to_bv 64 ri) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3a214) fc None mj (seg_rom rsegs))) end.
  { intros a0' a2' a3' s2'.
    amz. amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. replace (ri + c ≪ 7) with R by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia).
    amz. if_false. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. if_cases K1; [ | amz; eapply mrtos_epi; try eassumption; lia ].
    (* [comment removed for export] *)
    amz. amz. amz. amz. (* [comment removed for export] *)
    amz. if_cases K2; [ eapply mrtos_epi; try eassumption; lia | ].
    amz. if_false. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. if_true. (* [comment removed for export] *)
    eapply mrtos_epi; try eassumption; lia. }
  if_cases KC.
  - (* [comment removed for export] *) do 9 amz. eapply J.
  - (* [comment removed for export] *) amz. amz. eapply J.
Qed.

End CEIL2.

Section Push.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (usp lo C c sb k cnt maxc : Z) (ks : list word) (s4v s3v s2v s1v s0v ra0 : word).
  Let E := C + 80 * c.
  Hypotheses (LOLE : lo <= usp - 48) (CEIL : alloc_ceiling <= lo) (USP : usp <= 2^47) (UAL : usp mod 16 = 0)
             (CLO : aobj C 3888) (CHI : C + 3888 <= alloc_ceiling) (CAL : C mod 16 = 0) (CR : 1 <= c <= 31)
             (SB0 : kHighMemBeg <= sb) (SB1 : sb + 2^37 <= alloc_ceiling) (SBA : sb mod 4096 = 0) (KR : 0 <= k < 2^28)
             (CNT : 0 <= cnt < 16) (MXC : 0 <= maxc < 2^32) (LKS : length ks = 16%nat) (RA : bv_unsigned ra0 mod 2 = 0).

  (* [comment removed for export] *)
  #[using="LKS CNT KR SB1 SB0 CR CAL CLO CEIL LOLE Clg"] Lemma lcd_push_tail : forall (ra t0 t1 t2 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (statv : word) m,
    mem_inv rsegs m -> stk rsegs m lo (usp - 48) ->
    ro_cells rsegs m 0xb1578 [C8 (Z_to_bv 64 sb)] ->
    rw_cells rsegs m (usp + -48) (lcd_frame s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m E [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m',
                 ms' = MS (mkR ra0 (Z_to_bv 64 usp) gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 48, usp); (E, E + 80); (C + 2576, C + 2584)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
                 /\ rw_cells rsegs m' E [C4 (Z_to_bv 64 (cnt + 1)); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s (upd ks (Z.to_nat cnt) (Z_to_bv 64 k)))]
                 /\ rw_cells rsegs m' (C + 2576) [C8 statv'])
        (MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 E) s1 (Z_to_bv 64 C) (Z_to_bv 64 0xb1558) (Z_to_bv 64 c)
                 (Z_to_bv 64 (sb + c * 4294967296 + 16 * k)) (Z_to_bv 64 cnt) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x397fc) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI ST SB FR PC STA. replace (usp - 48) with (usp + -48) in ST by lia.
    pose proof alloc_ceiling_val as CV. unfold lcd_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
    pose proof (class_size_range31 c CR) as CSR.
    pose proof (munch_refl [(usp - 48, usp); (E, E + 80); (C + 2576, C + 2584)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    set (cq := C / 16) in *. assert (CQ : C = 16 * cq) by (subst cq; rewrite (Z_div_mod_eq_full C 16) at 1; rewrite CAL; lia). clearbody cq.
    assert (AL8 : (C + 2576) mod 8 = 0) by (rewrite CQ; replace (16 * cq + 2576) with ((2 * cq + 322) * 8) by lia; apply Z_mod_mult).
    hot_qset.
    amz. (* [comment removed for export] *)
    amz. replace (Z.shiftl c 32) with (c * 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *) replace (sb + c * 4294967296 + 16 * k - c * 4294967296 - sb) with (16 * k) by lia.
    amz. (* [comment removed for export] *)
    amz. amz. rewrite slli32_srli30 by lia. amz. amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *) rewrite shr4_mul16 by lia.
    apply rw_cells_app_split with (cs1 := [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c))]) in PC as [PCH PCT].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PCT. change (Z.of_nat 16) with 16 in PCT.
    apply u32arr_of_CB in PCT.
    amz. (* [comment removed for export] *)
    pose proof (u32arr_store_ok rsegs _ (E + 16) ks cnt (Z_to_bv 64 (E + cnt * 4 + 16)) PCT ltac:(rewrite LKS; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    amz. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
      replace (write_to_mem mm a bs) with (write_to_mem mm (wa (E + 16 + 4 * cnt)) bs) by (unfold wa; f_equal; f_equal; lia);
      pose proof (u32arr_write rsegs mm (E + 16) ks cnt (Z_to_bv 64 k) PCT ltac:(rewrite LKS; lia)) as PCT2 end.
    clear PCT. store_done.
    amz. amz. (* [comment removed for export] *)
    do 7 amz. release_frame FR ST usp. amz.
    all: hot_qend.
    apply CB_of_u32arr in PCT2. rewrite upd_length, LKS in PCT2. change (4 * 16)%nat with 64%nat in PCT2.
    pose proof (rw_cells_app_join _ _ _ _ PCH PCT2) as PC'. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in PC'.
    finish. all: try exact STA.
  Qed.

  #[using="LKS CNT KR SB1 SB0 CR CAL CLO CEIL LOLE Clg"] Theorem lcdealloc_after_ok0 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (statv : word) m,
    mem_inv rsegs m -> stk rsegs m lo (usp - 48) ->
    ro_cells rsegs m 0xb1578 [C8 (Z_to_bv 64 sb)] ->
    rw_cells rsegs m (usp + -48) (lcd_frame s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m E [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m',
                 ms' = MS (mkR ra0 (Z_to_bv 64 usp) gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 48, usp); (E, E + 80); (C + 2576, C + 2584)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
                 /\ rw_cells rsegs m' E [C4 (Z_to_bv 64 (cnt + 1)); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s (upd ks (Z.to_nat cnt) (Z_to_bv 64 k)))]
                 /\ rw_cells rsegs m' (C + 2576) [C8 statv'])
        (MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 C) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0xb1558) (Z_to_bv 64 c) (Z_to_bv 64 (sb + c * 4294967296 + 16 * k)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 lcdealloc_after) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI ST SB FR PC STA.
    pose proof alloc_ceiling_val as CV. unfold lcdealloc_after, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
    amz. amz. amz. amz. (* [comment removed for export] *)
    amz. rewrite sx32_small by lia. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    eapply lcd_push_tail; eassumption.
  Qed.
End Push.

Section CEIL3.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem lcdealloc_after_ok : lcdealloc_after_stmt.
Proof.
  unfold lcdealloc_after_stmt. intros until ra0. cbv zeta.
  intros MI ST LOLE CEIL USP UAL CLO CHI CAL CR SB0 SB1 SBA KR CNT MXC LKS SB FR PC STA RA.
  eapply lcdealloc_after_ok0; eassumption.
Qed.

Theorem lcdealloc_push_ok : lcdealloc_push_stmt.
Proof.
  unfold lcdealloc_push_stmt. intros until statv. cbv zeta.
  intros MI ST LOLE CEIL A0 A1 A2 A3 CLO CHI CAL CR SB0 SB1 SBA KR CNT MXC LKS SB PC STA RA.
  pose proof alloc_ceiling_val as CV. unfold lcdealloc_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS. subst a0 a1 a2 a3.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (C + 80 * c, C + 80 * c + 80); (C + 2576, C + 2584)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  remember (C + 80 * c) as E eqn:HE.
  carve_frame 48%nat ST.
  do 7 amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  replace (C + c * 80) with E by lia.
  amz. rewrite sx32_small by lia. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. rewrite sx32_small by lia. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  subst E. eapply evt_mono.
  { eapply lcd_push_tail; try eassumption; try lia. }
  intros ms' PO. destruct_exs PO. destruct PO as (E0 & MU1 & WM1 & REST). rewrite Z_to_bv_bv_unsigned in E0. subst ms'.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
  split; [ eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU1]]; unfold sub_fp; cbn [outside]; intros; lia |].
  split; [eapply wmono_trans; [exact WM | exact WM1]|].
  exact REST.
Qed.

Theorem lcdealloc_full_ok : lcdealloc_full_stmt.
Proof.
  unfold lcdealloc_full_stmt. intros until Q. cbv zeta.
  intros MI ST LOLE CEIL A0 A1 A2 A3 CLO CHI CAL CR PR MXC LKS PC K.
  pose proof alloc_ceiling_val as CV. unfold lcdealloc_entry, lcdealloc_after, lcdrain_entry, lcd_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS. subst a0 a1 a2 a3.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  remember (C + 80 * c) as E eqn:HE.
  carve_frame 48%nat ST.
  do 7 amz.
  amz. br_not_taken.
  amz. amz. br_not_taken.
  amz. amz. amz.
  replace (C + c * 80) with E by lia.
  amz. rewrite sx32_small by lia.
  amz. br_not_taken.
  amz. rewrite sx32_small by lia.
  amz. br_taken. (* [comment removed for export] *)
  do 7 amz. amz. (* [comment removed for export] *)
  eapply K; [exact FR | exact PC | exact MU | exact WM | assumption | exact ST].
Qed.

Theorem rta_lock_ok : rta_lock_stmt.
Proof.
  unfold rta_lock_stmt. intros until Q. cbv zeta. intros MI ST LOLE CEIL A1 A2 A3 A4 A5 SB RI CR RLO RHI RAL SB0 SB1 MMR STR DR NR NFR MX NFC K.
  pose proof alloc_ceiling_val as CV. unfold rta_entry, rta_efasret, efas_entry, kMutexWriter, free_array_of, rta_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS. subst a1 a2 a3 a4 a5.
  remember (ri + 128 * c) as R eqn:HR.
  set (rq := ri / 128) in *. assert (RQ : ri = 128 * rq) by (subst rq; rewrite (Z_div_mod_eq_full ri 128) at 1; rewrite RAL; lia). clearbody rq.
  assert (RAL8 : R mod 8 = 0) by (rewrite HR, RQ; replace (128 * rq + 128 * c) with ((16 * rq + 16 * c) * 8) by lia; apply Z_mod_mult).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (R, R + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 128%nat ST.
  do 14 amz. (* [comment removed for export] *)
  do 7 amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  do 9 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *) replace (ri + c ≪ 7) with R by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia).
  amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  run_to 0x39dac.
  amz. (* [comment removed for export] *)
  amz. br_not_taken.
  scstep; zsimp.
  amz. if_false.
  amz. if_true. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  replace (sb + c ≪ 32 + 3758096384) with (sb + c * 4294967296 + 3758096384) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^32) with 4294967296; lia).
  replace (sb + c ≪ 32) with (sb + c * 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^32) with 4294967296; lia).
  eapply K; [exact MX | exact NFC | exact FR | exact MU | exact WM | assumption | exact ST].
Qed.

End CEIL3.

Section RtaCopy.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (src dst n : Z) (ws junk : list word) (Q : machine_state -> Prop).
  Hypotheses (LWS : length ws = Z.to_nat n) (LJ : length junk = Z.to_nat n) (N : 1 <= n <= 8)
             (SLO : aobj src (4 * n)) (SHI : src + 4 * n <= alloc_ceiling) (DLO : kHighMemBeg <= dst) (DHI : dst + 4 * n <= alloc_ceiling)
             (DJ : src + 4 * n <= dst \/ dst + 4 * n <= src).
  Definition cst2 (i : Z) (a1 : word) (pc : Z) (m : word -> option byte) : machine_state :=
    MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (src + 4 * n)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (src + 4 * i)) s7 s8 (Z_to_bv 64 (dst + 4 * i)) s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).
  #[using="DJ DHI DLO SLO N LJ LWS Clg"] Lemma rta_copy_loop : forall (k : nat) (i : Z) m (a1 : word),
    Z.of_nat k = n - i -> 0 <= i < n ->
    mem_inv rsegs m -> u32arr rsegs m src ws -> u32arr rsegs m dst (firstn (Z.to_nat i) ws ++ skipn (Z.to_nat i) junk) ->
    (forall m' (a1' : word), mem_inv rsegs m' -> u32arr rsegs m' src ws -> u32arr rsegs m' dst ws ->
        munch [(dst, dst + 4 * n)] m m' -> wmono rsegs m m' -> evt rsegs Q (cst2 n a1' 0x39e80 m')) ->
    evt rsegs Q (cst2 i a1 0x39e6c m).
  Proof.
    induction k as [|k IH]; intros i m a1 HK HI MI SRC DA K; [lia|].
    unfold cst2. pose proof alloc_ceiling_val as CV. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
    pose proof (munch_refl [(dst, dst + 4 * n)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:NW; [| apply nth_error_None in NW; lia].
    assert (LDA : length (firstn (Z.to_nat i) ws ++ skipn (Z.to_nat i) junk) = Z.to_nat n) by (rewrite app_length, firstn_length, skipn_length; lia).
    pose proof (u32arr_read rsegs m src ws i w (Z_to_bv 64 (src + 4 * i)) SRC NW ltac:(lia) ltac:(unfold wa; reflexivity)) as RD.
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    pose proof (u32arr_store_ok rsegs m dst _ i (Z_to_bv 64 (dst + 4 * i)) DA ltac:(rewrite LDA; lia) ltac:(unfold wa; reflexivity)) as SOK.
    amz. (* [comment removed for export] *) rewrite le4_sx32.
    change (write_to_mem m (Z_to_bv 64 (dst + 4 * i)) (le4 w)) with (write_to_mem m (wa (dst + 4 * i)) (le4 w)).
    pose proof (u32arr_write rsegs m dst _ i w DA ltac:(rewrite LDA; lia)) as DA2. clear DA.
    store_done.
    amz. amz. (* [comment removed for export] *)
    lazymatch goal with H : mem_inv rsegs ?mm |- _ => rename H into MI2 end.
    rewrite (copy_step ws junk (Z.to_nat i) w NW ltac:(lia)) in DA2.
    replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in DA2 by lia.
    if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
    - replace (dst + 4 * i + 4) with (dst + 4 * (i + 1)) by lia. replace (src + 4 * i + 4) with (src + 4 * (i + 1)) by lia.
      apply (IH (i + 1)); [lia | lia | exact MI2 | exact SRC | exact DA2 |].
      intros m' a1' MI' SRC' DA' MU' WM'. apply K; [exact MI' | exact SRC' | exact DA' | eapply munch_trans; [exact MU | exact MU'] | eapply wmono_trans; [exact WM | exact WM']].
    - unfold cst2 in K.
      replace (dst + 4 * i + 4) with (dst + 4 * n) by lia. replace (src + 4 * i + 4) with (src + 4 * n) by lia.
      apply K; [exact MI2 | exact SRC | | exact MU | exact WM].
      rewrite firstn_all2 in DA2 by lia. rewrite skipn_all2 in DA2 by lia. rewrite app_nil_r in DA2. exact DA2.
  Qed.
End RtaCopy.

Section CEIL4.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem rta_post_ok : rta_post_stmt.
Proof.
  unfold rta_post_stmt. intros MR. intros until ra0. cbv zeta.
  intros MI ST LOLE CEIL USP UAL RI ITV GOTP PGS CR RLO RHI RAL SB0 SB1 SBA DLO DHI DAL NR NF0 NFR RNZ RR MMR LWS LJ DJ1 DJ2 DJ3 FR MX NFC NFS SRC DST RA.
  pose proof alloc_ceiling_val as CV. unfold rta_efasret, kMutexWriter, rta_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_allS.
  remember (ri + 128 * c) as R eqn:HR.
  remember (free_array_of sb c) as fa eqn:HFA.
  assert (FAR : sb <= fa /\ fa + 4 * (nf + n) <= sb + 2^37) by (subst fa; unfold free_array_of; lia).
  destruct FAR as [FALO FAHI].
  set (rq := ri / 128) in *. assert (RQ : ri = 128 * rq) by (subst rq; rewrite (Z_div_mod_eq_full ri 128) at 1; rewrite RAL; lia). clearbody rq.
  assert (RAL8 : R mod 8 = 0) by (rewrite HR, RQ; replace (128 * rq + 128 * c) with ((16 * rq + 16 * c) * 8) by lia; apply Z_mod_mult).
  replace (usp - 128) with (usp + -128) in ST by lia.
  pose proof (munch_refl [(usp - 128 - 80, usp); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88); (fa + 4 * nf, fa + 4 * nf + 4 * n)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  hot_qset.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  replace (fa + nf ≪ 2) with (fa + 4 * nf + 4 * 0) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (D + n ≪ 2) with (D + 4 * n) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 4 * 0)) by (f_equal; lia).
  eapply rta_copy_loop with (src := D) (dst := fa + 4 * nf) (ws := ws) (junk := junk) (i := 0) (k := Z.to_nat n).
  all: try eassumption. all: try plia; try (unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; lia).
  intros m' a1' MI' SRC' DST' MU' WM'. unfold cst2.
  try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST); transport_after_call rsegs m m' MU' WM'. clear MI MU' WM'.
  (* [comment removed for export] *)
  apply CB_of_u32arr in SRC'. rewrite LWS in SRC'. replace (4 * Z.to_nat n)%nat with (Z.to_nat (4 * n)) in SRC' by lia.
  apply CB_of_u32arr in DST'. rewrite LWS in DST'. replace (4 * Z.to_nat n)%nat with (Z.to_nat (4 * n)) in DST' by lia.
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  rewrite HR in NFC, NFS.
  callz (MR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo ri c).
  all: try eassumption.
  all: try (rewrite unsigned_lit by lia; first [reflexivity | lia | assumption]).
  run_to 0x39ee0.
  amz. (* [comment removed for export] *)
  amz. br_not_taken.
  scstep; zsimp.
  amz. if_false.
  amz. if_true. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  do 14 amz.
  lazymatch goal with H : stk rsegs _ lo _ |- _ => release_frame FR H usp end. amz. (* [comment removed for export] *)
  all: hot_qend.
  apply u32arr_of_CB in SRC'. apply u32arr_of_CB in DST'.
  replace (ri + 128 * c) with R in NFC by exact HR. replace (ri + 128 * c) with R in NFS by exact HR.
  finish.
Qed.

End CEIL4.

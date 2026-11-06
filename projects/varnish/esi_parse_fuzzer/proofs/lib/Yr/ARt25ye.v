(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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
            (Z_to_bv 64 (a5of k)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3c110) fc None m (seg_rom rsegs).
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
            F (Z_to_bv 64 0x3c0ec) fc None m (seg_rom rsegs))).
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

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0SMAGEN.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma lxor_sign_mod : forall z, (- 9223372036854775808 <= z < 9223372036854775808)%Z ->
    Z.lxor (z mod 18446744073709551616) 9223372036854775808 = (z + 9223372036854775808)%Z.
  Proof.
    intros z Hz.
    assert (R : forall x, (0 <= x < 18446744073709551616)%Z -> Z.lxor x 9223372036854775808 = ((x + 9223372036854775808) mod 18446744073709551616)%Z).
    { intros x Hx. change 9223372036854775808%Z with (2^63)%Z. change 18446744073709551616%Z with (2^64)%Z. apply zb_lxor_sign.
      change (2^64)%Z with 18446744073709551616%Z. lia. }
    destruct (Z.lt_ge_cases z 0).
    - replace (z mod 18446744073709551616)%Z with (z + 18446744073709551616)%Z.
      2:{ symmetry. rewrite <- (Z.mod_add z 1 18446744073709551616) by lia. apply Z.mod_small. lia. }
      rewrite R by lia. rewrite <- (Z.mod_add _ (-1)) by lia.
      replace (z + 18446744073709551616 + 9223372036854775808 + -1 * 18446744073709551616)%Z with (z + 9223372036854775808)%Z by lia.
      apply Z.mod_small. lia.
    - rewrite (Z.mod_small z) by lia. rewrite R by lia. apply Z.mod_small. lia.
  Qed.

  Lemma row_before_memset : forall segs m P l Jl N a k,
    u8arr segs m P (ovb l Jl N) -> (0 <= a)%Z -> (0 <= k)%Z -> (a + k <= N)%Z ->
    u8arr segs m P (firstn (Z.to_nat a) (ovb l Jl N)) /\
    rw_cells segs m (P + a)%Z [CB (Z.to_nat k) (firstn (Z.to_nat k) (skipn (Z.to_nat a) (ovb l Jl N)))] /\
    u8arr segs m (P + a + k)%Z (skipn (Z.to_nat (a + k)) (ovb l Jl N)).
  Proof.
    intros segs m P l Jl N a k H Ha Hk HN. pose proof (ovb_length_nat l Jl N) as L.
    rewrite <- (firstn_skipn (Z.to_nat a) (ovb l Jl N)) in H. apply (proj1 (u8arr_app segs m P _ _)) in H. destruct H as [H0 H].
    rewrite length_firstn, L in H. replace (P + Z.of_nat (Nat.min (Z.to_nat a) (Z.to_nat N)))%Z with (P + a)%Z in H by lia.
    rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat a) (ovb l Jl N))) in H. apply (proj1 (u8arr_app segs m (P + a) _ _)) in H. destruct H as [H1 H2].
    rewrite length_firstn, length_skipn, L, skipn_skipn in H2.
    replace (P + a + Z.of_nat (Nat.min (Z.to_nat k) (Z.to_nat N - Z.to_nat a)))%Z with (P + a + k)%Z in H2 by lia.
    replace (Z.to_nat k + Z.to_nat a)%nat with (Z.to_nat (a + k)) in H2 by lia.
    split; [exact H0|]. split; [|exact H2].
    apply (rw_cells_of_u8arr segs) in H1. rewrite length_firstn, length_skipn, L in H1.
    replace (Nat.min (Z.to_nat k) (Z.to_nat N - Z.to_nat a)) with (Z.to_nat k) in H1 by lia. exact H1.
  Qed.

  Lemma ovb_row_split : forall l Jl N t k, (0 <= t)%Z -> (0 <= k)%Z -> (258 * t + k <= N)%Z ->
    ovb (sm_len_init_row (Z.to_nat k) l t 0) Jl N = firstn (Z.to_nat (258 * t)) (ovb l Jl N) ++ repeat (Z_to_bv 8 15) (Z.to_nat k) ++ skipn (Z.to_nat (258 * t + k)) (ovb l Jl N).
  Proof.
    intros l Jl N t k Ht Hk HN. apply nth_error_ext. intros i.
    pose proof (ovb_length_nat l Jl N) as L. pose proof (ovb_length_nat (sm_len_init_row (Z.to_nat k) l t 0) Jl N) as L'.
    destruct (Nat.lt_ge_cases i (Z.to_nat N)) as [Hi|Hi].
    2:{ rewrite (proj2 (nth_error_None _ _)) by lia. symmetry. apply (proj2 (nth_error_None _ _)).
        rewrite !length_app, length_firstn, repeat_length, length_skipn. lia. }
    replace i with (Z.to_nat (Z.of_nat i)) by lia.
    rewrite ovb_nth_raw by lia. rewrite sm_len_init_row_def, sm_len_init_row_get.
    destruct (Nat.lt_ge_cases i (Z.to_nat (258 * t))) as [H1|H1].
    - rewrite nth_error_app1 by (rewrite length_firstn; lia). rewrite nth_error_firstn' by lia. rewrite ovb_nth_raw by lia.
      replace ((258 * t + 0 <=? Z.of_nat i) && (Z.of_nat i <? 258 * t + 0 + Z.of_nat (Z.to_nat k)))%Z%bool with false
        by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      reflexivity.
    - rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
      destruct (Nat.lt_ge_cases i (Z.to_nat (258 * t) + Z.to_nat k)) as [H2|H2].
      + rewrite nth_error_app1 by (rewrite repeat_length; lia). rewrite nth_error_repeat by lia.
        replace ((258 * t + 0 <=? Z.of_nat i) && (Z.of_nat i <? 258 * t + 0 + Z.of_nat (Z.to_nat k)))%Z%bool with true
          by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        reflexivity.
      + rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, nth_error_skipn.
        replace (Z.to_nat (258 * t + k) + (Z.to_nat (Z.of_nat i) - Nat.min (Z.to_nat (258 * t)) (length (ovb l Jl N)) - Z.to_nat k))%nat with (Z.to_nat (Z.of_nat i)) by lia.
        rewrite ovb_nth_raw by lia.
        replace ((258 * t + 0 <=? Z.of_nat i) && (Z.of_nat i <? 258 * t + 0 + Z.of_nat (Z.to_nat k)))%Z%bool with false
          by (symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
        reflexivity.
  Qed.

  Lemma row_after_memset : forall segs m P l Jl N t k,
    u8arr segs m P (firstn (Z.to_nat (258 * t)) (ovb l Jl N)) ->
    rw_cells segs m (P + 258 * t)%Z [CB (Z.to_nat k) (repeat (Z_to_bv 8 15) (Z.to_nat k))] ->
    u8arr segs m (P + 258 * t + k)%Z (skipn (Z.to_nat (258 * t + k)) (ovb l Jl N)) ->
    (0 <= t)%Z -> (0 <= k)%Z -> (258 * t + k <= N)%Z ->
    u8arr segs m P (ovb (sm_len_init_row (Z.to_nat k) l t 0) Jl N).
  Proof.
    intros segs m P l Jl N t k H0 H1 H2 Ht Hk HN. pose proof (ovb_length_nat l Jl N) as L.
    rewrite (ovb_row_split l Jl N t k) by lia.
    apply (proj2 (u8arr_app segs m P _ _)). split; [exact H0|].
    rewrite length_firstn, L. replace (P + Z.of_nat (Nat.min (Z.to_nat (258 * t)) (Z.to_nat N)))%Z with (P + 258 * t)%Z by lia.
    apply (proj2 (u8arr_app segs m _ _ _)). split.
    - pose proof (u8arr_of_rw_cells segs m _ _ _ H1) as U. exact U.
    - rewrite repeat_length. replace (P + 258 * t + Z.of_nat (Z.to_nat k))%Z with (P + 258 * t + k)%Z by lia. exact H2.
  Qed.

  Lemma zbv_mod_mul : forall x c, Z_to_bv 64 ((x mod 18446744073709551616) * c) = Z_to_bv 64 (x * c).
  Proof.
    intros x c. apply Z_to_bv_eqm. change (2^64)%Z with 18446744073709551616%Z.
    rewrite (Z.mod_eq x 18446744073709551616) by lia.
    replace ((x - 18446744073709551616 * (x / 18446744073709551616)) * c)%Z with (x * c + (- (x / 18446744073709551616) * c) * 18446744073709551616)%Z by nia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Lemma zbv_add_mod_mul : forall a x c, Z_to_bv 64 (a + (x mod 18446744073709551616) * c) = Z_to_bv 64 (a + x * c).
  Proof.
    intros a x c. apply Z_to_bv_eqm. change (2^64)%Z with 18446744073709551616%Z.
    rewrite (Z.mod_eq x 18446744073709551616) by lia.
    replace (a + (x - 18446744073709551616 * (x / 18446744073709551616)) * c)%Z with (a + x * c + (- (x / 18446744073709551616) * c) * 18446744073709551616)%Z by nia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Lemma v_divw_lit : forall a b, (0 <= a < 2147483648)%Z -> (0 < b < 2147483648)%Z ->
    v_divw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
  Proof.
    intros a b Ha Hb. unfold v_divw. rewrite !unsigned_lit by lia. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 32)%Z with 4294967296%Z. rewrite (Z.mod_small b 4294967296%Z ltac:(lia)).
    replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (swrap32_small a) by lia. rewrite (swrap32_small b) by lia. rewrite Z.quot_div_nonneg by lia.
    pose proof (Z.div_pos a b ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound a b a ltac:(lia) ltac:(nia)).
    rewrite swrap32_small by lia. reflexivity.
  Qed.

End A0SMAGEN.

Section A0SMA.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis SF : smA_facts e.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1616 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation mf := (e_mtfFreq e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Notation RI ra a0 a1 a2 a3 a4 a5 a6 s2 s3 s5 s7 s8 s9 s11 t6 :=
    (mkR ra cP gp tp (Z_to_bv 64 E) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 (E + 676)) s0 cP a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 nInUse)
         s2 s3 cSB s5 (Z_to_bv 64 (E + 668)) s7 s8 s9 (Z_to_bv 64 1) s11 (Z_to_bv 64 3) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2147483647)) t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_smA_grow : forall (f : nat) (ge aF gs tF remF : Z) (m : word -> option byte)
      (ra a4 a6 s2 s5 s7 s9 t6 : word),
    (1 <= f)%nat -> (A - 1 - ge <= Z.of_nat f)%Z ->
    (0 <= gs)%Z -> (gs - 1 <= ge <= A - 2)%Z -> (aF < tF)%Z -> (0 < tF <= nMTF)%Z ->
    aF = sumF (fun v => zget mf v) gs (Z.to_nat (ge + 1 - gs)) ->
    remF = sumF (fun v => zget mf v) gs (Z.to_nat (A - gs)) -> (remF <= nMTF)%Z ->
    u32arr a0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) ->
    shzW a0segs [] m E (E + ESTATE_SIZE) ->
    (forall ge' aF' (a0 a3 a4 a5 a6 : word),
      sm_grow f mf tF A ge aF = (ge', aF') -> (ge < ge' <= A - 1)%Z -> aF' = sumF (fun v => zget mf v) gs (Z.to_nat (ge' + 1 - gs)) -> (0 <= aF' <= remF)%Z ->
      evt a0segs Q (MS (RI ra a0 (Z_to_bv 64 (ge' * 4294967296)) (Z_to_bv 64 tF) a3 a4 a5 a6 s2 (Z_to_bv 64 aF') s5 s7 (Z_to_bv 64 ge') s9 (Z_to_bv 64 gs) t6)
                       F (Z_to_bv 64 0x8a7a0) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (RI ra (Z_to_bv 64 (E + 676 + 4 * ge)) (Z_to_bv 64 (ge * 4294967296)) (Z_to_bv 64 tF) (Z_to_bv 64 (E + 676 + 4 * ge)) a4 (Z_to_bv 64 ge) a6
                         s2 (Z_to_bv 64 aF) s5 s7 (Z_to_bv 64 ge) s9 (Z_to_bv 64 gs) t6)
                     F (Z_to_bv 64 0x8a750) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]. { intros; lia. }
    intros ge aF gs tF remF m ra a4 a6 s2 s5 s7 s9 t6 Hf1 Hf Hgs Hge HaF HtF EaF EremF HremF MTF SHe K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openSF. unfold sm_alpha, sm_nmtf in *. unfold ESTATE_SIZE in SHe.
    pose proof (munch_refl [] m) as MU.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm. pose proof (ovw_length mf (jseg J 672 1032) 258 ltac:(lia)) as LM.
    pose proof (MFD (ge + 1)%Z ltac:(lia)) as [Dq Rq].
    (* [comment removed for export] *)
    assert (EaF' : (aF + zget mf (ge + 1))%Z = sumF (fun v => zget mf v) gs (Z.to_nat (ge + 2 - gs))).
    { rewrite EaF. replace (Z.to_nat (ge + 2 - gs)) with (S (Z.to_nat (ge + 1 - gs))) by lia. rewrite sumF_S_last. f_equal. f_equal. lia. }
    assert (BaF' : (0 <= aF + zget mf (ge + 1) <= remF)%Z).
    { rewrite EaF', EremF. apply sumF_prefix_le; [lia|]. intros b Hb. apply (proj1 (proj2 (MFD b ltac:(lia)))). }
    rewrite sm_grow_S in K. replace ((aF <? tF) && (ge <? nInUse + 2 - 1))%Z%bool with true in K
      by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    arun.
    pose proof (ovw_read a0segs m (E + 672) mf (jseg J 672 1032) 258 (ge + 1) _ MTF ltac:(lia) Dq ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget mf (ge + 1))) by lia.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z (zget mf (ge + 1) + aF)) by lia. wstep. wstep. wstep. try rewrite (sx32_of_Z_signed (ge + 1)) by lia. try rewrite (sx32_of_Z (ge + 1)) by lia.
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (K (ge + 1)%Z (aF + zget mf (ge + 1))%Z _ _ _ _ _); [st_eq| | lia| | lia].
      + apply sm_grow_stop. lia.
      + rewrite EaF'. f_equal. lia.
    - (* [comment removed for export] *)
      wstep. wstep. wstep. wstep; if_cases Kx; zify_cond_z Kx.
      + enter_with (IH (ge + 1)%Z (aF + zget mf (ge + 1))%Z gs tF remF m); [st_eq| lia| lia| lia| lia| lia| lia| | exact EremF| lia| exact MTF| unfold ESTATE_SIZE; exact SHe|].
        * rewrite EaF'. f_equal. lia.
        * intros ge' aF' y0 y3 y4 y5 y6 E' Hge' EaF2 B2. eapply K; [exact E'| lia| exact EaF2| exact B2].
      + (* [comment removed for export] *)
        wstep.
        enter_with (K (ge + 1)%Z (aF + zget mf (ge + 1))%Z _ _ _ _ _); [st_eq| | lia| | lia].
        * apply sm_grow_stop. lia.
        * rewrite EaF'. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wlen := [(E + 37708, E + 39256)]%Z.
  Lemma A0_smA_setrow : forall (n : nat) (v t gs ge : Z) (len : zarr) (me m : word -> option byte)
      (ra a0 a2 a3 a4 a5 a6 s2 s3 s5 t6 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < 6)%Z ->
    (0 <= gs <= 258)%Z -> (gs - 1 <= ge <= 258)%Z ->
    u8arr a0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) -> mem_inv a0segs m ->
    munch Wlen me m -> wmono a0segs me m ->
    shzW a0segs Wlen me E (E + ESTATE_SIZE) ->
    frdW a0segs Wlen me (P + 1416) [C8 (Z_to_bv 64 A)] ->
    (forall m' (a0 a2 : word),
      u8arr a0segs m' (E + 37708) (ovb (sm_setrow n len t gs ge v) (jseg J 37708 1548) 1548) -> mem_inv a0segs m' ->
      munch Wlen me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (RI ra a0 (Z_to_bv 64 A) a2 a3 a4 a5 a6 s2 s3 s5 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 ge) (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 gs) t6)
                       F (Z_to_bv 64 0x8a8cc) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RI ra a0 (Z_to_bv 64 v) a2 a3 a4 a5 a6 s2 s3 s5 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 ge) (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 gs) t6)
                     F (Z_to_bv 64 0x8a804) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v t gs ge len me m ra a0 a2 a3 a4 a5 a6 s2 s3 s5 t6 Hv Hv0 Hn Ht Hgs Hge LEN MI MU WM SHe V1416 K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openSF. unfold sm_alpha in *. unfold ESTATE_SIZE in SHe.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    rewrite sm_setrow_S in K.
    (* [comment removed for export] *)
    arun_to 0x8a818%Z.
    (* [comment removed for export] *)
    destruct (Z.ltb_spec v gs) as [Hl|Hl]; [| destruct (Z.ltb_spec ge v) as [Hr|Hr]];
      (wstep; rewrite ?lxor_sign_mod by lia; flags); (wstep; rewrite ?lxor_sign_mod by lia; flags); wstep; wstep; wstep; wstep; wstep.
    all: pose proof (u8arr_store_ok a0segs m (E + 37708) _ (258 * t + v) _ LEN ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    all: wstep; store_addr (E + 37708 + (258 * t + v))%Z; ovb_store1 LEN (258 * t + v)%Z.
    all: lazymatch type of LEN with context [wr8 ?l0 ?i0 ?w] =>
           replace (wr8 l0 i0 w) with (zset l0 i0 (setrow_val gs ge v)) in LEN
             by (unfold wr8, setrow_val, BZ_LESSER_ICOST, BZ_GREATER_ICOST; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia;
                 destruct (Z.leb_spec gs v), (Z.leb_spec v ge); cbn [andb]; first [reflexivity| exfalso; lia]) end.
    (* [comment removed for export] *)
    all: lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V1416 mm MU') as RO end; wstep; clear RO.
    all: wstep; if_cases Ke; zify_cond_z Ke;
      [ enter_with (IH (v + 1)%Z t gs ge (zset len (258 * t + v) (setrow_val gs ge v)) me); [st_eq| lia| lia| lia| lia| lia| lia| exact LEN| assumption| assumption| assumption| unfold ESTATE_SIZE; exact SHe| exact V1416| exact K]
      | assert (n = 0)%nat by lia; subst n; cbn [sm_setrow] in K; wstep;
        enter_with (K _ _ _); [st_eq| exact LEN| assumption| assumption| assumption] ].
  Qed.
End A0SMA.
End ACeilS1.

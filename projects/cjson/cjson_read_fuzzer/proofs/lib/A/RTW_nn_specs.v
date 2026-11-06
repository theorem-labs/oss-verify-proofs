(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_m_a1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_ALLOCATE : Z := 0x31ef4.

(* [comment removed for export] *)
Ltac if2 K := if_cases K; zify_cond K.
(* [comment removed for export] *)
Ltac fold_ext16 :=
  repeat match goal with
  | |- context [sx16 (Z_to_bv 64 ?z)] => is_closed_arith z; let v := eval vm_compute in (bv_unsigned (sx16 (Z_to_bv 64 z))) in
        progress change (sx16 (Z_to_bv 64 z)) with (Z_to_bv 64 v : word)
  | |- context [zx16 (Z_to_bv 64 ?z)] => is_closed_arith z; let v := eval vm_compute in (bv_unsigned (zx16 (Z_to_bv 64 z))) in
        progress change (zx16 (Z_to_bv 64 z)) with (Z_to_bv 64 v : word)
  end.
Ltac fl16 := fold_ext16; fl.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ladder_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
  mem_inv asegs m -> a0 = wz 49 -> s5 = wz n -> 0 <= n < 2^32 ->
  evt asegs (fun ms' => exists (a0' : word),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (wz (rz_log n)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (wz 0x32060) fc None m (seg_rom asegs)
                 /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x31f8c) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros MI -> -> Hn.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  cbv beta delta [wz] in *.
  unfold rz_log.
  lstep; if2 BR.                                   (* [comment removed for export] *)
  2:{ destruct (Z.leb_spec0 n 48); [| exfalso; lia]. clear BR. lstep. lstep. finish. }
  destruct (Z.leb_spec0 n 48); [exfalso; lia| clear BR].
  lstep. lstep; if2 BR.                            (* [comment removed for export] *)
  2:{ destruct (Z.leb_spec0 n 96); [| exfalso; lia]. clear BR. lstep. lstep. finish. }
  destruct (Z.leb_spec0 n 96); [exfalso; lia| clear BR].
  lstep. lstep; if2 BR.                            (* [comment removed for export] *)
  2:{ destruct (Z.leb_spec0 n 448); [| exfalso; lia]. clear BR. lstep. lstep. finish. }
  destruct (Z.leb_spec0 n 448); [exfalso; lia| clear BR].
  lstep. lstep. fl. lstep; if2 BR.                 (* [comment removed for export] *)
  2:{ destruct (Z.leb_spec0 n 3968); [| exfalso; lia]. clear BR. lstep. lstep. finish. }
  destruct (Z.leb_spec0 n 3968); [exfalso; lia| clear BR].
  lstep. lstep. fl. lstep; if2 BR.                 (* [comment removed for export] *)
  2:{ destruct (Z.leb_spec0 n 16128); [| exfalso; lia]. clear BR. lstep. lstep. finish. }
  destruct (Z.leb_spec0 n 16128); [exfalso; lia| clear BR].
  lstep. lstep. fl. lstep; if2 BR.                 (* [comment removed for export] *)
  2:{ destruct (Z.leb_spec0 n 32256); [| exfalso; lia]. clear BR. lstep. lstep. finish. }
  destruct (Z.leb_spec0 n 32256); [exfalso; lia| clear BR].
  lstep. lstep. fl.                                (* [comment removed for export] *)
  lstep. lstep.                                    (* [comment removed for export] *)
  destruct (Z.leb_spec0 n 64512).
  - replace (Z.lxor (Z.b2z (n <? 64513)) 7) with 6 by (destruct (Z.ltb_spec0 n 64513); [reflexivity| lia]). finish.
  - replace (Z.lxor (Z.b2z (n <? 64513)) 7) with 7 by (destruct (Z.ltb_spec0 n 64513); [lia| reflexivity]). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (n <=? _)); lia. Qed.

(* [comment removed for export] *)
Lemma land_m8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
  intros x Hx. replace 18446744073709551608 with ((-8) mod 2^64) by reflexivity.
  rewrite land_mod_pow2_r by lia. replace (-8) with (Z.lnot (Z.ones 3)) by reflexivity. rewrite <- Z.ldiff_land.
  rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma rounded8_eq : forall n, 0 <= n < 2^32 -> Z.land (Z.max n 8 + 7) 18446744073709551608 = rounded8 n.
Proof. intros n Hn. rewrite land_m8 by lia. unfold rounded8, roundup. f_equal. f_equal. lia. Qed.
Lemma rounded8_and7 : forall n, Z.land (rounded8 n) 7 = 0.
Proof. intros n. unfold rounded8, roundup. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. apply Z_mod_mult. Qed.
Lemma rounded8_range : forall n, 0 <= n < 2^32 -> Z.max n 8 <= rounded8 n <= Z.max n 8 + 7 /\ rounded8 n mod 8 = 0.
Proof. intros n Hn. unfold rounded8, roundup. split; [| apply Z_mod_mult]. Z.div_mod_to_equations. lia. Qed.
Lemma rz_size_val : forall n, rz_size n = 16 * 2 ^ rz_log n /\ 16 <= rz_size n <= 2048.
Proof.
  intros n. unfold rz_size. rewrite Z.shiftl_mul_pow2 by (pose proof (rz_log_range n); lia).
  pose proof (rz_log_range n) as R. split; [reflexivity|].
  assert (C : rz_log n = 0 \/ rz_log n = 1 \/ rz_log n = 2 \/ rz_log n = 3 \/ rz_log n = 4 \/ rz_log n = 5 \/ rz_log n = 6 \/ rz_log n = 7) by lia.
  destruct C as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; cbn; lia.
Qed.

Lemma swrap32_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap. change (bv_half_modulus 32) with 2147483648. unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap_rz : forall n, bv_swrap 32 (Z.shiftl 16 (rz_log n mod 32)) = rz_size n.
Proof.
  intros n. pose proof (rz_log_range n) as R. pose proof (rz_size_val n) as [E B]. rewrite Z.mod_small by lia.
  unfold rz_size in *. apply swrap32_small. lia.
Qed.
Lemma usz_eq : forall n, 0 <= n -> n + Z.b2z (n <? 1) = usz n.
Proof. intros n Hn. unfold usz. destruct (Z.ltb_spec0 n 1); cbn; lia. Qed.
Lemma needed0_range : forall n, 0 <= n < 2^32 -> Z.max n 8 + 16 <= needed0 n <= n + 2063.
Proof. intros n Hn. unfold needed0. pose proof (rounded8_range n Hn). pose proof (rz_size_val n). lia. Qed.

Lemma minmax_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
  mem_inv asegs m -> s1 = wz 0 -> a0 = wz 7 -> s3 = wz (rz_log n) -> s5 = wz n -> 0 <= n < 2^32 ->
  evt asegs (fun ms' =>
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (Z.max n 8)) (wz 8) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (wz 0x320a8) fc None m (seg_rom asegs)
                 /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x3208c) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros MI -> -> -> -> Hn.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM. pose proof (rz_log_range n) as RR.
  cbv beta delta [wz] in *.
  lstep; if2 BR.                                   (* [comment removed for export] *)
  - (* [comment removed for export] *) lstep; if2 BR2.             (* [comment removed for export] *)
    + (* [comment removed for export] *) lstep. lstep. lstep; if2 BR3.   (* [comment removed for export] *)
      * replace (Z.max n 8) with n by lia. finish.
      * lstep. replace (Z.max n 8) with 8 by lia. finish.
    + (* [comment removed for export] *) lstep. replace (rz_log n) with 7 by lia.
      lstep. lstep. lstep; if2 BR3.                (* [comment removed for export] *)
      * lstep. replace (Z.max n 8) with 8 by lia. finish.
      * lstep. replace (Z.max n 8) with n by lia. finish.
  - (* [comment removed for export] *) lstep. replace (rz_log n) with 0 by lia.
    lstep; if2 BR2.                                (* [comment removed for export] *)
    + exfalso. lia.
    + lstep. lstep. lstep; if2 BR3.                (* [comment removed for export] *)
      * replace (Z.max n 8) with n by lia. finish.
      * lstep. replace (Z.max n 8) with 8 by lia. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALLOC_DEPTH : Z := 2816.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition alloc_frame (j0 : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 8 j0; C8 (wz 1); C8 (wz 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition a1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n : Z) (S : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (j0 : list byte),
    ms' = MS (mkR ra' (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (wz (if is_primary n then 1 else 0)) (wz (usz n)) a0 a1 a2 a3 a4 a5 a6 a7
                  (wz 8) (wz (needed n)) (wz (rz_size n)) (wz n) (wz A_ALLOC) S (wz (-8)) (wz 7) (wz (A_ALLOC + 2047)) (wz 1)
                  t3 t4 t5 t6)
             F (wz 0x32174) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ rw_cells asegs m' (bv_unsigned sp + -128) (alloc_frame j0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Section A1.
Hypothesis asan_inited_proof : asan_inited_spec.
Hypothesis rss_exceeded_proof : rss_exceeded_spec.
Hypothesis rzsize2log_proof : rzsize2log_spec.

Lemma alloc_a1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (n Sz lo : Z),
  RTREP st m -> RTWF st -> mem_inv asegs m ->
  a0 = wz A_ALLOC -> a1 = wz n -> a2 = wz 8 -> a3 = wz Sz -> a4 = wz 1 -> a5 = wz 1 ->
  0 <= n < 2^32 -> 0 < Sz < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + ALLOC_DEPTH <= bv_unsigned sp ->
  evt asegs (a1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (wz Sz) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_ALLOCATE) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HR WF MI -> -> -> -> -> -> Hn HS ST CEIL LO. unfold a1_post.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof HR as HR0.
  (* [comment removed for export] *)
  (nelimp (rr_alloc st m HR) 5%nat; intros _ _ _ _ KL). change (cells_at asegs m A_MAXUSERSZ) with (ro_cells asegs m 0xa7a38) in KL.
  unfold A_ALLOCATE, ALLOC_DEPTH, A_ALLOC in *. leaf_prep.
  carve_frame 128%nat ST.
  do 14 lstep.                                     (* [comment removed for export] *)
  do 6 lstep.                                      (* [comment removed for export] *)
  lstep.                                           (* [comment removed for export] *)
  pose proof HR0 as HR1. rtrep_high HR1 WF MU WM.
  call asan_inited_proof; [exact HR1 | exact MI | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. rename PC into ST. cbv beta delta [wz] in POST. subst x2.
  assert (E128 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
  rewrite E128 in ST.
  lstep; if_lia.                                   (* [comment removed for export] *)
  lstep.                                           (* [comment removed for export] *)
  pose proof HR0 as HR1. rtrep_high HR1 WF MU WM.
  call rss_exceeded_proof; [exact HR1 | exact MI0 | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. rename PC into ST. rewrite E128 in ST.
  match goal with H : ?x = wz 0 |- _ => cbv beta delta [wz] in H; subst x end.
  lstep; if_lia.                                   (* [comment removed for export] *)
  lstep; if_lia.                                   (* [comment removed for export] *)
  lstep. lstep; if_lia.                            (* [comment removed for export] *)
  lstep. lstep. lstep; if_lia.                     (* [comment removed for export] *)
  lstep. lstep. lstep; if_lia.                     (* [comment removed for export] *)
  lstep. lstep. fl.                                (* [comment removed for export] *)
  lstep. lstep. lstep.                             (* [comment removed for export] *)
  lstep. lstep. lstep. lstep.                      (* [comment removed for export] *)
   (* [comment removed for export] *)
  lstep. fl.                                       (* [comment removed for export] *)
 
  lstep. lstep. lstep.                      (* [comment removed for export] *)
  lstep. lstep; if_lia.                            (* [comment removed for export] *)
  lstep. lstep. lstep. lstep; if_lia.              (* [comment removed for export] *)
  lstep. lstep.                                    (* [comment removed for export] *)
  lstep. lstep.                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  call ladder_spec; [ | reflexivity | reflexivity | exact Hn | ].
  { match goal with H : mem_inv asegs ?mm |- _ => exact H end. }
  cbv beta delta [wz].
  lstep. fl16.                              (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. fl.    (* [comment removed for export] *)
  lstep.                                           (* [comment removed for export] *)
  callx ltac:(eapply rzsize2log_proof with (k := 0) (lo := lo);
               [ eassumption | lia | reflexivity | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia ]).
  rename PC into ST. rewrite E128 in ST. match goal with H : ?x = wz 0 |- _ => cbv beta delta [wz] in H; subst x end.
  lstep. lstep. fl16.                       (* [comment removed for export] *)
  lstep. lstep. fl.                         (* [comment removed for export] *)
  lstep.                                           (* [comment removed for export] *)
  callx ltac:(eapply rzsize2log_proof with (k := 7) (lo := lo);
               [ eassumption | lia | reflexivity | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia ]).
  rename PC into ST. rewrite E128 in ST. match goal with H : ?x = wz 7 |- _ => cbv beta delta [wz] in H; subst x end.
 
  (* [comment removed for export] *)
  call minmax_spec; [ eassumption | reflexivity | reflexivity | reflexivity | reflexivity | exact Hn | ].
  cbv beta delta [wz].
  lstep. lstep. lstep. lstep. lstep. fl.   (* [comment removed for export] *)
  lstep. lstep. lstep. fl.                        (* [comment removed for export] *)
  rewrite (rounded8_eq n Hn). pose proof (rounded8_range n Hn) as R8.
  lstep. rewrite rounded8_and7.                                 (* [comment removed for export] *)
  lstep; if_lia.                                                (* [comment removed for export] *)
  pose proof (rz_size_val n) as [RZE RZR]. pose proof (rz_log_range n) as RLR.
  lstep. lstep. lstep. lstep. fl.                              (* [comment removed for export] *)
  rewrite swrap_rz.
  lstep. lstep. lstep. lstep. fl.                              (* [comment removed for export] *)
  rewrite (usz_eq n) by lia. change (rounded8 n + rz_size n) with (needed0 n). pose proof (needed0_range n Hn) as NR.
  unfold needed. unfold is_primary. unfold KMAXSIZE.
  destruct (Z.leb_spec0 (needed0 n) 65536) as [PR|PR].
  - lstep. destruct (Z.ltb_spec0 (needed0 n) 65537) as [PR'|PR']; [| exfalso; lia]. cbn [Z.b2z].
    lstep. lstep. lstep. fl.                                    (* [comment removed for export] *)
    rewrite Z.land_0_l.
    lstep. lstep. fl. rewrite Z.add_0_l.                        (* [comment removed for export] *)
    unfold usz.
    lstep; if_lia. lstep; if_lia.                               (* [comment removed for export] *)
    lstep. fl. lstep; if_lia.                                   (* [comment removed for export] *)
    finish. unfold alloc_frame. eassumption.
    - lstep. destruct (Z.ltb_spec0 (needed0 n) 65537) as [PR'|PR']; [exfalso; lia|]. cbn [Z.b2z].
    lstep. lstep. lstep. fl.                                    (* [comment removed for export] *)
    change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia.
    lstep. lstep. fl. rewrite (Z.add_comm (rz_size n) (needed0 n)).   (* [comment removed for export] *)
    unfold usz.
    lstep; if_lia. lstep; if_lia.                               (* [comment removed for export] *)
    lstep. fl. lstep; if_lia.                                   (* [comment removed for export] *)
    finish. unfold alloc_frame. eassumption.
Qed.
End A1.


End CeilWrap.
(* [comment removed for export] *)
Ltac if2 K := if_cases K; zify_cond K.
Ltac fold_ext16 :=
  repeat match goal with
  | |- context [sx16 (Z_to_bv 64 ?z)] => is_closed_arith z; let v := eval vm_compute in (bv_unsigned (sx16 (Z_to_bv 64 z))) in
        progress change (sx16 (Z_to_bv 64 z)) with (Z_to_bv 64 v : word)
  | |- context [zx16 (Z_to_bv 64 ?z)] => is_closed_arith z; let v := eval vm_compute in (bv_unsigned (zx16 (Z_to_bv 64 z))) in
        progress change (zx16 (Z_to_bv 64 z)) with (Z_to_bv 64 v : word)
  end.
Ltac fl16 := fold_ext16; fl.
End RTW_m_a1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib2.
Module RTW_m_a3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma alloc_a3_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (n r t ctx S ntr : Z) (hj : list byte) (j0 : list byte) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word) (tj : list byte),
  mem_inv asegs m ->
  s1 = wz (usz n) -> s2 = wz r -> s3 = wz (needed n) -> s4 = wz (rz_size n) -> s5 = wz n -> s7 = wz S ->
  s9 = wz 7 -> s10 = wz t -> s11 = wz 1 ->
  0 <= n < 2^32 -> AIMG_HI <= r -> r + needed n <= alloc_ceiling -> r mod 16 = 0 ->   (* [comment removed for export] *)
  4096 <= t -> t + 4096 <= alloc_ceiling -> 4096 <= ctx -> ctx + 160 <= alloc_ceiling ->   (* [comment removed for export] *)
  (r + needed n <= t \/ t + 4096 <= r) -> (r + needed n <= ctx \/ ctx + 160 <= r) ->
  alloc_ceiling <= S -> S + 2064 <= 2^64 -> 0 <= ntr < 2^32 ->
  alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  rw_cells asegs m (r + rz_size n + -16) [CB 16 hj] ->
  rw_cells asegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
  rw_cells asegs m t [C8 (wz ctx); CB 72 tj] ->
  rw_cells asegs m (ctx + CTX_TID) [C4 (wz 0)] ->
  rw_cells asegs m S [C8 (wz (S + 16)); C8 (wz ntr)] ->
  evt asegs (fun ms' => exists (a2' a4' : word) (b1 : Z) (j1 j8 : list byte) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (S + 16)) (wz ntr) a2' a3 a4' a5 a6 a7
                    s2 s3 (wz (r + rz_size n)) (wz (r + rz_size n + -16)) s6 s7 (wz 0) (wz (r + rz_size n + usz n)) s10 s11 t3 t4 t5 t6)
               F (wz 0x3229c) fc None m' (seg_rom asegs)
      /\ munch [(r + rz_size n + -16, r + rz_size n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (r + rz_size n + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); CB 8 j8]
      /\ Z.land b1 115 = 17 /\ 0 <= b1 < 256)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x3219c) fc None m (seg_rom asegs)).
Proof.
  intros until tj. intros MI -> -> -> -> -> -> -> -> -> Hn R1 R2 R16 T1 T2 C1 C2 DT DC HS1 HS2 NTR SP1 SP2 HDR FR TC CX SC.
  pose proof (munch_refl [(r + rz_size n + -16, r + rz_size n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (rz_size_range n) as (RZ1 & RZ2). pose proof (usz_le_rounded8 n) as (U1 & U2 & U3). pose proof (needed0_range n Hn) as NR.
  assert (ND : rz_size n + usz n <= needed n) by (unfold needed, needed0 in *; destruct (is_primary n); lia).
  assert (NDB : needed n <= n + 4200) by (unfold needed; destruct (is_primary n); lia).
  unfold usz in *. unfold KHIGHMEM_BEG, AIMG_HI, CTX_TID in *. idtac. unfold alloc_frame in FR.
  leaf_prep.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [1;1;2;4;8]%nat) in HDR; [| reflexivity]. cbn [mk_CB_cells app firstn skipn] in HDR.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  replace (Z.land (r + rz_size n) 7) with 0 by (symmetry; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof (junk_byte_range (firstn 1 (skipn 1 hj))) as JB.
  set (hb := bv_unsigned (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn 1 hj)))))) in *.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  rewrite (Z.shiftr_div_pow2 (n `max` 1) 32), (Z.shiftr_div_pow2 n 48) by lia.
  replace (n `max` 1 / 2^32) with 0 by (symmetry; apply Z.div_small; lia).
  replace (n / 2^48) with 0 by (symmetry; apply Z.div_small; lia).
  zstep. sbfix. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  zstep. sbfix. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (sx32_lit 0) by lia.
  lstep. lstep. (* [comment removed for export] *) change (bv_unsigned (Z_to_bv 64 0) ≪ 32) with 0.
  lstep. lstep. (* [comment removed for export] *)
  pose proof (hdr_b1_mid_ok hb JB) as [HB1 HB2]. unfold hdr_b1_mid in HB1, HB2. subst hb.
  finish; [eassumption| | |]; lia.
Qed.


End CeilWrap.
End RTW_m_a3.

(* [comment removed for export] *)
Module RTW_m_a4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma alloc_a4p_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (n r id : Z) (j1 j8 : list byte) (b1 : Z),
  mem_inv asegs m ->
  a0 = wz id -> s0 = wz 1 -> s1 = wz (usz n) -> s2 = wz r -> s4 = wz (r + rz_size n) -> s5 = wz (r + rz_size n + -16) -> s8 = wz 0 ->
  0 <= n < 2^32 -> 0 <= id < 2^32 -> KHIGHMEM_BEG <= r -> r + needed n <= alloc_ceiling -> r mod 16 = 0 ->
  rw_cells asegs m (r + rz_size n + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); CB 8 j8] ->
  ro_cells asegs m 0xa1f80 [C8 (Z_to_bv 64 0xaa278)] -> ro_cells asegs m 0xaa278 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (SH r) [C1 (zb SV_HEAP_LEFT_RZ)] ->
  evt asegs (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 (wz (usz n / 8 * 8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x32398) fc None m' (seg_rom asegs)
      /\ munch [(r + rz_size n + -8, r + rz_size n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (r + rz_size n + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x322a0) fc None m (seg_rom asegs)).
Proof.
  intros until b1. intros MI -> -> -> -> -> -> -> Hn Hid R1 R2 R16 HDR G1 G2 SHD.
  pose proof (munch_refl [(r + rz_size n + -8, r + rz_size n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (rz_size_range n) as (RZ1 & RZ2). pose proof (usz_le_rounded8 n) as (U1 & U2 & U3). pose proof (needed0_range n Hn) as NR.
  assert (NDB : rz_size n + 8 <= needed n <= n + 4200) by (unfold needed, needed0 in *; destruct (is_primary n); lia).
  pose proof (rt_SH_bounds r ltac:(idtac; unfold KHIGHMEM_BEG in R1; lia)) as SB.
  unfold usz, SV_HEAP_LEFT_RZ in *. unfold KHIGHMEM_BEG in *. idtac. cbv beta delta [zb] in SHD.
  leaf_prep.
  lstep. lstep. lstep. (* [comment removed for export] *)
  rewrite (Z.mod_small id), Z.lor_0_l by lia.
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  replace (2147450880 + r ≫ 3) with (SH r) by (unfold SH, SHADOW_OFFSET; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  lstep. (* [comment removed for export] *) fl.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. (* [comment removed for export] *)
  rewrite land_48m8 by lia.
  finish.
Qed.


End CeilWrap.
End RTW_m_a4.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_tpz.
Module RTW_m_aspec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz RTW_m_a1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition AALLOCATE : Z := 0x31ef4.
Definition AALLOCATE_STACK : Z := 2816.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition alloc_deposit (n : Z) : Z := calloc_deposit n + fp n + rp n + (if is_cl24 n then CL24_TAX else 0).
Lemma cl24_tax_nonneg : forall n, 0 <= (if is_cl24 n then CL24_TAX else 0).
Proof. intros n. unfold CL24_TAX. destruct (is_cl24 n); lia. Qed.
Lemma cl24_prim : forall n, bprim n = true -> (if is_cl24 n then CL24_TAX else 0) = (if pclass n =? 24 then CL24_TAX else 0).
Proof. intros n HP. unfold is_cl24. unfold bprim in HP. rewrite HP. reflexivity. Qed.
Lemma cl24_sec : forall n, bprim n = false -> (if is_cl24 n then CL24_TAX else 0) = 0.
Proof. intros n HP. unfold is_cl24. unfold bprim in HP. rewrite HP. reflexivity. Qed.


(* [comment removed for export] *)
Definition alloc_same (st st' : rtstate) : Prop :=
  st_apend st' = st_apend st /\ st_spend st' = st_spend st /\ st_qpend st' = st_qpend st
  /\ st_qtmp st' = st_qtmp st /\ st_qcur st' = st_qcur st.

Definition alloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n : Z) (tr : list Z) (lo : Z) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists r,
        a0' = wz r /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m' /\ gmono g g'
        /\ st_sp0 st' = st_sp0 st /\ st_lf st' = st_lf st /\ alloc_same st st'
        /\ ( (r = 0 /\ st_lb st' = st_lb st /\ st_trs st' = st_trs st /\ budget_ok st g st' g' 0)
           \/ (r <> 0 /\ ablock_range r n /\ ~ In r (map fst (st_lb st))
               /\ (forall Fr k, In (Fr, k) (st_lf st) -> r + n <= Fr \/ Fr + fsz k <= r)
               /\ st_lb st' = (r, n) :: st_lb st /\ trs_put tr (st_trs st) (st_trs st')
               /\ budget_ok st g st' g' (alloc_deposit n)
               /\ exists junk, rw_cells asegs m' r [CB (Z.to_nat n) junk]
                    /\ Forall (fun b => b = zb MALLOC_FILL_BYTE) (firstn (Z.to_nat (Z.min n MALLOC_FILL_MAX)) junk)) )).

(* [comment removed for export] *)
Definition alloc_post_blk (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n : Z) (tr : list Z) (lo : Z) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists r,
        a0' = wz r /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m' /\ gmono g g'
        /\ st_sp0 st' = st_sp0 st /\ st_lf st' = st_lf st /\ alloc_same st st'
        /\ r <> 0 /\ ablock_range r n /\ ~ In r (map fst (st_lb st))
        /\ (forall Fr k, In (Fr, k) (st_lf st) -> r + n <= Fr \/ Fr + fsz k <= r)
        /\ st_lb st' = (r, n) :: st_lb st /\ trs_put tr (st_trs st) (st_trs st')
        /\ budget_ok st g st' g' (alloc_deposit n)
        /\ (exists junk, rw_cells asegs m' r [CB (Z.to_nat n) junk]
               /\ Forall (fun b => b = zb MALLOC_FILL_BYTE) (firstn (Z.to_nat (Z.min n MALLOC_FILL_MAX)) junk))
        /\ st_regions st' = st_regions st /\ st_cache st' = st_cache st).
Lemma alloc_post_blk_post : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g ms mo' g',
  alloc_post_blk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g ms mo' g' ->
  alloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g ms mo' g'.
Proof.
  intros until g'. intros H. unfold alloc_post_blk, alloc_post, rt_post_std in *.
  destruct H as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & E & MI' & r & Er & RTS' & ST' & CP & ES & GM & E1 & E2 & AS
                 & NZ & ABR & NIN & NFR & ELB & TP & BUD & JK & _ & _).
  do 15 eexists. exists m', st'. split; [exact E|]. split; [exact MI'|]. exists r. repeat (split; [assumption|]).
  right. repeat (split; [assumption|]). exact JK.
Qed.

(* [comment removed for export] *)
Definition alloc_post_null (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n : Z) (tr : list Z) (lo : Z) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' =>
        a0' = wz 0 /\ st' = st /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m' /\ gmono g g' /\ budget_ok st g st' g' 0).

Definition allocate_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n S : Z) (tr : list Z) (lo : Z),
  RTS st m mo g -> (forall st0, RTWF st0 -> tpx_ok st0) -> st_apend st = [] ->
  0 <= n < 2^32 ->
  a0 = wz A_ALLOC -> a1 = wz n -> a2 = wz 8 -> a3 = wz S -> a4 = wz 1 -> a5 = wz 1 ->
  tp = wz ATP ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (wz (S + 16)); C4 (wz (zlen tr)); C4 (wz 0)] -> cells_at asegs m (S + 16) (trace_cells tr) ->
  1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr ->
  bv_unsigned sp <= S -> S + BST_SIZE <= st_sp0 st + 4096 ->
  trs_room tr (st_trs st) ->
  alloc_deposit n + rt_prov st <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AALLOCATE_STACK <= bv_unsigned sp -> bv_unsigned sp <= st_sp0 st ->
  mem_inv asegs m ->
  LSCPS asegs (alloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AALLOCATE) fc None m (seg_rom asegs)) mo g.


(* [comment removed for export] *)
Definition alloc_sec_stmt : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte) (mo1 : Model) (g g1 : lghost)
         (st st1 : rtstate) (n S mb : Z) (tr : list Z) (lo : Z) (j0 : list byte),
  RTS st1 m1 mo1 g1 -> (forall st0, RTWF st0 -> tpx_ok st0) -> RTWF st ->
  0 <= n < 2^32 -> bprim n = false -> tp = wz ATP ->
  ablk mb (mb + smapsize n) -> mb mod 4096 = 0 -> mb + smapsize n <= alloc_ceiling ->   (* [comment removed for export] *)
  st_spend st1 = (mb, n) :: st_spend st -> st_sec st1 = st_sec st ++ [(mb, n)] ->
  same_client st st1 -> st_t st1 = st_t st ->
  st_apend st1 = st_apend st -> st_qpend st1 = st_qpend st -> st_qtmp st1 = st_qtmp st -> st_qcur st1 = st_qcur st ->
  st_regions st1 = st_regions st -> st_cache st1 = st_cache st ->
  rw_cells asegs m1 S [C8 (wz (S + 16)); C4 (wz (zlen tr)); C4 (wz 0)] -> cells_at asegs m1 (S + 16) (trace_cells tr) ->
  1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr ->
  bv_unsigned sp <= S -> S + BST_SIZE <= st_sp0 st + 4096 -> trs_room tr (st_trs st) ->
  budget_ok st g st1 g1 (calloc_deposit n) -> alloc_deposit n + rt_prov st <= g_res g -> gmono g g1 ->
  cli_pres st (bv_unsigned sp) m m1 -> errno_same m m1 ->
  stk asegs m1 lo (bv_unsigned sp - 128) -> alloc_ceiling <= lo -> lo + AALLOCATE_STACK <= bv_unsigned sp -> bv_unsigned sp <= st_sp0 st ->
  mem_inv asegs m1 ->
  rw_cells asegs m1 (bv_unsigned sp - 128) (alloc_frame j0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells asegs m1 (SH mb) (zcells (zrep SV_HEAP_LEFT_RZ 512)) ->
  rw_cells asegs m1 (SH (sec_alloc_beg mb + rounded8 n + 4096))
       (zcells (zrep SV_HEAP_LEFT_RZ ((mb + smapsize n - (sec_alloc_beg mb + rounded8 n + 4096)) / 8))) ->
  sec_win g1 mb n ->
  LSCPS asegs (alloc_post_blk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g)
        (MS (mkR (wz 0x32194) (wz (bv_unsigned sp - 128)) gp tp t0 t1 t2 (wz 0) (wz (usz n)) (wz (sec_alloc_beg mb)) a1 a2 a3 a4 a5 a6 a7
                 (wz (sec_alloc_beg mb)) (wz (needed n)) (wz (rz_size n)) (wz n) (wz A_ALLOC) (wz S) (wz (-8)) (wz 7) (wz (st_t st)) (wz 1)
                 t3 t4 t5 t6)
            F (wz 0x32198) fc None m1 (seg_rom asegs)) mo1 g1.


(* [comment removed for export] *)
Definition allocate2_sec_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n S : Z) (tr : list Z) (lo : Z),
  RTS st m mo g -> (forall st0, RTWF st0 -> tpx_ok st0) -> st_apend st = [] ->
  0 <= n < 2^32 -> bprim n = false ->
  a0 = wz A_ALLOC -> a1 = wz n -> a2 = wz 8 -> a3 = wz S -> a4 = wz 1 -> a5 = wz 1 ->
  tp = wz ATP ->
  rw_cells asegs m S [C8 (wz (S + 16)); C4 (wz (zlen tr)); C4 (wz 0)] -> cells_at asegs m (S + 16) (trace_cells tr) ->
  1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr ->
  bv_unsigned sp <= S -> S + BST_SIZE <= st_sp0 st + 4096 ->
  trs_room tr (st_trs st) ->
  alloc_deposit n + rt_prov st <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AALLOCATE_STACK <= bv_unsigned sp -> bv_unsigned sp <= st_sp0 st ->
  mem_inv asegs m ->
  LSCPS2 asegs (alloc_post_null ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g)
               (alloc_post_blk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AALLOCATE) fc None m (seg_rom asegs)) mo g.


(* [comment removed for export] *)
Definition alloc_post_blk0 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n : Z) (tr : list Z) (lo : Z) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists r,
        a0' = wz r /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m' /\ gmono g g'
        /\ st_sp0 st' = st_sp0 st /\ st_lf st' = st_lf st /\ alloc_same st st'
        /\ r <> 0 /\ ablock_range r n /\ ~ In r (map fst (st_lb st))
        /\ (forall Fr k, In (Fr, k) (st_lf st) -> r + n <= Fr \/ Fr + fsz k <= r)
        /\ st_lb st' = (r, n) :: st_lb st /\ trs_put tr (st_trs st) (st_trs st')
        /\ budget_ok st g st' g' (alloc_deposit n)
        /\ (exists junk, rw_cells asegs m' r [CB (Z.to_nat n) junk]
               /\ Forall (fun b => b = zb MALLOC_FILL_BYTE) (firstn (Z.to_nat (Z.min n MALLOC_FILL_MAX)) junk))).
Definition alloc_post_null0 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n : Z) (tr : list Z) (lo : Z) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' =>
        a0' = wz 0 /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m' /\ gmono g g'
        /\ st_sp0 st' = st_sp0 st /\ st_lf st' = st_lf st /\ alloc_same st st'
        /\ st_lb st' = st_lb st /\ st_trs st' = st_trs st /\ budget_ok st g st' g' 0).

Definition allocate2_fresh_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n S : Z) (tr : list Z) (lo : Z),
  RTS st m mo g -> (forall st0, RTWF st0 -> tpx_ok st0) -> st_apend st = [] ->
  0 <= n < 2^32 -> bprim n = true -> fresh_cls st (pclass n) ->
  a0 = wz A_ALLOC -> a1 = wz n -> a2 = wz 8 -> a3 = wz S -> a4 = wz 1 -> a5 = wz 1 ->
  tp = wz ATP ->
  rw_cells asegs m S [C8 (wz (S + 16)); C4 (wz (zlen tr)); C4 (wz 0)] -> cells_at asegs m (S + 16) (trace_cells tr) ->
  1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr ->
  bv_unsigned sp <= S -> S + BST_SIZE <= st_sp0 st + 4096 ->
  trs_room tr (st_trs st) ->
  alloc_deposit n + rt_prov st <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AALLOCATE_STACK <= bv_unsigned sp -> bv_unsigned sp <= st_sp0 st ->
  mem_inv asegs m ->
  LSCPS2 asegs (alloc_post_null0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g)
               (alloc_post_blk0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AALLOCATE) fc None m (seg_rom asegs)) mo g.


End CeilWrap.
End RTW_m_aspec.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_cid.
Module RTW_m_cidw2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_cid.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma cid_block2_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : Z),
  mem_inv asegs m -> s3 = wz s -> 513 <= s <= 65536 -> s mod 8 = 0 ->
  evt asegs (fun ms' => exists (a2' a3' a4' a5' a6' : word),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (classid s)) a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (wz 0x32584) fc None m (seg_rom asegs)
                 /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x324a8) fc None m (seg_rom asegs)).
Proof.
  intros until s. intros MI -> Hs Hm8.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  cbv beta delta [wz] in *.
  do 55 lstep.
  let v := reg_val 11 in
  lazymatch v with Z_to_bv 64 ?e => replace e with (classid s); [ | rewrite <- (cid_code_ok s) by lia; reflexivity ] end.
  finish.
Qed.


End CeilWrap.
End RTW_m_cidw2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
Module RTW_m_leaves2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition leafc (st : rtstate) (m : word -> option byte) : Prop :=
  ro_cells asegs m 0xaaf58 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0)]
  /\ ro_cells asegs m 0xaaf7c [C4 (Z_to_bv 64 30)]
  /\ ro_cells asegs m 0xa9adc [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xa9ae0 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xa9ae4 [C4 (Z_to_bv 64 0)]
  /\ ro_cells asegs m 0x12c4e1 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0)]
  /\ ro_cells asegs m 0x13bd40 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                               C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ ro_cells asegs m 0x5dd260 [C4 (Z_to_bv 64 0)]
  /\ ro_cells asegs m 0xa2bd8 [C8 (Z_to_bv 64 0x10)]
  /\ ro_cells asegs m 6148600 [C8 (Z_to_bv 64 0x5fe5f8)]
  /\ ro_cells asegs m 0x5fe5f8 [C8 (Z_to_bv 64 (st_ctx st))]
  /\ rw_cells asegs m (st_ctx st + 152) [C8 (Z_to_bv 64 (st_t st))].

Lemma leafc_of_RTREP : forall st m, RTREP st m -> leafc st m.
Proof. intros st m HR. exact (leaf_cells st m HR). Qed.

(* [comment removed for export] *)
Definition leafc_ivs (st : rtstate) : list (Z * Z) :=
  [(0xa2bd8, 0xa2be0); (0xa9adc, 0xa9ae8); (0xaaf58, 0xaaf80); (0x12c4e1, 0x12c4e3); (0x13bd40, 0x13bd90);
   (0x5dd1f8, 0x5dd200); (0x5dd260, 0x5dd264); (0x5fe5f8, 0x5fe600); (st_ctx st + 152, st_ctx st + 160)].
Lemma leafc_munch : forall st W m m',
  munch W m m' -> wmono asegs m m' ->
  (forall lo hi a b, In (lo, hi) W -> In (a, b) (leafc_ivs st) -> hi <= a \/ b <= lo) ->
  leafc st m -> leafc st m'.
Proof.
  intros st W m m' MU WM HD (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  assert (D : forall a b, In (a, b) (leafc_ivs st) -> forall a' n, a <= a' -> a' + n <= b -> disjoint_from W a' n).
  { intros a b Hab a' n H1 H2. clear - HD Hab H1 H2. induction W as [|[lo hi] W' IH]; [exact I|]. cbn. split.
    - destruct (HD lo hi a b ltac:(left; reflexivity) Hab); lia.
    - apply IH. intros lo' hi' a0 b0 Hin Hab'. apply (HD lo' hi' a0 b0); [right; exact Hin| exact Hab']. }
  Local Ltac tro K D a b := eapply (ro_cells_transport asegs _ _ _ _ _ K); [eassumption| apply (D a b); [cbn; tauto| cbn; lia| cbn; lia]].
  unfold leafc.
  split; [tro K1 D 0xaaf58 0xaaf80|]. split; [tro K2 D 0xaaf58 0xaaf80|]. split; [tro K3 D 0xa9adc 0xa9ae8|].
  split; [tro K4 D 0xa9adc 0xa9ae8|]. split; [tro K5 D 0xa9adc 0xa9ae8|]. split; [tro K6 D 0x12c4e1 0x12c4e3|].
  split; [tro K7 D 0x13bd40 0x13bd90|]. split; [tro K8 D 0x5dd260 0x5dd264|]. split; [tro K9 D 0xa2bd8 0xa2be0|].
  split; [tro K10 D 0x5dd1f8 0x5dd200|]. split; [tro K11 D 0x5fe5f8 0x5fe600|].
  eapply (rw_cells_transport asegs _ _ _ _ _ K12); [eassumption| eassumption| apply (D (st_ctx st + 152) (st_ctx st + 160)); [cbn; tauto| cbn; lia| cbn; lia]].
Qed.

(* [comment removed for export] *)
Definition tiny_spec_c (entry : Z) (needs_tp : bool) (res : word -> word -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  leafc st m -> mem_inv asegs m -> (needs_tp = true -> tp = wz ATP) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
               (fun a0' _ _ => res ra a0'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz entry) fc None m (seg_rom asegs)).

Ltac tiny_intro_c :=
  intros until lo; intros HR MI TP ST CEIL LO;
  lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU; pose proof (wmono_refl asegs m) as WM end;
  pose proof HR as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12); clear HR.
Ltac keep_only l :=
  repeat match goal with H : ro_cells _ _ ?a _ |- _ => lazymatch l with context [a] => fail | _ => clear H end end;
  repeat match goal with H : rw_cells _ _ (st_ctx _ + _) _ |- _ => clear H end.

Theorem can_poison_c : tiny_spec_c A_CAN_POISON_FN false (fun _ a0' => a0' = wz 1).
Proof.
  unfold tiny_spec_c. tiny_intro_c. unfold A_CAN_POISON_FN. keep_only [0xa9adc]. leaf_prep.
  lstep. lstep. fl. lstep. lstep. fl. lstep.
  finish. reflexivity.
Qed.

Theorem lsan_disabled_c : tiny_spec_c A_LSAN_DISABLED_FN true (fun _ a0' => a0' = wz 0).
Proof.
  unfold tiny_spec_c. tiny_intro_c. specialize (TP eq_refl). subst tp. unfold A_LSAN_DISABLED_FN. keep_only [0xa2bd8; 0x5dd260]. leaf_prep.
  lstep. lstep. fl. clear K9. lstep. fl. lstep. fl. lstep. fl. lstep.
  finish. reflexivity.
Qed.

Definition get_current_thread_c_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  leafc st m -> RTWF st -> mem_inv asegs m -> tp = wz ATP ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
               (fun a0' _ _ => a0' = wz (st_t st)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_GET_CURRENT_THREAD) fc None m (seg_rom asegs)).

Theorem get_current_thread_c : get_current_thread_c_stmt.
Proof.
  unfold get_current_thread_c_stmt. intros until lo. intros HR WF MI TP ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof HR as (_ & _ & _ & K4 & K5 & _ & _ & _ & _ & K10 & K11 & K12). clear HR.
  pose proof (ctx_range st WF) as CR. pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in CR, TR. olin_all.
  unfold A_GET_CURRENT_THREAD. subst tp. leaf_prep.
  carve_frame 16%nat ST.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *) clear K4 K5.
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *) clear K10.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. reflexivity.
Qed.

Definition get_thread_stats_c_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  leafc st m -> RTWF st -> mem_inv asegs m -> tp = wz ATP ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
               (fun a0' _ _ => a0' = wz (st_t st + T_STATS)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_GET_THREAD_STATS) fc None m (seg_rom asegs)).

Theorem get_thread_stats_c : get_thread_stats_c_stmt.
Proof.
  unfold get_thread_stats_c_stmt. intros until lo. intros HR WF MI TP ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  unfold A_GET_THREAD_STATS. subst tp. leaf_prep.
  carve_frame 16%nat ST.
  lstep. lstep. lstep. (* [comment removed for export] *)
  pose proof HR as HR1.
  eapply (leafc_munch st _ _ _ MU WM) in HR1; [| intros lo' hi' a b Hin Hab; cbn in Hin; destruct Hin as [E|[]]; injection E; intros; subst;
    pose proof (ctx_range st WF) as CR; unfold KHIGHMEM_BEG, AIMG_HI in CR; cbn in Hab;
    destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; lia].
  call get_current_thread_c; [exact HR1 | exact WF | exact MI | reflexivity | rewrite unsigned_lit by lia; exact ST | idtac; lia | rewrite unsigned_lit by lia; lia | ].
  assert (E16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  rewrite E16 in *. clear E16. subst x2. cbv beta delta [wz]. rename PC into ST.
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. unfold T_STATS. apply f_equal. lia.
Qed.

Definition run_malloc_hooks_c_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  leafc st m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
               (fun _ _ _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_RUN_MALLOC_HOOKS) fc None m (seg_rom asegs)).

Theorem run_malloc_hooks_c : run_malloc_hooks_c_stmt.
Proof.
  unfold run_malloc_hooks_c_stmt. intros until lo. intros HR MI ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof HR as (_ & _ & _ & _ & _ & _ & K7 & _). clear HR.
  unfold A_RUN_MALLOC_HOOKS. leaf_prep.
  carve_frame 32%nat ST.
  do 5 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. exact I.
Qed.

Definition run_free_hooks_c_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  leafc st m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
               (fun a0' _ _ => a0' = wz 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_RUN_FREE_HOOKS) fc None m (seg_rom asegs)).

Theorem run_free_hooks_c : run_free_hooks_c_stmt.
Proof.
  unfold run_free_hooks_c_stmt. intros until lo. intros HR MI ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof HR as (_ & _ & _ & _ & _ & _ & K7 & _). clear HR.
  unfold A_RUN_FREE_HOOKS. leaf_prep.
  carve_frame 32%nat ST.
  do 4 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. reflexivity.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac tiny_intro_c :=
  intros until lo; intros HR MI TP ST CEIL LO;
  lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU; pose proof (wmono_refl asegs m) as WM end;
  pose proof HR as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12); clear HR.
Ltac keep_only l :=
  repeat match goal with H : ro_cells _ _ ?a _ |- _ => lazymatch l with context [a] => fail | _ => clear H end end;
  repeat match goal with H : rw_cells _ _ (st_ctx _ + _) _ |- _ => clear H end.
End RTW_m_leaves2.

(* [comment removed for export] *)
Module RTW_m_a5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 RTW_m_leaves2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memtoshadow_cells (m : word -> option byte) : Prop :=
  ro_cells asegs m 0xa1f78 [C8 (Z_to_bv 64 0xa7a78)] /\ ro_cells asegs m 0xa1f80 [C8 (Z_to_bv 64 0xaa278)]
  /\ ro_cells asegs m 0xa1f88 [C8 (Z_to_bv 64 0xaaf68)] /\ ro_cells asegs m 0xa1f90 [C8 (Z_to_bv 64 0xaaf70)]
  /\ ro_cells asegs m 0xa1f98 [C8 (Z_to_bv 64 0xaaf60)] /\ ro_cells asegs m 0xa7acd [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xaa278 [C8 (Z_to_bv 64 0x7fff8000)] /\ ro_cells asegs m 0xaaf60 [C8 (Z_to_bv 64 0x7fffffffffff)]
  /\ ro_cells asegs m 0xaaf68 [C8 (Z_to_bv 64 0)] /\ ro_cells asegs m 0xaaf70 [C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Lemma alloc_a5_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (n ub lo : Z) (g0 : byte),
  leafc st m -> mem_inv asegs m -> memtoshadow_cells m ->
  s1 = wz (usz n) -> s4 = wz ub -> s6 = wz (usz n / 8 * 8) ->
  0 <= n < 2^32 -> usz n mod 8 <> 0 -> ablk ub (ub + usz n + 8) -> ub + usz n + 8 <= alloc_ceiling -> ub mod 8 = 0 ->   (* [comment removed for export] *)
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  rw_cells asegs m (SH (ub + usz n / 8 * 8)) [C1 g0] ->      (* [comment removed for export] *)
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 (wz (ub + usz n / 8 * 8)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz 0x32440) fc None m' (seg_rom asegs)
      /\ munch [(SH (ub + usz n / 8 * 8), SH (ub + usz n / 8 * 8) + 1); (bv_unsigned sp - 16, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (SH (ub + usz n / 8 * 8)) [C1 (zb (usz n mod 8))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x323b0) fc None m (seg_rom asegs)).
Proof.
  intros until g0. intros LC MI GG -> -> -> Hn M8 U1 U2 U8 ST HCL LO SHB.
  pose proof (munch_refl [(SH (ub + usz n / 8 * 8), SH (ub + usz n / 8 * 8) + 1); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (usz_le_rounded8 n) as (V1 & V2 & V3).
  set (p := ub + usz n / 8 * 8) in *.
  assert (P8 : p mod 8 = 0) by (subst p; rewrite Z.add_mod, U8, Z_mod_mult by lia; reflexivity).
  assert (PR : ub <= p /\ p + 8 <= alloc_ceiling) by (subst p; unfold usz in *; Z.div_mod_to_equations; lia).
  pose proof (ablk_lin _ _ U1) as (UL1 & UL2 & UL3 & UL4). pose proof (ablk_disj_band _ _ U1) as UD. unfold AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in UL1, UD. clear U1.
  pose proof (rt_SH_bounds p ltac:(idtac; lia)) as SB.
  unfold usz, SV_HEAP_LEFT_RZ in *. unfold KHIGHMEM_BEG, AIMG_HI in *. idtac.
  leaf_prep.
  destruct GG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  lstep. (* [comment removed for export] *)
  call can_poison_c; [exact LC| exact MI| intros; discriminate| exact ST| idtac; lia| lia|].
  cbv beta delta [wz] in *. subst x2. rename PC into ST.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) fold p.
  lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
 
  destruct UD as [UD|UD].
  { (* [comment removed for export] *)
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. fl. lstep. fl. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    replace (2147450880 + p ≫ 3) with (SH p) by (unfold SH, SHADOW_OFFSET; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    lstep. lstep. lstep. fl. (* [comment removed for export] *)
    rewrite (land_m1_7 (n `max` 1)) by lia.
    zstep. sbfix.
    finish.
  }
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. lstep. fl. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. fl. lstep. lstep. fl. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  replace (2147450880 + p ≫ 3) with (SH p) by (unfold SH, SHADOW_OFFSET; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  lstep. lstep. lstep. fl. (* [comment removed for export] *)
  rewrite (land_m1_7 (n `max` 1)) by lia.
  zstep. sbfix.
  finish.
Qed.


End CeilWrap.
End RTW_m_a5.

(* [comment removed for export] *)
Module RTW_m_a6.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_cid RTW_m_cidw2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition fill_cells (m : word -> option byte) : Prop :=
  ro_cells asegs m 0xa1f78 [C8 (Z_to_bv 64 0xa7a78)] /\ ro_cells asegs m 0xa1fa0 [C8 (Z_to_bv 64 0xa3e08)]
  /\ ro_cells asegs m 0xa3e08 [C8 (Z_to_bv 64 A_MUSL_MEMSET)]
  /\ ro_cells asegs m 0xa7aa4 [C4 (Z_to_bv 64 4096)] /\ ro_cells asegs m 0xa7aac [C4 (Z_to_bv 64 MALLOC_FILL_BYTE)].

Lemma disjoint_high_img : forall W a n, Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> a + n <= AIMG_HI -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Ha; [exact I|]. cbn. pose proof (Forall_inv HW) as H1. cbn [fst] in H1.
  split; [lia| apply IH; [exact (Forall_inv_tail HW)| exact Ha]].
Qed.
Lemma fill_cells_high : forall W m m', munch W m m' -> Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> fill_cells m -> fill_cells m'.
Proof.
  intros W m m' MU HW nelH_; (nelim nelH_ 5%nat; intros K1 K2 K3 K4 K5). unfold fill_cells.
  repeat match goal with |- _ /\ _ => split end;
  (eapply ro_cells_transport; [eassumption| exact MU| apply disjoint_high_img; [exact HW| unfold AIMG_HI; cbn; lia]]).
Qed.

(* [comment removed for export] *)
Lemma disjoint_out_img : forall W a n, Forall (fun iv : Z * Z => snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) W ->
  AIMG_LO <= a -> a + n <= AIMG_HI -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Ha Hb; [exact I|]. cbn. pose proof (Forall_inv HW) as H1. cbn [fst snd] in H1.
  split; [lia| apply IH; [exact (Forall_inv_tail HW)| exact Ha| exact Hb]].
Qed.
Lemma fill_cells_out : forall W m m', munch W m m' -> Forall (fun iv : Z * Z => snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) W -> fill_cells m -> fill_cells m'.
Proof.
  intros W m m' MU HW nelH_; (nelim nelH_ 5%nat; intros K1 K2 K3 K4 K5). unfold fill_cells.
  repeat match goal with |- _ /\ _ => split end;
  (eapply ro_cells_transport; [eassumption| exact MU| apply disjoint_out_img; [exact HW| unfold AIMG_LO; cbn; lia| unfold AIMG_HI; cbn; lia]]).
Qed.

Lemma classid_small : forall s, s <= 512 -> classid s = (s + 31) / 32.
Proof. intros s Hs. unfold classid. destruct (Z.leb_spec0 s 512); [reflexivity| lia]. Qed.

(* [comment removed for export] *)
Lemma alloc_a6t_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (n ub cidp : Z) (sj3 : word) (j0 : list byte) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  mem_inv asegs m -> fill_cells m ->
  s1 = wz (usz n) -> s4 = wz ub -> a0 = wz (cidp - 8 * pclass n) -> a1 = wz (pclass n) ->
  0 <= n < 2^32 -> bprim n = true -> (4096 <= cidp /\ (cidp + 8 <= AIMG_LO \/ AIMG_HI <= cidp)) -> cidp + 8 <= alloc_ceiling ->   (* [comment removed for export] *)
  alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
  rw_cells asegs m cidp [C8 sj3] ->
  evt asegs (fun ms' => exists (a3' : word) (sj3' : word) (m' : word -> option byte),
      ms' = MS (mkR (wz 0x325d4) sp gp tp t0 t1 t2 s0 s1 (wz ub) (wz MALLOC_FILL_BYTE) (wz (Z.min (usz n) MALLOC_FILL_MAX)) a3' a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz A_MUSL_MEMSET) fc None m' (seg_rom asegs)
      /\ munch [(cidp, cidp + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11)
      /\ rw_cells asegs m' cidp [C8 sj3'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x32584) fc None m (seg_rom asegs)).
Proof.
  intros until v11. intros MI FC -> -> -> -> Hn HP C1 C2 SP1 SP2 FR TC.
  pose proof (munch_refl [(cidp, cidp + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (prim_facts n HP) as (PC & _). (nelimp (usz_le_rounded8 n) 3%nat; intros V1 V2 V3).
  (nelim FC 5%nat; intros K1 K2 K3 K4 K5).
  unfold usz, MALLOC_FILL_BYTE, MALLOC_FILL_MAX, A_MUSL_MEMSET, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in *. idtac.
  unfold alloc_frame in FR. leaf_prep.
  lstep. lstep. (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 (pclass n) 3) by lia.
  replace (cidp - 8 * pclass n + pclass n * 2 ^ 3) with cidp by lia.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if2 BR2. (* [comment removed for export] *)
  + lstep. lstep. fl. lstep. lstep. fl. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 636404)) with (Z_to_bv 64 636404) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite (Z.min_l (n `max` 1) 4096) by lia.
    finish; eassumption.
  + lstep. (* [comment removed for export] *)
    lstep. lstep. fl. lstep. lstep. fl. lstep. lstep.
    replace (ret_pc (Z_to_bv 64 636404)) with (Z_to_bv 64 636404) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite (Z.min_r (n `max` 1) 4096) by lia.
    finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma alloc_a6p_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (n ub lo : Z) (sj0 sj1 sj2 sj3 : word) (j0 : list byte) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  leafc st m -> RTWF st -> mem_inv asegs m -> fill_cells m -> tp = wz ATP ->
  s1 = wz (usz n) -> s3 = wz (needed n) -> s4 = wz ub ->
  0 <= n < 2^32 -> bprim n = true ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
  rw_cells asegs m (st_t st + 2800) [C8 sj0; C8 sj1; C8 sj2] ->
  rw_cells asegs m (st_t st + 2912 + 8 * pclass n) [C8 sj3] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (sj0' sj1' sj2' sj3' : word) (m' : word -> option byte),
      ms' = MS (mkR (wz 0x325d4) sp gp tp t0' t1' t2' s0 s1 (wz ub) (wz MALLOC_FILL_BYTE) (wz (Z.min (usz n) MALLOC_FILL_MAX)) a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz A_MUSL_MEMSET) fc None m' (seg_rom asegs)
      /\ munch [(st_t st + 2800, st_t st + 2824); (st_t st + 2912 + 8 * pclass n, st_t st + 2912 + 8 * pclass n + 8);
                (bv_unsigned sp - 32, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11)
      /\ rw_cells asegs m' (st_t st + 2800) [C8 sj0'; C8 sj1'; C8 sj2']
      /\ rw_cells asegs m' (st_t st + 2912 + 8 * pclass n) [C8 sj3'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x32440) fc None m (seg_rom asegs)).
Proof.
  intros until v11. intros LC WF MI FC TP -> -> -> Hn HP ST HCL LO SPH FR TS TC.
  set (cidp := st_t st + 2912 + 8 * pclass n) in *.
  pose proof (munch_refl [(st_t st + 2800, st_t st + 2824); (cidp, cidp + 8); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (prim_facts n HP) as (PC & _). (nelimp (usz_le_rounded8 n) 3%nat; intros V1 V2 V3). pose proof (needed0_range n Hn) as NR.
  pose proof (rounded8_range n Hn) as R8. pose proof (rz_size_range n) as RZ.
  assert (NDp : needed n = needed0 n) by (unfold needed; unfold bprim in HP; rewrite HP; reflexivity).
  assert (N8 : needed0 n mod 8 = 0) by (unfold needed0; apply mod0_add; [lia| tauto | apply (mod0_trans _ 8 16); [lia|lia|reflexivity|tauto]]).
  assert (NP : needed0 n <= 65536) by (unfold bprim, is_primary, KMAXSIZE in HP; apply Z.leb_le in HP; exact HP).
  pose proof (t_range st WF) as TR.
  unfold usz, KHIGHMEM_BEG, AIMG_HI in *. idtac. rewrite NDp in *.
  leaf_prep. subst tp.
  lstep. (* [comment removed for export] *)
  call get_thread_stats_c; [exact LC| exact WF| exact MI| reflexivity| exact ST| idtac; lia| lia|].
  cbv beta delta [wz] in *. subst x2. rename PC into ST. unfold T_STATS.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. fl. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  match goal with H : mem_inv _ _ |- _ => rename H into MI end.
  replace (st_t st + 2912) with (cidp - 8 * pclass n) by (subst cidp; lia).
  olin_all.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (FC1 : fill_cells mx) end.
  { eapply fill_cells_out; [exact MU| | exact FC]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_LO, AIMG_HI; lia. }
  lstep; if2 BR. (* [comment removed for export] *)
  - call cid_block2_spec; [exact MI| reflexivity| lia| exact N8|]. cbv beta delta [wz].
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    change (classid (needed0 n)) with (pclass n).
    callx ltac:(eapply alloc_a6t_spec with (n := n) (cidp := cidp);
      [ exact MI| exact FC1| reflexivity| reflexivity| reflexivity| reflexivity| exact Hn| exact HP| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; subst cidp; lia| subst cidp; idtac; lia| idtac; lia| lia| exact FR| exact TC ]).
    finish; eassumption.
  - lstep. lstep. (* [comment removed for export] *)
    rewrite (Z.shiftr_div_pow2 _ 5) by lia. change (2^5) with 32. unfold pclass in *. rewrite <- (classid_small (needed0 n)) by lia.
    lstep. (* [comment removed for export] *)
    callx ltac:(eapply alloc_a6t_spec with (n := n) (cidp := cidp);
      [ exact MI| exact FC1| reflexivity| reflexivity| reflexivity| reflexivity| exact Hn| exact HP| unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI; subst cidp; lia| subst cidp; idtac; lia| idtac; lia| lia| exact FR| exact TC ]).
    finish; eassumption.
Qed.


End CeilWrap.
End RTW_m_a6.

(* [comment removed for export] *)
Module RTW_m_a6s.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 RTW_m_leaves2 RTW_m_a6 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.
Set Printing Depth 100.

(* [comment removed for export] *)
Lemma alloc_a6s_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (n ub lo : Z) (sj0 sj1 sj2 sj3 : word) (j0 : list byte) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  leafc st m -> RTWF st -> mem_inv asegs m -> fill_cells m -> tp = wz ATP ->
  s1 = wz (usz n) -> s3 = wz (needed n) -> s4 = wz ub ->
  0 <= n < 2^32 -> bprim n = false ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
  rw_cells asegs m (st_t st + 2800) [C8 sj0; C8 sj1; C8 sj2] ->
  rw_cells asegs m (st_t st + 2904) [C8 sj3] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (sj0' sj1' sj2' sj3' : word) (m' : word -> option byte),
      ms' = MS (mkR (wz 0x325d4) sp gp tp t0' t1' t2' s0 s1 (wz ub) (wz MALLOC_FILL_BYTE) (wz (Z.min (usz n) MALLOC_FILL_MAX)) a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz A_MUSL_MEMSET) fc None m' (seg_rom asegs)
      /\ munch [(st_t st + 2800, st_t st + 2824); (st_t st + 2904, st_t st + 2912); (bv_unsigned sp - 32, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11)
      /\ rw_cells asegs m' (st_t st + 2800) [C8 sj0'; C8 sj1'; C8 sj2']
      /\ rw_cells asegs m' (st_t st + 2904) [C8 sj3'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x32440) fc None m (seg_rom asegs)).
Proof.
  intros until v11. intros LC WF MI FC TP -> -> -> Hn HP ST HCL LO SPH FR TS TL.
  pose proof (munch_refl [(st_t st + 2800, st_t st + 2824); (st_t st + 2904, st_t st + 2912); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (sec_facts n HP) as (F1 & F2 & F3 & F4 & F5 & F6). pose proof (usz_le_rounded8 n) as (V1 & V2 & V3). pose proof (rounded8_range n Hn) as R8.
  pose proof (t_range st WF) as TR.
  unfold usz, KHIGHMEM_BEG, AIMG_HI, MALLOC_FILL_BYTE, MALLOC_FILL_MAX, A_MUSL_MEMSET in *. idtac. rewrite F6 in *.
  unfold alloc_frame in FR. leaf_prep. subst tp.
  lstep. (* [comment removed for export] *)
  call get_thread_stats_c; [exact LC| exact WF| exact MI| reflexivity| exact ST| idtac; lia| lia|].
  cbv beta delta [wz] in *. subst x2. rename PC into ST. unfold T_STATS.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. fl. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) lstep; if_lia. (* [comment removed for export] *)
  match goal with H : mem_inv _ _ |- _ => rename H into MI end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (FC1 : fill_cells mx) end.
  { eapply fill_cells_out; [exact MU| | exact FC]. pose proof (t_range st WF) as TRq. olin TRq. pose proof alloc_ceiling_range as ACRq.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_LO, AIMG_HI, CEIL in *; lia. }
  destruct FC1 as (K1' & K2' & K3' & K4' & K5'). unfold MALLOC_FILL_BYTE, A_MUSL_MEMSET in K3', K5'.
  lstep. lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. lstep. fl. lstep. lstep. (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 636404)) with (Z_to_bv 64 636404) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite (Z.min_r (n `max` 1) 4096) by lia.
  finish; eassumption.
Qed.


End CeilWrap.
End RTW_m_a6s.

(* [comment removed for export] *)
Module RTW_m_a7.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 RTW_m_leaves2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma alloc_a7_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (n r id b1 lo : Z) (j1 bj j0 : list byte) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  leafc st m -> mem_inv asegs m -> tp = wz ATP ->
  s1 = wz (usz n) -> s2 = wz r -> s4 = wz (r + rz_size n) -> s5 = wz (r + rz_size n + -16) ->
  0 <= n < 2^32 -> 0 <= id < 2^32 -> 0 <= b1 < 256 -> Z.land b1 115 = 17 ->
  AIMG_HI <= r -> r + needed n <= alloc_ceiling -> r mod 16 = 0 ->
  (st_ctx st + 160 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= st_ctx st) -> st_ctx st + 160 <= alloc_ceiling -> (r + needed n <= st_ctx st \/ st_ctx st + 160 <= r) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
  rw_cells asegs m (r + rz_size n + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)] ->
  (16 < rz_size n -> rw_cells asegs m r [CB 16 bj]) ->
  evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (b1' : Z) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 128)) gp tp t0' t1' t2' v0 v1 (wz (r + rz_size n)) a1' a2' a3' a4' a5' a6' a7'
                    v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3' t4' t5' t6')
               F (ret_pc vra) fc None m' (seg_rom asegs)
      /\ munch [(r, r + 16); (r + rz_size n + -16, r + rz_size n); (bv_unsigned sp - 32, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + 128)
      /\ rw_cells asegs m' (r + rz_size n + -16) [C1 (zb CHUNK_ALLOCATED); C1 (zb b1'); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)]
      /\ Z.land b1' 127 = HDR_BYTE1_MALLOC /\ 0 <= b1' < 256
      /\ (16 < rz_size n -> rw_cells asegs m' r [C8 (wz KALLOCBEG_MAGIC); C8 (wz (r + rz_size n + -16))]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x325d4) fc None m (seg_rom asegs)).
Proof.
  intros until v11. intros LC MI TP -> -> -> -> Hn Hid Hb1 Hb1' R1 R2 R16 C1 C2 DC ST HCL LO SPH FR HDR BH.
  pose proof (munch_refl [(r, r + 16); (r + rz_size n + -16, r + rz_size n); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (rz_size_range n) as (RZ1 & RZ2). (nelimp (usz_le_rounded8 n) 3%nat; intros U1 U2 U3). pose proof (needed0_range n Hn) as NR.
  assert (NDB : rz_size n + 8 <= needed n <= n + 4200) by (unfold needed, needed0 in *; destruct (is_primary n); lia).
  unfold usz, CHUNK_ALLOCATED, HDR_BYTE1_MALLOC, KALLOCBEG_MAGIC, KHIGHMEM_BEG, AIMG_HI in *. idtac. cbv beta delta [zb] in HDR.
  unfold alloc_frame in FR. leaf_prep. subst tp.
  assert (LCW : forall m', munch [(r, r + 16); (r + rz_size n + -16, r + rz_size n); (bv_unsigned sp - 32, bv_unsigned sp)] m m' ->
                wmono asegs m m' -> leafc st m').
  { intros m' MU' WM'. eapply (leafc_munch st _ _ _ MU' WM'); [| exact LC].
    intros lo' hi' a b Hin Hab. cbn in Hab. unfold AIMG_HI in *.
    destruct Hab as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; injection E; intros; subst;
      (destruct Hin as [E'|[E'|[E'|[]]]]; injection E'; intros; subst; lia). }
  destruct (Z.eq_dec (rz_size n) 16) as [RZ16|RZBIG].
  - (* [comment removed for export] *)
    clear BH.
  lstep. (* [comment removed for export] *)
    call lsan_disabled_c; [exact LC| exact MI| reflexivity| exact ST| idtac; lia| lia|].
    cbv beta delta [wz] in *. subst x2. rename PC into ST.
    lstep. (* [comment removed for export] *) fl.
    replace (bv_unsigned (Z_to_bv 8 b1)) with b1 by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; rewrite Z.mod_small; lia).
    lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
    change (Z.lor (Z.land b1 243) 0) with (hdr_b1_fin b1). pose proof (hdr_b1_fin_ok b1 Hb1 Hb1') as [FB1 FB2].
    lstep. (* [comment removed for export] *)
    zstep. sbfix. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    call run_malloc_hooks_c; [apply LCW; assumption| exact MI| exact ST| idtac; lia| lia|].
    cbv beta delta [wz] in *. rename PC into ST.
    lstep. do 13 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp + 128).
    finish; [eassumption| exact FB1| lia| lia| intros; exfalso; lia].
  - (* [comment removed for export] *)
    specialize (BH ltac:(lia)).
  lstep. (* [comment removed for export] *)
    call lsan_disabled_c; [exact LC| exact MI| reflexivity| exact ST| idtac; lia| lia|].
    cbv beta delta [wz] in *. subst x2. rename PC into ST.
    lstep. (* [comment removed for export] *) fl.
    replace (bv_unsigned (Z_to_bv 8 b1)) with b1 by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; rewrite Z.mod_small; lia).
    lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
    change (Z.lor (Z.land b1 243) 0) with (hdr_b1_fin b1). pose proof (hdr_b1_fin_ok b1 Hb1 Hb1') as [FB1 FB2].
    lstep. (* [comment removed for export] *)
    zstep. sbfix. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    call run_malloc_hooks_c; [apply LCW; assumption| exact MI| exact ST| idtac; lia| lia|].
    cbv beta delta [wz] in *. rename PC into ST.
    lstep. do 13 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp + 128).
    finish; [eassumption| exact FB1| lia| lia| intros _; assumption].
Qed.


End CeilWrap.
End RTW_m_a7.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib4.
Module RTW_m_d1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_lock RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AASAN_FREE : Z := 0x31bb8.
Definition ADEALLOCATE : Z := 0x31be0.
Definition AQCHUNK : Z := 0x36088.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
(* [comment removed for export] *)
Lemma leafc_keep : forall st W m m', munch W m m' -> wmono asegs m m' ->
  Forall (fun iv : Z * Z => (snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= st_ctx st \/ st_ctx st + 160 <= fst iv)) W -> leafc st m -> leafc st m'.   (* [comment removed for export] *)
Proof.
  intros st W m m' MU WM HW LC. eapply leafc_munch; [exact MU| exact WM| | exact LC].
  intros lo hi a b Hin Hin'. rewrite Forall_forall in HW. specialize (HW _ Hin). cbn [fst snd] in HW.
  unfold leafc_ivs in Hin'. cbn [In] in Hin'. unfold AIMG_LO, AIMG_HI in HW.
  repeat (destruct Hin' as [E|Hin']; [injection E as <- <-; lia|]). destruct Hin'.
Qed.

Lemma free_d1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (A n S lo : Z) (b1 : byte) (cid uw sj3 sj4 : word),
  leafc st m -> RTWF st -> mem_inv asegs m -> tp = wz ATP ->
  a0 = wz A_ALLOC -> a1 = wz A -> a2 = wz 0 -> a3 = wz 0 -> a4 = wz S -> a5 = wz 1 ->
  0 <= n < 2^40 -> A mod 16 = 0 -> AIMG_HI + 16 <= A -> A + 8 <= alloc_ceiling -> 0 <= S < 2^64 ->
  hdr_b1_ok (bv_unsigned b1) ->
  (A + 8 <= st_t st \/ st_t st + 4096 <= A - 16) -> (A + 8 <= st_ctx st \/ st_ctx st + 160 <= A - 16) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 96 <= bv_unsigned sp ->
  rw_cells asegs m (A + -16) [C1 (zb CHUNK_ALLOCATED); C1 b1; C2 (wz (size_hi n)); C4 (wz (size_lo n)); C8 cid] ->
  rw_cells asegs m A [C8 uw] ->
  rw_cells asegs m (st_t st + 2824) [C8 sj3; C8 sj4] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (sj3' sj4' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz A_ALLOC) (wz (A + -16)) (wz A) (wz S) a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz AQCHUNK) fc None m' (seg_rom asegs)
      /\ munch [(A + -16, A + -12); (A, A + 8); (st_t st + 2824, st_t st + 2840); (bv_unsigned sp - 96, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (A + -16) [C1 (zb CHUNK_QUARANTINE); C1 b1; C2 (wz (size_hi n)); C4 (wz (size_lo n)); C8 cid]
      /\ rw_cells asegs m' A [C8 (wz (2^64 - 2^32))]
      /\ rw_cells asegs m' (st_t st + 2824) [C8 sj3'; C8 sj4'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ADEALLOCATE) fc None m (seg_rom asegs)).
Proof.
  intros until sj4. intros LC WF MI TP -> -> -> -> -> -> Hn A16 A1 A2 HS Hb1 TA CA ST HCL LO HDR UW TS.
  (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros cb ck CL1 CL2 CL3). (nelimp (loose0_range st WF cb ck CL1) 4%nat; intros CR1 CR2 CR3 CR4).
  pose proof (munch_refl [(A + -16, A + -12); (A, A + 8); (st_t st + 2824, st_t st + 2840); (bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (nelimp (size_hilo n Hn) 3%nat; intros SH1 SL1 SHL). pose proof (t_range st WF) as TR.
  pose proof (bv_unsigned_in_range 8 b1) as Rb. unfold bv_modulus in Rb. cbn in Rb.
  unfold CHUNK_ALLOCATED, CHUNK_QUARANTINE, KHIGHMEM_BEG, AIMG_HI, ADEALLOCATE, AQCHUNK, A_ALLOC in *. idtac.
  leaf_prep. subst tp.
  carve_frame 64%nat ST.
  do 9 lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  do 8 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  assert (HWL : Forall (fun iv : Z * Z => (snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= st_ctx st \/ st_ctx st + 160 <= fst iv))
                        [(A + -16, A + -12); (A, A + 8); (st_t st + 2824, st_t st + 2840); (bv_unsigned sp - 96, bv_unsigned sp)]).
  { pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT. olin_all. unfold AIMG_LO, AIMG_HI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (leafc_keep st _ m mx MU WM HWL LC) as LC0 end.
  call run_free_hooks_c; [exact LC0| eassumption| rewrite ?unsigned_lit by lia; exact ST| idtac; lia| rewrite ?unsigned_lit by lia; lia|].
  cbv beta delta [wz] in *. match goal with H : ?x = Z_to_bv 64 0 |- _ => subst x end. restk. rewrite ?unsigned_lit in ST by lia.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  rewrite (land_align4' (A + -16)) by (first [lia| Z.div_mod_to_equations; lia]).
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  replace ((((A + -16) ≪ 3) mod 18446744073709551616) mod 32) with 0
    by (symmetry; rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8; rewrite (Z.mod_small ((A + -16) * 8) 18446744073709551616) by lia; Z.div_mod_to_equations; lia).
  change (bv_swrap 32 (255 ≪ 0)) with 255. change (bv_swrap 32 (2 ≪ 0)) with 2. change (bv_swrap 32 (3 ≪ 0)) with 3.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app _ _ [_; _; _] [_; _])) in HDR as [HW HR]. cbn [cells_size Cells.csize Nat.add] in HR.
  apply hdr_word_join in HW; [| lia| lia].
  set (q := bv_unsigned b1 + 256 * size_hi n) in HW.
  pose proof (cas_word q ltac:(lia)) as [CW1 CW2].
  assert (AL4 : (A + -16) mod 4 = 0) by (Z.div_mod_to_equations; lia).
  assert (AR : 0 <= A + -16 < 2^64) by lia.
  amo_zstep. (* [comment removed for export] *)
  change (wz (2 + 256 * q)) with (Z_to_bv 64 (2 + 256 * q)). rewrite (sx32_lit (2 + 256 * q)) by lia.
  lstep. (* [comment removed for export] *)
  rewrite CW1.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  rewrite CW2.
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
 
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  match goal with H : rw_cells _ _ (A + -16) [C4 _] |- _ => apply hdr_word_split in H; [| lia| lia]; rename H into HW' end.
  lstep. (* [comment removed for export] *) cbv beta.
  lstep. (* [comment removed for export] *)
  rewrite (hdr_b1_type (bv_unsigned b1) Hb1).
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (leafc_keep st _ m mx MU WM HWL LC) as LC2 end.
  call get_thread_stats_c; [exact LC2| exact WF| eassumption| reflexivity| rewrite ?unsigned_lit by lia; exact ST| idtac; lia| rewrite ?unsigned_lit by lia; lia|].
  cbv beta delta [wz] in *. match goal with H : ?x = Z_to_bv 64 _ |- _ => subst x end. restk. rewrite ?unsigned_lit in ST by lia. unfold T_STATS.
  match goal with H : rw_cells _ _ (A + -16 + Z.of_nat 4) _ |- _ => replace (A + -16 + Z.of_nat 4) with (A + -12) in H by lia; rename H into HR' end.
  lstep. (* [comment removed for export] *) rewrite zx16_lit by lia.
  lstep. (* [comment removed for export] *) rewrite zx32_lit by lia.
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  do 8 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => rename H into FR' end.
  release_frame FR' ST (bv_unsigned sp).
  match goal with H1 : rw_cells _ ?mx (A + -16) [_;_;_], H2 : rw_cells _ ?mx (A + -12) _ |- _ =>
    replace (A + -12) with (A + -16 + Z.of_nat (cells_size [C1 (zb 3); C1 b1; C2 (Z_to_bv 64 (size_hi n))])) in H2 by (cbn; lia);
    pose proof (proj2 (rw_cells_app mx (A + -16) [_;_;_] [_;_]) (conj H1 H2)) as HDR' end.
  cbn [app] in HDR'.
  finish; eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
End RTW_m_d1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_lock.
Module RTW_q_drainw.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_lock RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_lock.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AQDRAIN : Z := 0x33b08.
Lemma A_QUAR_val : A_QUAR = 683760. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition drain_frame (j0 : list byte) (vs3 vs2 vs1 vs0 vra : word) : list cell :=
  [CB 8 j0; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra].

(* [comment removed for export] *)
Lemma drain_a1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (C ng gf gl gb nt tf tl tb lo : Z) (gnx : word) (b2 b3 : byte),
  let U := bv_unsigned b2 + 256 * bv_unsigned b3 in
  mem_inv asegs m ->
  a0 = wz A_QUAR -> a1 = wz C ->
  0 < ng -> 0 < nt -> ng + nt < 2^63 -> 0 <= gf < 2^64 -> 0 <= tf < 2^64 -> 0 <= tl < 2^64 ->
  0 <= gb -> 0 <= tb -> gb + tb < 2^63 ->
  (4096 <= C /\ (C + 32 <= AIMG_LO \/ AIMG_HI <= C)) -> C + 32 <= alloc_ceiling ->   (* [comment removed for export] *)
  AIMG_HI <= gl -> gl + 8 <= alloc_ceiling -> (C + 32 <= gl \/ gl + 8 <= C) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  rw_cells asegs m (A_QUAR + 152) [C4 (wz (lkw 0 0 U))] ->
  rw_cells asegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz gb)] ->
  rw_cells asegs m C [C8 (wz nt); C8 (wz tf); C8 (wz tl); C8 (wz tb)] ->
  rw_cells asegs m gl [C8 gnx] ->
  evt asegs (fun ms' => exists (t0' t1' a4' a5' a6' a7' : word) (j0 : list byte) (m' : word -> option byte),
      ms' = MS (mkR ra (wz (bv_unsigned sp - 48)) gp tp t0' t1' t2 s0 s1 a0 a1 a2 a3 a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33bcc) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (A_QUAR + 152, A_QUAR + 156); (A_QUAR + 160, A_QUAR + 192); (C, C + 32); (gl, gl + 8)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp - 48)
      /\ rw_cells asegs m' (bv_unsigned sp - 48) (drain_frame j0 s3 s2 s1 s0 ra)
      /\ rw_cells asegs m' (A_QUAR + 152) [C4 (wz (lkw 0 0 U))]
      /\ rw_cells asegs m' (A_QUAR + 160) [C8 (wz (ng + nt)); C8 (wz gf); C8 (wz tl); C8 (wz (gb + tb))]
      /\ rw_cells asegs m' C [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
      /\ rw_cells asegs m' gl [C8 (wz tf)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQDRAIN) fc None m (seg_rom asegs)).
Proof.
  intros until b3. intros U MI -> -> Hng Hnt Hngt Hgf Htf Htl Hgb Htb Hgbt HC1 HC2 Hgl1 Hgl2 DJ ST HCL LO QL QH TC GL.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A_QUAR + 152, A_QUAR + 156); (A_QUAR + 160, A_QUAR + 192); (C, C + 32); (gl, gl + 8)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3. unfold bv_modulus in R2, R3. cbn in R2, R3.
  assert (HU : 0 <= U < 65536) by (subst U; lia). assert (EU : U = bv_unsigned b2 + 256 * bv_unsigned b3) by reflexivity. clearbody U.
  unfold AQDRAIN, drain_frame, AIMG_LO, AIMG_HI in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in QL, QH.
  replace (683760 + 152) with 683912 in QL by reflexivity. replace (683760 + 160) with 683920 in QH by reflexivity.
  pose proof (lkw_range 0 0 U ltac:(lia) ltac:(lia) HU) as LR.
  leaf_prep.
  carve_frame 48%nat ST.
  do 6 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  amo_zstep. (* [comment removed for export] *)
  pose proof (sx32_word_facts (lkw 0 0 U) LR) as XF. cbv zeta in XF.
  remember (sx32 (Z_to_bv 64 (lkw 0 0 U))) as xv eqn:Exv. (nelim XF 3%nat; intros XR XM _).
  (nelimp (lane0_facts (bv_unsigned xv) 0 U XR XM ltac:(lia) HU) 5%nat; intros L1 L2 L3 L4 L5).
  lstep. lstep. lstep. (* [comment removed for export] *) rewrite L1.
  lstep. (* [comment removed for export] *) rewrite L2.
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite L3.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  match type of QL with rw_cells _ ?mx _ _ =>
    apply (qlock_w3 mx 683912 _ 1 0 b2 b3) in QL; [| lia| lia| apply cas_le4; [lia| lia| lia| rewrite <- EU; exact L5]] end.
  lstep. (* [comment removed for export] *)
  match type of QL with rw_cells _ ?mx _ _ => apply qlock_w1 in QL; [| lia| lia]; rewrite <- EU in QL end.
  try rewrite unsigned_lit in * by lia.
  finish; eassumption.
Qed.


(* [comment removed for export] *)
Lemma drain_a0_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (C gb nt tf tl tb lo : Z) (b2 b3 : byte),
  let U := bv_unsigned b2 + 256 * bv_unsigned b3 in
  mem_inv asegs m ->
  a0 = wz A_QUAR -> a1 = wz C ->
  0 < nt < 2^63 -> 0 <= tf < 2^64 -> 0 <= tl < 2^64 ->
  0 <= gb -> 0 <= tb -> gb + tb < 2^63 ->
  (4096 <= C /\ (C + 32 <= AIMG_LO \/ AIMG_HI <= C)) -> C + 32 <= alloc_ceiling ->   (* [comment removed for export] *)
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  rw_cells asegs m (A_QUAR + 152) [C4 (wz (lkw 0 0 U))] ->
  rw_cells asegs m (A_QUAR + 160) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz gb)] ->
  rw_cells asegs m C [C8 (wz nt); C8 (wz tf); C8 (wz tl); C8 (wz tb)] ->
  evt asegs (fun ms' => exists (t0' t1' a4' a5' a6' a7' : word) (j0 : list byte) (m' : word -> option byte),
      ms' = MS (mkR ra (wz (bv_unsigned sp - 48)) gp tp t0' t1' t2 s0 s1 a0 a1 a2 a3 a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33bcc) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (A_QUAR + 152, A_QUAR + 156); (A_QUAR + 160, A_QUAR + 192); (C, C + 32)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp - 48)
      /\ rw_cells asegs m' (bv_unsigned sp - 48) (drain_frame j0 s3 s2 s1 s0 ra)
      /\ rw_cells asegs m' (A_QUAR + 152) [C4 (wz (lkw 0 0 U))]
      /\ rw_cells asegs m' (A_QUAR + 160) [C8 (wz nt); C8 (wz tf); C8 (wz tl); C8 (wz (gb + tb))]
      /\ rw_cells asegs m' C [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQDRAIN) fc None m (seg_rom asegs)).
Proof.
  intros until b3. intros U MI -> -> Hnt Htf Htl Hgb Htb Hgbt HC1 HC2 ST HCL LO QL QH TC.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A_QUAR + 152, A_QUAR + 156); (A_QUAR + 160, A_QUAR + 192); (C, C + 32)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3. unfold bv_modulus in R2, R3. cbn in R2, R3.
  assert (HU : 0 <= U < 65536) by (subst U; lia). assert (EU : U = bv_unsigned b2 + 256 * bv_unsigned b3) by reflexivity. clearbody U.
  unfold AQDRAIN, drain_frame, AIMG_LO, AIMG_HI in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in QL, QH.
  replace (683760 + 152) with 683912 in QL by reflexivity. replace (683760 + 160) with 683920 in QH by reflexivity.
  pose proof (lkw_range 0 0 U ltac:(lia) ltac:(lia) HU) as LR.
  leaf_prep.
  carve_frame 48%nat ST.
  do 6 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  amo_zstep. (* [comment removed for export] *)
  pose proof (sx32_word_facts (lkw 0 0 U) LR) as XF. cbv zeta in XF.
  remember (sx32 (Z_to_bv 64 (lkw 0 0 U))) as xv eqn:Exv. (nelim XF 3%nat; intros XR XM _).
  (nelimp (lane0_facts (bv_unsigned xv) 0 U XR XM ltac:(lia) HU) 5%nat; intros L1 L2 L3 L4 L5).
  lstep. lstep. lstep. (* [comment removed for export] *) rewrite L1.
  lstep. (* [comment removed for export] *) rewrite L2.
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite L3.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  match type of QL with rw_cells _ ?mx _ _ =>
    apply (qlock_w3 mx 683912 _ 1 0 b2 b3) in QL; [| lia| lia| apply cas_le4; [lia| lia| lia| rewrite <- EU; exact L5]] end.
  lstep. (* [comment removed for export] *)
  match type of QL with rw_cells _ ?mx _ _ => apply qlock_w1 in QL; [| lia| lia]; rewrite <- EU in QL end.
  try rewrite unsigned_lit in * by lia.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma drain_ret_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (j0 : list byte) (vs3 vs2 vs1 vs0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ng gf gl gb lo : Z),
  mem_inv asegs m ->
  a0 = wz A_QUAR ->
  0 <= gb <= QUAR_MAX_SIZE ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 48 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (drain_frame j0 vs3 vs2 vs1 vs0 vra) ->
  rw_cells asegs m (A_QUAR + 64) [C8 (wz QUAR_MAX_SIZE); C8 (wz QUAR_MIN_SIZE); C8 (wz QUAR_MAX_CACHE)] ->
  rw_cells asegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz gb)] ->
  evt asegs (fun ms' => exists (a1' a4' : word),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 48)) gp tp t0 t1 t2 vs0 vs1 a0 a1' a2 a3 a4' a5 a6 a7
                    vs2 vs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m (seg_rom asegs)
      /\ stk asegs m lo (bv_unsigned sp + 48))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33bcc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI -> Hgb ST HCL LO SPH FR QC QH.
  unfold drain_frame, QUAR_MAX_SIZE, QUAR_MIN_SIZE, QUAR_MAX_CACHE in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in QC, QH.
  replace (683760 + 64) with 683824 in QC by reflexivity. replace (683760 + 160) with 683920 in QH by reflexivity.
  leaf_prep.
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  do 5 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp + 48).
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma drain_rec_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (j0 : list byte) (vs3 vs2 vs1 vs0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ng gf gl gb lo : Z) (b2 b3 : byte),
  let U := bv_unsigned b2 + 256 * bv_unsigned b3 in
  mem_inv asegs m ->
  a0 = wz A_QUAR ->
  QUAR_MAX_SIZE < gb < 2^63 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 48 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (drain_frame j0 vs3 vs2 vs1 vs0 vra) ->
  rw_cells asegs m (A_QUAR + 64) [C8 (wz QUAR_MAX_SIZE); C8 (wz QUAR_MIN_SIZE); C8 (wz QUAR_MAX_CACHE)] ->
  rw_cells asegs m (A_QUAR + 152) [C4 (wz (lkw 0 0 U))] ->
  rw_cells asegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz gb)] ->
  evt asegs (fun ms' => exists (t0' a4' a5' a6' a7' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 48)) gp tp t0' t1 t2 vs0 vs1 a0 (wz QUAR_MIN_SIZE) a2 a3 a4' a5' a6' a7'
                    vs2 vs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33cac) fc None m' (seg_rom asegs)
      /\ munch [(A_QUAR + 152, A_QUAR + 156)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + 48)
      /\ rw_cells asegs m' (A_QUAR + 152) [C4 (wz (lkw 0 1 U))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33bcc) fc None m (seg_rom asegs)).
Proof.
  intros until b3. intros U MI -> Hgb ST HCL LO SPH FR QC QL QH.
  pose proof (munch_refl [(683912, 683916)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3. unfold bv_modulus in R2, R3. cbn in R2, R3.
  assert (HU : 0 <= U < 65536) by (subst U; lia). assert (EU : U = bv_unsigned b2 + 256 * bv_unsigned b3) by reflexivity. clearbody U.
  unfold drain_frame, QUAR_MAX_SIZE, QUAR_MIN_SIZE, QUAR_MAX_CACHE in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in QC, QL, QH.
  replace (683760 + 64) with 683824 in QC by reflexivity. replace (683760 + 152) with 683912 in QL by reflexivity.
  replace (683760 + 160) with 683920 in QH by reflexivity.
  pose proof (lkw_range 0 0 U ltac:(lia) ltac:(lia) HU) as LR.
  leaf_prep.
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  try change (bv_swrap 32 256) with 256. try change (bv_swrap 32 65280) with 65280.
  amo_zstep. (* [comment removed for export] *)
  pose proof (sx32_word_facts (lkw 0 0 U) LR) as XF. cbv zeta in XF.
  remember (sx32 (Z_to_bv 64 (lkw 0 0 U))) as xv eqn:Exv. (nelim XF 3%nat; intros XR XM _).
  (nelimp (lane1_facts (bv_unsigned xv) 0 U XR XM ltac:(lia) HU) 5%nat; intros L1 L2 L3 L4 L5).
  lstep. lstep. lstep. (* [comment removed for export] *) rewrite L1.
  lstep. (* [comment removed for export] *) rewrite L2.
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *) rewrite L3.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 5 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp + 48).
  match type of QL with rw_cells _ ?my _ _ => assert (QL' : rw_cells asegs my 683912 [C4 (Z_to_bv 64 (lkw 0 1 U))]) end.
  { match type of QL with rw_cells _ ?mx _ _ =>
      apply (qlock_w3 mx 683912 _ 0 1 b2 b3) in QL; [| lia| lia| apply cas_le4; [lia| lia| lia| rewrite <- EU; exact L5]] end.
    apply qlock_w1 in QL; [| lia| lia]. rewrite <- EU in QL. exact QL. }
  finish; eassumption.
Qed.


End CeilWrap.
End RTW_q_drainw.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Frame Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_tpz.
Import RTW_m_a1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_specs.
Import RTW_m_aspec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Definition large_alloc_nn_specW : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n lo : Z),
  RTS st m mo g ->
  0 <= n -> bprim n = false -> needed n <= 2^40 ->
  a0 = wz A_SECONDARY -> a1 = wz A_GSTATS -> a2 = wz (needed n) -> a3 = wz 8 ->
  tp = wz ATP ->
  SEC_ALLOC_COST n + SEC_SLOT_TAX + rt_prov st <= g_res g ->
  mmap_placeable mo (smapsize n) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ALARGE_ALLOC_STACK ->
  mem_inv asegs m ->
  LSCPS asegs (sec_alloc2_post_blkW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ALARGE_ALLOC) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ms_a0 (ms : machine_state) : word := reg_get (ms_regs ms) 10.
Lemma ms_a0_MS : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F pc fc rv m ro,
  ms_a0 (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv m ro) = a0.
Proof. intros. reflexivity. Qed.
Definition nz_post (P : machine_state -> Model -> lghost -> Prop) : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => P ms' mo' g' /\ ms_a0 ms' <> wz 0.
Lemma wz_nz : forall r, 0 < r < 2^64 -> wz r <> wz 0.
Proof.
  intros r Hr E. apply (f_equal bv_unsigned) in E. unfold wz in E. rewrite !unsigned_lit in E by lia. lia.
Qed.

(* [comment removed for export] *)
Definition refill_room (st : rtstate) (cls : Z) : Prop :=
  navail st cls < nrefill cls -> r_mapped (rg st cls) + 262144 <= KFREEARRAY_OFF.
Definition refill_nn_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (cls lo : Z),
  RTS st m mo g ->
  1 <= cls <= 30 -> cch st cls = [] ->
  a0 = wz (acache st) -> a1 = wz (pcaddr st cls) -> a2 = wz A_ALLOC -> a3 = wz cls ->
  tp = wz ATP ->
  rt_prov st <= g_res g ->
  refill_room st cls ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  mem_inv asegs m ->
  LSCPS asegs (refill2_post 1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AREFILL) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
Definition cnn_ok (st : rtstate) (mo : Model) (n : Z) : Prop :=
  if bprim n then refill_room st (pclass n) else mmap_placeable mo (smapsize n).

(* [comment removed for export] *)
Definition combined_alloc_nn_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n lo : Z),
  RTS st m mo g -> (forall st0, RTWF st0 -> tpx_ok st0) -> st_apend st = [] ->
  0 <= n < 2^32 ->
  a0 = wz A_ALLOC -> a1 = wz (acache st) -> a2 = wz (needed n) -> a3 = wz 8 ->
  tp = wz ATP ->
  calloc_deposit n + rt_prov st <= g_res g ->
  cnn_ok st mo n ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ACALLOC_STACK -> bv_unsigned sp <= st_sp0 st ->
  mem_inv asegs m ->
  LSCPS asegs (nz_post (calloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ACALLOC) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
Definition alloc_post_nn (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n : Z) (tr : list Z) (lo : Z) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' =>
    nz_post (alloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g) ms' mo' g'
    /\ (bprim n = false -> alloc_post_blk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g ms' mo' g').
Definition allocate_nn_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n S : Z) (tr : list Z) (lo : Z),
  RTS st m mo g -> (forall st0, RTWF st0 -> tpx_ok st0) -> st_apend st = [] ->
  0 <= n < 2^32 ->
  a0 = wz A_ALLOC -> a1 = wz n -> a2 = wz 8 -> a3 = wz S -> a4 = wz 1 -> a5 = wz 1 ->
  tp = wz ATP ->
  rw_cells asegs m S [C8 (wz (S + 16)); C4 (wz (zlen tr)); C4 (wz 0)] -> cells_at asegs m (S + 16) (trace_cells tr) ->
  1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr ->
  bv_unsigned sp <= S -> S + BST_SIZE <= st_sp0 st + 4096 ->
  trs_room tr (st_trs st) ->
  alloc_deposit n + rt_prov st <= g_res g ->
  cnn_ok st mo n ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AALLOCATE_STACK <= bv_unsigned sp -> bv_unsigned sp <= st_sp0 st ->
  mem_inv asegs m ->
  LSCPS asegs (alloc_post_nn ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AALLOCATE) fc None m (seg_rom asegs)) mo g.


End CeilWrap.

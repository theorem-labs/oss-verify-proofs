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
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRep MRepAux MTree.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Lemma srliw_small a k : 0 <= a < 2^31 -> 0 <= k -> bv_swrap 32 (Z.shiftr (bv_wrap 32 a) k) = Z.shiftr a k.
Proof.
  intros Ha Hk. change (bv_wrap 32 a) with (a mod 2^32). rewrite Z.mod_small by lia.
  apply swrap32_small. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]|].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Lemma lor_small n a b : 0 <= n -> 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros Hn Ha Hb. pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)) as NN. split; [exact NN|].
  destruct (Z.eq_dec a 0) as [->|A0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|B0]; [rewrite Z.lor_0_r; lia|].
  assert (P : 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [apply zb_lor_eq0 in E; lia|]. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n P)).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia.
  - apply (proj1 (Z.log2_lt_pow2 b n ltac:(lia))). lia.
Qed.
Lemma shiftr_small n a k : 0 <= a < 2^n -> 0 <= k -> 0 <= Z.shiftr a k < 2^n.
Proof.
  intros Ha Hk. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition rDB32 : Z := 125613361.   (* [comment removed for export] *)
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.

Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof. unfold rdbi. pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

Definition rdebruijn_bytes : list byte :=
  Eval vm_compute in (match image_bytes rsegs DEBRUIJN 32 with Some bs => bs | None => [] end).

Lemma rdebruijn_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m DEBRUIJN [CB 32 rdebruijn_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold DEBRUIJN; lia | unfold DEBRUIJN; cbn; lia]. Qed.

Lemma rdebruijn_read : forall m k, mem_inv rsegs m -> 0 <= k < 32 ->
  ov_read_bytes rsegs m (wa (DEBRUIJN + rdbi k)) 1 = Some [b8 k].
Proof.
  intros m k MI Hk.
  destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  pose proof (rdbi_range k) as R.
  rewrite (bytes_at_read rsegs m DEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
  assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
  destruct Hn as (n & -> & Hn).
  Ltac solve_db := vm_compute; reflexivity.
  do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed.

(* [comment removed for export] *)
Lemma mul_srliw27 k : 0 <= k < 32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (2 ^ k * rDB32)))) 27) = rdbi k.
Proof.
  intros Hk. unfold rdbi.
  assert (P : 0 < 2 ^ k <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
  rewrite unsigned_lit by (unfold rDB32; nia).
  change (bv_wrap 32 (2 ^ k * rDB32)) with ((2 ^ k * rDB32) mod 2^32).
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
  apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rclz_v4 (x : Z) : Z :=
  let v1 := Z.lor (Z.shiftr x 2) x in
  let v2 := Z.lor v1 (Z.shiftr x 1) in
  let w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1) in
  let w3 := Z.lor (Z.shiftr w2 4) w2 in
  Z.lor (Z.shiftr w3 8) w3.
Definition clz_pow (x : Z) : Z := Z.land (rclz_v4 x + 1) (Z.lxor (rclz_v4 x) 18446744073709551615).
Definition clz_notv (x : Z) : Z :=
  let v1 := Z.lor (Z.shiftr x 2) (Z.shiftr x 1) in
  let v2 := Z.lor v1 (Z.shiftr v1 2) in
  let v3 := Z.lor v2 (Z.shiftr v2 4) in
  let v4 := Z.lor v3 (Z.shiftr v3 8) in
  Z.lxor v4 18446744073709551615.
Definition clz_fn (x : Z) : bool := (clz_pow x =? 2 ^ Z.log2 x) && (rclz_v4 x <? 2 ^ 13).
Lemma clz_check_true : forallb clz_fn (zseq 11 8181) = true.
Proof. (lazymatch goal with |- @eq ?T _ ?r => vm_cast_no_check (@eq_refl T r) end). Qed.   (* [comment removed for export] *)
Lemma clz_pow_eq x : 11 <= x < 8192 -> clz_pow x = 2 ^ Z.log2 x /\ 0 <= rclz_v4 x < 2 ^ 13.
Proof.
  intros Hx. pose proof (forallb_zseq clz_fn 11 8181 x clz_check_true ltac:(lia) ltac:(lia)) as X. unfold clz_fn in X.
  apply andb_prop in X. destruct X as [X1 X2].
  apply Z.eqb_eq in X1. apply Z.ltb_lt in X2. split; [exact X1| split; [|exact X2]].
  unfold rclz_v4. repeat first [apply Z.lor_nonneg; split | apply Z.shiftr_nonneg]; lia.
Qed.
Definition stc_q (q : Z) : Z :=
  if q <? 10 then q else
    let x := q + 1 in
    let i := 4 * Z.log2 x - 4 in
    let i := if size_class (i + 1) <? x then i + 2 else i in
    if size_class i <? x then i + 1 else i.
Definition stc_fn (q : Z) : bool :=
  let sc := stc_q q in (0 <=? sc) && (sc <? 48) && (q + 1 <=? size_class sc)
                    && ((q <? 10) || ((3 <=? Z.log2 (q + 1)) && (Z.log2 (q + 1) <=? 12))).
Lemma stc_check_true : forallb stc_fn (zseq 0 8191) = true.
Proof. (lazymatch goal with |- @eq ?T _ ?r => vm_cast_no_check (@eq_refl T r) end). Qed.   (* [comment removed for export] *)
Lemma size_to_class_q n : 0 <= n -> size_to_class n = stc_q ((n + 3) / 16).
Proof.
  intros Hn. unfold size_to_class, stc_q, IB, clz32.
  replace (Z.shiftr (n + 4 - 1) 4) with ((n + 3) / 16) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 4) with 16; f_equal; lia).
  set (q := (n + 3) / 16). cbv zeta.
  replace ((28 - (31 - Z.log2 (q + 1))) * 4 + 8) with (4 * Z.log2 (q + 1) - 4) by lia.
  reflexivity.
Qed.
Lemma size_to_class_props n : 0 <= n < MMAP_THRESHOLD ->
  0 <= size_to_class n < 48 /\ n + 4 <= 16 * size_class (size_to_class n)
  /\ (10 <= (n + 3) / 16 -> 3 <= Z.log2 ((n + 3) / 16 + 1) <= 12).
Proof.
  intros Hn. unfold MMAP_THRESHOLD in Hn. rewrite size_to_class_q by lia.
  assert (Q : 0 <= (n + 3) / 16 < 8191) by (Z.div_mod_to_equations; lia).
  pose proof (forallb_zseq stc_fn 0 8191 ((n + 3) / 16) stc_check_true ltac:(lia) ltac:(lia)) as X. unfold stc_fn in X. cbv zeta in X.
  apply andb_prop in X. destruct X as [X X4]. apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
  apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply Z.leb_le in X3.
  split; [lia|]. split; [Z.div_mod_to_equations; lia|].
  intros HQ. apply orb_prop in X4. destruct X4 as [X4|X4]; [apply Z.ltb_lt in X4; lia|].
  apply andb_prop in X4. destruct X4 as [X5 X6]. apply Z.leb_le in X5. apply Z.leb_le in X6. lia.
Qed.

Lemma lxor_4k_124 k : 3 <= k <= 12 -> Z.lxor (k * 4) 124 = 124 - 4 * k.
Proof. intros Hk. assert (H : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
  destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; reflexivity. Qed.

Lemma lor_even_1 a : 0 <= a -> Z.even a = true -> Z.lor a 1 = a + 1.
Proof. intros Ha He.
  assert (D : Z.land a 1 = 0). { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. exact He. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity. Qed.

Definition entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 MLOCK) a0 a1 a2 a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 DEBRUIJN) (Z_to_bv 64 (size_to_class n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x23f00) fc None m' (seg_rom rsegs)
    /\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk rsegs m' lo (bv_unsigned sp + -48)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma malloc_entry_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
  a0 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
  stk rsegs m lo (bv_unsigned sp) -> 0x64000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
  rw_cells rsegs m NEED_LOCKS [C1 (b8 0)] ->
  evt rsegs (entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 malloc_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros HA N ST ILO LO MI NL. subst a0.
  pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold malloc_entry, NEED_LOCKS in *.
  step. carve_frame 48%nat ST. step. step. step. step. step. step.
  (* [comment removed for export] *)
  step. step. step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  clear K0.
  (* [comment removed for export] *)
  step. step. step. step. step.
  step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  clear K1.
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  (* [comment removed for export] *)
  assert (LOCKJ : forall (a0' a1' a2' a3' : word) (sc : Z) (mj : mem),
    sc = size_to_class n ->
    mem_inv rsegs mj -> rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs mj lo (bv_unsigned sp + -48) ->
    munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono rsegs m mj -> rw_cells rsegs mj 403339 [C1 (b8 0)] ->
    evt rsegs (entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 403448) a0' a1' a2' a3' a4 a5 a6 a7
               s2 (Z_to_bv 64 85128) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x23ee8) fc None mj (seg_rom rsegs))).
  { intros a0' a1' a2' a3' sc mj -> MIj FRj STj MUj WMj NLj.
    step. step. rewrite ?zxb_b8 by lia. step. if_cases KL; zify_cond KL. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in KL by lia. lia. }
    apply evt_done. unfold entry_post, MLOCK, DEBRUIJN. do 5 eexists. split; [reflexivity|].
    split; [exact FRj|]. split; [exact STj|]. split; [exact MUj|]. split; [exact WMj| exact MIj]. }
  step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
  - (* [comment removed for export] *)
    apply LOCKJ; try assumption.
    rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (clz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. step.
    rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
    replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    rewrite (unsigned_lit 0), Z.lor_0_l by lia.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (clz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold DEBRUIJN in DBR end.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. step. step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step.
    rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. step. replace (85160 + (i + 1) * 2) with (85160 + 2 * (i + 1)) by lia.
    lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (size_classes_read mc (i + 1) HI ltac:(lia)) as RS1; unfold SIZE_CLASSES in RS1 end.
    (* [comment removed for export] *)
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z) (mj : mem),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      mem_inv rsegs mj -> rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs mj lo (bv_unsigned sp + -48) ->
      munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono rsegs m mj -> rw_cells rsegs mj 403339 [C1 (b8 0)] ->
      evt rsegs (entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 403448)
                 (Z_to_bv 64 (120 - i)) (Z_to_bv 64 85160) (Z_to_bv 64 c) (Z_to_bv 64 (85160 + 2 * (i + 1))) a4 a5 a6 a7
                 s2 (Z_to_bv 64 85128) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x23ecc) fc None mj (seg_rom rsegs))).
    { intros i1 c mj Hi1 Hc MIj FRj STj MUj WMj NLj.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (85160 + i1 * 2) with (85160 + 2 * i1) by lia.
      pose proof (size_classes_read mj i1 MIj ltac:(lia)) as RS2. unfold SIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

(* [comment removed for export] *)
Definition entry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 MLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x23d68) fc None m' (seg_rom rsegs)
    /\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk rsegs m' lo (bv_unsigned sp + -48)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma entry_big_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
  a0 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2^32 ->
  stk rsegs m lo (bv_unsigned sp) -> 0x64000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
  evt rsegs (entry_big_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 malloc_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros HA N ST ILO LO MI. subst a0. unfold MMAP_THRESHOLD in N.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold malloc_entry.
  step. carve_frame 48%nat ST. step. step. step. step. step. step.
  step. step. step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  clear K0.
  step. step. step. step. step.
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  clear K1.
  apply evt_done. unfold entry_big_post, MLOCK. do 2 eexists. split; [reflexivity|].
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -48) _ |- _ => split; [exact H|] end.
  repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

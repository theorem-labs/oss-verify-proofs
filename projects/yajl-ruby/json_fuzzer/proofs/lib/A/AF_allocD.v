(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_kit2 AF_poison AM_memset AF_allocA AF_allocC.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts AsanClassSwar.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes ZBridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.

Ltac cstep := stepA; try first [if_true | if_false].
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ True => split; [lia| exact I] | |- _ /\ _ => split; [lia| first [exact I| lia]] end | lia ].

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wr_at_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at asegs m a (n1 + n2) <-> (wr_at asegs m a n1 /\ wr_at asegs m (a + n1) n2).
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (A0 & AL & W). repeat split; try lia. 
    + intros i Hi. apply W. lia.
    + intros i Hi. rewrite <- Z.add_assoc. apply W. lia.
  - intros ((A0 & AL & W1) & (B0 & BL & W2)). split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i n1); [apply W1; lia|].
    replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.
Lemma rwc_split : forall m A cs1 cs2,
  rw_cells asegs m A (cs1 ++ cs2) -> rw_cells asegs m A cs1 /\ rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[WF B] W]. apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite (cells_bytes_length _ WF1) in B2.
  rewrite cells_size_app, Nat2Z.inj_add in W. apply wr_at_app in W; [| lia| lia]. destruct W as [W1 W2].
  split; (split; [split|]); assumption.
Qed.
Lemma rwc_join : forall m A cs1 cs2,
  rw_cells asegs m A cs1 -> rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells asegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite (cells_bytes_length _ WF1). split; assumption.
  - rewrite cells_size_app, Nat2Z.inj_add. apply wr_at_app; [lia| lia|]. split; assumption.
Qed.
(* [comment removed for export] *)
Lemma CB_cut : forall m A k l bs, rw_cells asegs m A [CB (k + l) bs] ->
  rw_cells asegs m A [CB k (firstn k bs)] /\ rw_cells asegs m (A + Z.of_nat k) [CB l (skipn k bs)].
Proof.
  intros m A k l bs H.
  assert (L : length bs = (k + l)%nat) by (pose proof (proj1 (proj1 (proj1 H))) as WF; cbn in WF; lia).
  assert (H2 : rw_cells asegs m A ([CB k (firstn k bs)] ++ [CB l (skipn k bs)])).
  { eapply rw_cells_recast; [exact H| | |].
    - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
    - cbn. rewrite !app_nil_r. apply firstn_skipn.
    - cbn. lia. }
  apply rwc_split in H2. cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.
Lemma CB_glue : forall m A k l bs1 bs2, rw_cells asegs m A [CB k bs1] -> rw_cells asegs m (A + Z.of_nat k) [CB l bs2] ->
  rw_cells asegs m A [CB (k + l) (bs1 ++ bs2)].
Proof.
  intros m A k l bs1 bs2 H1 H2.
  assert (L1 : length bs1 = k) by (pose proof (proj1 (proj1 (proj1 H1))) as WF; cbn in WF; lia).
  assert (L2 : length bs2 = l) by (pose proof (proj1 (proj1 (proj1 H2))) as WF; cbn in WF; lia).
  pose proof (rwc_join m A [CB k bs1] [CB l bs2] H1 ltac:(cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; exact H2)) as H.
  eapply rw_cells_recast; [exact H| | |].
  - cbn. rewrite length_app. split; [lia| exact I].
  - cbn. rewrite !app_nil_r. reflexivity.
  - cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma hdr_b1_keep : forall bb, Z.land bb 115 = 17 -> Z.land (Z.land (bv_unsigned (Z_to_bv 8 bb)) 243) 127 = 17.
Proof.
  intros bb H. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8). rewrite <- (Z.land_ones bb 8) by lia.
  rewrite <- !Z.land_assoc. change (Z.land (Z.ones 8) (Z.land 243 127)) with 115. exact H.
Qed.
Lemma hdr_b1_keep' : forall bb, Z.land bb 115 = 17 -> Z.land (Z.land bb 243) 127 = 17.
Proof. intros bb H. rewrite <- Z.land_assoc. change (Z.land 243 127) with 115. exact H. Qed.
Lemma rz_size_16_or : forall n, rz_size n = 16 \/ 32 <= rz_size n.
Proof. intros n. pose proof (rz_size_values n) as H. cbn in H. lia. Qed.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section ALLOC.
Variable P : acc -> Prop.

(* [comment removed for export] *)
Lemma bysize_ptr_walk :
  forall (ra' sp' gp tp t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
         (F : bvmap 5 word) (fc : bv 32) (mk : mem) (X s : Z),
  17 <= s <= 65536 -> 0 <= X -> X + 4096 <= 2^47 ->
  evtA asegs P
    (fun ms => exists (a1x a2x a3x a4x a5x a6x : word),
       ms = MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (X + 112 + 8 * class_id s)) a1x a2x a3x a4x a5x a6x a7'
                    s2' (Z_to_bv 64 s) s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
               F (Z_to_bv 64 0x33298) fc None mk (seg_rom asegs))
    (MS (mkR ra' sp' gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 X) a1' a2' a3' a4' a5' a6' a7'
             s2' (Z_to_bv 64 s) s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
        F (Z_to_bv 64 0x3319c) fc None mk (seg_rom asegs)).
Proof.
  intros until s. intros Hs X0 X1.
  pose proof (class_id_spec s ltac:(clear -Hs; lia)) as (HC & _).
  do 2 zstepA.                        (* [comment removed for export] *)
  zstepA; if_cases KB; zify_cond KB.
  - (* [comment removed for export] *)
    do 29 zstepA. lazymatch goal with |- context [Z.lxor ?e 18446744073709551615] => set (sm := e) in * end.
    do 14 zstepA. lazymatch goal with |- context [Z.shiftr ?e 56] => set (pz := e) in * end.
    do 12 zstepA.
    match goal with |- context [Z_to_bv 64 (?e + -2)] =>
      replace (e + -2) with (class_id s)
        by (transitivity (swar_class s); [symmetry; apply swar_class_ok; unfold kMidSize, kMaxSize; revert KB; rewrite ?unsigned_lit by (clear -Hs; lia); intros KB; clear -Hs KB; lia| subst pz sm; reflexivity]) end.
    do 2 zstepA.                      (* [comment removed for export] *)
    rewrite (Z.shiftl_mul_pow2 (class_id s) 3) by (clear; lia). change (2^3) with 8.
    replace (X + 112 + class_id s * 8) with (X + 112 + 8 * class_id s) by (clear; lia).
    apply evtA_done. do 6 eexists. reflexivity.
  - (* [comment removed for export] *)
    do 2 zstepA.                      (* [comment removed for export] *)
    replace ((s + 31) ≫ 5) with (class_id s)
      by (unfold class_id, kMidSize, kMinSize; replace (s <=? 512) with true by (symmetry; apply Z.leb_le; revert KB; rewrite ?unsigned_lit by (clear -Hs; lia); intros KB; clear -KB Hs; lia);
          rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^5) with 32; f_equal; clear; lia).
    cstep.                            (* [comment removed for export] *)
    do 2 zstepA.                      (* [comment removed for export] *)
    rewrite (Z.shiftl_mul_pow2 (class_id s) 3) by (clear; lia). change (2^3) with 8.
    replace (X + 112 + class_id s * 8) with (X + 112 + 8 * class_id s) by (clear; lia).
    apply evtA_done. do 6 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Variables (ra sp gp tp : word) (xra t0 t1 t2 xs0 a0 a1 a2 a3 a4 a5 a6 a7 xs9 t3 t4 t5 t6 : word)
          (os0 os1 os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem).
Variables (lo hi n B : Z) (T CTX TSD ab id b1 SPAN : Z).
Variables (j0 jS : bv 8) (fj uj mj : list byte) (st0 st1 st2 stl bsz : word).
Definition rz : Z := rz_size n.
Definition ub : Z := ab + rz.                 (* [comment removed for export] *)
Definition cb : Z := ab + rz + -16.           (* [comment removed for export] *)
Definition n8 : Z := n / 8.                   (* [comment removed for export] *)
Definition cid : Z := class_id (needed n).    (* [comment removed for export] *)
Definition ctr : Z := if from_primary n then T + 2912 + 8 * cid else T + 2904.   (* [comment removed for export] *)
#[local] Notation usp := (bv_unsigned sp).

Hypothesis SK : stk asegs m lo (bv_unsigned sp + -128).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 512.
Hypothesis SPH : bv_unsigned sp <= hi.
Hypothesis HI : hi < 2^47.
Hypothesis MI : mem_inv asegs m.
Hypothesis Hn : 1 <= n <= 2^27.
Hypothesis HID : 1 <= id < 2^31.
Hypothesis HB1 : 0 <= b1 < 256.
Hypothesis HB1' : Z.land b1 115 = 17.
(* [comment removed for export] *)
Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -128)
  [CB 8 fj; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 os11; C8 os10; C8 os9; C8 os8; C8 os7; C8 os6; C8 os5; C8 os4; C8 os3; C8 os2; C8 os1; C8 os0; C8 ra].
Hypothesis HDR : rw_cells asegs m cb [C1 j0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
Hypothesis USR : rw_cells asegs m ub [CB (Z.to_nat n) uj].
Hypothesis MAG : rw_cells asegs m ab [CB (Z.to_nat (rz - 16)) mj].            (* [comment removed for export] *)
Hypothesis PSHB : n mod 8 <> 0 -> rw_cells asegs m (kShadowBase + (ub + 8 * n8) / 8) [C1 jS].   (* [comment removed for export] *)
Hypothesis TC : thread_cells m tp TSD CTX T.
Hypothesis HTSD : 0x5cfdd0 <= TSD /\ TSD + 8 <= 0x603000.              (* [comment removed for export] *)
Hypothesis HCTX : placed CTX 4096.                                    (* [comment removed for export] *)
Hypothesis HT : placed_s T 4096 /\ T mod 8 = 0.                      (* [comment removed for export] *)
Hypothesis HTP : 0x5cfdd0 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 60 <= 0x603000.   (* [comment removed for export] *)
Hypothesis TCX : T + 4096 <= CTX \/ CTX + 160 <= T.
Hypothesis STATS : rw_cells asegs m (T + 2800) [C8 st0; C8 st1; C8 st2].       (* [comment removed for export] *)
Hypothesis LRG : rw_cells asegs m (T + 2904) [C8 stl].                         (* [comment removed for export] *)
Hypothesis BYSZ : from_primary n = true -> rw_cells asegs m (T + 2912 + 8 * cid) [C8 bsz].   (* [comment removed for export] *)
Hypothesis PG : poison_globals m.
Hypothesis GOTFL : rw_cells asegs m 0xa49a8 [C8 (Z_to_bv 64 0xab378)].      (* [comment removed for export] *)
Hypothesis FL44 : rw_cells asegs m 0xab3a4 [C4 (Z_to_bv 64 4096)].              (* [comment removed for export] *)
Hypothesis FL52 : rw_cells asegs m 0xab3ac [C4 (Z_to_bv 64 0xbe)].              (* [comment removed for export] *)
Hypothesis FL85 : rw_cells asegs m 0xab3cd [C1 (Z_to_bv 8 1)].                     (* [comment removed for export] *)
Hypothesis LSG : rw_cells asegs m 0xa5608 [C8 (Z_to_bv 64 0x10)].             (* [comment removed for export] *)
Hypothesis LSC : rw_cells asegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
Hypothesis HK0 : rw_cells asegs m 0x13f640 [C8 (Z_to_bv 64 0)].               (* [comment removed for export] *)
Hypothesis HAB : 0x603000 <= ab /\ ab + SPAN <= alloc_ceiling /\ ab mod 8 = 0.
Hypothesis HSPAN : needed n <= SPAN.
Hypothesis HSP8 : SPAN mod 8 = 0.                                           (* [comment removed for export] *)
Hypothesis APP : ab + SPAN <= 0x7fff7000 \/ kHighMemBeg <= ab.              (* [comment removed for export] *)
Hypothesis BT : ab + SPAN <= T \/ T + 4096 <= ab.                           (* [comment removed for export] *)
Hypothesis HCID : from_primary n = true -> 1 <= cid <= 30.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= hi -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRO : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x31000 -> P (Z_to_bv 64 a, k).
Hypothesis PTHR : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : forall a k, CTX <= a -> a + Z.of_nat k <= CTX + 160 -> P (Z_to_bv 64 a, k).
Hypothesis PBLK : forall a k, ab <= a -> a + Z.of_nat k <= ab + needed n -> P (Z_to_bv 64 a, k).
Hypothesis PBSH : forall a k, kShadowBase + ab / 8 <= a -> a + Z.of_nat k <= kShadowBase + (ab + SPAN) / 8 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition W4 : list (Z * Z) :=
  [(lo, bv_unsigned sp); (cb, cb + 2); (ab, ab + 16); (ub, ub + Z.min n 4096)]
  ++ (if n mod 8 =? 0 then [] else [(kShadowBase + (ub + 8 * n8) / 8, kShadowBase + (ub + 8 * n8) / 8 + 1)])   (* [comment removed for export] *)
  ++ [(T + 2800, T + 2824); (ctr, ctr + 8)].

Definition segD5_post : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (b1' : Z),
    ms = MS (mkR ra sp gp tp t0' t1' t2' os0 os1 (Z_to_bv 64 ub) a1' a2' a3' a4' a5' a6' a7'
                 os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W4 m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ Z.land b1' 127 = 0x11
    /\ rw_cells asegs m' cb [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1'); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' ub [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
    /\ (16 < rz -> exists mrest, rw_cells asegs m' ab [C8 (Z_to_bv 64 kAllocBegMagicVal); C8 (Z_to_bv 64 cb); CB (Z.to_nat (rz - 32)) mrest])
    /\ (n mod 8 <> 0 -> rw_cells asegs m' (kShadowBase + (ub + 8 * n8) / 8) [C1 (Z_to_bv 8 (n mod 8))])
    /\ rw_cells asegs m' (T + 2800) [C8 (Z_to_bv 64 (bv_unsigned st0 + 1)); C8 (Z_to_bv 64 (bv_unsigned st1 + n)); C8 (Z_to_bv 64 (bv_unsigned st2 + (needed n - n)))]
    /\ (if from_primary n then rw_cells asegs m' (T + 2912 + 8 * cid) [C8 (Z_to_bv 64 (bv_unsigned bsz + 1))] /\ rw_cells asegs m' (T + 2904) [C8 stl]
        else rw_cells asegs m' (T + 2904) [C8 (Z_to_bv 64 (bv_unsigned stl + 1))]).

Definition entryD : machine_state :=
  MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 xs0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 ub) (Z_to_bv 64 cb) (Z_to_bv 64 (8 * n8)) (Z_to_bv 64 B) (Z_to_bv 64 0)
           xs9 (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
     F (Z_to_bv 64 0x330b8) fc None m (seg_rom asegs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qa : Z := ab / 8.
Definition qr : Z := rz / 8.
Definition qS : Z := (ab + SPAN) / 8.
Definition PBA : Z := 2147450880 + qa + qr + n8.          (* [comment removed for export] *)

Definition NUMS : Prop :=
     (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000) /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 512 /\ bv_unsigned sp <= hi /\ hi < 2^47
  /\ (0 <= bv_unsigned sp < 2^64) /\ (1 <= n <= 2^27) /\ (1 <= id < 2^31) /\ (0 <= b1 < 256)
  /\ 0x603000 <= ab /\ ab + SPAN <= alloc_ceiling /\ needed n <= SPAN
  /\ (16 <= rz <= 2048) /\ n <= rounded n /\ 8 <= rounded n /\ rounded n <= n + 15
  /\ needed1 n = rounded n + rz /\ (needed1 n <= needed n <= needed1 n + rz)
  /\ ab = 8 * qa /\ rz = 8 * qr /\ (0 <= n8 /\ 8 * n8 <= n < 8 * n8 + 8) /\ ab + SPAN = 8 * qS
  /\ (ab + SPAN <= 0x7fff7000 \/ 0x10007fff8000 <= ab)
  /\ (0x1000 <= T /\ T + 4096 <= alloc_ceiling) /\ (0x603000 <= CTX /\ CTX + 4096 <= alloc_ceiling)
  /\ (0x5cfdd0 <= TSD /\ TSD + 8 <= 0x603000) /\ (0x5cfdd0 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 60 <= 0x603000)
  /\ (ab + SPAN <= T \/ T + 4096 <= ab) /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T) /\ (CTX + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= CTX)
  /\ (T + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= T).
Lemma nums : NUMS.
Proof.
  pose proof LOC as LOCu. aceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rz_size_pos n) as RZP. change (rz_size n) with rz in RZP.
  pose proof (rz_size_mod16 n) as RZ16. change (rz_size n) with rz in RZ16.
  pose proof (needed_range n Hn) as NR. change (rz_size n) with rz in NR. assert (N1 : needed1 n = rounded n + rz) by reflexivity.
  pose proof (rounded_ge n) as (RG1 & RG2 & RG3).
  assert (N8R : 0 <= n8 /\ 8 * n8 <= n < 8 * n8 + 8) by (unfold n8; clear -Hn; pose proof (Z.div_mod n 8 ltac:(lia)); pose proof (Z.mod_pos_bound n 8 ltac:(lia)); lia).
  assert (A8 : ab = 8 * qa) by (unfold qa; destruct HAB as (_ & _ & M8); clear -M8; pose proof (Z.div_mod ab 8 ltac:(lia)); lia).
  assert (RZ8 : rz = 8 * qr) by (unfold qr; clear -RZ16 RZP; pose proof (Z.div_mod rz 16 ltac:(lia)); pose proof (Z.div_mod rz 8 ltac:(lia)); lia).
  assert (QS8 : ab + SPAN = 8 * qS) by (unfold qS; clear -HAB HSP8; destruct HAB as (_ & _ & M8); pose proof (Z.div_mod (ab + SPAN) 8 ltac:(lia)); pose proof (Z.div_mod ab 8 ltac:(lia)); pose proof (Z.div_mod SPAN 8 ltac:(lia)); lia).
  pose proof APP as APP'. rewrite kHighMemBeg_val in APP'.
  pose proof HCTX as NCTX. unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in NCTX. pose proof HT as ((NT1 & NT2 & NT3 & NT4) & _). unfold A_IMG_END in NT3. unfold A_LOWAPP_END, A_HIGH_BEG in NT4.
  unfold NUMS. repeat match goal with |- _ /\ _ => split end; (first [assumption| lia]).
Qed.
Ltac open_nums :=
  let NF' := fresh "NF'" in
  pose proof nums as NF; pose proof NF as NF'; unfold NUMS in NF';
  destruct NF' as (CEI & LOC' & LO' & SPH' & HI' & SPR & Hn' & HID' & HB1r & AB0 & ABS & NSP & RZP & RG1 & RG8 & RG2
                  & N1 & NV & A8 & RZ8 & N8R & QS8 & APP' & NT & NCTX & NTSD & NTP & BT' & TIMG & CTXA & TAPP).
Ltac nlia := lazymatch goal with NF : NUMS |- _ => clear -NF; pose proof NF as NF'; unfold NUMS in NF'; decompose [and] NF'; unfold PBA in *; lia end.
Tactic Notation "nliaK" ne_hyp_list(l) :=
  lazymatch goal with NF : NUMS |- _ => clear -NF l; pose proof NF as NF'; unfold NUMS in NF'; decompose [and] NF'; unfold PBA in *; lia end.
(* [comment removed for export] *)
Ltac hx_split H := lazymatch type of H with
  | _ /\ _ => (let H1 := fresh "Dj" in let H2 := fresh "Dj" in destruct H as [H1 H2]; hx_split H2)
  | _ => idtac
  end.
Tactic Notation "incl_by" ne_hyp_list(l) :=
  unfold sub_fp; cbn [outside];
  let xo := fresh "xo" in let Hx := fresh "Hxo" in intros xo Hx; hx_split Hx;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  match goal with D : ~ _ |- _ => revert D; nliaK l end.
Ltac kill1 K := exfalso; revert K; rewrite ?unsigned_lit by nlia; nlia.
Ltac kill2 K H := exfalso; revert K H; rewrite ?unsigned_lit by nlia; nlia.
Tactic Notation "killn" hyp(K) ne_hyp_list(l) := exfalso; revert l; revert K; rewrite ?unsigned_lit by nlia; nlia.
Ltac br1n := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [kill1 K| try clear K]).
Ltac br2n := zstepA; let K := fresh "K" in (if_cases K; zify_cond K; [try clear K| kill1 K]).
(* [comment removed for export] *)
Ltac xport H MU WM :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?A ?cs =>
      apply (rw_cells_transport asegs W ma mb A cs) in H; [| exact MU| exact WM| cbn [disjoint_from]; simpl_sizes; nlia]
    end end.
Tactic Notation "xportK" hyp(H) hyp(MU) hyp(WM) ne_hyp_list(l) :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?A ?cs =>
      apply (rw_cells_transport asegs W ma mb A cs) in H; [| exact MU| exact WM| cbn [disjoint_from]; simpl_sizes; nliaK l]
    end end.
Tactic Notation "xport_stkK" hyp(H) hyp(MU) hyp(WM) ne_hyp_list(l) :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    lazymatch type of H with stk _ _ ?lq ?hq =>
      apply (stk_transport_disjoint asegs W ma mb lq hq) in H; [| exact MU| exact WM| cbn [disjoint_from]; nliaK l]
    end end.
Tactic Notation "xport_pgK" hyp(H) hyp(MU) ne_hyp_list(l) :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    apply (poison_globals_agree ma mb) in H;
    [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply MU; rewrite wa_unsigned by (clear -Ha; lia); cbn [outside]; revert Ha; nliaK l]
  end.
Ltac xport_stk H MU WM :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    lazymatch type of H with stk _ _ ?l ?h =>
      apply (stk_transport_disjoint asegs W ma mb l h) in H; [| exact MU| exact WM| cbn [disjoint_from]; nlia]
    end end.
Ltac xport_pg H MU :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
    apply (poison_globals_agree ma mb) in H;
    [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply MU; rewrite wa_unsigned by (clear -Ha; lia); cbn [outside]; nliaK Ha]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PGW : list (Z * Z) := if n mod 8 =? 0 then [] else [(PBA, PBA + 1)].
Definition pgran_post : machine_state -> Prop :=
  fun ms => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' s6' : word) m1,
    ms = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 xs0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0)
                 xs9 (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
            F (Z_to_bv 64 0x3314c) fc None m1 (seg_rom asegs)
    /\ munch PGW m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
    /\ (8 * n8 < n -> rw_cells asegs m1 PBA [C1 (Z_to_bv 8 (n - 8 * n8))]).

Lemma secD_pgran : evtA asegs P pgran_post entryD.
Proof.
  unfold entryD. open_nums.
  clear SK FR HDR USR MAG TC STATS LRG BYSZ FL44 FL52 LSG LSC HK0 PSTK PRO PTHR PCTX PBLK HCTX HT TCX BT HCID APP.
  pose proof PBSH as PBSH'. unfold kShadowBase in PBSH'. change (ab / 8) with qa in PBSH'. change ((ab + SPAN) / 8) with qS in PBSH'. clear PBSH.
  unfold ub, cb in *.
  assert (MU : munch [(PBA, PBA + 1)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  zstepA; if_cases KQ; zify_cond KQ.
  - (* [comment removed for export] *)
    apply evtA_done. unfold pgran_post. do 11 eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [exact WM|]. split; [exact MI|]. intros LT. exfalso. revert KQ LT. rewrite ?unsigned_lit by nlia. nlia.
  - assert (LT : 8 * n8 < n) by (revert KQ; rewrite ?unsigned_lit by nlia; nlia). clear KQ.
    assert (NM8 : (n mod 8 =? 0) = false) by (apply Z.eqb_neq; rewrite (Z.mod_eq n 8) by (clear; lia); fold n8; nliaK LT).
    specialize (PSHB ltac:(rewrite (Z.mod_eq n 8) by (clear; lia); fold n8; nliaK LT)).
    unfold kShadowBase in PSHB.
    replace (2147450880 + (ab + rz + 8 * n8) / 8) with PBA in PSHB
      by (unfold PBA; replace (ab + rz + 8 * n8) with ((qa + qr + n8) * 8) by nlia; rewrite Z.div_mul by (clear; lia); clear; lia).
    cstep.                            (* [comment removed for export] *)
    pose proof PG as (PG1 & Gx2 & PG3 & PG4 & Gx5 & PG6 & Gx7). clear Gx2 Gx5 Gx7 PG.
    unfold kShadowBase in PG3. unfold kHighMemEnd in PG4.
    zstepA. zstepA.                   (* [comment removed for export] *)
    replace (sxb (Z_to_bv 8 1)) with (Z_to_bv 64 1) by reflexivity.
    zstepA. (zstepA; litc).           (* [comment removed for export] *)
    cstep.                            (* [comment removed for export] *)
    zstepA; if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by (clear; lia); clear; lia|]. clear K0.   (* [comment removed for export] *)
    do 3 zstepA.                      (* [comment removed for export] *)
    zstepA.                           (* [comment removed for export] *)
    do 4 (zstepA; litc).              (* [comment removed for export] *)
    (* [comment removed for export] *)
    let ra' := getreg 1 in
    assert (JOIN : forall (a2x a3x a4x a5x a6x a7x : word),
      evtA asegs P pgran_post
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 xs0 (Z_to_bv 64 n) (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879)
                 a2x a3x a4x a5x a6x a7x
                 (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) (Z_to_bv 64 (ab + rz + 8 * n8)) (Z_to_bv 64 B) (Z_to_bv 64 0)
                 xs9 (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
            F (Z_to_bv 64 0x33128) fc None m (seg_rom asegs))).
    { intros. clear PG3 PG4 PG6.
      do 3 zstepA.                    (* [comment removed for export] *)
      do 2 zstepA.                    (* [comment removed for export] *)
      do 3 (zstepA; litc).            (* [comment removed for export] *)
      try rewrite (Z.mod_small (ab + rz + 8 * n8) 18446744073709551616) by nlia. rewrite (Z.shiftr_div_pow2 (ab + rz + 8 * n8) 3) by (clear; lia).
      change (2 ^ 3) with 8.
      replace (2147450880 + (ab + rz + 8 * n8) / 8) with PBA
        by (unfold PBA; replace (ab + rz + 8 * n8) with ((qa + qr + n8) * 8) by nlia; rewrite Z.div_mul by (clear; lia); clear; lia).
      try rewrite (Z.mod_small n 18446744073709551616) by nlia.
      change 18446744073709551615 with (Z.ones 64). rewrite (Z.land_ones n 64) by nlia. change (2 ^ 64) with 18446744073709551616.
      rewrite (Z.mod_small n 18446744073709551616) by nlia.
      change (Z.land n 7) with (Z.land n (Z.ones 3)). rewrite (Z.land_ones n 3) by nlia. change (2 ^ 3) with 8.
      replace (n mod 8) with (n - 8 * n8) by (unfold n8; rewrite (Z.mod_eq n 8) by (clear; lia); clear; lia).
      clear PG1 GOTFL FL85.
      zstepA.                         (* [comment removed for export] *)
      1: apply PBSH'; nliaK LT.
      try rewrite (Z.mod_small (n - 8 * n8) 256) in PSHB by nlia.
      apply evtA_done. unfold pgran_post. do 11 eexists. split; [reflexivity|].
      split; [unfold PGW; rewrite NM8; exact MU|]. split; [exact WM|]. split; [exact MI|]. intros _; exact PSHB. }
    (* [comment removed for export] *)
    zstepA; if_cases K1; zify_cond K1.
    + (* [comment removed for export] *)
      apply JOIN.
    + do 4 zstepA.                    (* [comment removed for export] *)
      do 2 zstepA.                    (* [comment removed for export] *)
      (zstepA; litc).                 (* [comment removed for export] *)
      zstepA; first [if_true | if_cases K2; zify_cond K2; [| kill1 K2]].   (* [comment removed for export] *)
      do 3 zstepA.                    (* [comment removed for export] *)
      do 2 (zstepA; litc).            (* [comment removed for export] *)
      assert (HIGH : 17594333495296 <= ab) by (revert K1; rewrite ?unsigned_lit by nlia; clear -NF LT; pose proof NF as NF'; unfold NUMS in NF'; decompose [and] NF'; lia). clear K1.
      zstepA; if_cases K3; zify_cond K3; [kill2 K3 HIGH| clear K3].   (* [comment removed for export] *)
      zstepA; if_cases K4; zify_cond K4; [kill2 K4 HIGH| clear K4].   (* [comment removed for export] *)
      apply JOIN.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fp_cases : (from_primary n = true /\ needed n = needed1 n /\ needed1 n <= 65536)
                 \/ (from_primary n = false /\ needed n = needed1 n + rz /\ 65536 < needed1 n).
Proof.
  clear. unfold needed, from_primary, kMaxSize, rz. destruct (needed1 n <=? 65536) eqn:E.
  - left. apply Z.leb_le in E. auto.
  - right. apply Z.leb_gt in E. repeat split; lia.
Qed.

Definition stats_post (s6' : word) (m1 : mem) : machine_state -> Prop :=
  fun ms => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' : word) m2,
    ms = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 xs0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0)
                 xs9 (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
            F (Z_to_bv 64 0x332ac) fc None m2 (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (T + 2800, T + 2824); (ctr, ctr + 8)] m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2
    /\ stk asegs m2 lo (bv_unsigned sp + -128)
    /\ rw_cells asegs m2 (T + 2800) [C8 (Z_to_bv 64 (bv_unsigned st0 + 1)); C8 (Z_to_bv 64 (bv_unsigned st1 + n)); C8 (Z_to_bv 64 (bv_unsigned st2 + (needed n - n)))]
    /\ (if from_primary n then rw_cells asegs m2 (T + 2912 + 8 * cid) [C8 (Z_to_bv 64 (bv_unsigned bsz + 1))] /\ rw_cells asegs m2 (T + 2904) [C8 stl]
        else rw_cells asegs m2 (T + 2904) [C8 (Z_to_bv 64 (bv_unsigned stl + 1))]).

Lemma secD_stats :
  forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s6' : word) (m1 : mem),
  mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) ->
  rw_cells asegs m1 (bv_unsigned sp + -128)
    [CB 8 fj; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 os11; C8 os10; C8 os9; C8 os8; C8 os7; C8 os6; C8 os5; C8 os4; C8 os3; C8 os2; C8 os1; C8 os0; C8 ra] ->
  thread_cells m1 tp TSD CTX T ->
  rw_cells asegs m1 (T + 2800) [C8 st0; C8 st1; C8 st2] -> rw_cells asegs m1 (T + 2904) [C8 stl] ->
  (from_primary n = true -> rw_cells asegs m1 (T + 2912 + 8 * cid) [C8 bsz]) ->
  evtA asegs P (stats_post s6' m1)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 xs0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0)
             xs9 (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x3314c) fc None m1 (seg_rom asegs)).
Proof.
  intros until m1. intros MI1 SK1 FR1 TC1 ST1 LRG1 BYSZ1. open_nums.
  clear SK FR HDR USR MAG PSHB TC STATS LRG BYSZ PG GOTFL FL44 FL52 FL85 LSG LSC HK0 PRO PBLK PBSH HAB APP BT MI.
  pose proof LOC as LOC0.
  unfold stats_post, ctr.
  assert (MU : munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (T + 2800, T + 2824);
                      ((if from_primary n then T + 2912 + 8 * cid else T + 2904), (if from_primary n then T + 2912 + 8 * cid else T + 2904) + 8)] m1 m1) by apply munch_refl.
  assert (WM : wmono asegs m1 m1) by apply wmono_refl.
  destruct TC1 as (TCa & TCb & TCc & TCd & TCe).
  (* [comment removed for export] *)
  Ltac d2_stats :=
    unname_sp;
    do 3 zstepA;                        (* [comment removed for export] *)
    do 2 zstepA;                        (* [comment removed for export] *)
    do 2 (zstepA; litc);                (* [comment removed for export] *)
    do 2 zstepA;                        (* [comment removed for export] *)
    do 3 zstepA.                        (* [comment removed for export] *)
  destruct fp_cases as [(FP & NE & N65)|(FP & NE & N65)]; rewrite FP in *.
  - specialize (BYSZ1 eq_refl). pose proof (HCID eq_refl) as HC. clear HCID.
    set (BYA := T + 2912 + 8 * cid) in *.
    cstep. name_sp sp (-128).
    callA (gcts_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
      [ first [exact SK1 | rewrite Hsp; exact SK1]| exact LOC0| nliaK Hsp| nliaK Hsp| eassumption| exact (conj TCa (conj TCb (conj TCc (conj TCd TCe))))| nlia| nlia| nlia| nlia| nlia| nlia
      | intros; apply PSTK; nliaK H H0 Hsp| exact PDAT| apply PCTX; nlia|].
    clear TCa TCb TCc TCd TCe. d2_stats.
    zstepA; if_cases K5; zify_cond K5; [clear K5| killn K5 NE N65].   (* [comment removed for export] *)
    eapply evtA_cut; [eapply (bysize_ptr_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T + 2800) (needed n)); nliaK NE N65|].
    cbv beta. intros ms' PO. destruct_exs PO. subst ms'.
    replace (T + 2800 + 112 + 8 * class_id (needed n)) with BYA by (subst BYA; unfold cid; clear; lia).
    do 3 zstepA.                      (* [comment removed for export] *)
    zstepA.                           (* [comment removed for export] *)
    cstep.                            (* [comment removed for export] *)
    change 18446744073709551616 with (2^64) in *. rewrite ?ZBridge.Z_to_bv_mod64 in *.
    replace (needed n - n + bv_unsigned st2) with (bv_unsigned st2 + (needed n - n)) in * by (clear; lia).
    apply evtA_done. do 10 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
  - clear BYSZ1 HCID.
    cstep. name_sp sp (-128).
    callA (gcts_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
      [ first [exact SK1 | rewrite Hsp; exact SK1]| exact LOC0| nliaK Hsp| nliaK Hsp| eassumption| exact (conj TCa (conj TCb (conj TCc (conj TCd TCe))))| nlia| nlia| nlia| nlia| nlia| nlia
      | intros; apply PSTK; nliaK H H0 Hsp| exact PDAT| apply PCTX; nlia|].
    clear TCa TCb TCc TCd TCe. d2_stats.
    zstepA; if_cases K5; zify_cond K5; [killn K5 NE N65| clear K5].   (* [comment removed for export] *)
    do 3 zstepA.                      (* [comment removed for export] *)
    zstepA.                           (* [comment removed for export] *)
    cstep.                            (* [comment removed for export] *)
    change 18446744073709551616 with (2^64) in *. rewrite ?ZBridge.Z_to_bv_mod64 in *.
    replace (needed n - n + bv_unsigned st2) with (bv_unsigned st2 + (needed n - n)) in * by (clear; lia).
    try replace (T + 2904 + 8) with (T + 2912) in MU by (clear; lia).
    apply evtA_done. do 10 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FL : Z := Z.min n 4096.
Definition fill_post (s6' : word) (uj2 : list byte) (m2 : mem) : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m3,
    ms = MS (mkR (Z_to_bv 64 0x332e0) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' xs0 (Z_to_bv 64 n) (Z_to_bv 64 (ab + rz)) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0)
                 xs9 (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
            F (Z_to_bv 64 0x332e0) fc None m3 (seg_rom asegs)
    /\ munch [(ab + rz, ab + rz + FL)] m2 m3 /\ wmono asegs m2 m3 /\ mem_inv asegs m3
    /\ rw_cells asegs m3 (ab + rz) [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat FL) ++ skipn (Z.to_nat FL) uj2)].

Lemma secD_fill :
  forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s6' : word) (uj2 : list byte) (m2 : mem),
  mem_inv asegs m2 -> poison_globals m2 ->
  rw_cells asegs m2 0xa49a8 [C8 (Z_to_bv 64 0xab378)] -> rw_cells asegs m2 0xab3a4 [C4 (Z_to_bv 64 4096)] -> rw_cells asegs m2 0xab3ac [C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m2 (ab + rz) [CB (Z.to_nat n) uj2] ->
  evtA asegs P (fill_post s6' uj2 m2)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 xs0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0)
             xs9 (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x332ac) fc None m2 (seg_rom asegs)).
Proof.
  intros until m2. intros MI2 PG2 GOTFL2 FL44_2 FL52_2 USR2. open_nums.
  clear SK FR HDR USR MAG PSHB TC STATS LRG BYSZ PG GOTFL FL44 FL52 FL85 LSG LSC HK0 PSTK PRO PTHR PCTX PBSH HAB APP BT MI HCTX HT TCX HCID.
  pose proof PG2 as (PGa & Gx2 & Gx3 & Gx4 & PGe & Gx6 & Gx7). clear Gx2 Gx3 Gx4 Gx6 Gx7 PG2.
  assert (MU : munch [(ab + rz, ab + rz + FL)] m2 m2) by apply munch_refl.
  assert (WM : wmono asegs m2 m2) by apply wmono_refl.
  do 3 zstepA.                        (* [comment removed for export] *)
  try change (sx32 (Z_to_bv 64 4096)) with (Z_to_bv 64 4096).
  cstep.                              (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  let ra1 := getreg 1 in
  assert (JOIN : forall L, L = FL ->
    evtA asegs P (fill_post s6' uj2 m2)
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 xs0 (Z_to_bv 64 n) (Z_to_bv 64 0xab378) (Z_to_bv 64 4096) (Z_to_bv 64 L) a3' a4' a5' a6' a7'
               (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0)
               xs9 (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
          F (Z_to_bv 64 0x332c8) fc None m2 (seg_rom asegs))).
  { intros L HL. assert (HL2 : 1 <= L <= n /\ L <= 4096) by (rewrite HL; unfold FL; clear -Hn'; lia).
    do 3 zstepA.                      (* [comment removed for export] *)
    zstepA.                           (* [comment removed for export] *)
    try change (sx32 (Z_to_bv 64 190)) with (Z_to_bv 64 190).
    zstepA.                           (* [comment removed for export] *)
    cstep.                            (* [comment removed for export] *)
    (* [comment removed for export] *)
    replace (Z.to_nat n) with (Z.to_nat L + Z.to_nat (n - L))%nat in USR2 by (clear -HL2; lia).
    apply CB_cut in USR2. destruct USR2 as [U1 U2].
    assert (E0 : bv_unsigned (Z_to_bv 64 (ab + rz)) = ab + rz) by (apply unsigned_lit; nlia).
    assert (E1 : bv_unsigned (Z_to_bv 64 190) = 190) by (apply unsigned_lit; clear; lia).
    assert (E2 : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; nliaK HL2).
    eapply evtA_cut.
    { eapply (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (firstn (Z.to_nat L) uj2) P);
        [ rewrite E0, E2; intros a k H1 H2; apply PBLK; nliaK H1 H2 HL2 | rewrite E0, E2; exact U1 | exact MI2 ]. }
    cbv beta. intros ms' PO. unfold memset_post in PO. rewrite E0, E1, E2 in PO. change (190 mod 256) with 190 in PO. destruct_exs PO.
    destruct PO as (-> & MU3 & WM3 & MI3 & U1'). ret_pc_lit.
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mk _) => rename mk into m3 end.
    apply (rw_cells_transport asegs _ m2 m3 _ _ U2) in MU3 as U2'; [| exact WM3| cbn [disjoint_from]; simpl_sizes; nliaK HL2].
    pose proof (CB_glue m3 _ _ _ _ _ U1' U2') as U3. clear U1' U2'.
    replace (Z.to_nat L + Z.to_nat (n - L))%nat with (Z.to_nat n) in U3 by (clear -HL2; lia).
    rewrite HL in *.
    apply evtA_done. unfold fill_post. do 15 eexists. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU3]|]. split; [eapply wmono_trans; [exact WM| exact WM3]|]. split; [exact MI3| exact U3]. }
  zstepA; if_cases KF; zify_cond KF.
  - apply JOIN. unfold FL. symmetry. apply Z.min_l. revert KF. rewrite ?unsigned_lit by nlia. clear; lia.
  - zstepA.                           (* [comment removed for export] *)
    apply JOIN. unfold FL. symmetry. apply Z.min_r. revert KF. rewrite ?unsigned_lit by nlia. clear; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tail_post (t0' t1' t2' t3' t4' t5' t6' : word) (m3 : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' a3' a4' a5' a6' a7' : word) m4 (b1' : Z),
    ms = MS (mkR ra sp gp tp t0' t1' t2' os0 os1 (Z_to_bv 64 (ab + rz)) a1' a2' a3' a4' a5' a6' a7'
                 os2 os3 os4 os5 os6 os7 os8 os9 os10 os11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m4 (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (ab + rz + -16, ab + rz + -16 + 2); (ab, ab + 16)] m3 m4 /\ wmono asegs m3 m4 /\ mem_inv asegs m4
    /\ stk asegs m4 lo (bv_unsigned sp)
    /\ Z.land b1' 127 = 0x11
    /\ rw_cells asegs m4 (ab + rz + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1'); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ (16 < rz -> exists mrest, rw_cells asegs m4 ab [C8 (Z_to_bv 64 kAllocBegMagicVal); C8 (Z_to_bv 64 (ab + rz + -16)); CB (Z.to_nat (rz - 32)) mrest]).

Lemma secD_tail :
  forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word) (mj3 : list byte) (m3 : mem),
  mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -128) ->
  rw_cells asegs m3 (bv_unsigned sp + -128)
    [CB 8 fj; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 os11; C8 os10; C8 os9; C8 os8; C8 os7; C8 os6; C8 os5; C8 os4; C8 os3; C8 os2; C8 os1; C8 os0; C8 ra] ->
  rw_cells asegs m3 (ab + rz + -16) [C1 j0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  rw_cells asegs m3 ab [CB (Z.to_nat (rz - 16)) mj3] ->
  rw_cells asegs m3 0xa5608 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m3 (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m3 0x13f640 [C8 (Z_to_bv 64 0)] ->
  evtA asegs P (tail_post t0' t1' t2' t3' t4' t5' t6' m3)
    (MS (mkR (Z_to_bv 64 0x332e0) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' xs0 (Z_to_bv 64 n) (Z_to_bv 64 (ab + rz)) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0)
             xs9 (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
        F (Z_to_bv 64 0x332e0) fc None m3 (seg_rom asegs)).
Proof.
  intros until m3. intros MI3 SK3 FR3 HDR3 MAG3 LSG3 LSC3 HK3. open_nums.
  clear SK FR HDR USR MAG PSHB TC STATS LRG BYSZ PG GOTFL FL44 FL52 FL85 LSG LSC HK0 PTHR PCTX PBSH HAB APP BT MI HCTX HT TCX HCID.
  pose proof LOC as LOC0.
  assert (MU : munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (ab + rz + -16, ab + rz + -16 + 2); (ab, ab + 16)] m3 m3) by apply munch_refl.
  assert (WM : wmono asegs m3 m3) by apply wmono_refl.
  cstep.                              (* [comment removed for export] *)
  eapply evtA_cut; [eapply lsan_dis_walk; [exact MI3| exact LSG3| exact LSC3| nlia| exact PDAT]|].
  cbv beta. intros ms' PO. destruct PO as [xa1 ->]. ret_pc_lit. clear LSG3 LSC3.
  do 5 (zstepA; litc).                (* [comment removed for export] *)
  rewrite ?Z.lor_0_r.
  lazymatch goal with |- context [Z.land (bv_unsigned (Z_to_bv 8 b1)) 243] =>
      pose proof (hdr_b1_keep b1 HB1') as B1K;
      assert (B1R : 0 <= Z.land (bv_unsigned (Z_to_bv 8 b1)) 243 < 256)
        by (pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 b1)) as R; change (bv_modulus 8) with (2^8) in R; clear -R; apply (Bytes.land_lt_pow2 _ 243 8); lia);
      set (b1' := Z.land (bv_unsigned (Z_to_bv 8 b1)) 243) in *
  | |- context [Z.land b1 243] =>
      pose proof (hdr_b1_keep' b1 HB1') as B1K;
      assert (B1R : 0 <= Z.land b1 243 < 256) by (clear -HB1r; apply (Bytes.land_lt_pow2 _ 243 8); lia);
      set (b1' := Z.land b1 243) in *
  end.
  zstepA.                             (* [comment removed for export] *)
  zstepA; litc.                       (* [comment removed for export] *)
  try rewrite (Z.mod_small b1' 256) in * by exact B1R.
  zstepA.                             (* [comment removed for export] *)
  zstepA; litc.                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mh _) =>
  assert (JOIN : forall (a0x a3x : word) (mq : mem),
    mem_inv asegs mq -> stk asegs mq lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (ab + rz + -16, ab + rz + -16 + 2); (ab, ab + 16)] m3 mq -> wmono asegs m3 mq ->
    rw_cells asegs mq (bv_unsigned sp + -128)
      [CB 8 fj; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 os11; C8 os10; C8 os9; C8 os8; C8 os7; C8 os6; C8 os5; C8 os4; C8 os3; C8 os2; C8 os1; C8 os0; C8 ra] ->
    rw_cells asegs mq 0x13f640 [C8 (Z_to_bv 64 0)] ->
    rw_cells asegs mq (ab + rz + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1'); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
    (exists cs, rw_cells asegs mq ab cs /\ cells_size cs = Z.to_nat (rz - 16) /\ (16 < rz -> exists mrest, cs = [C8 (Z_to_bv 64 kAllocBegMagicVal); C8 (Z_to_bv 64 (ab + rz + -16)); CB (Z.to_nat (rz - 32)) mrest])) ->
    evtA asegs P (tail_post t0' t1' t2' t3' t4' t5' t6' m3)
      (MS (mkR (Z_to_bv 64 0x332e4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' xs0 (Z_to_bv 64 n) a0x (Z_to_bv 64 2) a2' a3x a4' a5' a6' a7'
               (Z_to_bv 64 ab) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 (ab + rz + -16)) s6' (Z_to_bv 64 B) (Z_to_bv 64 0)
               xs9 (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
          F (Z_to_bv 64 0x33328) fc None mq (seg_rom asegs)))
  end.
  { intros a0x a3x mq MIq SKq MUq WMq FRq HKq HDRq (cs & MGq & MGS & MGP).
    clear MU WM FR3 HDR3 MAG3 HK3.
    repeat match goal with H : mem_inv asegs ?mx |- _ => lazymatch mx with mq => fail | _ => clear H end end.
    do 2 zstepA.                       (* [comment removed for export] *)
    cstep.                             (* [comment removed for export] *)
    name_sp sp (-128).
    callA (rmh_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo);
      [ first [exact SKq | rewrite Hsp; exact SKq]| exact LOC0| nliaK Hsp| nliaK Hsp| eassumption| exact HKq| intros; apply PSTK; nliaK H H0 Hsp| exact PDAT|].
    unname_sp.
    zstepA.                            (* [comment removed for export] *)
    do 13 zstepA.                      (* [comment removed for export] *)
    zstepA.                            (* [comment removed for export] *)
    match goal with ST : stk _ _ lo _ |- _ => release_frame FRq ST (bv_unsigned sp) end.
    cstep.                             (* [comment removed for export] *)
    apply evtA_done. unfold tail_post. do 9 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption.
    intros R. destruct (MGP R) as [mrest ->]. exists mrest. exact MGq. }
  zstepA; if_cases KM; zify_cond KM.
  - (* [comment removed for export] *)
    assert (R16 : rz = 16) by (revert KM; rewrite ?unsigned_lit by nlia; nlia). clear KM.
    eapply JOIN; try eassumption. eexists. split; [exact MAG3|]. split; [cbn [cells_size csize]; apply Nat.add_0_r|]. intros R; exfalso; clear -R R16; lia.
  - assert (R32 : 32 <= rz) by (destruct (rz_size_16_or n) as [R|R]; change (rz_size n) with rz in R; [exfalso; revert KM; rewrite ?unsigned_lit by nlia; nliaK R| exact R]). clear KM.
    zstepA.                           (* [comment removed for export] *)
    zstepA; if_cases K8; zify_cond K8; [killn K8 R32| clear K8].      (* [comment removed for export] *)
    zstepA. zstepA.                   (* [comment removed for export] *)
    replace (Z.to_nat (rz - 16)) with (16 + Z.to_nat (rz - 32))%nat in MAG3 by (clear -R32; lia).
    apply CB_cut in MAG3. destruct MAG3 as [MG1 MG2].
    zstepA.                           (* [comment removed for export] *)
    zstepA.                           (* [comment removed for export] *)
    zstepA; litc.                     (* [comment removed for export] *)
    eapply JOIN; try eassumption.
    exists ([C8 (Z_to_bv 64 kAllocBegMagicVal); C8 (Z_to_bv 64 (ab + rz + -16))] ++ [CB (Z.to_nat (rz - 32)) (skipn 16 mj3)]).
    split; [apply rwc_join; [exact MG1|]; cbn [cells_size csize Nat.add]; first [exact MG2| cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in MG2 |- *; exact MG2]|].
    split; [cbn [cells_size csize app Nat.add]; clear -R32; lia|]. intros _. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma alloc5_segD : evtA asegs P segD5_post entryD.
Proof.
  open_nums.
  pose proof SK as SK0. pose proof FR as FR0. pose proof HDR as HDR0. pose proof USR as USR0. pose proof MAG as MAG0.
  pose proof STATS as ST0. pose proof LRG as LRG0. pose proof PG as PG0.
  pose proof GOTFL as GF0. pose proof FL44 as F44. pose proof FL52 as F52. pose proof LSG as LSG0. pose proof LSC as LSC0. pose proof HK0 as HK00.
  unfold ub, cb in SK0, FR0, HDR0, USR0, MAG0.
  assert (CTRR : T + 2904 <= ctr /\ ctr + 8 <= T + 3160) by (unfold ctr; destruct (from_primary n); [specialize (HCID eq_refl); clear -HCID| clear]; lia).
  assert (PBR : 2147450880 + 787968 <= PBA /\ PBA <= 2147450880 + qS) by nlia.
  (* [comment removed for export] *)
  eapply evtA_cut; [apply secD_pgran|]. cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU1c & WM1 & MI1 & PSH1).
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mk _) => rename mk into m1 end.
  assert (MU1 : munch [(PBA, PBA + 1)] m m1).
  { eapply munch_weaken; [| exact MU1c]. unfold PGW. destruct (n mod 8 =? 0); [intros xo _; exact I| intros xo Hxo; exact Hxo]. }
  xport_stk SK0 MU1 WM1. xport FR0 MU1 WM1. xport HDR0 MU1 WM1. xport USR0 MU1 WM1. xport MAG0 MU1 WM1.
  xport ST0 MU1 WM1. xport LRG0 MU1 WM1. xport_pg PG0 MU1.
  xport GF0 MU1 WM1. xport F44 MU1 WM1. xport F52 MU1 WM1. xport LSG0 MU1 WM1. xport LSC0 MU1 WM1. xport HK00 MU1 WM1.
  assert (TC1 : thread_cells m1 tp TSD CTX T).
  { destruct TC as (Ta & Tb & Tc & Td & Te). xport Ta MU1 WM1. xport Tb MU1 WM1. xport Tc MU1 WM1. xport Td MU1 WM1. xport Te MU1 WM1.
    exact (conj Ta (conj Tb (conj Tc (conj Td Te)))). }
  assert (BYSZ1 : from_primary n = true -> rw_cells asegs m1 (T + 2912 + 8 * cid) [C8 bsz]).
  { intros FP. pose proof (BYSZ FP) as BY. pose proof (HCID FP) as HC. xportK BY MU1 WM1 HC. exact BY. }
  (* [comment removed for export] *)
  eapply evtA_cut; [eapply secD_stats; [exact MI1| exact SK0| exact FR0| exact TC1| exact ST0| exact LRG0| exact BYSZ1]|].
  cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU2 & WM2 & MI2 & SK2 & ST2 & CTR2).
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mk _) => rename mk into m2 end.
  clear SK0 ST0 LRG0 BYSZ1 TC1 MI1.
  xportK FR0 MU2 WM2 CTRR. xportK HDR0 MU2 WM2 CTRR. xportK USR0 MU2 WM2 CTRR. xportK MAG0 MU2 WM2 CTRR. xport_pgK PG0 MU2 CTRR.
  xportK GF0 MU2 WM2 CTRR. xportK F44 MU2 WM2 CTRR. xportK F52 MU2 WM2 CTRR. xportK LSG0 MU2 WM2 CTRR. xportK LSC0 MU2 WM2 CTRR. xportK HK00 MU2 WM2 CTRR.
  (* [comment removed for export] *)
  eapply evtA_cut; [eapply secD_fill; [exact MI2| exact PG0| exact GF0| exact F44| exact F52| exact USR0]|].
  cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU3 & WM3 & MI3 & USR3).
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mk _) => rename mk into m3 end.
  clear GF0 F44 F52 PG0 USR0 MI2.
  unfold FL in *.
  assert (FLR : 1 <= Z.min n 4096 <= n) by (clear -Hn'; lia).
  xport_stkK SK2 MU3 WM3 FLR. xportK FR0 MU3 WM3 FLR. xportK HDR0 MU3 WM3 FLR. xportK MAG0 MU3 WM3 FLR.
  xportK LSG0 MU3 WM3 FLR. xportK LSC0 MU3 WM3 FLR. xportK HK00 MU3 WM3 FLR.
  (* [comment removed for export] *)
  eapply evtA_cut; [eapply secD_tail; [exact MI3| exact SK2| exact FR0| exact HDR0| exact MAG0| exact LSG0| exact LSC0| exact HK00]|].
  cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU4 & WM4 & MI4 & SK4 & B1K & HDR4 & MAG4).
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mk _) => rename mk into m4 end.
  clear SK2 FR0 HDR0 MAG0 LSG0 LSC0 HK00 MI3.
  (* [comment removed for export] *)
  xport USR3 MU4 WM4.
  assert (MU34 : munch [(lo, bv_unsigned sp); (ab + rz + -16, ab + rz + -16 + 2); (ab, ab + 16); (ab + rz, ab + rz + Z.min n 4096)] m2 m4).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU3] | eapply munch_weaken; [| exact MU4]]; incl_by FLR. }
  assert (WM34 : wmono asegs m2 m4) by (eapply wmono_trans; [exact WM3| exact WM4]).
  xportK ST2 MU34 WM34 FLR.
  assert (CTR4 : if from_primary n then rw_cells asegs m4 (T + 2912 + 8 * cid) [C8 (Z_to_bv 64 (bv_unsigned bsz + 1))] /\ rw_cells asegs m4 (T + 2904) [C8 stl]
                 else rw_cells asegs m4 (T + 2904) [C8 (Z_to_bv 64 (bv_unsigned stl + 1))]).
  { destruct (from_primary n); [destruct CTR2 as [C1x C2x]; pose proof (HCID eq_refl) as HC; xportK C1x MU34 WM34 FLR HC; xportK C2x MU34 WM34 FLR; exact (conj C1x C2x)
                                | xportK CTR2 MU34 WM34 FLR; exact CTR2]. }
  assert (PSH4 : n mod 8 <> 0 -> rw_cells asegs m4 (kShadowBase + (ub + 8 * n8) / 8) [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NZ. assert (LT : 8 * n8 < n) by (revert NZ; rewrite (Z.mod_eq n 8) by (clear; lia); fold n8; clear -N8R; lia).
    specialize (PSH1 LT). xportK PSH1 MU2 WM2 CTRR PBR. xportK PSH1 MU34 WM34 FLR PBR.
    unfold kShadowBase, ub. replace (2147450880 + (ab + rz + 8 * n8) / 8) with PBA
      by (unfold PBA; replace (ab + rz + 8 * n8) with ((qa + qr + n8) * 8) by nlia; rewrite Z.div_mul by (clear; lia); clear; lia).
    rewrite (Z.mod_eq n 8) by (clear; lia). fold n8. exact PSH1. }
  (* [comment removed for export] *)
  assert (MU : munch W4 m m4).
  { unfold W4, ub, cb, kShadowBase.
    replace (2147450880 + (ab + rz + 8 * n8) / 8) with PBA
      by (unfold PBA; replace (ab + rz + 8 * n8) with ((qa + qr + n8) * 8) by nlia; rewrite Z.div_mul by (clear; lia); clear; lia).
    revert MU1c. unfold PGW. destruct (n mod 8 =? 0); cbn [app]; intros MU1c.
    all: eapply munch_trans; [| eapply munch_trans; [| eapply munch_weaken; [| exact MU34]]].
    1: eapply munch_weaken; [| exact MU1c]. 2: eapply munch_weaken; [| exact MU2].
    4: eapply munch_weaken; [| exact MU1c]. 5: eapply munch_weaken; [| exact MU2].
    all: incl_by FLR CTRR PBR. }
  apply evtA_done. unfold segD5_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [eapply wmono_trans; [exact WM1|]; eapply wmono_trans; [exact WM2| exact WM34]|]. split; [exact MI4|]. split; [exact SK4|].
  split; [exact B1K|]. split; [exact HDR4|]. split; [exact USR3|]. split; [exact MAG4|]. split; [exact PSH4|]. split; [exact ST2| exact CTR4].
Qed.
End ALLOC.
End RC__1.

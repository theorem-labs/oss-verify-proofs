(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_unwind AF_depot1 AF_depot2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts AsanState AsanOps AsanDepot.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac cstep := stepA; try first [if_true | if_false].

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac tlia ::= first [ Zify.zify; xlia zchecker
  | sf_unhide; first [ zify_prune_neg; Zify.zify; xlia zchecker
                     | zify_prune_plain; Zify.zify; xlia zchecker
                     | LiaA.zify_prune_keep_or; Zify.zify; xlia zchecker
                     | Zify.zify; xlia zchecker ] ].
Ltac transport_after_call ::= transport_after_call_fast.
Tactic Notation "callA_drop" uconstr(SPEC) "dropping" ne_hyp_list(hs) :=
  lazymatch goal with
  | |- evtA ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtA_cut; [ eapply SPEC | clear hs; post_call segs m; ret_pc_lit ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma rw_cells_app_split : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. aceil.
  intros segs m A cs1 cs2 [[WF B] W]. apply cells_wf_app in WF. destruct WF as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite (cells_bytes_length _ W1) in B2.
  rewrite cells_size_app in W. destruct W as (Wa & Wb & Wr).
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Wr. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Wr. lia.
Qed.
Lemma rw_cells_app_join : forall segs m A cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof. aceil.
  intros segs m A cs1 cs2 [[W1 B1] (Wa & Wb & Wr)] [[W2 B2] (Va & Vb & Vr)]. split; [split|].
  - apply cells_wf_app. auto.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite (cells_bytes_length _ W1). auto.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))); [apply Wr; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply Vr. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PUT.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem).
Variables (lo hi A len : Z) (ws : list word) (NB : list Z) (HS : list Z) (N : Z)
          (fr b sb : Z) (bs : list byte) (mx j0 j1 j2 : word).
Definition TD : Z := 0x18fa58.
Definition SS : Z := 0x17fa48.
Definition keyZ : list Z := map bv_unsigned (firstn (Z.to_nat len) ws).
Definition h : Z := depot_hash keyZ.
Definition bkt : Z := bucket_of h.
Definition head : Z := bucket_head HS bkt.
Definition NA : Z := nthz NB ((N + 1) / kDepotNodesPerBlock) + 16 * ((N + 1) mod kDepotNodesPerBlock).

Hypothesis SK : stk asegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 224.
Hypothesis SPH : bv_unsigned sp <= hi.
Hypothesis HI : hi < 2^47.
Hypothesis MI : mem_inv asegs m.
(* [comment removed for export] *)
Hypothesis TR : u64arr asegs m A ws.
Hypothesis LEN : 1 <= len <= Z.of_nat (length ws).
Hypothesis LWS : Z.of_nat (length ws) <= 30.
Hypothesis TA : bv_unsigned sp <= A /\ A + 8 * Z.of_nat (length ws) <= hi.
(* [comment removed for export] *)
Hypothesis HN : 0 <= N /\ N + 2 < 2^31 /\ N = zlen HS.
Hypothesis HSR : forall i, 0 <= nth_hash HS i < 2^64.
Hypothesis TABK : rw_cells asegs m (TD + 4 * bkt) [C4 (Z_to_bv 64 head)].
Hypothesis NUQ : rw_cells asegs m (TD + 0x400000) [C4 (Z_to_bv 64 N)].
Hypothesis HM1 : forall k, 0 <= k < kNodesMap1 -> rw_cells asegs m (TD + 0x400010 + 8 * k) [C8 (Z_to_bv 64 (nthz NB k))].
Hypothesis HND : forall i, 1 <= i <= N -> exists sid,
  rw_cells asegs m (nthz NB (i / kDepotNodesPerBlock) + 16 * (i mod kDepotNodesPerBlock))
           [C8 (Z_to_bv 64 (nth_hash HS i)); C4 (Z_to_bv 64 (node_link HS i)); C4 sid].
Hypothesis NBC : forall i, 1 <= i <= N + 1 -> i / kDepotNodesPerBlock < zlen NB.          (* [comment removed for export] *)
Hypothesis NBR : forall blk, In blk NB -> placed blk kDepotNodeBlockBytes.          (* [comment removed for export] *)
Hypothesis NBAL : forall blk, In blk NB -> blk mod 16 = 0.
Hypothesis NEWN : rw_cells asegs m NA [C8 j0; C4 j1; C4 j2].                            (* [comment removed for export] *)
Hypothesis NEWSEP : forall i, 1 <= i <= N ->
  NA + 16 <= nthz NB (i / kDepotNodesPerBlock) + 16 * (i mod kDepotNodesPerBlock) \/ nthz NB (i / kDepotNodesPerBlock) + 16 * (i mod kDepotNodesPerBlock) + 16 <= NA.
(* [comment removed for export] *)
Hypothesis SSC : rw_cells asegs m SS [C8 (Z_to_bv 64 fr)].
Hypothesis BLK : rw_cells asegs m (SS + 16 + 16 * b) [C8 (Z_to_bv 64 sb); C4 (Z_to_bv 64 (fr - b * kStoreBlockFrames))].
Hypothesis BMX : rw_cells asegs m (SS + 28 + 16 * b) [C4 mx].
Hypothesis Hb : b = fr / kStoreBlockFrames.
Hypothesis NOSTR : (fr + len) / kStoreBlockFrames = b.                                   (* [comment removed for export] *)
Hypothesis FR0 : 0 <= fr.
Hypothesis FRB : fr + len + 1 < 2^32.
Hypothesis SB : u8arr asegs m sb bs.
Hypothesis LSB : Z.of_nat (length bs) = kStoreBlockBytes.
Hypothesis SB1 : 0x603000 <= sb.                                                       (* [comment removed for export] *)
Hypothesis SB2 : sb + kStoreBlockBytes <= alloc_ceiling.
Hypothesis NASB : NA + 16 <= sb \/ sb + kStoreBlockBytes <= NA.
Hypothesis NBSB : forall blk, In blk NB -> blk + kDepotNodeBlockBytes <= sb \/ sb + kStoreBlockBytes <= blk.
(* [comment removed for export] *)
Hypothesis GOTF : rw_cells asegs m 0xa49a0 [C8 (Z_to_bv 64 0x13f6a8)].
Hypothesis CFF : rw_cells asegs m (0x13f6a8 + 240) [C4 (Z_to_bv 64 0)].
(* [comment removed for export] *)
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= hi -> P (Z_to_bv 64 a, n).
Hypothesis PDAT : forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).
Hypothesis PRO : forall a n, 0x10000 <= a -> a + Z.of_nat n <= 0x31000 -> P (Z_to_bv 64 a, n).
Hypothesis PNB : forall blk a n, In blk NB -> blk <= a -> a + Z.of_nat n <= blk + kDepotNodeBlockBytes -> P (Z_to_bv 64 a, n).
Hypothesis PSB : forall a n, sb <= a -> a + Z.of_nat n <= sb + kStoreBlockBytes -> P (Z_to_bv 64 a, n).

Definition put_post : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (id : Z),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 id) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ ( (* [comment removed for export] *)
         (1 <= id <= N /\ nth_hash HS id = h /\ munch [(bv_unsigned sp - 224, bv_unsigned sp)] m m')
       \/ (* [comment removed for export] *)
         (id = N + 1 /\ (forall j, 1 <= j <= N -> nth_hash HS j <> h)
          /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (TD + 4 * bkt, TD + 4 * bkt + 4); (TD + 0x400000, TD + 0x400000 + 4);
                    (NA, NA + 16); (SS, SS + 8); (SS + 24 + 16 * b, SS + 28 + 16 * b);
                    (sb + 8 * (fr mod 2^20), sb + 8 * (fr mod 2^20) + 8 * (len + 1))] m m'
          /\ rw_cells asegs m' (TD + 4 * bkt) [C4 (Z_to_bv 64 (N + 1))]
          /\ rw_cells asegs m' (TD + 0x400000) [C4 (Z_to_bv 64 (N + 1))]
          /\ (exists sid, rw_cells asegs m' NA [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 head); C4 sid])
          /\ rw_cells asegs m' SS [C8 (Z_to_bv 64 (fr + (len + 1)))]
          /\ rw_cells asegs m' (SS + 16 + 16 * b) [C8 (Z_to_bv 64 sb); C4 (Z_to_bv 64 (fr - b * 2^20 + (len + 1)))]
          /\ (exists bs', u8arr asegs m' sb bs' /\ Z.of_nat (length bs') = kStoreBlockBytes))).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End PUT.
End RC__1.

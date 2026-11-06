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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 AMTac ARt2_lib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d AMallocI.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt2gfb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt22wr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx.ARt27j4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2gfb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt23oh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2hw4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt22wr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Definition AINST : Z := 0xb1558.
Definition QINST : Z := 0xb1830.   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac base_of t := lazymatch t with ?u + _ => base_of u | ?u - _ => base_of u | _ * ?u => base_of u | _ => t end.
Ltac apart_guided x y :=
  let bx := base_of x in let bz := base_of y in
  match goal with
  | H : apart ?a _ ?c _ |- _ =>
      let ba := base_of a in let bc := base_of c in
      first [ constr_eq bx ba; constr_eq bz bc | constr_eq bx bc; constr_eq bz ba ];
      unfold apart in H; lia
  end.
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].
Ltac kung := cbv delta [kHighMemBeg kDepotNodesBlock kStackStoreBlockBytes kShadowOffset kStackStoreBlockFrames kMaxSize
                        kAsanHeapLeftRedzoneMagic kMaxPrimaryUser kMallocFillByte kAllocBegMagic CHUNK_ALLOCATED].
Ltac eqrefl := lazymatch goal with |- _ = _ => reflexivity end.

(* [comment removed for export] *)
Ltac faobj := first
  [ assumption
  | match goal with K : aobjK _ _ |- _ => exact (aobjK_e _ _ K) end
  | match goal with H : aobjK _ _ /\ _ |- _ => exact (aobjK_e _ _ (proj1 H)) end
  | match goal with H : aobj _ _ /\ _ |- _ => exact (proj1 H) end
  | lazymatch goal with |- aobj ?q' _ => let b' := base_of q' in     (* [comment removed for export] *)
      match goal with
      | K : aobjK ?q _ |- _ => let b := base_of q in constr_eq b b'; apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kung; lia
      | K : aobj ?q _ |- _ => let b := base_of q in constr_eq b b'; apply (aobj_sub _ _ _ _ K); kung; lia
      | H : aobjK ?q _ /\ _ |- _ => let b := base_of q in constr_eq b b'; apply (aobj_sub _ _ _ _ (aobjK_e _ _ (proj1 H))); kung; lia
      | H : aobj ?q _ /\ _ |- _ => let b := base_of q in constr_eq b b'; apply (aobj_sub _ _ _ _ (proj1 H)); kung; lia
      end end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kung; lia end
  | match goal with H : aobjK _ _ /\ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ (proj1 H))); kung; lia end
  | apply aobj_hi; kung; lia ].
Ltac fpz := first
  [ assumption
  | lazymatch goal with |- pz_in ?q' _ => let b' := base_of q' in
      match goal with
      | K : aobjK ?q _ |- _ => let b := base_of q in constr_eq b b'; apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kung; lia
      | K : aobj ?q _ |- _ => let b := base_of q in constr_eq b b'; apply (aobj_pz_in _ _ _ _ K); kung; lia
      | H : aobjK ?q _ /\ _ |- _ => let b := base_of q in constr_eq b b'; apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ (proj1 H))); kung; lia
      | H : aobj ?q _ /\ _ |- _ => let b := base_of q in constr_eq b b'; apply (aobj_pz_in _ _ _ _ (proj1 H)); kung; lia
      end end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kung; lia end
  | unfold pz_in, kLowShadowMapBeg, kHighMemBeg; kung; lia ].
(* [comment removed for export] *)
Ltac free_linC H := lazymatch type of H with aobj ?p ?n /\ ?R =>
  let A := fresh "A" H in pose proof (proj1 H : aobj p n) as A; change (aobjK p n /\ R) in H; aobj_lin1 A end.
Ltac free_lin := repeat match goal with
  | H : aobj _ _ /\ _ |- _ => free_linC H
  | H : aobj _ _ |- _ => aobj_lin1S H end.
(* [comment removed for export] *)
Ltac xfer H M WMH :=
  lazymatch type of M with munch ?W ?mi ?mc =>
  lazymatch type of H with
  | ro_cells _ _ ?A ?cs => apply (ro_cells_transport rsegs W mi mc A cs) in H; [| exact M| cbn [disjoint_from]; simpl_sizes; slia]
  | bytes_at _ _ ?A ?bs => apply (bytes_at_transport rsegs W mi mc A bs) in H; [| exact M| cbn [disjoint_from]; simpl_sizes; slia]
  | rw_cells _ _ ?A ?cs => apply (rw_cells_transport rsegs W mi mc A cs) in H; [| exact M| exact WMH| cbn [disjoint_from]; simpl_sizes; slia]
  end end.
(* [comment removed for export] *)
Ltac kpost MUc WMc :=
  lazymatch type of MUc with munch _ ?mo ?mn =>
    rewrite ?unsigned_lit in MUc by lia;
    transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
    try match goal with H : mem_inv rsegs mo |- _ => clear H end; try clear mo end.
(* [comment removed for export] *)
Ltac xdepot DR MUc :=
  lazymatch type of DR with depot_repL _ _ _ ?n0 ?f0 ?mo =>
  lazymatch type of MUc with munch _ mo ?mn =>
    eapply (depot_repL_agree _ _ _ n0 f0 mo mn) in DR;
    [| intros a Ha; apply (MUc (Z_to_bv 64 a));
       unfold depot_foot in Ha; cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha; unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in Ha;
       destruct Ha as [Ha|[Ha|Ha]]; rewrite unsigned_lit by lia; cbn [outside];
       OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
       first [ exact I
             | (* [comment removed for export] *)
               lazymatch goal with |- ~ (?lo <= _ < _) => lazymatch type of Ha with ?blk <= _ < _ =>
                 let bl := base_of lo in
                 match goal with H : apart ?a' _ ?c' _ |- _ =>
                   first [ constr_eq a' blk; (let bc := base_of c' in constr_eq bc bl) | constr_eq c' blk; (let ba := base_of a' in constr_eq ba bl) ];
                   unfold apart in H; lia end end end
             | lia
             | match goal with H : apart ?a' _ ?c' _ |- _ =>
                 first [ constr_eq a' n0 | constr_eq a' f0 | constr_eq c' n0 | constr_eq c' f0 ]; unfold apart in H; lia end ] ]
  end end.
(* [comment removed for export] *)
Ltac tcells E := unfold thread_cells; rewrite E; change (6192088 - 88) with 6192000;
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [assumption | faobj | kung; lia].
(* [comment removed for export] *)
Ltac fside E :=
  lazymatch goal with
  | |- poison_consts _ => unfold poison_consts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; eassumption
  | |- aobj _ _ => lazymatch goal with |- ?g => tryif has_evar g then try eassumption else faobj end
  | |- aobjK _ _ => apply aobjK_i; faobj
  | |- pz_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try eassumption else fpz end
  | |- pz0_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try eassumption else plia end
  | |- fl_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try eassumption else plia end
  | |- m2s_in _ => lazymatch goal with |- ?g => tryif has_evar g then try eassumption else plia end
  | |- ?g => tryif has_evar g then first [ eassumption | eqrefl ]
             else first [ eassumption | eqrefl | lia | unfold QINST, AINST; kung; lia | rewrite <- E; eassumption
                        | match goal with S : sh _ = _ |- _ => rewrite S; eassumption end | left; kung; lia
                        | rewrite ?unsigned_lit by lia; first [eassumption | lia | kung; lia]
                        | kung; slia
                        | apply mod_add_lit; [lia | assumption | reflexivity]
                        | lazymatch goal with |- _ \/ _ => unfold boxed in *; kung; lia end ]
  end.
Ltac unfa := unfold off_th_unwinding, dealloc_entry, qchunk_entry, qput_entry, enqueue_entry, free_mid_entry, ia_entry in *.


(* [comment removed for export] *)
Definition free_key (top bot fp : Z) (ra : word) : list Z :=
  if unwind_depth2 top bot fp then [0x58994; bv_unsigned ra] else [0x58994].
Lemma free_key_len : forall top bot fp ra, (1 <= length (free_key top bot fp ra) <= 255)%nat.
Proof. intros. unfold free_key. destruct (unwind_depth2 top bot fp); cbn; lia. Qed.
Lemma free_key_len2 : forall top bot fp ra, (length (free_key top bot fp ra) <= 2)%nat.
Proof. intros. unfold free_key. destruct (unwind_depth2 top bot fp); cbn; lia. Qed.
Lemma free_key_range : forall top bot fp ra, Forall (fun w => 0 <= w < 2^64) (free_key top bot fp ra).
Proof.
  intros. unfold free_key. pose proof (zr_word ra) as R; unfold inr64 in R.
  destruct (unwind_depth2 top bot fp); repeat constructor; lia.
Qed.

(* [comment removed for export] *)
Definition free_consts (m : word -> option byte) : Prop :=
     ro_cells rsegs m 0xb5898 [C1 (Z_to_bv 8 1)]                                              (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xb58bc [C4 (wz 30)]                                                     (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa8b60 [C8 (wz 0x1466e8)] /\ ro_cells rsegs m (0x1466e8 + 34) [C1 (Z_to_bv 8 1)]  (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x146688 [C8 (wz 0)]                                                       (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa8b68 [C8 (wz 0xb23b8)] /\ ro_cells rsegs m (0xb23b8 + 48) [C4 (wz 0)] (* [comment removed for export] *)
  /\ ro_cells rsegs m (QINST + 64) [C8 (wz (2^28))] /\ ro_cells rsegs m (QINST + 80) [C8 (wz (2^20))].  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition free_prefix_W (sp : word) (lo thr p r8 n0 f0 : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (thr + 3168, thr + 3168 + 1); (p + -16, p + -12); (p, p + 8);
   (thr + 2824, thr + 2840); (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (sh p, sh p + r8)].

(* [comment removed for export] *)
Definition dep_w8 (top bot fp : Z) : Z := if unwind_depth2 top bot fp then 2 else 1.
Definition dep_b16 (top bot fp : Z) (ra : word) (jb1 : list byte) : list byte := if unwind_depth2 top bot fp then le8 ra else jb1.
Lemma fdep_cells : forall (m : word -> option byte) top bot fp (ra : word) jb1,
  (if unwind_depth2 top bot fp
   then rw_cells rsegs m (fp + -2128 + 8) [C4 (wz 2)] /\ rw_cells rsegs m (fp + -2128 + 16) [C8 (wz 0x58994); C8 ra]
   else rw_cells rsegs m (fp + -2128 + 8) [C4 (wz 1)] /\ rw_cells rsegs m (fp + -2128 + 16) [C8 (wz 0x58994); CB 8 jb1]) ->
  rw_cells rsegs m (fp + -2128 + 8) [C4 (wz (dep_w8 top bot fp))] /\
  rw_cells rsegs m (fp + -2128 + 16) [C8 (wz 0x58994); CB 8 (dep_b16 top bot fp ra jb1)].
Proof.
  intros m top bot fp ra jb1 DEP. unfold dep_w8, dep_b16. destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16]; split; try assumption.
  apply (rwc_rebytes _ _ _ [C8 (wz 0x58994); CB 8 (le8 ra)]) in D16; [exact D16| cbn -[le8]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; apply length_le8| reflexivity].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ftrc_cells : forall (m : word -> option byte) top bot fp (ra : word) jb1 (A : Z),
  rw_cells rsegs m A [C8 (wz (A + 16))] -> rw_cells rsegs m (A + 8) [C4 (wz (dep_w8 top bot fp))] -> rw_cells rsegs m (A + 12) [C4 (wz 0)] ->
  rw_cells rsegs m (A + 16) [C8 (wz 0x58994); CB 8 (dep_b16 top bot fp ra jb1)] ->
  ro_cells rsegs m A [C8 (wz (A + 16)); C8 (wz (Z.of_nat (length (free_key top bot fp ra))))]
  /\ bytes_at rsegs m (A + 16) (u64s (map (Z_to_bv 64) (free_key top bot fp ra))).
Proof.
  intros m top bot fp ra jb1 A O0 D8 O12 D16. unfold free_key, dep_w8, dep_b16 in *.
  destruct (unwind_depth2 top bot fp); cbn [length Z.of_nat Pos.of_succ_nat Pos.succ map u64s]; split.
  - apply (trc_join m _ _ 2 O0 D8 O12). right; reflexivity.
  - destruct D16 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite Z_to_bv_bv_unsigned. exact B.
  - apply (trc_join m _ _ 1 O0 D8 O12). left; reflexivity.
  - destruct D16 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. apply bytes_at_app in B. destruct B as [B _].
    rewrite app_nil_r. exact B.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma obj_reshape : forall (m : word -> option byte) A junk, rw_cells rsegs m A [CB 2064 junk] ->
  exists (j0 j3 : word) (j12 jb : list byte), rw_cells rsegs m A [C8 j0; CB 8 j12; CB 2040 jb; C8 j3].
Proof.
  intros m A junk H.
  apply (rw_cells_split_CB rsegs m A [] 2064 junk [] [8; 8; 2040; 8]%nat) in H; [| reflexivity]. cbn [app mk_CB_cells] in H.
  pose proof H as [[WF _] _]. cbn in WF. (first [ dand5 WF as L0 L1 L2 L3 _ | destruct WF as (L0 & L1 & L2 & L3 & _) ]).
  exists (le_bytes_to_word (firstn 8 junk)), (le_bytes_to_word (firstn 8 (skipn 2040 (skipn 8 (skipn 8 junk))))),
         (firstn 8 (skipn 8 junk)), (firstn 2040 (skipn 8 (skipn 8 junk))).
  eapply rwc_rebytes; [| | exact H].
  - cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact L1 | exact L2 | exact I].
  - cbn [cells_bytes cbytes app]. rewrite (le8_of_bytes8 _ L0), (le8_of_bytes8 _ L3). reflexivity.
Qed.

End CEIL.

(* [comment removed for export] *)
Lemma obj_rejoin : forall (m : word -> option byte) A (w0 wf : word) (dw pc : Z) (b16 jrest : list byte),
  rw_cells rsegs m A [C8 w0] -> rw_cells rsegs m (A + 8) [C4 (wz dw)] -> rw_cells rsegs m (A + 12) [C4 (wz 0)] ->
  rw_cells rsegs m (A + 16) [C8 (wz pc); CB 8 b16] -> rw_cells rsegs m (A + 32) [CB 2024 jrest] -> rw_cells rsegs m (A + 2056) [C8 wf] ->
  exists junk, rw_cells rsegs m A [CB 2064 junk].
Proof.
  intros m A w0 wf dw pc b16 jrest H0 H8 H12 H16 H32 H2056.
  pose proof H16 as [[W16 _] _]. cbn in W16. (first [ dand3 W16 as _ L16 _ | destruct W16 as (_ & L16 & _) ]).
  pose proof H32 as [[W32 _] _]. cbn in W32. destruct W32 as (L32 & _).
  assert (J : rw_cells rsegs m A ([C8 w0] ++ [C4 (wz dw)] ++ [C4 (wz 0)] ++ [C8 (wz pc); CB 8 b16] ++ [CB 2024 jrest] ++ [C8 wf])).
  { apply rw_cells_app_join; [exact H0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply rw_cells_app_join; [exact H8|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
    apply rw_cells_app_join; [exact H12|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
    apply rw_cells_app_join; [exact H16|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.of_nat]. rewrite <- Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
    apply rw_cells_app_join; [exact H32|]. rewrite <- Z.add_assoc.
    replace (16 + 16 + Z.of_nat (cells_size [CB 2024 jrest])) with 2056 by (cbn [cells_size csize Nat.add]; lia). exact H2056. }
  cbn [app] in J.
  exists (le8 w0 ++ le4 (wz dw) ++ le4 (wz 0) ++ le8 (wz pc) ++ b16 ++ jrest ++ le8 wf).
  eapply rwc_rebytes; [| | exact J].
  - cbn -[le8 le4]. split; [| exact I]. rewrite !length_app, !length_le8, !length_le4, L16, L32. reflexivity.
  - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition free_hit_fast_W (sp : word) (lo thr p r8 n0 f0 lb cnt : Z) : list (Z * Z) :=
  free_prefix_W sp lo thr p r8 n0 f0 ++ [(thr + 80, thr + 112); (lb, lb + 24); (lb + 24 + 8 * cnt, lb + 32 + 8 * cnt)].

Definition free_hit_new0_W (sp : word) (lo thr p r8 n0 f0 b : Z) : list (Z * Z) :=
  free_prefix_W sp lo thr p r8 n0 f0 ++ [(thr + 80, thr + 112); (thr + 208 + 1920, thr + 208 + 1924); (thr + 208 + 2576, thr + 208 + 2584); (b, b + 32)].
Definition free_hit_newfull_W (sp : word) (lo thr p r8 n0 f0 lb b : Z) : list (Z * Z) :=
  free_prefix_W sp lo thr p r8 n0 f0 ++ [(thr + 80, thr + 112); (lb, lb + 8); (thr + 208 + 1920, thr + 208 + 1924); (thr + 208 + 2576, thr + 208 + 2584); (b, b + 32)].

Section FreeHit.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo p n b1 tsd ctx thr top bot r8 n0 f0 fr fd : Z) (D : list (list Z)) (old : word) (oldsh : list byte).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 2688.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis RA0 : 4096 <= bv_unsigned ra.
  Hypothesis RANE : bv_unsigned ra <> 0x58994.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis VLE : bv_unsigned s0 <= bv_unsigned sp.
  Hypothesis TOPR : 0 <= top < 2^64.
  Hypothesis BOTR : 0 <= bot < 2^64.
  Hypothesis TPE : tp = Z_to_bv 64 TP.
  (* [comment removed for export] *)
  Hypothesis PAL : p mod 16 = 0.
  Hypothesis PLO : aobj (p + -16) (16 + 8 * r8).   (* [comment removed for export] *)
  Hypothesis PNB : 0x60a000 <= p + -16.             (* [comment removed for export] *)
  Hypothesis PHI : p + 8 * r8 <= alloc_ceiling.
  Hypothesis NR : 1 <= n < 2^32.
  Hypothesis NQ : n <= 2^28.
  Hypothesis R8 : 8 * r8 - 8 < n <= 8 * r8.
  Hypothesis B1R : 0 <= b1 < 256.
  Hypothesis B1M : Z.land b1 3 = 1.
  Hypothesis HDR : rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)].
  Hypothesis CTX0 : rw_cells rsegs m p [C8 old].
  Hypothesis SHC : rw_cells rsegs m (sh p) [CB (Z.to_nat r8) oldsh].
  (* [comment removed for export] *)
  Hypothesis FCo : free_consts m.
  Hypothesis PCo : poison_consts m.
  Hypothesis IAM : ro_cells rsegs m (0xb5dc8 + 8 * Z.shiftr p 32) [C8 (wz 0)].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (wz ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (wz kMainTid)].
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TTB : rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)].
  Hypothesis TDT : ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)].
  Hypothesis TUNW : rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  Hypothesis TST : rw_cells rsegs m (thr + 2824) [C8 (wz fr); C8 (wz fd)].
  Hypothesis FRR : 0 <= fr < 2^64.
  Hypothesis FDR : 0 <= fd < 2^64.
  (* [comment removed for export] *)
  Hypothesis DR : depot_repL AL_pboth rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 3 < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_pc : apart (p + -16) (8 * r8 + 16) ctx 0x10000.
  Hypothesis SEP_pt : apart (p + -16) (8 * r8 + 16) thr 4096.
  Hypothesis SEP_pn : apart (p + -16) (8 * r8 + 16) n0 kDepotNodesBlock.
  Hypothesis SEP_pf : apart (p + -16) (8 * r8 + 16) f0 kStackStoreBlockBytes.
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).
  Let KEY : list Z := free_key top bot fp ra.
  Let D' : list (list Z) := fst (depot_putC D KEY).
  Let fid : Z := snd (depot_putC D KEY).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

End FreeHit.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].

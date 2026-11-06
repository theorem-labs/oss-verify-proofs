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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtSf1m ARtSnjd ARtSrgm AMTac ARt2_lib ARt_u2d AMallocI.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeH0 ANodijx ANod9v0 APgGeo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt4chi.

Module AFreePc.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw ARtSnjd AFreeH.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt4chi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt4chi.AFreePB.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition natz_boxed (P : Prop) : Prop := P.
Lemma natz_len_range : forall (A : Type) (l : list A) (a b : nat) (za zb : Z),
  Z.of_nat a = za -> Z.of_nat b = zb -> (a <= length l <= b)%nat -> (za <= Z.of_nat (length l) <= zb)%Z.
Proof. intros A l a b za zb <- <- H. split; apply Nat2Z.inj_le; apply H. Qed.
Lemma natz_len_le : forall (A : Type) (l : list A) (b : nat) (zb : Z), Z.of_nat b = zb -> (length l <= b)%nat -> (Z.of_nat (length l) <= zb)%Z.
Proof. intros A l b zb <- H. apply Nat2Z.inj_le; exact H. Qed.
Local Ltac natz_pos_lit p := lazymatch p with xH => idtac | xO ?q => natz_pos_lit q | xI ?q => natz_pos_lit q end.
Local Ltac natz_z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => natz_pos_lit p end.
Local Ltac natz_kl_box :=
  try (lazymatch goal with
       | H : (?a <= @length ?A ?l <= ?b)%nat |- _ =>
           let za := eval vm_compute in (Z.of_nat a) in let zb := eval vm_compute in (Z.of_nat b) in
           natz_z_lit za; natz_z_lit zb;
           let Hz := fresh "KLz" in
           pose proof (natz_len_range A l a b za zb (@eq_refl Z za) (@eq_refl Z zb) H) as Hz;
           change (natz_boxed (a <= @length A l <= b)%nat) in H
       | H : (@length ?A ?l <= ?b)%nat |- _ =>
           let zb := eval vm_compute in (Z.of_nat b) in
           natz_z_lit zb;
           let Hz := fresh "KLz" in
           pose proof (natz_len_le A l b zb (@eq_refl Z zb) H) as Hz;
           change (natz_boxed (@length A l <= b)%nat) in H
       end).
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
Definition free_cprefixB_W (spd : word) (thr p n0 f0 : Z) : list (Z * Z) :=
  [(bv_unsigned spd - 560, bv_unsigned spd); (p + -16, p + -12); (p, p + 8);
   (thr + 2824, thr + 2840); (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000)].

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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TfIncl.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_with_region B S a n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TfIncl.tf_with_region_fast B S a n.
(* [comment removed for export] *)

Section FreeBigCore.
Context {Clg : Ceiling}.
  Variables (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto : Z) (D : list (list Z)) (key : list Z) (old : word) (sb : Z).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned spd).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned spd - 704.
  Hypothesis SPA : bv_unsigned spd mod 16 = 0.
  Hypothesis SPH : bv_unsigned spd <= 2^47.
  Hypothesis RA2 : bv_unsigned rac mod 2 = 0.
  Hypothesis TPE : tp = Z_to_bv 64 TP.
  (* [comment removed for export] *)
  Hypothesis PAL : p mod 16 = 0.
  Hypothesis PLO : aobj (p + -16) (16 + 8 * r8).
  Hypothesis PNB : 0x60a000 <= p + -16.
  Hypothesis PHI : p + 8 * r8 <= alloc_ceiling.
  Hypothesis NR : 1 <= n < 2^32.
  Hypothesis NQB : 2^28 < n.
  Hypothesis R8 : 8 * r8 - 8 < n <= 8 * r8.
  Hypothesis B1R : 0 <= b1 < 256.
  Hypothesis B1M : Z.land b1 3 = 1.
  Hypothesis HDR : rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)].
  Hypothesis CTX0 : rw_cells rsegs m p [C8 old].
  (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis POUT : p + -16 < sb \/ sb + 2^37 <= p + -16.
  Hypothesis CSB : ro_cells rsegs m 0xb1578 [C8 (wz sb)].
  (* [comment removed for export] *)
  Hypothesis FCo : free_consts m.
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (wz ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (wz kMainTid)].
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TST : rw_cells rsegs m (thr + 2824) [C8 (wz fr); C8 (wz fd)].
  Hypothesis FRR : 0 <= fr < 2^64.
  Hypothesis FDR : 0 <= fd < 2^64.
  (* [comment removed for export] *)
  Hypothesis DR : depot_repL AL_pboth rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 256 < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis STO : ro_cells rsegs m sto [C8 (wz (sto + 16)); C8 (wz (Z.of_nat (length key)))].
  Hypothesis TRW : bytes_at rsegs m (sto + 16) (u64s (map (Z_to_bv 64) key)).
  Hypothesis STOR : bv_unsigned spd <= sto /\ sto + 2064 <= 2^47.
  Hypothesis KL : (1 <= length key <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) key.
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

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned spd).
  Let D' : list (list Z) := fst (depot_putC D key).
  Let fid : Z := snd (depot_putC D key).

  (* [comment removed for export] *)
  #[using="SEP_tc SEP_f0c SEP_n0c SEP_f0t SEP_n0t SEP_pf SEP_pn SEP_pt SEP_pc KR KL STOR TRW STO DF0 DN0 DTOT DLEN DND DR FDR FRR TST TSDL CT8 TH0 TC FCo CSB POUT SBR CTX0 HDR B1M B1R R8 NQB NR PNB PLO PAL TPE RA2 LO ST MI sb old r8 ctx tsd Clg"] Lemma free_cprefixB : forall (Q : machine_state -> Prop),
    (forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        (* [comment removed for export] *)
        rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
        (* [comment removed for export] *)
        rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
        rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        rw_cells rsegs m' p [C8 (wz fid)] ->
        depot_repL AL_pboth rsegs D' n0 f0 m' ->
        munch (free_cprefixB_W spd thr p n0 f0) m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (usp - 80) ->
        evt rsegs Q (MS (mkR (wz qput_recret) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                            (wz (usp + -80)) (wz (p + -16)) (wz (thr + 208)) (wz sto) (wz (p + -16)) (wz n) a6' a7'
                            s2 s3 s4 s5 (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz cbrec_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz AINST) (wz p) a2 a3 (wz sto) (wz 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz dealloc_entry) fc None m (seg_rom rsegs)).
  Proof. natz_kl_box. try clear SPA. try clear SPH. try clear PHI.   (* [comment removed for export] *)
    intros Q K.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR. pose proof (zr_word rac) as RAR; unfold inr64 in RAR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    pose proof FCo as FC'. (first [ dand9 FC' as Fini Fmcs Fgotcf Ffu Fhook Fgotfl Fffs Fqmax Fcmax | destruct FC' as (Fini & Fmcs & Fgotcf & Ffu & Fhook & Fgotfl & Fffs & Fqmax & Fcmax) ]).
    unfold free_cprefixB_W, qput_recret, cbrec_entry, QINST, AINST, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kStackStoreBlockFrames, off_th_unwinding in *.
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    rewrite TPL in *. change (6192088 - 88) with 6192000 in Ctsd.
    assert (P32E : Z.shiftr p 32 = Z.shiftr p 32) by reflexivity.
    pose proof (munch_refl [(usp - 560, usp); (p + -16, p + -12); (p, p + 8); (thr + 2824, thr + 2840); (1600136, 6122152); (n0, n0 + 1048576); (f0, f0 + 8388608)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    eapply (dealloc_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m 726360 p n b1 sto tsd ctx thr fr fd lo old);
      [> try (fside P32E) .. | idtac].
    intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 HDR4 CTX4 TST4 MU4 WM4 MI4 ST4. unfa.
    rewrite ?unsigned_lit in MU4, ST4 by lia.
    clear HDR CTX0 TST. xdepot DR MU4.
    xfer STO MU4 WM4. eapply bytes_at_transport in TRW; [| exact MU4| rewrite u64s_length, length_map; cbn [disjoint_from]; slia].
    kpost MU4 WM4.
    assert (TC4 : thread_cells m4 tp tsd ctx thr) by tcells TPL.
    (* [comment removed for export] *)
    eapply (qchunk_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 726360 p n b1 sto tsd ctx thr lo D key (sto + 16) n0 f0);
      [> try (fside P32E) .. | idtac].
    intros t0d t1d t2d a6d a7d t3d t4d t5d t6d m5 HDR5 CTX5 DR5 MU5 WM5 MI5 ST5. unfa.
    rewrite ?unsigned_lit in MU5, ST5 by lia. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in MU5.
    unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in MU5. change (5860008 + 8 * 2 ^ 15) with 6122152 in MU5.
    clear HDR4 CTX4 DR STO TRW. kpost MU5 WM5.
    assert (TC5 : thread_cells m5 tp tsd ctx thr) by tcells TPL. clear TC4.
    (* [comment removed for export] *)
    change (726360 + 728) with 727088.
    eapply (qput_pre_big_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 727088 (thr + 80) (thr + 208) sto p n (2^28) (2^20) sb lo);
      [> try (fside P32E) .. | idtac].
    intros m6 PFR MU6 WM6 MI6 ST6. unfa.
    rewrite ?unsigned_lit in PFR, MU6, ST6 by lia.
    xdepot DR5 MU6. kpost MU6 WM6.
    eapply K; unfa; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="fid KL DF0 DN0 TC PNB PLO SPH LO key D f0 n0 r8 ctx tsd p m"] Lemma free_cbtail : forall (Q : machine_state -> Prop) (m6 : word -> option byte)
      (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (xs2 xs3 xs4 xs5 : word) (nb fb lb qb : Z),
    mem_inv rsegs m6 -> stk rsegs m6 lo (usp + -80) ->
    0 <= qb <= 2^20 -> aobj (thr + 80) 32 ->
    rw_cells rsegs m6 (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
    rw_cells rsegs m6 (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    (stk rsegs m6 lo usp ->
       evt rsegs Q (MS (mkR rac spd gp tp t0' t1' t2' s0 s1 (wz qb) a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m6 (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz qput_recret) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                        a0' a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 xs5 (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz qput_recret) fc None m6 (seg_rom rsegs)).
  Proof. natz_kl_box. try clear MI. try clear ST. try clear SPA. try clear RA2. try clear TPE. try clear PAL. try clear PHI. try clear NR. try clear NQB. try clear R8. try clear B1R. try clear B1M. try clear HDR. try clear CTX0. try clear SBR. try clear POUT. try clear CSB. try clear FCo. try clear TH0. try clear CT8. try clear TSDL. try clear TST. try clear FRR. try clear FDR. try clear DR. try clear DND. try clear DLEN. try clear DTOT. try clear STO. try clear TRW. try clear STOR. try clear KR. try clear SEP_pc. try clear SEP_pt. try clear SEP_pn. try clear SEP_pf. try clear SEP_n0t. try clear SEP_f0t. try clear SEP_n0c. try clear SEP_f0c. try clear SEP_tc.   (* [comment removed for export] *)
    intros until qb. intros MI6 ST6 QBR C80 PFR QC K.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold QINST, kHighMemBeg in *.
    eapply (qput_tailB_ok gp tp _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m6 usp 727088 (thr + 80) (2^20) nb fb lb qb lo);
      [> try (fside CV) .. | idtac].
    intros ST7. rewrite Z_to_bv_bv_unsigned. apply K. exact ST7.
  Qed.
End FreeBigCore.
End AFreePc.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeS AFreeWD.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSf1m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANod9v0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS.ARtSxaw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt4chi.AFreePB OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeWDc.AFreePc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeWD.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Lemma natz_len_range : forall (A : Type) (l : list A) (a b : nat) (za zb : Z),
  Z.of_nat a = za -> Z.of_nat b = zb -> (a <= length l <= b)%nat -> (za <= Z.of_nat (length l) <= zb)%Z.
Proof. intros A l a b za zb <- <- H. split; apply Nat2Z.inj_le; apply H. Qed.
Lemma natz_len_le : forall (A : Type) (l : list A) (b : nat) (zb : Z), Z.of_nat b = zb -> (length l <= b)%nat -> (Z.of_nat (length l) <= zb)%Z.
Proof. intros A l b zb <- H. apply Nat2Z.inj_le; exact H. Qed.
Local Ltac natz_pos_lit p := lazymatch p with xH => idtac | xO ?q => natz_pos_lit q | xI ?q => natz_pos_lit q end.
Local Ltac natz_z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => natz_pos_lit p end.   (* [comment removed for export] *)
Local Ltac natz_kl :=
  repeat match goal with
  | H : (?a <= @length ?A ?l <= ?b)%nat |- _ =>
      let za := eval vm_compute in (Z.of_nat a) in let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit za; natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_range A l a b za zb (@eq_refl Z za) (@eq_refl Z zb) H) as Hz; clear H
  | H : (@length ?A ?l <= ?b)%nat |- _ =>
      let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_le A l b zb (@eq_refl Z zb) H) as Hz; clear H
  end.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Zifyk6b.   (* [comment removed for export] *)
Local Ltac Zify.zify_pre_hook ::= natz_kl; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Zifyk6b.zon_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
Definition free_directS0c_W (spd : word) (lo thr p n0 f0 pa idx hla h msz : Z) : list (Z * Z) :=
  [(bv_unsigned spd - 704, bv_unsigned spd); (p + -16, p + -12); (p, p + 8);
   (thr + 2824, thr + 2840); (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000)]
  ++ [(0xb1800, 0xb1804); (thr + 2840, thr + 2856); (0xb15d0, 0xb15d9); (0xb15e8, 0xb15f8); (0xb1818, 0xb1828);
      (pa + 8 * idx, pa + 8 * idx + 8); (hla + 24, hla + 32); (sh h, sh h + msz / 8); (thr + 2888, thr + 2904)].
(* [comment removed for export] *)
Ltac img_xfer H m2 AG WM :=
  lazymatch type of H with
  | ro_cells _ ?mm ?A ?cs => apply (ro_cells_ag mm m2 A cs) in H; [| intros i Hi; apply AG; clear -Hi; unfold img_quiet1, img_quiet; cbn [cells_size csize Nat.add] in Hi; lia]
  | rw_cells _ ?mm ?A ?cs => apply (rw_cells_ag mm m2 A cs) in H; [| exact WM | intros i Hi; apply AG; clear -Hi; unfold img_quiet1, img_quiet; cbn [cells_size csize Nat.add] in Hi; lia]
  end.

Section FreeDirectCore.
  Context {Clg : Ceiling}.
  Variables (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  (* [comment removed for export] *)
  Variables (lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto : Z) (D : list (list Z)) (key : list Z) (old : word) (sb : Z).
  (* [comment removed for export] *)
  Variables (pa u1 u2 srt h msz csz idx nf ca gA gM rf rfd mu md sealed : Z) (hs : list word) (hl hlb hlm hls canary : word) (oldsh : list byte).

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation nch := (Z.of_nat (length hs)).
  #[warnings="-notation-for-abbreviation"] Local Notation hla := (bv_unsigned hl).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned spd).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned spd - 704.   (* [comment removed for export] *)
  Hypothesis SPA : bv_unsigned spd mod 16 = 0.
  Hypothesis SPH : bv_unsigned spd <= 2^47.
  Hypothesis RA2 : bv_unsigned rac mod 2 = 0.
  Hypothesis TPE : tp = Z_to_bv 64 TP.
  (* [comment removed for export] *)
  Hypothesis PAL : p mod 16 = 0.
  Hypothesis PLO : aobj (p + -16) (16 + 8 * r8).
  Hypothesis PNB : 0x60a000 <= p + -16.
  Hypothesis PHI : p + 8 * r8 <= alloc_ceiling.
  Hypothesis NR : 1 <= n < 2^32.
  Hypothesis NQB : 2^28 < n.
  Hypothesis R8 : 8 * r8 - 8 < n <= 8 * r8.
  Hypothesis B1R : 0 <= b1 < 256.
  Hypothesis B1M : Z.land b1 3 = 1.
  Hypothesis HDR : rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)].
  Hypothesis CTX0 : rw_cells rsegs m p [C8 old].
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis POUT : p + -16 < sb \/ sb + 2^37 <= p + -16.
  Hypothesis CSB : ro_cells rsegs m 0xb1578 [C8 (wz sb)].
  (* [comment removed for export] *)
  Hypothesis FCo : free_consts m.
  Hypothesis PCo : poison_consts m.
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (wz ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (wz kMainTid)].
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TDT : ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)].
  Hypothesis TST : rw_cells rsegs m (thr + 2824) [C8 (wz fr); C8 (wz fd)].
  Hypothesis FRR : 0 <= fr < 2^64.
  Hypothesis FDR : 0 <= fd < 2^64.
  Hypothesis TRF : rw_cells rsegs m (thr + 2840) [C8 (wz rf); C8 (wz rfd)].
  Hypothesis TMU : rw_cells rsegs m (thr + 2888) [C8 (wz mu); C8 (wz md)].
  Hypothesis RFR : 0 <= rf < 2^64.
  Hypothesis RFDR : 0 <= rfd < 2^64.
  Hypothesis MUR : 0 <= mu < 2^64.
  Hypothesis MDR : 0 <= md < 2^64.
  (* [comment removed for export] *)
  Hypothesis DR : depot_repL AL_pboth rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 256 < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis STO : ro_cells rsegs m sto [C8 (wz (sto + 16)); C8 (wz (Z.of_nat (length key)))].
  Hypothesis TRW : bytes_at rsegs m (sto + 16) (u64s (map (Z_to_bv 64) key)).
  Hypothesis STOR : bv_unsigned spd <= sto /\ sto + 2064 <= 2^47.
  Hypothesis KL : (1 <= length key <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) key.
  (* [comment removed for export] *)
  Hypothesis PALO : aobj pa (8 * nch).
  Hypothesis PAHI : pa + 8 * nch <= alloc_ceiling.
  Hypothesis PAAL : pa mod 8 = 0.
  Hypothesis NRC : 1 <= nch < 2^20.
  Hypothesis U1R : 0 <= u1 < 256.
  Hypothesis U2R : 0 <= u2 < 2^15.
  Hypothesis SRTR : 0 <= srt < 256.
  Hypothesis IDX : 0 <= idx < nch.
  Hypothesis NTH : nth_error hs (Z.to_nat idx) = Some (wz h).
  Hypothesis NTL : nth_error hs (Z.to_nat (nch - 1)) = Some hl.
  Hypothesis HLLO : aobj hla 32.
  Hypothesis HLHI : hla + 32 <= alloc_ceiling.
  Hypothesis HLAL : hla mod 8 = 0.
  Hypothesis NFR : 0 <= nf < 2^64.
  Hypothesis CAR : 0 <= ca < 2^64.
  Hypothesis GAR : 0 <= gA < 2^64.
  Hypothesis GMR : 0 <= gM < 2^64.
  Hypothesis CSR : 0 <= csz < 2^64.
  Hypothesis HLO : aobj h msz.
  Hypothesis HAL : h mod 4096 = 0.
  Hypothesis MSZ : 4096 + 32 <= msz.
  Hypothesis MSZAL : msz mod 4096 = 0.
  Hypothesis HHI : h + msz <= alloc_ceiling.
  Hypothesis HSB : apart h msz sb (2^37).
  Hypothesis PH : p = h + 6144.                 (* [comment removed for export] *)
  Hypothesis PIN : p + 8 * r8 <= h + msz.
  Hypothesis BIG : 0x10000 <= msz / 8.          (* [comment removed for export] *)
  Hypothesis SHR : 0x7fff8200 <= sh h /\ sh h + msz / 8 <= kHighMemBeg.   (* [comment removed for export] *)
  Hypothesis NRST : nearest hs (p + -16) = h.
  Hypothesis SEALR : sealed <> 0 /\ 0 <= sealed < 2^64.
  Hypothesis SEP_hp : apart h msz pa (8 * nch).
  Hypothesis SEP_lp : apart hla 32 pa (8 * nch).
  Hypothesis SEP_ht : apart h msz thr 4096.
  Hypothesis SEP_hc : apart h msz ctx 0x10000.
  Hypothesis SEP_hn : apart h msz n0 kDepotNodesBlock.
  Hypothesis SEP_hf : apart h msz f0 kStackStoreBlockBytes.
  Hypothesis SEP_at : apart pa (8 * nch) thr 4096.
  Hypothesis SEP_ac : apart pa (8 * nch) ctx 0x10000.
  Hypothesis SEP_an : apart pa (8 * nch) n0 kDepotNodesBlock.
  Hypothesis SEP_af : apart pa (8 * nch) f0 kStackStoreBlockBytes.
  Hypothesis SEP_lt : apart hla 32 thr 4096.
  Hypothesis SEP_lc : apart hla 32 ctx 0x10000.
  Hypothesis SEP_ln : apart hla 32 n0 kDepotNodesBlock.
  Hypothesis SEP_lf : apart hla 32 f0 kStackStoreBlockBytes.
  Hypothesis HLA : hla = h \/ apart hla 32 h msz.
  Hypothesis SEP_pc : apart (p + -16) (8 * r8 + 16) ctx 0x10000.
  Hypothesis SEP_pt : apart (p + -16) (8 * r8 + 16) thr 4096.
  Hypothesis SEP_pn : apart (p + -16) (8 * r8 + 16) n0 kDepotNodesBlock.
  Hypothesis SEP_pf : apart (p + -16) (8 * r8 + 16) f0 kStackStoreBlockBytes.
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  (* [comment removed for export] *)
  Hypothesis CLMA : ro_cells rsegs m LMA_L [C8 (wz 4096); C8 (wz pa)].
  Hypothesis CSEAL : ro_cells rsegs m 0xa8bb0 [C8 (wz sealed)].
  Hypothesis NSRT : rw_cells rsegs m 0xb15d0 [C8 (wz nch); C1 (Z_to_bv 8 srt)].
  Hypothesis NFCA : rw_cells rsegs m 0xb15e8 [C8 (wz nf); C8 (wz ca)].
  Hypothesis LCK : rw_cells rsegs m 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)].
  Hypothesis GAM : rw_cells rsegs m 0xb1818 [C8 (wz gA); C8 (wz gM)].
  Hypothesis ARR : u64arr rsegs m pa hs.
  Hypothesis HDRL : rw_cells rsegs m h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)].
  Hypothesis HLC : hla = h \/ rw_cells rsegs m hla [C8 hlb; C8 hlm; C8 hls; C8 (wz (nch - 1))].
  Hypothesis A8C : a8_consts m canary.
  Hypothesis SHC : rw_cells rsegs m (sh h) [CB (Z.to_nat (msz / 8)) oldsh].

  Let D' : list (list Z) := fst (depot_putC D key).
  Let fid : Z := snd (depot_putC D key).

  (* [comment removed for export] *)
  Definition free_directS0c_post : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a4' a5' a6' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MSsvc (mkR (wz ldealloc_resume) (wz (usp + -80 + -32)) gp tp t0' t1' t2' (wz h) (wz h)
                     (wz (a8_pbeg h)) (wz (a8_len h msz)) (wz 4) (wz 4) a4' a5' a6' (wz 233)
                     (wz msz) s3 s4 s5 (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (wz madvise_ecall_pc) (wz 233) fc None m' (seg_rom rsegs)
    /\ munch (free_directS0c_W spd lo thr p n0 f0 pa idx hla h msz) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (usp + -80 + -32)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac]
    /\ rw_cells rsegs m' (usp + -80 + -32) [C8 s2; C8 (wz (thr + 80)); C8 (wz QINST); C8 (wz qput_recret)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xb15d0 [C8 (wz (nch - 1)); C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' 0xb15e8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))]
    /\ rw_cells rsegs m' 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)]
    /\ rw_cells rsegs m' 0xb1818 [C8 (wz (gA - msz)); C8 (wz (gM - msz))]
    /\ u64arr rsegs m' pa (upd hs (Z.to_nat idx) hl)
    /\ rw_cells rsegs m' h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)]
    /\ (hla = h \/ rw_cells rsegs m' hla [C8 hlb; C8 hlm; C8 hls; C8 (wz idx)])
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
    /\ rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))]
    /\ rw_cells rsegs m' (thr + 2888) [C8 (wz mu); C8 (wz md)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
    /\ rw_cells rsegs m' p [C8 (wz fid)]
    /\ depot_repL AL_pboth rsegs D' n0 f0 m'
    (* [comment removed for export] *)
    /\ bytes_at rsegs m' (sh h) (repeat (Z_to_bv 8 0) (Z.to_nat (msz / 8))).

  Theorem free_directS0c :
    evt rsegs free_directS0c_post
        (MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz AINST) (wz p) a2 a3 (wz sto) (wz 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz dealloc_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR. pose proof (zr_word hl) as HLR; unfold inr64 in HLR.
    eapply (free_cprefixB rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto D key old sb
              MI ST LO RA2 TPE PAL PLO PNB NR NQB R8 B1R B1M HDR CTX0 SBR POUT CSB FCo TC TH0 CT8 TSDL TST FRR FDR DR DND DLEN DTOT DN0 DF0
              STO TRW STOR KL KR SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc).
    intros t0' t1' t2' a6' a7' t3' t4' t5' t6' m1 PFR TST1 HDR1 CTX1 DR1 MU1 WM1 MI1 ST1.
    (* [comment removed for export] *)
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    rewrite TPL in *. change (6192088 - 88) with 6192000 in Ctsd.
    destruct SHR as [SH1 SH2]. destruct SEALR as [SNZ SR].
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, LMA_L in *.
    assert (SEP_pa : apart (p + -16) (8 * r8 + 16) pa (8 * nch)) by (clear -SEP_hp PH PIN R8 MSZ; unfold apart in *; lia).
    assert (SEP_ph : apart (p + -16) (8 * r8 + 16) h 32) by (clear -PH PIN R8 MSZ; unfold apart in *; lia).
    assert (SEP_pl : apart (p + -16) (8 * r8 + 16) hla 32) by (clear -HLA PH PIN R8 MSZ; unfold apart in *; lia).
    box POUT. box HLA.
    (* [comment removed for export] *)
    assert (AG1 : forall x, img_quiet1 x -> m1 (wz x) = m (wz x)).
    { intros x Hx. apply (MU1 (wz x)). rewrite unsigned_lit by (clear -Hx; unfold img_quiet1, img_quiet in Hx; lia).
      revert Hx. unfold free_cprefixB_W, img_quiet1, img_quiet. cbn [outside]. intros Hx. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; lia. }
    pose proof MU1 as MUY. unfold free_cprefixB_W in MUY.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    img_xfer Ccan m1 AG1 WM1. img_xfer Cgotcf m1 AG1 WM1. img_xfer Cthr m1 AG1 WM1. img_xfer Cgotsh m1 AG1 WM1. img_xfer Cshoff m1 AG1 WM1. img_xfer Cgotmid m1 AG1 WM1.
    img_xfer Cgotmide m1 AG1 WM1. img_xfer Cgothi m1 AG1 WM1. img_xfer Chivars m1 AG1 WM1. img_xfer Cgotms m1 AG1 WM1. img_xfer Creal m1 AG1 WM1. img_xfer Cgotps m1 AG1 WM1. img_xfer Cps m1 AG1 WM1.
    img_xfer Cini m1 AG1 WM1. img_xfer Ckey m1 AG1 WM1. img_xfer Ctsd m1 AG1 WM1.
    img_xfer CSB m1 AG1 WM1. img_xfer CLMA m1 AG1 WM1. img_xfer CSEAL m1 AG1 WM1.
    img_xfer NSRT m1 AG1 WM1. img_xfer NFCA m1 AG1 WM1. img_xfer LCK m1 AG1 WM1. img_xfer GAM m1 AG1 WM1.
    xfer Cctx MUY WM1. xfer Cthr2 MUY WM1. xfer TH0 MUY WM1. xfer CT8 MUY WM1. xfer TDT MUY WM1.
    xfer HDRL MUY WM1. xfer TRF MUY WM1. xfer TMU MUY WM1. xfer SHC MUY WM1.
    assert (ARR1 : u64arr rsegs m1 pa hs).
    { eapply u64arr_transport; [exact ARR| exact MUY| exact WM1|]. cbn [disjoint_from]. simpl_sizes. slia. }
    assert (HLC1 : hla = h \/ ((h + 32 <= hla \/ hla + 32 <= h) /\ rw_cells rsegs m1 hla [C8 hlb; C8 hlm; C8 hls; C8 (wz (nch - 1))])).
    { destruct HLA as [EE|AP]; [left; exact EE|]. destruct HLC as [EE|CC]; [left; exact EE| right].
      split; [clear -AP MSZ; unfold apart in AP; lia|].
      xfer CC MUY WM1. exact CC. }
    clear ARR HLC MUY. box HLC1.
    assert (TC1 : thread_cells m1 tp tsd ctx thr) by tcells TPL.
    assert (PC1 : poison_consts m1) by (unfold poison_consts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption).
    assert (NEI : a8_pbeg h < a8_pend h msz) by (apply a8_interior_nonempty; clear -BIG; lia).
    pose proof (rw_ro_prefix1 m1 (usp + -80) _ _ PFR) as CBC1.
    pose proof (proj1 HDR1 : ro_cells rsegs m1 (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]) as HDRU1.
    idtac "cells ok".
    (* [comment removed for export] *)
    assert (SPA2 : (usp + -80) mod 16 = 0) by (apply mod_add_lit; [lia | exact SPA | reflexivity]).
    rewrite ?unsigned_lit by lia.
    eapply (sdeal_pre (wz qput_recret) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80)) (wz (thr + 208)) (wz sto) (wz (p + -16)) (wz n) a6' a7'
              s2 s3 s4 s5 (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1
              lo (usp + -80) (p + -16) sb pa u1 u2 srt h msz csz idx nf ca gA gM n CHUNK_QUARANTINE b1 tsd ctx thr rf rfd mu md sealed hs hl hlb hlm hls);
      [> try (fside CV) .. | idtac].
    all: try (rewrite ?unsigned_lit by lia; first [fside CV | unfold CHUNK_QUARANTINE; lia | kcell]).
    idtac "sdeal applied".
    intros t0b t1b t2b a4b a5b a6b t3b t4b t5b t6b m2 DF NSRT2 NFCA2 LCK2 GAM2 ARR2 HDRL2 HLC2 TRF2 TMU2 SHD2 MU2 WM2 MI2 ST2.
    rewrite unsigned_lit in DF by (clear -LO CV SPR; lia). rewrite unsigned_lit in ST2 by (clear -LO CV SPR; lia).
    (* [comment removed for export] *)
    unfold sdeal_W, sdeal_prefix_W in MU2. cbn [app] in MU2. rewrite unsigned_lit in MU2 by (clear -LO CV SPR; lia). unfold off_th_unwinding in *.
    xfer PFR MU2 WM2. xfer TST1 MU2 WM2. xfer HDR1 MU2 WM2. xfer CTX1 MU2 WM2.
    xdepot DR1 MU2.
    unfold free_directS0c_post. rewrite ?unsigned_lit by lia. hot_eexists_all.
    split; [reflexivity|].
    split.
    { (* [comment removed for export] *)
      intros y Hy. rewrite (MU2 y), (MU1 y); [reflexivity| |]; revert Hy; clear -LO; unfold free_directS0c_W, free_cprefixB_W; rewrite ?AFreeH0.outside_app; cbn [outside app];
        intros Hy; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try tauto; try lia. }
    split; [exact (wmono_trans _ _ _ _ WM1 WM2)|].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [kcell | exact HLC2 | eassumption].
  Qed.

  (* [comment removed for export] *)
  Definition free_directS2c_post (m9 : mem) (qb : Z) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR rac spd gp tp t0' t1' t2' s0 s1 (wz qb) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc rac) fc None m' (seg_rom rsegs)
    /\ munch [(usp + -80 - 48, usp + -80)] m9 m' /\ wmono rsegs m9 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp.

  Theorem free_directS2c : forall (m9 : word -> option byte) (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xt3 xt4 xt5 xt6 : word) (scr : list byte) (nb fb lb qb : Z),
    mem_inv rsegs m9 -> stk rsegs m9 lo (usp + -80 + -48) ->
    rw_cells rsegs m9 (usp + -80 + -48) (unmap_frame scr s2 (wz (thr + 80)) (wz QINST) (wz qput_recret)) ->
    ro_cells rsegs m9 0xa8b60 [C8 (wz CF)] -> ro_cells rsegs m9 (CF + 144) [C8 (wz 0)] ->
    0 <= qb <= 2^20 ->
    rw_cells rsegs m9 (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
    rw_cells rsegs m9 (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    evt rsegs (free_directS2c_post m9 qb)
        (MS (mkR (wz unmap_resume) (wz (usp + -80 + -48)) gp tp xt0 xt1 xt2 (wz msz) (wz 0) (wz 0) (wz msz) (wz 0) xa3 xa4 xa5 xa6 (wz 215)
                 (wz h) s3 s4 s5 (wz (2^20)) s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (wz munmap_after_pc) fc None m9 (seg_rom rsegs)).
  Proof.
    intros until qb. intros MI9 ST9 UF CGCF KML QBR PFR QC.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR. pose proof (zr_word s2) as S2R; unfold inr64 in S2R.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold kHighMemBeg in *.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (unmap_post_ok gp tp xt0 xt1 xt2 (wz msz) (wz 0) (wz msz) (wz 0) xa3 xa4 xa5 xa6 (wz 215)
                (wz h) s3 s4 s5 (wz (2^20)) s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F fc m9
                (usp + -80) lo scr s2 (wz (thr + 80)) (wz QINST) (wz qput_recret)
                (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m10 : word -> option byte),
                   ms' = MS (mkR (wz qput_recret) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80)) a0' a1' a2' a3' a4' a5' a6' a7'
                                 s2 s3 s4 s5 (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                             F (ret_pc (wz qput_recret)) fc None m10 (seg_rom rsegs)
                   /\ munch [(usp + -80 - 48, usp + -80)] m9 m10 /\ wmono rsegs m9 m10 /\ mem_inv rsegs m10 /\ stk rsegs m10 lo (usp + -80)));
        [exact MI9| exact ST9| clear -LO; lia| clear -LO; lia| clear -LO SPH CV; lia| exact UF| rewrite unsigned_lit by (unfold qput_recret; lia); reflexivity| exact CGCF| exact KML|].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m10 MU10 WM10 MI10 ST10.
      hot_eexists_all. split; [reflexivity|]. exact (conj MU10 (conj WM10 (conj MI10 ST10))). }
    intros ms' PO. (first [ dex16 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m10; dand5 PO as -> MU10 WM10 MI10 ST10 | dand21 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m10 -> MU10 WM10 MI10 ST10 | destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m10 & -> & MU10 & WM10 & MI10 & ST10) ]).
    replace (ret_pc (wz qput_recret)) with (Z_to_bv 64 qput_recret) by (symmetry; apply ret_pc_even; [unfold qput_recret; lia| reflexivity]).
    (* [comment removed for export] *)
    xfer PFR MU10 WM10. xfer QC MU10 WM10.
    eapply (free_cbtail rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo p tsd ctx thr r8 n0 f0 sto D key LO SPH PLO PNB TC DN0 DF0 KL
              _ m10 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s2 s3 s4 s5 nb fb lb qb);
      [exact MI10| exact ST10| exact QBR| faobj| exact PFR| exact QC|].
    intros ST11. apply evt_done. unfold free_directS2c_post.
    hot_eexists_all. split; [reflexivity|].
    split; [exact MU10|]. split; [exact WM10|]. split; [exact MI10| exact ST11].
  Qed.
End FreeDirectCore.

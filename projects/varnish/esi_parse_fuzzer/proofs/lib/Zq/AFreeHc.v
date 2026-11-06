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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw ARt20wx ARtSnjd AFreeH.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
Definition free_cprefix_W (spd : word) (thr p r8 n0 f0 : Z) : list (Z * Z) :=
  [(bv_unsigned spd - 560, bv_unsigned spd); (p + -16, p + -12); (p, p + 8);
   (thr + 2824, thr + 2840); (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (sh p, sh p + r8)].

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

Section FreeHitCore.
Context {Clg : Ceiling}.
  Variables (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo p n b1 tsd ctx thr r8 n0 f0 fr fd sto : Z) (D : list (list Z)) (key : list Z) (old : word) (oldsh : list byte).

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
  Lemma free_cprefix : forall (Q : machine_state -> Prop),
    (forall (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        (* [comment removed for export] *)
        rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
        (* [comment removed for export] *)
        rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
        rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        rw_cells rsegs m' p [C8 (wz fid)] ->
        bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)) ->
        depot_repL AL_pboth rsegs D' n0 f0 m' ->
        munch (free_cprefix_W spd thr p r8 n0 f0) m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (usp - 80) ->
        evt rsegs Q (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                            (wz (thr + 80)) (wz (thr + 208)) (wz sto) (wz (p + -16)) (wz n) a5' a6' a7'
                            (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz enqueue_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz AINST) (wz p) a2 a3 (wz sto) (wz 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz dealloc_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros Q K.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR. pose proof (zr_word rac) as RAR; unfold inr64 in RAR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof FCo as FC'. (first [ dand9 FC' as Fini Fmcs Fgotcf Ffu Fhook Fgotfl Fffs Fqmax Fcmax | destruct FC' as (Fini & Fmcs & Fgotcf & Ffu & Fhook & Fgotfl & Fffs & Fqmax & Fcmax) ]).
    unfold free_cprefix_W, QINST, AINST, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kStackStoreBlockFrames, off_th_unwinding in *.
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    rewrite TPL in *. change (6192088 - 88) with 6192000 in Ctsd.
    assert (IAMR : 0 <= Z.shiftr p 32 < 2^15).
    { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2^32 * 2^15) with (2^47). lia. }
    set (p32 := Z.shiftr p 32) in *. assert (P32E : p32 = Z.shiftr p 32) by reflexivity. clearbody p32.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    rewrite SHF in *.
    pose proof (munch_refl [(usp - 560, usp); (p + -16, p + -12); (p, p + 8); (thr + 2824, thr + 2840); (1600136, 6122152); (n0, n0 + 1048576); (f0, f0 + 8388608); (2 * pq + 2147450880, 2 * pq + 2147450880 + r8)] m) as MU.
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
    eapply (qput_pre_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 727088 (thr + 80) (thr + 208) sto p n b1 (2^28) (2^20) r8 lo oldsh);
      [> try (fside P32E) .. | idtac].
    intros t0e t1e t2e a5e a6e a7e t3e t4e t5e t6e m6 PFR HDR6 SHD6 MU6 WM6 MI6 ST6. unfa.
    rewrite ?unsigned_lit in PFR, MU6, ST6 by lia. rewrite SHF in SHD6, MU6.
    clear HDR5 SHC. xdepot DR5 MU6. kpost MU6 WM6.
    eapply K; unfa; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma free_cptail : forall (Q : machine_state -> Prop) (m6 : word -> option byte)
      (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (xs2 xs3 xs4 xs5 : word) (nb fb lb qb : Z),
    mem_inv rsegs m6 -> stk rsegs m6 lo (usp + -80) ->
    0 <= qb <= 2^20 -> aobj (thr + 80) 32 ->
    rw_cells rsegs m6 (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
    rw_cells rsegs m6 (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    (stk rsegs m6 lo usp ->
       evt rsegs Q (MS (mkR rac spd gp tp t0' t1' t2' s0 s1 (wz qb) a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m6 (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                        a0' a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 xs5 (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz 0x3b60c) fc None m6 (seg_rom rsegs)).
  Proof.
    intros until qb. intros MI6 ST6 QBR C80 PFR QC K.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold QINST, kHighMemBeg in *.
    eapply (qput_tail_nodrain_ok gp tp _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m6 usp 727088 (thr + 80) 0 (2^20) nb fb lb qb lo);
      [> try (fside CV) .. | idtac].
    intros ST7. rewrite Z_to_bv_bv_unsigned. apply K. exact ST7.
  Qed.
End FreeHitCore.

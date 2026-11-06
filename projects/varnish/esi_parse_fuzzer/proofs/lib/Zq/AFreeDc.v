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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw ARt20wx ARtSoqz ARtSnjd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt22wr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt4chi AFreeH AFreeH0 AFreeT AFreeHc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt22wr.ARt2mo1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt4chi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeHc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
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
Definition free_cdtail_W (spd : word) (thr : Z) : list (Z * Z) :=
  [(bv_unsigned spd + -80 - 48, bv_unsigned spd + -80); (QINST + 152, QINST + 156); (QINST + 160, QINST + 192); (thr + 80, thr + 112)].
Definition free_cdtail_WA (spd : word) (thr gl : Z) : list (Z * Z) :=
  [(bv_unsigned spd + -80 - 48, bv_unsigned spd + -80); (QINST + 152, QINST + 156); (QINST + 160, QINST + 192); (thr + 80, thr + 112); (gl, gl + 8)].
Definition free_cdtailR_W := free_cdtail_W.
Definition free_cdtailR_WA := free_cdtail_WA.
(* [comment removed for export] *)
Definition ctail_W (tk : ftail) (spd : word) (thr gl : Z) : list (Z * Z) :=
  match tk with TN => [] | T0 => free_cdtail_W spd thr | TA => free_cdtail_WA spd thr gl end.

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

Section FreeTailCore.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
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
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
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


  Definition free_cdtail0_post (W0 : list (Z * Z)) (m0 m7 : word -> option byte) (nb fb lb qb rl hi gf gl gqb : Z) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR rac spd gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m' (seg_rom rsegs)
    /\ munch (W0 ++ free_cdtail_W spd thr) m0 m' /\ wmono rsegs m0 m'
    /\ munch (free_cdtail_W spd thr) m7 m' /\ wmono rsegs m7 m'
    /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
    /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
    /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
    /\ rw_cells rsegs m' p [C8 (wz fid)]
    /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
    /\ depot_repL AL_pboth rsegs D' n0 f0 m'
    /\ rw_cells rsegs m' (thr + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
    /\ rw_cells rsegs m' (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)]
    /\ rw_cells rsegs m' (QINST + 160) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz (gqb + qb))].

  (* [comment removed for export] *)
  #[using="SEP_f0t SEP_n0t SEP_pt KL STOR DF0 DN0 TC R8 NR PNB PLO PAL SPH LO ctx tsd m Clg"] Lemma free_cdtail0 : forall (W0 : list (Z * Z)) (m0 m7 : word -> option byte)
      (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
      (nb fb lb qb rl hi gf gqb : Z) (gl : Z),
    2^20 < qb < 2^64 -> nb <> 0 -> 0 <= nb < 2^64 -> 0 <= fb < 2^64 -> 0 <= lb < 2^64 ->
    0 <= rl < 256 -> 0 <= hi < 2^15 -> 0 <= gqb -> gqb + qb <= 2^28 ->
    rw_cells rsegs m7 (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m7 (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)] ->
    rw_cells rsegs m7 (QINST + 160) [C8 (wz 0); C8 (wz gf); C8 (wz gl); C8 (wz gqb)] ->
    ro_cells rsegs m7 (QINST + 64) [C8 (wz (2^28))] ->
    rw_cells rsegs m7 (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
    rw_cells rsegs m7 (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
    rw_cells rsegs m7 (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m7 p [C8 (wz fid)] ->
    bytes_at rsegs m7 (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)) ->
    depot_repL AL_pboth rsegs D' n0 f0 m7 ->
    munch W0 m0 m7 -> wmono rsegs m0 m7 -> mem_inv rsegs m7 -> stk rsegs m7 lo (usp + -80) ->
    evt rsegs (free_cdtail0_post W0 m0 m7 nb fb lb qb rl hi gf gl gqb)
        (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                 a0' a1' a2' a3' a4' a5' a6' a7' (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20))
                 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz 0x3b60c) fc None m7 (seg_rom rsegs)).
  Proof. natz_kl_box. try clear MI. try clear ST. try clear SPA. try clear RA2. try clear TPE. try clear PHI. try clear NQ. try clear B1R. try clear B1M. try clear HDR. try clear CTX0. try clear SHC. try clear FCo. try clear PCo. try clear TH0. try clear CT8. try clear TSDL. try clear TST. try clear FRR. try clear FDR. try clear DR. try clear DND. try clear DLEN. try clear DTOT. try clear STO. try clear TRW. try clear KR. try clear SEP_pc. try clear SEP_pn. try clear SEP_pf. try clear SEP_n0c. try clear SEP_f0c. try clear SEP_tc.   (* [comment removed for export] *)
    intros until gqb. intros gl QBR NB0 NBR FBR LBR RLR HIR GQ0 GQM QC LCK QGL QMX PFR TST7 HDR7 CTX7 SHD7 DR7 MU0 WM0 MI7 ST7.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR. pose proof (zr_word rac) as RAR; unfold inr64 in RAR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold off_th_unwinding, QINST, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *. rewrite SHF in SHD7.
    kp MU0.
    pose proof (munch_refl (free_cdtail_W spd thr) m7) as MU. unfold free_cdtail_W, free_cdtail_W, QINST in MU. pose proof (wmono_refl rsegs m7) as WM.
    (* [comment removed for export] *)
    eapply (qput_tail_drain_ok gp tp _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ F fc m7
              usp 727088 (thr + 80) (thr + 208) sto (2^20) nb fb lb qb);
      [> try (fside CV) .. | idtac].
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (qdrain0_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m7
                               727088 (thr + 80) (thr + 208) sto rl hi gf gl gqb (2^28) nb fb lb qb lo)|];
      [> try (fside CV) .. | idtac].
    all: try (fside CV).
    intros ms' PO. destruct_exs PO. (first [ dand8 PO as E MUc WMc MI8 ST8 LCK8 QGL8 QC8 | destruct PO as (E & MUc & WMc & MI8 & ST8 & LCK8 & QGL8 & QC8) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST8 by lia.
    eapply bytes_at_transport in SHD7; [| exact MUc | rewrite repeat_length; cbn [disjoint_from]; kung; lia].
    clear QC LCK QGL. xdepot DR7 MUc. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x3b544)) with (Z_to_bv 64 0x3b544) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m8 end.
    (* [comment removed for export] *)
    eapply (qput_epi_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m8 usp lo);
      [> try (fside CV) .. | idtac].
    intros ST9. rewrite Z_to_bv_bv_unsigned.
    unfold keep in MU0.
    apply evt_done. unfold free_cdtail0_post, free_cdtail_W, off_th_unwinding, QINST. rewrite SHF.
    hot_eexists_all. split; [reflexivity|].
    split. { intros y Hy. apply outside_app in Hy. destruct Hy as [Hy0 HyT]. rewrite (MU y HyT). exact (MU0 y Hy0). }
    split. { exact WM0. }
    split. { exact MU. }
    split. { exact WM. }
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; kcell.
  Qed.

  Definition free_cdtailA_post (W0 : list (Z * Z)) (m0 m7 : word -> option byte) (nb fb lb qb rl hi gn gf gl gqb : Z) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR rac spd gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m' (seg_rom rsegs)
    /\ munch (W0 ++ free_cdtail_WA spd thr gl) m0 m' /\ wmono rsegs m0 m'
    /\ munch (free_cdtail_WA spd thr gl) m7 m' /\ wmono rsegs m7 m'
    /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
    /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
    /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
    /\ rw_cells rsegs m' p [C8 (wz fid)]
    /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
    /\ depot_repL AL_pboth rsegs D' n0 f0 m'
    /\ rw_cells rsegs m' (thr + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
    /\ rw_cells rsegs m' (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)]
    /\ rw_cells rsegs m' (QINST + 160) [C8 (wz (gn + nb)); C8 (wz gf); C8 (wz lb); C8 (wz (gqb + qb))]
    /\ rw_cells rsegs m' gl [C8 (wz fb)].

  (* [comment removed for export] *)
  #[using="SEP_f0t SEP_n0t SEP_pt KL STOR DF0 DN0 TC R8 NR PNB PLO PAL SPH LO ctx tsd m"] Lemma free_cdtailA : forall (W0 : list (Z * Z)) (m0 m7 : word -> option byte)
      (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
      (nb fb lb qb rl hi gf gqb : Z) (gn gl : Z) (glnx : word),
    2^20 < qb < 2^64 -> nb <> 0 -> 0 <= nb < 2^64 -> 0 <= fb < 2^64 -> 0 <= lb < 2^64 ->
    0 <= rl < 256 -> 0 <= hi < 2^15 -> 0 <= gqb -> gqb + qb <= 2^28 ->
    kHighMemBeg <= gl -> gl + 24 <= alloc_ceiling -> (thr + 112 <= gl \/ gl + 8 <= thr + 80) -> gn <> 0 -> 0 <= gn < 2^64 ->
    apart gl 24 (p + -16) (8 * r8 + 16) -> apart gl 24 thr 4096 -> apart gl 24 n0 kDepotNodesBlock -> apart gl 24 f0 kStackStoreBlockBytes ->
    rw_cells rsegs m7 (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m7 (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)] ->
    rw_cells rsegs m7 (QINST + 160) [C8 (wz gn); C8 (wz gf); C8 (wz gl); C8 (wz gqb)] ->
    ro_cells rsegs m7 (QINST + 64) [C8 (wz (2^28))] ->
    rw_cells rsegs m7 gl [C8 glnx] ->
    rw_cells rsegs m7 (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
    rw_cells rsegs m7 (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
    rw_cells rsegs m7 (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m7 p [C8 (wz fid)] ->
    bytes_at rsegs m7 (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)) ->
    depot_repL AL_pboth rsegs D' n0 f0 m7 ->
    munch W0 m0 m7 -> wmono rsegs m0 m7 -> mem_inv rsegs m7 -> stk rsegs m7 lo (usp + -80) ->
    evt rsegs (free_cdtailA_post W0 m0 m7 nb fb lb qb rl hi gn gf gl gqb)
        (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                 a0' a1' a2' a3' a4' a5' a6' a7' (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20))
                 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz 0x3b60c) fc None m7 (seg_rom rsegs)).
  Proof. natz_kl_box. try clear MI. try clear ST. try clear SPA. try clear RA2. try clear TPE. try clear PHI. try clear NQ. try clear B1R. try clear B1M. try clear HDR. try clear CTX0. try clear SHC. try clear FCo. try clear PCo. try clear TH0. try clear CT8. try clear TSDL. try clear TST. try clear FRR. try clear FDR. try clear DR. try clear DND. try clear DLEN. try clear DTOT. try clear STO. try clear TRW. try clear KR. try clear SEP_pc. try clear SEP_pn. try clear SEP_pf. try clear SEP_n0c. try clear SEP_f0c. try clear SEP_tc.   (* [comment removed for export] *)
    intros until gqb. intros gn gl glnx QBR NB0 NBR FBR LBR RLR HIR GQ0 GQM GLL GLH GLC GN0 GNR Agp Agt Agn Agf QC LCK QGL QMX GL PFR TST7 HDR7 CTX7 SHD7 DR7 MU0 WM0 MI7 ST7.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR. pose proof (zr_word rac) as RAR; unfold inr64 in RAR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold off_th_unwinding, QINST, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *. rewrite SHF in SHD7.
    kp MU0.
    pose proof (munch_refl (free_cdtail_WA spd thr gl) m7) as MU. unfold free_cdtail_WA, free_cdtail_WA, QINST in MU. pose proof (wmono_refl rsegs m7) as WM.
    (* [comment removed for export] *)
    eapply (qput_tail_drain_ok gp tp _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ F fc m7
              usp 727088 (thr + 80) (thr + 208) sto (2^20) nb fb lb qb);
      [> try (fside CV) .. | idtac].
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (qdrainA_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m7
                               727088 (thr + 80) (thr + 208) sto rl hi gn gf gl gqb (2^28) nb fb lb qb lo glnx)|];
      [> try (fside CV) .. | idtac].
    all: try (fside CV).
    intros ms' PO. destruct_exs PO. (first [ dand9 PO as E MUc WMc MI8 ST8 LCK8 QGL8 QC8 GL8 | destruct PO as (E & MUc & WMc & MI8 & ST8 & LCK8 & QGL8 & QC8 & GL8) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST8 by lia.
    eapply bytes_at_transport in SHD7; [| exact MUc | rewrite repeat_length; cbn [disjoint_from]; kung; lia].
    clear QC LCK QGL GL. xdepot DR7 MUc. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x3b544)) with (Z_to_bv 64 0x3b544) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m8 end.
    (* [comment removed for export] *)
    eapply (qput_epi_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m8 usp lo);
      [> try (fside CV) .. | idtac].
    intros ST9. rewrite Z_to_bv_bv_unsigned.
    unfold keep in MU0.
    apply evt_done. unfold free_cdtailA_post, free_cdtail_WA, off_th_unwinding, QINST. rewrite SHF.
    hot_eexists_all. split; [reflexivity|].
    split. { intros y Hy. apply outside_app in Hy. destruct Hy as [Hy0 HyT]. rewrite (MU y HyT). exact (MU0 y Hy0). }
    split. { exact WM0. }
    split. { exact MU. }
    split. { exact WM. }
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; kcell.
  Qed.

  (* [comment removed for export] *)
  #[using="SEP_f0t SEP_n0t SEP_pt KL STOR DF0 DN0 TC R8 NR PNB PLO PAL SPH LO ctx tsd m Clg"] Lemma free_cdtailR0 : forall (W0 : list (Z * Z)) (m0 m7 : word -> option byte)
      (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
      (nb fb lb qb rl hi gf gqb : Z) (gl : Z) (qmin : Z) (Q : machine_state -> Prop),
    rl = 0 ->
    2^20 < qb < 2^64 -> nb <> 0 -> 0 <= nb < 2^64 -> 0 <= fb < 2^64 -> 0 <= lb < 2^64 ->
    0 <= rl < 256 -> 0 <= hi < 2^15 -> 0 <= gqb -> 2^28 < gqb + qb < 2^64 ->
    0 <= qmin < 2^64 -> ro_cells rsegs m7 (QINST + 64) [C8 (wz (2^28)); C8 (wz qmin)] ->
    rw_cells rsegs m7 (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m7 (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)] ->
    rw_cells rsegs m7 (QINST + 160) [C8 (wz 0); C8 (wz gf); C8 (wz gl); C8 (wz gqb)] ->
    rw_cells rsegs m7 (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
    rw_cells rsegs m7 (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
    rw_cells rsegs m7 (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m7 p [C8 (wz fid)] ->
    bytes_at rsegs m7 (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)) ->
    depot_repL AL_pboth rsegs D' n0 f0 m7 ->
    munch W0 m0 m7 -> wmono rsegs m0 m7 -> mem_inv rsegs m7 -> stk rsegs m7 lo (usp + -80) ->
    (forall (t0'' t1'' a4'' a5'' a6'' a7'' : word) (m' : word -> option byte),
        rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
        rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
        rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        rw_cells rsegs m' p [C8 (wz fid)] ->
        bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)) ->
        depot_repL AL_pboth rsegs D' n0 f0 m' ->
        rw_cells rsegs m' (thr + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
        rw_cells rsegs m' (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (wz hi)] ->
        rw_cells rsegs m' (QINST + 160) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz (gqb + qb))] ->
        ro_cells rsegs m' (QINST + 64) [C8 (wz (2^28)); C8 (wz qmin)] ->
        munch (W0 ++ free_cdtailR_W spd thr) m0 m' -> wmono rsegs m0 m' ->
        munch (free_cdtailR_W spd thr) m7 m' -> wmono rsegs m7 m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (usp + -80) ->
        evt rsegs Q (MS (mkR (wz 0x3b544) (wz (usp + -80)) gp tp t0'' t1'' t2' (wz QINST) (wz (thr + 80))
                            (wz QINST) (wz qmin) (wz (thr + 208)) (wz sto) a4'' a5'' a6'' a7''
                            (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (wz recycle_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                 a0' a1' a2' a3' a4' a5' a6' a7' (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20))
                 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz 0x3b60c) fc None m7 (seg_rom rsegs)).
  Proof. natz_kl_box. try clear MI. try clear ST. try clear SPA. try clear RA2. try clear TPE. try clear PHI. try clear NQ. try clear B1R. try clear B1M. try clear HDR. try clear CTX0. try clear SHC. try clear FCo. try clear PCo. try clear TH0. try clear CT8. try clear TSDL. try clear TST. try clear FRR. try clear FDR. try clear DR. try clear DND. try clear DLEN. try clear DTOT. try clear STO. try clear TRW. try clear KR. try clear SEP_pc. try clear SEP_pn. try clear SEP_pf. try clear SEP_n0c. try clear SEP_f0c. try clear SEP_tc.   (* [comment removed for export] *)
    intros until gqb. intros gl qmin Q RL0 QBR NB0 NBR FBR LBR RLR HIR GQ0 GQM QMR QMM QC LCK QGL PFR TST7 HDR7 CTX7 SHD7 DR7 MU0 WM0 MI7 ST7 K.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR. pose proof (zr_word rac) as RAR; unfold inr64 in RAR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold off_th_unwinding, QINST, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *. rewrite SHF in SHD7.
    kp MU0.
    pose proof (munch_refl (free_cdtailR_W spd thr) m7) as MU. unfold free_cdtailR_W, free_cdtail_W, QINST in MU. pose proof (wmono_refl rsegs m7) as WM.
    (* [comment removed for export] *)
    eapply (qput_tail_drain_ok gp tp _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ F fc m7
              usp 727088 (thr + 80) (thr + 208) sto (2^20) nb fb lb qb);
      [> try (fside CV) .. | idtac].
    subst rl.
    (* [comment removed for export] *)
    eapply (qdrainR0_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m7
              727088 (thr + 80) (thr + 208) sto hi gf gl gqb (2^28) qmin nb fb lb qb lo);
      [> try (fside CV) .. | idtac].
    all: try (fside CV).
    intros t0c t1c a4c a5c a6c a7c m8 MUc WMc MI8 ST8 LCK8 QGL8 QC8.
    rewrite ?unsigned_lit in MUc, ST8 by lia.
    eapply bytes_at_transport in SHD7; [| exact MUc | rewrite repeat_length; cbn [disjoint_from]; kung; lia].
    clear QC LCK QGL. xdepot DR7 MUc. kpost MUc WMc.
    unfold keep in MU0.
    assert (MUF : munch (W0 ++ free_cdtailR_W spd thr) m0 m8).
    { unfold free_cdtailR_W, free_cdtail_W, QINST. intros y Hy. apply outside_app in Hy. destruct Hy as [Hy0 HyT]. rewrite (MU y HyT). exact (MU0 y Hy0). }
    clear MU0. unfold recycle_entry in *.
    assert (MUT : munch (free_cdtailR_W spd thr) m7 m8) by (unfold free_cdtailR_W, free_cdtail_W, QINST; exact MU).
    clear MU.
    eapply K.
    all: first [kcell | exact MUF | exact WM0 | exact MUT | exact WM | rewrite SHF; kcell | rewrite ?unsigned_lit by lia; first [kcell | eassumption]].
  Qed.

  (* [comment removed for export] *)
  #[using="SEP_f0t SEP_n0t SEP_pt KL STOR DF0 DN0 TC R8 NR PNB PLO PAL SPH LO ctx tsd m"] Lemma free_cdtailRA : forall (W0 : list (Z * Z)) (m0 m7 : word -> option byte)
      (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
      (nb fb lb qb rl hi gf gqb : Z) (gn gl : Z) (glnx : word) (qmin : Z) (Q : machine_state -> Prop),
    rl = 0 ->
    2^20 < qb < 2^64 -> nb <> 0 -> 0 <= nb < 2^64 -> 0 <= fb < 2^64 -> 0 <= lb < 2^64 ->
    0 <= rl < 256 -> 0 <= hi < 2^15 -> 0 <= gqb -> 2^28 < gqb + qb < 2^64 ->
    kHighMemBeg <= gl -> gl + 24 <= alloc_ceiling -> (thr + 112 <= gl \/ gl + 8 <= thr + 80) -> gn <> 0 -> 0 <= gn -> gn + nb < 2^64 ->
    apart gl 24 (p + -16) (8 * r8 + 16) -> apart gl 24 thr 4096 -> apart gl 24 n0 kDepotNodesBlock -> apart gl 24 f0 kStackStoreBlockBytes ->
    0 <= qmin < 2^64 -> ro_cells rsegs m7 (QINST + 64) [C8 (wz (2^28)); C8 (wz qmin)] ->
    rw_cells rsegs m7 (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m7 (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)] ->
    rw_cells rsegs m7 (QINST + 160) [C8 (wz gn); C8 (wz gf); C8 (wz gl); C8 (wz gqb)] ->
    rw_cells rsegs m7 gl [C8 glnx] ->
    rw_cells rsegs m7 (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
    rw_cells rsegs m7 (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
    rw_cells rsegs m7 (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m7 p [C8 (wz fid)] ->
    bytes_at rsegs m7 (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)) ->
    depot_repL AL_pboth rsegs D' n0 f0 m7 ->
    munch W0 m0 m7 -> wmono rsegs m0 m7 -> mem_inv rsegs m7 -> stk rsegs m7 lo (usp + -80) ->
    (forall (t0'' t1'' a4'' a5'' a6'' a7'' : word) (m' : word -> option byte),
        rw_cells rsegs m' (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
        rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
        rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        rw_cells rsegs m' p [C8 (wz fid)] ->
        bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)) ->
        depot_repL AL_pboth rsegs D' n0 f0 m' ->
        rw_cells rsegs m' (thr + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
        rw_cells rsegs m' (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (wz hi)] ->
        rw_cells rsegs m' (QINST + 160) [C8 (wz (gn + nb)); C8 (wz gf); C8 (wz lb); C8 (wz (gqb + qb))] ->
        rw_cells rsegs m' gl [C8 (wz fb)] ->
        ro_cells rsegs m' (QINST + 64) [C8 (wz (2^28)); C8 (wz qmin)] ->
        munch (W0 ++ free_cdtailR_WA spd thr gl) m0 m' -> wmono rsegs m0 m' ->
        munch (free_cdtailR_WA spd thr gl) m7 m' -> wmono rsegs m7 m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (usp + -80) ->
        evt rsegs Q (MS (mkR (wz 0x3b544) (wz (usp + -80)) gp tp t0'' t1'' t2' (wz QINST) (wz (thr + 80))
                            (wz QINST) (wz qmin) (wz (thr + 208)) (wz sto) a4'' a5'' a6'' a7''
                            (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (wz recycle_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz 0x3b60c) (wz (usp + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                 a0' a1' a2' a3' a4' a5' a6' a7' (wz n) (wz sto) (wz (thr + 208)) (wz (p + -16)) (wz (2^20))
                 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz 0x3b60c) fc None m7 (seg_rom rsegs)).
  Proof. natz_kl_box. try clear MI. try clear ST. try clear SPA. try clear RA2. try clear TPE. try clear PHI. try clear NQ. try clear B1R. try clear B1M. try clear HDR. try clear CTX0. try clear SHC. try clear FCo. try clear PCo. try clear TH0. try clear CT8. try clear TSDL. try clear TST. try clear FRR. try clear FDR. try clear DR. try clear DND. try clear DLEN. try clear DTOT. try clear STO. try clear TRW. try clear KR. try clear SEP_pc. try clear SEP_pn. try clear SEP_pf. try clear SEP_n0c. try clear SEP_f0c. try clear SEP_tc.   (* [comment removed for export] *)
    intros until gqb. intros gn gl glnx qmin Q RL0 QBR NB0 NBR FBR LBR RLR HIR GQ0 GQM GLL GLH GLC GN0 GNR GNB Agp Agt Agn Agf QMR QMM QC LCK QGL GL PFR TST7 HDR7 CTX7 SHD7 DR7 MU0 WM0 MI7 ST7 K.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR. pose proof (zr_word rac) as RAR; unfold inr64 in RAR.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold off_th_unwinding, QINST, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes in *. rewrite SHF in SHD7.
    kp MU0.
    pose proof (munch_refl (free_cdtailR_WA spd thr gl) m7) as MU. unfold free_cdtailR_WA, free_cdtail_WA, QINST in MU. pose proof (wmono_refl rsegs m7) as WM.
    (* [comment removed for export] *)
    eapply (qput_tail_drain_ok gp tp _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ F fc m7
              usp 727088 (thr + 80) (thr + 208) sto (2^20) nb fb lb qb);
      [> try (fside CV) .. | idtac].
    subst rl.
    (* [comment removed for export] *)
    eapply (qdrainRA_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m7
              727088 (thr + 80) (thr + 208) sto hi gn gf gl gqb (2^28) qmin nb fb lb qb lo glnx);
      [> try (fside CV) .. | idtac].
    all: try (fside CV).
    intros t0c t1c a4c a5c a6c a7c m8 MUc WMc MI8 ST8 LCK8 QGL8 QC8 GL8.
    rewrite ?unsigned_lit in MUc, ST8 by lia.
    eapply bytes_at_transport in SHD7; [| exact MUc | rewrite repeat_length; cbn [disjoint_from]; kung; lia].
    clear QC LCK QGL GL. xdepot DR7 MUc. kpost MUc WMc.
    unfold keep in MU0.
    assert (MUF : munch (W0 ++ free_cdtailR_WA spd thr gl) m0 m8).
    { unfold free_cdtailR_WA, free_cdtail_WA, QINST. intros y Hy. apply outside_app in Hy. destruct Hy as [Hy0 HyT]. rewrite (MU y HyT). exact (MU0 y Hy0). }
    clear MU0. unfold recycle_entry in *.
    assert (MUT : munch (free_cdtailR_WA spd thr gl) m7 m8) by (unfold free_cdtailR_WA, free_cdtail_WA, QINST; exact MU).
    clear MU.
    eapply K.
    all: first [kcell | exact MUF | exact WM0 | exact MUT | exact WM | rewrite SHF; kcell | rewrite ?unsigned_lit by lia; first [kcell | eassumption]].
  Qed.

  (* [comment removed for export] *)
  #[using="KL PNB SPH LO key D p Clg"] Lemma free_crtail : forall (Q : machine_state -> Prop) (m9 : word -> option byte)
      (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    mem_inv rsegs m9 -> stk rsegs m9 lo (usp + -80) ->
    rw_cells rsegs m9 (usp + -80) [C8 (wz (thr + 208)); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac] ->
    (stk rsegs m9 lo usp ->
       evt rsegs Q (MS (mkR rac spd gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m9 (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR xra (wz (usp + -80)) gp tp t0' t1' t2' xs0 xs1
                        a0' a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz 0x3b544) fc None m9 (seg_rom rsegs)).
  Proof. natz_kl_box. try clear MI. try clear ST. try clear SPA. try clear RA2. try clear TPE. try clear PAL. try clear PLO. try clear PHI. try clear NR. try clear NQ. try clear R8. try clear B1R. try clear B1M. try clear HDR. try clear CTX0. try clear SHC. try clear FCo. try clear PCo. try clear TC. try clear TH0. try clear CT8. try clear TSDL. try clear TST. try clear FRR. try clear FDR. try clear DR. try clear DND. try clear DLEN. try clear DTOT. try clear DN0. try clear DF0. try clear STO. try clear TRW. try clear STOR. try clear KR. try clear SEP_pc. try clear SEP_pt. try clear SEP_pn. try clear SEP_pf. try clear SEP_n0t. try clear SEP_f0t. try clear SEP_n0c. try clear SEP_f0c. try clear SEP_tc.   (* [comment removed for export] *)
    clear fid D'. intros until t6'. intros MI9 ST9 PFR K.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    eapply (qput_epi_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m9 usp lo);
      [> try (fside CV) .. | idtac].
    intros ST10. rewrite Z_to_bv_bv_unsigned. apply K. exact ST10.
  Qed.
End FreeTailCore.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].

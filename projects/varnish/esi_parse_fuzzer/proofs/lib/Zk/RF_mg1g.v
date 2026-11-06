(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mremap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes SysStep Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import F_sy88u F_mm4hw MRep MRepAux MProg Mrems6x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@GOT]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
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
Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eff_mem (m : word -> option byte) (eff : SyscallEffect) : word -> option byte :=
  apply_writes (apply_copies m (apply_zeros (apply_unmaps m (eff_unmaps eff)) (eff_zeros eff)) (eff_copies eff)) (eff_writes eff).

Lemma nret_MSsvc_eff : forall R F pc x8 fc rv m ro eff,
  nret (MSsvc R F pc x8 fc rv m ro) eff = MS (bvmap_set 10 (eff_ret eff) R) F (pc + Z_to_bv 64 4) fc rv (eff_mem m eff) ro.
Proof. intros. destruct eff. reflexivity. Qed.

(* [comment removed for export] *)
Definition copies_cover (cs : list MemCopy) (a : word) : bool :=
  existsb (fun c => Z.leb (bv_unsigned (copy_dst c)) (bv_unsigned a)
                    && Z.ltb (bv_unsigned a) (bv_unsigned (copy_dst c) + bv_unsigned (copy_len c)))%Z cs.
Definition eff_cover (eff : SyscallEffect) (a : word) : bool :=
  zeros_cover (eff_unmaps eff) a || zeros_cover (eff_zeros eff) a || copies_cover (eff_copies eff) a.

Lemma apply_zeros_outside m zs x : zeros_cover zs x = false -> apply_zeros m zs x = m x.
Proof. intros H. destruct zs; cbn [apply_zeros]; [reflexivity|]. rewrite H. reflexivity. Qed.
Lemma apply_unmaps_outside m us x : zeros_cover us x = false -> apply_unmaps m us x = m x.
Proof. intros H. destruct us; cbn [apply_unmaps]; [reflexivity|]. rewrite H. reflexivity. Qed.
Lemma apply_copies_outside before : forall cs mem x, copies_cover cs x = false -> apply_copies before mem cs x = mem x.
Proof.
  induction cs as [|c cs IH]; intros mem x H; cbn [apply_copies]; [reflexivity|].
  cbn [copies_cover existsb] in H. apply orb_false_iff in H as [H1 H2].
  rewrite IH by exact H2. unfold apply_copy. rewrite H1. reflexivity.
Qed.
Lemma eff_mem_outside m eff x : eff_writes eff = [] -> eff_cover eff x = false -> eff_mem m eff x = m x.
Proof.
  intros W H. unfold eff_mem. rewrite W. cbn [apply_writes]. unfold eff_cover in H.
  apply orb_false_iff in H as [H H3]. apply orb_false_iff in H as [H1 H2].
  rewrite apply_copies_outside by exact H3. rewrite apply_zeros_outside by exact H2. apply apply_unmaps_outside. exact H1.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_agree m m' A cs :
  rw_cells rsegs m A cs -> (forall x, (A <= bv_unsigned x < A + Z.of_nat (cells_size cs))%Z -> m' x = m x) -> rw_cells rsegs m' A cs.
Proof.
  intros [[Hwf (H0 & H1 & Hb)] (W0 & W1 & Hw)] AG.
  pose proof (cells_bytes_length cs Hwf) as LEN.
  split; [split; [exact Hwf|]|].
  - split; [lia|]. split; [lia|]. intros i Hi. unfold mrd. rewrite AG; [apply Hb; exact Hi|]. rewrite wa_unsigned by lia. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite AG; [apply Hw; exact Hi|]. rewrite wa_unsigned by lia. lia.
Qed.
Lemma stk_agree m m' lo hi :
  stk rsegs m lo hi -> (forall x, (lo <= bv_unsigned x < hi)%Z -> m' x = m x) -> stk rsegs m' lo hi.
Proof.
  intros (H0 & H1 & H) AG. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw Hr]. unfold wview, mrd in *. rewrite AG by (rewrite wa_unsigned by lia; lia). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mremap_raw (old old_len new_len : Z) (r : word) (m : word -> option byte) : word -> option byte :=
  eff_mem m (mremap_expected old old_len new_len r).

Lemma mremap_expected_writes old old_len new_len r : eff_writes (mremap_expected old old_len new_len r) = [].
Proof.
  unfold mremap_expected, mremap_inplace_effect, mremap_move_effect.
  destruct (mrlen old_len =? mrlen new_len)%Z; [reflexivity|]. destruct (bv_eqb r (mw old)); [|reflexivity].
  destruct (mrlen new_len <? mrlen old_len)%Z; reflexivity.
Qed.

Lemma zeros_cover1 (b n x : word) : zeros_cover [(b, n)] x = true -> (bv_unsigned b <= bv_unsigned x < bv_unsigned b + bv_unsigned n)%Z.
Proof. unfold zeros_cover. cbn [existsb fst snd]. rewrite orb_false_r. intros H. apply andb_prop in H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia. Qed.
Lemma copies_cover1 c (x : word) : copies_cover [c] x = true ->
  (bv_unsigned (copy_dst c) <= bv_unsigned x < bv_unsigned (copy_dst c) + bv_unsigned (copy_len c))%Z.
Proof. unfold copies_cover. cbn [existsb]. rewrite orb_false_r. intros H. apply andb_prop in H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia. Qed.

Lemma mrlen_nonneg len : (0 <= mrlen len)%Z.
Proof. unfold mrlen. apply Mmap.page_round_up_Z_nonneg. pose proof (bv_unsigned_in_range _ (mw len)). lia. Qed.

(* [comment removed for export] *)
Lemma mremap_expected_cover old old_len new_len (r x : word) :
  (0 <= old)%Z -> (old + mrlen old_len < 2^64)%Z ->
  (bv_unsigned r + mspan old_len new_len < 2^64)%Z ->
  eff_cover (mremap_expected old old_len new_len r) x = true ->
  (old <= bv_unsigned x < old + mrlen old_len)%Z
  \/ (bv_unsigned r <= bv_unsigned x < bv_unsigned r + mspan old_len new_len)%Z.
Proof.
  intros OLD0 OLDHI RHI C.
  pose proof (bv_unsigned_in_range _ r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  pose proof (mrlen_nonneg old_len) as OZ0. pose proof (mrlen_nonneg new_len) as NZ0.
  unfold mspan in *. set (oZ := mrlen old_len) in *. set (nZ := mrlen new_len) in *.
  assert (Uold : bv_unsigned (mw old) = old) by (unfold mw; apply unsigned_lit; lia).
  unfold mremap_expected, eff_cover in C. fold oZ nZ in C.
  destruct (oZ =? nZ)%Z eqn:E; [cbn in C; discriminate|]. apply Z.eqb_neq in E.
  destruct (bv_eqb r (mw old)) eqn:ER.
  - (* [comment removed for export] *) apply bv_eqb_true_iff in ER. subst r. rewrite Uold in *. unfold mremap_inplace_effect in C.
    destruct (nZ <? oZ)%Z eqn:L; [apply Z.ltb_lt in L| apply Z.ltb_ge in L]; cbn [eff_unmaps eff_zeros eff_copies] in C.
    + rewrite ?orb_false_r in C. apply zeros_cover1 in C. unfold mw, mwlen in C. fold nZ in C.
      rewrite lit_add_lit, !unsigned_lit in C by lia. left. lia.
    + unfold mremap_tail in C. change (zeros_cover [] x) with false in C. change (copies_cover [] x) with false in C.
      rewrite orb_false_r in C. cbn [orb] in C.
      destruct (oZ <? nZ)%Z eqn:L2; [apply Z.ltb_lt in L2| cbn in C; discriminate].
      apply zeros_cover1 in C. unfold mw, mwlen in C. fold oZ in C.
      rewrite lit_add_lit, !unsigned_lit in C by lia. right. lia.
  - (* [comment removed for export] *) unfold mremap_move_effect in C. cbn [eff_unmaps eff_zeros eff_copies] in C.
    apply orb_prop in C as [C|C]; [apply orb_prop in C as [C|C]|].
    + apply zeros_cover1 in C. unfold mw, mwlen in C. fold oZ in C. rewrite !unsigned_lit in C by lia. left. lia.
    + unfold mremap_tail in C. destruct (oZ <? nZ)%Z eqn:L2; [apply Z.ltb_lt in L2| cbn in C; discriminate].
      apply zeros_cover1 in C. unfold mwlen in C. fold oZ in C.
      assert (UA : bv_unsigned (r + Z_to_bv 64 oZ) = (bv_unsigned r + oZ)%Z).
      { rewrite <- (definitions.Z_to_bv_bv_unsigned 64 r) at 1. rewrite lit_add_lit. apply unsigned_lit. lia. }
      rewrite UA, !unsigned_lit in C by lia. right. lia.
    + apply copies_cover1 in C. cbn [copy_dst copy_len] in C. unfold mwlen in C. fold oZ in C. rewrite unsigned_lit in C by lia. right. lia.
Qed.

Section CEIL.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)

Definition rmremap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (avoid : list (Z * Z)) (old old_len new_len : Z) (errv : word) (lo : Z) (m : word -> option byte) (z : Z) : machine_state -> Prop :=
  fun ms' =>
    (exists e, z = neg_errno e /\ (1 <= e <= 4095)%Z /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp)
        /\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)])
    \/ (exists r : word, errno_of r = None /\ z = bv_unsigned r /\ mremap_dst_ok avoid old_len new_len r = true
        /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mremap_raw old old_len new_len r m2) (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2
        /\ wmono rsegs m m2 /\ mem_inv rsegs m2
        /\ stk rsegs (mremap_raw old old_len new_len r m2) lo (bv_unsigned sp)
        /\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]).

Lemma rmremap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (avoid : list (Z * Z)) (old old_len new_len : Z) (errv g : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  rw_cells rsegs m GOT_SSP [C8 (Z_to_bv 64 SSP_GUARD)] -> rw_cells rsegs m SSP_GUARD [C8 g] ->
  a0 = Z_to_bv 64 old -> a1 = Z_to_bv 64 old_len -> a2 = Z_to_bv 64 new_len -> a3 = Z_to_bv 64 1 ->
  (0 <= new_len < 2^62)%Z -> (0 <= old < 2^64)%Z -> (0 <= old_len < 2^64)%Z ->
  (lo <= bv_unsigned sp - 112)%Z -> (alloc_ceiling <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (errno_addr tp + 4 <= SSP_GUARD \/ SSP_GUARD + 8 <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  (* [comment removed for export] *)
  (old + mrlen old_len <= alloc_ceiling)%Z ->
  (old + mrlen old_len <= SSP_GUARD \/ SSP_GUARD + 8 <= old)%Z ->
  (exists iv, In iv avoid /\ (fst iv <= SSP_GUARD)%Z /\ (SSP_GUARD + 8 <= snd iv)%Z) ->
  impl rsegs (at_node rsegs) (enode (NMremap old old_len new_len 1) (dec_mremap avoid old old_len new_len))
       (epost (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc avoid old old_len new_len errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 mremap_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR MI GOT GRD -> -> -> -> NL OLD OLDL LO CEIL SEP1 SEP2 TP OC OG (giv & GIN & GLO & GHI).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  unfold mremap_entry, GOT_SSP, SSP_GUARD in *. apply impl_enode.
  carve_frame 96%nat ST.
  do 7 step.
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  step. step. step. step.
  (* [comment removed for export] *)
  step. step. step. step.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. } clear K1.
  step. step_ecall.
  split. { at_node_solve. }
  intros rsp z Hdec.
  destruct (dec_mremap_expected _ _ _ _ _ _ Hdec) as [(e & He & Ersp & ->)|(Hn & Ersp & -> & DOK)]; clear Hdec.
  - (* [comment removed for export] *)
    clear MU1. destruct (errno_of_Some _ _ He) as [Er RE]. rewrite Ersp, Er. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. }
    step. step. step. step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    apply evt_done. left. exists e. split; [reflexivity|]. split; [lia|].
    do 15 eexists. split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
  - (* [comment removed for export] *)
    clear MU. set (r := eff_ret rsp) in *.
    assert (RR : eff_ret (mremap_expected old old_len new_len r) = r) by (rewrite <- Ersp; reflexivity).
    clearbody r. rewrite Ersp. clear Ersp rsp.
    assert (RB : (bv_unsigned r < 2^64 - 4095)%Z).
    { unfold errno_of in Hn. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [discriminate| lia]. }
    pose proof (bv_unsigned_in_range _ r) as RBR. change (bv_modulus 64) with (2^64)%Z in RBR.
    rewrite nret_MSsvc_eff, RR, ?mkR_set_a0. simp_regs.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
    end.
    fold (mremap_raw old old_len new_len r m0).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m' := mm) in * end.
    pose proof (mremap_dst_ok_sound _ _ _ _ DOK) as (DA & DP & DC & DAV). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    pose proof (DAV giv GIN) as DG. pose proof (mrlen_nonneg old_len) as OZ0. pose proof (mrlen_nonneg new_len) as NZ0.
    assert (AG : forall x, (alloc_ceiling <= bv_unsigned x \/ (402376 <= bv_unsigned x < 402384))%Z -> m' x = m0 x).
    { intros x Hx. unfold m', mremap_raw. apply eff_mem_outside; [apply mremap_expected_writes|].
      destruct (eff_cover (mremap_expected old old_len new_len r) x) eqn:C; [| reflexivity].
      exfalso. destruct (mremap_expected_cover old old_len new_len r x ltac:(lia) ltac:(lia) ltac:(unfold mspan in *; lia) C); unfold mspan in *; lia. }
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
    assert (FR' : rw_cells rsegs m' (bv_unsigned sp + -96)
              [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk)))))));
               C8 g; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; C8 a4; C8 a5; C8 a6; C8 a7]).
    { apply (rw_cells_agree _ _ _ _ FR). cbn [cells_size csize Nat.add]. intros x Hx. apply AG. lia. }
    assert (GRD' : rw_cells rsegs m' 402376 [C8 g]).
    { apply (rw_cells_agree _ _ _ _ GRD). cbn [cells_size csize Nat.add]. intros x Hx. apply AG. lia. }
    assert (ST' : stk rsegs m' lo (bv_unsigned sp + -96)).
    { apply (stk_agree _ _ _ _ ST). intros x Hx. apply AG. lia. }
    clear FR GRD ST. assert (Em' : m' = mremap_raw old old_len new_len r m0) by reflexivity. clearbody m'.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
    step.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K4; zify_cond K4. { exfalso. apply K4. reflexivity. }
    step. step. step. step. step. step. step. step. step. release_frame FR' ST' (bv_unsigned sp).
    apply evt_done. right. exists r. split; [exact Hn|]. split; [reflexivity|]. split; [exact DOK|]. subst m'.
    do 15 eexists. split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

End CEIL.

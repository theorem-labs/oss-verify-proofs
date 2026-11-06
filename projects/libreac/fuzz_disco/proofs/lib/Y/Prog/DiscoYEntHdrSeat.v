(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 365 of its 397 lines of code are new or changed and 37 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntLatch.v, with its module paths and module names changed; 305 of its 402 lines of code are new or changed and 300 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntHdrLib DiscoYEntHdrSem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac hd_ro HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
    ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS;
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end
end.

Lemma hd_A_range : forall S, 0 <= S - MFRAME ->
  S - MFRAME - 31 <= 32 * ((S - MFRAME) / 32) <= S - MFRAME.
Proof.
intros S Hs. pose proof (Z.div_mod (S - MFRAME) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (S - MFRAME) 32 ltac:(lia)) as Hmp. lia.
Qed.

Lemma hd_rng64 : forall v, 0 <= v < 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_N 8).
Proof. intros v Hv. exact Hv. Qed.

Lemma hd_dnot_rng : forall F o, 0 <= F -> F + 4096 <= 0x7fffff800000 -> 0 <= o <= 4096 ->
  0 <= dnot (F + o) < 2 ^ 64.
Proof. intros F o HF HC Ho. unfold dnot. lia. Qed.

Lemma hd_xregb_eqs : forall ss, hd_xregb ss = true ->
  sr_get (ss_regs ss) 2 = SOff 60 0 /\ sr_get (ss_regs ss) 3 = SOff 3 0 /\ sr_get (ss_regs ss) 4 = SOff 4 0 /\
  sr_get (ss_regs ss) 8 = SOff 2 0 /\ sr_get (ss_regs ss) 9 = SOff 60 0 /\ sr_get (ss_regs ss) 19 = SOff 32 0 /\
  sr_get (ss_regs ss) 27 = SOff 529 0.
Proof.
intros ss HX. unfold hd_xregb, hd_xregs in HX. cbn [forallb fst snd] in HX.
rewrite !andb_true_iff in HX.
destruct HX as (X2 & X3 & X4 & X8 & X9 & X19 & X27 & _).
apply sv_eqb_eq in X2. apply sv_eqb_eq in X3. apply sv_eqb_eq in X4. apply sv_eqb_eq in X8.
apply sv_eqb_eq in X9. apply sv_eqb_eq in X19. apply sv_eqb_eq in X27.
exact (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X19 X27)))))).
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma hd_mrestrict_ext : forall (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall x, mrestrict H m' x = mrestrict H m x.
Proof. intros H m m' HM x. unfold mrestrict. rewrite HM. reflexivity. Qed.

Lemma hd_mbyte_ext : forall segs (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof. intros segs H m m' HM a. unfold mbyte, mrestrict. rewrite HM. reflexivity. Qed.

Lemma hd_aview_ext : forall segs (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' HM a. unfold aview. rewrite (hd_mbyte_ext segs H m m' HM). reflexivity. Qed.

Lemma hd_rok_ext : forall segs E (m m' : word -> option byte) r,
  (forall x, m' x = m x) -> region_ok segs E m r -> region_ok segs E m' r.
Proof.
intros segs E m m' r HM HR. unfold region_ok in *. cbv zeta in *.
destruct HR as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. apply (writable_at_grows segs m m'); [intros x Hx; rewrite HM; exact Hx | exact (H3 o Ho)].
- refine (Forall_impl _ _ H4). intros c Hc i Hi. destruct (Hc i Hi) as (b & Hb & Hm).
  exists b. split; [exact Hb|]. unfold mbyte in *. rewrite HM. exact Hm.
Qed.

Lemma hd_frame_ext : forall cx h shf (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_frame cx h shf W m -> d_frame cx h shf W m'.
Proof.
intros cx h shf W m m' HM (E & HE & HR & HFL & V1 & V2 & V3 & V4 & V5 & V6 & V7).
pose proof (hd_mbyte_ext SEGS (w_H W) m m' HM) as MB.
assert (VM : forall a n v, val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W m') a n v)
  by (intros a n v Hv j Hj; rewrite MB; exact (Hv j Hj)).
exists E. split; [exact HE|]. split.
- refine (Forall_impl _ _ HR). intros r Hr. exact (hd_rok_ext SEGS E _ _ r (hd_mrestrict_ext (w_H W) m m' HM) Hr).
- split.
  + rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W) m')); [exact HFL|].
    intros j _. apply hd_aview_ext. exact HM.
  + exact (conj (VM _ _ _ V1) (conj (VM _ _ _ V2) (conj (VM _ _ _ V3) (conj (VM _ _ _ V4)
      (conj (VM _ _ _ V5) (conj (VM _ _ _ V6) (VM _ _ _ V7))))))).
Qed.

Lemma hd_shadow_ext : forall cx shf (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_shadow cx shf W m -> d_shadow cx shf W m'.
Proof. intros cx shf W m m' HM Hs j Hj. rewrite (hd_aview_ext SEGS (w_H W) m m' HM). exact (Hs j Hj). Qed.

Lemma hd_frame_x_of : forall cx h shf (W : world SEGS) m, d_frame cx h shf W m -> d_frame_x cx W m.
Proof.
intros cx h shf W m (E & HE & HR & Hfl & _). exists E. split; [exact HE|]. split; [|exact Hfl].
unfold d_regions in HR. unfold d_regions_x.
apply Forall_inv_tail in HR as HR1. apply Forall_inv in HR as R1.
apply Forall_inv_tail in HR1 as HR2. apply Forall_inv in HR1 as R2.
apply Forall_inv_tail in HR2 as HR3. apply Forall_inv in HR2 as R3.
apply Forall_inv in HR3 as R4.
destruct R2 as (A1 & A2 & A3 & A4). destruct R3 as (C1 & C2 & C3 & _). destruct R4 as (D1 & D2 & D3 & _).
constructor; [exact R1|]. constructor.
- refine (conj A1 (conj A2 (conj A3 _))).
  constructor; [apply (proj1 (Forall_forall _ _) A4); cbn [YP09.r_chunks]; unfold dslot_chunks; cbn [map fst snd In];
    repeat (first [left; reflexivity | right])|].
  constructor; [apply (proj1 (Forall_forall _ _) A4); cbn [YP09.r_chunks]; unfold dslot_chunks; cbn [map fst snd In];
    repeat (first [left; reflexivity | right])|].
  constructor.
- constructor; [exact (conj C1 (conj C2 (conj C3 (Forall_nil _))))|].
  constructor; [exact (conj D1 (conj D2 (conj D3 (Forall_nil _))))|].
  constructor.
Qed.

Lemma hd_ex : forall cx E h i n now regs (j q : nat), q = (AT_X + j)%nat -> (j <? 38)%nat = true ->
  ew (d_env cx E (hd_vals cx h i n now regs)) q = nth j (hd_vals cx h i n now regs) (Z_to_bv 64 0).
Proof.
intros cx E h i n now regs j q -> Hj. apply hd_env_x.
apply Nat.ltb_lt in Hj. assert (L : length (hd_vals cx h i n now regs) = 38%nat) by reflexivity.
rewrite L. exact Hj.
Qed.

Lemma hd_dx : forall cx E h i n now regs (j q : nat), q = (AT_X + j)%nat -> (j <? 38)%nat = true ->
  sv_denot (d_env cx E (hd_vals cx h i n now regs)) (SOff q 0) = nth j (hd_vals cx h i n now regs) (Z_to_bv 64 0).
Proof.
intros cx E h i n now regs j q Hq Hj. rewrite sv_denot_SOff0. exact (hd_ex cx E h i n now regs j q Hq Hj).
Qed.

Lemma hd_den : forall cx E vals, d_E cx E ->
  sv_denot (d_env cx E vals) (SOff 60 0) = w64 (d_A cx) /\
  sv_denot (d_env cx E vals) (SOff 2 0) = w64 (d_S cx) /\
  sv_denot (d_env cx E vals) (SOff 3 0) = getr (c_regs cx) 3 /\
  sv_denot (d_env cx E vals) (SOff 4 0) = getr (c_regs cx) 4 /\
  sv_denot (d_env cx E vals) (SOff 32 0) = w64 SHADOW_OFF /\
  sv_denot (d_env cx E vals) (SOff 529 0) = w64 (shadow_addr (d_FB cx)).
Proof.
intros cx E vals (EE & E32 & _ & E60 & _ & E529). unfold AT_A, AT_SH in E60, E529.
rewrite !sv_denot_SOff0.
rewrite !hd_env_old by (unfold AT_FL; lia).
split; [exact E60|].
split; [rewrite (EE 2%nat 2%bv eq_refl); unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned|].
split; [exact (EE 3%nat 3%bv eq_refl)|]. split; [exact (EE 4%nat 4%bv eq_refl)|].
split; [exact E32 | exact E529].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MT_TRIV : MT = ameter_triv.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BKEEP : d_body_keep_stmt B.

Lemma hd_body_ext : forall cx h n shf ly3 S3 (W3 : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_body B cx h n [] shf ly3 S3 W3 m -> d_body B cx h n [] shf ly3 S3 W3 m'.
Proof.
intros cx h n shf ly3 S3 W3 m m' HM HBD.
pose proof HBD as (T & G & Lk & H & HFRM & HSHD & _ & _ & (Rn & _) & _).
apply (BKEEP cx h n n shf ly3 S3 W3 m m' (d_S cx) (d_S cx) HBD).
- unfold LLVMF_STK. lia.
- lia.
- intros a _ _. apply hd_aview_ext. exact HM.
- intros a _ (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite HM. exact Hb.
- exact (hd_frame_ext cx h shf W3 m m' HM HFRM).
- exact (hd_shadow_ext cx shf W3 m m' HM HSHD).
- lia.
Qed.

Lemma hd_body_x_of : forall cx h n shf ly S (W : world SEGS) m,
  d_body B cx h n [] shf ly S W m -> d_body_x B cx h ly S W m.
Proof.
intros cx h n shf ly S W m (T & G & Lk & H & Hfr & _ & _ & Hbl & _ & Himg & _).
pose proof Hfr as (E & _ & _ & _ & V1 & _).
exact (conj (hd_frame_x_of cx h shf W m Hfr) (conj Hbl (conj Himg V1))).
Qed.

Lemma hd_exit_weaken : forall cx h W c,
  d_at B MT XM_LIB RLO RHI tfib_K cx EXIT_OFF (EV_HEAD MAX_OPS) (ACC_HEAD MT MAX_OPS)
    (fun regs ly3 S3 W3 mem3 md3 => exists n, d_rX B cx h regs /\ d_body B cx h n [] dsh_loop ly3 S3 W3 mem3) W c ->
  exit_pre B MT XM_LIB RLO RHI tfib_K cx h W c.
Proof.
intros cx h W c (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hfm & Hb & HJ & Hfr & Hk & Hn & Hmo & Hacc & (n & HX & HB)).
exists fq, ly3, S3, regs, mem3, md3, k, acc.
exact (conj Hc (conj Hfm (conj Hb (conj HJ (conj Hfr (conj Hk (conj Hn (conj Hmo (conj Hacc
  (conj HX (hd_body_x_of cx h n dsh_loop ly3 S3 W mem3 HB))))))))))).
Qed.

Lemma hd_mono : forall cx pc kmax accmax
  (P P' : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop) W c,
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P W c ->
  (forall regs ly S W' mem md, P regs ly S W' mem md -> P' regs ly S W' mem md) ->
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P' W c.
Proof.
intros cx pc kmax accmax P P' W c (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hfm & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HP) HPP.
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]). apply HPP. exact HP.
Qed.

Lemma hd_land : forall (fq : YK11.FPState) (cx : dcx) (h n : Z) ly3 S3 (W3 : world SEGS) mem3 md' k acc
  (E : env) (ss : sstate) (ms : machine_state) (pc kmax accmax : Z) (P : bvmap 5 word -> Prop),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax ->
  mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  d_body B cx h n [] dsh_loop ly3 S3 W3 mem3 ->
  (forall x, ms_mem ms x = mem3 x) ->
  P (ms_regs ms) ->
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax
    (fun regs ly S W m md => P regs /\ d_body B cx h n [] dsh_loop ly S W m) W3 (mkCfg ms md').
Proof.
intros fq cx h n ly3 S3 W3 mem3 md' k acc E ss ms pc kmax accmax P
  FR HB HJ HFR Hk Hev Hmo Hacc HS Hrv Hpc HBD MEQ HP.
pose proof (hd_body_ext cx h n dsh_loop ly3 S3 W3 mem3 (ms_mem ms) MEQ HBD) as HBD'.
pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact FR|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|]. split; [exact HP | exact HBD'].
Qed.

Lemma hd_exit_ok : forall (fq : YK11.FPState) (cx : dcx) (h n i : Z) ly3 S3 (W : world SEGS) mem3 md' k acc
  (E : env) (ss : sstate) (ms : machine_state),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i -> 0 <= i < MAX_OPS ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> ss_pc ss = EXIT_OFF ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 -> (forall x, ms_mem ms x = mem3 x) ->
  d_rX B cx h (ms_regs ms) ->
  exit_pre B MT XM_LIB RLO RHI tfib_K cx h W (mkCfg ms md').
Proof.
intros fq cx h n i ly3 S3 W mem3 md' k acc E ss ms FR HB HJ HFR Hk Hev Hmo Hacc Ri HS Hrv Hpc HBD MEQ HX.
apply hd_exit_weaken.
eapply hd_mono.
- apply (hd_land fq cx h n ly3 S3 W mem3 md' k acc E ss ms EXIT_OFF (EV_HEAD MAX_OPS) (ACC_HEAD MT MAX_OPS)
    (d_rX B cx h) FR HB HJ HFR).
  + clear - Hk Ri. unfold EV_HEAD, EV_PRO, EV_ITER, MAX_OPS in *. lia.
  + clear - Hev Ri. unfold EV_HEAD, EV_PRO, EV_ITER, MAX_OPS in *. lia.
  + exact Hmo.
  + clear - Hacc Ri MT_TRIV. unfold ACC_HEAD, ACC_PRO, ACC_ITER, MAX_OPS in *. rewrite MT_TRIV in *.
    cbn [mo_malloc mo_free ameter_triv] in *. lia.
  + exact HS.
  + exact Hrv.
  + exact Hpc.
  + exact HBD.
  + exact MEQ.
  + exact HX.
- intros regs ly S W' m md [HX' HBD']. exists n. split; [exact HX' | exact HBD'].
Qed.

Lemma hd_regs_ok : forall cx E0 h i n now regs,
  d_base B MT XM_LIB RLO RHI tfib_K cx -> d_E cx E0 -> d_rH B cx h i n now regs ->
  regs_ok (d_env cx E0 (hd_vals cx h i n now regs)) hd_sr regs.
Proof.
intros cx E0 h i n now regs HB HE HR.
pose proof HB as ((HPRE & _) & _).
pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof (hd_den cx E0 (hd_vals cx h i n now regs) HE) as (D60 & D2 & D3' & D4' & D32 & D529).
assert (D3 : sv_denot (d_env cx E0 (hd_vals cx h i n now regs)) (SOff 3 0) = w64 (as_gp B))
  by (rewrite D3'; exact Hgp0).
assert (D4 : sv_denot (d_env cx E0 (hd_vals cx h i n now regs)) (SOff 4 0) = w64 (as_tp B))
  by (rewrite D4'; exact Htp0).
pose proof HR as ((Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27) & H22 & H21 & H14 & H26 & H24).
clear HB HE HR HPRE Hgp0 Htp0 D3' D4'.
apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
repeat (destruct Hz as [<-|Hz];
  [ match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r0) =>
      let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
    lazymatch goal with
    | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
    | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H18 | exact H20 | exact H22 ]
    | |- _ = sv_denot _ (SOff 60 0) => rewrite D60;
        first [ exact H9 | unfold w64; rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned ]
    | |- _ = sv_denot _ (SOff 2 0) => rewrite D2; exact H8
    | |- _ = sv_denot _ (SOff 3 0) => rewrite D3; exact Hgp
    | |- _ = sv_denot _ (SOff 4 0) => rewrite D4; exact Htp
    | |- _ = sv_denot _ (SOff 32 0) => rewrite D32; exact H19
    | |- _ = sv_denot _ (SOff 529 0) => rewrite D529; exact H27
    | |- _ = sv_denot _ (SOff ?q 0) =>
        let j := eval vm_compute in (q - 531)%nat in
        rewrite (hd_dx cx E0 h i n now regs j q eq_refl eq_refl); cbn [nth hd_vals];
        first [ reflexivity | exact H14 | exact H21 | exact H24 | exact H26 ]
    end
  | ]).
destruct Hz.
Qed.

Lemma hd_acs_ok : forall cx E0 h i n now regs ly3 S3 (W : world SEGS) mem3,
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 ->
  Forall (YP09.chunk_ok SEGS (d_env cx E0 (hd_vals cx h i n now regs)) (rd W mem3) (d_A cx)) hd_acs.
Proof.
intros cx E0 h i n now regs ly3 S3 W mem3 HBD.
destruct HBD as (T & G & Lk & H & HFRM & _ & _ & _ & _ & _ & _ & HGEO & _).
destruct HFRM as (E & _ & _ & _ & V1 & V2 & V3 & V4 & V5 & V6 & V7).
destruct HGEO as (G1 & G2 & G3 & G4 & _).
change (fs_frame_bytes DFRAME_CLASS) with 4096 in G2.
pose proof asan_consts as (C1 & _).
assert (Rh : 0 <= h /\ h + 440 < 2 ^ 64) by (clear - G3 G4 C1; unfold HUNT_SIZE in *; lia).
assert (RF : 0 <= d_FB cx /\ d_FB cx + 4096 <= 0x7fffff800000) by (clear - G1 G2 C1; lia).
clear T G Lk H E G1 G2 G3 G4 C1.
unfold hd_acs. cbn [map fst snd].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS _ _ _ _ 8 _ h);
    [ rewrite (hd_dx cx E0 h i n now regs 21 552 eq_refl eq_refl); cbn [nth hd_vals]; reflexivity
    | apply hd_rng64; lia | lia | exact V1 ].
- apply (chunk_ok_val SEGS _ _ _ _ 8 _ (h + 440));
    [ cbn [sv_denot]; rewrite (hd_ex cx E0 h i n now regs 21 552 eq_refl eq_refl); cbn [nth hd_vals];
      unfold w64; rewrite unsigned_lit_small by lia; reflexivity
    | apply hd_rng64; lia | lia | exact V2 ].
- apply (chunk_ok_val SEGS _ _ _ _ 8 _ 0); [ reflexivity | apply hd_rng64; lia | lia | exact V3 ].
- apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OG)));
    [ rewrite (hd_dx cx E0 h i n now regs 22 553 eq_refl eq_refl); cbn [nth hd_vals]; reflexivity
    | apply hd_rng64; unfold d_obj; apply hd_dnot_rng; [lia | lia | cbn [dobj_off]; lia] | lia | exact V4 ].
- apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OT)));
    [ rewrite (hd_dx cx E0 h i n now regs 23 554 eq_refl eq_refl); cbn [nth hd_vals]; reflexivity
    | apply hd_rng64; unfold d_obj; apply hd_dnot_rng; [lia | lia | cbn [dobj_off]; lia] | lia | exact V5 ].
- apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OO)));
    [ rewrite (hd_dx cx E0 h i n now regs 24 555 eq_refl eq_refl); cbn [nth hd_vals]; reflexivity
    | apply hd_rng64; unfold d_obj; apply hd_dnot_rng; [lia | lia | cbn [dobj_off]; lia] | lia | exact V6 ].
- apply (chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OUSED)));
    [ rewrite (hd_dx cx E0 h i n now regs 25 556 eq_refl eq_refl); cbn [nth hd_vals]; reflexivity
    | apply hd_rng64; unfold d_obj; apply hd_dnot_rng; [lia | lia | cbn [dobj_off]; lia] | lia | exact V7 ].
Qed.

Lemma hd_rX_of : forall (fq : YK11.FPState) cx h i n now regs E0 (W : world SEGS) ss ms,
  d_base B MT XM_LIB RLO RHI tfib_K cx -> d_E cx E0 ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) ss (restrict (w_H W) ms) ->
  hd_xregb ss = true -> d_rX B cx h (ms_regs ms).
Proof.
intros fq cx h i n now regs E0 W ss ms HB HE HS HX.
pose proof HB as ((HPRE & _) & _).
pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (c_regs cx)) with (d_S cx) in Hslo, Hshi.
pose proof asan_consts as (C1 & _).
pose proof (hd_A_range (d_S cx) ltac:(clear - C1 Hceil Hslo; unfold MFRAME, LLVMF_STK in *; lia)) as HAr.
change (32 * ((d_S cx - MFRAME) / 32)) with (d_A cx) in HAr.
assert (RA : 0 <= d_A cx < 2 ^ 64) by (clear - C1 Hceil Hslo Hshi H47 HAr; unfold MFRAME, LLVMF_STK in *; lia).
pose proof (hd_den cx E0 (hd_vals cx h i n now regs) HE) as (D60 & D2 & D3 & D4 & D32 & D529).
pose proof (hd_xregb_eqs ss HX) as (X2 & X3 & X4 & X8 & X9 & X19 & X27).
pose proof (st_ok_pi_restrict_reg (w_H W) _ ss ms (2%bv : bv 5) HS) as R2. rewrite X2 in R2.
pose proof (st_ok_pi_restrict_reg (w_H W) _ ss ms (3%bv : bv 5) HS) as R3. rewrite X3 in R3.
pose proof (st_ok_pi_restrict_reg (w_H W) _ ss ms (4%bv : bv 5) HS) as R4. rewrite X4 in R4.
pose proof (st_ok_pi_restrict_reg (w_H W) _ ss ms (8%bv : bv 5) HS) as R8. rewrite X8 in R8.
pose proof (st_ok_pi_restrict_reg (w_H W) _ ss ms (9%bv : bv 5) HS) as R9. rewrite X9 in R9.
pose proof (st_ok_pi_restrict_reg (w_H W) _ ss ms (19%bv : bv 5) HS) as R19. rewrite X19 in R19.
pose proof (st_ok_pi_restrict_reg (w_H W) _ ss ms (27%bv : bv 5) HS) as R27. rewrite X27 in R27.
unfold d_rX.
split; [unfold spZ; rewrite R2, D60; unfold w64; apply unsigned_lit_small; exact RA|].
split; [rewrite R3, D3; exact Hgp0|]. split; [rewrite R4, D4; exact Htp0|].
split; [rewrite R8; exact D2|]. split; [rewrite R9; exact D60|].
split; [rewrite R19; exact D32|]. rewrite R27; exact D529.
Qed.

Lemma hd_seat0 : forall (fq : YK11.FPState) (cx : dcx) (h i n now : Z) ly3 S3 (W : world SEGS) mem3 md3 k acc
  (regs : bvmap 5 word) (E0 : env),
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) hd_ss0
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + HDR_OFF)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HCX.
pose proof HCX as (HB & HJ & HFR & _ & _ & _ & _ & _ & _ & _ & HR & HBD & HE & HRG & HFL).
pose proof (SEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E0 HDR_OFF hd_sr (hd_vals cx h i n now regs)
  hd_acs [] [] (d_facts [] []) (conj HB (conj HJ HFR)) HE HRG HFL (hd_regs_ok cx E0 h i n now regs HB HE HR)
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E0 (hd_vals cx h i n now regs) [] [] (conj HB (conj HJ HFR)) HE I I)
  (hd_acs_ok cx E0 h i n now regs ly3 S3 W mem3 HBD) (Forall_nil _) (Forall_nil _) I (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS.
clear - HS.
hd_ro HS 516%nat. hd_ro HS 529%nat.
exact HS.
Qed.

Lemma hd_exit : forall (fq : YK11.FPState) (cx : dcx) (h i n now : Z) ly3 S3 (W : world SEGS) mem3 md3 k acc
  (regs : bvmap 5 word) (E0 : env) (ss : sstate) (ms : machine_state) (md : Model),
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  (forall x, ms_mem ms x = mem3 x) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> ss_pc ss = EXIT_OFF -> hd_xregb ss = true ->
  hd_post B MT XM_LIB RLO RHI tfib_K cx h i W (mkCfg ms md).
Proof.
intros fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ss ms md HCX FR HJ MEQ HS Hrv Hpc HX.
pose proof HCX as (HB & _ & HFR & Hk & Hev & Hmo & Hacc & Ri & _ & _ & _ & HBD & HE & _).
unfold hd_post. left.
exact (hd_exit_ok fq cx h n i ly3 S3 W mem3 md k acc _ ss ms FR HB HJ HFR Hk Hev Hmo Hacc Ri HS Hrv Hpc HBD MEQ
  (hd_rX_of fq cx h i n now regs E0 W ss ms HB HE HS HX)).
Qed.
End h.
End f.
End d.

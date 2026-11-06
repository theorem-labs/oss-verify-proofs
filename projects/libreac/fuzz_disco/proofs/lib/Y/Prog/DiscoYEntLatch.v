(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 365 of its 397 lines of code are new or changed and 37 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntLatch.v, with its module paths and numbers changed; 268 of its 488 lines of code are new or changed and 177 lines of the source are left out. *)
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
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition lt_sr : list sv :=
  [SLit 0; SOff 534 0; SOff AT_A 0; SOff 3 0; SOff 4 0; SOff 535 0; SOff 536 0; SOff 537 0;
   SOff AT_STK 0; SOff AT_A 0; SOff 538 0; SOff 539 0; SOff 540 0; SOff 541 0; SOff 542 0; SOff 543 0;
   SOff 544 0; SOff 545 0; SLit WS_MASK; SOff 32 0; SLit 32; SOff 546 0; SLit 1; SOff 547 0;
   SOff 548 0; SOff 549 0; SOff 550 0; SOff AT_SH 0; SOff 551 0; SOff 552 0; SOff 553 0; SOff 554 0].
Definition lt_acs (lat : bool) : list YP09.chunk :=
  if lat then
    [YP09.mkChunk 192 (CVal 8 (SOff 531 0)); YP09.mkChunk 200 (CVal 8 (SOff 533 0));
     YP09.mkChunk 208 (CVal 8 (SOff 532 0))]
  else [YP09.mkChunk 192 (CVal 8 (SOff 531 0))].
Definition lt_rs (acs : list YP09.chunk) : smem := [YP09.mkRegion (Some AT_A) 0 472 0 0 acs].

Lemma lt_sub : forall acs, submem (lt_rs acs) (d_kregions dsh_loop acs [] ++ []).
Proof.
intros acs. unfold lt_rs, d_kregions. cbn [app].
apply submem_drop. apply submem_keep; [|apply submem_nil].
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
intros c Hc. apply in_or_app. right. exact Hc.
Qed.

Lemma lt_frame_eq : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hw x. apply HF. intros (r & Hr & Ha).
rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.

Lemma lt_mrestrict_ext : forall (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall x, mrestrict H m' x = mrestrict H m x.
Proof. intros H m m' HM x. unfold mrestrict. rewrite HM. reflexivity. Qed.

Lemma lt_mbyte_ext : forall segs (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof. intros segs H m m' HM a. unfold mbyte, mrestrict. rewrite HM. reflexivity. Qed.

Lemma lt_aview_ext : forall segs (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' HM a. unfold aview. rewrite (lt_mbyte_ext segs H m m' HM). reflexivity. Qed.

Lemma lt_rok_ext : forall segs E (m m' : word -> option byte) r,
  (forall x, m' x = m x) -> region_ok segs E m r -> region_ok segs E m' r.
Proof.
intros segs E m m' r HM HR. unfold region_ok in *. cbv zeta in *.
destruct HR as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. apply (writable_at_grows segs m m'); [intros x Hx; rewrite HM; exact Hx | exact (H3 o Ho)].
- refine (Forall_impl _ _ H4). intros c Hc i Hi. destruct (Hc i Hi) as (b & Hb & Hm).
  exists b. split; [exact Hb|]. unfold mbyte in *. rewrite HM. exact Hm.
Qed.

Lemma lt_addw1 : forall E k i, ew E k = Z_to_bv 64 i -> 0 <= i < 2 ^ 31 - 1 ->
  sv_denot E (SAluw ALU_ADD (SOff k 0) (SLit 1)) = Z_to_bv 64 (i + 1).
Proof.
intros E k i Hk Hi. rewrite denot_lit_U. f_equal. rewrite U_of_S, S_SAluw.
rewrite (U_atom E k i Hk) by lia. rewrite U_lit by lia. cbn [zalu_raw].
rewrite (Z.mod_small i) by lia. rewrite (Z.mod_small 1) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small (i + 1 + 2 ^ 32 / 2)) by lia.
replace (i + 1 + 2 ^ 32 / 2 - 2 ^ 32 / 2) with (i + 1) by lia.
apply Z.mod_small. lia.
Qed.

Lemma lt_beq : forall E k i, ew E k = Z_to_bv 64 i -> 0 <= i < 512 ->
  branch_taken BC_EQ (sv_denot E (SAluw ALU_ADD (SOff k 0) (SLit 1))) (sv_denot E (SLit 512)) = (i + 1 =? 512).
Proof.
intros E k i Hk Hi. rewrite branch_eq_U. unfold U. rewrite (lt_addw1 E k i Hk) by lia. cbn [sv_denot].
rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma lt_bvr : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as Hr. unfold bv_modulus in Hr. exact Hr. Qed.

Lemma lt_A_range : forall S, 0 <= S - MFRAME ->
  S - MFRAME - 31 <= 32 * ((S - MFRAME) / 32) <= S - MFRAME.
Proof.
intros S Hs. pose proof (Z.div_mod (S - MFRAME) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (S - MFRAME) 32 ltac:(lia)) as Hmp. lia.
Qed.

Ltac lt_rg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Definition lt_vals (cx : dcx) (i n : Z) (regs : bvmap 5 word) : list word :=
  [w64 n; w64 i; w64 (d_cur cx n); getr regs 1; getr regs 5; getr regs 6; getr regs 7;
   getr regs 10; getr regs 11; getr regs 12; getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17;
   getr regs 21; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 28; getr regs 29; getr regs 30;
   getr regs 31].

Lemma lt_env_old : forall cx E vals n, (n < AT_FL)%nat -> ew (d_env cx E vals) n = ew E n.
Proof. intros cx E vals n Hn. unfold d_env. apply ew_havoc_old. exact Hn. Qed.

Lemma lt_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
intros cx E vals j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.

Lemma lt_E_env : forall cx E vals, d_E cx E -> d_E cx (d_env cx E vals).
Proof.
intros cx E vals (EE & E32 & HEI & E60 & EF & ESH). unfold d_E.
rewrite !lt_env_old by (unfold AT_FL, AT_A, AT_F, AT_SH; lia).
split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
- intros n r Hn. rewrite lt_env_old; [exact (EE n r Hn)|].
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL. lia.
- unfold d_env. apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL; lia].
Qed.

Lemma lt_frame_ext : forall cx h shf (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_frame cx h shf W m -> d_frame cx h shf W m'.
Proof.
intros cx h shf W m m' HM (E & HE & HR & HFL & V1 & V2 & V3 & V4 & V5 & V6 & V7).
pose proof (lt_mbyte_ext SEGS (w_H W) m m' HM) as MB.
assert (VM : forall a n v, val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W m') a n v)
  by (intros a n v Hv j Hj; rewrite MB; exact (Hv j Hj)).
exists E. split; [exact HE|]. split.
- refine (Forall_impl _ _ HR). intros r Hr. exact (lt_rok_ext SEGS E _ _ r (lt_mrestrict_ext (w_H W) m m' HM) Hr).
- split.
  + rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W) m')); [exact HFL|].
    intros j _. apply lt_aview_ext. exact HM.
  + exact (conj (VM _ _ _ V1) (conj (VM _ _ _ V2) (conj (VM _ _ _ V3) (conj (VM _ _ _ V4)
      (conj (VM _ _ _ V5) (conj (VM _ _ _ V6) (VM _ _ _ V7))))))).
Qed.

Lemma lt_shadow_ext : forall cx shf (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_shadow cx shf W m -> d_shadow cx shf W m'.
Proof. intros cx shf W m m' HM Hs j Hj. rewrite (lt_aview_ext SEGS (w_H W) m m' HM). exact (Hs j Hj). Qed.

Lemma lt_frame_x_of : forall cx h shf (W : world SEGS) m, d_frame cx h shf W m -> d_frame_x cx W m.
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

Lemma lt_body_ext : forall cx h n shf ly3 S3 (W3 : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_body B cx h n [] shf ly3 S3 W3 m -> d_body B cx h n [] shf ly3 S3 W3 m'.
Proof.
intros cx h n shf ly3 S3 W3 m m' HM HBD.
pose proof HBD as (T & G & Lk & H & HFRM & HSHD & _ & _ & (Rn & _) & _).
apply (BKEEP cx h n n shf ly3 S3 W3 m m' (d_S cx) (d_S cx) HBD).
- unfold LLVMF_STK. lia.
- lia.
- intros a _ _. apply lt_aview_ext. exact HM.
- intros a _ (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite HM. exact Hb.
- exact (lt_frame_ext cx h shf W3 m m' HM HFRM).
- exact (lt_shadow_ext cx shf W3 m m' HM HSHD).
- lia.
Qed.

Lemma lt_body_x_of : forall cx h n shf ly S (W : world SEGS) m,
  d_body B cx h n [] shf ly S W m -> d_body_x B cx h ly S W m.
Proof.
intros cx h n shf ly S W m (T & G & Lk & H & Hfr & _ & _ & Hbl & _ & Himg & _).
pose proof Hfr as (E & _ & _ & _ & V184 & _).
exact (conj (lt_frame_x_of cx h shf W m Hfr) (conj Hbl (conj Himg V184))).
Qed.

Lemma lt_exit_weaken : forall cx h W c,
  d_at B MT XM_LIB RLO RHI tfib_K cx EXIT_OFF (EV_HEAD MAX_OPS) (ACC_HEAD MT MAX_OPS)
    (fun regs ly3 S3 W3 mem3 md3 => exists n, d_rX B cx h regs /\ d_body B cx h n [] dsh_loop ly3 S3 W3 mem3) W c ->
  exit_pre B MT XM_LIB RLO RHI tfib_K cx h W c.
Proof.
intros cx h W c (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & HM & Hb & HJ & Hfr & Hk & Hn & Hmo & Hacc & (n & HX & HB)).
exists fq, ly3, S3, regs, mem3, md3, k, acc.
exact (conj Hc (conj HM (conj Hb (conj HJ (conj Hfr (conj Hk (conj Hn (conj Hmo (conj Hacc
  (conj HX (lt_body_x_of cx h n dsh_loop ly3 S3 W mem3 HB))))))))))).
Qed.

Lemma lt_mono : forall cx pc kmax accmax
  (P P' : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop) W c,
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P W c ->
  (forall regs ly S W' mem md, P regs ly S W' mem md -> P' regs ly S W' mem md) ->
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P' W c.
Proof.
intros cx pc kmax accmax P P' W c (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & HM & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HP) HPP.
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]). apply HPP. exact HP.
Qed.

Lemma lt_land : forall (fq : YK11.FPState) (cx : dcx) (h n : Z) ly3 S3 (W3 : world SEGS) mem3 md' k acc
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
  HM HB HJ HFR Hk Hev Hmo Hacc HS Hrv Hpc HBD MEQ HP.
pose proof (lt_body_ext cx h n dsh_loop ly3 S3 W3 mem3 (ms_mem ms) MEQ HBD) as HBD'.
pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HM|].
split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|]. split; [exact HP | exact HBD'].
Qed.

Lemma lt_exit_ok : forall (fq : YK11.FPState) (cx : dcx) (h n i : Z) ly3 S3 (W : world SEGS) mem3 md' k acc
  (E : env) (ss : sstate) (ms : machine_state),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD (i + 1) -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD (i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT (i + 1) -> 0 <= i < MAX_OPS ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> ss_pc ss = EXIT_OFF ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 -> (forall x, ms_mem ms x = mem3 x) ->
  d_rX B cx h (ms_regs ms) ->
  exit_pre B MT XM_LIB RLO RHI tfib_K cx h W (mkCfg ms md').
Proof.
intros fq cx h n i ly3 S3 W mem3 md' k acc E ss ms HM HB HJ HFR Hk Hev Hmo Hacc Ri HS Hrv Hpc HBD MEQ HX.
apply lt_exit_weaken.
eapply lt_mono.
- apply (lt_land fq cx h n ly3 S3 W mem3 md' k acc E ss ms EXIT_OFF (EV_HEAD MAX_OPS) (ACC_HEAD MT MAX_OPS)
    (d_rX B cx h) HM HB HJ HFR).
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

Lemma lt_hdr_ok : forall (fq : YK11.FPState) (cx : dcx) (h i n now : Z) ly3 S3 (W : world SEGS) mem3 md' k acc
  (E : env) (ss : sstate) (ms : machine_state),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD (i + 1) -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD (i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT (i + 1) ->
  0 <= i + 1 < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> ss_pc ss = HDR_OFF ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 -> (forall x, ms_mem ms x = mem3 x) ->
  d_rH B cx h (i + 1) n now (ms_regs ms) ->
  loop_inv B MT XM_LIB RLO RHI tfib_K cx h (i + 1) W (mkCfg ms md').
Proof.
intros fq cx h i n now ly3 S3 W mem3 md' k acc E ss ms HM HB HJ HFR Hk Hev Hmo Hacc Ri Rn Rnow HS Hrv Hpc HBD MEQ HP.
eapply lt_mono.
- exact (lt_land fq cx h n ly3 S3 W mem3 md' k acc E ss ms HDR_OFF (EV_HEAD (i + 1)) (ACC_HEAD MT (i + 1))
    (d_rH B cx h (i + 1) n now) HM HB HJ HFR Hk Hev Hmo Hacc HS Hrv Hpc HBD MEQ HP).
- intros regs ly S W' m md [HP' HBD']. exists n, now.
  split; [exact Ri|]. split; [exact Rn|]. split; [exact Rnow|]. split; [exact HP' | exact HBD'].
Qed.

Ltac lt_leaf_mem :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msf; cfg_model := _ |} _ =>
  lazymatch goal with HBD : d_body _ _ _ _ _ _ _ _ _ ?m0 |- _ =>
  let MEQ := fresh "MEQ" in
  assert (MEQ : forall x, ms_mem msf x = m0 x)
    by (intros x; repeat match goal with Mx : forall x, ms_mem _ x = _ |- _ => rewrite Mx; clear Mx end; reflexivity)
  end end.

Ltac lt_after_run :=
  lazymatch goal with HF : frame_of _ _ (ms_mem _) (ms_mem _) |- _ =>
    let M := fresh "M" in pose proof (lt_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as M;
    clear HF; repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.

Lemma lt_walk : forall (lat : bool) (cx : dcx) (h i n now : Z) (W : world SEGS) (fq : YK11.FPState)
  ly3 S3 (regs : bvmap 5 word) mem3 md3 k acc,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD (i + 1) -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD (i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT (i + 1) ->
  0 <= i < MAX_OPS -> 0 <= n ->
  d_rLAT B cx h regs -> d_sp0 cx i now W mem3 -> val_mem SEGS (rd W mem3) (d_A cx + 192) 8 n ->
  (if lat then val_mem SEGS (rd W mem3) (d_A cx + 200) 8 (d_cur cx n)
   else getr regs 21 = w64 i /\ getr regs 24 = w64 (d_cur cx n)) ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + (if lat then LAT_OFF else L27_OFF)) regs mem3 md3)
    (fun W' c' => (i + 1 < MAX_OPS /\ loop_inv B MT XM_LIB RLO RHI tfib_K cx h (i + 1) W' c') \/
                  exit_pre B MT XM_LIB RLO RHI tfib_K cx h W' c').
Proof.
intros lat cx h i n now W fq ly3 S3 regs mem3 md3 k acc HM HB HJ HFR Hk Hev Hmo Hacc Ri Rn HR HSP0 V192 HX HBD.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact HB | split; [exact HJ | exact HFR]]).
pose proof asan_consts as (C1 & _).
pose proof HB as ((HPRE & _ & _ & _ & HINdisj & _) & _).
pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (c_regs cx)) with (d_S cx) in Hslo, Hshi.
pose proof (lt_A_range (d_S cx) ltac:(clear - C1 Hceil Hslo; unfold MFRAME, LLVMF_STK in *; lia)) as HAr.
change (32 * ((d_S cx - MFRAME) / 32)) with (d_A cx) in HAr.
assert (RA : 0 <= d_A cx < 2 ^ 64) by (clear - C1 Hceil Hslo Hshi H47 HAr; unfold MFRAME, LLVMF_STK in *; lia).
pose proof HBD as (T & G & Lk & H & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTK & HWR).
pose proof HFRM as (E & HE & HRG & HFL & _).
pose proof HE as (EE & E32 & HEI & E60 & E516 & E529).
unfold AT_A, AT_F, AT_SH in E60, E516, E529.
pose proof HR as ((Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27) & H22).
pose proof HSP0 as (V208 & _).
pose proof HINP as (Rn' & _ & _).
assert (Rcn : c_n cx < 2 ^ 26) by (clear - HINdisj; destruct HINdisj as [(-> & _) | (Hr & _)]; lia).
assert (Rn64 : 0 <= n < 2 ^ 64) by (clear - Rn Rn' Rcn; lia).
assert (Ri64 : 0 <= i < 2 ^ 64) by (clear - Ri; unfold MAX_OPS in Ri; lia).
assert (Rcur : 0 <= d_cur cx n < 2 ^ 64).
{ clear - HINdisj HGEO Rn Rn' C1. unfold d_cur. destruct HINdisj as [(Hn0 & Hp0) | (Hnr & _)].
  - rewrite Hp0, Hn0. rewrite Hn0 in Rn'. unfold A_EMPTY. lia.
  - destruct HGEO as (_ & _ & _ & _ & _ & _ & _ & HGin). destruct (HGin (proj1 Hnr)) as (Hp0 & Hpc & _). lia. }
pose proof (lt_E_env cx E (lt_vals cx i n regs) HE) as HEd.
pose proof HEd as (_ & _ & HEI' & _).
assert (AO : forall q, (q < AT_FL)%nat -> ew (d_env cx E (lt_vals cx i n regs)) q = ew E q)
  by (intros q Hq; apply lt_env_old; exact Hq).
assert (AX : forall j, (j < 24)%nat ->
  ew (d_env cx E (lt_vals cx i n regs)) (AT_X + j) = nth j (lt_vals cx i n regs) (Z_to_bv 64 0))
  by (intros j Hj; apply lt_env_x; cbn [length lt_vals]; lia).
assert (D60 : sv_denot (d_env cx E (lt_vals cx i n regs)) (SOff 60 0) = w64 (d_A cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E60).
assert (D2 : sv_denot (d_env cx E (lt_vals cx i n regs)) (SOff 2 0) = w64 (d_S cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D3 : sv_denot (d_env cx E (lt_vals cx i n regs)) (SOff 3 0) = w64 (as_gp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 3%nat 3%bv eq_refl); exact Hgp0).
assert (D4 : sv_denot (d_env cx E (lt_vals cx i n regs)) (SOff 4 0) = w64 (as_tp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 4%nat 4%bv eq_refl); exact Htp0).
assert (D32 : sv_denot (d_env cx E (lt_vals cx i n regs)) (SOff 32 0) = w64 SHADOW_OFF)
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E32).
assert (D529 : sv_denot (d_env cx E (lt_vals cx i n regs)) (SOff 529 0) = w64 (shadow_addr (d_FB cx)))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E529).
assert (DX : forall j q, q = (AT_X + j)%nat -> (j < 24)%nat ->
  sv_denot (d_env cx E (lt_vals cx i n regs)) (SOff q 0) = nth j (lt_vals cx i n regs) (Z_to_bv 64 0))
  by (intros j q -> Hj; rewrite sv_denot_SOff0; exact (AX j Hj)).
assert (HROK : regs_ok (d_env cx E (lt_vals cx i n regs)) lt_sr regs).
{ apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
  repeat (destruct Hz as [<-|Hz];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
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
          rewrite (DX j q eq_refl ltac:(lia)); cbn [nth lt_vals]; reflexivity
      end
    | ]).
  destruct Hz. }
assert (HFACTS : facts_ok (d_env cx E (lt_vals cx i n regs)) (d_facts [] []))
  by exact (FACTS LAWS cx ly3 S3 W mem3 md3 k E (lt_vals cx i n regs) [] [] HC HE I I).
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (lt_vals cx i n regs)) (rd W mem3) (d_A cx)) (lt_acs lat)).
{ destruct lat; cbn [lt_acs]; repeat apply Forall_cons; try apply Forall_nil.
  1, 4: apply (chunk_ok_val SEGS _ _ _ _ 8 _ n);
      [rewrite (DX 0%nat 531%nat eq_refl ltac:(lia)); reflexivity | cbn; clear - Rn64; lia | lia | exact V192].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (d_cur cx n));
      [rewrite (DX 2%nat 533%nat eq_refl ltac:(lia)); reflexivity | cbn; clear - Rcur; lia | lia | exact HX].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ i);
      [rewrite (DX 1%nat 532%nat eq_refl ltac:(lia)); reflexivity | cbn; clear - Ri64; lia | lia | exact V208]. }
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof (SEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E (if lat then LAT_OFF else L27_OFF) lt_sr
  (lt_vals cx i n regs) (lt_acs lat) [] [] (d_facts [] []) HC HE HRG HFL HROK HFACTS HACS (Forall_nil _) (Forall_nil _)
  I (Forall_nil _) ltac:(destruct lat; vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ (lt_rs (lt_acs lat)) HS0 (lt_sub (lt_acs lat))
  ltac:(destruct lat; vm_compute; reflexivity)) as HS1.
clear HS0 HROK HFACTS HACS HRG HFL HFRM HE EE HEI HEd HOBJ HBLK HINP HIMG HOFF HGEO HCAN HSTK HWR HSHD HPRE HINdisj.
unfold cfg_at.
destruct lat;
[ assert (Ak : ew (d_env cx E (lt_vals cx i n regs)) 532%nat = Z_to_bv 64 i) by exact (AX 1%nat ltac:(lia));
  change (w64 (BASE + (if true then LAT_OFF else L27_OFF))) with (Z_to_bv 64 (BASE + LAT_OFF))
| destruct HX as [H21 H24];
  assert (Ak : ew (d_env cx E (lt_vals cx i n regs)) 546%nat = Z_to_bv 64 i)
    by (change 546%nat with (AT_X + 15)%nat; rewrite (AX 15%nat ltac:(lia)); exact H21);
  change (w64 (BASE + (if false then LAT_OFF else L27_OFF))) with (Z_to_bv 64 (BASE + L27_OFF)) ].
all: let lt_regL HS :=
  unfold d_rL;
  lt_rg HS (2%bv : bv 5) R2; lt_rg HS (3%bv : bv 5) R3; lt_rg HS (4%bv : bv 5) R4; lt_rg HS (8%bv : bv 5) R8;
  lt_rg HS (9%bv : bv 5) R9; lt_rg HS (19%bv : bv 5) R19; lt_rg HS (18%bv : bv 5) R18; lt_rg HS (20%bv : bv 5) R20;
  lt_rg HS (27%bv : bv 5) R27;
  split; [unfold spZ; rewrite R2, D60; unfold w64; apply unsigned_lit_small; exact RA|];
  split; [rewrite R3; exact D3|]; split; [rewrite R4; exact D4|]; split; [rewrite R8; exact D2|];
  split; [rewrite R9; exact D60|]; split; [rewrite R19; exact D32|]; split; [rewrite R18; reflexivity|];
  split; [rewrite R20; reflexivity|]; rewrite R27; exact D529 in
let lt_regX HS :=
  unfold d_rX;
  lt_rg HS (2%bv : bv 5) R2; lt_rg HS (3%bv : bv 5) R3; lt_rg HS (4%bv : bv 5) R4; lt_rg HS (8%bv : bv 5) R8;
  lt_rg HS (9%bv : bv 5) R9; lt_rg HS (19%bv : bv 5) R19; lt_rg HS (27%bv : bv 5) R27;
  split; [unfold spZ; rewrite R2, D60; unfold w64; apply unsigned_lit_small; exact RA|];
  split; [rewrite R3; exact D3|]; split; [rewrite R4; exact D4|]; split; [rewrite R8; exact D2|];
  split; [rewrite R9; exact D60|]; split; [rewrite R19; exact D32|]; rewrite R27; exact D529 in
let lt_exit HS :=
  lt_leaf_mem; apply SRr_ret; right;
  lazymatch goal with MEQ : forall x, ms_mem _ x = _ |- _ =>
  eapply (lt_exit_ok fq cx h n i ly3 S3 W mem3 _ k acc _ _ _ HM HB HJ HFR Hk Hev Hmo Hacc Ri HS eq_refl eq_refl HBD MEQ);
  lt_regX HS end in
let lt_hdr kk HS :=
  lt_leaf_mem; apply SRr_ret; left;
  rewrite (lt_beq _ kk i Ak) in Hc by (clear - Ri; unfold MAX_OPS in Ri; lia);
  apply Z.eqb_neq in Hc;
  split; [clear - Ri Hc; unfold MAX_OPS in *; lia|];
  lazymatch goal with MEQ : forall x, ms_mem _ x = _ |- _ =>
  apply (lt_hdr_ok fq cx h i n (bv_unsigned (getr regs 26)) ly3 S3 W mem3 _ k acc _ _ _ HM HB HJ HFR Hk Hev Hmo Hacc
    ltac:(clear - Ri Hc; unfold MAX_OPS in *; lia) Rn (lt_bvr (getr regs 26)) HS eq_refl eq_refl HBD MEQ) end;
  unfold d_rH; split; [lt_regL HS|];
  lt_rg HS (22%bv : bv 5) R22; lt_rg HS (21%bv : bv 5) R21; lt_rg HS (14%bv : bv 5) R14;
  lt_rg HS (26%bv : bv 5) R26; lt_rg HS (24%bv : bv 5) R24;
  split; [rewrite R22; reflexivity|];
  split; [rewrite R21, (lt_addw1 _ kk i Ak) by (clear - Ri; unfold MAX_OPS in *; lia); reflexivity|];
  split; [rewrite R14, (DX 0%nat 531%nat eq_refl ltac:(lia)); reflexivity|];
  split; [rewrite R26, (DX 19%nat 550%nat eq_refl ltac:(lia)); cbn [nth lt_vals]; unfold w64; symmetry;
          apply Z_to_bv_bv_unsigned|];
  rewrite R24; first [ rewrite (DX 2%nat 533%nat eq_refl ltac:(lia)); reflexivity
                     | rewrite (DX 17%nat 548%nat eq_refl ltac:(lia)); cbn [nth lt_vals]; exact H24 ] in
let lt_go kk :=
  paj_run_to_sh RUNTO HS1 HJ HDR_OFF; [awr_ok_tac | lt_after_run;
  apply (BR W _ _ _ _ _ BC_EQ (SAluw ALU_ADD (SOff kk 0) (SLit 1)) (SLit 512) HS1); intros Hc HS2;
  [ paj_run_to_sh RUNTO HS2 HJ EXIT_OFF; [awr_ok_tac | lt_after_run; lt_exit HS2]
  | paj_run_to_sh RUNTO HS2 HJ HDR_OFF; [awr_ok_tac | lt_after_run; lt_hdr kk HS2] ] ] in
lazymatch type of Ak with ew _ ?kk = _ => lt_go kk end.
Qed.

Theorem pb_latch : latch_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold latch_spec. intros cx h i n now W c [Hpre | Hpre].
- destruct Hpre as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HM & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
    Ri & Rn & Rnow & HR & HSP & HBD).
  exact (lt_walk true cx h i n now W fq ly3 S3 regs mem3 md3 k acc HM HB HJ HFR Hk Hev Hmo Hacc Ri Rn HR
    (proj1 HSP) (proj1 (proj2 HSP)) (proj2 (proj2 HSP)) HBD).
- destruct Hpre as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HM & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
    Ri & Rn & Rnow & HR & H21 & H24 & HSP0 & V192 & HBD).
  exact (lt_walk false cx h i n now W fq ly3 S3 regs mem3 md3 k acc HM HB HJ HFR Hk Hev Hmo Hacc Ri Rn HR
    HSP0 V192 (conj H21 H24) HBD).
Qed.
End h.
End f.
End d.

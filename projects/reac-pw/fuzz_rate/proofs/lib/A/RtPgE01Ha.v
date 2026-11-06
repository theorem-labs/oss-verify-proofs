(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths, module names and addresses changed; 1418 of its 1528 lines of code are new or changed and 904 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW3a.v, with its module paths and module names changed; 145 of its 178 lines of code are new or changed and 1495 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the eight input-length
   arms of part HDR of segment S_E01 of the walk of LLVMFuzzerTestOneInput (HD 0x808e4 -> CALL 0x52bb4), each one
   run of the symbolic engine under the harness journal (lib/Reusable/YCbq.v aj_run_to_tok) from the state
   lib/A/RtPgE01Hk.v e01h_ss to the `jal` of malloc's target 0x52bb4, read off as RtPgE01Hk.e01h_leaf.
   Proves no function (kind: segment lemma, its parts).

   THE ARMS (n the input length, m = min n 7 header bytes read; s5 pinned to the literal n, or to its own atom with
   the fact [8, 2^26 - 1] when n >= 8; the metadata byte of the input's first granule the literal n when n < 8, 0 when
   n >= 8): n = 0 (`beqz s5` 0x808e4 -> 0x8091c, six zero spills), n = 1 .. 6 (the reads of bytes 0 .. n - 1, each
   check's slow block taken and passing, the tests `bne s5,k` deciding the exit), n = 7 (all seven reads, every slow
   block taken), n >= 8 (all seven reads, every metadata byte 0). Templates: lib/A/RtPgSteps.v PART 2 (u32_run_arm,
   u32_leaf: one run per arm, the last state's registers read by st_ok_restrict_reg) and the role walk
   proofs/reac-pw/fuzz_role/lib/A/RPgW3a.v at commit 67b6b93ee241 (w3_rgn, w3_slot, w3_kwr,
   w3_in). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg RtPgE01D.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgMem RtPgSteps RtPgE01Hk.
From OSSVerify.reac_pw.fuzz_rate.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ---- reading the last state ---- *)
Ltac e01h_in := repeat (first [left; reflexivity | right]).
(* a register of the last state: its symbolic value, computed *)
Ltac e01h_sr HS :=
  lazymatch type of HS with st_ok ?segs ?E ?s (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E s ms _ HS);
    lazymatch goal with |- sv_denot _ (sr_get ?l ?r) = _ =>
      let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e end
  end.
(* the value of a symbolic term the run left *)
Ltac e01h_v E25 E21 Hpr Hnr :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = _ =>
      cbn [sv_denot]; unfold w64; f_equal; first [reflexivity | lia | (rewrite e01h_u8_out by lia; first [reflexivity | lia])]
  | |- sv_denot ?EE (SOff 25 ?c) = _ => rewrite (e01h_den_off EE 25 _ c E25 Hpr); unfold w64; f_equal; lia
  | |- sv_denot ?EE (SOff 21 ?c) = _ => rewrite (e01h_den_off EE 21 _ c E21 Hnr); unfold w64; f_equal; lia
  | |- sv_denot ?EE (SOff ?k 0) = _ =>
      apply e01h_den_off0; [apply e01h_ewb; lia | match goal with |- 0 <= rh_u8 ?pl ?i < _ => pose proof (e01h_u8_range pl i); lia end]
  | |- sv_denot ?EE (SAlu ALU_SLL _ _) = _ => apply e01h_den_sll8; [apply e01h_ewb; lia | apply e01h_u8_range]
  | |- sv_denot ?EE (SAlu ALU_ADD _ _) = _ => apply e01h_den_mod24; [apply e01h_ewb; lia | apply e01h_u8_range]
  end.
(* a window of the start regions lies in R+0x38 .. R+0x128 *)
Ltac e01h_kwr Ub9 :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  cbn [ss_mem e01h_ss e01h_mem In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val e01h_rR e01h_rIn e01h_rC e01h_rK] in Hb;
     first [rewrite Ub9 in Hb | idtac]; lia | ]);
  destruct Hr.
(* the leaf: e01h_leaf off the last state *)
Ltac e01h_leaf_tac hx Ub9 E25 E21 Hpr Hnr :=
  lazymatch goal with HS : st_ok _ ?EE ?ssf (restrict (w_H ?Wx) ?msx), HFr : frame_of _ _ (mrestrict _ ?m1) _ |- _ =>
  let HR0 := fresh "HR0" in
  let r := eval vm_compute in (nth_error (ss_mem ssf) 0) in
  lazymatch r with Some ?rr => pose proof (e01h_region_nth _ ssf _ 0 rr HS ltac:(vm_compute; reflexivity)) as HR0 end;
  cbn [ms_mem restrict] in HR0;
  unfold e01h_leaf;
  split; [assumption|];
  split;
  [ let q := fresh "q" in let Hq := fresh "Hq" in intros q Hq; cbn [In] in Hq;
    repeat (destruct Hq as [<- | Hq]; [eapply (e01h_reg_atom _ _ msx (w_H Wx) _ _ _ HS (env_agree_refl 32 _));
                                       vm_compute; reflexivity|]);
    destruct Hq |];
  do 7 (split; [e01h_sr HS; e01h_v E25 E21 Hpr Hnr|]);
  do 6 (split; [eapply (e01h_slot _ _ 9 _ _ _ _ _ _ _ _ _ HR0 Ub9); [e01h_in | e01h_v E25 E21 Hpr Hnr]|]);
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
  intros a Ha Hn;
  apply (e01h_keep_run _ _ (w_H Wx) m1 (ms_mem msx) (fun a => e01_R hx + 0x38 <= a < e01_R hx + 0x128) HFr);
  [e01h_kwr Ub9 | exact Ha | exact Hn]
  end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x1f0 + ASTACK <= LLVMF_STK.
Hypothesis HEMPTY : 0 < A_EMPTY < kLowMemEnd.
Hypothesis HSTATIC : rh_static_law rsegs B RLO RHI.
Hypothesis HRELRO : forall a, RLO <= a < RHI -> in_img rsegs a.

(* one arm: from HD to the `jal` of malloc's target, given the input length's case P *)
Definition e01h_arm_stmt (P : Z -> Prop) : Prop :=
  forall hx pos lyc Sc W regs mem md (Q : world rsegs -> config -> Prop),
  rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
  e01_hd B LLVMF_STK hx pos lyc Sc W regs mem md -> P (h_n rsegs hx) ->
  (forall regs' mem' md', e01h_leaf B LLVMF_STK hx pos lyc Sc W regs mem regs' mem' md' ->
     SRr rsegs W (cfg_at rsegs E01_MALLOC regs' mem' md') Q) ->
  SRr rsegs W (cfg_at rsegs E01_HD regs mem md) Q.

(* the whole proof of one arm: m bytes read, s5 = nv, the metadata byte s, the extra atom facts nf *)
Local Ltac e01h_arm m nv s nf nvtac nftac svtac :=
  intros hx pos lyc Sc W regs mem md Q Hb Hhd HN K;
  pose proof Hb as (_ & _ & _ & _ & Hcase & _);
  destruct (e01h_pre B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSTK HSTATIC HRELRO
              hx pos lyc Sc W regs mem md Hb Hhd)
    as (HJ & H9 & H18 & H21 & H25 & Hlen & Hn26 & Hg & HR0 & HR32 & HR1 & HRs & HRS & Hpres & Hrom & Hp);
  pose proof (AR_laws_ok rsegs B) as LAWS; pose proof rts_segs_low as Hsegs; pose proof rts_wx as Hwx;
  assert (Hpr : 0 <= h_p rsegs hx < 2 ^ 64)
    by (destruct Hcase as [[Hn0 Hp0] | [Hn0 _]];
        [rewrite Hp0; unfold kLowMemEnd in HEMPTY; lia | destruct (Hp ltac:(lia)) as (_ & ? & _ & ? & _); lia]);
  assert (Hnr : 0 <= h_n rsegs hx < 2 ^ 64) by lia;
  assert (E9 : ew (Ereg regs (e01h_extra (h_p rsegs hx) (h_pl rsegs hx))) 9 = w64 (e01_R hx))
    by (rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl); exact H9);
  assert (E25 : ew (Ereg regs (e01h_extra (h_p rsegs hx) (h_pl rsegs hx))) 25 = w64 (h_p rsegs hx))
    by (rewrite (ew_Ereg_nat regs _ 25 (Z_to_bv 5 25) eq_refl); exact H25);
  assert (E21 : ew (Ereg regs (e01h_extra (h_p rsegs hx) (h_pl rsegs hx))) 21 = w64 (h_n rsegs hx))
    by (rewrite (ew_Ereg_nat regs _ 21 (Z_to_bv 5 21) eq_refl); exact H21);
  assert (Ub9 : bv_unsigned (ew (Ereg regs (e01h_extra (h_p rsegs hx) (h_pl rsegs hx))) 9) = e01_R hx)
    by (rewrite E9; apply unsigned_lit_small; lia);
  assert (HS : st_ok rsegs (Ereg regs (e01h_extra (h_p rsegs hx) (h_pl rsegs hx))) (e01h_ss m nv s nf)
     (restrict (w_H W) (mkst regs (Z_to_bv 64 0x808e4) mem (seg_rom rsegs))));
  [ apply (e01h_entry W regs mem (e01_R hx) (h_p rsegs hx) (h_pl rsegs hx) m nv s nf H9 H25 H18);
    [ nvtac | nftac | lia | lia | exact HR0 | exact HR32 | exact HR1 | exact Hpres | exact Hg
    | let Hm0 := fresh "Hm0" in intros Hm0;
      let A1 := fresh "A" in let A2 := fresh "A" in let A3 := fresh "A" in let A4 := fresh "A" in
      let A5 := fresh "A" in let A6 := fresh "A" in let A7 := fresh "A" in
      destruct (Hp ltac:(lia)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7);
      split; [exact A1|]; split; [exact A2|]; split; [lia|]; split; [exact A4|];
      split; [rewrite A5; f_equal; svtac|]; split; lia
    | intros; exact Hrom ]
  | ];
  unfold cfg_at, E01_HD; change (w64 0x808e4) with (Z_to_bv 64 0x808e4);
  assert (SHOK : sh_ok rsegs E01H_Bx [] (Ereg regs (e01h_extra (h_p rsegs hx) (h_pl rsegs hx))) (mrestrict (w_H W) mem))
    by (unfold sh_ok; apply Forall_nil);
  aj_run_to_tok e01h_tbl_ok HS HJ SHOK E01H_span 0x52bb4;
  [ apply (e01h_awr _ m s LLVMF_STK (spZ (h_regs rsegs hx)) (e01_R hx) _ _ _ _ _ Ub9); lia
  | let Ems := fresh "Ems" in
    lazymatch goal with HS' : st_ok _ _ _ (restrict _ ?ms) |- _ =>
      pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS' eq_refl) as Ems; cbn [ss_pc] in Ems; rewrite Ems end;
    apply K;
    e01h_leaf_tac hx Ub9 E25 E21 Hpr Hnr ].

Local Ltac e01h_nv_lit :=
  idtac; match goal with H : _ = w64 (h_n _ _), HN : h_n _ _ = _ |- _ => etransitivity; [exact H | rewrite HN; reflexivity] end.
Local Ltac e01h_nv_atom :=
  idtac; match goal with E : ew _ 21 = w64 (h_n _ _), H : getr _ _ = w64 (h_n _ _) |- _ =>
    cbn [sv_denot]; rewrite E; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; exact H end.
Local Ltac e01h_nf_big :=
  idtac; match goal with E : ew _ 21 = w64 (h_n _ _) |- _ =>
    cbn [atoms_ok]; split; [|exact I]; unfold afact_ok; cbn [af_lo af_hi af_al2];
    rewrite E; unfold w64; rewrite unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia end.
Local Ltac e01h_sv_lit := idtac; match goal with HN : h_n _ _ = _ |- _ => unfold e01h_sv; rewrite HN; reflexivity end.
Local Ltac e01h_sv_big :=
  idtac; match goal with HN : 8 <= h_n ?a ?b |- _ =>
    unfold e01h_sv; replace (h_n a b <? 8) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity end.

Lemma e01h_arm0 : e01h_arm_stmt (fun n => n = 0).
Proof using HSTK HEMPTY HSTATIC HRELRO.
e01h_arm 0%nat (SLit 0) 0 (@nil (nat * afact)) e01h_nv_lit ltac:(exact I) e01h_sv_lit.
Qed.
Lemma e01h_arm1 : e01h_arm_stmt (fun n => n = 1).
Proof using HSTK HEMPTY HSTATIC HRELRO.
e01h_arm 1%nat (SLit 1) 1 (@nil (nat * afact)) e01h_nv_lit ltac:(exact I) e01h_sv_lit.
Qed.
Lemma e01h_arm2 : e01h_arm_stmt (fun n => n = 2).
Proof using HSTK HEMPTY HSTATIC HRELRO.
e01h_arm 2%nat (SLit 2) 2 (@nil (nat * afact)) e01h_nv_lit ltac:(exact I) e01h_sv_lit.
Qed.
Lemma e01h_arm3 : e01h_arm_stmt (fun n => n = 3).
Proof using HSTK HEMPTY HSTATIC HRELRO.
e01h_arm 3%nat (SLit 3) 3 (@nil (nat * afact)) e01h_nv_lit ltac:(exact I) e01h_sv_lit.
Qed.
Lemma e01h_arm4 : e01h_arm_stmt (fun n => n = 4).
Proof using HSTK HEMPTY HSTATIC HRELRO.
e01h_arm 4%nat (SLit 4) 4 (@nil (nat * afact)) e01h_nv_lit ltac:(exact I) e01h_sv_lit.
Qed.
Lemma e01h_arm5 : e01h_arm_stmt (fun n => n = 5).
Proof using HSTK HEMPTY HSTATIC HRELRO.
e01h_arm 5%nat (SLit 5) 5 (@nil (nat * afact)) e01h_nv_lit ltac:(exact I) e01h_sv_lit.
Qed.
Lemma e01h_arm6 : e01h_arm_stmt (fun n => n = 6).
Proof using HSTK HEMPTY HSTATIC HRELRO.
e01h_arm 6%nat (SLit 6) 6 (@nil (nat * afact)) e01h_nv_lit ltac:(exact I) e01h_sv_lit.
Qed.
Lemma e01h_arm7 : e01h_arm_stmt (fun n => n = 7).
Proof using HSTK HEMPTY HSTATIC HRELRO.
e01h_arm 7%nat (SLit 7) 7 (@nil (nat * afact)) e01h_nv_lit ltac:(exact I) e01h_sv_lit.
Qed.
Lemma e01h_arm8 : e01h_arm_stmt (fun n => 8 <= n).
Proof using HSTK HEMPTY HSTATIC HRELRO.
e01h_arm 7%nat (SOff 21 0) 0 [(21%nat, mkAF 8 67108863 0)] e01h_nv_atom e01h_nf_big e01h_sv_big.
Qed.
End b.

Print Assumptions e01h_arm0.
Print Assumptions e01h_arm8.

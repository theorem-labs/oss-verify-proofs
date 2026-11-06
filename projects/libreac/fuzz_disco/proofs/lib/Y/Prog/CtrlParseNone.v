(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated to libreac/fuzz_disco (the same code of reac_ctrl_parse at other addresses; the cut specifications are fuzz_disco's, which bound n and keep one memory equation instead of acall_kept). *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin, for fuzz_disco.asan-ubsan (lib_both3_0_listing, entry 0x874a4): the run steps relocated from fuzz_grant image B's walk of the same code (a working branch edc3e948664, lib/B/Prog/CtrlParseNone.v; Y pc = image B pc + 0x4d30), on the fuzz_disco statement layer of lib/A/Prog/CtrlParseNone.v (a working branch eafd64be243) over lib/Y/Prog/CtrlParseCut.v; the n < 50 branch is refuted from 50 <= n (that path is the short walk's). *)
(* reac_ctrl_parse (0x874a4 of fuzz_disco's asan-ubsan image, AF_both3_reac_ctrl_parse 0x64e8 of the listing),
   the walk from cut M (0x875e4) to cut J (0x878c4) on the two paths the header check rejects when 50 <= n
   (frame[12] <> 0x88, frame[13] <> 0x19): the return code 0, the out struct all zero.
   The branches the engine decides from the atom facts on the way: the NULL check of f (0x875ec beqz s5)
   and the overflow checks of f + 12 (0x875f4 bgeu) and f + 13 (0x8761c bltu), each to the trap 0x87ca0
   (atom 10 lies in [1, 2^47 - 50]); the alignment check of o (0x878c0 bnez, to 0x87ca0) on the rejecting
   path (atom 12 is 8-aligned). The two shadow checks of the header bytes (0x87608, 0x87630) branch to the
   report stubs 0x87ca4 and 0x87cb0, whose `jal __asan_report_load1` at 0x87cac and 0x87cb8 this walk
   refutes from the shadow facts (sh_ok). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YM05 YI16 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC81 YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo YCkd YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParse CtrlParseLib KindOfLink1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
(* The windows of a run lie in the stack below the entry sp, the out struct or the own frame. *)
Local Ltac pzN_win :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Ha := fresh "Ha" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Ha;
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (b, wlo, whi) l') in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; revert Ha; pz_bases; intro Ha; cbv beta;
unfold pz_nf, SHADOW_OFF, SB in *; lia |]); destruct Hin.
Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
(* The caller's memory after a run: the run wrote only its windows (the stack below sp, the out struct),
   so what the call keeps of the caller's memory (pz_kept) carries over it. *)
Local Ltac pzN_kp :=
lazymatch goal with
| HFr : frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB), HF : frame_of _ _ (ms_mem _) (ms_mem _), HG : mem_grows _ _,
  KP : pz_kept ?B ?lyc ?Sc ?W ?memc _ ?slo ?sp ?o,
  HAR : AR _ ?B ?lyc ?Sc ?W ?memc ?mdc,
  Hfrs2 : frames ?S2 = (1, ?fpos) :: frames ?Sc,
  HARc : AR _ ?B ?lyc ?S2 ?W _ _,
  Eab : ablocks ?B ?lyc ?S2 = ablocks ?B ?lyc ?Sc,
  EF : ?F = frame_addr ?lyc 1 ?fpos, EFL : ?FL = flag_addr ?lyc 1 ?fpos,
  FFL : frame_flag_lawP _ ?B, LAWS : AR_laws _ ?B, Hoimg : off_img ?o 36,
  B33 : bv_unsigned (ew _ 33) = ?sp1 |- _ =>
  let Hw := fresh "Hw" in let KP' := fresh "KP" in
  assert (Hw : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) a) by pzN_win;
  pose proof (pz_kept_own B LAWS lyc Sc S2 W memc mdc _ _ mA mB slo sp o fpos F FL
  (fun a => (sp1 <= a < sp) \/ (o <= a < o + 36) \/ pz_nf F FL a) HAR HARc Hfrs2 Eab EF EFL FFL
  ltac:(lia) ltac:(lia) Hoimg
  ltac:(intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha])
  KP (kept_of_frame _ _ _ _ _ _ HFr Hw) (fun a Ha => apresent_grows _ _ _ a HG Ha)) as KP';
  clear KP Hw HF HFr HG; rename KP' into KP
end.
(* One run to the next branch or to cut J, and the caller's memory after it. *)
Local Ltac pzN_run :=
lazymatch goal with
| RUNTO : context [sym_run_toN_pi_tok _ _ _ _ _ _ _ _ _], HS : st_ok_pi _ _ _ _ _,
  HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, ?fpos) :: _) _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
  AG : forall n0, (n0 < 33)%nat -> _, EF : ?F = frame_addr _ 1 ?fpos |- _ =>
  paj_run_to_tok RUNTO HS HJ2 SHOK PZspan AF_JOIN; [ awrFL_with ltac:(idtac; pz_awr_hd) AG fpos F I | pzN_kp ]
end.
(* The 36 bytes of the out struct are zero: region 12 still holds the zero chunk of cut M. *)
Local Ltac pzN_zero HZ :=
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?W) ?msv),
  KP : pz_kept _ _ _ _ _ _ _ _ ?o |- _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let ix := idx_of_base rs 12%nat in let ix := eval vm_compute in ix in
  let r := eval vm_compute in (nth ix rs got_regionP) in
  let R12 := fresh "R12" in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msv) ix r HS ltac:(vm_compute; reflexivity)) as R12;
  cbn [ms_mem restrict] in R12;
  assert (HZ : forall j, (j < 36)%nat -> aview SEGS (w_H W) (ms_mem msv) (o + Z.of_nat j) = Some (bv_unsigned cp_z));
  [ let j := fresh "j" in let Hj := fresh "Hj" in let Hb := fresh "Hb" in let Hv := fresh "Hv" in
    intros j Hj;
    assert (Hb : pz_chunk_at Ex (base_val Ex (Some 12%nat)) [YP09.mkChunk 0 (CZero 36)] (Z.of_nat j) = Some (Z_to_bv 8 0))
    by (cbn [pz_chunk_at YP09.c_off YP09.c_len YP09.cv_len YP09.c_val];
        replace ((0 <=? Z.of_nat j) && (Z.of_nat j <? 0 + 36)) with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia);
        reflexivity);
    pose proof (pz_region_byte Ex (w_H W) (ms_mem msv) _ (Z.of_nat j) _ R12 Hb) as Hv;
    revert Hv; cbn [YP09.r_base base_val]; pz_bases; intros Hv; exact Hv
  | clear R12 ]
end.
(* The frame (516) and its shadow (529) become writable again (cut J's windows). *)
Local Ltac pzN_rw :=
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex ?ssx ?msx, E529 : ew ?Ex 529 = _, HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, _) :: _) _ _ _ _ _ _,
  HFSp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 16 -> apresent _ m a |- _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let ix := idx_of_base rs 529%nat in let ix := eval vm_compute in ix in
  let r := eval vm_compute in (nth ix rs got_regionP) in
  let HS' := fresh "HS" in
  pose proof (ast_ok_pi_set_region Ex ssx msx ix r (set_window r 0 16) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 16 (st_ok_pi_region_nth Ex ssx msx ix r HS ltac:(vm_compute; reflexivity))
  ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E529, unsigned_lit_small by (unfold SB; lia);
  let o0 := fresh "o0" in let Ho0 := fresh "Ho0" in
  intros o0 Ho0; apply (apresent_writable _); apply (HFSp _ _ (proj1 HJ2)); lia))) as HS';
  clear HS; rename HS' into HS; pz_norm HS
end;
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex ?ssx ?msx, RF : ew ?Ex 516 = _, HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, _) :: _) _ _ _ _ _ _,
  HFp : forall m md', AR _ _ _ _ _ m md' -> forall a, _ <= a < _ + 128 -> apresent _ m a |- _ =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let ix := idx_of_base rs 516%nat in let ix := eval vm_compute in ix in
  let r := eval vm_compute in (nth ix rs got_regionP) in
  let HS' := fresh "HS" in
  pose proof (ast_ok_pi_set_region Ex ssx msx ix r (set_window r 0 128) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 128 (st_ok_pi_region_nth Ex ssx msx ix r HS ltac:(vm_compute; reflexivity))
  ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite RF, unsigned_lit_small by lia;
  let o0 := fresh "o0" in let Ho0 := fresh "Ho0" in
  intros o0 Ho0; apply (apresent_writable _); apply (HFp _ _ (proj1 HJ2)); lia))) as HS';
  clear HS; rename HS' into HS; pz_norm HS
end.
(* At cut J (0x878c4) with a0 = 0: the state is joined to ss_cutJ and the cut J hypothesis applies. *)
Local Ltac pzN_join :=
let HZ := fresh "HZ" in let R0 := fresh "R0" in let E700 := fresh "E700" in
pzN_zero HZ; pzN_rw;
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
  prreg HS (10%bv : bv 5) R0;
  ra_join HS ss_cutJ 700%nat pz_deadJ ltac:(idtac);
  ra_join_val HS 700%nat 0%nat R0 E700;
  lazymatch goal with AGX : forall n0, (n0 < 512)%nat -> _ |- _ => pz_rebase HS AGX end
end;
lazymatch goal with
| HS : st_ok_pi _ _ ?Ev _ (restrict _ ?msv), Hh : cp_hdr ?n ?fr = false,
  HJc : forall (E : env) (ms : machine_state) (md : Model), _ -> st_ok_pi _ _ E ss_cutJ _ -> _,
  AGX : forall n0, (n0 < 512)%nat -> ew ?Ev n0 = _, RF : ew ?Ev 516 = _, E528 : ew ?Ev 528 = _, E529 : ew ?Ev 529 = _,
  HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ ((1, _) :: _) _ _ _ (ms_mem ?msv) _ _,
  KP : pz_kept _ _ _ _ _ (ms_mem ?msv) _ _ _ |- _ =>
  apply (HJc Ev msv);
  [ split; [assumption|]; split; [exact AGX|]; split; [exact RF|]; split; [exact E528|]; split; [exact E529|];
    split; [exact HJ2 | exact KP]
  | exact HS
  | unfold ctrlparse; rewrite Hh; cbn [fst]; exact E700
  | let j := fresh "j" in let Hj := fresh "Hj" in
    intros j Hj; rewrite (ctrlparse_bytes_none n fr Hh), nth_repeat; exact (HZ j Hj) ]
end.
Lemma pz_segN : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutJ_spec B c ->
pz_cutM_case B c (cp_hdr (cx_n c) (cx_fr c) = false).
Proof.
intros B G RT c Hok HJc Hbig E ms md Hcur HS SHOK Hh.
pz_open c Hok. pz_open_rt RT. pz_open_cur Hcur. pz_open_f Hbig. pz_std.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO. pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
lazymatch type of AGX with forall n0, _ -> ew _ n0 = ew ?E0 n0 =>
assert (AG : forall n0, (n0 < 33)%nat -> ew E n0 = ew E0 n0) by (intros; apply AGX; lia) end.
assert (A11 : ew E 11 = Z_to_bv 64 n) by (rewrite AGX by lia; exact E11).
assert (HFp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, F <= a < F + 128 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & Hp & _).
rewrite <- EF in Hp. change (fs_frame_bytes 1) with 128 in Hp. exact (proj1 (Hp a Ha)). }
assert (HFSp : forall m md', AR SEGS B lyc S2 W m md' -> forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> apresent (w_H W) m a).
{ intros m md' HA a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HA Hfin2) as (_ & _ & _ & Hp).
rewrite <- EF in Hp. unfold shadow_addr in Hp. change (fs_frame_bytes 1 / 8) with 16 in Hp.
replace a with (SHADOW_OFF + F / 8 + (a - (SB + F / 8))) by (unfold SHADOW_OFF, SB; lia).
assert (Hi : 0 <= a - (SB + F / 8) < 16) by (unfold SB in *; lia).
apply (proj1 (Hp (a - (SB + F / 8)) Hi)). }
(* 1. 0x875e4 li a0,50; 0x875e8 bltu s6,a0 -> 0x878bc: len < 50. *)
pzN_run.
psrr_branch_tok RUN BR HS SHOK PZspan.
{ (* len < 50: the short walk's path (CtrlParseShort.v); here 50 <= n refutes it. *)
exfalso. rewrite branch_ltu_U in Hc.
rewrite (U_atom E 11 n A11 ltac:(lia)), U_lit in Hc by lia.
apply Z.ltb_lt in Hc. lia. }
rename Hc into Hc1.
(* 2. The NULL check of f (0x875ec beqz s5 -> 0x87ca0) and the overflow check of f + 12 (0x875f4 bgeu s5,-12
   -> 0x87ca0), which the engine decides from atom 10's fact; the shadow check of frame[12] (0x87608 bnez ->
   0x87ca4), decided from sh_ok; 0x87614 bne frame[12],0x88 -> 0x878bc. *)
pzN_run.
psrr_branch_tok RUN BR HS SHOK PZspan.
{ (* frame[12] <> 0x88: 0x878bc andi a0,s3,3 (0: o is 8-aligned; its bnez to 0x87ca0 decided), to cut J. *)
clear Hc. pzN_run. pzN_join. }
rename Hc into Hc2.
(* 3. The overflow check of f + 13 (0x8761c bltu -14,s5 -> 0x87ca0), decided from atom 10's fact; the shadow
   check of frame[13] (0x87630 bnez -> 0x87cb0), decided from sh_ok; 0x8763c bne frame[13],0x19 -> 0x878bc. *)
pzN_run.
psrr_branch_tok RUN BR HS SHOK PZspan.
{ (* frame[13] <> 0x19: 0x878bc, to cut J. *)
clear Hc. pzN_run. pzN_join. }
rename Hc into Hc3.
(* 4. The accepting path (to the memcpy call at 0x87660): len >= 50, frame[12] = 0x88, frame[13] = 0x19 is the
   header cp_hdr accepts (cp_hdr_spec), against the case hypothesis. *)
exfalso.
rewrite branch_ltu_U in Hc1. rewrite branch_ne_U in Hc2, Hc3.
assert (A52 : ew E 52 = Z_to_bv 64 (cp_v fr 12)) by (rewrite AGX by lia; exact (EFB 12%nat ltac:(lia))).
assert (A53 : ew E 53 = Z_to_bv 64 (cp_v fr 13)) by (rewrite AGX by lia; exact (EFB 13%nat ltac:(lia))).
pose proof (cp_v_range fr 12) as R12. pose proof (cp_v_range fr 13) as R13.
rewrite (U_atom E 11 n A11 ltac:(lia)), U_lit in Hc1 by lia.
rewrite (U_atom E 52 _ A52 ltac:(lia)), U_lit in Hc2 by lia.
rewrite (U_atom E 53 _ A53 ltac:(lia)), U_lit in Hc3 by lia.
apply Z.ltb_ge in Hc1. apply negb_false_iff, Z.eqb_eq in Hc2. apply negb_false_iff, Z.eqb_eq in Hc3.
assert (Hacc : cp_hdr n fr = true) by (apply cp_hdr_spec; lia).
congruence.
Qed.
End d.
End b.

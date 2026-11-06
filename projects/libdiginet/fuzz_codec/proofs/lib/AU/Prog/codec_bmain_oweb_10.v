(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_rd13.v, with its module paths and module names changed; 18 of its 49 lines of code are new or changed and 192 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe9.v, with its module paths and module names changed; 518 of its 554 lines of code are new or changed and 13 lines of the source are left out. *)
(* Segment OWE10 of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v seg_owe 10): owe()'s
   COUNTER case, from the cut OWE10 (owe_pc 10 = 0x82c8c) to CHK 0x82dd4. It is the image-A segment
   (lib/A/Prog/codec_amain_owe10.v) at image B.
     0x82c8c-0x82c94  lw a0,28(s7); bltu 127,a0 -> 0x82dc8             b > 127: want_rc = -11
     0x82c98-0x82cb0  the test loop over k.bytes[0 .. 8) (ld 120(s1) = F + 232): lb; bltz -> 0x82dc8
     0x82cb4-0x82cbc  the UBSan tests of the desk pointer s6 (NULL, not 8-aligned; trap edges 0x82cb4 / 0x82cbc of
                      codec_bmain_inv.v bm_trap_taken), decided by the engine from the desk's atom fact
     0x82cc0-0x82d50  desk + 11 (counter) with its instrumented check (s9 its shadow byte's address), pl[10] at
                      206(sp1) = [counter; b; bytes[7] .. bytes[0]] (the copy loop reads ld 16(s1) = F + 239
                      backward), desk + 8 (dev), want[0..2) = 0x13f0, want[2] = dev, want[3] = 0x30
     0x82d5c          the checked copy (want + 4, sp1 + 206, 10)
     0x82d60-0x82d94  the UBSan test of want + 14 (trap edge 0x82d68, decided: want lies far below 2^64 - 14),
                      want[14] = 0xf7, want_len = 15, want_display = 1, desk + 11 again, the key
     0x82a0c-0x82a10  want_key = counter | 0x60000; 0x82dd0 s9 = 128(s1); CHK
     0x82dc8-0x82dd0  the error path: want_rc = -11
   The executor runs from the start state of lib/AU/Prog/codec_bmain_st.v's bm_entry with the regions and atoms of
   lib/AU/Prog/codec_bmain_oweb_10l.v; each undecided test is split (cw_branch) and its condition read back on the
   atoms; the error paths end through o10_err_fin; the success path adds want[0..4), want[14] and pl after the loop,
   calls the checked copy through CPgWalkIntrU's cw_intrin_call (the source pl on the machine stack, whose shadow is
   zero: CPgWalkFrameU's cw_stack_src) and ends through codec_bmain_owex.v's owex_chk. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkIntrU CPgWalkFrameU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_owel codec_bmain_owex codec_bmain_oweb_10l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the write premise of a run: codec_bmain_owel.v's owe_awr, with its arguments found in the context *)
Ltac o10_awr :=
  idtac;
  let U2 := lazymatch goal with H : bv_unsigned (ew _ 2) = _ |- _ => H end in
  let sp1 := lazymatch type of U2 with _ = ?s => s end in
  let U33 := lazymatch goal with H : bv_unsigned (ew _ 33) = FA _ _ |- _ => H end in
  let F := lazymatch type of U33 with _ = ?f => f end in
  let pos := lazymatch type of U33 with _ = FA _ ?p => p end in
  let EFA := lazymatch goal with H : frame_addr _ 3 _ = FA _ _ |- _ => H end in
  let spz := lazymatch goal with |- awr_ok _ _ _ ?s _ _ _ _ _ => s end in
  owe_awr sp1 spz pos F U2 U33 EFA.
(* the zone of the windows, for cw_keep (zone: owe_zone .. 0, o10_zs1 or o10_zs2) *)
Ltac o10_kwr zone :=
  idtac;
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
      repeat match goal with U : bv_unsigned (ew _ ?n) = _, Hb' : context [bv_unsigned (ew _ ?n)] |- _ =>
        rewrite U in Hb' end;
      unfold zone; try unfold o10_zs2; lia | ]);
  destruct Hr.
(* the extents of a region added to the state are apart from the state's regions *)
Ltac o10_dj :=
  idtac;
  cbn [all_disjoint]; unfold extent_disjoint, o10_rd, o10_re, o10_rh, o10_rg; unfold owe_desk_region, bm_frame_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  repeat match goal with U : bv_unsigned (ew _ ?n) = _ |- context [bv_unsigned (ew _ ?n)] => rewrite U end;
  repeat split; lia.
(* add the region r to the state: tok proves it ok in the current memory, tdj its disjointness *)
Ltac o10_add r tok tdj :=
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict (w_H ?W) ?msv) |- _ =>
    let HS' := fresh "HS" in
    pose proof (ast_ok_add_region tfibsegs Ev ssv (restrict (w_H W) msv) r HS eq_refl) as HS';
    lazymatch type of HS' with ?A -> ?B -> _ =>
      let X1 := fresh "X" in let X2 := fresh "X" in
      assert (X1 : A) by (cbn [ms_mem restrict]; tok);
      assert (X2 : B) by (let l := eval vm_compute in (ss_mem ssv) in change (all_disjoint Ev r l); tdj);
      specialize (HS' X1 X2); clear X1 X2 end;
    clear HS; rename HS' into HS end.
(* the stopped state as a configuration (lib/A/Prog/codec_bmain_latch.v's lt_shape) *)
Ltac o10_shape pc :=
  lazymatch goal with HS : st_ok _ _ ?ssx (restrict (w_H ?W2) ?msx) |- _ =>
    let Hpc := fresh "Hpc" in let Hshape := fresh "Hshape" in
    assert (Hpc : ss_pc ssx = pc) by (vm_compute; reflexivity);
    pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) _ ssx msx HS eq_refl) as Hshape;
    rewrite Hpc in Hshape; rewrite Hshape in HS |- *; clear Hpc Hshape end.
(* sv_denot of an atom *)
Ltac o10_den En :=
  rewrite (bm_den_off _ _ _ 0 En) by lia; rewrite Z.add_0_r; reflexivity.
(* a register of the stopped state as the denotation of its sv (st_ok_restrict_reg, the sv computed) *)
Ltac o10_reg HS r R :=
  pose proof (st_ok_restrict_reg tfibsegs _ _ _ _ r HS) as R;
  lazymatch type of R with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in R end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy BM_asan_memcpy.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.

(* the error path from a test that failed, to CHK *)
Ltac o10_err why HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE :=
  cw_run_to o10_awr 0x82dd4;
  cw_keep ltac:(o10_kwr owe_zone);
  o10_shape PC_CHK;
  eapply (o10_err_fin B MT K XM_LIB LAWS);
  [ exact HJ0 | exact Hfr | exact Hk | exact Hmo | exact HC | exact Hops | exact Hcur | exact Hkat | exact Hrec
  | exact Hrc | eassumption | env_agree_chain HAE | eassumption | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | eassumption | why ].

Theorem seg_owe10_holds : seg_owe B MT K XM_LIB 10.
Proof using TL LAWS AMEMCPY GM IV ROB.
unfold seg_owe. intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hk & Hmo & HC &
  (Hops & Hkr & c & k & od & Hcur & Hkat & Hrec & Hkind & Hod & Hrc & Hwrc & Hwl & Hwk & Hwd & R22)).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct od as [d|]; [| exfalso; destruct (Hod eq_refl) as [X | [X | X]]; lia].
pose proof Hrec as (_ & Hpd & Hrdr & _).
destruct (pd_range_B _ _ _ Hpd) as (_ & Hdv & Rdev & Rstr & Rchr & Rctr).
pose proof (owe_desk_range _ _ _ Hpd) as Hdr.
pose proof Hrdr as (Ra & Rb & Rcc & Rdl & Rlen & Rby & Rn & _ & Rb8 & _). specialize (Rb8 Hkind).
pose proof Hkat as ((Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gby & Vn & Vrc & Gbef & Gout & Vwrc & Gwant &
  Vwl & Vwk & Vwd) & Hwf).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
unfold BM_HI in Hchi. change (fs_frame_bytes 3) with 512 in Hfceil.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HC as (Hpre & _ & R2 & _).
pose proof (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 kj Hpre HJ) as HRO.
(* the bytes k.bytes[0 .. 8) *)
assert (BY : forall j, (j < 8)%nat ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + (232 + Z.of_nat j)) 1 (nth j (kz_bytes k) 0) /\
  0 <= nth j (kz_bytes k) 0 < 256).
{ intros j Hj. destruct (Gby j ltac:(lia)) as [G1 G2]. split; [|exact G2].
  replace (FA g pos + (232 + Z.of_nat j)) with (FA g pos + 192 + 40 + Z.of_nat j) by lia. exact G1. }
pose proof (BY 0%nat ltac:(lia)) as (_ & B0). pose proof (BY 1%nat ltac:(lia)) as (_ & B1).
pose proof (BY 2%nat ltac:(lia)) as (_ & B2). pose proof (BY 3%nat ltac:(lia)) as (_ & B3).
pose proof (BY 4%nat ltac:(lia)) as (_ & B4). pose proof (BY 5%nat ltac:(lia)) as (_ & B5).
pose proof (BY 6%nat ltac:(lia)) as (_ & B6). pose proof (BY 7%nat ltac:(lia)) as (_ & B7).
(* the environment *)
set (ys := o10_ys k d).
remember (bm_env g pos c regs2 ys) as E eqn:HEE.
assert (HAE : env_agree 37 (bm_env g pos c regs2 ys) E) by (subst E; apply env_agree_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (kz_b k)) by (subst E; exact (bm_ew_y g pos c regs2 ys 0)).
assert (E38 : ew E 38 = Z_to_bv 64 (nth 0 (kz_bytes k) 0)) by (subst E; exact (bm_ew_y g pos c regs2 ys 1)).
assert (E39 : ew E 39 = Z_to_bv 64 (nth 1 (kz_bytes k) 0)) by (subst E; exact (bm_ew_y g pos c regs2 ys 2)).
assert (E40 : ew E 40 = Z_to_bv 64 (nth 2 (kz_bytes k) 0)) by (subst E; exact (bm_ew_y g pos c regs2 ys 3)).
assert (E41 : ew E 41 = Z_to_bv 64 (nth 3 (kz_bytes k) 0)) by (subst E; exact (bm_ew_y g pos c regs2 ys 4)).
assert (E42 : ew E 42 = Z_to_bv 64 (nth 4 (kz_bytes k) 0)) by (subst E; exact (bm_ew_y g pos c regs2 ys 5)).
assert (E43 : ew E 43 = Z_to_bv 64 (nth 5 (kz_bytes k) 0)) by (subst E; exact (bm_ew_y g pos c regs2 ys 6)).
assert (E44 : ew E 44 = Z_to_bv 64 (nth 6 (kz_bytes k) 0)) by (subst E; exact (bm_ew_y g pos c regs2 ys 7)).
assert (E45 : ew E 45 = Z_to_bv 64 (nth 7 (kz_bytes k) 0)) by (subst E; exact (bm_ew_y g pos c regs2 ys 8)).
assert (E46 : ew E 46 = Z_to_bv 64 (d_dev d)) by (subst E; exact (bm_ew_y g pos c regs2 ys 9)).
assert (E47 : ew E 47 = Z_to_bv 64 (d_strips d)) by (subst E; exact (bm_ew_y g pos c regs2 ys 10)).
assert (E48 : ew E 48 = Z_to_bv 64 (d_chars d)) by (subst E; exact (bm_ew_y g pos c regs2 ys 11)).
assert (E49 : ew E 49 = Z_to_bv 64 (d_counter d)) by (subst E; exact (bm_ew_y g pos c regs2 ys 12)).
assert (E22 : ew E 22 = Z_to_bv 64 (kz_desk k))
  by (subst E; rewrite (bm_ew_reg g pos c regs2 ys 22 22%bv eq_refl), R22; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (subst E; exact (bm_ew_F g pos c regs2 ys)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (bm_ew_SB g pos c regs2 ys)).
assert (U2 : bv_unsigned (ew E 2) = sp1)
  by (subst E; rewrite (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = FA g pos) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = kz_desk k) by (rewrite E22; apply unsigned_lit_small; lia).
(* the start state *)
assert (Hap : FA g pos + 376 <= kz_desk k + 8 \/ kz_desk k + 8 + 4 <= FA g pos + 220).
{ pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos (kz_desk k + 8) 4 220 376 HAR Hin) as G.
  rewrite EFA in G. change (fs_frame_bytes 3) with 512 in G. apply G; lia. }
assert (HRS : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) o10_rs).
{ unfold o10_rs. repeat apply Forall_cons; try apply Forall_nil.
  - rewrite HEE. apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 220 240 220 220
      _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite <- HEE.
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 220 4 (SOff 37 0) (kz_b k)); [o10_den E37 | cbn; lia | cbn; lia |].
      replace (FA g pos + 220) with (FA g pos + 192 + 28) by lia. exact Vb.
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 232 1 (SOff 38 0) (nth 0 (kz_bytes k) 0));
      [o10_den E38 | cbn; pose proof (BY 0%nat ltac:(lia)); lia | cbn; lia | exact (proj1 (BY 0%nat ltac:(lia)))].
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 233 1 (SOff 39 0) (nth 1 (kz_bytes k) 0));
      [o10_den E39 | cbn; pose proof (BY 1%nat ltac:(lia)); lia | cbn; lia | exact (proj1 (BY 1%nat ltac:(lia)))].
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 234 1 (SOff 40 0) (nth 2 (kz_bytes k) 0));
      [o10_den E40 | cbn; pose proof (BY 2%nat ltac:(lia)); lia | cbn; lia | exact (proj1 (BY 2%nat ltac:(lia)))].
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 235 1 (SOff 41 0) (nth 3 (kz_bytes k) 0));
      [o10_den E41 | cbn; pose proof (BY 3%nat ltac:(lia)); lia | cbn; lia | exact (proj1 (BY 3%nat ltac:(lia)))].
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 236 1 (SOff 42 0) (nth 4 (kz_bytes k) 0));
      [o10_den E42 | cbn; pose proof (BY 4%nat ltac:(lia)); lia | cbn; lia | exact (proj1 (BY 4%nat ltac:(lia)))].
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 237 1 (SOff 43 0) (nth 5 (kz_bytes k) 0));
      [o10_den E43 | cbn; pose proof (BY 5%nat ltac:(lia)); lia | cbn; lia | exact (proj1 (BY 5%nat ltac:(lia)))].
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 238 1 (SOff 44 0) (nth 6 (kz_bytes k) 0));
      [o10_den E44 | cbn; pose proof (BY 6%nat ltac:(lia)); lia | cbn; lia | exact (proj1 (BY 6%nat ltac:(lia)))].
    + apply (chunk_ok_val tfibsegs E _ (FA g pos) 239 1 (SOff 45 0) (nth 7 (kz_bytes k) 0));
      [o10_den E45 | cbn; pose proof (BY 7%nat ltac:(lia)); lia | cbn; lia | exact (proj1 (BY 7%nat ltac:(lia)))].
  - subst E. apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 332 336 332 336
      _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val tfibsegs _ _ (FA g pos) 332 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    replace (FA g pos + 332) with (FA g pos + 192 + 140) by lia. rewrite <- Hwrc. exact Vwrc.
  - subst E. apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 360 376 360 376
      _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val tfibsegs _ _ (FA g pos) 360 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      replace (FA g pos + 360) with (FA g pos + 192 + 168) by lia. rewrite <- Hwl. exact Vwl.
    + apply (chunk_ok_val tfibsegs _ _ (FA g pos) 368 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      replace (FA g pos + 368) with (FA g pos + 192 + 176) by lia. rewrite <- Hwk. exact Vwk.
    + apply (chunk_ok_val tfibsegs _ _ (FA g pos) 372 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      replace (FA g pos + 372) with (FA g pos + 192 + 180) by lia. rewrite <- Hwd. exact Vwd.
  - apply (owe_desk_region_ok B TL E W2 mem2 (kz_p k) (kz_desk k) d _ HRO Hpd U22).
    intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth desk_bytesZ];
    [o10_den E46 | o10_den E47 | o10_den E48 | o10_den E49 | lia]. }
assert (HPD : pairwise_disjoint E o10_rs).
{ unfold o10_rs, o10_rk, o10_rc, o10_rf, o10_rg, owe_desk_region, bm_frame_region.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U33, U22. repeat split; lia. }
assert (HAP : Forall (fun r => all_disjoint E r bm_regs) o10_rs).
{ unfold o10_rs. rewrite HEE. repeat apply Forall_cons; try apply Forall_nil.
  - exact (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 220 240 220 220 _
      HJ Hfr HC ltac:(lia) ltac:(lia)).
  - exact (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 332 336 332 336 _
      HJ Hfr HC ltac:(lia) ltac:(lia)).
  - exact (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 360 376 360 376 _
      HJ Hfr HC ltac:(lia) ltac:(lia)).
  - rewrite <- HEE. exact (owe_desk_apart_base E _ (kz_desk k) sp1 U22 Hdr U2 ltac:(lia)). }
assert (HAF : atoms_ok E o10_AF).
{ unfold o10_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E22, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49.
  rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  destruct Hdv as [Hd1 | Hd1]; rewrite Hd1; repeat split; first [reflexivity | lia]. }
pose proof (bm_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c 0x82c8c ys o10_rs o10_AF
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity)) as HS.
rewrite <- HEE in HS. specialize (HS HRS HPD HAP HAF).
assert (SHOK : sh_ok tfibsegs CW_Bx o10_SH E (mrestrict (w_H W2) mem2)).
{ unfold o10_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (owe_desk_shent B ly2 S2 W2 mem2 md2 E (kz_p k) (kz_desk k) d GM IV HAR Hpd E22 E32).
  - subst E. exact (owe_k_shent B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 kj c ys HJ Hfr HC). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ owe_zone g pos sp1 0 a ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
unfold cfg_at. change (w64 (owe_pc 10)) with (Z_to_bv 64 0x82c8c).
cw_keep_j0 HJ HJ0.
(* 0x82c8c-0x82c94: lw b, bltu 127,b *)
cw_run o10_awr.
cw_keep ltac:(o10_kwr owe_zone).
cw_branch Hb1. all: rewrite (o10_br_b _ 37 (kz_b k) E37 ltac:(lia)) in Hb1.
{ apply Z.ltb_lt in Hb1.
  o10_err ltac:(unfold owe_kZ; rewrite Hkind; apply owe10_rng_b; lia) HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE. }
apply Z.ltb_ge in Hb1.
(* the test loop *)
(* byte 0 *)
cw_run o10_awr. cw_keep ltac:(o10_kwr owe_zone).
cw_branch Hb.
all: rewrite (o10_br_sx8 _ 38 (nth 0 (kz_bytes k) 0) E38 ltac:(exact (proj2 (BY 0%nat ltac:(lia))))) in Hb.
{ apply Z.ltb_lt in Hb.
  o10_err ltac:(unfold owe_kZ; rewrite Hkind; apply owe10_rng_s; exact (o10_sb_false (kz_bytes k) 0 Rlen Rby ltac:(lia) Hb))
    HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE. }
apply Z.ltb_ge in Hb. rename Hb into Hby0.
(* byte 1 *)
cw_run o10_awr. cw_keep ltac:(o10_kwr owe_zone).
cw_branch Hb.
all: rewrite (o10_br_sx8 _ 39 (nth 1 (kz_bytes k) 0) E39 ltac:(exact (proj2 (BY 1%nat ltac:(lia))))) in Hb.
{ apply Z.ltb_lt in Hb.
  o10_err ltac:(unfold owe_kZ; rewrite Hkind; apply owe10_rng_s; exact (o10_sb_false (kz_bytes k) 1 Rlen Rby ltac:(lia) Hb))
    HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE. }
apply Z.ltb_ge in Hb. rename Hb into Hby1.
(* byte 2 *)
cw_run o10_awr. cw_keep ltac:(o10_kwr owe_zone).
cw_branch Hb.
all: rewrite (o10_br_sx8 _ 40 (nth 2 (kz_bytes k) 0) E40 ltac:(exact (proj2 (BY 2%nat ltac:(lia))))) in Hb.
{ apply Z.ltb_lt in Hb.
  o10_err ltac:(unfold owe_kZ; rewrite Hkind; apply owe10_rng_s; exact (o10_sb_false (kz_bytes k) 2 Rlen Rby ltac:(lia) Hb))
    HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE. }
apply Z.ltb_ge in Hb. rename Hb into Hby2.
(* byte 3 *)
cw_run o10_awr. cw_keep ltac:(o10_kwr owe_zone).
cw_branch Hb.
all: rewrite (o10_br_sx8 _ 41 (nth 3 (kz_bytes k) 0) E41 ltac:(exact (proj2 (BY 3%nat ltac:(lia))))) in Hb.
{ apply Z.ltb_lt in Hb.
  o10_err ltac:(unfold owe_kZ; rewrite Hkind; apply owe10_rng_s; exact (o10_sb_false (kz_bytes k) 3 Rlen Rby ltac:(lia) Hb))
    HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE. }
apply Z.ltb_ge in Hb. rename Hb into Hby3.
(* byte 4 *)
cw_run o10_awr. cw_keep ltac:(o10_kwr owe_zone).
cw_branch Hb.
all: rewrite (o10_br_sx8 _ 42 (nth 4 (kz_bytes k) 0) E42 ltac:(exact (proj2 (BY 4%nat ltac:(lia))))) in Hb.
{ apply Z.ltb_lt in Hb.
  o10_err ltac:(unfold owe_kZ; rewrite Hkind; apply owe10_rng_s; exact (o10_sb_false (kz_bytes k) 4 Rlen Rby ltac:(lia) Hb))
    HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE. }
apply Z.ltb_ge in Hb. rename Hb into Hby4.
(* byte 5 *)
cw_run o10_awr. cw_keep ltac:(o10_kwr owe_zone).
cw_branch Hb.
all: rewrite (o10_br_sx8 _ 43 (nth 5 (kz_bytes k) 0) E43 ltac:(exact (proj2 (BY 5%nat ltac:(lia))))) in Hb.
{ apply Z.ltb_lt in Hb.
  o10_err ltac:(unfold owe_kZ; rewrite Hkind; apply owe10_rng_s; exact (o10_sb_false (kz_bytes k) 5 Rlen Rby ltac:(lia) Hb))
    HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE. }
apply Z.ltb_ge in Hb. rename Hb into Hby5.
(* byte 6 *)
cw_run o10_awr. cw_keep ltac:(o10_kwr owe_zone).
cw_branch Hb.
all: rewrite (o10_br_sx8 _ 44 (nth 6 (kz_bytes k) 0) E44 ltac:(exact (proj2 (BY 6%nat ltac:(lia))))) in Hb.
{ apply Z.ltb_lt in Hb.
  o10_err ltac:(unfold owe_kZ; rewrite Hkind; apply owe10_rng_s; exact (o10_sb_false (kz_bytes k) 6 Rlen Rby ltac:(lia) Hb))
    HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE. }
apply Z.ltb_ge in Hb. rename Hb into Hby6.
(* byte 7 *)
cw_run o10_awr. cw_keep ltac:(o10_kwr owe_zone).
cw_branch Hb.
all: rewrite (o10_br_sx8 _ 45 (nth 7 (kz_bytes k) 0) E45 ltac:(exact (proj2 (BY 7%nat ltac:(lia))))) in Hb.
{ apply Z.ltb_lt in Hb.
  o10_err ltac:(unfold owe_kZ; rewrite Hkind; apply owe10_rng_s; exact (o10_sb_false (kz_bytes k) 7 Rlen Rby ltac:(lia) Hb))
    HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Hrec Hrc HAE. }
apply Z.ltb_ge in Hb. rename Hb into Hby7.
(* the success path: the zone widens to want[0 .. 4), want[14] and pl; their regions join the state *)
assert (Hby : forall j, (j < 8)%nat -> nth j (kz_bytes k) 0 <= 127).
{ intros j Hj. destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; first [lia | exfalso; lia]. }
lazymatch type of KE with forall a, _ -> ~ _ -> aview _ (w_H W2) ?m a = _ =>
  assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> ~ o10_zs1 g pos sp1 a ->
    aview tfibsegs (w_H W2) m a = aview tfibsegs (w_H W2) mem2 a)
  by (intros a Ha Hz; apply KE; [exact Ha | intros Hz'; apply Hz; unfold o10_zs1, o10_zs2, owe_zone in *; lia]) end.
clear KE. rename KE1 into KE.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & _).
assert (G1 : FA g pos + 376 <= A_GOT_shadow \/ A_GOT_shadow + 8 <= FA g pos + 220).
{ pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos A_GOT_shadow 8 220 376 HAR Hin) as G.
  rewrite EFA in G. change (fs_frame_bytes 3) with 512 in G. unfold A_GOT_shadow in *. apply G; lia. }
assert (G2 : FA g pos + 376 <= A_shadow_glob \/ A_shadow_glob + 8 <= FA g pos + 220).
{ pose proof (owe_img_frame_apart B LAWS ly2 S2 W2 mem2 md2 3 pos A_shadow_glob 8 220 376 HAR Hin) as G.
  rewrite EFA in G. change (fs_frame_bytes 3) with 512 in G. unfold A_shadow_glob in *. apply G; lia. }
unfold A_GOT_shadow, A_shadow_glob in G1, G2.
o10_add o10_rd
  ltac:(apply (o10_fwin_ok B LAWS E W2 _ ly2 S2 _ pos 336 340 336 340 HARc Hin ltac:(rewrite EFA; exact U33)); lia)
  ltac:(o10_dj).
o10_add o10_re
  ltac:(apply (o10_fwin_ok B LAWS E W2 _ ly2 S2 _ pos 350 351 350 351 HARc Hin ltac:(rewrite EFA; exact U33)); lia)
  ltac:(o10_dj).
o10_add o10_rh
  ltac:(apply (o10_swin_ok E W2 _ sp1 206 216 U2); [intros a Ha; apply Hpresc; lia | lia | lia | lia])
  ltac:(o10_dj).
(* 0x82cb4-0x82d5c: the UBSan tests of the desk pointer (decided by the engine from its atom fact), desk + 11, pl,
   desk + 8, want[0 .. 4), the arguments, to the checked copy *)
cw_run_to o10_awr 0x51ae8. cw_keep ltac:(o10_kwr o10_zs1).
(* at the checked copy 0x51ae8: a0 = want + 4 = F + 340, a1 = pl = sp1 + 206, a2 = 10, ra = 0x82d60 *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msc) |- _ => rename msc into msC end.
rename KE into KEc.
(* the run's env: E with the fresh atoms of the two shadow loads *)
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ => remember Ev as Ec eqn:HEc in HS end.
assert (XC : forall n, (n < 50)%nat -> ew Ec n = ew E n)
  by (intros n Hn; rewrite HEc; rewrite ?ew_ewset_other by lia; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (E2c : ew Ec 2 = Z_to_bv 64 sp1)
  by (rewrite XC by lia; rewrite HEE, (bm_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2; reflexivity).
assert (U2c : bv_unsigned (ew Ec 2) = sp1) by (rewrite XC by lia; exact U2).
assert (U33c : bv_unsigned (ew Ec 33) = FA g pos) by (rewrite XC by lia; exact U33).
assert (E33c : ew Ec 33 = Z_to_bv 64 (FA g pos)) by (rewrite XC by lia; exact E33).
assert (E37c : ew Ec 37 = Z_to_bv 64 (kz_b k)) by (rewrite XC by lia; exact E37).
assert (E38c : ew Ec 38 = Z_to_bv 64 (nth 0 (kz_bytes k) 0)) by (rewrite XC by lia; exact E38).
assert (E39c : ew Ec 39 = Z_to_bv 64 (nth 1 (kz_bytes k) 0)) by (rewrite XC by lia; exact E39).
assert (E40c : ew Ec 40 = Z_to_bv 64 (nth 2 (kz_bytes k) 0)) by (rewrite XC by lia; exact E40).
assert (E41c : ew Ec 41 = Z_to_bv 64 (nth 3 (kz_bytes k) 0)) by (rewrite XC by lia; exact E41).
assert (E42c : ew Ec 42 = Z_to_bv 64 (nth 4 (kz_bytes k) 0)) by (rewrite XC by lia; exact E42).
assert (E43c : ew Ec 43 = Z_to_bv 64 (nth 5 (kz_bytes k) 0)) by (rewrite XC by lia; exact E43).
assert (E44c : ew Ec 44 = Z_to_bv 64 (nth 6 (kz_bytes k) 0)) by (rewrite XC by lia; exact E44).
assert (E45c : ew Ec 45 = Z_to_bv 64 (nth 7 (kz_bytes k) 0)) by (rewrite XC by lia; exact E45).
assert (E49c : ew Ec 49 = Z_to_bv 64 (d_counter d)) by (rewrite XC by lia; exact E49).
pose proof HC as (_ & _ & _ & _ & _ & R3 & R4 & _).
pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof (owe_frame_app B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ0 Hfr HC) as Happ.
assert (D8 : 0 <= FA g pos / 8 /\ 8 * (FA g pos / 8) <= FA g pos)
  by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
o10_reg HS (10%bv : bv 5) Rg10. o10_reg HS (11%bv : bv 5) Rg11. o10_reg HS (12%bv : bv 5) Rg12.
o10_reg HS (2%bv : bv 5) Rg2. o10_reg HS (3%bv : bv 5) Rg3. o10_reg HS (4%bv : bv 5) Rg4.
rewrite (bm_den_off Ec 33 (FA g pos) 340 E33c) in Rg10 by lia.
rewrite (bm_den_off Ec 2 sp1 206 E2c) in Rg11 by lia.
cbn [sv_denot] in Rg12.
rewrite (bm_den_off Ec 2 sp1 0 E2c), Z.add_0_r in Rg2 by lia.
assert (Hspc : spZ (ms_regs msC) = sp1) by (unfold spZ; rewrite Rg2; apply unsigned_lit_small; lia).
assert (G3 : getr (ms_regs msC) 3 = w64 (as_gp B)).
{ rewrite Rg3. cbn [sv_denot]. rewrite (XC 3%nat) by lia.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, HEE, (bm_ew_reg g pos c regs2 ys 3 3%bv eq_refl). exact R3. }
assert (G4 : getr (ms_regs msC) 4 = w64 (as_tp B)).
{ rewrite Rg4. cbn [sv_denot]. rewrite (XC 4%nat) by lia.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, HEE, (bm_ew_reg g pos c regs2 ys 4 4%bv eq_refl). exact R4. }
(* the frame's shadow bytes at the call, k's marks, want[4 .. 14) usable *)
assert (SHc : forall i, 0 <= i < 60 ->
  aview tfibsegs (w_H W2) (ms_mem msC) (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm 0) 0)).
{ intros i Hi. rewrite KEc; [exact (HSH i Hi) | unfold shadow_addr, SHADOW_OFF; lia
  | unfold o10_zs1, o10_zs2, shadow_addr, SHADOW_OFF; appn; lia]. }
pose proof (o10_bs_k W2 (ms_mem msC) (FA g pos) Hf64 SHc) as HBSc.
pose proof (block_shadow_range (aview tfibsegs (w_H W2) (ms_mem msC)) SHADOW_OFF (FA g pos + 192) 184
  (FA g pos + 340) 10 HBSc ltac:(lia) ltac:(lia)) as RAd.
pose proof (o10_hull (aview tfibsegs (w_H W2) (ms_mem msC)) (FA g pos) Hf64 ltac:(lia)
  ltac:(intros i Hi; rewrite (SHc i Hi); discriminate)) as HVd.
assert (Hamd : amem_range (FA g pos + 340) 10) by (appn; lia).
(* the source pl on the machine stack *)
destruct (cw_stack_src B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem msC) _ kj (sp1 + 206) 10 LAWS HJ ltac:(lia) ltac:(lia) ltac:(lia)) as (Hams & RAs & HVs & Hpvs).
(* pl's ten bytes at the call, from the region rh (index 0 of the state) *)
owe_region HS 0%nat Hrh. cbn [ms_mem restrict] in Hrh.
lazymatch type of Hrh with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
  assert (PB : forall off n v, In (YP09.mkChunk off (CVal 1 (SOff n 0))) cs -> ew Ec n = Z_to_bv 64 v -> 0 <= v < 256 ->
    aview tfibsegs (w_H W2) (ms_mem msC) (sp1 + off) = Some v)
  by (intros off n v Hic Hn Hv; apply o10_aview_vm1; [|exact Hv];
      exact (field_of_region Ec _ 2%nat sp1 cs 206 216 206 216 off 1 (SOff n 0) v Hrh U2c Hic ltac:(o10_den Hn)
        ltac:(cbn; lia) ltac:(lia))) end.
assert (Hpl : forall i, 0 <= i < 10 ->
  aview tfibsegs (w_H W2) (ms_mem msC) (sp1 + 206 + i) = Some (nth (Z.to_nat i) (o10_pl k d) 0)).
{ intros i Hi.
  assert (Ei : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
  destruct Ei as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
  - change (nth (Z.to_nat 0) (o10_pl k d) 0) with (d_counter d).
    replace (sp1 + 206 + 0) with (sp1 + 206) by lia. apply (PB 206 49%nat); [owe_in | exact E49c | lia].
  - change (nth (Z.to_nat 1) (o10_pl k d) 0) with (kz_b k).
    replace (sp1 + 206 + 1) with (sp1 + 207) by lia. apply (PB 207 37%nat); [owe_in | exact E37c | lia].
  - change (nth (Z.to_nat 2) (o10_pl k d) 0) with (nth 7 (kz_bytes k) 0).
    replace (sp1 + 206 + 2) with (sp1 + 208) by lia. apply (PB 208 45%nat); [owe_in | exact E45c | lia].
  - change (nth (Z.to_nat 3) (o10_pl k d) 0) with (nth 6 (kz_bytes k) 0).
    replace (sp1 + 206 + 3) with (sp1 + 209) by lia. apply (PB 209 44%nat); [owe_in | exact E44c | lia].
  - change (nth (Z.to_nat 4) (o10_pl k d) 0) with (nth 5 (kz_bytes k) 0).
    replace (sp1 + 206 + 4) with (sp1 + 210) by lia. apply (PB 210 43%nat); [owe_in | exact E43c | lia].
  - change (nth (Z.to_nat 5) (o10_pl k d) 0) with (nth 4 (kz_bytes k) 0).
    replace (sp1 + 206 + 5) with (sp1 + 211) by lia. apply (PB 211 42%nat); [owe_in | exact E42c | lia].
  - change (nth (Z.to_nat 6) (o10_pl k d) 0) with (nth 3 (kz_bytes k) 0).
    replace (sp1 + 206 + 6) with (sp1 + 212) by lia. apply (PB 212 41%nat); [owe_in | exact E41c | lia].
  - change (nth (Z.to_nat 7) (o10_pl k d) 0) with (nth 2 (kz_bytes k) 0).
    replace (sp1 + 206 + 7) with (sp1 + 213) by lia. apply (PB 213 40%nat); [owe_in | exact E40c | lia].
  - change (nth (Z.to_nat 8) (o10_pl k d) 0) with (nth 1 (kz_bytes k) 0).
    replace (sp1 + 206 + 8) with (sp1 + 214) by lia. apply (PB 214 39%nat); [owe_in | exact E39c | lia].
  - change (nth (Z.to_nat 9) (o10_pl k d) 0) with (nth 0 (kz_bytes k) 0).
    replace (sp1 + 206 + 9) with (sp1 + 215) by lia. apply (PB 215 38%nat); [owe_in | exact E38c | lia]. }
clear PB Hrh.
(* the call: cw_intrin_call keeps want_rc, want[0 .. 4), want[14], want_len .. want_display, the cursor and the
   spills (o10_spill, which the walk reads after the call) *)
lazymatch goal with HS : st_ok _ _ ?ssv _ |- _ =>
  let l := eval vm_compute in (ss_mem ssv) in
  let rsC := eval vm_compute in
    (map (fun i => nth i l o10_rh) [1; 2]%nat ++ [o10_spill] ++ map (fun i => nth i l o10_rh) [7; 9; 10]%nat) in
  let kk := eval vm_compute in (run_K 50 (SOff 32 0) o10_SH ssv) in
  eapply (cw_intrin_call B LAWS OCpy BM_asan_memcpy AMEMCPY W2 _ _ msC _ LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
    (e_mem g) (e_md g) [(3, pos)] ly2 S2 kj (FA g pos + 340) (sp1 + 206) 10 0x82d60 kk rsC _ HS) end.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact HJ.
- exact Rg10.
- exact Rg11.
- exact Rg12.
- lia.
- lia.
- lia.
- rewrite Hspc, Hes. lia.
- rewrite Hspc. lia.
- rewrite Hspc. pose proof (Z.div_mod sp1 32 ltac:(lia)) as DM. rewrite Hsp32, Z.add_0_r in DM.
  rewrite DM. replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult.
- exact Hsp016.
- exact G3.
- exact G4.
- vm_compute. reflexivity.
- lia.
- apply ret_ok_even. vm_compute. reflexivity.
- intros a Ha. split.
  + right; right; right. exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
  + rewrite Hspc, Hes. lia.
- exact Hamd.
- exact RAd.
- intros _. exact HVd.
- cbv beta iota. split; [lia|]. split; [lia|]. split.
  { intros a Ha. split; [apply Hpvs; lia | rewrite Hspc, Hes; lia]. }
  split; [lia|]. split; [exact Hams|]. split; [exact RAs | intros _; exact HVs].
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- lazymatch goal with |- submem ?a ?b =>
    let a' := eval vm_compute in a in let b' := eval vm_compute in b in change (submem a' b') end.
  submem_to.
- repeat apply Forall_cons; try apply Forall_nil;
  (split; [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
            repeat match goal with U : bv_unsigned (ew _ ?n) = _, H' : context [bv_unsigned (ew _ ?n)] |- _ =>
              rewrite U in H' end;
            rewrite Hspc, Hes; split; lia
          | cbn; lia ]).
- (* 0x82d60: the state after the call *)
  intros regs3 mem3 md3 HJ3 HP3 Hd3 Hcp Hkp Hpr3 Hsm HS3.
  cbv beta iota in Hcp. rewrite Hspc, Hes in Hkp.
  clear HS SHOK HJ.
  lazymatch type of HS3 with st_ok _ ?Ev _ _ => remember Ev as E3 eqn:HE3 in HS3 end.
  rename HS3 into HS.
  assert (HAE3 : env_agree 37 (bm_env g pos c regs2 ys) E3) by (rewrite HE3, HEc; env_agree_chain HAE).
  assert (X3 : forall n, (n < 50)%nat -> ew E3 n = ew E n)
    by (intros n Hn; rewrite HE3, ew_havoc_old by lia; apply XC; exact Hn).
  assert (U2' : bv_unsigned (ew E3 2) = sp1) by (rewrite X3 by lia; exact U2).
  assert (U33' : bv_unsigned (ew E3 33) = FA g pos) by (rewrite X3 by lia; exact U33).
  assert (U22' : bv_unsigned (ew E3 22) = kz_desk k) by (rewrite X3 by lia; exact U22).
  assert (E22' : ew E3 22 = Z_to_bv 64 (kz_desk k)) by (rewrite X3 by lia; exact E22).
  assert (E32' : ew E3 32 = Z_to_bv 64 SB) by (rewrite X3 by lia; exact E32).
  assert (E33' : ew E3 33 = Z_to_bv 64 (FA g pos)) by (rewrite X3 by lia; exact E33).
  assert (E46' : ew E3 46 = Z_to_bv 64 (d_dev d)) by (rewrite X3 by lia; exact E46).
  assert (E47' : ew E3 47 = Z_to_bv 64 (d_strips d)) by (rewrite X3 by lia; exact E47).
  assert (E48' : ew E3 48 = Z_to_bv 64 (d_chars d)) by (rewrite X3 by lia; exact E48).
  assert (E49' : ew E3 49 = Z_to_bv 64 (d_counter d)) by (rewrite X3 by lia; exact E49).
  clear U2 U33 U22 U2c U33c.
  pose proof (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem3 md3 kj Hpre HJ3) as HRO3.
  pose proof HJ3 as (HAR3 & _).
  (* the desk's four bytes again (the call kept no region with a window outside its range) *)
  o10_add o10_rg
    ltac:(apply (owe_desk_region_ok B TL E3 W2 mem3 (kz_p k) (kz_desk k) d _ HRO3 Hpd U22');
          intros i Hi; destruct i as [|[|[|[|i]]]]; cbn [nth desk_bytesZ];
          [o10_den E46' | o10_den E47' | o10_den E48' | o10_den E49' | lia])
    ltac:(o10_dj).
  (* the shadow entries in the memory after the call *)
  assert (SH3 : forall i, 0 <= i < 60 ->
    aview tfibsegs (w_H W2) mem3 (shadow_addr (FA g pos) + i) = Some (nth (Z.to_nat i) (shm 0) 0)).
  { intros i Hi. rewrite Hkp; [exact (SHc i Hi) | unfold shadow_addr, SHADOW_OFF; lia
    | unfold shadow_addr, SHADOW_OFF; appn; lia | unfold shadow_addr, SHADOW_OFF; lia]. }
  assert (SHOK : sh_ok tfibsegs CW_Bx o10_SH E3 (mrestrict (w_H W2) mem3)).
  { unfold o10_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - exact (owe_desk_shent B ly2 S2 W2 mem3 md3 E3 (kz_p k) (kz_desk k) d GM IV HAR3 Hpd E22' E32').
    - pose proof (o10_bs_k W2 mem3 (FA g pos) Hf64 SH3) as HBS3.
      pose proof (block_shadow_range (aview tfibsegs (w_H W2) mem3) SHADOW_OFF (FA g pos + 192) 184
        (FA g pos + 192) 184 HBS3 ltac:(lia) ltac:(lia)) as RA3.
      assert (Hamk : amem_range (FA g pos + 192) 184) by (appn; lia).
      unfold owe_SHk. change 376 with (192 + 184).
      apply (cw_shent_ra_off W2 mem3 E3 33 (FA g pos) 192 184 RA3 Hamk); [lia | lia | lia | lia | exact E33' | exact E32']. }
  rename HJ3 into HJ.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ o10_zs2 g pos sp1 a ->
    aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem3 a) by (intros; reflexivity).
  (* 0x82d60-0x82dd0: the UBSan test of want + 14 (decided), want[14], want_len, want_display, desk + 11, the key,
     s9 again; to CHK *)
  cw_run_to o10_awr 0x82dd4. cw_keep ltac:(o10_kwr o10_zs2).
  o10_shape PC_CHK.
  lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ => remember Ev as Ef eqn:HEf in HS end.
  assert (XF : forall n, (n < 50)%nat -> ew Ef n = ew E3 n)
    by (intros n Hn; rewrite HEf; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (U33f : bv_unsigned (ew Ef 33) = FA g pos) by (rewrite XF by lia; exact U33').
  assert (E46f : ew Ef 46 = Z_to_bv 64 (d_dev d)) by (rewrite XF by lia; exact E46').
  assert (E49f : ew Ef 49 = Z_to_bv 64 (d_counter d)) by (rewrite XF by lia; exact E49').
  owe_region HS 1%nat Hre. owe_region HS 2%nat Hrd. owe_region HS 5%nat Hrc'. owe_region HS 6%nat Hrf.
  rewrite restrict_mkst_fx in Hre, Hrd, Hrc', Hrf. cbn [ms_mem] in Hre, Hrd, Hrc', Hrf.
  lazymatch goal with U : bv_unsigned (ew Ef 33) = FA g pos |- _ =>
    pose proof (field_of_region Ef _ 33%nat (FA g pos) _ 336 340 336 340 336 2 (SLit 5104) 5104 Hrd U
      ltac:(owe_in) eq_refl ltac:(cbn; lia) ltac:(lia)) as V336;
    pose proof (field_of_region Ef _ 33%nat (FA g pos) _ 336 340 336 340 338 1 (SOff 46 0) (d_dev d) Hrd U
      ltac:(owe_in) ltac:(o10_den E46f) ltac:(cbn; lia) ltac:(lia)) as V338;
    pose proof (field_of_region Ef _ 33%nat (FA g pos) _ 336 340 336 340 339 1 (SLit 48) 48 Hrd U
      ltac:(owe_in) eq_refl ltac:(cbn; lia) ltac:(lia)) as V339;
    pose proof (field_of_region_any Ef _ 33%nat (FA g pos) _ 350 351 350 351 350 1 (SLit 18446744073709551607) Hre U
      ltac:(owe_in) ltac:(lia)) as V350;
    pose proof (field_of_region Ef _ 33%nat (FA g pos) _ 332 336 332 336 332 4 (SLit 0) 0 Hrc' U
      ltac:(owe_in) eq_refl ltac:(cbn; lia) ltac:(lia)) as V332;
    pose proof (field_of_region Ef _ 33%nat (FA g pos) _ 360 376 360 376 360 8 (SLit 15) 15 Hrf U
      ltac:(owe_in) eq_refl ltac:(cbn; lia) ltac:(lia)) as V360;
    pose proof (field_of_region_any Ef _ 33%nat (FA g pos) _ 360 376 360 376 368 4
      (SAlu ALU_OR (SOff 49 0) (SLit 393216)) Hrf U ltac:(owe_in) ltac:(lia)) as V368;
    pose proof (field_of_region Ef _ 33%nat (FA g pos) _ 360 376 360 376 372 4 (SLit 1) 1 Hrf U
      ltac:(owe_in) eq_refl ltac:(cbn; lia) ltac:(lia)) as V372;
    rewrite (o10_key _ _ d Ef 49 Hpd E49f) in V368 end.
  eapply (o10_ok_fin B MT K XM_LIB LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c ys k d Ef _ (ms_mem msC) mem3).
  + exact HJ0.
  + exact Hfr.
  + exact Hk.
  + exact Hmo.
  + exact HC.
  + exact Hops.
  + exact Hcur.
  + exact Hkat.
  + exact Hrec.
  + exact Hrc.
  + exact Hkind.
  + eassumption.
  + rewrite HEf. env_agree_chain HAE3.
  + eassumption.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + apply (nth_error_In _ 4). vm_compute. reflexivity.
  + exact KEc.
  + exact Hkp.
  + exact KE.
  + exact Hcp.
  + exact Hpl.
  + exact V336.
  + exact V338.
  + exact V339.
  + apply (owe_vm _ _ 1 _ _ V350). vm_compute. reflexivity.
  + exact V332.
  + exact V360.
  + apply (owe_vm _ _ 4 _ _ V368). change (8 * Z.of_N 4) with 32. change (8 * Z.of_nat 4) with 32.
    apply Z.mod_mod. lia.
  + exact V372.
  + exact Hb1.
  + exact Hby.
Qed.
End b.
End a.

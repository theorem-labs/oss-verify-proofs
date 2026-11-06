(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/APgMain3.v of this library: SEGMENT S3 LOOP of
   libreac/fuzz_knock's ASan harness walk of LLVMFuzzerTestOneInput in fuzz_knock.asan-ubsan (sha256
   f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82), pc 0x7f154-0x7f1e8, from the loop head ss_L
   (INV_L (S fuel)) to ss_T (INV_T fuel) at 0x7f1ec (lib/AU/APgStates.v, lib/AU/APgLoop0.v).
   The proof is lib/A/APgMain3.v's (donor model proofs/cgif/cgif_file_fuzzer/lib/A/ACf1.v at c8557374ad2e: rt_B_aux
   :410-497 and pin_reg :268-280), with the module paths of the lib/AU twins and the asan-ubsan pcs.  The asan-ubsan
   code differs from the asan code in three ways, none of which adds a step to the proof
   (internal path, sections 2 and 4):
   - three UBSan pointer-overflow guards `addi rX,cur,k; bgeu s11,rX,0x7f3f8` (k = 1, 2, 3 at 0x7f158, 0x7f188,
     0x7f1c4; trap iff cur + k <=u 1).  s11 = 1 is a literal of ss_L and the cursor is the atom N_cur = 301 with the
     range [4096, 140737479966720] (lib/AU/APgStates.v rl_atomsR, from INV_L's inv_cursor), so the engine decides each
     guard not taken (decide_cond BC_GEU over ranges_ltu, lib/Reusable/YP0m.v); no split, no lemma;
   - the rem = 1 test is `bne s9,s11` (asan `li a1,1; bne s9,a1`): s11 = 1 again;
   - the slow paths of the shadow checks of cur and cur + 1 have the other polarity (`blt` back to the fast path, `j`
     to the report); the engine pays every shadow obligation with obl_cur, so no slow path is walked.
   Each `lb shadow; bnez; slow block` is one shadow obligation of the engine (lib/Reusable/YCbn.v tok_load /
   tok_branch), paid by obl_cur from the input block; the trap word 0x7f3f8 and the reports 0x7f43c-0x7f444 are never
   reached.

   THE CODE (asan-ubsan image; agrees with (internal path))
     0x7f154  addi a0,s3,1 / bgeu s11,a0       guard 5      0x7f15c-0x7f16c  shadow check of cur
     0x7f170  lbu  s7,0(s3)      ev               0x7f174  bne  s9,s11,0x7f184   rem <> 1
     0x7f178  li s9,0 / li a1,0 / j 0x7f1b4      rem = 1: rem' = 0, lo = 0, hi = 0, cur' = cur + 1
     0x7f184  addi a1,a0,1 / bgeu s11,a1       guard 6      0x7f18c-0x7f19c  shadow check of cur + 1
     0x7f1a0  lbu  a1,0(a0)      lo               0x7f1a4  addi a0,s3,2 / li a2,2 / bne s9,a2,0x7f1c0   rem <> 2
     0x7f1b0  li s9,0 / 0x7f1b4 li a2,0 / mv s3,a0 / j 0x7f1ec     rem = 2: rem' = 0, hi = 0, cur' = cur + 2
     0x7f1c0  addi a2,a0,1 / bgeu s11,a2       guard 7      0x7f1c8-0x7f1d8  shadow check of cur + 2
     0x7f1dc  lbu  a2,0(a0)      hi               0x7f1e0  addi s9,s9,-3 / addi s3,s3,3 / slli a2,a2,8
                                                   rem >= 3: rem' = rem - 3, cur' = cur + 3

   rule 24: no function proved. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm APgRt APgStates APgLoop0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* one input byte at a moving cursor  [DONOR A/ACf1.v:396-407 in_bytes, for one byte] *)
Ltac in_byte HJ LAWS HAR Hpin Hpin3 Hrq FP0 cx j bj PBj Aj :=
let HJc := fresh "HJc" in pose proof HJ as HJc; rewrite FP0 in HJc;
destruct (PB_at_now _ _ cx _ _ _ _ _ _ _ j LAWS HAR HJc Hpin Hpin3 Hrq ltac:(cbn [c_n]; lia)) as (bj & PBj & Aj);
cbn [c_p] in Aj; clear HJc.
(* point register r at a fresh atom e whose value is the register's  [the donor's pin_reg, A/ACf1.v:267-281, with
   the equation proved by dtac instead of read off a chunk] *)
Ltac pin_by HS r e dtac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let eo := eval vm_compute in (sr_get (ss_regs ssx) r) in
let Hv := fresh "Hv" in
assert (Hv : sv_denot Ev e = sv_denot Ev eo) by dtac;
let HS3 := fresh "HS3" in
pose proof (st_ok_pin_rege Ev ssx msx r e HS ltac:(intros X; discriminate X)
(eq_trans Hv (eq_sym (st_ok_reg tfibsegs Ev ssx msx r HS)))) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS end.
Ltac pin_tac :=
rewrite sv_denot_SOff0; cbn [sv_denot];
repeat match goal with H : ew ?Ex ?m = Z_to_bv 64 _ |- context [ew ?Ex ?m] => rewrite H end;
rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia].
(* a2 = hi << 8 (`slli a2,a2,8` at 0x7f1e8) *)
Ltac sll_tac b E322 E326 :=
idtac; lazymatch goal with |- sv_denot ?Ev (SOff _ 0) = sv_denot ?Ev (SAlu ALU_SLL (SOff ?m 0) (SLit 8)) =>
rewrite sv_denot_SOff0, E322, (denot_lit_U Ev (SAlu ALU_SLL (SOff m 0) (SLit 8))); f_equal;
rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SLit, (U_atom Ev m b E326) by lia;
change (Z.land (zcanon 8) 63) with 8; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256;
rewrite zcanon_id by (unfold M64; lia); lia end.
(* the conjuncts of INV_T once its witnesses are given; the inv_cells / inv_cursor arms are picked by the goal's
   head before the plain lia, which only fails on them, slowly, in the walk's large context *)
Ltac fin_conj :=
repeat match goal with |- _ /\ _ => split end;
first [ eassumption
| lazymatch goal with |- inv_cells _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
  unfold inv_cells; repeat match goal with |- _ /\ _ => split end; first [eassumption | lia] end
| lazymatch goal with |- inv_cursor _ _ _ _ =>
  unfold inv_cursor; cbn [c_p c_n]; repeat match goal with |- _ /\ _ => split end; lia end
| lia ].
(* in_region of lib/A/APgLoop0.v:211-225, except that each all_disjoint goal first runs zone_lia's second arm
   `zones; req_lits; lia` after `keep`, a `clear -` that leaves only the bounds the goal uses, and runs zone_lia
   itself only if that fails.  zone_lia's lia reads the whole walk context, 0.2-3 s per goal, which made the
   three in_region calls 110 s of this file's 192 s; after the cut a goal takes ~0.02 s.  APgMain0.v and
   APgMain4.v cut the context the same way before their zone_lia. *)
Ltac in_region_keep HS R E10x AG keep :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev ssv msv R HS eq_refl) as HS3;
specialize (HS3 ltac:(
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
ewpeel; rewrite E10x, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
repeat (apply Forall_cons; [ eapply rt_chunk1_of_val; [ apply val_mem1_of_aview; eassumption | eassumption | ewpeel; eassumption ] | ]); apply Forall_nil));
specialize (HS3 ltac:(
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
repeat split; first [keep; zones; req_lits; lia | zone_lia]));
clear HS; rename HS3 into HS; norm_ss HS end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FP0 : FP = [].

Lemma rt_S3 : forall fuel : nat,
  rt_from B MT FP POST ss_T (INV_T B MT fuel) ->
  rt_from B MT FP POST ss_L (INV_L B MT (S fuel)).
Proof.
intros fuel RT. rt_prelude.
pose proof HINV as (Hk & Hacc & HPerm3 & rem & cur & i & d & h & now & quiet & op & due & hns & st & g &
p1 & p2 & c & Erem & Ecur & Ei & Ed & Eh & Enow & Equiet & HCELL & HKN & HCUR & Hfuel & Hrem1 & Hi & Hnow).
cbn [c_ly c_S c_p c_n] in HPerm3, HCUR.
destruct HCELL as (Est & Ep1 & Eop & Edue & Ehns & Eg & Ep2 & Rp1 & Rp2 & Rop & Rdue & Rhns).
destruct HCUR as (Hcur & Hc0 & Hcn & Hrem0 & Hcur4096 & HcurHi). cbn [c_p c_n] in Hcur, Hcn.
cbv [N_rem N_cur N_cnt N_d N_h N_now N_quiet N_st N_p1 N_op N_due N_hns N_g N_p2] in
Erem, Ecur, Ei, Ed, Eh, Enow, Equiet, Est, Ep1, Eop, Edue, Ehns, Eg, Ep2.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (Hpin : In (p, n) (ablocks B ly S)) by (destruct Hpn as [[Hn0 _] | [_ Hin]]; [exfalso; lia | exact Hin]).
assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | exact Hpin]).
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); [exfalso; lia | reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hpin3) as (_ & Hp4096 & Hpceil & HinApp & _).
rewrite Hrq in Hpceil, HinApp.
pose proof YM05.alloc_ceiling_val as Hceilv.
pose proof (blk_off_img B _ _ _ _ _ p n (proj1 HJ3) Hpin3) as HoffImg. rewrite Hrq in HoffImg.
pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 _ _ _ p n 1 fpos (proj1 HJ3) Hpin3 Hfin3) as HpF.
unfold zdisjoint in HpF. cbn [fst snd] in HpF. change (fs_frame_bytes 1) with 128 in HpF. rewrite EFA3 in HpF. fold F in HpF.
rewrite Hrq in HpF.
in_byte HJ3 LAWS HAR Hpin Hpin3 Hrq FP0 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) c b0 PB0 A0.
replace (p + c) with (cur + 0) in A0 by lia. pose proof (proj1 PB0) as R0.
add_atom_win HS 320%nat (Z_to_bv 64 b0) E320.
add_fact HS 320%nat 0 255 E320 ltac:(lia).
in_region_keep HS (YP09.mkRegion (Some 301%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 320 0))]) Ecur AG
  ltac:(clear - Hcur Hc0 Hcn Hrem1 HpF HinApp HoffImg Hpceil Hceil Hslo FFS Hsp1 HFceil C1 HF8c HF8lo).
rd_run HS HJ3 AG fpos F EFA3 Ecur E32n Hpin3 Hrq.
rb HS AG E10 E11 E32 E10n E11n E32n.
br_split HS Hc1.
all: hc_bool Hc1 ltac:(fun H => hc_atom H 300%nat rem Erem ltac:(lia)); hc_prop Hc1.
- (* rem <> 1: the second byte *)
  in_byte HJ3 LAWS HAR Hpin Hpin3 Hrq FP0 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) (c + 1) b1 PB1 A1.
  replace (p + (c + 1)) with (cur + 1) in A1 by lia. pose proof (proj1 PB1) as R1.
  add_atom_win HS 321%nat (Z_to_bv 64 b1) E321.
  add_fact HS 321%nat 0 255 E321 ltac:(lia).
  in_region_keep HS (YP09.mkRegion (Some 301%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 321 0))]) Ecur AG
    ltac:(clear - Hcur Hc0 Hcn Hrem1 HpF HinApp HoffImg Hpceil Hceil Hslo FFS Hsp1 HFceil C1 HF8c HF8lo Hc1).
  rd_run HS HJ3 AG fpos F EFA3 Ecur E32n Hpin3 Hrq.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  br_split HS Hc2.
  all: hc_bool Hc2 ltac:(fun H => hc_atom H 300%nat rem Erem ltac:(lia)); hc_prop Hc2.
  + (* rem <> 2: the third byte *)
    in_byte HJ3 LAWS HAR Hpin Hpin3 Hrq FP0 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) (c + 2) b2 PB2 A2.
    replace (p + (c + 2)) with (cur + 2) in A2 by lia. pose proof (proj1 PB2) as R2.
    add_atom_win HS 326%nat (Z_to_bv 64 b2) E326.
    add_fact HS 326%nat 0 255 E326 ltac:(lia).
    in_region_keep HS (YP09.mkRegion (Some 301%nat) 2 3 0 0 [YP09.mkChunk 2 (CVal 1 (SOff 326 0))]) Ecur AG
      ltac:(clear - Hcur Hc0 Hcn Hrem1 HpF HinApp HoffImg Hpceil Hceil Hslo FFS Hsp1 HFceil C1 HF8c HF8lo Hc1 Hc2).
    rd_run_to HS HJ3 AG fpos F EFA3 Ecur E32n Hpin3 Hrq 0x7f1ec.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    add_atom_win HS 322%nat (Z_to_bv 64 (256 * b2)) E322.
    add_atom_win HS 323%nat (Z_to_bv 64 (rem - 3)) E323.
    add_atom_win HS 324%nat (Z_to_bv 64 (cur + 3)) E324.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    pin_by HS (12%bv : bv 5) (SOff 322 0) ltac:(sll_tac b2 E322 E326).
    pin_by HS (25%bv : bv 5) (SOff 323 0) pin_tac.
    pin_by HS (19%bv : bv 5) (SOff 324 0) pin_tac.
    add_fact HS 322%nat 0 65280 E322 ltac:(lia).
    add_fact HS 323%nat 0 67108863 E323 ltac:(lia).
    add_fact HS 324%nat 4096 140737479966720 E324 ltac:(lia).
    ra_join_win HS ss_T 700%nat rt_loop_deadsT_bv ltac:(idtac).
    rb HS AG E10 E11 E32 E10n E11n E32n.
    rt_hand RT HS.
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact HPerm3|].
    exists (rem - 3), (cur + 3), i, d, h, now, quiet, op, due, hns, st, g, p1, p2, (c + 3), b0, b1, b2.
    fin_conj.
  + pl_run_to HS HJ3 AG fpos F EFA3 0x7f1ec.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    add_atom_win HS 322%nat (Z_to_bv 64 (256 * 0)) E322.
    add_atom_win HS 323%nat (Z_to_bv 64 0) E323.
    add_atom_win HS 324%nat (Z_to_bv 64 (cur + 2)) E324.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    pin_by HS (12%bv : bv 5) (SOff 322 0) pin_tac.
    pin_by HS (25%bv : bv 5) (SOff 323 0) pin_tac.
    pin_by HS (19%bv : bv 5) (SOff 324 0) pin_tac.
    add_fact HS 322%nat 0 65280 E322 ltac:(lia).
    add_fact HS 323%nat 0 67108863 E323 ltac:(lia).
    add_fact HS 324%nat 4096 140737479966720 E324 ltac:(lia).
    ra_join_win HS ss_T 700%nat rt_loop_deadsT_bv ltac:(idtac).
    rb HS AG E10 E11 E32 E10n E11n E32n.
    rt_hand RT HS.
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact HPerm3|].
    exists 0, (cur + 2), i, d, h, now, quiet, op, due, hns, st, g, p1, p2, (c + 2), b0, b1, 0.
    fin_conj.
- pl_run_to HS HJ3 AG fpos F EFA3 0x7f1ec.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  add_atom_win HS 321%nat (Z_to_bv 64 0) E321.
  add_atom_win HS 322%nat (Z_to_bv 64 (256 * 0)) E322.
  add_atom_win HS 323%nat (Z_to_bv 64 0) E323.
  add_atom_win HS 324%nat (Z_to_bv 64 (cur + 1)) E324.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  pin_by HS (11%bv : bv 5) (SOff 321 0) pin_tac.
  pin_by HS (12%bv : bv 5) (SOff 322 0) pin_tac.
  pin_by HS (25%bv : bv 5) (SOff 323 0) pin_tac.
  pin_by HS (19%bv : bv 5) (SOff 324 0) pin_tac.
  add_fact HS 321%nat 0 255 E321 ltac:(lia).
  add_fact HS 322%nat 0 65280 E322 ltac:(lia).
  add_fact HS 323%nat 0 67108863 E323 ltac:(lia).
  add_fact HS 324%nat 4096 140737479966720 E324 ltac:(lia).
  ra_join_win HS ss_T 700%nat rt_loop_deadsT_bv ltac:(idtac).
  rb HS AG E10 E11 E32 E10n E11n E32n.
  rt_hand RT HS.
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact HPerm3|].
  exists 0, (cur + 1), i, d, h, now, quiet, op, due, hns, st, g, p1, p2, (c + 1), b0, 0, 0.
  fin_conj.
Qed.

End d.
End c.

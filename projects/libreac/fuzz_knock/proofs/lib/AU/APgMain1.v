(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/APgMain1.v of this library (segment S1 HEADER of
   libreac/fuzz_knock's ASan harness walk), for
   LLVMFuzzerTestOneInput 0x7eed0 in fuzz_knock.asan-ubsan (sha256
   f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82; 350 words, size 0x578), made the way
   proofs/cgif/cgif_file_fuzzer/lib/YCf1.v is made from A/ACf1.v at c8557374ad2e: the walk framework imports move to
   the lib/AU twins, every pc is the asan-ubsan one, and the registers follow the asan-ubsan code. The A file's
   comment gives the donor line each step follows. rule 24: no function proved (a twin of a port of the released
   cgif_file_fuzzer harness walk structure). *)

(* SEGMENT S1 HEADER, pc 0x7f004-0x7f0d0 (52 insns), 0x7f3c8-0x7f3f4 (12) and the check slow paths 0x7f408-0x7f438
   (13), ending at ss_P, pc 0x7f0d4. The instruction-by-instruction comparison with the asan image is
   (internal path) (section 2 row S1, section 4, section 6 lines 295-348).
   The code (capstone 5.0.7 over the pinned image bytes): fuzz_u32 inlined. s3 = p, s4 = n.
     0x7f004 beqz s4 -> 0x7f044 (n = 0: s9 = a2 = a1 = a3 = a4 = 0, j 0x7f0d4)
     0x7f008 a0 = p+1; a1 = 1; 0x7f010 bgeu a1,a0 -> 0x7f3f8 (UBSan guard 1)
     0x7f014-0x7f024 check of the byte p (shadow byte at (p >> 3) + 56(s1), in a1 / a2); slow path 0x7f408-0x7f414
     0x7f028 lbu a1,0(s3); a2 = 1; 0x7f030 bne s4,a2 -> 0x7f05c (n = 1: s9 = a2 = a3 = 0, j 0x7f0c0: a4 = 0,
       j 0x7f0d0: s3 = p+1)
     0x7f05c a3 = p+2; 0x7f060 bgeu a2,a3 -> 0x7f3f8 (UBSan guard 2)
     0x7f064-0x7f074 check of p+1; slow path 0x7f418-0x7f420; 0x7f078 lbu a2; a4 = n-2; a0 = p+2; a2 <<= 8;
     0x7f088 beqz a4 -> 0x7f0c8 (n = 2: s9 = a3 = 0, s3 = p+2; a4 = n-2 = 0)
     0x7f08c a3 = p+3; a5 = 1; 0x7f094 bgeu a5,a3 -> 0x7f3f8 (UBSan guard 3)
     0x7f098-0x7f0a8 check of p+2; slow path 0x7f424-0x7f42c; 0x7f0ac lbu a3; a5 = 1; a0 = p+3;
     0x7f0b8 bne a4,a5 -> 0x7f3c8 (n = 3: s9 = 0, a4 = 0, j 0x7f0d0: s3 = p+3)
     0x7f3c8 a4 = p+4; 0x7f3cc bgeu a5,a4 -> 0x7f3f8 (UBSan guard 4)
     0x7f3d0-0x7f3e0 check of p+3; slow path 0x7f430-0x7f438; 0x7f3e4 lbu a4; s9 = n-4; s3 = p+4; a4 <<= 8; j 0x7f0d4.
   The four UBSan guards trap iff p + k <=u 1 (k = 1..4; the trap word 0x7f3f8 is never reached). Each is decided by
   the executor itself (decide_cond BC_GEU over the atom ranges, Reusable/YP0m.v) from the range [4096, 2^47 - 2^23]
   of atom 10 (= p) that the segment adds at its entry, exactly as the A file does (A/APgMain1.v:349-355): n = 0 gives
   p = A_EMPTY (lib/AU/YCfm.v); n <> 0 gives In (p, n) (ablocks ..) from rt_base and AR_blocks_law's 4096 <= p and
   p + req_size n <= alloc_ceiling. The four shadow checks (report calls at 0x7f414, 0x7f420, 0x7f42c, 0x7f438) are
   discharged by obl_pay -> obl_of_block, as in the A file.
   The five exits join at 0x7f0d4 with five register shapes; the walk pins s3 (cur = p + c), s9 (rem = n - c) and the
   four byte registers a1..a4 to fresh slots 100..105 and havocs a0 / a5.

   What differs from the A file, and why:
   - the n = 2 and n = 3 tests compare a4 = n - 2 (`addi a4,s4,-2` 0x7f07c; `beqz a4` 0x7f088, `bne a4,a5` 0x7f0b8 with
     a5 = 1) where the A image compares s4 with 2 and 3: br_go_off reads the condition through atom 11 at offset -2,
     and the n = 2 test is inverted (its taken side is the n = 2 tail), so the two sub-cases come in the other order.
   - on the n = 2 exit a4 holds n - 2 = 0 (the A image's a4 = 0 literal): p_vb reads it through atom 11 too.
   - ss_P: x17 (a7) = F, slot 75 (S0's `mv a7,a6` 0x7ef54; read by S2's `sd a7,16(s1)` 0x7f0d4 and `addi s4,a7,32`
     0x7f0d8) where the A image's x17 is a fresh atom 82; x16 (a6) = F in both. ss_H is a Theorem Labs lane's AU twin
     (lib/AU/APgMain0.v).
   - the four UBSan guards and the moved blocks need no proof step of their own (above).

   Section hypotheses (all named; no Axiom / Admitted / Parameter): TL : TfibLib B; LAWS : AR_laws tfibsegs B;
   FP0 : FP = []; and rt_S1's premise rt_from B MT FP POST ss_P (INV_P B MT) (S2, lib/AU/APgMain2.v rt_S2). *)
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
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm APgRt.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import APgMain0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== Part 1: local copies of donor walk tactics ============================== *)
(* [A/ACf9.v:246-279, 339-340, 347-348], as lib/A/APgMain1.v:66-105 *)
Ltac add_atom_win HS n w En :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win tfibsegs n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
Ltac ra_join_win HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win tfibsegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
Lemma denot_havoc_win : forall E k ws e, sv_atoms_on (win_free k (length ws)) e = true -> sv_denot (havoc E k ws) e = sv_denot E e.
Proof. intros E k ws e He. apply (sv_denot_agree_on (win_free k (length ws)) E); [apply env_agree_on_havoc | exact He]. Qed.
Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_havoc_above by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac ewpeel_in H := repeat (first [ rewrite ew_havoc_old in H by nat_side | rewrite ew_havoc_above in H by nat_side | rewrite ew_ewset_other in H by nat_side ]).
Section loc. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* [A/ACew.v:89-94] *)
Lemma val_mem1_of_aview : forall H m a v, aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
destruct (aview_byte tfibsegs H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
assert (Rb : 0 <= bv_unsigned b < 256) by (pose proof (bv_unsigned_in_range 8 b) as X; exact X).
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by exact Rb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* [A/ACf9.v:489-505] *)
Lemma PB_at_now : forall B STK cx own ly3 S3 W3 mem3 md3 k i,
AR_laws tfibsegs B -> AR tfibsegs B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ->
ajournal tfibsegs B STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)) -> In (c_p cx, c_n cx) (ablocks B ly3 S3) -> req_size (c_n cx) = c_n cx ->
0 <= i < c_n cx ->
exists b, PB cx i b /\ aview tfibsegs (w_H W3) mem3 (c_p cx + i) = Some b.
Proof.
intros B STK cx own ly3 S3 W3 mem3 md3 k i LAWS HAR0 HJ Hin0 Hin3 Hrq Hi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HAR0 Hin0) as (_ & _ & _ & _ & Hpres & _). rewrite Hrq in Hpres.
destruct (aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) as [b|] eqn:Ev;
[| exfalso; exact (aview_some_of_apresent tfibsegs _ _ _ (proj1 (Hpres (c_p cx + i) ltac:(lia))) Ev)].
destruct (aview_byte tfibsegs _ _ _ b Ev) as (bb & _ & _ & Hb).
exists b. split.
- split; [exact Hb | apply val_mem1_of_aview; exact Ev].
- pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2 (c_p cx) (c_n cx) i Hin0 Hin3); [exact Ev | rewrite Hrq; exact Hi | apply inFP_nil].
Qed.
(* [A/ACf1.v:112-123] *)
Lemma rt_chunk1_of_val : forall E (m : word -> option byte) base off k v,
val_mem tfibsegs m (base + off) 1 v -> 0 <= v < 256 -> ew E k = Z_to_bv 64 v ->
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 (SOff k 0))).
Proof.
intros E m base off k v Hv Hr Hk i Hi. cbn [YP09.c_len YP09.c_val YP09.cv_len Z.of_N] in Hi.
assert (i = 0) as -> by lia.
exists (Z_to_bv 8 (YO0f.le_byte v 1 0)). split.
- cbn [YP09.c_off YP09.c_val YP09.cbyte]. rewrite sv_denot_SOff0, Hk. f_equal. unfold YP09.byte_of_word.
rewrite unsigned_lit_small by lia. f_equal. unfold YO0f.le_byte. change (Z.of_nat 1) with 1. cbn [Z.of_nat]. rewrite ?Z.mul_0_r, ?Z.shiftr_0_r.
change (2 ^ (8 * 1)) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
- cbn [YP09.c_off]. rewrite Z.add_0_r. pose proof (Hv 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r in H0. exact H0.
Qed.
(* [A/ACf1.v:192-223] *)
Lemma rt_ad_split : forall E x pre r post, all_disjoint E x (pre ++ r :: post) -> extent_disjoint E x r /\ all_disjoint E x (pre ++ post).
Proof. intros E x pre r post. induction pre as [|y pre IH]; cbn [app all_disjoint]; [tauto|]. intros [Hy Hr]. destruct (IH Hr) as [A B']. tauto. Qed.
Lemma rt_ed_sym : forall E a b, extent_disjoint E a b -> extent_disjoint E b a.
Proof. unfold extent_disjoint. intros E a b H. lia. Qed.
Lemma rt_pd_move : forall E pre r post, pairwise_disjoint E (pre ++ r :: post) -> all_disjoint E r (pre ++ post) /\ pairwise_disjoint E (pre ++ post).
Proof.
intros E pre r post. induction pre as [|x pre IH]; cbn [app pairwise_disjoint all_disjoint]; [tauto|].
intros [Hx Hrest]. destruct (IH Hrest) as [Hr Hp]. destruct (rt_ad_split E x pre r post Hx) as [Hxr Hxa].
split; [split; [apply rt_ed_sym; exact Hxr | exact Hr] | split; [exact Hxa | exact Hp]].
Qed.
Lemma rt_wf_move : forall pre r post, regions_wf (pre ++ r :: post) = true -> regions_wf (r :: pre ++ post) = true.
Proof.
intros pre r post. induction pre as [|x pre IH]; cbn [app regions_wf]; [tauto|]. intros H.
apply andb_prop in H as [Hx H]. specialize (IH H). cbn [regions_wf] in IH. apply andb_prop in IH as [Hr Hp].
rewrite Hr, Hx, Hp. reflexivity.
Qed.
Lemma rt_forall_move : forall {A} (P : A -> Prop) pre r post, Forall P (pre ++ r :: post) -> Forall P (r :: pre ++ post).
Proof.
intros A P pre r post H. rewrite Forall_forall in *. intros x Hx. apply H.
destruct Hx as [<- | Hx]; [apply in_or_app; right; left; reflexivity|].
apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx].
Qed.
Lemma rt_st_ok_move : forall E ss ms pre r post,
st_ok tfibsegs E ss ms -> ss_mem ss = pre ++ r :: post ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (r :: pre ++ post) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms pre r post (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (W & O & D) & H9) Hm.
rewrite Hm in W, O, D.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact (rt_wf_move pre r post W)|]. split; [exact (rt_forall_move _ pre r post O)|].
destruct (rt_pd_move E pre r post D) as [A B']. split; [exact A | exact B'].
Qed.
(* knock: the byte bounds of the four header registers at the join *)
Lemma U_lit0 : forall E, U E (SLit 0) = 0.
Proof. intros E. rewrite U_SLit. reflexivity. Qed.
Lemma U_zext8_lt : forall E x, 0 <= U E (SExt false 8 x) < 2 ^ 16.
Proof. intros E x. rewrite U_zext. change (2 ^ Z.of_N 8) with 256. pose proof (Z.mod_pos_bound (U E x) 256 ltac:(lia)). lia. Qed.
Lemma U_sll8_zext8_lt : forall E x, 0 <= U E (SAlu ALU_SLL (SExt false 8 x) (SLit 8)) < 2 ^ 16.
Proof.
intros E x. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_zext, U_SLit. change (2 ^ Z.of_N 8) with 256.
change (Z.land (zcanon 8) 63) with 8. pose proof (Z.mod_pos_bound (U E x) 256 ltac:(lia)).
rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End loc.
(* [A/ACf1.v:124-161, 243-251, 267-281, 396-409]; knsegs = tfibsegs (a Theorem Labs lane's names), as lib/A/APgMain1.v:192-260 *)
Ltac in_region HS R E10x AG :=
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
    repeat split; zone_lia));
  clear HS; rename HS3 into HS; norm_ss HS end.
Ltac rd_run HS HJ AG fpos F EFA E10x E32x Hpin3 Hrq :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok tfibtbl_lib_ok HS HJ SH RTBspan;
  try (lazymatch goal with |- range_addressable _ _ _ _ => obl_pay HJ E10x E32x Hpin3 Hrq end);
  try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac rd_run_to HS HJ AG fpos F EFA E10x E32x Hpin3 Hrq stop :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan stop;
  try (lazymatch goal with |- range_addressable _ _ _ _ => obl_pay HJ E10x E32x Hpin3 Hrq end);
  try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac br_go HS Hc E11x :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH RTBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end;
  lazymatch type of E11x with _ = Z_to_bv 64 ?nv =>
  hc_bool Hc ltac:(fun H => hc_atom H 11%nat nv E11x ltac:(lia)); hc_prop Hc end.
(* asan-ubsan: the n = 2 / n = 3 tests read a4 = n + c (`addi a4,s4,-2` 0x7f07c), the atom 11 at offset c *)
Ltac br_go_off HS Hc E11x c :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH RTBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end;
  lazymatch type of E11x with _ = Z_to_bv 64 ?nv =>
  hc_bool Hc ltac:(fun H => rewrite (U_atom_off _ 11 nv c) in H by first [ewpeel; exact E11x | lia]); hc_prop Hc end.
Ltac move_region HS i :=
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let pre := eval vm_compute in (firstn i rs) in
  let r := eval vm_compute in (nth i rs got_region) in
  let post := eval vm_compute in (skipn (S i) rs) in
  let HS3 := fresh "HS3" in
  pose proof (rt_st_ok_move Ex ssx msx pre r post HS ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end.
Ltac pin_reg HS rr a v Hv Ea :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict ?Hh ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
  remember (U Ev e) as v eqn:Hv;
  let Q := fresh "Q" in
  assert (Q : getr (ms_regs ms) rr = sv_denot Ev e) by exact (st_ok_restrict_reg tfibsegs Hh Ev ssx ms rr HS);
  add_atom_win HS a (Z_to_bv 64 v) Ea;
  lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msv2 =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_pin_rege Ev2 ssx2 msv2 rr (SOff a 0) HS ltac:(intros X; discriminate X)
    ltac:(rewrite sv_denot_SOff0, Ea; cbn [ms_regs restrict mkst]; rewrite Q, Hv; symmetry; apply denot_lit_U)) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end; clear Q end.
Ltac in_bytes HJ cx LAWS HAR Hpin Hpin3 Hrq FP0 i0 n0 :=
  let HJc := fresh "HJc" in pose proof HJ as HJc; rewrite FP0 in HJc;
  let rec go j k :=
    lazymatch k with
    | O => idtac
    | S ?k' =>
      let bj := fresh "b" in let PBj := fresh "PB" in let Aj := fresh "A" in let Rj := fresh "R" in
      destruct (PB_at_now _ _ cx _ _ _ _ _ _ _ j LAWS HAR HJc Hpin Hpin3 Hrq ltac:(cbn [c_n]; lia)) as (bj & PBj & Aj);
      cbn [c_p] in Aj; pose proof (proj1 PBj) as Rj;
      let j' := eval vm_compute in (j + 1) in go j' k'
    end in
  go i0 n0; clear HJc.
Ltac rb HS AG E10 E11 E32 E10n E11n E32n :=
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv; relowRT HS AG E10 E11 E32 E10n E11n E32n.

(* ============================== Part 2: the states and the invariant ============================== *)
Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
(* ss_H, the S0 -> S1 boundary state at 0x7f004, is a Theorem Labs lane's AU twin, defined in lib/AU/APgMain0.v (Required). *)
(* ss_P: the state at 0x7f0d4, where the five header exits join (lib/A/APgMain1.v:267-283 at 0x7f088). ss_H's
   registers, memory, atoms and alias, with s9 = slot 100 (rem), s3 = slot 101 (cur = p + c), a1 = slot 102 (the low
   byte or 0), a2 = slot 103 (the second byte << 8 or 0), a3 = slot 104 (the third byte or 0), a4 = slot 105 (the
   fourth byte << 8 or 0); a0 and a5 dead (slots 110, 111); a6 = a7 = F (slot 75: ss_H's, S1 writes neither); the
   condition (n >> 26) = 0 dropped; the frame's shadow region read-only (fs_roF, as the donor's A/ACf0.v:49 before its
   checked reads: the shadow-check table needs every writable region to be app memory). *)
Definition rt_P_deads : list nat := [10; 15]%nat.
Definition rt_P_deads_bv : list (bv 5) := [10; 15]%bv.
Definition RT_PN : nat := 110.
Definition ss_P_0 : sstate :=
mkSS 0x7f0d4
[SLit 0; SOff 71 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 72 0; SOff 73 0; SOff 74 0; SOff 2 0; SOff 70 0;
 SOff 10 0; SOff 102 0; SOff 103 0; SOff 104 0; SOff 105 0; SOff 15 0; SOff 75 0; SOff 75 0; SOff 18 0; SOff 101 0;
 SOff 11 0; SOff 21 0; SOff 88 0; SOff 23 0; SOff 24 0; SOff 100 0; SOff 26 0; SOff 27 0; SOff 83 0; SOff 84 0;
 SOff 85 0; SOff 86 0]
(set_window (nth 0 (ss_mem ss_H) got_region) 0 0 :: tl (ss_mem ss_H)) None
(mkFacts (f_atoms (ss_facts ss_H)) [] (f_alias (ss_facts ss_H))).
Definition ss_P : sstate := Eval vm_compute in ss_havoc_regs ss_P_0 RT_PN rt_P_deads.
(* INV_P: INV_0's three conjuncts, and the join's values: c bytes consumed (0 <= c <= 4), rem = n - c with rem = 0 unless
   c = 4, and the four byte registers below 2^16 (lib/A/APgMain1.v:284-292, unchanged) *)
Definition INV_P (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= 0 /\ acc <= ACC0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
exists c rem v1 v2 v3 v4,
ew E 100 = Z_to_bv 64 rem /\ ew E 101 = Z_to_bv 64 (c_p cx + c) /\
ew E 102 = Z_to_bv 64 v1 /\ ew E 103 = Z_to_bv 64 v2 /\ ew E 104 = Z_to_bv 64 v3 /\ ew E 105 = Z_to_bv 64 v4 /\
0 <= c <= 4 /\ 0 <= rem /\ c + rem = c_n cx /\ (rem = 0 \/ c = 4) /\
0 <= v1 < 2 ^ 16 /\ 0 <= v2 < 2 ^ 16 /\ 0 <= v3 < 2 ^ 16 /\ 0 <= v4 < 2 ^ 16.
End st.

(* ============================== Part 3: the segment ============================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FP0 : FP = [].
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
(* the hand-off at 0x7f0d4 for c consumed bytes [A/ACf1.v:282-296, 367-388]; a register bound is a literal, a zero
   extended byte, a shifted byte, or (a4 on the n = 2 exit) n - 2 = 0 through atom 11 *)
Ltac p_vb Hv E11n n := rewrite Hv; first [ lia | rewrite U_lit0; lia | apply U_zext8_lt | apply U_sll8_zext8_lt
  | rewrite (U_atom_off _ 11 n (-2)) by first [ewpeel; exact E11n | lia]; lia ].
Ltac p_fin HS AG E10 E11 E32 E10n E11n E32n RP Hk0 Hacc Eab3 p n c :=
  rb HS AG E10 E11 E32 E10n E11n E32n;
  let cur := fresh "cur" in let Hcur := fresh "Hcur" in let E101 := fresh "E101" in
  let rem := fresh "rem" in let Hrem := fresh "Hrem" in let E100 := fresh "E100" in
  let v1 := fresh "v1" in let Hv1 := fresh "Hv1" in let E102 := fresh "E102" in
  let v2 := fresh "v2" in let Hv2 := fresh "Hv2" in let E103 := fresh "E103" in
  let v3 := fresh "v3" in let Hv3 := fresh "Hv3" in let E104 := fresh "E104" in
  let v4 := fresh "v4" in let Hv4 := fresh "Hv4" in let E105 := fresh "E105" in
  pin_reg HS (19%bv : bv 5) 101%nat cur Hcur E101;
  pin_reg HS (25%bv : bv 5) 100%nat rem Hrem E100;
  pin_reg HS (11%bv : bv 5) 102%nat v1 Hv1 E102;
  pin_reg HS (12%bv : bv 5) 103%nat v2 Hv2 E103;
  pin_reg HS (13%bv : bv 5) 104%nat v3 Hv3 E104;
  pin_reg HS (14%bv : bv 5) 105%nat v4 Hv4 E105;
  let Bv1 := fresh "Bv1" in let Bv2 := fresh "Bv2" in let Bv3 := fresh "Bv3" in let Bv4 := fresh "Bv4" in
  assert (Bv1 : 0 <= v1 < 2 ^ 16) by p_vb Hv1 E11n n; assert (Bv2 : 0 <= v2 < 2 ^ 16) by p_vb Hv2 E11n n;
  assert (Bv3 : 0 <= v3 < 2 ^ 16) by p_vb Hv3 E11n n; assert (Bv4 : 0 <= v4 < 2 ^ 16) by p_vb Hv4 E11n n;
  first [ rewrite (U_atom_off _ 10 p c) in Hcur by first [ewpeel; exact E10n | lia]
        | rewrite (U_atom _ 10 p) in Hcur by first [ewpeel; exact E10n | lia] ];
  first [ rewrite U_lit0 in Hrem
        | rewrite (U_atom_off _ 11 n (-4)) in Hrem by first [ewpeel; exact E11n | lia] ];
  ra_join_win HS ss_P 110%nat rt_P_deads_bv ltac:(idtac);
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv; rt_hand RP HS;
  [ split; [exact Hk0|]; split; [exact Hacc|]; split; [exact Eab3|];
    exists c, rem, v1, v2, v3, v4;
    split; [exact E100|]; split; [rewrite E101; f_equal; lia|];
    split; [exact E102|]; split; [exact E103|]; split; [exact E104|]; split; [exact E105|];
    repeat split; first [ lia | (left; lia) | (right; lia) ] .. ].
Ltac tail_run HS HJ AG fpos F EFA stop :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan stop;
  try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Lemma rt_S1_aux : rt_from B MT FP POST ss_P (INV_P B MT) -> rt_from B MT FP POST ss_H (INV_0 B MT 0).
Proof.
intros RP. rt_prelude.
pose proof HINV as (Hk0 & Hacc & Eab3).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
(* atom 10 = p in [4096, 2^47 - 2^23]: what decides the four UBSan guards (A/APgMain1.v:349-355) *)
assert (HpR : 4096 <= p /\ p + n <= alloc_ceiling).
{ destruct Hpn as [[Hn0 HpE] | [Hnr Hin]].
  - rewrite HpE, Hn0. unfold A_EMPTY. clear - C1. lia.
  - assert (Hp3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hp3) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos n ltac:(clear - Hnr; lia)) as [_ Hrq]. clear - Hp4096 Hpceil Hrq. lia. }
add_fact HS 10%nat 4096 140737479966720 E10n ltac:(clear - HpR C1 Hn26; lia).
fs_roF HS.
(* 0x7f004 beqz s4 *)
br_go HS Hc1 E11n.
- (* n = 0: 0x7f044-0x7f058, j 0x7f0d4 *)
  tail_run HS HJ3 AG fpos F EFA3 0x7f0d4. clear_frames.
  p_fin HS AG E10 E11 E32 E10n E11n E32n RP Hk0 Hacc Eab3 p n 0.
- (* n <> 0: In (p, n) ablocks, req_size n = n *)
  assert (Hpin : In (p, n) (ablocks B ly S)) by (destruct Hpn as [[Hn0 _] | [_ Hin]]; [exfalso; clear - Hn0 Hc1; lia | exact Hin]).
  assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpin).
  assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); [exfalso; clear - Hc1 e; lia | reflexivity]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hpin3) as (_ & _ & _ & HinApp & _). rewrite Hrq in HinApp.
  pose proof (blk_off_img B _ _ _ _ _ p n (proj1 HJ3) Hpin3) as HoffImg. rewrite Hrq in HoffImg.
  pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 _ _ _ p n 1 fpos (proj1 HJ3) Hpin3 Hfin3) as HpF.
  unfold zdisjoint in HpF. cbn [fst snd] in HpF. change (fs_frame_bytes 1) with 128 in HpF. rewrite EFA3 in HpF. fold F in HpF. rewrite Hrq in HpF.
  (* 0x7f008-0x7f030: a0 = p+1, UBSan guard 0x7f010 (decided), the check of p, lbu a1,0(s3) *)
  in_bytes HJ3 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) LAWS HAR Hpin Hpin3 Hrq FP0 0 1%nat.
  add_atom_win HS 200%nat (Z_to_bv 64 b) E200.
  in_region HS (YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 200 0))]) E10n AG.
  rd_run HS HJ3 AG fpos F EFA3 E10n E32n Hpin3 Hrq. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  (* 0x7f030 bne s4,a2 (a2 = 1) *)
  br_go HS Hc2 E11n.
  + (* n <> 1: 0x7f05c-0x7f088, UBSan guard 0x7f060 (decided), the check of p+1, lbu a2, a4 = n-2 *)
    in_bytes HJ3 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) LAWS HAR Hpin Hpin3 Hrq FP0 1 1%nat.
    add_atom_win HS 201%nat (Z_to_bv 64 b0) E201.
    in_region HS (YP09.mkRegion (Some 10%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 201 0))]) E10n AG.
    rd_run HS HJ3 AG fpos F EFA3 E10n E32n Hpin3 Hrq. clear_frames.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    (* 0x7f088 beqz a4 (a4 = n-2) *)
    br_go_off HS Hc3 E11n (-2).
    * (* n = 2: 0x7f0c8-0x7f0d0 *)
      tail_run HS HJ3 AG fpos F EFA3 0x7f0d4. clear_frames.
      p_fin HS AG E10 E11 E32 E10n E11n E32n RP Hk0 Hacc Eab3 p n 2.
    * (* n <> 2: 0x7f08c-0x7f0b8, UBSan guard 0x7f094 (decided), the check of p+2, lbu a3 *)
      in_bytes HJ3 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) LAWS HAR Hpin Hpin3 Hrq FP0 2 1%nat.
      add_atom_win HS 202%nat (Z_to_bv 64 b1) E202.
      in_region HS (YP09.mkRegion (Some 10%nat) 2 3 0 0 [YP09.mkChunk 2 (CVal 1 (SOff 202 0))]) E10n AG.
      rd_run HS HJ3 AG fpos F EFA3 E10n E32n Hpin3 Hrq. clear_frames.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      (* 0x7f0b8 bne a4,a5 (a4 = n-2, a5 = 1) *)
      br_go_off HS Hc4 E11n (-2).
      -- (* n <> 3: 0x7f3c8-0x7f3f4, UBSan guard 0x7f3cc (decided), the check of p+3, lbu a4, s9 = n - 4,
            s3 = p + 4, j 0x7f0d4 *)
         in_bytes HJ3 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) LAWS HAR Hpin Hpin3 Hrq FP0 3 1%nat.
         add_atom_win HS 203%nat (Z_to_bv 64 b2) E203.
         in_region HS (YP09.mkRegion (Some 10%nat) 3 4 0 0 [YP09.mkChunk 3 (CVal 1 (SOff 203 0))]) E10n AG.
         rd_run_to HS HJ3 AG fpos F EFA3 E10n E32n Hpin3 Hrq 0x7f0d4. clear_frames.
         p_fin HS AG E10 E11 E32 E10n E11n E32n RP Hk0 Hacc Eab3 p n 4.
      -- (* n = 3: 0x7f0bc-0x7f0c4, j 0x7f0d0 *)
         tail_run HS HJ3 AG fpos F EFA3 0x7f0d4. clear_frames.
         p_fin HS AG E10 E11 E32 E10n E11n E32n RP Hk0 Hacc Eab3 p n 3.
  + (* n = 1: 0x7f034-0x7f040, j 0x7f0c0 *)
    tail_run HS HJ3 AG fpos F EFA3 0x7f0d4. clear_frames.
    p_fin HS AG E10 E11 E32 E10n E11n E32n RP Hk0 Hacc Eab3 p n 1.
Qed.
(* S1 HEADER: ss_H (0x7f004) -> ss_P (0x7f0d4) *)
Lemma rt_S1 : rt_from B MT FP POST ss_P (INV_P B MT) -> rt_from B MT FP POST ss_H (INV_0 B MT 0).
Proof. exact rt_S1_aux. Qed.
End e.
End c.

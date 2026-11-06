(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/APgLoop0.v of this library (libreac/fuzz_knock's ASan
   harness walk of LLVMFuzzerTestOneInput in fuzz_knock.asan-ubsan, sha256
   f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82), made the way proofs/cgif/cgif_file_fuzzer/lib/YCf7.v
   is made from A/ACf7.v at c8557374ad2e: the walk framework imports move to the lib/AU twins (AWalkFw0 YCef YF0l YCej
   YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm APgRt APgMain7), and the text follows the asan-ubsan code.  This module is the
   SHARED PART of the input loop (segments S3 LOOP, S4 TAIL, S5 MID, S6 CHECKS and the loop closure): the loop
   invariants INV_L / INV_T / INV_M / INV_C, the functional model the loop body needs, and the walk helpers of
   lib/A/APgLoop0.v sections 0-2 (each copied block keeps its donor line, as there).
   The four walk states ss_L / ss_T / ss_M / ss_C, their env slots, dead-register lists and memory shape are
   lib/AU/APgStates.v's; this module
   Requires that file and defines none of them.  ss_X / INV_X are a Theorem Labs lane's lib/AU/APgMain7.v.  The two callee
   contracts are a Theorem Labs lane's lib/A/APgCSpec.v (image-independent: segs is a parameter), used at segs := tfibsegs of
   lib/AU/AWalkFw0.v and the asan-ubsan entries below.
   Users: lib/AU/APgMain3.v (S3), APgMain4.v (S4), APgMain5.v (S5), APgMain6.v (S6), APgMainL.v (the closure).

   rule 24: no function proved.  Definitions, generic lemmas and tactics only.

   WHAT DIFFERS FROM THE ASAN INVARIANTS (the asan-ubsan / asan image comparison:
   (internal path), section 3)
   - the trip counter counts DOWN: s10 = 4096 - i (`lui s10,0x1` 0x7f130, `addiw s10,s10,-1` 0x7f294, `bnez s10,0x7f150`
     0x7f298), in env slot N_cnt = 302 (the asan N_i).  So each invariant carries `ew E N_cnt = Z_to_bv 64 (4096 - i)`
     where the asan one carries `ew E N_i = Z_to_bv 64 i`; i itself, its range [0, 4095] and the `now` bound in terms of
     i are unchanged.
   - d moved from s11 to s8 and s11 is the constant 1: both are register facts of the states (APgStates.v), not
     conjuncts here; d keeps its slots N_d / N_dC.  The two spills 32(s1) / 40(s1) are swapped literals of the states.
   - the asan invariants end with `0 <= c_T cx`; it is left out here: rt_prelude (lib/AU/APgRt.v) gives it as HT0 from
     rt_base's last conjunct.
   - the callee entries are the asan-ubsan ones: reac_knock_heard 0x7f520 (call 0x7f210, RA 0x7f214), reac_knock_step
     0x7f5b0 (call 0x7f22c, RA 0x7f230).

   THE LOOP, AND WHY IT IS AN INDUCTION ON FUEL (as lib/A/APgLoop0.v:33-40)
   knock's loop is input-driven: the trip count is the remaining byte count `rem`, which the body decreases by 1, 2
   or 3, and the loop also leaves when the countdown reaches 0.  The closure is the released PLAIN proof's induction
   on a nat `fuel` with `Z.to_nat rem <= fuel` (lib/Prog/LLVMFuzzerTestOneInput.v:83-101 loop_ok, :303-307
   knock_loop).  ss_L (0x7f154, after the head test `beqz s9,0x7f2c4` at 0x7f150) carries INV_L fuel with 1 <= rem;
   the three body states carry the post-decrement bound without that lower bound; S6's back edge `bnez s10,0x7f150`
   at 0x7f298 re-enters through the head test, which re-establishes 1 <= rem.

   THE REGISTERS OF THE LOOP (asan-ubsan image)
     s1 = sp = sp1 (slot 70), s0 = sp0 (slot 2), s4 = F + 32 = &k, s6 = SB + F/8 (slot 88), s8 = d (DRIVEN),
     s9 = rem, s10 = 4096 - i, s11 = 1, s2 = h (HEARD), s5 = now, s3 = cur, s7 = ev (inside the body).
     Spills off s1: 16 = F, 24 = F, 32 = 499999999, 40 = 500000000, 48 = quiet, 56 = SB, 80 = F.
     k = struct reac_knock at F + 32, fields at 0/4/8/16/24/32/36 of widths 4/4/8/8/8/4/4
     (lib/Prog/reac_knock_struct.v:9-10): state, pad1, opened, due, heard, granted, pad2.

   THE ENV SLOTS (lib/AU/APgStates.v): 300-343 for the loop's values, and the dead-register havoc windows 700 (ss_T) /
   720 (ss_M) / 740 (ss_C) / 760 (ss_L).  Slots < 33 and 70 / 75 / 87 / 88 are the context record's (AU/APgRt.v). *)
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
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm APgRt.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import APgBase APgCSpec.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import APgMain7 APgStates.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================== 0. the walk helpers a Theorem Labs lane's set does not carry ===================== *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* [DONOR A/ACew.v:89-95] *)
Lemma val_mem1_of_aview : forall H m a v, aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
destruct (aview_byte tfibsegs H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small (bv_unsigned b) 256) by lia.
rewrite (Z.mod_small (bv_unsigned b) 256) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* [DONOR A/ACf1.v:112-123] *)
Lemma rt_chunk1_of_val : forall E (m : word -> option byte) base off k v,
val_mem tfibsegs m (base + off) 1 v -> 0 <= v < 256 -> ew E k = Z_to_bv 64 v ->
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 (SOff k 0))).
Proof.
intros E m base off k v Hv Hr Hk i Hi. cbn [YP09.c_len YP09.c_val YP09.cv_len Z.of_N] in Hi.
assert (i = 0) as -> by lia.
exists (Z_to_bv 8 (YO0f.le_byte v 1 0)). split.
- cbn [YP09.c_off YP09.c_val YP09.cbyte]. rewrite sv_denot_SOff0, Hk. f_equal. unfold YP09.byte_of_word.
rewrite unsigned_lit_small by lia. f_equal. unfold YO0f.le_byte. change (Z.of_nat 1) with 1. cbn [Z.of_nat].
rewrite ?Z.mul_0_r, ?Z.shiftr_0_r.
change (2 ^ (8 * 1)) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
- cbn [YP09.c_off]. rewrite Z.add_0_r. pose proof (Hv 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0.
rewrite Z.add_0_r in H0. exact H0.
Qed.
(* [DONOR A/ACf9.v:339-340] *)
Lemma denot_havoc_win : forall E k ws e, sv_atoms_on (win_free k (length ws)) e = true -> sv_denot (havoc E k ws) e = sv_denot E e.
Proof. intros E k ws e He. apply (sv_denot_agree_on (win_free k (length ws)) E); [apply env_agree_on_havoc | exact He]. Qed.
(* [DONOR A/ACf9.v:489-505] *)
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
(* [DONOR A/ACf1.v:192-223]: move one region of the state to the head, so that a join can shrink it *)
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
End h.
(* [DONOR A/ACf9.v:347-348] *)
Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_havoc_above by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac ewpeel_in H := repeat (first [ rewrite ew_havoc_old in H by nat_side | rewrite ew_havoc_above in H by nat_side | rewrite ew_ewset_other in H by nat_side ]).
(* [DONOR A/ACf9.v:246-251] *)
Ltac add_atom_win HS n w En :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win tfibsegs n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
(* [DONOR A/ACf9.v:252-279] *)
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
(* [DONOR A/ACf9.v:389-393] *)
Ltac vkeep V H2 m2 etac :=
lazymatch type of V with val_mem _ (mrestrict ?Hh ?m) ?a ?n ?v =>
let V2 := fresh "V" in
assert (V2 : val_mem tfibsegs (mrestrict H2 m2) a n v) by (apply (val_mem_kept Hh H2 m m2 a n v V); intros i Hi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; etac);
clear V; rename V2 into V end.
(* [DONOR A/ACf1.v:243-251] *)
Ltac move_region HS i :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let pre := eval vm_compute in (firstn i rs) in
let r := eval vm_compute in (nth i rs got_region) in
let post := eval vm_compute in (skipn (S i) rs) in
let HS3 := fresh "HS3" in
pose proof (rt_st_ok_move Ex ssx msx pre r post HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* [DONOR A/ACf1.v:124-138]: put a read-only region with one-byte chunks over an input-block address *)
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
(* the shadow-check obligation of an input byte at a MOVING cursor.  The donor pays it with obl_pay
   [A/ACf9.v:230-239], which reads the block's base out of the atom the address is an offset of; knock's cursor is
   its own atom (cur = p + c with c symbolic), so the block base and the size come from Hin instead, and the two
   range side conditions are closed by lia from `Hcur : cur = p + c` and the block's bounds. *)
Ltac obl_cur HJx HEcur HEbx Hin Hrq :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
lazymatch type of HEcur with _ = Z_to_bv 64 ?cv =>
lazymatch type of Hin with In (?pb, ?sz) _ =>
first [ rewrite (U_atom_off Ex n cv c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEcur | lia | lia]
| rewrite (U_atom Ex n cv); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEcur | lia] ];
eapply (obl_of_block tfibsegs _ L _ _ _ _ _ Ex (SOff bx 0) _ len pb sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEbx | unfold SB; lia]
| lia | rewrite Hrq; lia ] end end end.
(* [DONOR A/ACf1.v:139-155], with obl_cur for obl_pay *)
Ltac rd_run HS HJ AG fpos F EFA HEcur HEbx Hin Hrq :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tfibtbl_lib_ok HS HJ SH RTBspan;
try (lazymatch goal with |- range_addressable _ _ _ _ => obl_cur HJ HEcur HEbx Hin Hrq end);
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac rd_run_to HS HJ AG fpos F EFA HEcur HEbx Hin Hrq stop :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan stop;
try (lazymatch goal with |- range_addressable _ _ _ _ => obl_cur HJ HEcur HEbx Hin Hrq end);
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
(* a run with no input read in it *)
Ltac pl_run HS HJ AG fpos F EFA :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tfibtbl_lib_ok HS HJ SH RTBspan;
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac pl_run_to HS HJ AG fpos F EFA stop :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan stop;
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
(* [DONOR A/ACf1.v:156-161], generalised: the branch the engine could not decide, with its condition named *)
Ltac br_split HS Hc :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH RTBspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac rb HS AG E10 E11 E32 E10n E11n E32n :=
let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv; relowRT HS AG E10 E11 E32 E10n E11n E32n.

(* ===================== 1. the functional model, over Z =====================
   L_NS, LAY_Knock and knock_step_f are a Theorem Labs lane's, in lib/A/APgCSpec.v (one definition each, theirs); this
   module adds only st_ofZ, which is the harness's own `d ? 1 : h ? 2 : 0`
   (lib/Prog/LLVMFuzzerTestOneInput.v:81), and the arithmetic the loop body needs. *)
(* lib/Prog/LLVMFuzzerTestOneInput.v:81 *)
Definition st_ofZ (d h : Z) : Z := if Z.eqb d 1 then 1 else if Z.eqb h 1 then 2 else 0.
(* lib/Prog/reac_knock_heard_c.v:25 *)
Definition knock_heard_stZ (st : Z) : Z := if Z.eqb st 0 then 2 else st.

(* lib/Prog/LLVMFuzzerTestOneInput.v:15-22, restated over Z for the asan-ubsan countdown: `addiw s10,s10,-1` at
   0x7f294 on s10 = 4096 - i in [1, 4096] gives 4095 - i with no 32-bit wrap (the asan image's iw_succZ, mirrored) *)
Lemma iw_predZ : forall x, 1 <= x <= 4096 -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 (x - 1))) = x - 1.
Proof.
intros x Hx. unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
rewrite (Z.mod_small (x - 1 + 2 ^ 31) (2 ^ 32)) by lia.
replace (x - 1 + 2 ^ 31 - 2 ^ 31) with (x - 1) by lia. apply unsigned_lit_small. lia.
Qed.
(* `lw` of a small non-negative field: the sign extension is the identity.  knock's plain proof says the same
   through knock_sx32_eqb (lib/Prog/reac_knock_struct.v:30-35); here the field is an atom of the k region. *)
Lemma U_sext32_small : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt. rewrite (U_atom E n v Hn) by lia.
rewrite (Z.mod_small v (2 ^ Z.of_N 32)) by (change (2 ^ Z.of_N 32) with (2 ^ 32); lia).
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
apply zcanon_id. unfold M64. lia.
Qed.

(* lib/Prog/knock_lib.v:79-92, restated over Z: the delay the body adds to `now` is < 2 ^ 23 *)
Lemma dt_boundZ : forall dt s, 0 <= dt < 2 ^ 16 -> 0 <= s < 8 -> 0 <= Z.shiftl dt s < 2 ^ 23.
Proof.
intros dt s Hdt Hs. rewrite Z.shiftl_mul_pow2 by lia.
assert (2 ^ s <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia).
assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
nia.
Qed.
(* the two bytes the body reads are combined with `or` and do not overlap  [DONOR A/ACf1.v:42-51 rt_lor_shl] *)
Lemma lor_byte_pair : forall hib lo, 0 <= hib < 256 -> 0 <= lo < 256 -> Z.lor (hib * 256) lo = hib * 256 + lo.
Proof.
intros hib lo Hh Hl.
assert (Hd : Z.land (hib * 256) lo = 0).
{ apply Z.bits_inj_0. intros i. rewrite Z.land_spec. destruct (Z_lt_le_dec i 8) as [Hi|Hi].
- destruct (Z_lt_le_dec i 0) as [Hn|Hn]; [rewrite Z.testbit_neg_r by exact Hn; reflexivity|].
replace (hib * 256) with (Z.shiftl hib 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite Z.shiftl_spec_low by exact Hi. reflexivity.
- rewrite <- (Z.mod_small lo 256) by exact Hl. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_high by lia.
apply Bool.andb_false_r. }
rewrite <- (Z.lxor_lor _ _ Hd). rewrite <- (Z.add_nocarry_lxor _ _ Hd). reflexivity.
Qed.

(* ===================== 2. the struct layout ===================== *)
(* LAY_Knock is a Theorem Labs lane's (lib/A/APgCSpec.v:18), from lib/Prog/reac_knock_struct.v:9-10: state, pad1, opened,
   due, heard, granted, pad2 at 0/4/8/16/24/32/36 of widths 4/4/8/8/8/4/4.  Only the harness-side constants are
   here: the struct's size and where S2 puts it inside the fake frame. *)
Definition KNOCK_SIZE : Z := 40.
(* `addi s4,a7,32` at 0x7f0d8, a7 = F *)
Definition K_OFF : Z := 32.

(* ===================== 3. the invariants =====================
   The text of lib/A/APgLoop0.v section 6, with the countdown slot N_cnt (= 4096 - i) for the asan N_i (= i) and
   without the last conjunct `0 <= c_T cx` (rt_prelude's HT0). *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.

(* the seven cells of k, as atoms, with the ranges the chunk widths need *)
Definition inv_cells (E : env) (nst np1 nop ndue nhns ng np2 : nat) (st p1 op due hns g p2 : Z) : Prop :=
ew E nst = Z_to_bv 64 st /\ ew E np1 = Z_to_bv 64 p1 /\ ew E nop = Z_to_bv 64 op /\
ew E ndue = Z_to_bv 64 due /\ ew E nhns = Z_to_bv 64 hns /\ ew E ng = Z_to_bv 64 g /\
ew E np2 = Z_to_bv 64 p2 /\
0 <= p1 < 2 ^ 32 /\ 0 <= p2 < 2 ^ 32 /\ 0 <= op < 2 ^ 63 /\
0 <= due <= 18446744073709551615 /\ 0 <= hns <= 9223406396593514176.
(* knock's own state machine, as loop_ok carries it (lib/Prog/LLVMFuzzerTestOneInput.v:90-97) *)
Definition inv_knock (d h st g op due hns quiet now : Z) : Prop :=
(d = 0 \/ d = 1) /\ (h = 0 \/ h = 1) /\ st = st_ofZ d h /\ g = d /\
(d = 0 -> h = 0 -> quiet = op /\ due = op + L_NS) /\
(d = 0 -> h = 1 -> hns = quiet) /\
quiet <= now.
(* the input cursor *)
Definition inv_cursor (cx : rtcx) (cur rem c : Z) : Prop :=
cur = c_p cx + c /\ 0 <= c /\ c + rem = c_n cx /\ 0 <= rem /\
4096 <= cur /\ cur <= 140737479966720.

Definition INV_L (B : asyms) (MT : ameter_ops) (fuel : nat)
: rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 =>
k <= EV_LIB /\ acc <= ACC0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
exists (rem cur i d h now quiet op due hns st g p1 p2 c : Z),
ew E N_rem = Z_to_bv 64 rem /\ ew E N_cur = Z_to_bv 64 cur /\ ew E N_cnt = Z_to_bv 64 (4096 - i) /\
ew E N_d = Z_to_bv 64 d /\ ew E N_h = Z_to_bv 64 h /\ ew E N_now = Z_to_bv 64 now /\
ew E N_quiet = Z_to_bv 64 quiet /\
inv_cells E N_st N_p1 N_op N_due N_hns N_g N_p2 st p1 op due hns g p2 /\
inv_knock d h st g op due hns quiet now /\
inv_cursor cx cur rem c /\
(Z.to_nat rem <= fuel)%nat /\ 1 <= rem /\
0 <= i <= 4095 /\ 0 <= now <= 2 ^ 63 + i * 2 ^ 23.

Definition INV_T (B : asyms) (MT : ameter_ops) (fuel : nat)
: rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 =>
k <= EV_LIB /\ acc <= ACC0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
exists (rem cur i d h now quiet op due hns st g p1 p2 c ev lo hib : Z),
ew E N_remT = Z_to_bv 64 rem /\ ew E N_curT = Z_to_bv 64 cur /\ ew E N_cnt = Z_to_bv 64 (4096 - i) /\
ew E N_d = Z_to_bv 64 d /\ ew E N_h = Z_to_bv 64 h /\ ew E N_now = Z_to_bv 64 now /\
ew E N_quiet = Z_to_bv 64 quiet /\
ew E N_ev = Z_to_bv 64 ev /\ ew E N_lo = Z_to_bv 64 lo /\ ew E N_hi = Z_to_bv 64 (256 * hib) /\
0 <= ev < 256 /\ 0 <= lo < 256 /\ 0 <= hib < 256 /\
inv_cells E N_st N_p1 N_op N_due N_hns N_g N_p2 st p1 op due hns g p2 /\
inv_knock d h st g op due hns quiet now /\
inv_cursor cx cur rem c /\
(Z.to_nat rem <= fuel)%nat /\
0 <= i <= 4095 /\ 0 <= now <= 2 ^ 63 + i * 2 ^ 23.

Definition INV_M (B : asyms) (MT : ameter_ops) (fuel : nat)
: rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 =>
k <= EV_LIB /\ acc <= ACC0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
exists (rem cur i d h now quiet op due hns st g p1 p2 c ev : Z),
ew E N_remT = Z_to_bv 64 rem /\ ew E N_curT = Z_to_bv 64 cur /\ ew E N_cnt = Z_to_bv 64 (4096 - i) /\
ew E N_d = Z_to_bv 64 d /\ ew E N_hM = Z_to_bv 64 h /\ ew E N_nowM = Z_to_bv 64 now /\
ew E N_quietM = Z_to_bv 64 quiet /\ ew E N_ev = Z_to_bv 64 ev /\ 0 <= ev < 256 /\
inv_cells E N_stM N_p1 N_op N_due N_hnsM N_g N_p2 st p1 op due hns g p2 /\
inv_knock d h st g op due hns quiet now /\
inv_cursor cx cur rem c /\
(Z.to_nat rem <= fuel)%nat /\
0 <= i <= 4095 /\ 0 <= now <= 2 ^ 63 + (i + 1) * 2 ^ 23.

Definition INV_C (B : asyms) (MT : ameter_ops) (fuel : nat)
: rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 =>
k <= EV_LIB /\ acc <= ACC0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
exists (rem cur i d h now quiet op due hns st g p1 p2 c : Z),
ew E N_remT = Z_to_bv 64 rem /\ ew E N_curT = Z_to_bv 64 cur /\ ew E N_cnt = Z_to_bv 64 (4096 - i) /\
ew E N_dC = Z_to_bv 64 d /\ ew E N_hM = Z_to_bv 64 h /\ ew E N_nowM = Z_to_bv 64 now /\
ew E N_quietM = Z_to_bv 64 quiet /\
inv_cells E N_stC N_p1 N_op N_dueC N_hnsM N_gC N_p2 st p1 op due hns g p2 /\
inv_knock d h st g op due hns quiet now /\
inv_cursor cx cur rem c /\
(Z.to_nat rem <= fuel)%nat /\
0 <= i <= 4095 /\ 0 <= now <= 2 ^ 63 + (i + 1) * 2 ^ 23.

(* ===================== 3b. the exit state of the loop =====================
   ss_X / INV_X at 0x7f2c4 are a Theorem Labs lane's, in lib/AU/APgMain7.v.  The
   three entries into it are S2's and S6's `beqz s9,0x7f2c4` at the head test 0x7f150 and S6's `j 0x7f2c4` at 0x7f29c
   (the countdown reached 0); lib/AU/APgStates.v proves ss_X_sub_C / ss_X_sub_L, so those joins need no region
   juggling. *)

(* ===================== 4. the two callee contracts the loop calls =====================
   a Theorem Labs lane's tknock_heard_specX / tknock_step_specX (lib/A/APgCSpec.v) at segs := tfibsegs (lib/AU/AWalkFw0.v) and
   the asan-ubsan entry a := the image address of the callee (nm of fuzz_knock.asan-ubsan: reac_knock_heard 0x7f520,
   reac_knock_step 0x7f5b0; au-harness-cut.md, Roots).  S4 takes `tknock_heard_specX tfibsegs B MT A_reac_knock_heard`
   as a Section hypothesis and S5 takes `tknock_step_specX tfibsegs B MT A_reac_knock_step`.  Nothing of the contract
   is restated here. *)
Definition A_reac_knock_heard : Z := 0x7f520.
Definition A_reac_knock_step : Z := 0x7f5b0.
Definition RA_heard : Z := 0x7f214.
Definition RA_step : Z := 0x7f230.

End b.

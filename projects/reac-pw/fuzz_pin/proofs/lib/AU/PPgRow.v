(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_Klib.v:146-200
   (aj_strlen_at) at origin/ossv/recipes f26f9fbd8777 [Apache-2.0]; proofs/reac-pw/fuzz_pin/lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at)
   [Apache-2.0 OR MIT]; proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v, QPgCheck.v, QPgRt.v [Apache-2.0] and QPgLoop0.v [Apache-2.0 OR MIT]
   at 160c9b4d5750 (walk tactics and plumbing lemmas); proofs/reac-pw/fuzz_pin/lib/A/ACep.v (reseat) [Apache-2.0]; for
   reac-pw/fuzz_pin's image A walk of fuzz_catalogue_row: the two call lemmas keep the wrappers' same_but_materialized
   clause, the copied tactics carry the rw_ prefix, and the walk, its loop and its call-site lemmas are new. The
   [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgRow.v of this library, for reac-pw/fuzz_pin's
   image B (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f). Image B's
   fuzz_catalogue_row is image A's code at new addresses with two immediates changed (the shadow-base .got load
   `ld a0,400(a0)` and the table's `addi s0,a0,20`) and no trap branch. What differs here: A_ROW 0x80fb4 and
   A_CAT_TBL 0x98000 (st_value of fuzz_catalogue_row and fuzz_catalogue in the unstripped twin's .symtab); the loop
   head 0x81004 and the next-row block 0x81030 (ss_H / ss_N and the run targets); the wrapper calls' return addresses
   0x81018 (528408) and 0x8102c (528428); the shadow-base .got cell 0x99170 (627056) and shadow-base variable 0xa16f8
   (661240) in rw_entry; the image modules are image B's lib/AU twins (AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1
   AWalkFw2 YCfm, lib/AU/Rt WrapRo StrlenDef; YCeh.ro_tfa_below_ofl for ACeh's). The wrapper trampolines 0x41908 and
   0x41924 are the same in both images. The contract lib/A/PPgCSpec.v and lib/A/PPgBase.v are the same text, and the
   proof text is image A's. *)
(* reac-pw/fuzz_pin, image B (fuzz_pin.asan-ubsan, sha256 d6f83d301522...): the walk of fuzz_catalogue_row
   (0x80fb4, 200 bytes; catalogue.c:29-35) against lib/A/PPgCSpec.v's tpin_row_specX at the table
   fuzz_catalogue (0x98000), and the two call-site lemmas pin_strlen_site_row (0x81014) and pin_bcmp_site
   (0x81028).
   rule 24 (reuse): no released asan-ubsan proof of fuzz_catalogue_row exists; this walk is image A's walk at
   image B's numbers, on the
   CONCRETE engine of the image (aj_run_to_tok / srr_branch_tok / SRr_ret_at over tfibsegs / tfibtbl_lib).

   THE CODE (neutral listing of the pinned image B):
     0x80fb4-0x80fd4  addi sp,sp,-64; ra and s0..s6 saved at sp+56 .. sp+0
     0x80fd8-0x80fdc  s1 = a1 = n, s2 = a0 = sa
     0x80fe0-0x80fe8  s5 = the shadow base, from the GOT cell 0x99170 (-> 0xa16f8 = 0x7fff8000)
     0x80fec-0x81000  s0 = s3 = 0x98000 (the table), s5 = shadow address of s0, s6 = 11
     0x81004 lbu a0,0(s5); 0x81008 bnez a0 -> 0x81074     the check of row i's first 8 bytes
     0x8100c ld s4,0(s0); 0x81010 mv a0,s4; 0x81014 jal 0x41908 (the strlen wrapper's trampoline)
     0x81018 bne a0,s1 -> 0x81030                           strlen(token) <> n: next row
     0x8101c-0x81024 a0 = s4, a1 = s2, a2 = s1; 0x81028 jal 0x41924 (the bcmp wrapper's trampoline)
     0x8102c beqz a0 -> 0x81048                             equal: return this row
     0x81030-0x8103c s6 -= 1, s3 += 0x128, s5 += 0x25, s0 += 0x128; 0x81040 bnez s6 -> 0x81004
     0x81044 s0 = 0; 0x81048 a0 = s0; 0x8104c-0x8106c ra, s0..s6 restored, sp += 64; 0x81070 ret
     0x81074 mv a0,s3; 0x81078 jal errpath_load8              (the error path)

   THE WALK. Segment 0 (rw_top): the prologue up to the loop head 0x81004, re-seated on the head state ss_H
   for row 0. The loop head (rw_head i): atom 33 is row i's address row_addr cat i, atom 34 the rows left
   11 - i, s0 = s3 = atom 33, s5 = SB + atom 33 / 8 (the form the engine reads as a shadow address), s6 =
   atom 34; the loop invariant is row_of sb = row_from i sb (no earlier row's token is sb). Segment H
   (rw_head_seg): the shadow check of the row's first granule passes by the shadow entry [mkSHE 33 0 8],
   paid by pin_cat_ok's range_addressable over the table (cat mod 8 = 0, row stride 296 = 8 * 37), so the
   error path 0x81074 is not reached; the token pointer TP i is read from the row region (pin_cat_ok's
   val_mem); the strlen wrapper returns pin_tokn i (pin_strlen_site_row); a length other than n goes to
   0x81030 (ss_N); else the bcmp wrapper (pin_bcmp_site) returns 0 exactly when the n bytes are equal,
   which with equal lengths is tok_bytes i = sb (rw_bytes_eq): then the function returns row_addr cat i,
   which is row_ptr cat sb by row_from_step; else 0x81030 with row_of sb = row_from (S i) sb. Segment N
   (rw_next_seg): the next-row arithmetic, then `bnez s6`: back to the head with row S i (atoms 33 / 34
   re-made through the scratch atoms 40 / 41), or, after row 10, the return of 0 = row_ptr cat sb
   (row_from_end). rw_loop closes the loop by induction on 11 - i.

   THE CALLS are Section hypotheses: ASTRLEN : astrlen_realizes tfibsegs B 0x41908 (lib/AU/Rt/StrlenDef.v)
   and ABCMP : abcmp_realizes tfibsegs B 0x41924 (lib/Reusable/YG0d.v), bound in the journal form by
   rw_aj_strlen_at and rw_aj_bcmp_at (below), each re-seated with jafter_call_keep (rw_reseat).

   The wrappers' amem_range premise of a token comes from pin_ro_str's amem_range clause (pin_cat_ok),
   through pin_amem_range_le (len + 1 for strlen, n for bcmp).
   fuzz_catalogue_row takes no pin_ro_law: its premises on the entry memory stay true across its two wrapper
   calls (rw_keep: every byte outside [sp - T_row_STK, sp) reads as at the call). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Rt Require Import WrapRo StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------
   The addresses (image B, fuzz_pin.asan-ubsan; st_value in the unstripped twin's .symtab, and the excerpt) *)
Definition A_ROW : Z := 0x80fb4.           (* fuzz_catalogue_row *)
Definition A_CAT_TBL : Z := 0x98000.       (* fuzz_catalogue, 3256 bytes of .data.rel.ro *)
Definition A_BCMP_TR : Z := 0x41924.       (* the bcmp wrapper's trampoline *)
(* STRLEN_ENTRY = 0x41908 (lib/AU/Rt/StrlenDef.v), the strlen wrapper's trampoline. *)

(* ------------------------------------------------------------------------------------------------
   The walk's states. Atoms: 0..31 the entry registers, 32 the shadow base SB, 33 the row address,
   34 the rows left, 35 the row's token pointer (inside segment H), 40 / 41 scratch (segment N). *)
Definition rw_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rw_extra : list word := [Z_to_bv 64 SB].
Definition rw_regionsE : smem := [ stack_region 64; got_region; bcell_region 32 ].
Definition rw_factsE : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_rwE : sstate := mkSS A_ROW sr_atoms rw_regionsE None rw_factsE.
(* the 64-byte frame with the eight saved registers, in the order the prologue's stores leave them *)
Definition rw_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0
[ YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
  YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
  YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
  YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ].
(* s5 at the head: the shadow address of the row, in the form the engine matches (srl 3, then + Bx) *)
Definition rw_sh5 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 32 0).
Definition rw_atomsH : list (nat * afact) :=
[ (34%nat, mkAF 1 11 0); (33%nat, mkAF A_CAT_TBL (A_CAT_TBL + 2960) 0);
  (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ].
Definition rw_atomsB : list (nat * afact) := [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ].
(* the registers dead at 0x81004 and at 0x81030: ra, the temporaries, the arguments and s4 *)
Definition rw_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 28; 29; 30; 31]%nat.
Definition rw_deads_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 28; 29; 30; 31]%bv.
Definition ss_H_0 : sstate :=
mkSS 0x81004
[SLit 0; SOff 1 0; SOff 2 (-64); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 33 0; SOff 11 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 10 0; SOff 33 0; SOff 20 0; rw_sh5; SOff 34 0; SOff 23 0;
 SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[rw_stack] None (mkFacts rw_atomsH [] []).
(* the loop head 0x81004 (dead registers at 2000..2016) and the next-row block 0x81030 (3000..3016) *)
Definition ss_H : sstate := Eval vm_compute in ss_havoc_regs ss_H_0 2000 rw_deads.
Definition ss_N : sstate := Eval vm_compute in ss_havoc_regs (ss_set_pc ss_H_0 0x81030) 3000 rw_deads.
(* row i's token pointer, read by `ld s4,0(s0)` *)
Definition rw_row_region : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
(* the shadow entry of the row's first granule *)
Definition rw_SH : list shent := [mkSHE 33 0 8].

(* ------------------------------------------------------------------------------------------------
   The walk tactics. rw_add_atom_win, rw_pin_by and rw_join are proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v's
   add_atom_win, pin_by and ra_join_win (reac-pw/fuzz_qdisc image A at 160c9b4d5750, made from
   proofs/libreac/fuzz_knock/lib/A/APgLoop0.v at origin/ossv/recipes 6ebe35ba632) with their names prefixed;
   rw_ewpeel is that file's ewpeel, made to skip an occurrence it cannot peel; rw_awr_stk (below) is
   QPgCheck.v's awr_stk with the stack atom's value found from the state. *)
Ltac rw_ewpeel := repeat match goal with
| |- context [ew (havoc ?E ?k ?ws) ?i] =>
  first [ rewrite (ew_havoc_old E k ws i) by nat_side | rewrite (ew_havoc_above E k ws i) by nat_side ]
| |- context [ew (ewset ?E ?k ?w) ?i] => rewrite (ew_ewset_other E k w i) by nat_side
end.
Ltac rw_add_atom_win HS n w En :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win tfibsegs n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
Ltac rw_pin_by HS r e dtac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let eo := eval vm_compute in (sr_get (ss_regs ssx) r) in
let Hv := fresh "Hv" in
assert (Hv : sv_denot Ev e = sv_denot Ev eo) by dtac;
let HS3 := fresh "HS3" in
pose proof (st_ok_pin_rege Ev ssx msx r e HS ltac:(intros X; discriminate X)
(eq_trans Hv (eq_sym (st_ok_reg tfibsegs Ev ssx msx r HS)))) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS end.
Ltac rw_join HS target N deads :=
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
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => change ssx with target in HS end.
(* the facts of a state cut down to sp and SB *)
Ltac rw_facts_base HS :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx rw_atomsB [] [] HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.

(* ------------------------------------------------------------------------------------------------
   Arithmetic and memory helpers *)
(* a run keeps every byte outside the window its write ranges lie in (proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v's
   kept_run at 160c9b4d5750, with the zone an interval) *)
Lemma rw_kept_run : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) lo hi,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m1 a = aview tfibsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> lo <= a < hi) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m2 a = aview tfibsegs H m0 a.
Proof.
intros E rs H m0 m1 m2 lo hi HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Lemma rw_mod16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - 64 - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, (Zminus_mod a 64), Ha, Hb. reflexivity. Qed.
Lemma rw_shadow_low : forall a, 0 <= a < 2 ^ 47 -> 0 <= shadow_addr a < 2 ^ 46.
Proof.
intros a Ha. unfold shadow_addr, SHADOW_OFF.
assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma rw_ra_keep : forall (rd rd' : reader) a len,
(forall x, a <= x < a + len -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
range_addressable rd SHADOW_OFF a len -> range_addressable rd' SHADOW_OFF a len.
Proof. intros rd rd' a len Hk H x Hx. rewrite (Hk x Hx). exact (H x Hx). Qed.
Lemma rw_hull_keep : forall (rd rd' : reader) x n,
(forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof. intros rd rd' x n Hk H s Hs. rewrite (Hk s Hs). exact (H s Hs). Qed.
Lemma rw_hull_sub : forall (rd : reader) x n n', 0 < n <= n' -> shadow_hull_vis rd x n' -> shadow_hull_vis rd x n.
Proof.
intros rd x n n' Hn H s Hs. apply H.
assert (shadow_addr (x + n - 1) / 8 * 8 <= shadow_addr (x + n' - 1) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. unfold shadow_addr.
  apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.
(* the shadow hull of a range below 2 ^ 47 lies below 2 ^ 46 + 8 *)
Lemma rw_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46 + 8.
Proof.
intros x n s Hx Hn Hxn Hs.
pose proof (rw_shadow_low x ltac:(lia)) as [L0 _]. pose proof (rw_shadow_low (x + n - 1) ltac:(lia)) as [_ L1].
pose proof (Z.mul_div_le (shadow_addr (x + n - 1)) 8 ltac:(lia)) as M1.
assert (0 <= shadow_addr x / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma rw_amr_lt : forall p n, amem_range p n -> p + n < 2 ^ 47.
Proof. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. intros p n H. lia. Qed.
Lemma rw_nth_zb : forall (l : list byte) j, (j < length l)%nat -> nth j (pin_zbytes l ++ [0]) 0 = bv_unsigned (nth j l NUL).
Proof.
intros l j Hj. unfold pin_zbytes. rewrite app_nth1 by (rewrite length_map; exact Hj).
rewrite (nth_indep _ 0 (bv_unsigned NUL)) by (rewrite length_map; exact Hj).
exact (map_nth (fun b : byte => bv_unsigned b) l NUL j).
Qed.
Lemma rw_nth_zb' : forall (l : list byte) j, (j < length l)%nat -> nth j (pin_zbytes l) 0 = bv_unsigned (nth j l NUL).
Proof.
intros l j Hj. unfold pin_zbytes.
rewrite (nth_indep _ 0 (bv_unsigned NUL)) by (rewrite length_map; exact Hj).
exact (map_nth (fun b : byte => bv_unsigned b) l NUL j).
Qed.
Lemma rw_nth_zb_end : forall (l : list byte), nth (length l) (pin_zbytes l ++ [0]) 0 = 0.
Proof. intros l. unfold pin_zbytes. rewrite app_nth2; rewrite length_map; [rewrite Nat.sub_diag; reflexivity | lia]. Qed.
Lemma rw_len_zb : forall (l : list byte), length (pin_zbytes l) = length l.
Proof. intros l. unfold pin_zbytes. apply length_map. Qed.
Lemma rw_len_zb0 : forall (l : list byte), length (pin_zbytes l ++ [0]) = S (length l).
Proof. intros l. rewrite length_app, rw_len_zb. cbn [length]. lia. Qed.
Lemma rw_garr8_aview : forall H (m : word -> option byte) x l j,
YI00.garr8 tfibsegs (mrestrict H m) x l -> (j < length l)%nat -> aview tfibsegs H m (x + Z.of_nat j) = Some (nth j l 0).
Proof. intros H m x l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. exact (aview_of_val_mem1 tfibsegs H m _ _ Hv Hr). Qed.
(* two byte strings of the same length are equal exactly when their bytes read the same *)
Lemma rw_bytes_eq : forall H (m : word -> option byte) x y (l1 l2 : list byte),
YI00.garr8 tfibsegs (mrestrict H m) x (pin_zbytes l1 ++ [0]) -> YI00.garr8 tfibsegs (mrestrict H m) y (pin_zbytes l2) ->
length l1 = length l2 ->
(l1 = l2 <-> forall j, 0 <= j < Z.of_nat (length l1) -> aview tfibsegs H m (x + j) = aview tfibsegs H m (y + j)).
Proof.
intros H m x y l1 l2 G1 G2 Hl. split.
- intros <- j Hj. replace j with (Z.of_nat (Z.to_nat j)) by lia.
  rewrite (rw_garr8_aview H m x _ (Z.to_nat j) G1) by (rewrite rw_len_zb0; lia).
  rewrite (rw_garr8_aview H m y _ (Z.to_nat j) G2) by (rewrite rw_len_zb; lia).
  rewrite rw_nth_zb, rw_nth_zb' by lia. reflexivity.
- intros Heq. apply nth_ext with (d := NUL) (d' := NUL); [exact Hl|]. intros j Hj.
  specialize (Heq (Z.of_nat j) ltac:(lia)).
  rewrite (rw_garr8_aview H m x _ j G1) in Heq by (rewrite rw_len_zb0; lia).
  rewrite (rw_garr8_aview H m y _ j G2) in Heq by (rewrite rw_len_zb; lia).
  injection Heq as Heq. rewrite rw_nth_zb, rw_nth_zb' in Heq by lia. apply bv_eq. exact Heq.
Qed.
Lemma rw_U_reg : forall E n w, ew E n = w -> U E (SOff n 0) = bv_unsigned w.
Proof.
intros E n w Hn. rewrite U_SOff, Hn, Z.add_0_r. apply zcanon_small.
pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.
Lemma rw_U_offx : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> U E (SOff n c) = (x + c) mod 2 ^ 64.
Proof. intros E n x c Hn Hx. rewrite U_SOff, Hn, unsigned_lit_small by lia. reflexivity. Qed.
(* s5 after `addi s5,s5,0x25`: the shadow address of the next row *)
Lemma rw_denot_sh37 : forall E n m v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v < 2 ^ 47 -> 0 <= sb < 2 ^ 32 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) (SLit 37)) = Z_to_bv 64 (sb + (v + 296) / 8).
Proof.
intros E n m v sb Hn Hm Hv Hsb. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, Hn, Hm, !U_SLit. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
change (Z.land (zcanon 3) 63) with 3. change (zcanon 37) with 37. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= v / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite (zcanon_small v) by lia. rewrite (zcanon_small (v / 8)) by lia. rewrite (zcanon_small sb) by lia.
rewrite (zcanon_small (v / 8 + sb)) by lia. rewrite zcanon_small by lia.
replace (v + 296) with (v + 37 * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.
(* QPgSlots.v's same_io_wvb (reac-pw/fuzz_qdisc at 160c9b4d5750), and its form for two backings of one model *)
Lemma rw_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
Lemma rw_same_io_wvb2 : forall md l X l' X', same_io (with_vm_backing l X md) (with_vm_backing l' X' md).
Proof. intros md l X l' X'. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
Lemma rw_row_bounds : forall i, (i < CAT_N)%nat ->
A_CAT_TBL <= row_addr A_CAT_TBL i /\ row_addr A_CAT_TBL i + 8 <= A_CAT_TBL + CAT_BYTES /\
row_addr A_CAT_TBL i <= A_CAT_TBL + 2960.
Proof. intros i Hi. unfold row_addr, CAT_ROW, CAT_BYTES, CAT_N, A_CAT_TBL in *. lia. Qed.
Lemma rw_row_next : forall i, row_addr A_CAT_TBL (S i) = row_addr A_CAT_TBL i + 296.
Proof. intros i. unfold row_addr, CAT_ROW. lia. Qed.
(* the loop invariant: a row whose token is not sb is skipped *)
Lemma rw_row_skip : forall i t, (i < CAT_N)%nat -> tok_bytes i <> t -> row_from i t = row_from (S i) t.
Proof.
intros i t Hi Hne. rewrite (row_from_step i t Hi).
destruct (bytes_eqb (tok_bytes i) t) eqn:E; [apply bytes_eqb_eq in E; contradiction | reflexivity].
Qed.
Lemma rw_row_hit : forall i t, (i < CAT_N)%nat -> tok_bytes i = t -> row_from i t = Some i.
Proof. intros i t Hi <-. rewrite (row_from_step i _ Hi), bytes_eqb_refl. reflexivity. Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
(* the two wrappers fuzz_catalogue_row calls, at their trampolines *)
Hypothesis ASTRLEN : astrlen_realizes tfibsegs B STRLEN_ENTRY.
Hypothesis ABCMP : abcmp_realizes tfibsegs B A_BCMP_TR.

(* the entry state: the 64-byte frame, the shadow-base GOT cell and the shadow cell (AR's const cells), in
   the form of proofs/reac-pw/fuzz_qdisc/lib/A/QPgRt.v's rt_entry (160c9b4d5750) *)
Lemma rw_entry : forall ly S (W : world tfibsegs) regs mem md,
AR tfibsegs B ly S W mem md ->
(forall a, spZ regs - 64 <= a < spZ regs -> apresent (w_H W) mem a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
st_ok tfibsegs (Ereg regs rw_extra) ss_rwE (restrict (w_H W) (mkst regs (Z_to_bv 64 A_ROW) mem (seg_rom tfibsegs))).
Proof.
intros ly S W regs mem md HAR Hpres Hsp Hal.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs rw_extra).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold ss_rwE. apply (entry_st_ok_full tfibsegs); change (Ereg regs rw_extra) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold rw_regionsE, stack_region, got_region, bcell_region.
repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 627056) at 1.
apply (chunk_ok_val tfibsegs E _ 0 627056 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kgot).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 661240) at 1.
apply (chunk_ok_val tfibsegs E _ 0 661240 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents.
unfold rw_regionsE, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok rw_factsE]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32. rewrite !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* The strlen wrapper in the journal form: a pin copy of
   proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_Klib.v:146-196 aj_strlen_at
   (origin/ossv/recipes f26f9fbd87), on the concrete image tfibsegs, which also keeps the wrapper's
   same_but_materialized (pin_post_simple asks same_io of the call's model). *)
Lemma rw_aj_strlen_at : forall pc, astrlen_realizes tfibsegs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k (o : Z) raw,
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte tfibsegs W memT x (k + 1) 0 k ->
src_ok tfibsegs W regsT memT x (k + 1) ->
(forall a, x <= a <= x + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x (k + 1) ->
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) memT) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfibsegs (w_H W) memT a <> None) ->
aro_unowned tfibsegs B (aview tfibsegs (w_H W) memT) ->
SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom tfibsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k o raw
HJ Ha0 Hx0 Hk0 Hk1 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Htl Hro.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre tfibsegs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try zlia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x k HPRE Hlo2 Hpres2E Ha0 Hx0 Hk0 Hk1 Hxk Hfb Hsx
    ltac:(rewrite Hsp'; exact Hbx) Hmx Hrx Hhx Htl Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write tfibsegs B LAWS tfib_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hsame].
Qed.

(* The bcmp wrapper in the journal form: the kit's lib/Reusable/YCbq.v:2262 aj_bcmp_at on tfibsegs, with the
   wrapper's same_but_materialized kept (the kit's post drops it; pin_post_simple asks same_io). *)
Lemma rw_aj_bcmp_at : forall pc, abcmp_realizes tfibsegs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (o : Z) raw,
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok tfibsegs W regsT memT x n -> src_ok tfibsegs W regsT memT y n ->
(forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) -> (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) x n) ->
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) y n) ->
SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom tfibsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview tfibsegs (w_H W) memT (x + i) = aview tfibsegs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw
HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre tfibsegs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption; [zlia|]. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a) by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x y n HPRE Hlo2 Hpres2E Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy
ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write tfibsegs B LAWS tfib_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hsame].
Qed.

(* ------------------------------------------------------------------------------------------------
   The call's context: the variables and premises of tpin_row_specX at fuzz_catalogue_row and the table *)
Section w.
Variables (RLO RHI : Z) (TP DP : nat -> Z).
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S0 : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(ch : list (Z * Z * Z)) (sa n : Z) (sb : list byte).
Hypothesis HPK : pin_pre_kit tfibsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs ch T_row_STK EV_row.
Hypothesis H10 : getr regs 10 = w64 sa.
Hypothesis H11 : getr regs 11 = w64 n.
Hypothesis Hn : n = Z.of_nat (length sb).
Hypothesis Hn32 : 0 <= n < 2 ^ 32.
Hypothesis Hsa : 0 < sa.
Hypothesis Hsan : sa + n <= 2 ^ 63.
Hypothesis Hsb : YI00.garr8 tfibsegs (mrestrict (w_H W) memc) sa (pin_zbytes sb).
Hypothesis Hras : range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF sa n.
Hypothesis Hhull : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memc) sa n.
Hypothesis Hamr : amem_range sa n.
Hypothesis Hwin : forall x, sa <= x < sa + n -> ~ (spZ regs - T_row_STK <= x < spZ regs).
Hypothesis HCAT : pin_cat_ok tfibsegs (mrestrict (w_H W) memc) (aview tfibsegs (w_H W) memc) A_CAT_TBL TP DP.
Hypothesis HOFF : pin_cat_off_stack A_CAT_TBL TP regs T_row_STK.
Hypothesis HROD : arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H W) memc).

Definition rw_post : world tfibsegs -> config -> Prop :=
pin_post_simple tfibsegs B MT STK sp0 FP ly S0 W0 mem0 md0 own k regs T_row_STK EV_row
(fun _ => False) (fun regs2 _ _ => getr regs2 10 = w64 (row_ptr A_CAT_TBL sb)) lyc Sc W memc mdc.
(* the kept memory: every byte outside the window [sp - T_row_STK, sp) reads as at the call *)
Definition rw_keep (m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_row_STK <= a < spZ regs) -> aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) memc a.

Lemma rw_sp : alloc_ceiling <= spZ regs - T_row_STK /\ spZ regs <= 2 ^ 47 /\ spZ regs mod 16 = 0 /\ sp0 mod 16 = 0 /\
sp0 - STK <= spZ regs - T_row_STK /\ spZ regs <= sp0 /\ sp0 <= 2 ^ 47.
Proof.
destruct HPK as (HJ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
repeat split; lia.
Qed.
Lemma rw_keep_low : forall m, rw_keep m -> forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) memc a.
Proof. intros m KP a Ha. unfold rw_keep in KP. pose proof rw_sp as (Hc & _). pose proof asan_consts as (C1 & _). apply KP; lia. Qed.
(* the shadow bytes of a range below 2 ^ 47 read as at the call *)
Lemma rw_keep_ra : forall m a len, rw_keep m -> 0 <= a -> a + len <= 2 ^ 47 ->
range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF a len -> range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF a len.
Proof.
intros m a len KP Ha Hal. apply rw_ra_keep. intros x Hx. apply rw_keep_low; [exact KP|].
pose proof rw_sp as (Hc & _). pose proof asan_consts as (C1 & _).
change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). pose proof (rw_shadow_low x ltac:(lia)). lia.
Qed.
Lemma rw_keep_hull : forall m x len, rw_keep m -> 0 <= x -> 0 < len -> x + len <= 2 ^ 47 ->
shadow_hull_vis (aview tfibsegs (w_H W) memc) x len -> shadow_hull_vis (aview tfibsegs (w_H W) m) x len.
Proof.
intros m x len KP Hx Hl Hxl. apply rw_hull_keep. intros s Hs. apply rw_keep_low; [exact KP|].
pose proof rw_sp as (Hc & _). pose proof asan_consts as (C1 & _).
pose proof (rw_hull_low x len s Hx Hl Hxl Hs). lia.
Qed.

(* ------------------------------------------------------------------------------------------------
   The call-site lemmas *)
(* 0x81014, the strlen wrapper on row i's token: every premise of astrlen_realizes the journal-form call
   lemma asks, at a state whose memory memT keeps the call's bytes outside the window (rw_keep), whose stack
   window is present, and whose sp is the entry sp - 64. *)
Lemma pin_strlen_site_row : forall i (memT : word -> option byte) (regsT : bvmap 5 word),
(i < CAT_N)%nat -> rw_keep memT ->
(forall a, spZ regs - T_row_STK <= a < spZ regs -> apresent (w_H W) memT a) ->
spZ regsT = spZ regs - 64 ->
0 < TP i /\ 0 <= pin_tokn i /\ pin_tokn i + 1 < 2 ^ 32 /\ TP i + pin_tokn i + 1 <= 2 ^ 63 /\
first_byte tfibsegs W memT (TP i) (pin_tokn i + 1) 0 (pin_tokn i) /\
src_ok tfibsegs W regsT memT (TP i) (pin_tokn i + 1) /\
(forall a, TP i <= a <= TP i + pin_tokn i -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
amem_range (TP i) (pin_tokn i + 1) /\
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF (TP i) (pin_tokn i + 1) /\
shadow_hull_vis (aview tfibsegs (w_H W) memT) (TP i) (pin_tokn i + 1) /\
(forall a, TP i + pin_tokn i < a < TP i + pin_tokn i - (TP i + pin_tokn i) mod 8 + 8 -> aview tfibsegs (w_H W) memT a <> None) /\
aro_unowned tfibsegs B (aview tfibsegs (w_H W) memT).
Proof.
intros i memT regsT Hi KP PRES Hsp.
pose proof (rw_keep_low memT KP) as KL. unfold rw_keep in KP.
pose proof rw_sp as (Hceil & Hsp47 & Hal16 & Hsp0al & Hwlo & Hwhi & Hsp047).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCAT as (_ & _ & _ & _ & _ & Hrows). destruct (Hrows i Hi) as (_ & _ & _ & _ & HRO).
destruct HRO as (Hx0 & Hxb & Hx32 & HAM & Hg & Hxra & Hxhull & Hxtail).
change (Z.of_nat (length (tok_bytes i))) with (pin_tokn i) in *. pose proof (rw_amr_lt _ _ HAM) as Hlt.
pose proof HOFF as (_ & HOT). specialize (HOT i). unfold T_row_STK in *. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hlen : pin_tokn i = Z.of_nat (length (tok_bytes i))) by reflexivity.
assert (Hbyte : forall j, 0 <= j < pin_tokn i ->
  aview tfibsegs (w_H W) memT (TP i + j) = Some (bv_unsigned (nth (Z.to_nat j) (tok_bytes i) NUL))).
{ intros j Hj. rewrite KP by (try lia; apply HOT; lia).
  replace j with (Z.of_nat (Z.to_nat j)) at 1 by lia.
  rewrite (rw_garr8_aview _ _ _ _ (Z.to_nat j) Hg) by (rewrite rw_len_zb0; lia).
  rewrite rw_nth_zb by lia. reflexivity. }
assert (Hnul : aview tfibsegs (w_H W) memT (TP i + pin_tokn i) = Some 0).
{ rewrite KP by (try lia; apply HOT; lia). rewrite Hlen.
  rewrite (rw_garr8_aview _ _ _ _ (length (tok_bytes i)) Hg) by (rewrite rw_len_zb0; lia).
  apply f_equal. apply rw_nth_zb_end. }
split; [exact Hx0|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
{ split; [lia|]. split.
  - intros j Hj. exists (bv_unsigned (nth (Z.to_nat j) (tok_bytes i) NUL)). split; [exact (Hbyte j Hj)|].
    apply (tokens_no_nul i _ Hi). apply nth_In. lia.
  - intros _. exact Hnul. }
split.
{ intros a Ha. split.
  - destruct (Z.eq_dec a (TP i + pin_tokn i)) as [->|Hne]; [rewrite Hnul; discriminate|].
    replace a with (TP i + (a - TP i)) by lia. rewrite (Hbyte (a - TP i)) by lia. discriminate.
  - rewrite Hsp. pose proof (HOT a Hi ltac:(lia)). lia. }
split; [intros a Ha; rewrite Hsp; pose proof (HOT a Hi ltac:(lia)); lia|].
split; [exact (pin_amem_range_le _ (pin_tokn i + 1) (pin_tokn i + 8) ltac:(lia) HAM)|].
split; [apply rw_keep_ra; [exact KP | lia | lia | exact Hxra]|].
split; [apply rw_keep_hull; [exact KP | lia | lia | lia | exact Hxhull]|].
split.
{ intros a Ha. pose proof (Z.mod_pos_bound (TP i + pin_tokn i) 8 ltac:(lia)) as M8.
  destruct (Z_lt_le_dec a (spZ regs - (64 + 2 * ESTACK))) as [Hlo|Hge].
  - rewrite KP by lia. exact (Hxtail a Ha).
  - destruct (Z_lt_le_dec a (spZ regs)) as [Hin|Hhi].
    + apply (aview_some_of_apresent tfibsegs). apply PRES. lia.
    + rewrite KP by lia. exact (Hxtail a Ha). }
apply (aro_unowned_keep tfibsegs B (aview tfibsegs (w_H W) memc));
[exact (fun a Ha Ho He => HROD a (or_introl Ha) Ho He)|].
intros a (sg & Hsg & _ & Ha) _ _. apply KL.
assert (Hi' : in_img tfibsegs a) by (exists sg; split; [exact Hsg | exact Ha]).
pose proof (tfib_segs_low a Hi'). lia.
Qed.

(* 0x81028, the bcmp wrapper on (TP i, sa, n) when strlen gave n: every premise of abcmp_realizes the
   journal-form call lemma asks. *)
Lemma pin_bcmp_site : forall i (memT : word -> option byte) (regsT : bvmap 5 word),
(i < CAT_N)%nat -> rw_keep memT -> spZ regsT = spZ regs - 64 -> pin_tokn i = n ->
0 <= n < 2 ^ 32 /\ 0 <= TP i /\ TP i + n <= 2 ^ 63 /\ 0 <= sa /\ sa + n <= 2 ^ 63 /\
src_ok tfibsegs W regsT memT (TP i) n /\ src_ok tfibsegs W regsT memT sa n /\
(forall a, TP i <= a < TP i + n -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
(forall a, sa <= a < sa + n -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
amem_range (TP i) n /\ amem_range sa n /\
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF (TP i) n /\
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) (TP i) n) /\
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF sa n /\
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) sa n).
Proof.
intros i memT regsT Hi KP Hsp Hln.
pose proof (rw_keep_low memT KP) as KL. unfold rw_keep in KP.
pose proof rw_sp as (Hceil & Hsp47 & Hal16 & Hsp0al & Hwlo & Hwhi & Hsp047).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCAT as (_ & _ & _ & _ & _ & Hrows). destruct (Hrows i Hi) as (_ & _ & _ & _ & HRO).
destruct HRO as (Hx0 & Hxb & Hx32 & HAM & Hg & Hxra & Hxhull & Hxtail).
change (Z.of_nat (length (tok_bytes i))) with (pin_tokn i) in *. pose proof (rw_amr_lt _ _ HAM) as Hlt. pose proof (rw_amr_lt _ _ Hamr) as Hlts.
pose proof HOFF as (_ & HOT). specialize (HOT i). unfold T_row_STK in *. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (Hwin) as HW. unfold T_row_STK in HW.
rewrite <- Hln in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha. split.
  - rewrite KP by (try lia; apply HOT; lia).
    replace a with (TP i + Z.of_nat (Z.to_nat (a - TP i))) by lia.
    rewrite (rw_garr8_aview _ _ _ _ _ Hg) by (rewrite rw_len_zb0; unfold pin_tokn in *; lia). discriminate.
  - rewrite Hsp. pose proof (HOT a Hi ltac:(lia)). lia. }
split.
{ intros a Ha. split.
  - rewrite KP by (try lia; apply HW; lia).
    replace a with (sa + Z.of_nat (Z.to_nat (a - sa))) by lia.
    rewrite (rw_garr8_aview _ _ _ _ _ Hsb) by (rewrite rw_len_zb; lia). discriminate.
  - rewrite Hsp. pose proof (HW a ltac:(lia)). lia. }
split; [intros a Ha; rewrite Hsp; pose proof (HOT a Hi ltac:(lia)); lia|].
split; [intros a Ha; rewrite Hsp; pose proof (HW a ltac:(lia)); lia|].
split; [exact (pin_amem_range_le _ (pin_tokn i) (pin_tokn i + 8) ltac:(lia) HAM)|].
split; [exact Hamr|].
split; [apply rw_keep_ra; [exact KP | lia | lia |]; eapply range_addressable_sub; [exact Hxra | lia | lia]|].
split; [intros Hp; apply rw_keep_hull; [exact KP | lia | lia | lia |]; apply (rw_hull_sub _ _ _ (pin_tokn i + 1)); [lia | exact Hxhull]|].
split; [apply rw_keep_ra; [exact KP | lia | lia | exact Hras]|].
intros Hp. apply rw_keep_hull; [exact KP | lia | lia | lia | exact (Hhull Hp)].
Qed.


Lemma rw_B20 : bv_unsigned (ew (Ereg regs rw_extra) 2) = spZ regs.
Proof. rewrite (ew_Ereg_nat regs rw_extra 2 2%bv eq_refl). reflexivity. Qed.
Lemma rw_E320 : ew (Ereg regs rw_extra) 32 = Z_to_bv 64 SB.
Proof. exact (ew_Ereg_extra regs rw_extra 0). Qed.

(* ------------------------------------------------------------------------------------------------
   The walk's stop predicate: at a state of shape ss for row i, with the loop invariant
   row_of sb = row_from j sb, every run ends in the contract's post. *)
Definition rw_at (ss : sstate) (i j : nat) : Prop :=
forall E ms md, (i < CAT_N)%nat ->
(forall n, (n < 33)%nat -> ew E n = ew (Ereg regs rw_extra) n) -> ed E = ed (Ereg regs rw_extra) ->
ew E 33 = Z_to_bv 64 (row_addr A_CAT_TBL i) -> ew E 34 = Z_to_bv 64 (Z.of_nat (CAT_N - i)) ->
ajournal tfibsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
same_io mdc md -> rw_keep (ms_mem ms) -> row_of sb = row_from j sb ->
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) rw_post.
Definition rw_head (i : nat) : Prop := rw_at ss_H i i.
Definition rw_next (i : nat) : Prop := rw_at ss_N i (S i).

(* the walk tactics that name the call's context *)
Ltac rw_sp2 Ex H :=
lazymatch goal with B20 : bv_unsigned (ew ?E0 2) = ?spv, AG : forall n, _ -> ew ?Ea n = ew ?E0 n |- _ =>
assert (H : bv_unsigned (ew Ex 2) = spv) by (rw_ewpeel; rewrite (AG 2%nat) by lia; exact B20) end.
Ltac rw_awr_stk :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
let B2c := fresh "B2c" in rw_sp2 E B2c;
lazymatch type of B2c with _ = ?spv =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[reflexivity | rewrite B2c; lia | cbn [YP09.r_wlo YP09.r_whi]; unfold T_row_STK, ESTACK in *; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ] end;
clear B2c end.
Ltac rw_kwr Ef :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
let B2c := fresh "B2c" in rw_sp2 Ef B2c;
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
first [ rewrite B2c in Hb; unfold T_row_STK, ESTACK in *; lia | lia ] | ]);
destruct Hr.
Ltac rw_keep_run :=
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), KP : rw_keep ?m1 |- _ =>
let KP2 := fresh "KP" in
assert (KP2 : rw_keep m2)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
intros a Ha Hw; apply (rw_kept_run Ef rs H memc m1 m2 (spZ regs - T_row_STK) (spZ regs) KP HFr); [rw_kwr Ef | exact Ha | exact Hw]);
clear KP; rename KP2 into KP end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac rw_sio :=
repeat match goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progress (rewrite ?wvb_collapse in H) end;
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdn) _ =>
lazymatch goal with SIO : same_io mdc ?mdo |- _ =>
let S2 := fresh "SIO" in
assert (S2 : same_io mdc mdn)
by (eapply same_io_trans; [exact SIO | first [apply same_io_refl | apply rw_same_io_wvb | apply rw_same_io_wvb2]]);
clear SIO; rename S2 into SIO end end.
Ltac rw_peel_lia := repeat (first [ rewrite ew_havoc_old by lia | rewrite ew_ewset_other by lia ]).
Ltac rw_rebase HS :=
let AG2 := fresh "AG" in let HED2 := fresh "HED" in let Ev := fresh "E" in let HEv := fresh "HEv" in
lazymatch goal with AG : forall n, _ -> ew ?Ea n = ew ?E0 n, HED : ed ?Ea = ed ?E0 |- _ =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn; rewrite HEv; rw_peel_lia; apply AG; exact Hnn);
assert (HED2 : ed Ev = ed E0) by (rewrite HEv; cbn [ed havoc ewset]; exact HED);
repeat match goal with H : ew ?Eo ?m = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| E0 => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 m)) with
| true => let H2 := fresh H in assert (H2 : ew Ev m = v) by (rewrite HEv; rw_ewpeel; exact H); clear H; rename H2 into H
end end end;
clear HEv AG HED; rename AG2 into AG; rename HED2 into HED end end.
(* the re-seat after a wrapper call: lib/AU/YCep.v's reseat (image B's twin of lib/A/ACep.v), with the env's data
   part carried *)
Ltac rw_reseat HS HJ2 HP2 keep kept_tac :=
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 (SOff 32 0) [] ss) end in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
rw_rebase HS.
(* the two regions a wrapper call keeps: the frame and the row's token-pointer cell *)
Ltac rw_kept_call Hfr Hpres2 :=
first
[ lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
  let B2c := fresh "B2c" in rw_sp2 Ex B2c;
  eapply (region_kept_aview _ _ _ _ 2%nat (spZ regs)); [ exact B2c | | exact Hpres2 ];
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; unfold ESTACK in *; lia end
| lazymatch goal with E33 : ew ?Ex 33 = Z_to_bv 64 (row_addr A_CAT_TBL ?i) |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 33%nat) _ _ _ _ _) =>
  eapply (region_kept_aview _ _ _ _ 33%nat (row_addr A_CAT_TBL i));
  [ rewrite E33; apply unsigned_lit_small; unfold A_CAT_TBL in *; lia | | exact Hpres2 ];
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; unfold A_CAT_TBL, ESTACK in *; lia end ].
(* the `ret` leaf: the post pin_post_simple, with vtac closing the claim on a0 *)
Ltac rw_leaf vtac :=
lazymatch goal with HS : st_ok _ ?E _ (restrict (w_H W) ?ms) |- SRr _ _ (mkCfg ?ms ?md) _ =>
lazymatch goal with AG : forall n, _ -> ew E n = ew (Ereg _ _) n, HED : ed E = _, SIO : same_io mdc md,
  KP : rw_keep (ms_mem ms), Hra : YK0s.ret_ok (getr regs 1),
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ms) md _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
let R10 := fresh "R10" in rreg HS (10%bv : bv 5) R10;
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
unfold rw_post, pin_post_simple;
exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat' md);
split; [rewrite R1, (AG 1%nat) by lia; rewrite (ew_Ereg_nat regs rw_extra 1 1%bv eq_refl), Hra; reflexivity|];
split; [unfold EV_row; rewrite Z.add_0_r; exact (ajournal_materialize tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)|];
split; [eapply (aregs_preserved_of_st_ok tfibsegs _ E _ _ regs rw_extra HS);
  [split; [let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn; apply AG; lia | exact HED] | vm_compute; reflexivity]|];
split; [reflexivity|]; split; [apply Permutation_refl|];
split; [exact (same_io_trans _ _ _ SIO (rw_same_io_wvb md _ _))|];
split; [apply mo_le_refl; exact MTL|];
split; [let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in intros a Ha Hw _; exact (KP a Ha Hw) | rewrite R10; vtac]
end end.
Ltac rw_prelude :=
pose proof Hwx_tfa as Hwx; pose proof tfib_segs_low as Hsegs;
pose proof rw_sp as (Hceil & Hsp47 & Hal16 & Hsp0al & Hwlo & Hwhi & Hsp047);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof HPK as (_ & Hra & _ & Hgp & Htp & _);
pose proof rw_B20 as B20; pose proof rw_E320 as E320;
unfold T_row_STK in Hwlo, Hceil; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac rw_shok HS name :=
repeat match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msx) =>
assert (name : sh_ok tfibsegs (SOff 32 0) [] Ev (mrestrict (w_H W) (ms_mem msx))) by constructor end.

(* ------------------------------------------------------------------------------------------------
   Segment N, 0x81030: the next row, or the return of 0 after row 10 *)
Lemma rw_next_seg : forall i, ((S i < CAT_N)%nat -> rw_head (S i)) -> rw_next i.
Proof.
intros i IHH E ms md Hi AG HED E33 E34 HJ SIO KP HROW HS.
rw_prelude. pose proof (rw_row_bounds i Hi) as (Hr0 & Hr8 & Hr1). pose proof (rw_row_next i) as Hrn.
rw_shok HS SHOK.
(* 0x81030 .. 0x8103c, stop at 0x81040 bnez s6 *)
aj_run_tok tfibtbl_lib_ok HS HJ SHOK rw_Bspan; [rw_awr_stk|].
rw_keep_run. rw_sio. rw_rebase HS.
rw_shok HS SHOK. srr_branch_tok tfibtbl_lib_ok HS SHOK rw_Bspan.
- (* taken: 11 - i - 1 <> 0, a row is left; back to the head with row i + 1 *)
  rewrite branch_ne_U, (rw_U_offx _ 34 (Z.of_nat (CAT_N - i)) (-1)), U_lit in Hc by (first [exact E34 | unfold CAT_N in *; lia]).
  rewrite Z.mod_small in Hc by (unfold CAT_N in *; lia). apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hsi : (S i < CAT_N)%nat) by (unfold CAT_N in *; lia).
  pose proof (rw_row_bounds (S i) Hsi) as (Hs0 & Hs8 & Hs1).
  rw_shok HS SHOK1. aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK1 rw_Bspan 0x81004; [rw_awr_stk|].
  rw_keep_run. rw_sio. rw_rebase HS.
  (* the new row and count in the scratch atoms 40 / 41 *)
  rw_add_atom_win HS 40%nat (Z_to_bv 64 (row_addr A_CAT_TBL (S i))) E40.
  rw_add_atom_win HS 41%nat (Z_to_bv 64 (Z.of_nat (CAT_N - S i))) E41.
  rw_pin_by HS (8%bv : bv 5) (SOff 40 0) ltac:(rewrite sv_denot_SOff0; cbn [sv_denot]; rw_ewpeel;
    rewrite E40, E33, unsigned_lit_small by (unfold A_CAT_TBL in *; lia); rewrite Hrn; reflexivity).
  rw_pin_by HS (19%bv : bv 5) (SOff 40 0) ltac:(rewrite sv_denot_SOff0; cbn [sv_denot]; rw_ewpeel;
    rewrite E40, E33, unsigned_lit_small by (unfold A_CAT_TBL in *; lia); rewrite Hrn; reflexivity).
  rw_pin_by HS (21%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 40 0) (SLit 3)) (SOff 32 0))
    ltac:(rewrite (denot_shx _ 40 32 0 (row_addr A_CAT_TBL (S i)) SB);
      [| rw_ewpeel; exact E40 | rw_ewpeel; rewrite (AG 32%nat) by lia; exact E320 | unfold A_CAT_TBL, SB in *; lia ..];
      rewrite (rw_denot_sh37 _ 33 32 (row_addr A_CAT_TBL i) SB);
      [| rw_ewpeel; exact E33 | rw_ewpeel; rewrite (AG 32%nat) by lia; exact E320 | unfold A_CAT_TBL in *; lia | unfold SB; lia];
      rewrite Hrn, Z.add_0_r; reflexivity).
  rw_pin_by HS (22%bv : bv 5) (SOff 41 0) ltac:(rewrite sv_denot_SOff0; cbn [sv_denot]; rw_ewpeel;
    rewrite E41, E34, unsigned_lit_small by (unfold CAT_N in *; lia); f_equal; unfold CAT_N in *; lia).
  rw_facts_base HS. clear E33 E34.
  (* the head's atoms 33 / 34 re-made *)
  rw_add_atom_win HS 33%nat (Z_to_bv 64 (row_addr A_CAT_TBL (S i))) E33.
  add_fact HS 33%nat A_CAT_TBL (A_CAT_TBL + 2960) E33 ltac:(unfold A_CAT_TBL in *; lia).
  rw_add_atom_win HS 34%nat (Z_to_bv 64 (Z.of_nat (CAT_N - S i))) E34.
  add_fact HS 34%nat 1 11 E34 ltac:(unfold CAT_N in *; lia).
  rw_pin_by HS (8%bv : bv 5) (SOff 33 0) ltac:(rewrite !sv_denot_SOff0; rw_ewpeel; rewrite E33, E40; reflexivity).
  rw_pin_by HS (19%bv : bv 5) (SOff 33 0) ltac:(rewrite !sv_denot_SOff0; rw_ewpeel; rewrite E33, E40; reflexivity).
  rw_pin_by HS (21%bv : bv 5) rw_sh5 ltac:(unfold rw_sh5;
    rewrite (denot_shx _ 33 32 0 (row_addr A_CAT_TBL (S i)) SB);
      [| rw_ewpeel; exact E33 | rw_ewpeel; rewrite (AG 32%nat) by lia; exact E320 | unfold A_CAT_TBL, SB in *; lia ..];
    rewrite (denot_shx _ 40 32 0 (row_addr A_CAT_TBL (S i)) SB);
      [reflexivity | rw_ewpeel; exact E40 | rw_ewpeel; rewrite (AG 32%nat) by lia; exact E320 | unfold A_CAT_TBL, SB in *; lia ..]).
  rw_pin_by HS (22%bv : bv 5) (SOff 34 0) ltac:(rewrite !sv_denot_SOff0; rw_ewpeel; rewrite E34, E41; reflexivity).
  rw_join HS ss_H 2000%nat rw_deads_bv. rw_rebase HS.
  exact (IHH Hsi _ _ _ Hsi AG HED E33 E34 HJ SIO KP HROW HS).
- (* not taken: row 10 was the last; 0x81044 s0 = 0, the epilogue, ret with a0 = 0 = row_ptr cat sb *)
  rewrite branch_ne_U, (rw_U_offx _ 34 (Z.of_nat (CAT_N - i)) (-1)), U_lit in Hc by (first [exact E34 | unfold CAT_N in *; lia]).
  rewrite Z.mod_small in Hc by (unfold CAT_N in *; lia). apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hi10 : i = 10%nat) by (unfold CAT_N in *; lia). subst i.
  rw_shok HS SHOK1. aj_run_tok tfibtbl_lib_ok HS HJ SHOK1 rw_Bspan; [rw_awr_stk|].
  rw_keep_run. rw_sio. rw_rebase HS.
  rw_leaf ltac:(unfold row_ptr; rewrite HROW; reflexivity).
Qed.

(* ------------------------------------------------------------------------------------------------
   Segment H, 0x81004: the row's shadow check, the strlen and bcmp calls, the return of a matching row *)
Lemma rw_head_seg : forall i, rw_next i -> rw_head i.
Proof.
intros i IHN E ms md Hi AG HED E33 E34 HJ SIO KP HROW HS.
rw_prelude.
pose proof (rw_row_bounds i Hi) as (Hrw0 & Hrw8 & Hrw1).
pose proof HCAT as (_ & _ & _ & _ & Hcatra & Hrows).
destruct (Hrows i Hi) as (VTP & _ & BTP & _ & HRO).
pose proof HRO as (_ & _ & _ & _ & Hgtok & _).
pose proof HOFF as (HOT1 & HOT2). unfold T_row_STK in HOT1, HOT2.
(* atom 35 = TP i, and the row region holding it *)
rw_add_atom_win HS 35%nat (Z_to_bv 64 (TP i)) E35.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (RO : region_ok tfibsegs Ev (mrestrict (w_H W) (ms_mem ms)) rw_row_region) end.
{ unfold region_ok, rw_row_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rw_ewpeel. rewrite E33, unsigned_lit_small by (unfold A_CAT_TBL in *; lia).
  split; [unfold A_CAT_TBL in *; lia|]. split; [unfold A_CAT_TBL in *; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs _ _ (row_addr A_CAT_TBL i) 0 8 (SOff 35 0) (TP i)).
  - rewrite sv_denot_SOff0. exact E35.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - zside.
  - rewrite Z.add_0_r.
    apply (val_mem_kept tfibsegs (w_H W) (w_H W) memc (ms_mem ms) _ 8 (TP i)); [|exact VTP].
    intros kk Hkk. apply KP; [unfold A_CAT_TBL in *; lia | apply HOT1; unfold CAT_BYTES in *; lia]. }
lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
assert (AD : all_disjoint Ev rw_row_region (ss_mem ssv));
[ let rs := eval vm_compute in (ss_mem ssv) in change (all_disjoint Ev rw_row_region rs)
| ] end.
{ unfold rw_row_region. cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rw_ewpeel. rewrite E33, unsigned_lit_small by (unfold A_CAT_TBL in *; lia). rewrite (AG 2%nat) by lia. rewrite B20.
  split; [unfold A_CAT_TBL in *; lia | exact I]. }
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (ast_ok_add_region tfibsegs Ev ssv msv rw_row_region HS eq_refl RO AD) as HS3 end.
clear HS RO AD. rename HS3 into HS. norm_ss HS.
(* the shadow entry of the row's first granule: pin_cat_ok's range_addressable over the table *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (SHOK : sh_ok tfibsegs (SOff 32 0) rw_SH Ev (mrestrict (w_H W) (ms_mem ms))) end.
{ unfold sh_ok, rw_SH. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite (U_atom _ 32 SB) by (first [rw_ewpeel; rewrite (AG 32%nat) by lia; exact E320 | unfold SB; lia]).
  rewrite (U_atom _ 33 (row_addr A_CAT_TBL i)) by (first [rw_ewpeel; exact E33 | unfold A_CAT_TBL in *; lia]).
  split.
  - change (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) with (aview tfibsegs (w_H W) (ms_mem ms)).
    rewrite Z.add_0_r, Z.sub_0_r, SB_SHADOW_OFF.
    apply rw_keep_ra; [exact KP | unfold A_CAT_TBL in *; lia | unfold A_CAT_TBL in *; lia |].
    eapply range_addressable_sub; [exact Hcatra | lia | unfold CAT_BYTES in *; lia].
  - intros a Ha. unfold SB, A_CAT_TBL in *. lia. }
(* 0x81004 .. 0x81014: the check passes (shadow byte 0), s4 = TP i, to the strlen wrapper *)
aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK rw_Bspan STRLEN_ENTRY; [rw_awr_stk|].
rw_keep_run. rw_sio. rw_rebase HS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?ms1) =>
rreg HS (10%bv : bv 5) Ra0; rreg HS (1%bv : bv 5) Rra; rreg HS (2%bv : bv 5) Rsp;
rreg HS (3%bv : bv 5) Rgp; rreg HS (4%bv : bv 5) Rtp;
assert (EspT : spZ (ms_regs ms1) = spZ regs - 64)
  by (unfold spZ at 1; rewrite Rsp; rewrite (AG 2%nat) by lia; rewrite B20; apply unsigned_lit_small; lia);
destruct (pin_strlen_site_row i (ms_mem ms1) (ms_regs ms1) Hi KP
  ltac:(intros a Ha; apply Hpres1; unfold T_row_STK, ESTACK in *; lia) EspT)
  as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12);
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
change (Z_to_bv 64 268552) with (Z_to_bv 64 STRLEN_ENTRY);
eapply SRr_bind;
[ eapply (rw_aj_strlen_at STRLEN_ENTRY ASTRLEN W (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc _ k
    (TP i) (pin_tokn i) (spZ regs - 64 - sp0) (Z_to_bv 64 528408) HJ);
  [ rewrite Ra0; exact E35 | exact P1 | exact P2 | exact P3 | exact P4 | rewrite EspT; lia
  | apply rw_mod16; assumption | lia | unfold ESTACK; lia
  | rewrite Rgp, (AG 3%nat) by lia; rewrite (ew_Ereg_nat regs rw_extra 3 3%bv eq_refl); exact Hgp
  | rewrite Rtp, (AG 4%nat) by lia; rewrite (ew_Ereg_nat regs rw_extra 4 4%bv eq_refl); exact Htp
  | exact Rra | apply ret_ok_even; vm_compute; reflexivity
  | exact P5 | exact P6
  | intros a Ha; replace (sp0 + (spZ regs - 64 - sp0)) with (spZ (ms_regs ms1)) by lia; exact (P7 a Ha)
  | exact P8 | exact P9 | exact P10 | exact P11 | exact P12 ]
| ] end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Hfr & Hpres2 & Hsame).
assert (KP2 : rw_keep mem2)
  by (intros a Ha Hw; unfold T_row_STK in Hw; rewrite (Hfr a Ha) by (unfold ESTACK in *; lia); exact (KP a Ha Hw)).
unfold same_but_materialized in Hsame.
assert (SIO2 : same_io mdc md2) by (rewrite Hsame; exact (same_io_trans _ _ _ SIO (rw_same_io_wvb _ _ _))).
rw_reseat HS HJ2 HP2 [0; 1]%nat ltac:(rw_kept_call Hfr Hpres2).
clear KP SIO HJ Hfr Hpres2 Hsame. rename KP2 into KP. rename SIO2 into SIO. rename HJ2 into HJ.
rreg HS (10%bv : bv 5) R10.
lazymatch type of R10 with _ = ew ?Ex ?m =>
assert (A0 : U Ex (SOff m 0) = pin_tokn i)
  by (rewrite (rw_U_reg Ex m (w64 (pin_tokn i))) by (rewrite <- R10; exact Hres); unfold w64; apply unsigned_lit_small; lia) end.
assert (U11 : forall Ex, (forall n, (n < 33)%nat -> ew Ex n = ew (Ereg regs rw_extra) n) -> U Ex (SOff 11 0) = n).
{ intros Ex AGx. rewrite (rw_U_reg Ex 11 (w64 n)) by (rewrite (AGx 11%nat) by lia; rewrite (ew_Ereg_nat regs rw_extra 11 11%bv eq_refl); exact H11).
  unfold w64; apply unsigned_lit_small; lia. }
rw_shok HS SHOK. srr_branch_tok tfibtbl_lib_ok HS SHOK rw_Bspan.
- (* 0x81018 bne taken: strlen(token) <> n, the next row *)
  rewrite branch_ne_U, A0, (U11 _ AG) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  rw_shok HS SHOK1. aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK1 rw_Bspan 0x81030; [rw_awr_stk|].
  rw_keep_run. rw_sio. rw_rebase HS.
  rw_join HS ss_N 3000%nat rw_deads_bv. rw_rebase HS.
  apply (IHN _ _ _ Hi AG HED E33 E34 HJ SIO KP); [|exact HS].
  rewrite HROW. apply rw_row_skip; [exact Hi|]. intros Heq. apply Hc. unfold pin_tokn. rewrite Heq, Hn. reflexivity.
- (* not taken: strlen(token) = n; 0x8101c .. 0x81028, to the bcmp wrapper *)
  rewrite branch_ne_U, A0, (U11 _ AG) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hlen : length (tok_bytes i) = length sb) by (unfold pin_tokn in Hc; lia).
  rw_shok HS SHOK1. aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK1 rw_Bspan A_BCMP_TR; [rw_awr_stk|].
  rw_keep_run. rw_sio. rw_rebase HS.
  lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?ms2) =>
  rreg HS (10%bv : bv 5) Rb0; rreg HS (11%bv : bv 5) Rb1; rreg HS (12%bv : bv 5) Rb2;
  rreg HS (1%bv : bv 5) Rbra; rreg HS (2%bv : bv 5) Rbsp; rreg HS (3%bv : bv 5) Rbgp; rreg HS (4%bv : bv 5) Rbtp;
  assert (EspB : spZ (ms_regs ms2) = spZ regs - 64)
    by (unfold spZ at 1; rewrite Rbsp; rewrite (AG 2%nat) by lia; rewrite B20; apply unsigned_lit_small; lia);
  destruct (pin_bcmp_site i (ms_mem ms2) (ms_regs ms2) Hi KP EspB Hc)
    as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15);
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
  change (Z_to_bv 64 268580) with (Z_to_bv 64 A_BCMP_TR);
  eapply SRr_bind;
  [ eapply (rw_aj_bcmp_at A_BCMP_TR ABCMP W (ms_regs ms2) (ms_mem ms2) STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc _ k
      (TP i) sa n (spZ regs - 64 - sp0) (Z_to_bv 64 528428) HJ);
    [ rewrite Rb0; exact E35
    | rewrite Rb1, (AG 10%nat) by lia; rewrite (ew_Ereg_nat regs rw_extra 10 10%bv eq_refl); exact H10
    | rewrite Rb2, (AG 11%nat) by lia; rewrite (ew_Ereg_nat regs rw_extra 11 11%bv eq_refl); exact H11
    | exact Q1 | exact Q2 | exact Q3 | exact Q4 | exact Q5 | rewrite EspB; lia
    | apply rw_mod16; assumption | lia | unfold ESTACK; lia
    | rewrite Rbgp, (AG 3%nat) by lia; rewrite (ew_Ereg_nat regs rw_extra 3 3%bv eq_refl); exact Hgp
    | rewrite Rbtp, (AG 4%nat) by lia; rewrite (ew_Ereg_nat regs rw_extra 4 4%bv eq_refl); exact Htp
    | exact Rbra | apply ret_ok_even; vm_compute; reflexivity
    | exact Q6 | exact Q7
    | intros a Ha; replace (sp0 + (spZ regs - 64 - sp0)) with (spZ (ms_regs ms2)) by lia; exact (Q8 a Ha)
    | intros a Ha; replace (sp0 + (spZ regs - 64 - sp0)) with (spZ (ms_regs ms2)) by lia; exact (Q9 a Ha)
    | exact Q10 | exact Q11 | exact Q12 | exact Q13 | exact Q14 | exact Q15 ]
  | ] end.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hres3 & Hcmp & Hfr3 & Hpres3 & Hsame3).
  (* bcmp's result is 0 exactly when row i's token is sb *)
  assert (HEQ : v = w64 0 <-> tok_bytes i = sb).
  { rewrite Hcmp. rewrite (rw_bytes_eq (w_H W) memc (TP i) sa (tok_bytes i) sb Hgtok Hsb Hlen).
    change (Z.of_nat (length (tok_bytes i))) with (pin_tokn i). rewrite Hc.
    split; intros Hq j Hj.
    - rewrite <- (KP (TP i + j)), <- (KP (sa + j));
      first [ apply Hq; exact Hj | lia | (apply Hwin; lia) | (apply (HOT2 i); [exact Hi | lia]) ].
    - rewrite (KP (TP i + j)), (KP (sa + j));
      first [ apply Hq; exact Hj | lia | (apply Hwin; lia) | (apply (HOT2 i); [exact Hi | lia]) ]. }
  assert (KP3 : rw_keep mem3)
    by (intros a Ha Hw; unfold T_row_STK in Hw; rewrite (Hfr3 a Ha) by (unfold ESTACK in *; lia); exact (KP a Ha Hw)).
  unfold same_but_materialized in Hsame3.
  assert (SIO3 : same_io mdc md3) by (rewrite Hsame3; exact (same_io_trans _ _ _ SIO (rw_same_io_wvb _ _ _))).
  rw_reseat HS HJ3 HP3 [0; 1]%nat ltac:(rw_kept_call Hfr3 Hpres3).
  clear KP SIO HJ Hfr3 Hpres3 Hsame3 Hcmp. rename KP3 into KP. rename SIO3 into SIO. rename HJ3 into HJ.
  rreg HS (10%bv : bv 5) R10b.
  lazymatch type of R10b with _ = ew ?Ex ?m =>
  assert (A0b : U Ex (SOff m 0) = bv_unsigned v) by (apply rw_U_reg; rewrite <- R10b; exact Hres3) end.
  rw_shok HS SHOK2. srr_branch_tok tfibtbl_lib_ok HS SHOK2 rw_Bspan.
  + (* 0x8102c beqz taken: v = 0, row i's token is sb; 0x81048, the epilogue, ret with a0 = row_addr cat i *)
    rewrite branch_eq_U, A0b, U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
    assert (Heq : tok_bytes i = sb) by (apply HEQ; apply bv_eq; rewrite Hc0; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    rw_shok HS SHOK3. aj_run_tok tfibtbl_lib_ok HS HJ SHOK3 rw_Bspan; [rw_awr_stk|].
    rw_keep_run. rw_sio. rw_rebase HS.
    rw_leaf ltac:(rewrite E33; unfold row_ptr; rewrite HROW, (rw_row_hit i sb Hi Heq); reflexivity).
  + (* not taken: v <> 0, row i's token is not sb; the next row *)
    rewrite branch_eq_U, A0b, U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
    assert (Hne : tok_bytes i <> sb).
    { intros Heq. apply HEQ in Heq. rewrite Heq in Hc0. unfold w64 in Hc0. rewrite unsigned_lit_small in Hc0 by lia. lia. }
    rw_shok HS SHOK3. aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK3 rw_Bspan 0x81030; [rw_awr_stk|].
    rw_keep_run. rw_sio. rw_rebase HS.
    rw_join HS ss_N 3000%nat rw_deads_bv. rw_rebase HS.
    apply (IHN _ _ _ Hi AG HED E33 E34 HJ SIO KP); [|exact HS].
    rewrite HROW. apply rw_row_skip; [exact Hi | exact Hne].
Qed.

(* ------------------------------------------------------------------------------------------------
   The loop, by induction on the rows left *)
Lemma rw_loop : forall j i, (i + j = CAT_N)%nat -> rw_head i.
Proof.
induction j as [|j IH]; intros i Hij.
- intros E ms md Hi. exfalso. unfold CAT_N in *. lia.
- apply rw_head_seg. apply rw_next_seg. intros Hsi. apply IH. lia.
Qed.

(* ------------------------------------------------------------------------------------------------
   Segment 0, 0x80fb4: the prologue, re-seated on the head for row 0 *)
Lemma rw_top : SRr tfibsegs W (cfg_at tfibsegs A_ROW regs memc mdc) rw_post.
Proof.
rw_prelude.
pose proof HPK as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof (rw_entry lyc Sc W regs memc mdc HAR ltac:(intros a Ha; apply Hpres; lia) ltac:(lia) Hal16) as HS.
remember (Ereg regs rw_extra) as E eqn:HE in HS.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew (Ereg regs rw_extra) n) by (intros nn Hnn; subst E; reflexivity).
assert (HED : ed E = ed (Ereg regs rw_extra)) by (subst E; reflexivity).
clear HE.
assert (KP : rw_keep memc) by (intros a Ha Hw; reflexivity).
assert (SIO : same_io mdc mdc) by apply same_io_refl.
assert (SHOK : sh_ok tfibsegs (SOff 32 0) [] E (mrestrict (w_H W) memc)) by constructor.
unfold cfg_at. change (w64 A_ROW) with (Z_to_bv 64 A_ROW).
(* 0x80fb4 .. 0x81000 *)
aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK rw_Bspan 0x81004; [rw_awr_stk|].
rw_keep_run. rw_sio. rw_rebase HS.
(* s0 = s3 = 0x98000 -> atom 33, s6 = 11 -> atom 34, s5 = SB + 0x13000 -> rw_sh5 *)
rw_add_atom_win HS 33%nat (Z_to_bv 64 A_CAT_TBL) E33.
add_fact HS 33%nat A_CAT_TBL (A_CAT_TBL + 2960) E33 ltac:(unfold A_CAT_TBL; lia).
rw_add_atom_win HS 34%nat (Z_to_bv 64 11) E34.
add_fact HS 34%nat 1 11 E34 ltac:(lia).
rw_pin_by HS (8%bv : bv 5) (SOff 33 0) ltac:(rewrite sv_denot_SOff0; rw_ewpeel; rewrite E33; reflexivity).
rw_pin_by HS (19%bv : bv 5) (SOff 33 0) ltac:(rewrite sv_denot_SOff0; rw_ewpeel; rewrite E33; reflexivity).
rw_pin_by HS (22%bv : bv 5) (SOff 34 0) ltac:(rewrite sv_denot_SOff0; rewrite E34; reflexivity).
rw_pin_by HS (21%bv : bv 5) rw_sh5 ltac:(unfold rw_sh5; rewrite (denot_shx _ 33 32 0 A_CAT_TBL SB);
  [| rw_ewpeel; exact E33 | rw_ewpeel; rewrite (AG 32%nat) by lia; exact E320 | unfold A_CAT_TBL, SB; lia ..];
  cbn [sv_denot]; rw_ewpeel; rewrite (AG 32%nat) by lia; rewrite E320, unsigned_lit_small by (unfold SB; lia); reflexivity).
rw_join HS ss_H 2000%nat rw_deads_bv. rw_rebase HS.
apply (rw_loop CAT_N 0 eq_refl _ _ _ ltac:(unfold CAT_N; lia) AG HED);
[ rewrite E33; reflexivity | rewrite E34; reflexivity | exact HJ | exact SIO | exact KP | reflexivity | exact HS ].
Qed.

End w.

(* ================================================================================================
   The contract at fuzz_catalogue_row and the table fuzz_catalogue *)
Theorem pin_pb_rowX : forall RLO RHI TP DP, tpin_row_specX tfibsegs B MT RLO RHI A_ROW A_CAT_TBL TP DP.
Proof.
intros RLO RHI TP DP. unfold tpin_row_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch sa n sb
HPK H10 H11 Hn Hn32 Hsa Hsan Hsb Hras Hhull Hamr Hwin HCAT HOFF HROD.
eapply rw_top; eassumption.
Qed.
End d.
End b.

Print Assumptions pin_pb_rowX.

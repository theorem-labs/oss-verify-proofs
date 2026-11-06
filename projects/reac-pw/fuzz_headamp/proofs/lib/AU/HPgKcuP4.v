(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf8.v, with its module paths and module names changed; 86 of its 105 lines of code are new or changed and 64 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgKcA.v, with its module paths and module names changed; 1235 of its 1279 lines of code are new or changed and 61 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): part 4 of the piece "the key and the channel" of the walk of LLVMFuzzerTestOneInput
   (lib/AU/HPgKcuCut.v hku_P4_stmt), DOT 0x833c8 -> VAL 0x83490 / RF 0x836a0. Proves no function
   (kind: segment lemma).

   THE CODE (fuzz_headamp.c:86-138; at DOT s7 = the key, a0 = the key + 13 = rest, a1 = d, a3 = the sign flag
   (0 for '-'), a4 = nd, a7 = the key + d + nd, t0 = the byte after the digits, s5 = acc, ra = big)
     0x833c8 li a5,4; 0x833cc beqz a4 -> RF (no digit: BAD_KEY); 0x833d0 bnez a3 / 0x833d4 neg s5 (the sign);
       0x833d8 add a1,a1,a4 (used = d + nd); 0x833dc beqz a1 -> RF (never: nd >= 1);
       0x833e0 addi a2,a7,13; 0x833e4 bltu a2,a0 -> unimp (never); 0x833e8 li a0,46;
       0x833ec bne t0,a0 -> RF (no '.': BAD_KEY); 0x833f0 beqz a2 -> unimp (never);
       0x833f4 add a1,a1,s7; 0x833f8 addi a1,a1,13; 0x833fc li a0,-1; 0x83400 beq a1,a0 -> unimp (never)
     0x83404 sd ra,0x90(s1) (big in the real frame); 0x83408 addi s7,a7,14 (the name); 0x8340c / 0x83410 the
       literal 0x21380; 0x83414 mv a0,s7; 0x83418 jal 0x41c20 (strcmp)
     0x8341c / 0x83430 beqz a0 -> the found arms 0x83460 / 0x8346c; else the next literal 0x213a0 / 0x213c0 and
       `jal` 0x41c20 at 0x8342c / 0x83440
     0x83444 ld t5,0x110(s1); ld t6,0x108(s1); li a5,4; 0x83450 bnez a0 -> RF (no name: BAD_KEY); else
       (a6, s7) := (2, 0x37)
     0x83460 (a6, s7) := (0, 1) / 0x8346c (s7, a6) := (1, 1); 0x83474 ld t5,0x110(s1); ld t6,0x108(s1)
     0x8347c li a5,5; ld a0,0x90(s1); 0x83484 bnez a0 -> RF (big: OUT_OF_RANGE); li a0,47;
       0x8348c bltu a0,s5 -> RF (the channel out of range: OUT_OF_RANGE); else VAL 0x83490.

   HOW. Six block lemmas over the token engine (lib/Reusable YCbn.v / YCbq.v), each stated for any float state
   with the post kq_post (the world and the journal's end state kept, the I/O state, the registers outside clob,
   every byte outside a write set, and what the arm says of the new registers and memory): kq_dot_blk
   (0x833c8 .. 0x83400), kq_st_blk (0x83404 .. 0x83418, through a writable region based at s1 = R whose write
   window [R+0x90, R+0x98) lies inside the journal's own stack), kq_test_ph / kq_test_pad (after the first two
   strcmps; a read-only region gives t5 / t6 from R+0x110 / R+0x108), kq_test_sens (after the third),
   kq_tail_blk (0x8347c .. 0x8348c; big from R+0x90 and the channel from s5). Between them the three strcmps go
   through lib/AU/HPgKcuScmp.v hksu_strcmp_call at the cut's float state. kq_mid carries, relative to the DOT
   cut, the journal at the cut's end state, the I/O state, sp / gp / tp and the callee-saved registers of hku_L
   (s5 and s7 excepted: this part writes them), and every byte outside the callees' stack [R - 2 ESTACK, R) and
   the one save [R+0x90, R+0x98); hku_base3_kept rebuilds hqu_base3 from it, kq_L3_kept the cut lists,
   kq_x_kept x's bytes. The model is lib/Prog/HeadCheck/KeyFacts.v's (read_channel_eq, expect_key_read, cstr_id,
   no_nul_skipn, param_phantom / pad / sens / none, expect_cell_key) and PairFacts.v's (expect_cell_bad);
   nothing of it is restated here.

   Section hypotheses: errno_low (as lib/AU/HPgKcuLib.v, whose hku_base3_kept, hku_cstr_now and hku_keymem take
   it) and STRCMP (the strcmp wrapper's contract at 0x41c20 at every float state, lib/AU/HPgKcuScmp.v's Section
   hypothesis at segs = rsegs). segs_low is lib/AU/HPgSteps.v img_segs_low, a lemma of this tree. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require KeyFacts PairFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls HPgCallsStr.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgKcuCut HPgKcuLib HPgKcuScmp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgMem HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the code table ======================================== *)
Definition KQ_ST : Z := 0x83404.    (* the '.' is found: the save of big, the name, the first strcmp's arguments *)
Definition KQ_TL : Z := 0x8347c.    (* a name was found: a5 := 5, big and the channel tested *)
(* the 50 words 0x833c8 .. 0x8348c; VAL 0x83490 and RF 0x836a0 lie outside it *)
Definition kq_tbl : ctable := build_table rsegs HKU_DOT 50 TEmpty.
Lemma kq_tbl_ok : table_ok rsegs kq_tbl.
Proof. apply build_table_ok0. unfold HKU_DOT. lia. Qed.
Definition KQBx : sv := SOff 27 0.
Definition KQBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma kq_m1 : (-1) mod 2 ^ 64 = 2 ^ 64 - 1.
Proof. vm_compute. reflexivity. Qed.

Ltac kq_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
Ltac kq_run := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok kq_tbl_ok HS HJ SHOK KQBspan; [awr_ok_tac | ] end.
Ltac kq_run_to pc := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok kq_tbl_ok HS HJ SHOK KQBspan pc; [awr_ok_tac | ] end.
Ltac kq_branch Hc := lazymatch goal with HS : st_ok _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  srr_branch_tok kq_tbl_ok HS SHOK KQBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* the memory after a run over read-only regions is the memory before it *)
Ltac kq_mem :=
lazymatch goal with HF : frame_of ?E0 ?rs0 ?m0 (ms_mem ?ms1) |- _ =>
  let H := fresh "HMn" in
  pose proof (frame_of_read_only E0 rs0 m0 (ms_mem ms1) eq_refl HF) as H;
  first [ match goal with HM0 : ms_mem ?ms0 = _ |- _ =>
            lazymatch ms0 with ms1 => fail | _ => rewrite HM0 in H; clear HM0 end end
        | idtac ];
  let HM := fresh "HM" in rename H into HM end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac kq_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.

(* The value of a branch's two operands, whatever shape the engine's normalisation left them in: every atom is
   replaced by the value its ew hypothesis gives, the ALU is reduced, and the nested canonical wraps are
   collapsed and dropped (every bound a wrap needs is in the block's own hypotheses). *)
Ltac kq_atoms Hc :=
repeat match type of Hc with context [U ?E (SOff ?n ?c)] =>
  match goal with He : ew E n = Z_to_bv 64 ?v |- _ =>
    rewrite (U_atom_off E n v c He ltac:(lia) ltac:(lia)) in Hc end end.
Ltac kq_norm Hc :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in Hc;
rewrite ?U_SAlu, ?U_SLit in Hc;
cbn [zalu_raw] in Hc;
kq_atoms Hc;
unfold zcanon, M64 in Hc;
rewrite ?kq_m1 in Hc;
rewrite ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r in Hc;
try (rewrite !Z.mod_small in Hc by lia).
Ltac kq_bool Hc :=
first [ (apply negb_true_iff in Hc; first [apply Z.eqb_neq in Hc | apply Z.ltb_ge in Hc])
      | (apply negb_false_iff in Hc; first [apply Z.eqb_eq in Hc | apply Z.ltb_lt in Hc])
      | apply Z.eqb_eq in Hc | apply Z.ltb_lt in Hc
      | apply Z.eqb_neq in Hc | apply Z.ltb_ge in Hc ].
Ltac kq_dead Hc := exfalso; kq_norm Hc; kq_bool Hc; lia.

Section blk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

Definition kq_kept (regs regs2 : bvmap 5 word) (clob : list (bv 5)) : Prop :=
  forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r.

(* the state at a block's end pc: the world and the journal's end state as at its start, the I/O state, the
   registers outside clob, every byte outside Wr, and what Rg says of the new registers and memory *)
Definition kq_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (pc : Z) (clob : list (bv 5))
(Wr : Z -> Prop) (Rg : bvmap 5 word -> (word -> option byte) -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = cfg_at rsegs pc regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
kq_kept regs regs2 clob /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
Rg regs2 mem2.

Lemma kq_post_intro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob Wr Rg E' ss' ms md',
st_ok rsegs E' ss' (restrict (w_H W) ms) -> ss_resv ss' = None -> ss_pc ss' = pc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md' k -> same_io mdc md' ->
kq_kept regs (ms_regs ms) clob ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
Rg (ms_regs ms) (ms_mem ms) ->
kq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob Wr Rg W (mkCfg ms md').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob Wr Rg E' ss' ms md' HS Hr Hpc HJ Hio Hk Hm HR.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md'.
split; [|split; [exact HJ|]; split; [exact Hio|]; split; [exact Hk|]; split; [exact Hm | exact HR]].
rewrite (st_ok_restrict_mkst rsegs (w_H W) E' ss' ms HS Hr) at 1. rewrite Hpc. reflexivity.
Qed.

Lemma kq_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* `neg s5,s5` at 0x833d4 *)
Lemma kq_sub_neg : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_SUB (SLit 0) (SOff n 0)) = w64 (- v).
Proof.
intros E n v H Hv. rewrite denot_lit_U. unfold w64. rewrite U_SAlu, U_SLit, (U_atom E n v H Hv).
cbn [zalu_raw]. change (zcanon 0) with 0. unfold zcanon, M64. rewrite Z.sub_0_l. apply Z_to_bv_mod64.
Qed.

(* a 64-bit chunk of a region holds its value *)
Lemma kq_chunk_val : forall E m b (cs : list YP09.chunk) o e v,
Forall (YP09.chunk_ok rsegs E m b) cs -> In (YP09.mkChunk o (CVal 8 e)) cs ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem rsegs m (b + o) 8 v.
Proof.
intros E m b cs o e v Hcs Hin He Hv.
exact (val_of_chunk_ok rsegs E m b o 8 e v (proj1 (Forall_forall _ _) Hcs _ Hin) He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* a register's value at a leaf: the engine's sv of it *)
Ltac kq_reg := lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict ?H ?ms) |- getr (ms_regs ?ms) _ = _ =>
  rewrite (st_ok_restrict_reg rsegs H E' ss' ms _ HS); kq_sv end.
(* the registers outside clob: their sv is still their own atom *)
Ltac kq_keep := lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict ?H ?ms), HAE : env_agree 32 (Ereg ?rg ?ex) _
  |- kq_kept _ _ ?cl =>
  exact (regs_kept_of_st_ok rsegs E' ss' ms rg ex H cl HS HAE ltac:(vm_compute; reflexivity)) end.
(* a leaf of a block whose regions are read-only: kq_post from the run's last state *)
Ltac kq_leaf rgtac :=
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HM : ms_mem ?ms = _,
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    eapply kq_post_intro;
    [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact HJ | kq_io | kq_keep
    | intros ? _ _; rewrite HM; reflexivity
    | rgtac ]
  end.

(* ---------------- DOT 0x833c8 .. 0x83400: no digit, the sign, the '.' test ---------------- *)
Definition kq_dot_clob : list (bv 5) := [10; 11; 12; 15; 21]%bv.

(* the dead `beqz a1` 0x833dc, the dead `bltu a2,a0` 0x833e4, the '.' test 0x833ec, the dead `beqz a2` 0x833f0
   and the dead `beq a1,a0` 0x83400, from the state after the sign *)
Ltac kq_dot_tail Hnz rgtac :=
  kq_run; kq_mem;
  let Hb2 := fresh "Hb2" in kq_branch Hb2; [ kq_dead Hb2 | ];
  kq_run; kq_mem;
  let Hb3 := fresh "Hb3" in kq_branch Hb3; [ kq_dead Hb3 | ];
  kq_run; kq_mem;
  let Hb4 := fresh "Hb4" in kq_branch Hb4; kq_norm Hb4;
  [ apply negb_true_iff, Z.eqb_neq in Hb4;
    kq_run; kq_mem; apply SRr_ret; cbv beta; right; left;
    split; [exact Hnz|]; split; [lia|];
    kq_leaf ltac:(kq_reg; reflexivity)
  | apply negb_false_iff, Z.eqb_eq in Hb4;
    kq_run; kq_mem;
    let Hb5 := fresh "Hb5" in kq_branch Hb5; [ kq_dead Hb5 | ];
    kq_run; kq_mem;
    let Hb6 := fresh "Hb6" in kq_branch Hb6; [ kq_dead Hb6 | ];
    kq_run_to KQ_ST; kq_mem; apply SRr_ret; cbv beta; right; right;
    split; [exact Hnz|]; split; [lia|];
    kq_leaf ltac:(rgtac) ].

Lemma kq_dot_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (K d nd acc c fl : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 23) = w64 K -> getr regs (Z_to_bv 5 10) = w64 (K + 13) ->
getr regs (Z_to_bv 5 11) = w64 d -> getr regs (Z_to_bv 5 13) = w64 fl ->
getr regs (Z_to_bv 5 14) = w64 nd -> getr regs (Z_to_bv 5 17) = w64 (K + d + nd) ->
getr regs (Z_to_bv 5 21) = w64 acc -> getr regs (Z_to_bv 5 5) = w64 c ->
0x4000 <= K -> K + 160 <= 2 ^ 47 -> 0 <= d <= 45 -> 0 <= nd <= 45 -> (fl = 0 \/ fl = 1) ->
0 <= c < 256 -> 0 <= acc <= 10000009 ->
SRr rsegs W (cfg_at rsegs HKU_DOT regs memc mdc)
(fun W2 c2 =>
 (nd = 0 /\ kq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF kq_dot_clob
    (fun _ => False) (fun regs2 _ => getr regs2 (Z_to_bv 5 15) = w64 4) W2 c2) \/
 (nd <> 0 /\ c <> 46 /\ kq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF kq_dot_clob
    (fun _ => False) (fun regs2 _ => getr regs2 (Z_to_bv 5 15) = w64 4) W2 c2) \/
 (nd <> 0 /\ c = 46 /\ kq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs KQ_ST kq_dot_clob
    (fun _ => False)
    (fun regs2 _ => getr regs2 (Z_to_bv 5 21) = w64 (if fl =? 0 then - acc else acc)) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs K d nd acc c fl HJ
  H23 H10 H11 H13 H14 H17 H21 H5 HK0 HK1 Hd Hnd Hfl Hc Hacc.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs []) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E23 : ew (Ereg regs []) 23 = Z_to_bv 64 K) by (rewrite (EA 23%nat (Z_to_bv 5 23) eq_refl); exact H23).
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 (K + 13)) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (Ereg regs []) 11 = Z_to_bv 64 d) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E13 : ew (Ereg regs []) 13 = Z_to_bv 64 fl) by (rewrite (EA 13%nat (Z_to_bv 5 13) eq_refl); exact H13).
assert (E14 : ew (Ereg regs []) 14 = Z_to_bv 64 nd) by (rewrite (EA 14%nat (Z_to_bv 5 14) eq_refl); exact H14).
assert (E17 : ew (Ereg regs []) 17 = Z_to_bv 64 (K + d + nd))
  by (rewrite (EA 17%nat (Z_to_bv 5 17) eq_refl); exact H17).
assert (E21 : ew (Ereg regs []) 21 = Z_to_bv 64 acc) by (rewrite (EA 21%nat (Z_to_bv 5 21) eq_refl); exact H21).
assert (E5 : ew (Ereg regs []) 5 = Z_to_bv 64 c) by (rewrite (EA 5%nat (Z_to_bv 5 5) eq_refl); exact H5).
assert (HS : st_ok rsegs (Ereg regs []) (mkSS HKU_DOT sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HKU_DOT) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs KQBx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl).
clear HE EA.
unfold cfg_at. change (w64 HKU_DOT) with (Z_to_bv 64 HKU_DOT).
(* 0x833c8 li a5,4; stop at 0x833cc beqz a4 *)
kq_run. kq_mem.
kq_branch Hb0; kq_norm Hb0.
- (* no digit: RF with BAD_KEY *)
  apply Z.eqb_eq in Hb0.
  kq_run. kq_mem. apply SRr_ret. cbv beta. left. split; [lia|].
  kq_leaf ltac:(kq_reg; reflexivity).
- apply Z.eqb_neq in Hb0.
  assert (Hnz : nd <> 0) by lia.
  kq_run. kq_mem.
  (* 0x833d0 bnez a3 *)
  kq_branch Hb1; kq_norm Hb1.
  + (* a3 <> 0: no `neg` *)
    apply negb_true_iff, Z.eqb_neq in Hb1.
    assert (Hf1 : fl = 1) by lia. subst fl.
    kq_dot_tail Hnz ltac:(kq_reg; rewrite kq_denot0, E21; reflexivity).
  + (* a3 = 0: s5 := - s5 *)
    apply negb_false_iff, Z.eqb_eq in Hb1.
    assert (Hf0 : fl = 0) by lia. subst fl.
    kq_dot_tail Hnz ltac:(kq_reg; rewrite (kq_sub_neg E 21 acc E21) by lia; reflexivity).
Qed.

(* ---------------- 0x83404 .. 0x83418: the save of big, the name, the first strcmp's arguments ---------------- *)
Definition kq_R1 : YP09.region := YP09.mkRegion (Some 9%nat) 0x90 0x98 0x90 0x98 [].
Definition kq_wr1 (R : Z) : Z -> Prop := fun a => R + 0x90 <= a < R + 0x98.
(* the real frame's base R (s1, atom 9) lies above the allocator's ceiling, far from the shadow band: what the
   token engine's static check asks of a writable region based at s1 *)
Definition kq_G9 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 0)] [] [].

Lemma kq_st_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R A tb : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 17) = w64 A -> getr regs (Z_to_bv 5 1) = w64 tb ->
2 ^ 46 <= R -> R <= 2 ^ 47 -> sp0 - STK <= R + 0x90 -> R + 0x98 <= sp0 ->
0 <= A -> A + 14 < 2 ^ 64 -> 0 <= tb < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs KQ_ST regs memc mdc)
(kq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs B_STRCMP [1; 10; 11; 23]%bv (kq_wr1 R)
  (fun regs2 mem2 => getr regs2 (Z_to_bv 5 1) = w64 RB_STRCMP1 /\
    getr regs2 (Z_to_bv 5 10) = w64 (A + 14) /\ getr regs2 (Z_to_bv 5 23) = w64 (A + 14) /\
    getr regs2 (Z_to_bv 5 11) = w64 B_HPH /\
    val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x90) 8 tb)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R A tb HJ H9 H17 H1
  HR0 HR1 Hlo Hhi HA0 HA1 Htb.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs []) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E9 : ew (Ereg regs []) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E17 : ew (Ereg regs []) 17 = Z_to_bv 64 A) by (rewrite (EA 17%nat (Z_to_bv 5 17) eq_refl); exact H17).
assert (E1 : ew (Ereg regs []) 1 = Z_to_bv 64 tb) by (rewrite (EA 1%nat (Z_to_bv 5 1) eq_refl); exact H1).
assert (U9 : bv_unsigned (ew (Ereg regs []) 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs []) (mkSS KQ_ST sr_atoms [kq_R1] None kq_G9)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 KQ_ST) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold kq_R1.
    apply (hm_rw_region rsegs _ (w_H W) memc 9 R); [exact U9 | lia | lia | | constructor].
    intros o Ho. apply Hpres. lia.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [kq_G9 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok rsegs KQBx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl).
clear HE EA.
unfold cfg_at. change (w64 KQ_ST) with (Z_to_bv 64 KQ_ST).
aj_run_tok kq_tbl_ok HS HJ SHOK KQBspan.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0)); [reflexivity | rewrite U9; ring | cbn; lia
  | cbn; lia | apply awr_ok_nil]. }
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) _ |- _ =>
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRg;
  destruct HRg as (_ & _ & _ & Hch0);
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch0; rewrite U9 in Hch0;
  apply SRr_ret; eapply kq_post_intro;
  [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity | eassumption | kq_io | kq_keep
  | intros a Ha Hw; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
    intros (rg & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val kq_R1] in Hr; rewrite U9 in Hr;
    rewrite unsigned_lit_small in Hr by lia; apply Hw; unfold kq_wr1; lia
  | ]
end.
split; [kq_reg; reflexivity|].
split; [kq_reg; rewrite denot_lit_U; unfold w64; f_equal;
  rewrite (U_atom_off E 17 A 14 E17) by lia; reflexivity|].
split; [kq_reg; rewrite denot_lit_U; unfold w64; f_equal;
  rewrite (U_atom_off E 17 A 14 E17) by lia; reflexivity|].
split; [kq_reg; reflexivity|].
replace (R + 0x90) with (R + 144) by reflexivity.
apply (kq_chunk_val _ _ R _ 144 (SOff 1 0) tb Hch0); [cbn; tauto | rewrite kq_denot0; exact E1 | exact Htb].
Qed.

(* ---------------- after a strcmp: the reloads of t5 / t6 read the real frame ---------------- *)
(* R+0x108 = t6's value (atom 32), R+0x110 = t5's (atom 33) *)
Definition kq_Rd : YP09.region := YP09.mkRegion (Some 9%nat) 0x108 0x118 0 0
  [YP09.mkChunk 0x108 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x110 (CVal 8 (SOff 33 0))].
Definition kq_ss_d (pc : Z) : sstate := mkSS pc sr_atoms [kq_Rd] None (mkFacts [] [] []).

Lemma kq_entry_d : forall (W : world rsegs) (regs : bvmap 5 word) memc pc (R t6v t5v : Z),
getr regs (Z_to_bv 5 9) = w64 R -> 0 <= R -> R + 0x118 <= 2 ^ 64 ->
0 <= t6v < 2 ^ 64 -> 0 <= t5v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 t6v ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 t5v ->
st_ok rsegs (Ereg regs [w64 t6v; w64 t5v]) (kq_ss_d pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros W regs memc pc R t6v t5v H9 HR0 HR1 Ht6 Ht5 V6 V5.
assert (U9 : bv_unsigned (ew (Ereg regs [w64 t6v; w64 t5v]) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), H9. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold kq_Rd.
  apply (hm_ro_region rsegs _ (w_H W) memc 9 R); [exact U9 | lia | lia |].
  constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val rsegs _ _ R 0x108 8 (SOff 32 0) t6v); [| cbn; lia | cbn; lia | exact V6].
    rewrite kq_denot0. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
  + apply (chunk_ok_val rsegs _ _ R 0x110 8 (SOff 33 0) t5v); [| cbn; lia | cbn; lia | exact V5].
    rewrite kq_denot0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity.
- cbn. tauto.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.

(* the strcmp against "phantom" (0x8341c) or "pad" (0x83430) has returned v: v = 0 sets a6 = p, s7 = smax,
   reloads t5 and t6 and goes to the tail; else the next strcmp's arguments (a0 = the name, a1 = lit, ra) *)
Definition kq_test_stmt (pc0 ra lit p smax : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R v t6v t5v : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 v ->
0 <= R -> R + 0x118 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= t6v < 2 ^ 64 -> 0 <= t5v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 t6v ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 t5v ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(fun W2 c2 =>
 (v = 0 /\ kq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs KQ_TL [16; 23; 30; 31]%bv
    (fun _ => False)
    (fun regs2 _ => getr regs2 (Z_to_bv 5 16) = w64 p /\ getr regs2 (Z_to_bv 5 23) = w64 smax /\
       getr regs2 (Z_to_bv 5 30) = w64 t5v /\ getr regs2 (Z_to_bv 5 31) = w64 t6v) W2 c2) \/
 (v <> 0 /\ kq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs B_STRCMP [1; 10; 11]%bv
    (fun _ => False)
    (fun regs2 _ => getr regs2 (Z_to_bv 5 1) = w64 ra /\ getr regs2 (Z_to_bv 5 10) = getr regs (Z_to_bv 5 23) /\
       getr regs2 (Z_to_bv 5 11) = w64 lit) W2 c2)).

Ltac kq_test_proof pc0 :=
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R v t6v t5v HJ H9 H10 HR0 HR1 Hv Ht6 Ht5 V6 V5;
pose proof img_wx as Hwx; pose proof img_segs_low as Hsegs; pose proof (AR_laws_ok rsegs B) as LAWS;
pose proof (kq_entry_d W regs memc pc0 R t6v t5v H9 HR0 HR1 Ht6 Ht5 V6 V5) as HS;
assert (E10 : ew (Ereg regs [w64 t6v; w64 t5v]) 10 = Z_to_bv 64 v)
  by (rewrite (ew_Ereg_nat regs _ 10 (Z_to_bv 5 10) eq_refl); exact H10);
assert (E23 : ew (Ereg regs [w64 t6v; w64 t5v]) 23 = getr regs (Z_to_bv 5 23))
  by exact (ew_Ereg_nat regs _ 23 (Z_to_bv 5 23) eq_refl);
assert (E32 : ew (Ereg regs [w64 t6v; w64 t5v]) 32 = w64 t6v) by exact (ew_Ereg_extra regs _ 0);
assert (E33 : ew (Ereg regs [w64 t6v; w64 t5v]) 33 = w64 t5v) by exact (ew_Ereg_extra regs _ 1);
assert (SHOK : sh_ok rsegs KQBx [] (Ereg regs [w64 t6v; w64 t5v]) (mrestrict (w_H W) memc)) by constructor;
remember (Ereg regs [w64 t6v; w64 t5v]) as E eqn:HE;
assert (HAE : env_agree 32 (Ereg regs [w64 t6v; w64 t5v]) E) by (subst E; apply env_agree_refl);
clear HE;
unfold cfg_at; change (w64 pc0) with (Z_to_bv 64 pc0);
kq_run; kq_mem;
let Hb := fresh "Hb" in
kq_branch Hb; rewrite branch_eq_U, (U_atom E 10 v E10), (U_lit E 0) in Hb by lia;
[ apply Z.eqb_eq in Hb; kq_run_to KQ_TL; kq_mem; apply SRr_ret; cbv beta; left; split; [exact Hb|];
  kq_leaf ltac:(split; [kq_reg; reflexivity|]; split; [kq_reg; reflexivity|];
    split; kq_reg; rewrite kq_denot0; assumption)
| apply Z.eqb_neq in Hb; kq_run; kq_mem; apply SRr_ret; cbv beta; right; split; [exact Hb|];
  kq_leaf ltac:(split; [kq_reg; reflexivity|];
    split; [kq_reg; rewrite kq_denot0; exact E23 | kq_reg; reflexivity]) ].

Lemma kq_test_ph : kq_test_stmt RB_STRCMP1 RB_STRCMP2 B_HPAD HA_PHANTOM 1.
Proof. unfold kq_test_stmt. kq_test_proof RB_STRCMP1. Qed.
Lemma kq_test_pad : kq_test_stmt RB_STRCMP2 RB_STRCMP3 B_HSENS HA_PAD 1.
Proof. unfold kq_test_stmt. kq_test_proof RB_STRCMP2. Qed.

(* the strcmp against "sens" (0x83444) has returned v: t5 and t6 reloaded, a5 := BAD_KEY; v <> 0 goes to RF,
   v = 0 sets a6 = SENS, s7 = SENS_MAX and goes to the tail *)
Lemma kq_test_sens : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R v t6v t5v : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 v ->
0 <= R -> R + 0x118 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= t6v < 2 ^ 64 -> 0 <= t5v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 t6v ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 t5v ->
SRr rsegs W (cfg_at rsegs RB_STRCMP3 regs memc mdc)
(fun W2 c2 =>
 (v <> 0 /\ kq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF [15; 30; 31]%bv
    (fun _ => False)
    (fun regs2 _ => getr regs2 (Z_to_bv 5 15) = w64 REFUSE_BAD_KEY /\
       getr regs2 (Z_to_bv 5 30) = w64 t5v /\ getr regs2 (Z_to_bv 5 31) = w64 t6v) W2 c2) \/
 (v = 0 /\ kq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs KQ_TL [15; 16; 23; 30; 31]%bv
    (fun _ => False)
    (fun regs2 _ => getr regs2 (Z_to_bv 5 16) = w64 HA_SENS /\ getr regs2 (Z_to_bv 5 23) = w64 HA_SENS_MAX /\
       getr regs2 (Z_to_bv 5 30) = w64 t5v /\ getr regs2 (Z_to_bv 5 31) = w64 t6v) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R v t6v t5v HJ H9 H10 HR0 HR1 Hv Ht6 Ht5 V6 V5.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (kq_entry_d W regs memc RB_STRCMP3 R t6v t5v H9 HR0 HR1 Ht6 Ht5 V6 V5) as HS.
assert (E10 : ew (Ereg regs [w64 t6v; w64 t5v]) 10 = Z_to_bv 64 v)
  by (rewrite (ew_Ereg_nat regs _ 10 (Z_to_bv 5 10) eq_refl); exact H10).
assert (E32 : ew (Ereg regs [w64 t6v; w64 t5v]) 32 = w64 t6v) by exact (ew_Ereg_extra regs _ 0).
assert (E33 : ew (Ereg regs [w64 t6v; w64 t5v]) 33 = w64 t5v) by exact (ew_Ereg_extra regs _ 1).
assert (SHOK : sh_ok rsegs KQBx [] (Ereg regs [w64 t6v; w64 t5v]) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs [w64 t6v; w64 t5v]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [w64 t6v; w64 t5v]) E) by (subst E; apply env_agree_refl).
clear HE.
unfold cfg_at. change (w64 RB_STRCMP3) with (Z_to_bv 64 RB_STRCMP3).
kq_run. kq_mem.
kq_branch Hb; rewrite branch_ne_U, (U_atom E 10 v E10), (U_lit E 0) in Hb by lia.
- apply negb_true_iff, Z.eqb_neq in Hb. kq_run. kq_mem. apply SRr_ret; cbv beta; left; split; [exact Hb|].
  kq_leaf ltac:(split; [kq_reg; reflexivity|]; split; kq_reg; rewrite kq_denot0; assumption).
- apply negb_false_iff, Z.eqb_eq in Hb. kq_run_to KQ_TL. kq_mem. apply SRr_ret; cbv beta; right; split; [exact Hb|].
  kq_leaf ltac:(split; [kq_reg; reflexivity|]; split; [kq_reg; reflexivity|];
    split; kq_reg; rewrite kq_denot0; assumption).
Qed.

(* ---------------- the tail 0x8347c .. 0x8348c: a5 := OUT_OF_RANGE, big reloaded, the range tests ---------------- *)
Definition kq_Rt : YP09.region := YP09.mkRegion (Some 9%nat) 0x90 0x98 0 0
  [YP09.mkChunk 0x90 (CVal 8 (SOff 32 0))].
Lemma kq_tail_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R tb chw : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 21) = w64 chw ->
0 <= R -> R + 0x98 <= 2 ^ 64 -> 0 <= tb < 2 ^ 64 -> 0 <= chw < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x90) 8 tb ->
SRr rsegs W (cfg_at rsegs KQ_TL regs memc mdc)
(fun W2 c2 =>
 ((tb <> 0 \/ 47 < chw) /\ kq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF [10; 15]%bv
    (fun _ => False) (fun regs2 _ => getr regs2 (Z_to_bv 5 15) = w64 REFUSE_OUT_OF_RANGE) W2 c2) \/
 (tb = 0 /\ chw <= 47 /\ kq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_VAL [10; 15]%bv
    (fun _ => False) (fun regs2 _ => getr regs2 (Z_to_bv 5 15) = w64 REFUSE_OUT_OF_RANGE) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R tb chw HJ H9 H21 HR0 HR1 Htb Hch Vb.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (U9 : bv_unsigned (ew (Ereg regs [w64 tb]) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), H9. apply unsigned_lit_small. lia. }
assert (E21 : ew (Ereg regs [w64 tb]) 21 = Z_to_bv 64 chw)
  by (rewrite (ew_Ereg_nat regs _ 21 (Z_to_bv 5 21) eq_refl); exact H21).
assert (E32 : ew (Ereg regs [w64 tb]) 32 = Z_to_bv 64 tb) by exact (ew_Ereg_extra regs _ 0).
assert (HS : st_ok rsegs (Ereg regs [w64 tb]) (mkSS KQ_TL sr_atoms [kq_Rt] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 KQ_TL) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold kq_Rt.
    apply (hm_ro_region rsegs _ (w_H W) memc 9 R); [exact U9 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ R 0x90 8 (SOff 32 0) tb);
      [rewrite kq_denot0; exact E32 | cbn; lia | cbn; lia | exact Vb].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs KQBx [] (Ereg regs [w64 tb]) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs [w64 tb]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [w64 tb]) E) by (subst E; apply env_agree_refl).
clear HE.
unfold cfg_at. change (w64 KQ_TL) with (Z_to_bv 64 KQ_TL).
kq_run. kq_mem.
kq_branch Hb; rewrite branch_ne_U, (U_atom E 32 tb E32), (U_lit E 0) in Hb by lia.
- apply negb_true_iff, Z.eqb_neq in Hb. kq_run. kq_mem. apply SRr_ret; cbv beta; left; split; [left; exact Hb|].
  kq_leaf ltac:(kq_reg; reflexivity).
- apply negb_false_iff, Z.eqb_eq in Hb. kq_run. kq_mem.
  kq_branch Hc1; rewrite branch_ltu_U, (U_atom E 21 chw E21), (U_lit E 47) in Hc1 by lia.
  + apply Z.ltb_lt in Hc1. kq_run. kq_mem. apply SRr_ret; cbv beta; left; split; [right; exact Hc1|].
    kq_leaf ltac:(kq_reg; reflexivity).
  + apply Z.ltb_ge in Hc1. kq_run. kq_mem. apply SRr_ret; cbv beta; right.
    split; [exact Hb|]. split; [exact Hc1|].
    kq_leaf ltac:(kq_reg; reflexivity).
Qed.

End blk.

(* ======================================== the model ======================================== *)
(* the 64-bit word of a channel ch with |ch| <= 10000009: unsigned <= 47 exactly when 0 <= ch <= 47 *)
Lemma kq_chw : forall ch, -10000009 <= ch <= 10000009 -> (ch mod 2 ^ 64 <= 47 <-> 0 <= ch <= 47).
Proof.
intros ch H. destruct (Z_lt_le_dec ch 0) as [Hn|Hp].
- rewrite <- (Z.mod_add ch 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.
Lemma kq_res_word : forall c1 c2, bv_unsigned (w64 (hksu_res c1 c2)) = 0 <-> hksu_res c1 c2 = 0.
Proof.
intros c1 c2. destruct (hksu_res_range c1 c2) as [E|[E|E]]; rewrite E; vm_compute; split; intros H;
  try discriminate H; reflexivity.
Qed.
Lemma kq_prefix_len : length HA_PREFIX = 13%nat.
Proof. vm_compute. reflexivity. Qed.
(* the name after the '.' is a suffix of the key *)
Lemma kq_garr8_suffix : forall (m : word -> option byte) a (l : list byte) j,
garr8 rsegs m a (hd_zbytes l ++ [0]) -> (j <= length l)%nat ->
garr8 rsegs m (a + Z.of_nat j) (hd_zbytes (skipn j l) ++ [0]).
Proof.
intros m a l j H Hj. rewrite <- (firstn_skipn j l) in H. unfold hd_zbytes in *.
rewrite map_app, <- app_assoc in H. apply garr8_app in H as [_ H].
rewrite length_map, length_firstn in H. replace (Nat.min j (length l)) with j in H by lia. exact H.
Qed.

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
(* The strcmp wrapper's contract at 0x41c20, at every float state: lib/AU/HPgKcuScmp.v's Section hypothesis
   STRCMP at segs = rsegs (libreac/fuzz_identity lib/Reusable/AStrcmpDef.v astrcmp_realizes rsegs B 0x41c20,
   str_meet and strcmp_res unfolded and beta-reduced). *)
Hypothesis STRCMP : forall fx' : YK11.FPState,
  forall ly S W regs mem md x y k c1 c2,
  ecall_pre rsegs B ly S W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
  (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  (0 <= k /\
   (forall i, 0 <= i < k -> exists b, aview rsegs (w_H W) mem (x + i) = Some b /\
                                      aview rsegs (w_H W) mem (y + i) = Some b /\ b <> 0) /\
   aview rsegs (w_H W) mem (x + k) = Some c1 /\ aview rsegs (w_H W) mem (y + k) = Some c2 /\
   (c1 <> c2 \/ c1 = 0)) ->
  src_ok rsegs W regs mem x (k + 1) -> src_ok rsegs W regs mem y (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  (forall a, y <= a <= y + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range x (k + 1) -> amem_range y (k + 1) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
  shadow_hull_vis (aview rsegs (w_H W) mem) x (k + 1) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF y (k + 1) ->
  shadow_hull_vis (aview rsegs (w_H W) mem) y (k + 1) ->
  SRr rsegs W (@cfg_at fx' rsegs B_STRCMP regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = @cfg_at fx' rsegs (raZ regs) regs' mem' md' /\
       AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ---------------- the shared lemmas of HPgKcuLib, as this file uses them ---------------- *)
Lemma kq_base3_kept : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
length sh = 116%nat ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem3 md3 (x_k rsegs cx) ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
same_io md2 md3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 ~ hku_wr cx a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb Hlen HJ3 Hr3 Hio3 Hk.
exact (hku_base3_kept (fx := fx) B MT errno_low cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
  HS Hb Hlen HJ3 Hr3 Hio3 Hk).
Qed.

Lemma kq_cstr_now : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 a s,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
In (a, s) (hi_strs headamp_himg_B) ->
hd_cstr rsegs (w_H W2) mem2 a s.
Proof.
intros cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 a s HS Hb Hin.
exact (hku_cstr_now (fx := fx) B MT errno_low cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 a s HS Hb Hin).
Qed.

Lemma kq_keymem : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 (m : nat) kk,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
(m < length (Model.ents r))%nat ->
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some kk ->
(length kk <= 44)%nat /\ ~ In Cursor.NUL kk /\
garr8 rsegs (mrestrict (w_H W2) mem2) (hku_kaddr rsegs cx m) (hd_zbytes kk ++ [0]) /\
In (e_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2) /\
4096 <= e_pp (x_e rsegs cx) /\ e_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling.
Proof.
intros cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 m kk HS Hb Hm Hk.
destruct (hku_keymem (fx := fx) B MT cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 m kk HS Hb Hm Hk)
  as (H1 & H2 & _ & H4 & _ & H6 & H7 & H8 & _).
exact (conj H1 (conj H2 (conj H4 (conj H6 (conj H7 H8))))).
Qed.

(* ---------------- the segment's start facts ---------------- *)
Lemma kq_start : forall cx r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev ->
hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B).
Proof. intros cx r ev HS. destruct HS as (H & _). exact H. Qed.

Lemma kq_geo : forall cx r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev ->
e_R (x_e rsegs cx) + 0x220 <= x_sp0 rsegs cx /\
x_sp0 rsegs cx - x_STK rsegs cx <= e_R (x_e rsegs cx) - T_SEG_STK /\
4096 <= e_F (x_e rsegs cx) /\ e_F (x_e rsegs cx) + 1024 <= alloc_ceiling /\
alloc_ceiling + T_SEG_STK <= e_R (x_e rsegs cx) /\ e_R (x_e rsegs cx) <= 2 ^ 47 /\
2 ^ 46 <= e_R (x_e rsegs cx).
Proof.
intros cx r ev HS. pose proof (kq_start cx r ev HS) as Hpre.
pose proof Hpre as HC0. unfold hsu_pre in HC0.
apply (hc_core_of_seg_pre rsegs B) in HC0; [|cbn [hi_rsz headamp_himg_B]; lia].
apply hc_core_R in HC0 as (HRc & HR47 & _).
unfold hsu_pre, hd_seg_pre in Hpre.
destruct Hpre as (HJ0 & _ & _ & _ & _ & HS0 & Hal & HRr & Hwin & Hown & HF & _).
change (hi_rsz headamp_himg_B) with 0x220 in HRr.
change (hi_cid headamp_himg_B) with 4 in Hown, HF.
pose proof (hc_frm_low rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 Hown) as (Hf4 & Hfl).
rewrite <- HF in Hf4.
rewrite hc_fb in Hfl. unfold HC_FB in Hfl. rewrite <- HF in Hfl.
assert (Hts : T_SEG_STK = 16384) by reflexivity.
pose proof (@alloc_ceiling_value rc) as [[HCl _] _].
repeat split; lia.
Qed.

Lemma kq_core : forall cx r ev fx2 sh ly2 S2 W2 regs2 mem2 md2,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2 regs2 (e_R (x_e rsegs cx)).
Proof.
intros cx r ev fx2 sh ly2 S2 W2 regs2 mem2 md2 HS Hb.
pose proof (kq_start cx r ev HS) as HC0. unfold hsu_pre in HC0.
apply (hc_core_of_seg_pre rsegs B) in HC0; [|cbn [hi_rsz headamp_himg_B]; lia].
destruct HC0 as (_ & Hnev & H2 & H3 & H4 & Hal & Hwin & HRs).
destruct Hb as ((HJ2 & Hr & _) & _).
split; [exact HJ2|]. split; [exact Hnev|].
split; [rewrite <- H2; exact (Hr 2 ltac:(lia))|].
split; [rewrite <- H3; exact (Hr 3 ltac:(lia))|].
split; [rewrite <- H4; exact (Hr 4 ltac:(lia))|].
split; [exact Hal|]. split; [exact Hwin | exact HRs].
Qed.

(* a value of a cut list *)
Lemma kq_at_reg : forall cx (W : world rsegs) mem regs L rr v,
hsu_at_cx rsegs cx W mem regs L -> In (LReg rr, v) L -> getr regs (Z_to_bv 5 rr) = w64 v.
Proof. intros cx W mem regs L rr v H Hin. exact (proj1 (Forall_forall _ _) H _ Hin). Qed.
Lemma kq_at_cell : forall cx (W : world rsegs) mem regs L o v,
hsu_at_cx rsegs cx W mem regs L -> In (LCell XR o, v) L ->
val_mem rsegs (mrestrict (w_H W) mem) (e_R (x_e rsegs cx) + o) 8 (v mod 2 ^ 64).
Proof. intros cx W mem regs L o v H Hin. exact (proj1 (Forall_forall _ _) H _ Hin). Qed.
Ltac kq_in := unfold hku_L, hqu_L_seg, hqu_L_frame, hqu_L_loopc, hqu_L_t56, hqu_L_body; cbn [app In];
  repeat (first [left; reflexivity | right]).

(* ---------------- what a cut's facts keep across the part ---------------- *)
Lemma kq_keeps_cell : forall (W : world rsegs) mem mem' (regs regs' : bvmap 5 word) e o,
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R e - 2 * ESTACK <= a < e_R e) -> ~ kq_wr1 (e_R e) a ->
 aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
0 <= e_R e -> e_R e + 0x160 <= 2 ^ 64 ->
(0 <= o /\ o + 8 <= 0x90) \/ (0x98 <= o /\ o + 8 <= 0x160) ->
hm_keeps rsegs (w_H W) mem (w_H W) mem' regs regs' e (LCell XR o).
Proof.
intros W mem mem' regs regs' e o Hm HR0 HR1 Ho. cbn [hm_keeps hd_xv]. intros i Hi.
assert (Hes : ESTACK = 4096) by reflexivity.
apply Hm; [lia | lia | unfold kq_wr1; lia].
Qed.

Lemma kq_L3_kept : forall cx j (W : world rsegs) mem mem' (regs regs' : bvmap 5 word),
hsu_at_cx rsegs cx W mem regs
  (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_t56 rsegs cx ++ hqu_L_body rsegs cx j) ->
(forall q, In q [8; 9; 19; 27; 20; 22; 25; 26; 30; 31] -> getr regs' (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
 ~ kq_wr1 (e_R (x_e rsegs cx)) a -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
0 <= e_R (x_e rsegs cx) -> e_R (x_e rsegs cx) + 0x160 <= 2 ^ 64 ->
hsu_at_cx rsegs cx W mem' regs'
  (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_t56 rsegs cx ++ hqu_L_body rsegs cx j).
Proof.
intros cx j W mem mem' regs regs' H Hr Hm HR0 HR1. unfold hsu_at_cx, hsu_at in *.
eapply hm_atl_kept; [exact H|]. intros f Hf.
unfold hqu_L_seg, hqu_L_frame, hqu_L_loopc, hqu_L_t56, hqu_L_body in Hf. cbn [app In] in Hf.
repeat (destruct Hf as [<-|Hf];
  [ first [ cbn [fst hm_keeps]; apply Hr; cbn [In]; repeat (first [left; reflexivity | right])
          | apply kq_keeps_cell; [exact Hm | exact HR0 | exact HR1 | lia] ] |]).
destruct Hf.
Qed.

Lemma kq_x_kept : forall cx (W : world rsegs) mem mem' cs keys rf,
hqu_x_at rsegs cx W mem cs keys rf ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
 ~ kq_wr1 (e_R (x_e rsegs cx)) a -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
0 <= e_F (x_e rsegs cx) -> e_F (x_e rsegs cx) + 1024 + 2 * ESTACK <= e_R (x_e rsegs cx) ->
e_R (x_e rsegs cx) <= 2 ^ 47 ->
hqu_x_at rsegs cx W mem' cs keys rf.
Proof.
intros cx W mem mem' cs keys rf (Hg & Hl & Hrest) Hm HF0 HF1 HR1.
split; [|split; [exact Hl | exact Hrest]].
pose proof (hqu_x_open_len cs keys rf Hl) as Hlen.
assert (Hes : ESTACK = 4096) by reflexivity.
apply (hm_bytes_kept rsegs (w_H W) mem (w_H W) mem' _ _ Hg).
intros x Hx. rewrite Hlen in Hx. unfold HQU_XO in Hx. apply Hm; [lia | lia | unfold kq_wr1; lia].
Qed.

(* ---------------- the state of the part relative to the DOT cut ---------------- *)
Definition kq_cs : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 26; 27].
Definition kq_mid (cx : hsu_scx rsegs) ly2 S2 (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem3 md3 (x_k rsegs cx) /\
same_io md2 md3 /\
(forall q, In q kq_cs -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
 ~ kq_wr1 (e_R (x_e rsegs cx)) a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a).

Lemma kq_kept_cs : forall regs3 regs4 clob, kq_kept regs3 regs4 clob ->
forallb (fun q => negb (existsb (fun c => bv_eqb c (Z_to_bv 5 q)) clob)) kq_cs = true ->
forall q, In q kq_cs -> getr regs4 (Z_to_bv 5 q) = getr regs3 (Z_to_bv 5 q).
Proof.
intros regs3 regs4 clob Hk Hb q Hq. apply Hk.
- unfold kq_cs in Hq. cbn [In] in Hq.
  repeat (destruct Hq as [<-|Hq]; [intros Hz; cbv in Hz; discriminate Hz|]). destruct Hq.
- intros Hin. pose proof (proj1 (forallb_forall _ _) Hb q Hq) as Hq'. cbv beta in Hq'.
  apply negb_true_iff in Hq'.
  assert (Ht : existsb (fun c => bv_eqb c (Z_to_bv 5 q)) clob = true).
  { apply existsb_exists. exists (Z_to_bv 5 q). split; [exact Hin|]. apply bv_eqb_eq. reflexivity. }
  rewrite Ht in Hq'. discriminate Hq'.
Qed.

Lemma kq_mid_refl : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs2 mem2 md2.
Proof.
intros cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 HS Hb. destruct Hb as ((HJ2 & _) & _).
split; [exact HJ2|]. split; [apply same_io_refl|]. split; [reflexivity|]. intros; reflexivity.
Qed.

Lemma kq_mid_step : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4,
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem4 md4 (x_k rsegs cx) ->
same_io md3 md4 ->
(forall q, In q kq_cs -> getr regs4 (Z_to_bv 5 q) = getr regs3 (Z_to_bv 5 q)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
 ~ kq_wr1 (e_R (x_e rsegs cx)) a -> aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem3 a) ->
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 (HJ3 & Hio3 & Hr3 & Hm3) HJ4 Hio4 Hr4 Hm4.
split; [exact HJ4|]. split; [eapply same_io_trans; [exact Hio3 | exact Hio4]|].
split; [intros q Hq; rewrite (Hr4 q Hq); exact (Hr3 q Hq)|].
intros a Ha H1 H2. rewrite (Hm4 a Ha H1 H2). exact (Hm3 a Ha H1 H2).
Qed.

(* a call: the callee-saved registers and every byte outside the callees' stack *)
Lemma kq_mid_call : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4,
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem4 md4 regs4 (e_R (x_e rsegs cx)) ->
aregs_preserved regs3 regs4 -> same_io md3 md4 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem3 a) ->
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 HM HC HP Hio Hm.
apply (kq_mid_step cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 HM); [exact (proj1 HC) | exact Hio | |].
- intros q Hq. apply HP. unfold kq_cs in Hq. unfold acallee_saved. cbn [In] in Hq. lia.
- intros a Ha H1 _. exact (Hm a Ha H1).
Qed.

Lemma kq_mid_post : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 clob (Wr : Z -> Prop),
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem4 md4 (x_k rsegs cx) ->
same_io md3 md4 -> kq_kept regs3 regs4 clob ->
forallb (fun q => negb (existsb (fun c => bv_eqb c (Z_to_bv 5 q)) clob)) kq_cs = true ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem3 a) ->
(forall a, Wr a -> kq_wr1 (e_R (x_e rsegs cx)) a) ->
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 clob Wr HM HJ Hio Hk Hb Hm HW.
apply (kq_mid_step cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 HM HJ Hio).
- exact (kq_kept_cs regs3 regs4 clob Hk Hb).
- intros a Ha _ H2. apply Hm; [exact Ha|]. intros Hw. exact (H2 (HW a Hw)).
Qed.

Lemma kq_core_mid : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2 regs2 (e_R (x_e rsegs cx)) ->
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem3 md3 regs3 (e_R (x_e rsegs cx)).
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (_ & Hnev & H2 & H3 & H4 & Hal & Hwin & HRs) (HJ3 & _ & Hr & _).
split; [exact HJ3|]. split; [exact Hnev|].
split; [rewrite <- H2; exact (Hr 2 ltac:(cbn; tauto))|].
split; [rewrite <- H3; exact (Hr 3 ltac:(cbn; tauto))|].
split; [rewrite <- H4; exact (Hr 4 ltac:(cbn; tauto))|].
split; [exact Hal|]. split; [exact Hwin | exact HRs].
Qed.

Lemma kq_base3_mid : forall cx ev fx2 r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 ->
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx ev fx2 r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb (HJ3 & Hio & Hr & Hm).
apply (kq_base3_kept cx ev fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb hqu_shX_len HJ3);
  [| exact Hio |].
- intros q Hq. apply Hr. unfold kq_cs. cbn [In]. lia.
- intros a Ha H1 H2. assert (Hes : ESTACK = 4096) by reflexivity.
  assert (Hts : T_SEG_STK = 16384) by reflexivity.
  apply Hm; [exact Ha | lia |]. intros Hw. apply H2. left. unfold kq_wr1 in Hw. lia.
Qed.

Lemma kq_val_step : forall (W : world rsegs) m1 m2 R a v,
val_mem rsegs (mrestrict (w_H W) m1) a 8 v ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (R - 2 * ESTACK <= x < R) -> aview rsegs (w_H W) m2 x = aview rsegs (w_H W) m1 x) ->
0 <= R -> R <= a -> a + 8 <= 2 ^ 64 -> val_mem rsegs (mrestrict (w_H W) m2) a 8 v.
Proof.
intros W m1 m2 R a v H Hm HR Ha Ha8. eapply val_mem_kept; [|exact H]. intros i Hi.
assert (Hes : ESTACK = 4096) by reflexivity. apply Hm; [lia | lia].
Qed.
Lemma kq_val_eq : forall (W : world rsegs) m1 m2 a v,
val_mem rsegs (mrestrict (w_H W) m1) a 8 v ->
(forall x, 0 <= x < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) m2 x = aview rsegs (w_H W) m1 x) ->
0 <= a -> a + 8 <= 2 ^ 64 -> val_mem rsegs (mrestrict (w_H W) m2) a 8 v.
Proof.
intros W m1 m2 a v H Hm Ha Ha8. eapply val_mem_kept; [|exact H]. intros i Hi. apply Hm; [lia | tauto].
Qed.

Lemma kq_cell_mid : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 o v,
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + o) 8 v ->
0 <= e_R (x_e rsegs cx) -> e_R (x_e rsegs cx) <= 2 ^ 47 -> 0x98 <= o -> o + 8 <= 0x160 ->
val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + o) 8 v.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 o v (_ & _ & _ & Hm) H HR0 HR1 Ho1 Ho2.
eapply val_mem_kept; [|exact H]. intros i Hi. assert (Hes : ESTACK = 4096) by reflexivity.
apply Hm; [lia | lia | unfold kq_wr1; lia].
Qed.

Ltac kq_incs := unfold kq_cs; cbn [In]; repeat (first [left; reflexivity | right]).
Ltac kq_nz := let H := fresh in intros H; cbv in H; discriminate H.
Ltac kq_nin := let H := fresh in intros H; try (unfold kq_dot_clob in H); cbn [In] in H;
  repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; cbv in H; discriminate H|]); exact H.

(* ======================================== the part from the DOT cut ======================================== *)
Section dot.
Variable cx : hsu_scx rsegs.
Variable r : Model.pod_rec.
Variable POST : world rsegs -> config -> Prop.
Variable ev : Z.
Variables at0 m : nat.
Hypothesis HS : @hqu_start_M03 fx rc SK rsegs B cx r ev.
Hypothesis HVAL : @hqu_from_VAL fx rc SK rsegs B MT cx r POST at0 m.
Hypothesis HRF : @hqu_from_RF fx rc SK rsegs B MT cx r POST at0 m.
Variable fx2 : YK11.FPState.
Variables (ly2 : alayout) (S2 : astate) (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
  (md2 : Model).
Variables (k : list byte) (cs : list cell) (keys rf : Z) (nd : nat) (acc : Z) (big : bool).
Hypothesis HC : @hku_cut_DOT fx rc SK rsegs B MT cx fx2 r at0 m k cs keys rf nd acc big ly2 S2 W2 regs2 mem2 md2.

Lemma kq_HI : @hku_inv fx rc SK rsegs B MT cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2.
Proof. exact (proj1 HC). Qed.

(* the channel's value, the name after the channel's '.', and its address *)
Definition kq_chv : Z := if hku_neg (hku_rest k) then - acc else acc.
Definition kq_nb : list byte := skipn (S (hku_d (hku_rest k) + nd)) (hku_rest k).
Definition kq_name : Z := hku_kaddr rsegs cx m + Z.of_nat (hku_d (hku_rest k)) + Z.of_nat nd + 14.

(* the cut's RF exit: the refusal fold with a5 = bad *)
Lemma kq_rf_leaf : forall regs3 mem3 md3 bad,
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 30) = getr regs2 (Z_to_bv 5 30) -> getr regs3 (Z_to_bv 5 31) = getr regs2 (Z_to_bv 5 31) ->
getr regs3 (Z_to_bv 5 15) = w64 bad ->
expect_cell k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) = inl bad ->
SRr rsegs W2 (@cfg_at fx2 rsegs HQU_RF regs3 mem3 md3) POST.
Proof.
intros regs3 mem3 md3 bad HM H30 H31 H15 Hcell.
pose proof kq_HI as (Hb & Hat & Hfs9 & Hfs18 & Hfs19 & Hlive & Hat0 & Hkey & Hpair & Hx & Hcls).
pose proof (kq_geo cx r ev HS) as (HRs & Hwin & HF4 & HFc & HRc & HR47 & HR46).
pose proof HM as (HJ3 & Hio3 & Hr3 & Hm3).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (HL3 : hsu_at_cx rsegs cx W2 mem2 regs2
  (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_t56 rsegs cx ++ hqu_L_body rsegs cx (Z.of_nat m + 2))).
{ unfold hsu_at_cx, hsu_at in *. unfold hku_L in Hat.
  rewrite app_assoc, app_assoc, app_assoc in Hat.
  apply Forall_app in Hat as [Hat _]. rewrite <- app_assoc, <- app_assoc in Hat. exact Hat. }
apply (HRF fx2 ly2 S2 W2 regs3 mem3 md3 k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) bad cs keys rf).
split; [exact (kq_base3_mid cx ev fx2 r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb HM)|].
split.
{ unfold hsu_at_cx, hsu_at. rewrite app_assoc, app_assoc, app_assoc. apply Forall_app. split.
  - rewrite <- app_assoc, <- app_assoc.
    refine (kq_L3_kept cx _ W2 mem2 mem3 regs2 regs3 HL3 _ Hm3 ltac:(lia) ltac:(lia)).
    intros q Hq. cbn [In] in Hq.
    destruct Hq as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
      first [ exact H30 | exact H31 | apply Hr3; kq_incs ].
  - repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [fst snd hd_at].
    exact H15. }
split; [exact Hfs9|]. split; [exact Hfs18|]. split; [exact Hfs19|].
split; [exact Hlive|]. split; [exact Hat0|].
split; [exact Hcell|].
split; [exact (PairFacts.expect_cell_bad k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) bad Hcell)|].
split; [exact Hpair|].
exact (kq_x_kept cx W2 mem2 mem3 cs (keys + 1) rf Hx Hm3 ltac:(lia) ltac:(lia) HR47).
Qed.

(* the cut's VAL exit *)
Lemma kq_val_leaf : forall regs3 mem3 md3 ch p,
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 30) = getr regs2 (Z_to_bv 5 30) -> getr regs3 (Z_to_bv 5 31) = getr regs2 (Z_to_bv 5 31) ->
getr regs3 (Z_to_bv 5 16) = w64 p -> getr regs3 (Z_to_bv 5 23) = w64 (if p =? HA_SENS then HA_SENS_MAX else 1) ->
getr regs3 (Z_to_bv 5 21) = w64 ch -> getr regs3 (Z_to_bv 5 15) = w64 REFUSE_OUT_OF_RANGE ->
expect_key (hku_rest k) = KCell ch p ->
SRr rsegs W2 (@cfg_at fx2 rsegs HQU_VAL regs3 mem3 md3) POST.
Proof.
intros regs3 mem3 md3 ch p HM H30 H31 H16 H23 H21 H15 Hkey.
pose proof kq_HI as (Hb & Hat & Hfs9 & Hfs18 & Hfs19 & Hlive & Hat0 & Hkey0 & Hpair & Hx & Hcls).
pose proof (kq_geo cx r ev HS) as (HRs & Hwin & HF4 & HFc & HRc & HR47 & HR46).
pose proof HM as (HJ3 & Hio3 & Hr3 & Hm3).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
pose proof (kq_at_reg cx _ _ _ _ 18 _ Hat ltac:(kq_in)) as R18.
pose proof (kq_at_reg cx _ _ _ _ 24 _ Hat ltac:(kq_in)) as R24.
assert (HL3 : hsu_at_cx rsegs cx W2 mem2 regs2
  (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_t56 rsegs cx ++ hqu_L_body rsegs cx (Z.of_nat m + 2))).
{ unfold hsu_at_cx, hsu_at in *. unfold hku_L in Hat.
  rewrite app_assoc, app_assoc, app_assoc in Hat.
  apply Forall_app in Hat as [Hat _]. rewrite <- app_assoc, <- app_assoc in Hat. exact Hat. }
apply (HVAL fx2 ly2 S2 W2 regs3 mem3 md3 k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) ch p cs keys rf).
split; [exact (kq_base3_mid cx ev fx2 r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb HM)|].
split.
{ unfold hsu_at_cx, hsu_at. rewrite app_assoc, app_assoc, app_assoc. apply Forall_app. split.
  - rewrite <- app_assoc, <- app_assoc.
    refine (kq_L3_kept cx _ W2 mem2 mem3 regs2 regs3 HL3 _ Hm3 ltac:(lia) ltac:(lia)).
    intros q Hq. cbn [In] in Hq.
    destruct Hq as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
      first [ exact H30 | exact H31 | apply Hr3; kq_incs ].
  - repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [fst snd hd_at].
    + exact H16.
    + exact H23.
    + exact H21.
    + exact H15.
    + rewrite (Hr3 18 ltac:(kq_incs)). exact R18.
    + rewrite (Hr3 24 ltac:(kq_incs)). exact R24. }
split; [exact Hfs9|]. split; [exact Hfs18|]. split; [exact Hfs19|].
split; [exact Hlive|]. split; [exact Hat0|].
split; [exact Hkey|]. split; [exact Hpair|]. split; [exact Hcls|].
exact (kq_x_kept cx W2 mem2 mem3 cs (keys + 1) rf Hx Hm3 ltac:(lia) ltac:(lia) HR47).
Qed.

(* the tail 0x8347c from a found name with param p: big or the channel out of range go to RF, else VAL *)
Lemma kq_tail_case : forall regs3 mem3 md3 p,
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 30) = getr regs2 (Z_to_bv 5 30) -> getr regs3 (Z_to_bv 5 31) = getr regs2 (Z_to_bv 5 31) ->
getr regs3 (Z_to_bv 5 16) = w64 p -> getr regs3 (Z_to_bv 5 23) = w64 (if p =? HA_SENS then HA_SENS_MAX else 1) ->
getr regs3 (Z_to_bv 5 21) = w64 (kq_chv mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + 0x90) 8 (Z.b2z big) ->
-10000009 <= kq_chv <= 10000009 ->
expect_key (hku_rest k) =
  (if big || (kq_chv <? 0) || (HA_CHANNELS <=? kq_chv) then KRange else KCell kq_chv p) ->
SRr rsegs W2 (@cfg_at fx2 rsegs KQ_TL regs3 mem3 md3) POST.
Proof.
intros regs3 mem3 md3 p HM H30 H31 H16 H23 H21 Vb Hch Hkey.
pose proof kq_HI as (Hb & Hat & _ & _ & _ & _ & _ & _ & Hpair & _).
pose proof (kq_geo cx r ev HS) as (HRs & Hwin & HF4 & HFc & HRc & HR47 & HR46).
pose proof HM as (HJ3 & _ & Hr3 & _).
assert (H9 : getr regs3 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx))).
{ rewrite (Hr3 9 ltac:(kq_incs)). exact (kq_at_reg cx _ _ _ _ 9 _ Hat ltac:(kq_in)). }
eapply SRr_bind.
{ apply (kq_tail_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 (e_R (x_e rsegs cx)) (Z.b2z big)
    (kq_chv mod 2 ^ 64) HJ3 H9 H21); [lia | lia | destruct big; cbn; lia | apply Z.mod_pos_bound; lia | exact Vb]. }
intros W4 c4 _ [(Hc & HP) | (Hb0 & Hc & HP)];
  destruct HP as (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Hm4 & Hr4).
- assert (HM4 : kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4)
    by (apply (kq_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 _ (fun _ => False)
          HM HJ4 Hio4 Hk4 ltac:(vm_compute; reflexivity) Hm4); intros a []).
  apply (kq_rf_leaf regs4 mem4 md4 REFUSE_OUT_OF_RANGE HM4).
  + rewrite (Hk4 (Z_to_bv 5 30) ltac:(kq_nz) ltac:(kq_nin)). exact H30.
  + rewrite (Hk4 (Z_to_bv 5 31) ltac:(kq_nz) ltac:(kq_nin)). exact H31.
  + exact Hr4.
  + rewrite KeyFacts.expect_cell_key. change (skipn 13 k) with (hku_rest k). rewrite Hkey.
    destruct Hc as [Hc|Hc].
    * destruct big; [reflexivity | cbn in Hc; lia].
    * assert (Hn : ~ (0 <= kq_chv <= 47)) by (rewrite <- (kq_chw kq_chv Hch); lia).
      destruct (Z.ltb_spec kq_chv 0); [rewrite orb_true_r; reflexivity|].
      destruct (Z.leb_spec HA_CHANNELS kq_chv) as [Hl|Hl]; [rewrite !orb_true_r; reflexivity|].
      unfold HA_CHANNELS in Hl. lia.
- assert (HM4 : kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4)
    by (apply (kq_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 _ (fun _ => False)
          HM HJ4 Hio4 Hk4 ltac:(vm_compute; reflexivity) Hm4); intros a []).
  assert (Hbig : big = false) by (destruct big; [cbn in Hb0; lia | reflexivity]). rewrite Hbig in Hkey.
  assert (Hr : 0 <= kq_chv <= 47) by (apply (kq_chw kq_chv Hch); exact Hc).
  apply (kq_val_leaf regs4 mem4 md4 kq_chv p HM4).
  + rewrite (Hk4 (Z_to_bv 5 30) ltac:(kq_nz) ltac:(kq_nin)). exact H30.
  + rewrite (Hk4 (Z_to_bv 5 31) ltac:(kq_nz) ltac:(kq_nin)). exact H31.
  + rewrite (Hk4 (Z_to_bv 5 16) ltac:(kq_nz) ltac:(kq_nin)). exact H16.
  + rewrite (Hk4 (Z_to_bv 5 23) ltac:(kq_nz) ltac:(kq_nin)). exact H23.
  + rewrite (Hk4 (Z_to_bv 5 21) ltac:(kq_nz) ltac:(kq_nin)). rewrite H21. unfold w64. apply Z_to_bv_mod64.
  + exact Hr4.
  + rewrite Hkey. destruct (Z.ltb_spec kq_chv 0) as [Hl|Hl]; [lia|].
    destruct (Z.leb_spec HA_CHANNELS kq_chv) as [Hl2|Hl2]; [unfold HA_CHANNELS in Hl2; lia | reflexivity].
Qed.

Lemma kq_nb_nul : ~ In Cursor.NUL kq_nb.
Proof.
pose proof kq_HI as (Hb & _ & _ & _ & _ & _ & _ & Hkey & Hpair & _).
pose proof Hpair as (_ & _ & HSm & _).
destruct (kq_keymem cx ev fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 m k HS Hb ltac:(lia) Hkey) as (_ & Hnul & _).
unfold kq_nb, hku_rest.
apply KeyFacts.no_nul_skipn, KeyFacts.no_nul_skipn. exact Hnul.
Qed.

(* read_channel's answer from the DOT cut *)
Lemma kq_rc_eq : read_channel (hku_rest k) =
  (if (nd =? 0)%nat then (0%nat, 0, big) else ((hku_d (hku_rest k) + nd)%nat, kq_chv, big)).
Proof.
pose proof HC as (_ & _ & _ & _ & Hrc & _).
unfold kq_chv, hku_d, hku_neg in *.
apply (KeyFacts.read_channel_eq (hku_rest k) _ _ acc big nd).
- apply surjective_pairing.
- exact Hrc.
Qed.

(* no digit: the key is bad *)
Lemma kq_key_bad0 : nd = 0%nat ->
expect_cell k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) = inl REFUSE_BAD_KEY.
Proof.
intros Hz.
assert (Hr0 : read_channel (hku_rest k) = (0%nat, 0, big)) by (rewrite kq_rc_eq, Hz; reflexivity).
rewrite KeyFacts.expect_cell_key. change (skipn 13 k) with (hku_rest k).
rewrite (KeyFacts.expect_key_read (hku_rest k) 0%nat 0 big Hr0). cbn [Nat.eqb orb]. reflexivity.
Qed.

(* nd >= 1 digits: expect_key from the byte after them and the name *)
Lemma kq_key_pos : (0 < nd)%nat ->
expect_key (hku_rest k) =
  (if negb (bv_unsigned (nth (hku_d (hku_rest k) + nd) (hku_rest k) Cursor.NUL) =? 46) then KBad
   else match param_of_name (Cursor.cstr (skipn (S (hku_d (hku_rest k) + nd)) (hku_rest k))) with
        | None => KBad
        | Some p => if big || (kq_chv <? 0) || (HA_CHANNELS <=? kq_chv) then KRange else KCell kq_chv p
        end).
Proof.
intros Hpos.
assert (Hr1 : read_channel (hku_rest k) = ((hku_d (hku_rest k) + nd)%nat, kq_chv, big)).
{ rewrite kq_rc_eq. replace ((nd =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
rewrite (KeyFacts.expect_key_read (hku_rest k) _ _ _ Hr1).
replace ((hku_d (hku_rest k) + nd =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
cbn [orb]. reflexivity.
Qed.

Lemma kq_key_eq : (0 < nd)%nat ->
bv_unsigned (nth (hku_d (hku_rest k) + nd) (hku_rest k) Cursor.NUL) = 46 ->
expect_key (hku_rest k) =
  match param_of_name kq_nb with
  | None => KBad
  | Some p => if big || (kq_chv <? 0) || (HA_CHANNELS <=? kq_chv) then KRange else KCell kq_chv p
  end.
Proof.
intros Hpos Hdot. rewrite (kq_key_pos Hpos), Hdot. cbn [Z.eqb Pos.eqb negb].
change (skipn (S (hku_d (hku_rest k) + nd)) (hku_rest k)) with kq_nb.
rewrite (KeyFacts.cstr_id _ kq_nb_nul). reflexivity.
Qed.

Lemma kq_key_bad_dot : (0 < nd)%nat ->
bv_unsigned (nth (hku_d (hku_rest k) + nd) (hku_rest k) Cursor.NUL) <> 46 ->
expect_cell k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) = inl REFUSE_BAD_KEY.
Proof.
intros Hpos Hdot. rewrite KeyFacts.expect_cell_key. change (skipn 13 k) with (hku_rest k).
rewrite (kq_key_pos Hpos).
replace (bv_unsigned (nth (hku_d (hku_rest k) + nd) (hku_rest k) Cursor.NUL) =? 46) with false
  by (symmetry; apply Z.eqb_neq; exact Hdot).
cbn [negb]. reflexivity.
Qed.

Lemma kq_key_bad_name : (0 < nd)%nat ->
bv_unsigned (nth (hku_d (hku_rest k) + nd) (hku_rest k) Cursor.NUL) = 46 ->
param_of_name kq_nb = None ->
expect_cell k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) = inl REFUSE_BAD_KEY.
Proof.
intros Hpos Hdot Hp. rewrite KeyFacts.expect_cell_key. change (skipn 13 k) with (hku_rest k).
rewrite (kq_key_eq Hpos Hdot), Hp. reflexivity.
Qed.

(* the strcmp at the name in the continuation form *)
Lemma kq_call : forall regs3 mem3 md3 ret alit lit,
kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 1) = w64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
getr regs3 (Z_to_bv 5 10) = w64 kq_name -> getr regs3 (Z_to_bv 5 11) = w64 alit ->
In (alit, hd_zbytes lit) (hi_strs headamp_himg_B) ->
bv_unsigned (nth (hku_d (hku_rest k) + nd) (hku_rest k) Cursor.NUL) = 46 ->
(forall regs4 mem4 md4, kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 -> aregs_preserved regs3 regs4 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
   aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem3 a) ->
  (exists v, getr regs4 (Z_to_bv 5 10) = w64 v /\ 0 <= v < 2 ^ 64 /\ (v = 0 <-> kq_nb = lit)) ->
  SRr rsegs W2 (@cfg_at fx2 rsegs ret regs4 mem4 md4) POST) ->
SRr rsegs W2 (@cfg_at fx2 rsegs B_STRCMP regs3 mem3 md3) POST.
Proof.
intros regs3 mem3 md3 ret alit lit HM H1 Hret Hret2 H10 H11 Hin Hdot K.
pose proof kq_HI as (Hb & _ & _ & _ & _ & _ & _ & Hkey & Hpair & _).
pose proof Hpair as (_ & _ & HSm & _).
pose proof (hku_start_wf (fx := fx) rsegs B cx r ev HS) as Hwf.
pose proof (Model.ents_wf r Hwf) as (Hn32 & _).
pose proof (kq_core cx r ev fx2 hqu_shX ly2 S2 W2 regs2 mem2 md2 HS Hb) as HC2.
pose proof (kq_core_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HC2 HM) as HC3.
pose proof (kq_base3_mid cx ev fx2 r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb HM) as Hb3.
destruct (kq_keymem cx ev fx2 r hqu_shX ly2 S2 W2 regs3 mem3 md3 m k HS Hb3 ltac:(lia) Hkey)
  as (Hk44 & Hnul & Hg & Hpp & Hpp1 & Hpp2).
pose proof (kq_cstr_now cx ev fx2 r hqu_shX ly2 S2 W2 regs3 mem3 md3 alit (hd_zbytes lit) HS Hb3 Hin) as Hlit.
assert (Hkd : hku_kaddr rsegs cx m = e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m)
  by (unfold hku_kaddr, Layout.OFF_ENT, Layout.ENT_SIZE; lia).
assert (HPP : Layout.PP_SIZE = 19744) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = 19744) by reflexivity.
assert (Hm31 : (m <= 31)%nat) by lia.
rewrite HPP in Hpp2.
assert (Hlr : length (hku_rest k) = (length k - 13)%nat)
  by (unfold hku_rest; rewrite length_skipn, kq_prefix_len; reflexivity).
assert (Hu : (hku_d (hku_rest k) + nd < length (hku_rest k))%nat).
{ destruct (Nat.lt_ge_cases (hku_d (hku_rest k) + nd) (length (hku_rest k))) as [Hl|Hl]; [exact Hl|].
  rewrite nth_overflow in Hdot by exact Hl. cbv in Hdot. discriminate Hdot. }
assert (Hnb : kq_nb = skipn (S (hku_d (hku_rest k) + nd) + 13) k)
  by (unfold kq_nb, hku_rest; rewrite skipn_skipn, kq_prefix_len; reflexivity).
assert (Hlnb : length kq_nb = (length k - (S (hku_d (hku_rest k) + nd) + 13))%nat)
  by (rewrite Hnb; apply length_skipn).
pose proof (kq_garr8_suffix _ _ k (S (hku_d (hku_rest k) + nd) + 13) Hg ltac:(lia)) as Hgn.
rewrite <- Hnb in Hgn.
replace (hku_kaddr rsegs cx m + Z.of_nat (S (hku_d (hku_rest k) + nd) + 13)) with kq_name in Hgn
  by (unfold kq_name; lia).
apply (hksu_strcmp_call (fx := fx2) rsegs B img_segs_low STRCMP POST ret alit lit (x_STK rsegs cx) (x_sp0 rsegs cx)
  (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
  (x_k rsegs cx) ly2 S2 W2 mem3 md3 regs3 (e_R (x_e rsegs cx)) kq_name (e_pp (x_e rsegs cx)) Layout.PP_SIZE kq_nb
  HC3 H1 Hret Hret2 H10 H11 Hpp).
- unfold kq_name. rewrite Hkd. lia.
- rewrite Hrq, Hlnb. unfold kq_name. rewrite Hkd. lia.
- exact Hgn.
- exact kq_nb_nul.
- exact Hlit.
- intros regs4 mem4 md4 HC4 HP4 Hio4 Hm4 (c1 & c2 & Hv & Hres). apply K.
  + exact (kq_mid_call cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 HM HC4 HP4 Hio4 Hm4).
  + exact HP4.
  + exact Hm4.
  + exists (bv_unsigned (w64 (hksu_res c1 c2))). split; [|split].
    * etransitivity; [exact Hv|]. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    * pose proof (bv_unsigned_in_range _ (w64 (hksu_res c1 c2))) as Hrg.
      change (bv_modulus 64) with (2 ^ 64) in Hrg. lia.
    * rewrite kq_res_word. exact Hres.
Qed.

Ltac kq_lit := cbv [hi_strs headamp_himg_B headamp_B_strs]; repeat (first [left; reflexivity | right]).
Ltac kq_keep1 Hk q := rewrite (Hk (Z_to_bv 5 q) ltac:(kq_nz) ltac:(kq_nin)).

(* the whole part from DOT *)
Lemma kq_main : SRr rsegs W2 (@cfg_at fx2 rsegs HKU_DOT regs2 mem2 md2) POST.
Proof.
pose proof HC as (HI & Hat & Hnd & Hstop & Hrc & Hacc).
pose proof HI as (Hb & HatL & _ & _ & _ & _ & _ & Hkey & Hpair & _).
pose proof Hb as ((HJ2 & _) & _).
pose proof (kq_geo cx r ev HS) as (HRs & Hwin & HF4 & HFc & HRc & HR47 & HR46).
pose proof Hpair as (_ & Hpre & HSm & _).
pose proof (hku_start_wf (fx := fx) rsegs B cx r ev HS) as Hwf.
pose proof (Model.ents_wf r Hwf) as (Hn32 & _).
pose proof (hku_inv_key_len (fx := fx) rsegs B MT cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 Hwf HI)
  as Hk45.
pose proof (hku_rest_len k) as Hrl.
destruct (kq_keymem cx ev fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 m k HS Hb ltac:(lia) Hkey)
  as (_ & _ & _ & _ & Hpp1 & Hpp2).
pose proof (kq_mid_refl cx ev fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 HS Hb) as HM2.
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (Hkd : hku_kaddr rsegs cx m = e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m)
  by (unfold hku_kaddr, Layout.OFF_ENT, Layout.ENT_SIZE; lia).
assert (HPP : Layout.PP_SIZE = 19744) by reflexivity. rewrite HPP in Hpp2.
assert (Hm31 : (m <= 31)%nat) by lia.
pose proof (@alloc_ceiling_value rc) as [[HCl HCh] _].
assert (HK0 : 0x4000 <= hku_kaddr rsegs cx m) by (rewrite Hkd; lia).
assert (HK1 : hku_kaddr rsegs cx m + 160 <= 2 ^ 47) by (rewrite Hkd; lia).
assert (Hd45 : 0 <= Z.of_nat (hku_d (hku_rest k)) <= 45) by lia.
assert (Hnd45 : 0 <= Z.of_nat nd <= 45) by lia.
(* the cut's registers and cells *)
pose proof (kq_at_reg cx _ _ _ _ 23 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R23.
pose proof (kq_at_reg cx _ _ _ _ 10 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R10.
pose proof (kq_at_reg cx _ _ _ _ 12 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R12.
pose proof (kq_at_reg cx _ _ _ _ 11 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R11.
pose proof (kq_at_reg cx _ _ _ _ 13 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R13.
pose proof (kq_at_reg cx _ _ _ _ 14 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R14.
pose proof (kq_at_reg cx _ _ _ _ 1 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R1.
pose proof (kq_at_reg cx _ _ _ _ 21 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R21.
pose proof (kq_at_reg cx _ _ _ _ 17 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R17.
pose proof (kq_at_reg cx _ _ _ _ 5 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R5.
pose proof (kq_at_reg cx _ _ _ _ 9 _ HatL ltac:(kq_in)) as R9.
pose proof (kq_at_reg cx _ _ _ _ 30 _ HatL ltac:(kq_in)) as R30.
pose proof (kq_at_reg cx _ _ _ _ 31 _ HatL ltac:(kq_in)) as R31.
pose proof (kq_at_cell cx _ _ _ _ 0x108 _ HatL ltac:(kq_in)) as C108.
pose proof (kq_at_cell cx _ _ _ _ 0x110 _ HatL ltac:(kq_in)) as C110.
pose proof (Cursor.byte_range (nth (hku_d (hku_rest k) + nd) (hku_rest k) Cursor.NUL)) as Hc256.
assert (Hchv : -10000009 <= kq_chv <= 10000009) by (unfold kq_chv; destruct (hku_neg (hku_rest k)); lia).
(* DOT 0x833c8 .. 0x83400 *)
eapply SRr_bind.
{ apply (kq_dot_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (hku_kaddr rsegs cx m)
    (Z.of_nat (hku_d (hku_rest k))) (Z.of_nat nd) acc
    (bv_unsigned (nth (hku_d (hku_rest k) + nd) (hku_rest k) Cursor.NUL))
    (if hku_neg (hku_rest k) then 0 else 1) HJ2).
  all: first [ exact R23 | exact R10 | exact R11 | exact R13 | exact R14 | exact R17 | exact R21 | exact R5
             | (destruct (hku_neg (hku_rest k)); [left | right]; reflexivity)
             | lia ]. }
intros W3 c3 _ [(Hz & HP) | [(Hz & Hc & HP) | (Hz & Hc & HP)]];
  destruct HP as (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hr3);
  (assert (HM3 : kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3)
     by (apply (kq_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs2 mem2 md2 regs3 mem3 md3 _ (fun _ => False)
           HM2 HJ3 Hio3 Hk3 ltac:(vm_compute; reflexivity) Hm3); intros a [])).
{ (* no digit: RF with BAD_KEY *)
  apply (kq_rf_leaf regs3 mem3 md3 REFUSE_BAD_KEY HM3).
  - kq_keep1 Hk3 30. reflexivity.
  - kq_keep1 Hk3 31. reflexivity.
  - exact Hr3.
  - apply kq_key_bad0. lia. }
{ (* no '.' after the digits: RF with BAD_KEY *)
  apply (kq_rf_leaf regs3 mem3 md3 REFUSE_BAD_KEY HM3).
  - kq_keep1 Hk3 30. reflexivity.
  - kq_keep1 Hk3 31. reflexivity.
  - exact Hr3.
  - apply kq_key_bad_dot; [lia | exact Hc]. }
(* the '.': the save of big, the name, the first strcmp's arguments *)
assert (Hpos : (0 < nd)%nat) by lia.
assert (R21' : getr regs3 (Z_to_bv 5 21) = w64 (kq_chv mod 2 ^ 64)).
{ rewrite Hr3. unfold kq_chv, w64. rewrite Z_to_bv_mod64. destruct (hku_neg (hku_rest k)); reflexivity. }
eapply SRr_bind.
{ apply (kq_st_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 (e_R (x_e rsegs cx))
    (hku_kaddr rsegs cx m + Z.of_nat (hku_d (hku_rest k)) + Z.of_nat nd) (Z.b2z big) HJ3).
  - kq_keep1 Hk3 9. exact R9.
  - kq_keep1 Hk3 17. exact R17.
  - kq_keep1 Hk3 1. exact R1.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - destruct big; cbn; lia. }
intros W4 c4 _ HP.
destruct HP as (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Hm4 & (H1_4 & H10_4 & H23_4 & H11_4 & Vb4)).
assert (HM4 : kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4)
  by (apply (kq_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 _ _ HM3 HJ4 Hio4 Hk4
        ltac:(vm_compute; reflexivity) Hm4); intros a Ha; exact Ha).
assert (Hname : getr regs4 (Z_to_bv 5 23) = w64 kq_name)
  by (rewrite H23_4; unfold w64, kq_name; f_equal; lia).
assert (Hname0 : getr regs4 (Z_to_bv 5 10) = w64 kq_name)
  by (rewrite H10_4; unfold w64, kq_name; f_equal; lia).
(* strcmp(name, "phantom") *)
apply (kq_call regs4 mem4 md4 RB_STRCMP1 B_HPH NAME_PHANTOM HM4 H1_4 ltac:(unfold RB_STRCMP1; lia) eq_refl
  Hname0 H11_4 ltac:(kq_lit) Hc).
intros regs5 mem5 md5 HM5 HP5 Hm5 (v5 & H10_5 & Hv5 & Hiff5).
pose proof (kq_val_step W2 mem4 mem5 _ _ _ Vb4 Hm5 ltac:(lia) ltac:(lia) ltac:(lia)) as Vb5.
assert (H23_5 : getr regs5 (Z_to_bv 5 23) = w64 kq_name)
  by (rewrite (HP5 23 ltac:(unfold acallee_saved; lia)); exact Hname).
assert (H21_5 : getr regs5 (Z_to_bv 5 21) = w64 (kq_chv mod 2 ^ 64))
  by (rewrite (HP5 21 ltac:(unfold acallee_saved; lia));
      rewrite (Hk4 (Z_to_bv 5 21) ltac:(kq_nz) ltac:(kq_nin)); exact R21').
pose proof HM5 as (HJ5 & _ & Hr5 & _).
eapply SRr_bind.
{ apply (kq_test_ph (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs5 (e_R (x_e rsegs cx)) v5
    (shadow_addr (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT) mod 2 ^ 64)
    ((e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT) mod 2 ^ 64) HJ5
    ltac:(rewrite (Hr5 9 ltac:(kq_incs)); exact R9) H10_5);
  [lia | lia | exact Hv5 | apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia
  | exact (kq_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 0x108 _ HM5 C108
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  | exact (kq_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 0x110 _ HM5 C110
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))]. }
intros W6 c6 _ [(Hv0 & HP) | (Hv0 & HP)];
  destruct HP as (-> & regs6 & mem6 & md6 & -> & HJ6 & Hio6 & Hk6 & Hm6 & Hr6);
  (assert (HM6 : kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs6 mem6 md6)
     by (apply (kq_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 regs6 mem6 md6 _ (fun _ => False)
           HM5 HJ6 Hio6 Hk6 ltac:(vm_compute; reflexivity) Hm6); intros a []));
  pose proof (kq_val_eq W2 mem5 mem6 _ _ Vb5 Hm6 ltac:(lia) ltac:(lia)) as Vb6.
{ (* the name is "phantom" *)
  destruct Hr6 as (H16_6 & H23_6 & H30_6 & H31_6).
  assert (Hnb : kq_nb = NAME_PHANTOM) by (apply Hiff5; exact Hv0).
  apply (kq_tail_case regs6 mem6 md6 HA_PHANTOM HM6).
  - rewrite H30_6, R30. unfold w64. apply Z_to_bv_mod64.
  - rewrite H31_6, R31. unfold w64. apply Z_to_bv_mod64.
  - exact H16_6.
  - exact H23_6.
  - rewrite (Hk6 (Z_to_bv 5 21) ltac:(kq_nz) ltac:(kq_nin)). exact H21_5.
  - exact Vb6.
  - exact Hchv.
  - rewrite (kq_key_eq Hpos Hc), (KeyFacts.param_phantom kq_nb Hnb). reflexivity. }
(* not "phantom": strcmp(name, "pad") *)
destruct Hr6 as (H1_6 & H10_6 & H11_6).
assert (Hnph : kq_nb <> NAME_PHANTOM) by (intros E; apply Hv0; apply Hiff5; exact E).
assert (H21_6 : getr regs6 (Z_to_bv 5 21) = w64 (kq_chv mod 2 ^ 64))
  by (rewrite (Hk6 (Z_to_bv 5 21) ltac:(kq_nz) ltac:(kq_nin)); exact H21_5).
apply (kq_call regs6 mem6 md6 RB_STRCMP2 B_HPAD NAME_PAD HM6 H1_6 ltac:(unfold RB_STRCMP2; lia) eq_refl
  ltac:(rewrite H10_6; exact H23_5) H11_6 ltac:(kq_lit) Hc).
intros regs7 mem7 md7 HM7 HP7 Hm7 (v7 & H10_7 & Hv7 & Hiff7).
pose proof (kq_val_step W2 mem6 mem7 _ _ _ Vb6 Hm7 ltac:(lia) ltac:(lia) ltac:(lia)) as Vb7.
assert (H23_7 : getr regs7 (Z_to_bv 5 23) = w64 kq_name)
  by (rewrite (HP7 23 ltac:(unfold acallee_saved; lia)); kq_keep1 Hk6 23; exact H23_5).
assert (H21_7 : getr regs7 (Z_to_bv 5 21) = w64 (kq_chv mod 2 ^ 64))
  by (rewrite (HP7 21 ltac:(unfold acallee_saved; lia)); exact H21_6).
pose proof HM7 as (HJ7 & _ & Hr7 & _).
eapply SRr_bind.
{ apply (kq_test_pad (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs7 (e_R (x_e rsegs cx)) v7
    (shadow_addr (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT) mod 2 ^ 64)
    ((e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT) mod 2 ^ 64) HJ7
    ltac:(rewrite (Hr7 9 ltac:(kq_incs)); exact R9) H10_7);
  [lia | lia | exact Hv7 | apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia
  | exact (kq_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs7 mem7 md7 0x108 _ HM7 C108
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  | exact (kq_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs7 mem7 md7 0x110 _ HM7 C110
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))]. }
intros W8 c8 _ [(Hv1 & HP) | (Hv1 & HP)];
  destruct HP as (-> & regs8 & mem8 & md8 & -> & HJ8 & Hio8 & Hk8 & Hm8 & Hr8);
  (assert (HM8 : kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs8 mem8 md8)
     by (apply (kq_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs7 mem7 md7 regs8 mem8 md8 _ (fun _ => False)
           HM7 HJ8 Hio8 Hk8 ltac:(vm_compute; reflexivity) Hm8); intros a []));
  pose proof (kq_val_eq W2 mem7 mem8 _ _ Vb7 Hm8 ltac:(lia) ltac:(lia)) as Vb8.
{ (* the name is "pad" *)
  destruct Hr8 as (H16_8 & H23_8 & H30_8 & H31_8).
  assert (Hnb : kq_nb = NAME_PAD) by (apply Hiff7; exact Hv1).
  apply (kq_tail_case regs8 mem8 md8 HA_PAD HM8).
  - rewrite H30_8, R30. unfold w64. apply Z_to_bv_mod64.
  - rewrite H31_8, R31. unfold w64. apply Z_to_bv_mod64.
  - exact H16_8.
  - exact H23_8.
  - rewrite (Hk8 (Z_to_bv 5 21) ltac:(kq_nz) ltac:(kq_nin)). exact H21_7.
  - exact Vb8.
  - exact Hchv.
  - rewrite (kq_key_eq Hpos Hc), (KeyFacts.param_pad kq_nb Hnph Hnb). reflexivity. }
(* not "pad": strcmp(name, "sens") *)
destruct Hr8 as (H1_8 & H10_8 & H11_8).
assert (Hnpad : kq_nb <> NAME_PAD) by (intros E; apply Hv1; apply Hiff7; exact E).
assert (H21_8 : getr regs8 (Z_to_bv 5 21) = w64 (kq_chv mod 2 ^ 64))
  by (rewrite (Hk8 (Z_to_bv 5 21) ltac:(kq_nz) ltac:(kq_nin)); exact H21_7).
apply (kq_call regs8 mem8 md8 RB_STRCMP3 B_HSENS NAME_SENS HM8 H1_8 ltac:(unfold RB_STRCMP3; lia) eq_refl
  ltac:(rewrite H10_8; exact H23_7) H11_8 ltac:(kq_lit) Hc).
intros regs9 mem9 md9 HM9 HP9 Hm9 (v9 & H10_9 & Hv9 & Hiff9).
pose proof (kq_val_step W2 mem8 mem9 _ _ _ Vb8 Hm9 ltac:(lia) ltac:(lia) ltac:(lia)) as Vb9.
assert (H21_9 : getr regs9 (Z_to_bv 5 21) = w64 (kq_chv mod 2 ^ 64))
  by (rewrite (HP9 21 ltac:(unfold acallee_saved; lia)); exact H21_8).
pose proof HM9 as (HJ9 & _ & Hr9 & _).
eapply SRr_bind.
{ apply (kq_test_sens (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs9 (e_R (x_e rsegs cx)) v9
    (shadow_addr (e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT) mod 2 ^ 64)
    ((e_pp (x_e rsegs cx) + Layout.OFF_PARAMS_STRUCT) mod 2 ^ 64) HJ9
    ltac:(rewrite (Hr9 9 ltac:(kq_incs)); exact R9) H10_9);
  [lia | lia | exact Hv9 | apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia
  | exact (kq_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs9 mem9 md9 0x108 _ HM9 C108
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  | exact (kq_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs9 mem9 md9 0x110 _ HM9 C110
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))]. }
intros W10 c10 _ [(Hv2 & HP) | (Hv2 & HP)];
  destruct HP as (-> & regs10 & mem10 & md10 & -> & HJ10 & Hio10 & Hk10 & Hm10 & Hr10).
- (* no name: RF with BAD_KEY *)
  assert (HM10 : kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs10 mem10 md10)
    by (apply (kq_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs9 mem9 md9 regs10 mem10 md10 _ (fun _ => False)
          HM9 HJ10 Hio10 Hk10 ltac:(vm_compute; reflexivity) Hm10); intros a []).
  destruct Hr10 as (H15_10 & H30_10 & H31_10).
  assert (Hnsens : kq_nb <> NAME_SENS) by (intros E; apply Hv2; apply Hiff9; exact E).
  apply (kq_rf_leaf regs10 mem10 md10 REFUSE_BAD_KEY HM10).
  + rewrite H30_10, R30. unfold w64. apply Z_to_bv_mod64.
  + rewrite H31_10, R31. unfold w64. apply Z_to_bv_mod64.
  + exact H15_10.
  + apply (kq_key_bad_name Hpos Hc). exact (KeyFacts.param_none kq_nb Hnph Hnpad Hnsens).
- (* the name is "sens" *)
  assert (HM10 : kq_mid cx ly2 S2 W2 regs2 mem2 md2 regs10 mem10 md10)
    by (apply (kq_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs9 mem9 md9 regs10 mem10 md10 _ (fun _ => False)
          HM9 HJ10 Hio10 Hk10 ltac:(vm_compute; reflexivity) Hm10); intros a []).
  destruct Hr10 as (H16_10 & H23_10 & H30_10 & H31_10).
  assert (Hnb : kq_nb = NAME_SENS) by (apply Hiff9; exact Hv2).
  apply (kq_tail_case regs10 mem10 md10 HA_SENS HM10).
  + rewrite H30_10, R30. unfold w64. apply Z_to_bv_mod64.
  + rewrite H31_10, R31. unfold w64. apply Z_to_bv_mod64.
  + exact H16_10.
  + exact H23_10.
  + rewrite (Hk10 (Z_to_bv 5 21) ltac:(kq_nz) ltac:(kq_nin)). exact H21_9.
  + exact (kq_val_eq W2 mem9 mem10 _ _ Vb9 Hm10 ltac:(lia) ltac:(lia)).
  + exact Hchv.
  + rewrite (kq_key_eq Hpos Hc), (KeyFacts.param_sens kq_nb Hnph Hnpad Hnb). reflexivity.
Qed.

End dot.

(* part 4 of M3c: DOT 0x833c8 -> VAL 0x83490 / RF 0x836a0 *)
Theorem hku_P4 : hku_P4_stmt rsegs B MT.
Proof.
unfold hku_P4_stmt. intros cx POST r ev at0 m HS HVAL HRF.
unfold hku_from_DOT. intros fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf nd acc big HC.
eapply kq_main; eassumption.
Qed.

End main.

Print Assumptions hku_P4.

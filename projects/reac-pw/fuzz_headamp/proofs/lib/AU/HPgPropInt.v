(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on its
   unstripped twin sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the shape-7 body of one
   property of LLVMFuzzerTestOneInput (0x80c40), SEL7 0x814d4 -> LATCH 0x82ae4 (pod.h:400-406: an Int pod with no key
   is built in the frame object e and written into the first block), as the block lemma hbp_int7 and the piece lemma
   hbp_piece_int7 : HPgSeg.hsu_piece_W4_int7_stmt at headamp_himg_B / headamp_bld_B. Proves no function (kind:
   segment lemma).
     0x814d4 .. 0x81504  thirteen `sb zero,(30..42)(s3)`: e in scope        (HPgSteps.hdu_scope_e_in)
     0x81508 li a2,96; ld a0,0xa0(s1) (&e + 8); li a1,0; mv s2,t0; mv s5,t3; mv s7,t2
     0x81520 jal 0x52228  __asan_memset(&e + 8, 0, 96)                     (Section hypothesis AMEMSET)
     0x81524 ld a1,0xb8(s1) (&e); li a0,4; sw a0,0(a1); sw a0,4(a1)         (e's type and size)
     0x81534 ld a0,0x148(s1) (pp); 0x81538 jal 0x84634  pod_write_ent(pp, &e) (Section hypothesis PWE)
     0x8153c mv a7,s7; mv t3,s5; li s10,1; mv t0,s2; li a0,-8
     0x81550 .. 0x81584  thirteen `sb a0,(30..42)(s3)` and li s7,-8: e out (HPgSteps.hdu_scope_e_out)
     0x81588 mv a3,s4; 0x8158c j 0x82ae4
   REGISTERS AND CELLS (for a port by a register / slot map): reads s1 = R, s3 = the shadow base of the frame for
   locals, s4 = seen, t0 = the property index, t2 = the cursor, t3 = what is left, sp / gp / tp for the two calls, and
   the cells R+0xa0 (&e + 8), R+0xb8 (&e), R+0x148 (pp); writes ra, a0, a1, a2, a3, s2, s5, s7, s10, t0, t3, a7 (and
   every register the two callees may change: t1, t2, a4 .. a6, t4 .. t6), the 104 bytes of e (F+0xf0), e's thirteen
   shadow granules 30 .. 42, the sixteen bytes of pp at the old length and the length cell pp + OFF_LEN; the two calls
   use the stack [R - T_pwe_STK, R). At LATCH: t0 = the index, a3 = seen, a7 = the cursor, t3 = what is left,
   s7 = -8, s10 = 1. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgMem HPgSeg HPgPropKit PweSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ---- the pcs of the block ---- *)
Definition HBP_I_MS : Z := 0x52228.    (* __asan_memset *)
Definition HBP_I_PWE : Z := 0x84634.   (* pod_write_ent *)
Definition HBP_I_A : Z := 0x81508.     (* after the scope stores *)
Definition HBP_I_B : Z := 0x81524.     (* the memset call's return *)
Definition HBP_I_C : Z := 0x8153c.     (* pod_write_ent's return *)
Definition HBP_I_O : Z := 0x81550.     (* the scope closers *)
Definition HBP_I_D : Z := 0x81588.     (* after them *)
(* the pod the block writes: Model.prop_step 7's (0, PInt 0), whose bytes are enc_val (PInt 0) *)
Definition hbp_i_ent : ent := Ent POD_INT 4 (le32 0).
(* every register the block may change *)
Definition hbp_i_clob : list (bv 5) :=
[1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 21; 23; 26; 28; 29; 30; 31]%bv.
(* the bytes it may change: e's shadow granules 30 .. 42, e's 104 bytes, the callees' stack below R, and what
   pod_write_ent writes (PweSpec.pwe_E: 16 bytes at pp + len and the len cell) *)
Definition hbp_i_Wr (R F pp len : Z) : Z -> Prop := fun a =>
(shadow_addr F + 30 <= a < shadow_addr F + 43) \/ (F + 240 <= a < F + 344) \/
(R - T_pwe_STK <= a < R) \/ pwe_E pp len hbp_i_ent a.

(* ---- the engine's states: env slot 32 = K, slots 33.. the block's quantities ---- *)
Definition hbp_i_facts : facts := mkFacts [ (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
(* 0x81508: slot 33 = &e + 8 (the cell R+0xa0) *)
Definition hbp_i_rA : YP09.region :=
YP09.mkRegion (Some 9%nat) 0xa0 0xa8 0 0 [ YP09.mkChunk 0xa0 (CVal 8 (SOff 33 0)) ].
Definition hbp_i_ssA : sstate := mkSS HBP_I_A sr_atoms [hbp_i_rA] None hbp_i_facts.
(* 0x81524: slot 33 = &e (the cell R+0xb8), slot 34 = pp (the cell R+0x148); e's first 8 bytes writable *)
Definition hbp_i_rB1 : YP09.region :=
YP09.mkRegion (Some 9%nat) 0xb8 0xc0 0 0 [ YP09.mkChunk 0xb8 (CVal 8 (SOff 33 0)) ].
Definition hbp_i_rB2 : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x148 0x150 0 0 [ YP09.mkChunk 0x148 (CVal 8 (SOff 34 0)) ].
Definition hbp_i_rBe : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 8 [].
(* &e is 8-aligned in the application range; with the shadow entry over e's first 8 bytes this lets the engine
   take the two stores into e as stores outside the shadow band *)
Definition hbp_i_factsB : facts :=
mkFacts [ (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 4096 0x7fffff800000 3) ] [] [].
Definition hbp_i_ssB : sstate := mkSS HBP_I_B sr_atoms [hbp_i_rB1; hbp_i_rB2; hbp_i_rBe] None hbp_i_factsB.
(* 0x8153c and 0x81588: no memory *)
Definition hbp_i_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None hbp_i_facts.

(* ---- registers ---- *)
Lemma hbp_i_bv5_cases : forall r : bv 5, bv_unsigned r <> 0 ->
bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 5 \/
bv_unsigned r = 6 \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/ bv_unsigned r = 10 \/
bv_unsigned r = 11 \/ bv_unsigned r = 12 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15 \/
bv_unsigned r = 16 \/ bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/
bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/
bv_unsigned r = 26 \/ bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/ bv_unsigned r = 30 \/
bv_unsigned r = 31.
Proof. intros r Hr. pose proof (u5_range r) as Hb. lia. Qed.
(* a register outside hbp_i_clob is callee-saved for both calls *)
Lemma hbp_i_cs : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hbp_i_clob -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr Hn. unfold acallee_saved.
pose proof (hbp_i_bv5_cases r Hr) as H.
repeat (destruct H as [H|H];
  [ first [ lia
          | exfalso; apply Hn; rewrite <- (Z_to_bv_bv_unsigned 5 r), H; cbv [hbp_i_clob In];
            repeat (first [left; apply bv_eq; reflexivity | right]) ] |]).
first [ lia
      | exfalso; apply Hn; rewrite <- (Z_to_bv_bv_unsigned 5 r), H; cbv [hbp_i_clob In];
        repeat (first [left; apply bv_eq; reflexivity | right]) ].
Qed.
Lemma hbp_i_pres : forall (r0 r1 : bvmap 5 word) (r : bv 5), aregs_preserved r0 r1 ->
bv_unsigned r <> 0 -> ~ In r hbp_i_clob -> getr r1 r = getr r0 r.
Proof.
intros r0 r1 r HP Hr Hn. pose proof (HP (bv_unsigned r) (hbp_i_cs r Hr Hn)) as H.
rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
Ltac hbp_i_nin := unfold hbp_i_clob; hbp_notin.
(* a list inside hbp_i_clob *)
Ltac hbp_i_sub Hn := let Hin := fresh "Hin" in intro Hin; apply Hn; unfold hbp_i_clob; cbn [In] in Hin |- *; tauto.
(* the symbolic value of register r at the end of a run *)
Ltac hbp_i_reg HS r H :=
lazymatch type of HS with st_ok ?sg ?E ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (H : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg sg Hh E ss ms r HS)
end.

(* ---- arithmetic ---- *)
Lemma hbp_i_mod16_sub : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. rewrite (Z.div_mod a 16) by lia. rewrite (Z.div_mod b 16) by lia. rewrite Ha, Hb, !Z.add_0_r.
replace (16 * (a / 16) - 16 * (b / 16)) with ((a / 16 - b / 16) * 16) by ring. apply Z.mod_mul. lia.
Qed.
Lemma hbp_i_mod8_240 : forall a, a mod 8 = 0 -> (a + 240) mod 8 = 0.
Proof. intros a Ha. rewrite Z.add_mod, Ha by lia. reflexivity. Qed.
Lemma hbp_i_shA_len : Z.of_nat (length headamp_B_shA) = 116.
Proof. reflexivity. Qed.
(* e back out of scope is the prologue's pattern again *)
Lemma hbp_i_P0_out : hm_setn headamp_B_shA 30 13 248 = headamp_B_shA.
Proof. vm_compute. reflexivity. Qed.

(* ---- where the block's objects lie (the frame for locals F, its shadow, the first block pp, R) ---- *)
Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition hbp_i_lay (R F pp : Z) : Prop :=
4096 <= F /\ F + 1024 <= alloc_ceiling /\ F mod 8 = 0 /\
0x7fff8000 <= shadow_addr F /\ shadow_addr F + 128 <= 0x10007fff8000 /\
(F + 1024 <= 0x7fff7fff \/ (0x10007fff8000 <= F /\ shadow_addr F + 128 <= F)) /\
4096 <= pp /\ pp + 19744 <= alloc_ceiling /\ (pp + 19744 <= 0x7fff7fff \/ 0x10007fff8000 <= pp) /\
(pp + 19744 <= F \/ F + 1024 <= pp) /\ alloc_ceiling + 16384 <= R.
Lemma hbp_i_lay_b : forall R F pp, hbp_i_lay R F pp ->
4096 <= F /\ F + 1024 <= alloc_ceiling /\ 0x7fff8000 <= shadow_addr F /\ shadow_addr F + 128 <= 0x10007fff8000 /\
4096 <= pp /\ pp + 19744 <= alloc_ceiling /\ alloc_ceiling + 16384 <= R.
Proof. intros R F pp (A1 & A2 & _ & A4 & A5 & _ & A7 & A8 & _ & _ & A11). repeat split; assumption. Qed.
Lemma hbp_i_lay_8 : forall R F pp, hbp_i_lay R F pp -> F mod 8 = 0.
Proof. intros R F pp (_ & _ & A3 & _). exact A3. Qed.
Lemma hbp_i_sh_rng : forall R F pp j, hbp_i_lay R F pp -> 0 <= j < 128 -> 0 <= shadow_addr F + j < 2 ^ 64.
Proof. intros R F pp j L Hj. pose proof (hbp_i_lay_b _ _ _ L) as (_ & _ & A4 & A5 & _). lia. Qed.
Lemma hbp_i_amem : forall R F pp o n, hbp_i_lay R F pp -> 0 <= o -> 0 <= n -> o + n <= 1024 -> amem_range (F + o) n.
Proof.
intros R F pp o n (_ & A2 & _ & _ & _ & A6 & _) Ho Hn Hon. pose proof asan_consts as (C1 & _).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
Qed.
Lemma hbp_i_sep : forall R F pp, hbp_i_lay R F pp -> pp + PP_SIZE <= F + 240 \/ F + 240 + ENT_SIZE <= pp.
Proof. intros R F pp (_ & _ & _ & _ & _ & _ & _ & _ & _ & A10 & _). unfold PP_SIZE, ENT_SIZE. lia. Qed.
Lemma hbp_i_F_app : forall R F pp x, hbp_i_lay R F pp -> F <= x < F + 1024 ->
~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof. intros R F pp x (_ & _ & _ & _ & _ & A6 & _) Hx. unfold SHADOW_OFF. lia. Qed.
(* what the block writes misses the real-frame cells, the frame's other shadow bytes and the rest of pp *)
Lemma hbp_i_nw_R : forall R F pp len a, hbp_i_lay R F pp -> 0 <= len -> len + 16 <= POD_BUF_MAX -> R <= a ->
~ hbp_i_Wr R F pp len a.
Proof.
intros R F pp len a L Hl0 Hl16 Ha. pose proof (hbp_i_lay_b _ _ _ L) as (A1 & A2 & A4 & A5 & A7 & A8 & A11).
pose proof asan_consts as (C1 & _).
unfold hbp_i_Wr, pwe_E. change (pwe_len hbp_i_ent) with 16.
unfold T_pwe_STK, ESTACK, OFF_LEN, POD_BUF_MAX in *. lia.
Qed.
Lemma hbp_i_nw_sh : forall R F pp len j, hbp_i_lay R F pp -> 0 <= len -> len + 16 <= POD_BUF_MAX ->
0 <= j < 116 -> ~ (30 <= j < 43) -> ~ hbp_i_Wr R F pp len (shadow_addr F + j).
Proof.
intros R F pp len j (A1 & A2 & _ & A4 & A5 & A6 & A7 & A8 & A9 & _ & A11) Hl0 Hl16 Hj Hn.
pose proof asan_consts as (C1 & _).
unfold hbp_i_Wr, pwe_E. change (pwe_len hbp_i_ent) with 16.
unfold T_pwe_STK, ESTACK, OFF_LEN, POD_BUF_MAX in *. lia.
Qed.
Lemma hbp_i_nw_pp : forall R F pp len y, hbp_i_lay R F pp -> 0 <= len -> len + 16 <= POD_BUF_MAX ->
pp <= y < pp + PP_SIZE -> ~ (pp + len <= y < pp + len + 16) -> ~ (pp + OFF_LEN <= y < pp + OFF_LEN + 8) ->
~ hbp_i_Wr R F pp len y.
Proof.
intros R F pp len y (A1 & A2 & _ & A4 & A5 & _ & A7 & A8 & A9 & A10 & A11) Hl0 Hl16 Hy Hn1 Hn2.
pose proof asan_consts as (C1 & _).
unfold hbp_i_Wr, pwe_E. change (pwe_len hbp_i_ent) with 16.
unfold T_pwe_STK, ESTACK, OFF_LEN, POD_BUF_MAX, PP_SIZE in *. lia.
Qed.
(* before the call of pod_write_ent the block has written only e's shadow, e and the memset call's stack *)
Lemma hbp_i_pre_R : forall R F pp a, hbp_i_lay R F pp -> R <= a ->
~ (shadow_addr F + 30 <= a < shadow_addr F + 43) /\ ~ (F + 240 <= a < F + 344) /\ ~ (R - ESTACK <= a < R).
Proof.
intros R F pp a L Ha. pose proof (hbp_i_lay_b _ _ _ L) as (A1 & A2 & A4 & A5 & A7 & A8 & A11).
pose proof asan_consts as (C1 & _). lia.
Qed.
Lemma hbp_i_pre_pp : forall R F pp y, hbp_i_lay R F pp -> pp <= y < pp + PP_SIZE ->
~ (shadow_addr F + 30 <= y < shadow_addr F + 43) /\ ~ (F + 240 <= y < F + 344) /\ ~ (R - ESTACK <= y < R).
Proof.
intros R F pp y (A1 & A2 & _ & A4 & A5 & _ & A7 & A8 & A9 & A10 & A11) Hy.
pose proof asan_consts as (C1 & _). unfold ESTACK, PP_SIZE in *. lia.
Qed.
Lemma hbp_i_pre_sh : forall R F pp j, hbp_i_lay R F pp -> 0 <= j < 116 ->
~ (F + 240 <= shadow_addr F + j < F + 344) /\ ~ (R - ESTACK <= shadow_addr F + j < R).
Proof.
intros R F pp j (A1 & A2 & _ & A4 & A5 & A6 & _ & _ & _ & _ & A11) Hj.
pose proof asan_consts as (C1 & _). unfold ESTACK. lia.
Qed.
(* the block's writes lie in the callees' stack below R or in M01's write set *)
Lemma hbp_i_Wr_E1 : forall (cx : hsu_scx rsegs) len a, 0 <= len -> len + 16 <= POD_BUF_MAX ->
hbp_i_Wr (e_R (x_e cx)) (e_F (x_e cx)) (e_pp (x_e cx)) len a ->
(e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/ hsu_E1 rsegs headamp_himg_B cx a.
Proof.
intros cx len a Hl0 Hl16 [X|[X|[X|X]]].
- right. apply hbp_E1_sh. lia.
- right. apply hbp_E1_F. lia.
- left. unfold T_pwe_STK, ESTACK, T_SEG_STK, ASTACK in *. lia.
- right. apply hbp_E1_pp. unfold pwe_E in X. change (pwe_len hbp_i_ent) with 16 in X.
  unfold OFF_LEN, PP_SIZE, POD_BUF_MAX in *. lia.
Qed.
(* e's 104 bytes: type 4, size 4, the memset's 96 zeros (the body le32 0 and its tail) *)
Lemma hbp_i_ent_bytes : forall (H : word -> bool) mem q,
val_mem rsegs (mrestrict H mem) q 4 4 -> val_mem rsegs (mrestrict H mem) (q + 4) 4 4 ->
(forall j, 0 <= j < 96 -> aview rsegs H mem (q + 8 + j) = Some 0) ->
garr8 rsegs (mrestrict H mem) q (map (fun x : byte => bv_unsigned x) (ent_mem hbp_i_ent)).
Proof.
intros H mem q V0 V4 Vz.
change (garr8 rsegs (mrestrict H mem) q (map (fun x : byte => bv_unsigned x) (ent_mem hbp_i_ent)))
  with (hm_bytes rsegs H mem q (ent_mem hbp_i_ent)).
replace (ent_mem hbp_i_ent) with (Z_to_le_bytes 4 4 ++ Z_to_le_bytes 4 4 ++ zeros 96) by (vm_compute; reflexivity).
apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V0|].
rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4.
apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V4|].
rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4. replace (q + 4 + 4) with (q + 8) by lia.
apply (proj2 (hm_bytes_aview rsegs H mem (q + 8) (zeros 96))). intros j Hj.
unfold zeros in *. rewrite repeat_length in Hj. unfold NUL. rewrite nth_repeat.
rewrite (Vz (Z.of_nat j) ltac:(lia)). reflexivity.
Qed.
(* the shadow hull of a range of a frame object lies in the frame's shadow bytes *)
Lemma hbp_i_hull : forall H mem F pat o n, hd_fsh rsegs H mem F pat -> 0 <= F -> F mod 8 = 0 ->
56 <= o -> 0 < n -> o + n + 64 <= 8 * Z.of_nat (length pat) ->
shadow_hull_vis (aview rsegs H mem) (F + o) n.
Proof.
intros H mem F pat o n Hf HF0 HF8 Ho Hn Hl s Hs.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
assert (E1 : shadow_addr (F + o) = shadow_addr F + o / 8).
{ unfold shadow_addr. replace (F + o) with (F / 8 * 8 + o) by lia. rewrite Z.div_add_l by lia. lia. }
assert (E2 : shadow_addr (F + o + n - 1) = shadow_addr F + (o + n - 1) / 8).
{ unfold shadow_addr. replace (F + o + n - 1) with (F / 8 * 8 + (o + n - 1)) by lia. rewrite Z.div_add_l by lia. lia. }
rewrite E1, E2 in Hs. set (X := shadow_addr F) in *.
pose proof (Z.div_mod (X + o / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (X + o / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (X + (o + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (X + (o + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.div_mod o 8 ltac:(lia)). pose proof (Z.mod_pos_bound o 8 ltac:(lia)).
pose proof (Z.div_mod (o + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (o + n - 1) 8 ltac:(lia)).
assert (Hi : 0 <= s - X < Z.of_nat (length pat)) by lia.
specialize (Hf (s - X) Hi). replace (shadow_addr F + (s - X)) with s in Hf by (unfold X; lia). rewrite Hf. discriminate.
Qed.
End l.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* __asan_memset (0x52228), which the block calls on e's body *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet 0x52228.
(* pod_write_ent (0x84634, out of line in image B) under its contract, lib/AU/PweSpec.v *)
Hypothesis PWE : pod_write_ent_specX rsegs B MT 0x84634.

(* a frame keeps its address under the journal's layout steps *)
Lemma hbp_i_faddr : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos Hle. unfold frame_addr. destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. Qed.

Lemma hbp_i_lay_of : forall ly S W mem md pos pp R, AR rsegs B ly S W mem md -> In (4, pos) (frames S) ->
In (pp, PP_SIZE) (ablocks B ly S) -> alloc_ceiling + T_SEG_STK <= R -> hbp_i_lay R (frame_addr ly 4 pos) pp.
Proof using LAWS.
intros ly S W mem md pos pp R HAR HinF Hpp HR.
pose proof asan_consts as (C1 & _).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 pos HAR HinF) as (F1 & F2 & F3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR HinF) as (F32 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp PP_SIZE HAR Hpp) as (_ & P1 & P2 & P3 & _).
pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ 4 pos HAR Hpp HinF) as Hsep.
assert (Erq : req_size PP_SIZE = 19744) by reflexivity.
rewrite Erq in P2, P3, Hsep.
change (fs_frame_bytes 4) with 1024 in F2, F3, Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
set (F := frame_addr ly 4 pos) in *.
assert (F8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite F32, Z.add_0_r in D. rewrite D.
  replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring. apply Z_mod_mult. }
clear F32.
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite F8, Z.add_0_r in D8.
unfold hbp_i_lay. unfold shadow_addr, SHADOW_OFF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, T_SEG_STK, ASTACK in *.
split; [lia|]. split; [lia|]. split; [exact F8|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* __asan_memset's contract as a block [YCbq.v aj_intrin_at at OSet], with the I/O state kept (same_io from the
   contract's same_but_materialized) *)
Lemma hbp_i_memset_at : forall pc, aintrin_realizes rsegs B OSet pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof using LAWS.
intros pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull.
pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok rsegs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  destruct (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
  split; [apply (apresent_writable rsegs); exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull I). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS Hsegs STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; zlia].
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [apply same_io_materialized; exact Hsame|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr | exact Hpres2].
Qed.

(* the entry state of a run that reads and writes no memory *)
Lemma hbp_i_st0 : forall pc (regs : bvmap 5 word) (H : word -> bool) memc,
st_ok rsegs (Ereg regs (hbp_extra [])) (hbp_i_ss0 pc) (restrict H (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc regs H memc. rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- reflexivity.
- constructor.
- exact I.
- split; [|split; [exact I | exact I]]. cbn [hbp_i_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite hbp_extra_K. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  repeat split; try lia; apply Z.mod_1_r.
Qed.

(* ---- 0x81508 .. 0x81520, to the memset call: a0 = &e + 8, a1 = 0, a2 = 96, ra = 0x81524, and the loop's three
   values saved: s2 = t0, s5 = t3, s7 = t2 ---- *)
Lemma hbp_i_runA : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R q8 : Z) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0 <= R -> R + 0xa8 <= 2 ^ 64 -> 0 <= q8 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa0) 8 q8 ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io mdc md2 ->
 (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [1; 10; 11; 12; 18; 21; 23]%bv -> getr regs2 r = getr regs r) ->
 getr regs2 1 = w64 HBP_I_B -> getr regs2 10 = w64 q8 -> getr regs2 11 = w64 0 -> getr regs2 12 = w64 96 ->
 getr regs2 18 = getr regs 5 -> getr regs2 21 = getr regs 28 -> getr regs2 23 = getr regs 7 ->
 SRr rsegs W (mkCfg (mkst regs2 (w64 HBP_I_MS) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs HBP_I_A regs memc mdc) Q.
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R q8 Q HJ H9 HR0 HR1 Hq Va KONT.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (E9 : bv_unsigned (ew (Ereg regs (hbp_extra [q8])) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs (hbp_extra [q8])) hbp_i_ssA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HBP_I_A) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, hbp_i_rA.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    eapply hbp_chunk8; [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Va].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [hbp_i_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite hbp_extra_K. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
assert (E33 : ew (Ereg regs (hbp_extra [q8])) 33 = Z_to_bv 64 q8) by reflexivity.
assert (E5 : ew (Ereg regs (hbp_extra [q8])) 5 = getr regs 5) by exact (ew_Ereg_nat regs _ 5 5%bv eq_refl).
assert (E7 : ew (Ereg regs (hbp_extra [q8])) 7 = getr regs 7) by exact (ew_Ereg_nat regs _ 7 7%bv eq_refl).
assert (E28 : ew (Ereg regs (hbp_extra [q8])) 28 = getr regs 28) by exact (ew_Ereg_nat regs _ 28 28%bv eq_refl).
remember (Ereg regs (hbp_extra [q8])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (hbp_extra [q8])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs HBPBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 HBP_I_A) with (Z_to_bv 64 HBP_I_A).
aj_run_to_tok hbp_tbl_ok HS HJ SHOK HBPspan HBP_I_MS; [awr_ok_tac | ].
hbp_keep hbp_kwr_ro.
pose proof (regs_kept_of_st_ok rsegs _ _ ms regs (hbp_extra [q8]) (w_H W) [1; 10; 11; 12; 18; 21; 23]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as KR.
hbp_i_reg HS (1%bv : bv 5) Rg1. hbp_i_reg HS (10%bv : bv 5) Rg10. hbp_i_reg HS (11%bv : bv 5) Rg11.
hbp_i_reg HS (12%bv : bv 5) Rg12. hbp_i_reg HS (18%bv : bv 5) Rg18. hbp_i_reg HS (21%bv : bv 5) Rg21.
hbp_i_reg HS (23%bv : bv 5) Rg23.
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1.
apply KONT.
- exact HJ.
- let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
- intros a Ha. exact (KE a Ha (fun X => X)).
- exact KR.
- rewrite Rg1. reflexivity.
- rewrite Rg10. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33.
- rewrite Rg11. reflexivity.
- rewrite Rg12. reflexivity.
- rewrite Rg18. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E5.
- rewrite Rg21. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E28.
- rewrite Rg23. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E7.
Qed.

(* ---- 0x81524 .. 0x81534, to pod_write_ent's call: e's type and size (4 and 4), a0 = pp, a1 = &e,
   ra = 0x8153c ---- *)
Lemma hbp_i_runB : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R q pp pos : Z) (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0 <= R -> R + 0x150 <= 2 ^ 64 -> 0 <= q -> q + 8 <= R + 0xb8 -> 0 <= pp < 2 ^ 64 ->
In (4, pos) own -> frame_addr lyc 4 pos <= q -> q + 8 <= frame_addr lyc 4 pos + 1024 ->
(forall o, 0 <= o < 8 -> apresent (w_H W) memc (q + o)) ->
q mod 8 = 0 -> 4096 <= q -> q <= 0x7fffff800000 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF q 8 ->
(forall x, q <= x < q + 8 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb8) 8 q ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io mdc md2 ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [1; 10; 11]%bv -> getr regs2 r = getr regs r) ->
 getr regs2 1 = w64 HBP_I_C -> getr regs2 10 = w64 pp -> getr regs2 11 = w64 q ->
 val_mem rsegs (mrestrict (w_H W) mem2) q 4 4 -> val_mem rsegs (mrestrict (w_H W) mem2) (q + 4) 4 4 ->
 SRr rsegs W (mkCfg (mkst regs2 (w64 HBP_I_PWE) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (mkCfg (mkst regs (w64 HBP_I_B) memc (seg_rom rsegs)) mdc) Q.
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R q pp pos Q
  HJ H9 HR0 HR1 Hq0 HqR Hpp Hown HqF1 HqF2 Hpres Hq8 Hq4096 HqHI Hqra Hqapp Vb8 V148 KONT.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (E9 : bv_unsigned (ew (Ereg regs (hbp_extra [q; pp])) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : ew (Ereg regs (hbp_extra [q; pp])) 33 = Z_to_bv 64 q) by reflexivity.
assert (E34 : ew (Ereg regs (hbp_extra [q; pp])) 34 = Z_to_bv 64 pp) by reflexivity.
assert (E33u : bv_unsigned (ew (Ereg regs (hbp_extra [q; pp])) 33) = q)
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs (hbp_extra [q; pp])) hbp_i_ssB
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HBP_I_B) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold region_ok, hbp_i_rB1.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      eapply hbp_chunk8; [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E33 | lia | exact Vb8].
    + unfold region_ok, hbp_i_rB2.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      eapply hbp_chunk8; [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E34 | lia | exact V148].
    + unfold region_ok, hbp_i_rBe.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E33u.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
  - unfold hbp_i_rB1, hbp_i_rB2, hbp_i_rBe. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E33u. lia.
  - split; [|split; [exact I | exact I]]. cbn [hbp_i_factsB f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite hbp_extra_K, E33u. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite Z.mod_1_r.
    repeat split; try lia; exact Hq8. }
assert (E32 : ew (Ereg regs (hbp_extra [q; pp])) 32 = Z_to_bv 64 SHADOW_OFF) by apply hbp_extra_K.
remember (Ereg regs (hbp_extra [q; pp])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (hbp_extra [q; pp])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs HBPBx [mkSHE 33 0 8] E (mrestrict (w_H W) memc)).
{ constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H W) memc E HBPBx 33 q 8 q 0 8 Hqra).
  - unfold HBPBx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF. lia.
  - apply (U_atom E 33 q E33). lia.
  - lia.
  - lia.
  - intros x Hx. apply Hqapp. lia. }
change (w64 HBP_I_B) with (Z_to_bv 64 HBP_I_B).
aj_run_to_tok hbp_tbl_ok HS HJ SHOK HBPspan HBP_I_PWE.
{ (* e's first 8 bytes lie in the frame for locals the journal holds *)
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat q); [reflexivity | exact E33u | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. right. right. exists 4, pos. split; [exact Hown|].
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 4) with 1024. lia. }
pose proof (regs_kept_of_st_ok rsegs _ _ ms regs (hbp_extra [q; pp]) (w_H W) [1; 10; 11]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as KR.
hbp_i_reg HS (1%bv : bv 5) Rg1. hbp_i_reg HS (10%bv : bv 5) Rg10. hbp_i_reg HS (11%bv : bv 5) Rg11.
pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _). cbn [ss_mem] in HOK.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HOK))) as (_ & _ & _ & Ce).
cbn [YP09.r_base YP09.r_chunks base_val] in Ce. rewrite E33u in Ce. clear HOK.
repeat rewrite Forall_cons_iff in Ce. destruct Ce as (C4 & C0 & _).
pose proof (val_of_chunk_ok rsegs E _ q 0 4 (SLit 4) 4 C0 eq_refl
  ltac:(split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(cbn; lia)) as V0.
pose proof (val_of_chunk_ok rsegs E _ q 4 4 (SLit 4) 4 C4 eq_refl
  ltac:(split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(cbn; lia)) as V4.
rewrite Z.add_0_r in V0. change (N.to_nat 4) with 4%nat in V0, V4.
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1.
apply KONT.
- exact HJ.
- let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
- intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (rg & Hr & Hb).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?E9, ?E33u in Hb; lia | ]).
  destruct Hr.
- exact KR.
- rewrite Rg1. reflexivity.
- rewrite Rg10. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E34.
- rewrite Rg11. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33.
- exact V0.
- exact V4.
Qed.

(* ---- 0x8153c .. 0x8154c, to the scope closers: a7 = s7, t3 = s5, s10 = 1, t0 = s2, a0 = -8 ---- *)
Lemma hbp_i_runC : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io mdc md2 ->
 (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [5; 10; 17; 26; 28]%bv -> getr regs2 r = getr regs r) ->
 getr regs2 5 = getr regs 18 -> getr regs2 10 = w64 (-8) -> getr regs2 17 = getr regs 23 ->
 getr regs2 26 = w64 1 -> getr regs2 28 = getr regs 21 ->
 SRr rsegs W (mkCfg (mkst regs2 (w64 HBP_I_O) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs HBP_I_C regs memc mdc) Q.
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q HJ KONT.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (hbp_i_st0 HBP_I_C regs (w_H W) memc) as HS.
assert (E18 : ew (Ereg regs (hbp_extra [])) 18 = getr regs 18) by exact (ew_Ereg_nat regs _ 18 18%bv eq_refl).
assert (E21 : ew (Ereg regs (hbp_extra [])) 21 = getr regs 21) by exact (ew_Ereg_nat regs _ 21 21%bv eq_refl).
assert (E23 : ew (Ereg regs (hbp_extra [])) 23 = getr regs 23) by exact (ew_Ereg_nat regs _ 23 23%bv eq_refl).
remember (Ereg regs (hbp_extra [])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (hbp_extra [])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs HBPBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 HBP_I_C) with (Z_to_bv 64 HBP_I_C).
aj_run_to_tok hbp_tbl_ok HS HJ SHOK HBPspan HBP_I_O; [awr_ok_tac | ].
hbp_keep hbp_kwr_ro.
pose proof (regs_kept_of_st_ok rsegs _ _ ms regs (hbp_extra []) (w_H W) [5; 10; 17; 26; 28]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as KR.
hbp_i_reg HS (5%bv : bv 5) Rg5. hbp_i_reg HS (10%bv : bv 5) Rg10. hbp_i_reg HS (17%bv : bv 5) Rg17.
hbp_i_reg HS (26%bv : bv 5) Rg26. hbp_i_reg HS (28%bv : bv 5) Rg28.
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1.
apply KONT.
- exact HJ.
- let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
- intros a Ha. exact (KE a Ha (fun X => X)).
- exact KR.
- rewrite Rg5. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E18.
- rewrite Rg10. cbn [sv_denot]. unfold w64. apply Z_to_bv64_eq_mod. reflexivity.
- rewrite Rg17. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E23.
- rewrite Rg26. reflexivity.
- rewrite Rg28. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E21.
Qed.

(* ---- 0x81588 .. 0x8158c, to LATCH: a3 = s4 ---- *)
Lemma hbp_i_runD : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io mdc md2 ->
 (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [13]%bv -> getr regs2 r = getr regs r) ->
 getr regs2 13 = getr regs 20 ->
 SRr rsegs W (mkCfg (mkst regs2 (w64 HBP_LATCH) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs HBP_I_D regs memc mdc) Q.
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q HJ KONT.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (hbp_i_st0 HBP_I_D regs (w_H W) memc) as HS.
assert (E20 : ew (Ereg regs (hbp_extra [])) 20 = getr regs 20) by exact (ew_Ereg_nat regs _ 20 20%bv eq_refl).
remember (Ereg regs (hbp_extra [])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (hbp_extra [])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs HBPBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 HBP_I_D) with (Z_to_bv 64 HBP_I_D).
aj_run_to_tok hbp_tbl_ok HS HJ SHOK HBPspan HBP_LATCH; [awr_ok_tac | ].
hbp_keep hbp_kwr_ro.
pose proof (regs_kept_of_st_ok rsegs _ _ ms regs (hbp_extra []) (w_H W) [13]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as KR.
hbp_i_reg HS (13%bv : bv 5) Rg13.
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1.
apply KONT.
- exact HJ.
- let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
- intros a Ha. exact (KE a Ha (fun X => X)).
- exact KR.
- rewrite Rg13. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E20.
Qed.

(* ================================ the block SEL7 0x814d4 -> LATCH 0x82ae4 ================================
   Entry facts: s1 = R = sp, s3 = shadow_addr F, t0 = i, s4 = seen, t2 = cur, t3 = lft, the cells R+0xa0 (&e + 8),
   R+0xb8 (&e = F + 0xf0), R+0x148 (pp), pp's len cell = len, the frame's shadow the prologue's pattern. At LATCH:
   t0 = i, a3 = seen, a7 = cur, t3 = lft, s7 = -8, s10 = 1, the frame's shadow the prologue's pattern again, the
   sixteen bytes enc_pod (Ent 4 4 (le32 0)) at pp + len and len + 16 in the len cell. *)
Definition hbp_i_R (F pp len i seen cur lft : Z) (W2 : world rsegs) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) : Prop :=
getr regs2 5 = w64 i /\ getr regs2 13 = w64 seen /\ getr regs2 17 = w64 cur /\ getr regs2 28 = w64 lft /\
getr regs2 23 = w64 (-8) /\ getr regs2 26 = w64 1 /\
hd_fsh rsegs (w_H W2) mem2 F headamp_B_shA /\
garr8 rsegs (mrestrict (w_H W2) mem2) (pp + len) (map (fun x : byte => bv_unsigned x) (enc_pod hbp_i_ent)) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (pp + OFF_LEN) 8 (len + 16).

Lemma hbp_int7 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R F pp pos len i seen cur lft : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> st_nev S + k <= EV_MAX ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
getr regs 5 = w64 i -> getr regs 20 = w64 seen -> getr regs 7 = w64 cur -> getr regs 28 = w64 lft ->
sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 -> R mod 16 = 0 -> alloc_ceiling + T_SEG_STK <= R ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
In (pp, PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, PP_SIZE) (ablocks B ly S) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa0) 8 (F + HSU_E + 8) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb8) 8 (F + HSU_E) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + OFF_LEN) 8 len ->
hd_fsh rsegs (w_H W) memc F headamp_B_shA ->
0 <= len -> len mod 8 = 0 -> len + 16 <= POD_BUF_MAX ->
SRr rsegs W (cfg_at rsegs HBP_SEL7 regs memc mdc)
(hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc HBP_LATCH hbp_i_clob
 (hbp_i_Wr R F pp len) (hbp_i_R F pp len i seen cur lft)).
Proof using MTL LAWS AMEMSET PWE.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp pos len i seen cur lft
  HJ Hnev H2 H3 H4 H9 H19 H5 H20 H7 H28 HRlo HRhi HR16 HRc Hown HF Hpp Hpp0 Va0 Vb8 V148 Vlen Hfsh Hl0 Hl8 Hl16.
unfold HSU_E in Va0, Vb8.
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp16 & _ & _ & _ & Hshi & H47 & _).
assert (HinF : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (hbp_i_lay_of _ _ _ _ _ pos pp R HAR HinF Hpp HRc) as LAY. rewrite <- HF in LAY.
pose proof (hbp_i_lay_b _ _ _ LAY) as (LB1 & LB2 & LB3 & LB4 & LB5 & LB6 & LB7).
pose proof (hbp_i_lay_8 _ _ _ LAY) as LF8.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HTP : T_pwe_STK = 4144) by reflexivity.
(* ---- 0x814d4 .. 0x81504: e in scope ---- *)
eapply SRr_bind.
{ refine (hdu_scope_e_in B MT MTL LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 4 pos HJ Hown
    ltac:(lia) _ _ _ _).
  - rewrite <- HF. exact H19.
  - rewrite <- HF. lia.
  - rewrite <- HF. lia.
  - change (fs_frame_bytes 4 / 8) with 128. lia. }
intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & K1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
rewrite <- HF in Hm1, HR1. cbv beta in Hm1.
pose proof HJ1 as (_ & Hly1 & _).
assert (EF1 : frame_addr ly1 4 pos = F).
{ rewrite HF, (hbp_i_faddr _ _ _ 4 pos Hly1), (hbp_i_faddr _ _ _ 4 pos Hly). reflexivity. }
assert (Hpp1 : In (pp, PP_SIZE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hp1 | exact Hpp]).
assert (R1r : forall r : bv 5, bv_unsigned r <> 0 -> getr regs1 r = getr regs r)
  by (intros r Hr; apply K1; [exact Hr | intros []]).
assert (Hfsh1 : hd_fsh rsegs (w_H W1) mem1 F (hmu_sh false false false true false false false false)).
{ rewrite <- (hmu_sh_e_in false false false false false false false false), hmu_sh_P0.
  apply (hm_fsh_set rsegs (w_H W) memc (w_H W1) mem1 F headamp_B_shA 30 13 0 Hfsh).
  - intros j Hj. apply HR1. lia.
  - intros j Hj Hn. rewrite hbp_i_shA_len in Hj.
    apply Hm1; [apply (hbp_i_sh_rng R F pp j LAY); lia | lia]. }
(* ---- 0x81508 .. 0x81520 ---- *)
apply (hbp_i_runA STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 R (F + 240 + 8) _ HJ1).
{ exact (eq_trans (R1r 9%bv ltac:(cbv; discriminate)) H9). }
{ lia. } { lia. } { lia. }
{ eapply val_mem_kept; [|exact Va0]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  destruct (hbp_i_pre_R R F pp (R + 0xa0 + j) LAY ltac:(lia)) as (N1 & _ & _).
  apply Hm1; [lia | exact N1]. }
intros regs2 mem2 md2 HJ2 Hio2 Hm2 K2 RA1 RA10 RA11 RA12 RA18 RA21 RA23.
assert (KK2 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hbp_i_clob -> getr regs2 r = getr regs r).
{ intros r Hr Hn. rewrite (K2 r Hr ltac:(hbp_i_sub Hn)). exact (R1r r Hr). }
assert (Hfsh2 : hd_fsh rsegs (w_H W1) mem2 F (hmu_sh false false false true false false false false)).
{ apply (hm_fsh_kept rsegs (w_H W1) mem1 (w_H W1) mem2 F _ Hfsh1). intros j Hj. rewrite hmu_sh_len in Hj.
  apply Hm2. apply (hbp_i_sh_rng R F pp j LAY). lia. }
(* ---- the call of __asan_memset(&e + 8, 0, 96) ---- *)
eapply SRr_bind.
{ apply (hbp_i_memset_at HBP_I_MS AMEMSET W1 regs2 mem2 STK sp0 FP ly S W0 mem0 md0 own ly1 S1 md2 k
    (F + 240 + 8) 0 96 (R - sp0) (Z_to_bv 64 HBP_I_B) HJ2).
  - exact RA10.
  - exact RA11.
  - exact RA12.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite (KK2 2%bv ltac:(cbv; discriminate) ltac:(hbp_i_nin)), H2. unfold w64.
    rewrite unsigned_lit_small by lia. lia.
  - apply hbp_i_mod16_sub; assumption.
  - lia.
  - rewrite HES. rewrite HTS in HRlo. lia.
  - rewrite (KK2 3%bv ltac:(cbv; discriminate) ltac:(hbp_i_nin)). exact H3.
  - rewrite (KK2 4%bv ltac:(cbv; discriminate) ltac:(hbp_i_nin)). exact H4.
  - exact RA1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split.
    + right. right. right. exists 4, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd].
      rewrite EF1. change (fs_frame_bytes 4) with 1024. lia.
    + rewrite HES. lia.
  - replace (F + 240 + 8) with (F + 248) by lia. apply (hbp_i_amem R F pp 248 96 LAY); lia.
  - pose proof (hmu_B_ra_e rsegs (w_H W1) mem2 F false false false false false false false 8 96 Hfsh2 LF8
      ltac:(lia) ltac:(lia)) as X. unfold HMU_E in X. exact X.
  - intros _. replace (F + 240 + 8) with (F + 248) by lia.
    apply (hbp_i_hull (w_H W1) mem2 F _ 248 96 Hfsh2); [lia | exact LF8 | lia | lia |].
    rewrite hmu_sh_len. lia. }
intros W2' c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & HP3 & R3_10 & Heff3 & Hfr3 & Hpres3).
assert (KK3 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hbp_i_clob -> getr regs3 r = getr regs r).
{ intros r Hr Hn. rewrite (hbp_i_pres _ _ r HP3 Hr Hn). exact (KK2 r Hr Hn). }
assert (J13 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 248 <= a < F + 344) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W1) mem3 a = aview rsegs (w_H W1) mem1 a).
{ intros a Ha N2 N3. rewrite (Hfr3 a Ha ltac:(lia) ltac:(lia)). exact (Hm2 a Ha). }
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & Hfrs3 & _).
assert (HinF3 : In (4, pos) (frames S1)) by (rewrite Hfrs3; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR3 HinF3) as (_ & _ & HFp3 & _).
rewrite EF1 in HFp3. change (fs_frame_bytes 4) with 1024 in HFp3.
(* ---- 0x81524 .. 0x81534 ---- *)
apply (hbp_i_runB STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem3 md3 k regs3 R (F + 240) pp pos _ HJ3).
{ exact (eq_trans (KK3 9%bv ltac:(cbv; discriminate) ltac:(hbp_i_nin)) H9). }
{ lia. } { lia. } { lia. } { lia. } { lia. }
{ exact Hown. }
{ rewrite EF1. lia. } { rewrite EF1. lia. }
{ intros o Ho. exact (proj1 (HFp3 (F + 240 + o) ltac:(lia))). }
{ apply hbp_i_mod8_240. exact LF8. } { lia. } { lia. }
{ assert (Hfsh3 : hd_fsh rsegs (w_H W1) mem3 F (hmu_sh false false false true false false false false)).
  { apply (hm_fsh_kept rsegs (w_H W1) mem1 (w_H W1) mem3 F _ Hfsh1). intros j Hj. rewrite hmu_sh_len in Hj.
    destruct (hbp_i_pre_sh R F pp j LAY ltac:(lia)) as (N2 & N3).
    apply J13; [apply (hbp_i_sh_rng R F pp j LAY); lia | lia | exact N3]. }
  pose proof (hmu_B_ra_e rsegs (w_H W1) mem3 F false false false false false false false 0 8 Hfsh3 LF8
    ltac:(lia) ltac:(lia)) as X. unfold HMU_E in X. rewrite Z.add_0_r in X. exact X. }
{ intros x Hx. apply (hbp_i_F_app R F pp x LAY). lia. }
{ eapply val_mem_kept; [|exact Vb8]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  destruct (hbp_i_pre_R R F pp (R + 0xb8 + j) LAY ltac:(lia)) as (N1 & N2 & N3).
  rewrite (J13 (R + 0xb8 + j) ltac:(lia) ltac:(lia) N3). apply Hm1; [lia | exact N1]. }
{ eapply val_mem_kept; [|exact V148]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  destruct (hbp_i_pre_R R F pp (R + 0x148 + j) LAY ltac:(lia)) as (N1 & N2 & N3).
  rewrite (J13 (R + 0x148 + j) ltac:(lia) ltac:(lia) N3). apply Hm1; [lia | exact N1]. }
intros regs4 mem4 md4 HJ4 Hio4 Hm4 K4 RB1 RB10 RB11 VB0 VB4.
assert (KK4 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hbp_i_clob -> getr regs4 r = getr regs r).
{ intros r Hr Hn. rewrite (K4 r Hr ltac:(hbp_i_sub Hn)). exact (KK3 r Hr Hn). }
assert (J14 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 240 <= a < F + 344) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W1) mem4 a = aview rsegs (w_H W1) mem1 a).
{ intros a Ha N2 N3. rewrite (Hm4 a Ha ltac:(lia)). exact (J13 a Ha ltac:(lia) N3). }
assert (Hfsh4 : hd_fsh rsegs (w_H W1) mem4 F (hmu_sh false false false true false false false false)).
{ apply (hm_fsh_kept rsegs (w_H W1) mem1 (w_H W1) mem4 F _ Hfsh1). intros j Hj. rewrite hmu_sh_len in Hj.
  destruct (hbp_i_pre_sh R F pp j LAY ltac:(lia)) as (N2 & N3).
  apply J14; [apply (hbp_i_sh_rng R F pp j LAY); lia | exact N2 | exact N3]. }
assert (SP4 : spZ regs4 = R).
{ unfold spZ. rewrite (KK4 2%bv ltac:(cbv; discriminate) ltac:(hbp_i_nin)), H2. unfold w64.
  apply unsigned_lit_small. lia. }
(* ---- the call of pod_write_ent(pp, &e) ---- *)
eapply SRr_bind.
{ apply (PWE STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem4 md4 k regs4 pp (F + 240) len hbp_i_ent).
  - split; [exact HJ4|]. split; [rewrite RB1; apply ret_ok_even; vm_compute; reflexivity|].
    split; [unfold raZ; rewrite RB1; unfold w64, HBP_I_C; rewrite unsigned_lit_small by lia; lia|].
    split; [rewrite (KK4 3%bv ltac:(cbv; discriminate) ltac:(hbp_i_nin)); exact H3|].
    split; [rewrite (KK4 4%bv ltac:(cbv; discriminate) ltac:(hbp_i_nin)); exact H4|].
    rewrite SP4. split; [exact HR16|]. split; [rewrite HTP; rewrite HTS in HRlo; lia|].
    split; [lia | exact Hnev].
  - exact RB10.
  - exact RB11.
  - exact (proj1 (pwe_pp_of_block rsegs B ly1 S1 W1 mem4 md4 pp (proj1 HJ4) Hpp1)).
  - exact (proj1 (proj2 (pwe_pp_of_block rsegs B ly1 S1 W1 mem4 md4 pp (proj1 HJ4) Hpp1))).
  - exact (proj1 (proj2 (proj2 (pwe_pp_of_block rsegs B ly1 S1 W1 mem4 md4 pp (proj1 HJ4) Hpp1)))).
  - exact (proj1 (proj2 (proj2 (proj2 (pwe_pp_of_block rsegs B ly1 S1 W1 mem4 md4 pp (proj1 HJ4) Hpp1))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (pwe_pp_of_block rsegs B ly1 S1 W1 mem4 md4 pp (proj1 HJ4) Hpp1)))))).
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 (pwe_pp_of_block rsegs B ly1 S1 W1 mem4 md4 pp (proj1 HJ4) Hpp1)))))).
  - exact (pwe_awr_fresh B STK sp0 FP ly S ly1 S1 own pp len hbp_i_ent Hpp1 Hpp0 Hl0
      ltac:(change (pwe_len hbp_i_ent) with 16; lia)).
  - left. rewrite SP4, HTP. unfold PP_SIZE. lia.
  - eapply val_mem_kept; [|exact Vlen]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
    destruct (hbp_i_pre_pp R F pp (pp + OFF_LEN + j) LAY ltac:(unfold OFF_LEN, PP_SIZE; lia)) as (N1 & N2 & N3).
    assert (Hb : 0 <= pp + OFF_LEN + j < 2 ^ 64) by (unfold OFF_LEN; lia).
    rewrite (J14 _ Hb N2 N3). exact (Hm1 _ Hb N1).
  - exact Hl0.
  - exact Hl8.
  - change (pwe_len hbp_i_ent) with 16. exact Hl16.
  - lia.
  - apply hbp_i_mod8_240. exact LF8.
  - apply (hbp_i_amem R F pp 240 ENT_SIZE LAY); unfold ENT_SIZE; lia.
  - reflexivity.
  - change (e_size hbp_i_ent) with 4. unfold ENT_SIZE. lia.
  - change (e_type hbp_i_ent) with 4. lia.
  - apply hbp_i_ent_bytes; [exact VB0 | exact VB4 |]. intros j Hj.
    rewrite (Hm4 (F + 240 + 8 + j) ltac:(lia) ltac:(lia)). rewrite (Heff3 j Hj). reflexivity.
  - pose proof (hmu_B_ra_e rsegs (w_H W1) mem4 F false false false false false false false 0 104 Hfsh4 LF8
      ltac:(lia) ltac:(lia)) as X. unfold HMU_E in X. rewrite Z.add_0_r in X. exact X.
  - apply (hbp_i_hull (w_H W1) mem4 F _ 240 104 Hfsh4); [lia | exact LF8 | lia | lia |].
    rewrite hmu_sh_len. lia.
  - exact (hbp_i_sep R F pp LAY).
  - left. rewrite SP4, HTP. unfold ENT_SIZE. lia. }
intros W5 c5 _ (fx5 & ly5 & S5 & regs5 & mem5 & md5 & -> & Hfx5 & HJ5 & HP5 & Hf5 & Hp5 & Hio5 & Hmo5 & Hm5 & HR5).
cbv beta in Hfx5. subst fx5. destruct HR5 as (Benc & Blen & _ & _ & _).
rewrite RB1. rewrite SP4 in Hm5.
assert (KK5 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hbp_i_clob -> getr regs5 r = getr regs r).
{ intros r Hr Hn. rewrite (hbp_i_pres _ _ r HP5 Hr Hn). exact (KK4 r Hr Hn). }
pose proof HJ5 as (_ & Hly5 & _).
assert (EF5 : frame_addr ly5 4 pos = F).
{ rewrite HF, (hbp_i_faddr _ _ _ 4 pos Hly5), (hbp_i_faddr _ _ _ 4 pos Hly). reflexivity. }
(* ---- 0x8153c .. 0x8154c ---- *)
apply (hbp_i_runC STK sp0 FP ly S W0 mem0 md0 own ly5 S5 W5 mem5 md5 k regs5 _ HJ5).
intros regs6 mem6 md6 HJ6 Hio6 Hm6 K6 RC5 RC10 RC17 RC26 RC28.
assert (KK6 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hbp_i_clob -> getr regs6 r = getr regs r).
{ intros r Hr Hn. rewrite (K6 r Hr ltac:(hbp_i_sub Hn)). exact (KK5 r Hr Hn). }
(* ---- 0x81550 .. 0x81584: e out of scope ---- *)
eapply SRr_bind.
{ refine (hdu_scope_e_out B MT MTL LAWS STK sp0 FP ly S W0 mem0 md0 own ly5 S5 W5 mem6 md6 k regs6 4 pos HJ6 Hown
    ltac:(lia) _ _ _ _ _).
  - rewrite EF5. exact (eq_trans (KK6 19%bv ltac:(cbv; discriminate) ltac:(hbp_i_nin)) H19).
  - exact RC10.
  - rewrite EF5. lia.
  - rewrite EF5. lia.
  - change (fs_frame_bytes 4 / 8) with 128. lia. }
intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & K7 & Hf7 & Hp7 & Hio7 & Hmo7 & Hm7 & HR7 & Hs7).
rewrite EF5 in Hm7, HR7. cbv beta in Hm7. unfold hdu_s7_m8 in Hs7.
(* ---- 0x81588 .. 0x8158c ---- *)
apply (hbp_i_runD STK sp0 FP ly S W0 mem0 md0 own ly7 S7 W7 mem7 md7 k regs7 _ HJ7).
intros regs8 mem8 md8 HJ8 Hio8 Hm8 K8 RD13.
(* ---- the post ---- *)
assert (MF : forall a, 0 <= a < 2 ^ 64 -> ~ hbp_i_Wr R F pp len a ->
  aview rsegs (w_H W7) mem8 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. unfold hbp_i_Wr in Hn.
  assert (N1 : ~ (shadow_addr F + 30 <= a < shadow_addr F + 43)) by (intro X; apply Hn; left; exact X).
  assert (N2 : ~ (F + 240 <= a < F + 344)) by (intro X; apply Hn; right; left; exact X).
  assert (N3 : ~ (R - T_pwe_STK <= a < R)) by (intro X; apply Hn; right; right; left; exact X).
  assert (N4 : ~ pwe_E pp len hbp_i_ent a) by (intro X; apply Hn; right; right; right; exact X).
  rewrite (Hm8 a Ha), (Hm7 a Ha N1), (Hm6 a Ha), (Hm5 a Ha N3 N4).
  rewrite (J14 a Ha N2 ltac:(rewrite HES; rewrite HTP in N3; lia)). exact (Hm1 a Ha N1). }
assert (MP : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 30 <= a < shadow_addr F + 43) ->
  aview rsegs (w_H W7) mem8 a = aview rsegs (w_H W5) mem5 a).
{ intros a Ha N1. rewrite (Hm8 a Ha), (Hm7 a Ha N1), (Hm6 a Ha). reflexivity. }
apply SRr_ret. red. exists ly7, S7, regs8, mem8, md8.
split; [reflexivity|].
split; [exact HJ8|].
split.
{ intros r Hr Hn. rewrite (K8 r Hr ltac:(hbp_i_sub Hn)), (K7 r Hr ltac:(hbp_i_sub Hn)). exact (KK6 r Hr Hn). }
split; [rewrite Hf7, Hf5, Hf1; reflexivity|].
split; [eapply Permutation_trans; [exact Hp7|]; eapply Permutation_trans; [exact Hp5 | exact Hp1]|].
split.
{ eapply same_io_trans; [exact Hio1|]. eapply same_io_trans; [exact Hio2|]. eapply same_io_trans; [exact Hio3|].
  eapply same_io_trans; [exact Hio4|]. eapply same_io_trans; [exact Hio5|]. eapply same_io_trans; [exact Hio6|].
  eapply same_io_trans; [exact Hio7 | exact Hio8]. }
split.
{ replace 0 with ((0 + 0) + 0) by reflexivity.
  exact (mle_station MT _ _ _ (0 + 0) 0 MTL (mle_station MT _ _ _ 0 0 MTL Hmo1 Hmo5) Hmo7). }
split; [exact MF|].
unfold hbp_i_R.
split.
{ refine (eq_trans (K8 5%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) _).
  refine (eq_trans (K7 5%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) _).
  refine (eq_trans RC5 _).
  refine (eq_trans (HP5 18 ltac:(unfold acallee_saved; lia)) _).
  refine (eq_trans (K4 18%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) _).
  refine (eq_trans (HP3 18 ltac:(unfold acallee_saved; lia)) _).
  refine (eq_trans RA18 _).
  exact (eq_trans (R1r 5%bv ltac:(cbv; discriminate)) H5). }
split.
{ refine (eq_trans RD13 _).
  refine (eq_trans (K7 20%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) _).
  exact (eq_trans (KK6 20%bv ltac:(cbv; discriminate) ltac:(hbp_i_nin)) H20). }
split.
{ refine (eq_trans (K8 17%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) _).
  refine (eq_trans (K7 17%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) _).
  refine (eq_trans RC17 _).
  refine (eq_trans (HP5 23 ltac:(unfold acallee_saved; lia)) _).
  refine (eq_trans (K4 23%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) _).
  refine (eq_trans (HP3 23 ltac:(unfold acallee_saved; lia)) _).
  refine (eq_trans RA23 _).
  exact (eq_trans (R1r 7%bv ltac:(cbv; discriminate)) H7). }
split.
{ refine (eq_trans (K8 28%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) _).
  refine (eq_trans (K7 28%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) _).
  refine (eq_trans RC28 _).
  refine (eq_trans (HP5 21 ltac:(unfold acallee_saved; lia)) _).
  refine (eq_trans (K4 21%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) _).
  refine (eq_trans (HP3 21 ltac:(unfold acallee_saved; lia)) _).
  refine (eq_trans RA21 _).
  exact (eq_trans (R1r 28%bv ltac:(cbv; discriminate)) H28). }
split; [exact (eq_trans (K8 23%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) Hs7)|].
split.
{ refine (eq_trans (K8 26%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) _).
  exact (eq_trans (K7 26%bv ltac:(cbv; discriminate) ltac:(hbp_notin)) RC26). }
split.
{ rewrite <- hbp_i_P0_out.
  apply (hm_fsh_set rsegs (w_H W) memc (w_H W7) mem8 F headamp_B_shA 30 13 248 Hfsh).
  - intros j Hj. rewrite (Hm8 (shadow_addr F + j) ltac:(apply (hbp_i_sh_rng R F pp j LAY); lia)).
    rewrite (HR7 j ltac:(lia)). reflexivity.
  - intros j Hj Hn. rewrite hbp_i_shA_len in Hj.
    apply MF; [apply (hbp_i_sh_rng R F pp j LAY); lia|].
    apply (hbp_i_nw_sh R F pp len j LAY Hl0 Hl16); lia. }
split.
{ change (hm_bytes rsegs (w_H W7) mem8 (pp + len) (enc_pod hbp_i_ent)).
  apply (hm_bytes_kept rsegs (w_H W5) mem5); [exact Benc|]. intros x Hx.
  change (Z.of_nat (length (enc_pod hbp_i_ent))) with 16 in Hx.
  destruct (hbp_i_pre_pp R F pp x LAY ltac:(unfold PP_SIZE, POD_BUF_MAX in *; lia)) as (N1 & _ & _).
  apply MP; [unfold POD_BUF_MAX in *; lia | exact N1]. }
{ change (pwe_len hbp_i_ent) with 16 in Blen.
  eapply val_mem_kept; [|exact Blen]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  destruct (hbp_i_pre_pp R F pp (pp + OFF_LEN + j) LAY ltac:(unfold OFF_LEN, PP_SIZE; lia)) as (N1 & _ & _).
  apply MP; [unfold OFF_LEN; lia | exact N1]. }
Qed.

(* ================================ the piece: SEL7 -> LATCH ================================ *)
Lemma hbp_piece_int7 : hsu_piece_W4_int7_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof using MTL LAWS AMEMSET PWE.
unfold hsu_piece_W4_int7_stmt. intros cx POST rest i Hst HL.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (hbp_R_bounds B cx _ Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (hbp_pp_blocks B LAWS cx _ Hpre) as (Ppin & Ppout & _).
pose proof asan_consts as (C1 & _).
pose proof Hpre as Hpre'. unfold hsu_pre, hd_seg_pre in Hpre'.
destruct Hpre' as (HJc & Hnev & _ & G3 & G4 & _ & _ & _ & _ & Hown & EF & _).
cbn [hi_cid headamp_himg_B] in Hown, EF.
unfold hsu_from_SEL7. intros ly2 S2 W2 regs2 mem2 md2 np ps r Hlen Hcut.
destruct Hcut as (Hb & Hat & Hpp & Hr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hpsl & Hsh & Hnp & Hps & Hnp3).
pose proof Hcore as (HJ & Hr234 & _ & HPerm & _).
pose proof HJc as (_ & Hlyc & _). pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _).
assert (EF2 : e_F (x_e cx) = frame_addr ly2 4 (x_pos cx)).
{ rewrite EF, (hbp_i_faddr _ _ _ 4 (x_pos cx) Hlyc), (hbp_i_faddr _ _ _ 4 (x_pos cx) Hly2). reflexivity. }
assert (HinF2 : In (4, x_pos cx) (frames S2)) by (rewrite Hfrs2; apply in_or_app; left; exact Hown).
assert (Ppin2 : In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Ppin]).
pose proof (hbp_i_lay_of _ _ _ _ _ (x_pos cx) (e_pp (x_e cx)) (e_R (x_e cx)) HAR2 HinF2 Ppin2 RB7) as LAY.
rewrite <- EF2 in LAY.
pose proof (hbp_i_lay_b _ _ _ LAY) as (LB1 & LB2 & LB3 & LB4 & LB5 & LB6 & LB7).
destruct (hbp_img_bounds 7 ps Hwf ltac:(lia)) as (IB1 & IB2 & IB3 & IB4).
unfold hsu_at_cx in Hat.
hbp_take Hat (LReg 9) (e_R (x_e cx)) A9.
hbp_take Hat (LReg 19) (shadow_addr (e_F (x_e cx))) A19.
hbp_take Hat (LReg 5) (Z.of_nat (length ps)) A5.
hbp_take Hat (LReg 20) (hsu_seen ps) A20.
hbp_take Hat (LReg 7) (hsu_cur rsegs cx rest r) A7.
hbp_take Hat (LReg 28) (Z.of_nat (length r)) A28.
hbp_take Hat (LCell XR 0xa0) (e_F (x_e cx) + HSU_E + 8) Aa0.
hbp_take Hat (LCell XR 0xb8) (e_F (x_e cx) + HSU_E) Ab8.
hbp_take Hat (LCell XR 0x148) (e_pp (x_e cx)) A148.
rewrite Z.mod_small in Aa0, Ab8, A148 by (unfold HSU_E; lia).
assert (A2 : getr regs2 2 = w64 (e_R (x_e cx))) by (exact (eq_trans (Hr234 2 ltac:(lia)) RB6)).
assert (A3 : getr regs2 3 = w64 (as_gp B)) by (exact (eq_trans (Hr234 3 ltac:(lia)) G3)).
assert (A4 : getr regs2 4 = w64 (as_tp B)) by (exact (eq_trans (Hr234 4 ltac:(lia)) G4)).
assert (Hb16 : Z.of_nat (length (pc_buf (PbCut 7 ps None))) <= POD_BUF_MAX) by (unfold POD_BUF_MAX; lia).
assert (Alen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + OFF_LEN) 8
  (Z.of_nat (length (pc_buf (PbCut 7 ps None))))).
{ unfold hsu_pp_at, pc_image in Hpp. exact (hm_pp_len rsegs _ _ _ _ _ _ Hb16 IB3 IB4 _ _ _ Hpp). }
eapply SRr_bind.
{ refine (hbp_int7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (e_F (x_e cx)) (e_pp (x_e cx)) (x_pos cx)
    (Z.of_nat (length (pc_buf (PbCut 7 ps None)))) (Z.of_nat (length ps)) (hsu_seen ps)
    (hsu_cur rsegs cx rest r) (Z.of_nat (length r))
    HJ Hnev A2 A3 A4 A9 A19 A5 A20 A7 A28 _ _ RB3 RB7 Hown EF2 Ppin2 Ppout Aa0 Ab8 A148 Alen Hfsh _ IB2 _);
  unfold POD_BUF_MAX in *; lia. }
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R5 & R13 & R17 & R28 & R23 & R26 & Rfsh & Renc & Rlen).
unfold hbp_i_clob in Hkeep.
clear RB3 IB2.
assert (SP : spZ (x_regs cx) = e_R (x_e cx)) by (unfold spZ; rewrite RB6; unfold w64; apply unsigned_lit_small; lia).
assert (Hcore3 : hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (hbp_core_step B MT MTL cx _ (hbp_i_Wr (e_R (x_e cx)) (e_F (x_e cx)) (e_pp (x_e cx))
    (Z.of_nat (length (pc_buf (PbCut 7 ps None))))) _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _).
  - hbp_regs234 Hkeep.
  - intros a Ha. rewrite SP.
    exact (hbp_i_Wr_E1 cx (Z.of_nat (length (pc_buf (PbCut 7 ps None)))) a ltac:(lia) ltac:(unfold POD_BUF_MAX; lia) Ha). }
assert (Hat' : hsu_at rsegs (w_H W2) mem2 regs2 (x_e cx) (hsu_Rc0 rsegs cx ++ hsu_Kc rsegs cx 7 np))
  by (hbp_list; hbp_from Hat).
assert (Hat3 : hsu_at rsegs (w_H W3) mem3 regs3 (x_e cx) (hsu_Rc0 rsegs cx ++ hsu_Kc rsegs cx 7 np)).
{ eapply hbp_at_move; [exact Hat'|].
  hbp_kept Hkeep ltac:(apply Hmem; [lia | apply (hbp_i_nw_R _ _ _ _ _ LAY); unfold POD_BUF_MAX; lia]). }
assert (Hpp3 : hsu_pp_at rsegs cx W3 mem3 (pc_image (PbCut 7 (ps ++ [(0, PInt 0)]) None))).
{ unfold hsu_pp_at. rewrite hbp_img7.
  unfold hsu_pp_at, pc_image in Hpp.
  assert (Lx : length (prop_bytes 7 (0, PInt 0)) = 16%nat) by reflexivity.
  eapply (hbp_pp_append (w_H W2) mem2 (w_H W3) mem3 (e_pp (x_e cx))); [| exact IB3 | exact IB4 | exact Hpp | | |].
  - rewrite Lx, Nat2Z.inj_add. unfold POD_BUF_MAX. lia.
  - change (prop_bytes 7 (0, PInt 0)) with (enc_pod hbp_i_ent). exact Renc.
  - rewrite Lx, Nat2Z.inj_add. change (Z.of_nat 16) with 16. exact Rlen.
  - intros y Hy Hx Hl. rewrite Lx in Hx. change (Z.of_nat 16) with 16 in Hx.
    apply Hmem; [unfold PP_SIZE in *; lia|].
    apply (hbp_i_nw_pp _ _ _ _ _ LAY); [lia | unfold POD_BUF_MAX; lia | exact Hy | exact Hx | exact Hl]. }
change (mkCfg (mkst regs3 (w64 HBP_LATCH) mem3 (seg_rom rsegs)) md3)
  with (cfg_at rsegs (bi_LATCH headamp_bld_B) regs3 mem3 md3).
apply (HL ly3 S3 W3 regs3 mem3 md3 7 np (ps ++ [(0, PInt 0)]) r ltac:(rewrite length_app, Hlen; cbn [length]; lia)).
split; [exact Hcore3|]. split; [exact Rfsh|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|].
split; [apply hbp_wf7; [exact Hwf | lia]|]. split; [exact Hsh|]. split; [exact Hnp|].
split; [rewrite length_app; cbn [length]; lia|]. split; [exact Hnp3|].
split; [rewrite length_app, Nat.add_1_r, hbp_loop7, <- Hpsl, <- Hr; reflexivity|].
unfold hsu_at_cx. hbp_list; first [hbp_from Hat3 | idtac].
- cbn [hd_at]. exact R23.
- cbn [hd_at]. exact R26.
- cbn [hd_at]. refine (eq_trans R5 _). rewrite length_app. cbn [length]. f_equal. lia.
- cbn [hd_at]. rewrite hbp_seen7. exact R13.
- cbn [hd_at]. exact R17.
- cbn [hd_at]. exact R28.
Qed.

End d.
End b.

Print Assumptions hbp_int7.
Print Assumptions hbp_piece_int7.

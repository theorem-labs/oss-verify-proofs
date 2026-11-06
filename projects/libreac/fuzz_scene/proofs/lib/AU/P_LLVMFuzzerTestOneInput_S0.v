(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* SEGMENT S0 of the asan-ubsan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput.  Proves
   `seg_S0_stmt SEGS B ameter_triv WK scene_geom_asan_ubsan` (lib/AU/P_LLVMFuzzerTestOneInput_seg.v:560): from the
   entry 0x828a4 to cut C1 0x82c28, the walk realizes whatever the rest of the walk realizes from C1, for the frame
   position the class-8 stack malloc picks.  Rule 24: one segment of the entry walk, not the function.

   Image: fuzz_scene.asan-ubsan, sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f; listing
   dis-LLVMF.asan-ubsan.txt (sha256 81fd8a77e9b7; internal record); offsets below are from 0x828a4 = BASE.
   The proof is split at the return of __asan_set_shadow_f8 (0x82a10, offset 0x16c); `s0_mid` is the state there.
     s0_head  0x828a4 .. 0x82a0c: the prologue and the 13 saves, the realignment `andi sp,sp,-0x20`, the UAR flag
              (1 by al_const: the real-stack arm is dead) and the shadow base, __asan_stack_malloc_8(9408) at 0x82918
              through J_StackSzPf.aj_stack_malloc_sz_at, the frame setup (P_check_step_frame.frame_setup at class 8),
              the frame header and the 28 inline shadow stores, __asan_set_shadow_f8(shF + 0x1c, 1113) at 0x82a0c
              through J_StackSzPf.aj_set_shadow_at.
     s0_tail  0x82a10 .. 0x82c28 (and the out-of-line block 0x8320c .. 0x83230): the 35 f3 stores, `bnez a1`
              (n >> 26 = 0 by the pre), the E header parse over the input (0 .. 5 bytes), the mac unpoison store
              0x82bbc and the 6-turn mac loop.  Twelve cases of n: n = 0 .. 10 pin s7 = n to a literal, n >= 11 keeps
              it an atom; each case runs four symbolic runs over the same fresh state: a plain run (the frame-shadow
              tail writable), a token run of the header (each input byte's shadow check an obligation discharged
              by AR's block law, obl_of_block), a plain run of the join 0x82b90 (the mac cell writable), and a token
              run of the loop (the mac object covered by its opened shadow).  The cut is built once (EXIT) from the
              final symbolic state of each case: registers, spill and frame chunks, and the bytes the runs did not
              write (frame_of, s0_keep_step).
   Section hypotheses are the instance file's (lib/AU/P_LLVMFuzzerTestOneInput.v Section h) by name: ML, TL, TLF,
   the class-8 stack-malloc and set_shadow_f8 contracts (SM8 at SIGMA SS___asan_stack_malloc_8 = 0x3f438, the value
   of StackMalloc8Tbl's PC_STACK_MALLOC_8; ASHF8), HSTK, HENTRY (A_LLVMF), and the segment-Section HWRLO / HWRHI of
   a Theorem Labs lane's ruling.  AR_laws and stack_malloc_progressP are the theorems AR_laws_ok and ml_stack_malloc_progress.
   Gate 6h: the sink head is the Section variable SK, passed explicitly; `llvmf_S0_scene` at the end is the theorem
   at scene's own head, musl's ofl_head 0x5f7190 of this image. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
(* gate 6o: the image-differing modules from lib.AU, everything the trunk's lib/Reusable holds from lib.Reusable *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import J_StackSz J_StackSzPf.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC1g YC81 YC45 SceneACjr ACj1 SceneACja.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx P_LLVMFuzzerTestOneInput_seg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC88.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The frame-shadow bytes [shadow_addr F, shadow_addr F + 0x475) at the return of __asan_set_shadow_f8 (0x82a10):
   the 28 inline stores 0x8298c-0x829fc give offsets 0 .. 0x1b, the call gives 0x1c .. 0x474. *)
Definition s0_sh (o : Z) : Z :=
if o <? 4 then 0xf1 else if o <? 9 then 0xf8 else if o <? 0xe then 0xf2 else if o <? 0xf then 0xf8
else if o <? 0x12 then 0xf2 else if o <? 0x17 then 0xf8 else if o <? 0x1c then 0xf2 else 0xf8.

(* ---- head lane helpers (s0_head): the entry state and the tactics of the walk 0x828a4 .. 0x82a10 ---- *)
(* The entry symbolic state: atoms 0..31 the entry registers, atom 32 the shadow base SB; the regions are the entry
   stack window [sp0 - 240, sp0) (the 224-byte frame `addi sp,sp,-0xe0` 0x828a4, and the realignment's 16 more), the
   shadow-base GOT word (object 1) with its cell (object 16), and the UAR flag's GOT word (object 0) with the flag
   cell (object 17), which holds 1 in every AR state (al_const). sp0 is only 16-aligned (atom 2, al2 = 4). *)
Definition s0h_extra : list word := [Z_to_bv 64 SB].
Definition s0h_regions0 : smem :=
[ stack_region 240; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 17); uar_cell_regionP (A_OBJ 17) ].
Definition s0h_atoms0 : list (nat * afact) := [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ].
Definition ss_s0h0 : sstate := mkSS 0 sr_atoms s0h_regions0 None (mkFacts s0h_atoms0 [] []).
(* The written-window heads of the walk's stack regions (atom 2 at sp0, atom 60 at sp1): the stack budget is the
   walk's variable `sw_stk WK`, so the bound comes from HSTK (the kit's awrFL head computes a literal STK). *)
Ltac s0h_awr_hd AG :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | cbn; lia | cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
  lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | cbn; lia | cbn; lia |] end
end.
(* The extent goals of the own frame and its shadow against the walk's regions, from one packed hypothesis BND
   (P_check_step_S0.v:46 cs_djtac, with this walk's sp1 bound). *)
Ltac s0h_djtac BND :=
repeat split; revert BND; clear; unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB; intros; lia.
(* One callee-saved word of the prologue, read back from a chunk of the entry stack region (atom 2): the shape of
   P_check_step_S0.v:217-231, over the Z-indexed save list `sc_saved_regs` of this walk's cut. *)
Ltac s0h_save HRs AG EE Usp :=
cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add nth sc_saved_regs];
lazymatch goal with
| |- rdword _ (?sp - 8 - 8 * ?jj) = Some (bv_unsigned (getr _ ?r)) =>
  let od := eval vm_compute in (- 8 - 8 * jj) in
  let rn := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
  replace (sp - 8 - 8 * jj) with (sp + od) by lia;
  apply rdword_of_val_mem; [| apply bv_unsigned_in_range];
  apply (slot_of_region _ _ _ _ _ _ _ _ od (SOff rn 0) _ HRs);
  [ rewrite (AG 2%nat) by lia; exact Usp
  | cbn [In]; repeat first [left; reflexivity | right]
  | cbn [sv_denot]; rewrite Z.add_0_r, (AG rn) by lia; rewrite (EE rn r) by reflexivity; rewrite Z_to_bv_bv_unsigned; reflexivity
  | apply bv_unsigned_in_range ]
end.
(* A callee-saved register kept by a runtime call (aregs_preserved), as the bv literal the walk uses
   (a Theorem Labs lane's AU S6 s6pres). *)
Ltac s0h_pres H z r name :=
pose proof (H z ltac:(unfold acallee_saved; lia)) as name;
replace (Z_to_bv 5 z) with r in name by (apply bv_eq; vm_compute; reflexivity).

(* ---- the tail's symbolic state at 0x82a10: every register an atom (0..31), the input bytes bs 0 .. bs 10 as
   atoms 32..42; the spill slots [s1 + 0x10, s1 + 0x40) (s1 = atom 9), the frame-shadow tail [shF + 0x475,
   shF + 0x498) and cell shF + 0xe (s3 = atom 19), the mac object [F + 0x70, F + 0x76) (s2 = atom 18) and the
   input bytes read [p, p + c) (s8 = atom 24). ---- *)
Definition s0_Rsp : YP09.region := YP09.mkRegion (Some 9%nat) 0x10 0x40 0x10 0x40 [].
Definition s0_RfsT : YP09.region := YP09.mkRegion (Some 19%nat) 0x475 0x498 0x475 0x498 [].
Definition s0_RfsE : YP09.region := YP09.mkRegion (Some 19%nat) 0xe 0xf 0 0 [].
Definition s0_Rmac : YP09.region := YP09.mkRegion (Some 18%nat) 0x70 0x76 0 0 [].
Definition s0_in_chunks (c : nat) : list YP09.chunk :=
map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (32 + j) 0))) (seq 0 c).
Definition s0_Rin (c : nat) : YP09.region := YP09.mkRegion (Some 24%nat) 0 (Z.of_nat c) 0 0 (s0_in_chunks c).
Definition s0_rs0 (c : nat) : smem :=
s0_Rsp :: s0_RfsT :: s0_RfsE :: s0_Rmac :: (if Nat.eqb c 0 then [] else [s0_Rin c]).
Definition s0_atoms0 (f23 : afact) : list (nat * afact) :=
(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5) :: (18%nat, HPTR 5) :: (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 2) ::
(23%nat, f23) :: (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: map (fun j => ((32 + j)%nat, mkAF 0 255 0)) (seq 0 11).
Definition s0_ss0 (c : nat) (f23 : afact) (FA : list (nat * afact)) (C : list acond) : sstate :=
mkSS 0x16c sr_atoms (s0_rs0 c) None (mkFacts (s0_atoms0 f23 ++ FA) C []).
(* `bnez a1` 0x82aa4 with a1 = n >> 26: the condition the run assumes on its not-taken edge *)
Definition s0_c26 : acond := mkAC BC_EQ (SAlu ALU_SRL (SOff 23 0) (SLit 26)) (SLit 0).
Lemma s0_c26_ok : forall E, 0 <= bv_unsigned (ew E 23) < 2 ^ 26 -> acond_ok E s0_c26.
Proof.
intros E H. unfold acond_ok, s0_c26. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, U_SAlu, U_SOff, !U_SLit. cbn [zalu_raw].
rewrite Z.add_0_r. unfold zcanon, M64. rewrite (Z.mod_small (bv_unsigned (ew E 23))) by lia.
change (26 mod 2 ^ 64) with 26. change (Z.land 26 63) with 26.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Definition s0_extra (bs : Z -> Z) : list word := map (fun j => Z_to_bv 64 (bs (Z.of_nat j))) (seq 0 11).
Definition s0_Bx : sv := SOff 26 0.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* gate 6h: the head's type is written fully qualified, so no other unit's YI16 twin can capture the short name *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head). #[local] Existing Instance SK.
Lemma s0_lit_byte : forall E z, 0 <= z < 2 ^ 64 -> bv_unsigned (sv_denot E (SLit z)) mod 2 ^ (8 * Z.of_N 1) = z mod 256.
Proof. intros E z Hz. change (bv_unsigned (sv_denot E (SLit z))) with (U E (SLit z)). rewrite U_SLit. unfold zcanon, M64. rewrite (Z.mod_small z (2 ^ 64)) by lia. reflexivity. Qed.
(* ---- byte arithmetic of the E parse, by exhaustion over the byte values (vm_compute) ---- *)
Lemma s0_brute1 : forall f g : Z -> Z,
forallb (fun b => Z.eqb (f (Z.of_nat b)) (g (Z.of_nat b))) (seq 0 256) = true -> forall v, 0 <= v < 256 -> f v = g v.
Proof.
intros f g H v Hv. rewrite forallb_forall in H. specialize (H (Z.to_nat v) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia. apply Z.eqb_eq. exact H.
Qed.
Lemma s0_brute2 : forall f g : Z -> Z -> Z,
forallb (fun a => forallb (fun b => Z.eqb (f (Z.of_nat a) (Z.of_nat b)) (g (Z.of_nat a) (Z.of_nat b))) (seq 0 256)) (seq 0 256) = true ->
forall u v, 0 <= u < 256 -> 0 <= v < 256 -> f u v = g u v.
Proof.
intros f g H u v Hu Hv. rewrite forallb_forall in H. specialize (H (Z.to_nat u) ltac:(apply in_seq; lia)).
rewrite forallb_forall in H. specialize (H (Z.to_nat v) ltac:(apply in_seq; lia)).
rewrite !Z2Nat.id in H by lia. apply Z.eqb_eq. exact H.
Qed.
(* s4 = srai(slli(b4, 56), 48) = sx16(256 * b4) (0x82ba8, 0x82bb4) *)
Lemma s0_U_s7v : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v < 256 ->
U E (SAlu ALU_SRA (SAlu ALU_SLL (SOff k 0) (SLit 56)) (SLit 48)) = sx16 (256 * v) mod 2 ^ 64.
Proof.
intros E k v Hk Hv. rewrite !U_SAlu, (U_atom E k v Hk ltac:(lia)), !U_SLit.
apply (s0_brute1 (fun v => zcanon (zalu_raw 63 64 ALU_SRA (zcanon (zalu_raw 63 64 ALU_SLL v (zcanon 56))) (zcanon 48)))
  (fun v => sx16 (256 * v) mod 2 ^ 64)); [vm_compute; reflexivity | exact Hv].
Qed.
(* s7 = srai(slli(b4, 56) | slli(b3, 48), 48) = sx16(b3 + 256 * b4) (0x82ba8-0x82bc0) *)
Lemma s0_U_step : forall E k3 k4 b3 b4, ew E k3 = Z_to_bv 64 b3 -> ew E k4 = Z_to_bv 64 b4 -> 0 <= b3 < 256 -> 0 <= b4 < 256 ->
U E (SAlu ALU_SRA (SAlu ALU_OR (SAlu ALU_SLL (SOff k4 0) (SLit 56)) (SAlu ALU_SLL (SOff k3 0) (SLit 48))) (SLit 48))
= sx16 (b3 + 256 * b4) mod 2 ^ 64.
Proof.
intros E k3 k4 b3 b4 H3 H4 R3 R4. rewrite !U_SAlu, (U_atom E k3 b3 H3 ltac:(lia)), (U_atom E k4 b4 H4 ltac:(lia)), !U_SLit.
apply (s0_brute2 (fun b3 b4 => zcanon (zalu_raw 63 64 ALU_SRA (zcanon (zalu_raw 63 64 ALU_OR
    (zcanon (zalu_raw 63 64 ALU_SLL b4 (zcanon 56))) (zcanon (zalu_raw 63 64 ALU_SLL b3 (zcanon 48))))) (zcanon 48)))
  (fun b3 b4 => sx16 (b3 + 256 * b4) mod 2 ^ 64)); [vm_compute; reflexivity | exact R3 | exact R4].
Qed.
(* the n = 4 arm: a2 = 0 (0x82b64), so s7 = sx16(b3) *)
Lemma s0_U_step4 : forall E k3 b3, ew E k3 = Z_to_bv 64 b3 -> 0 <= b3 < 256 ->
U E (SAlu ALU_SRA (SAlu ALU_OR (SLit 0) (SAlu ALU_SLL (SOff k3 0) (SLit 48))) (SLit 48)) = sx16 (b3 + 256 * 0) mod 2 ^ 64.
Proof.
intros E k3 b3 H3 R3. rewrite !U_SAlu, (U_atom E k3 b3 H3 ltac:(lia)), !U_SLit.
apply (s0_brute1 (fun b3 => zcanon (zalu_raw 63 64 ALU_SRA (zcanon (zalu_raw 63 64 ALU_OR (zcanon 0)
    (zcanon (zalu_raw 63 64 ALU_SLL b3 (zcanon 48))))) (zcanon 48)))
  (fun b3 => sx16 (b3 + 256 * 0) mod 2 ^ 64)); [vm_compute; reflexivity | exact R3].
Qed.
(* s8 = (b2 << 8) | b1 (0x82b28-0x82b2c, 0x82bd0) *)
Lemma s0_U_u16 : forall E k1 k2 b1 b2, ew E k1 = Z_to_bv 64 b1 -> ew E k2 = Z_to_bv 64 b2 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
U E (SAlu ALU_ADD (SAlu ALU_OR (SAlu ALU_SLL (SOff k2 0) (SLit 8)) (SOff k1 0)) (SLit 0)) = b1 + 256 * b2.
Proof.
intros E k1 k2 b1 b2 H1 H2 R1 R2. rewrite !U_SAlu, (U_atom E k1 b1 H1 ltac:(lia)), (U_atom E k2 b2 H2 ltac:(lia)), !U_SLit.
apply (s0_brute2 (fun b1 b2 => zcanon (zalu_raw 63 64 ALU_ADD (zcanon (zalu_raw 63 64 ALU_OR
    (zcanon (zalu_raw 63 64 ALU_SLL b2 (zcanon 8))) b1)) (zcanon 0)))
  (fun b1 b2 => b1 + 256 * b2)); [vm_compute; reflexivity | exact R1 | exact R2].
Qed.
Lemma s0_rdword_kept : forall (rd rd' : Z -> option Z) a,
(forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (rewrite <- (Z.add_0_r a); apply H; lia).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Section f.
#[local] Notation PI := (@PI_scene rc).
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).

(* One byte of a region chunk, read through the ASan reader view: the port of cgif_file_fuzzer lib/YCew.v:18-30
   (byte_of_chunk_ok) and :70-80 (byte_of_region), image-free, with aview_of_val_mem1 (AU/Prog/SceneFrame.v:235)
   in front.  The 28 inline shadow stores leave one-byte chunks whose value is a NEGATIVE literal (`addi a0,zero,-0xf`),
   so the byte read is its low eight bits, not the literal. *)
Lemma s0h_byte_of_chunk_ok : forall E (m : word -> option byte) base off e V,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 1 e)) ->
sv_denot E e = Z_to_bv 64 V -> 0 <= V < 2 ^ 64 ->
val_mem SEGS m (base + off) 1 (V mod 256).
Proof.
intros E m base off e V H He HV k Hk. assert (k = 0%nat) as -> by lia.
destruct (H 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2.
rewrite He in Hb1. unfold YP09.byte_of_word in Hb1. rewrite Z_to_bv_unsigned in Hb1.
unfold bv_wrap, bv_modulus in Hb1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hb1. rewrite Z.mod_small in Hb1 by lia.
replace (8 * 0) with 0 in Hb1 by lia. rewrite Z.shiftr_0_r in Hb1. injection Hb1 as <-.
change (Z.of_nat 0) with 0. rewrite Hb2. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma s0h_byte_of_region : forall E (m : word -> option byte) n b cs lo hi wlo whi od e,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs ->
val_mem SEGS m (b + od) 1 (bv_unsigned (sv_denot E e) mod 256).
Proof.
intros E m n b cs lo hi wlo whi od e (_ & _ & _ & Hcs) Hn Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
apply (s0h_byte_of_chunk_ok E m b od e (bv_unsigned (sv_denot E e)) Hck).
- rewrite Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as HR. change (bv_modulus 64) with (2 ^ 64) in HR. exact HR.
Qed.
Lemma s0h_aview_byte : forall E (H : word -> bool) (m : word -> option byte) n b cs lo hi wlo whi od e v,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs ->
bv_unsigned (sv_denot E e) mod 256 = v -> 0 <= v < 256 ->
aview SEGS H m (b + od) = Some v.
Proof.
intros E H m n b cs lo hi wlo whi od e v Hr Hn Hin Hv Hrng.
apply (aview_of_val_mem1 SEGS H m); [| exact Hrng].
rewrite <- Hv. exact (s0h_byte_of_region E (mrestrict H m) n b cs lo hi wlo whi od e Hr Hn Hin).
Qed.


(* the bytes the tail writes: the four spill slots, the mac cell, the frame-shadow tail and the mac object *)
Definition s0_inW (sp1 F a : Z) : Prop :=
(sp1 + 0x10 <= a < sp1 + 0x40) \/ (shadow_addr F + 0xe <= a < shadow_addr F + 0xf) \/
(shadow_addr F + 0x475 <= a < shadow_addr F + 0x498) \/ (F + 0x70 <= a < F + 0x76).
Lemma s0_keep_step : forall E rs H (m0 m m' : word -> option byte) (P : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, 0 <= a < 2 ^ 64 -> in_wrange E rs a -> P a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m a = aview SEGS H m0 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m0 a).
Proof.
intros E rs H m0 m m' P HF Hw Hk a Ha Hn. rewrite <- (Hk a Ha Hn).
apply (aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia. intros Hin. exact (Hn (Hw a Ha Hin)).
Qed.

(* The state at 0x82a10 (offset 0x16c), the return of __asan_set_shadow_f8: the interface between the head of the
   walk (entry .. the set_shadow call) and its tail (0x82a10 .. C1). *)
Definition s0_mid (B : asyms) (WK : swalk) (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p n fpos : Z)
(S2 : astate) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
ajournal (SK := SK) SEGS B (sw_stk WK) (spZ regs) [] ly S W mem md [(8, fpos)] ly S2 W mem2 md2 0 /\
frames S2 = [(8, fpos)] /\
ablocks B ly S2 = ablocks B ly S /\ blocks_bytes S2 = blocks_bytes S /\
getr regs2 2 = w64 (32 * ((spZ regs - 224) / 32)) /\
getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
getr regs2 8 = w64 (spZ regs) /\
getr regs2 9 = w64 (32 * ((spZ regs - 224) / 32)) /\
getr regs2 18 = w64 (frame_addr ly 8 fpos) /\
getr regs2 19 = w64 (shadow_addr (frame_addr ly 8 fpos)) /\
getr regs2 20 = w64 (frame_addr ly 8 fpos) /\
getr regs2 21 = w64 (shadow_addr (frame_addr ly 8 fpos) + 0x1c) /\
getr regs2 23 = w64 n /\ getr regs2 24 = w64 p /\
getr regs2 26 = w64 SHADOW_OFF /\
(forall j, 0 <= j < 13 ->
rdword (aview SEGS (w_H W) mem2) (spZ regs - 8 - 8 * j)
= Some (bv_unsigned (getr regs (nth (Z.to_nat j) sc_saved_regs 0%bv)))) /\
rdword (aview SEGS (w_H W) mem2) (frame_addr ly 8 fpos + 16384 - 8) = Some (flag_addr ly 8 fpos) /\
(forall o, 0 <= o < 0x475 -> aview SEGS (w_H W) mem2 (shadow_addr (frame_addr ly 8 fpos) + o) = Some (s0_sh o)).

Section h.
Variable B : asyms.
Variable WK : swalk.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis ML : model_laws (as_universe B).
Let SMP : stack_malloc_progressP B := ml_stack_malloc_progress _ ML.
Hypothesis TL : PALib (L := scene_listing) (PI := PI) B.
Hypothesis TLF : PALibF (L := scene_listing) (PI := PI) B.
Hypothesis SM8 : astack_malloc_sz_realizes SEGS B (SIGMA SS___asan_stack_malloc_8) 8.
Hypothesis ASHF8 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8.
Hypothesis HSTK : 240 + ASTACK <= sw_stk WK.
Hypothesis HENTRY : sw_entry WK = BASE + AF_LLVMFuzzerTestOneInput.
(* A Theorem Labs lane's ruling: each segment's own Section binds the cut's read-only window to PI_scene's relro window
   (the same two lines in every segment file); the top discharges them by eq_refl. *)
Hypothesis HWRLO : sw_rlo WK = pa_relro_lo.
Hypothesis HWRHI : sw_rhi WK = pa_relro_hi.
Let RUNTOP := SRr_run_to_pi_AJ (SK := SK) (L := scene_listing) (PL := PL_scene) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (SK := SK) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).

(* The entry state at 0x828a4 (sp0 16-aligned): the port of check_step's cs_entry (P_check_step_S0_aux.v:57) with
   the 240-byte stack window and the stack budget sw_stk WK. *)
Lemma s0h_entry : forall ly S W (regs : bvmap 5 word) mem md,
afn_pre SEGS B (sw_stk WK) ly S W regs mem md [] ->
st_ok_pi SEGS VAL (Eimg (Ereg regs s0h_extra)) ss_s0h0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : 16624 <= sw_stk WK) by (pose proof HSTK as H; change ASTACK with 16384 in H; lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kguar, Kuar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs s0h_extra)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs s0h_extra 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E257 : ew E (A_OBJ 16) = Z_to_bv 64 (VAL (A_OBJ 16))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E258 : ew E (A_OBJ 17) = Z_to_bv 64 (VAL (A_OBJ 17))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 16 ltac:(lia)) as Hob16. pose proof (pa_obj_img 17 ltac:(lia)) as Hob17.
pose proof (palf_sep B TLF) as Hsep. rewrite (pal_uar_cell B TL) in Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_s0h0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s0h_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 16) 0) (VAL (A_OBJ 16)));
[cbn [sv_denot]; rewrite E257, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 16)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) E257) by (pose proof (pa_val_range (A_OBJ 16)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 16)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 17) 0) (VAL (A_OBJ 17)));
[cbn [sv_denot]; rewrite E258, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 17)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB (A_OBJ 17) (VAL (A_OBJ 17)) E258) by (pose proof (pa_val_range (A_OBJ 17)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 17)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold s0h_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) E257) by (pose proof (pa_val_range (A_OBJ 16)); lia).
rewrite (VB (A_OBJ 17) (VAL (A_OBJ 17)) E258) by (pose proof (pa_val_range (A_OBJ 17)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 FFS Hstk0 Hob0 Hob1 Hob16 Hob17 Hsep. clear. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : _ + 8 <= _ \/ _ |- _ => clear H | H : _ + 4 <= _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok s0h_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 FFS Hstk0 Hal16. clear. unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

Lemma s0_head : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md p n T (POST : world SEGS -> config -> Prop),
sc_base0 SEGS B ameter_triv WK ly S W regs mem md p n T ->
(forall fpos S2 regs2 mem2 md2, s0_mid B WK ly S W regs mem md p n fpos S2 regs2 mem2 md2 ->
SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x16c)) mem2 (seg_rom SEGS)) md2) POST) ->
SRr SEGS W (cfg_at SEGS (sw_entry WK) regs mem md) POST.
Proof.
intros ly S W regs mem md p n T POST Hb HKc.
pose proof Hb as (HPRE & Hra & Ha0 & Ha1 & Hpn & Hfrs0 & Hev0 & Hlive0 & HROD & HSNK0 & HFD0 & HSORT0 & _).
pose proof (SRr_run_to_pi_AJ (SK := SK) B LAWS) as RUNTOPh. pose proof (SRr_run_pi_AJ (SK := SK) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (SK := SK) B LAWS) as RUNC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_scene)) as HBLO.
pose proof (s0h_entry ly S W regs mem md HPRE) as HS.
pose proof (ajournal_init SEGS B (sw_stk WK) [] ly S W regs mem md [] HPRE) as HJ.
pose proof HPRE as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : 16624 <= sw_stk WK) by (pose proof HSTK as H; change ASTACK with 16384 in H; lia).
assert (Hes : ESTACK = 4096) by reflexivity.
remember (Eimg (Ereg regs s0h_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact Ha0).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Ha1).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs s0h_extra 0)).
img_factsF E. img_hull_factsF.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r) by (intros k r Hk; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hk).
clear HE.
unfold cfg_at. rewrite HENTRY. unfold AF_LLVMFuzzerTestOneInput, w64.
assert (AG : forall k, (k < 33)%nat -> ew E k = ew E k) by (intros; reflexivity).
assert (EFA0 : forall c q, frame_addr ly c q = frame_addr ly c q) by reflexivity.
(* ---- run 1: 0x828a4 .. 0x828e8, the prologue through the realignment `andi sp,sp,-0x20` ---- *)
paj_run_to_shc RUNTOPh HS HJ 0x44.
{ awrFL_with ltac:(idtac; s0h_awr_hd AG) AG 0 0 EFA0. }
(* ---- the realignment: sp1 = 32 * ((sp0 - 224) / 32), a fresh atom 60 ---- *)
set (sp1 := 32 * ((spZ regs - 224) / 32)).
destruct (sp1_facts (spZ regs - 224) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity))
as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 240 <= sp1 <= spZ regs - 224) by lia. clear Hsp1r.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 Ev 2 (spZ regs) (-224) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(lia) ltac:(lia) ltac:(lia)) R2 end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 60%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E60 : ew Ev 60 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
(* trim the sp0 stack region to the 13 saves and add the sp1 region [sp1 + 0x70, sp1 + 0x78) *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0x70 0x78 0x70 0x78 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E60, unsigned_lit_small by lia; evalE AG;
repeat split; lia)) as HS3; clear HJpres;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* ---- run 2: 0x828e8 .. the call `jal __asan_stack_malloc_8` at 0x82918 (the UAR flag reads 1, so the
   `beqz a2` at 0x8290c is not taken and the real-stack arm is not entered here) ---- *)
clear HF HFr HG.
paj_run_shc RUNP RUNC HS HJ.
{ awrFL_with ltac:(idtac; s0h_awr_hd AG) AG 0 0 EFA0. }
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
pmkst HS.
(* ---- the call __asan_stack_malloc_8(9408) at 0x82918, ra = BASE + 0x78 ---- *)
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_sz_at (SK := SK) SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP
(SIGMA SS___asan_stack_malloc_8) 8 SM8 ltac:(lia) W (ms_regs msX) (ms_mem msX)
(sw_stk WK) (spZ regs) [] ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ 9408 HJ) end.
- unfold spZ at 1. rewrite R2. evalE AG.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
- lia.
- rewrite Hes. lia.
- rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite R10. unfold w64. f_equal.
- change (fs_frame_bytes 8) with 16384. lia.
- reflexivity.
- rewrite Hfrs0. cbn [count_cid].
  let v := eval vm_compute in (fs_frames 8) in change (fs_frames 8) with v. lia. }
cbv beta. clear R2 R3 R4 R1 R10 HJ.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & HaF & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK).
(* ---- the fake frame F and its shadow: re-seat the kept regions at the return 0x8291c ---- *)
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (8, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 8 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 8 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 8) with 16384 in *.
set (F := frame_addr ly 8 fpos) in *. set (FL := flag_addr ly 8 fpos) in *.
rewrite Hes in HK.
replace (spZ regs + (sp1 - spZ regs) - 4096) with (sp1 - 4096) in HK by lia.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by lia.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; keptFL HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)).
(* ---- the frame region (F, 16384 bytes, the flag word at F + 16376) and the frame-shadow region
   (2048 bytes, write window [0, 0x1c)): P_check_step_frame.frame_setup at class 8, n = 9408 ---- *)
assert (FS : forall segs val B0 cid nn, frame_setup_stmt segs val B0 cid nn)
by (first [exact (frame_setup SK) | exact frame_setup]).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite HaF in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E32b : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
clear HEv.
destruct (al_flag _ _ LAWS _ _ _ _ _ 8 fpos HAR2 Hfin2) as (_ & _ & HFLapp & HFLc). fold FL in HFLapp, HFLc.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
pose proof (conj Hslo (conj Hshi (conj H47 (conj Hceil (conj Hstk0 (conj C1 (conj HF4096 (conj HFceil (conj HFhigh
(conj HFhigh_img (conj HFq (conj HF8 (conj HF8lo (conj HF8hi (conj Hob241 (conj Hob242 (conj Hob257 (conj Hob258
(conj Hsp1 (conj HFLapp FFS)))))))))))))))))))) as BND.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict _ ?msv) =>
assert (DJ1 : all_disjoint Ev (fframe_region 516 528 8 []) (ss_mem ssv));
[ let rs2 := eval vm_compute in (ss_mem ssv) in change (all_disjoint Ev (fframe_region 516 528 8 []) rs2);
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 8) with 16384; rewrite RF; evalE AG; s0h_djtac BND | ];
assert (DJ2 : all_disjoint Ev (fshadow_region 529 8 0 28 (fzero_chunks 0)) (fframe_region 516 528 8 [] :: ss_mem ssv));
[ let rs2 := eval vm_compute in (ss_mem ssv) in change (all_disjoint Ev (fshadow_region 529 8 0 28 (fzero_chunks 0)) (fframe_region 516 528 8 [] :: rs2));
cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 8 / 8) with 2048; change (fs_frame_bytes 8) with 16384; rewrite RF, E529; evalE AG; s0h_djtac BND | ];
pose proof (FS SEGS VAL B 8 9408 LAWS W Ev ssv msv md2 ly S2 fpos 516%nat 528%nat 529%nat 32%nat 0%nat 0 28 HS HAR2 Hfin2
RF E528 ltac:(rewrite E32b; reflexivity) ltac:(rewrite E529; reflexivity) Hflag ltac:(change (fs_frame_bytes 8) with 16384; lia) eq_refl Hz
ltac:(cbn; lia) ltac:(lia) ltac:(change (fs_frame_bytes 8 / 8) with 2048; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
DJ1 DJ2) as HS3 end.
clear HS DJ1 DJ2. rename HS3 into HS. unfold frame_ss, fzero_chunks in HS. norm_ss HS.
(* ---- run 3: 0x8291c .. the call `jal __asan_set_shadow_f8` at 0x82a0c (the `bnez s4` at 0x8292c is TAKEN:
   4096 <= F by the frame atom's fact, so the real-stack arm 0x82930-0x82950 is dead) ---- *)
clear HF HFr HG.
paj_run_shc RUNP RUNC HS HJ2.
{ awrFL_with ltac:(idtac; s0h_awr_hd AG) AG fpos F EFA0. }
(* ---- the memory the walk has built at the call: the 13 saves, the frame's flag word, the 28 shadow bytes ---- *)
assert (ESH : shadow_addr F = SB + F / 8) by reflexivity.
assert (HSV : forall j, 0 <= j < 13 ->
rdword (aview SEGS (w_H W) (ms_mem ms1)) (spZ regs - 8 - 8 * j)
= Some (bv_unsigned (getr regs (nth (Z.to_nat j) sc_saved_regs 0%bv)))).
{ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 3 _ HS eq_refl) as HRs end.
  cbn [ms_mem restrict] in HRs.
  intros j Hj.
  assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12) by lia.
  repeat (destruct Hc as [-> | Hc]); try subst j; s0h_save HRs AG EE Usp. }
assert (HFLW : rdword (aview SEGS (w_H W) (ms_mem ms1)) (F + 16384 - 8) = Some FL).
{ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 1 _ HS eq_refl) as HRf end.
  cbn [ms_mem restrict] in HRf.
  pose proof (field_of_region _ _ _ F _ _ _ _ _ 16376 8%N (SOff 528 0) FL HRf) as VF.
  specialize (VF ltac:(rewrite RF; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
    ltac:(cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(change (Z.of_N 8) with 8; lia)).
  replace (F + 16384 - 8) with (F + 16376) by lia.
  apply (rdword_of_val_mem SEGS); [exact VF | lia]. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (U529 : bv_unsigned (ew Ex 529) = SB + F / 8) by (rewrite E529; apply unsigned_lit_small; unfold SB; lia) end.
assert (HSHB : forall o, 0 <= o < 28 -> aview SEGS (w_H W) (ms_mem ms1) (SB + F / 8 + o) = Some (s0_sh o)).
{ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 0 _ HS eq_refl) as HRsh end.
  cbn [ms_mem restrict] in HRsh.
  intros o Ho.
  assert (Hc : o = 0 \/ o = 1 \/ o = 2 \/ o = 3 \/ o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8 \/ o = 9 \/ o = 10
  \/ o = 11 \/ o = 12 \/ o = 13 \/ o = 14 \/ o = 15 \/ o = 16 \/ o = 17 \/ o = 18 \/ o = 19 \/ o = 20 \/ o = 21
  \/ o = 22 \/ o = 23 \/ o = 24 \/ o = 25 \/ o = 26 \/ o = 27) by lia.
  repeat (destruct Hc as [-> | Hc]); try subst o;
  (eapply (s0h_aview_byte _ _ _ 529%nat _ _ _ _ _ _ _ _ _ HRsh U529);
   [ cbn [In]; repeat first [left; reflexivity | right]
   | vm_compute; reflexivity
   | unfold s0_sh; cbn; lia ]). }
(* ---- the call __asan_set_shadow_f8(shadow_addr F + 0x1c, 1113) at 0x82a0c, ra = BASE + 0x16c ---- *)
prreg HS (1%bv : bv 5) R1b. prreg HS (2%bv : bv 5) R2b. prreg HS (3%bv : bv 5) R3b. prreg HS (4%bv : bv 5) R4b.
prreg HS (10%bv : bv 5) RQ. prreg HS (11%bv : bv 5) RN.
prreg HS (8%bv : bv 5) R8b. prreg HS (9%bv : bv 5) R9b. prreg HS (18%bv : bv 5) R18b. prreg HS (19%bv : bv 5) R19b.
prreg HS (20%bv : bv 5) R20b. prreg HS (21%bv : bv 5) R21b. prreg HS (23%bv : bv 5) R23b. prreg HS (24%bv : bv 5) R24b.
prreg HS (26%bv : bv 5) R26b.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_set_shadow_at (SK := SK) SEGS B LAWS pa_segs_low
(SIGMA SS___asan_set_shadow_f8) 0xf8 ASHF8 W (ms_regs msX) (ms_mem msX)
(sw_stk WK) (spZ regs) [] ly S W mem md [(8, fpos)] ly S2 _ 0 8 fpos (SB + F / 8 + 28) 1113
(sp1 - spZ regs) (Z_to_bv 64 (BASE + 364)) HJ2) end.
- left; reflexivity.
- rewrite RQ, E529, unsigned_lit_small by (unfold SB; lia). unfold w64. reflexivity.
- rewrite RN. unfold w64. f_equal.
- lia.
- fold F. rewrite ESH. lia.
- fold F. rewrite ESH. change (fs_frame_bytes 8 / 8) with 2048. lia.
- unfold spZ at 1. rewrite R2b. evalE AG.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
- lia.
- rewrite Hes. lia.
- rewrite R3b. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite R4b. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R1b.
- apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HFILL & HKEEP & HPRES3).
(* ---- the state at 0x82a10 is s0_mid ---- *)
apply (HKc fpos S2 regs3 mem3 md3).
s0h_pres HP3 2 ((2%bv) : bv 5) P2. s0h_pres HP3 3 ((3%bv) : bv 5) P3. s0h_pres HP3 4 ((4%bv) : bv 5) P4.
s0h_pres HP3 8 ((8%bv) : bv 5) P8. s0h_pres HP3 9 ((9%bv) : bv 5) P9. s0h_pres HP3 18 ((18%bv) : bv 5) P18.
s0h_pres HP3 19 ((19%bv) : bv 5) P19. s0h_pres HP3 20 ((20%bv) : bv 5) P20. s0h_pres HP3 21 ((21%bv) : bv 5) P21.
s0h_pres HP3 23 ((23%bv) : bv 5) P23. s0h_pres HP3 24 ((24%bv) : bv 5) P24. s0h_pres HP3 26 ((26%bv) : bv 5) P26.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFhigh.
unfold s0_mid. fold sp1 F FL.
split; [exact HJ3|].
split; [rewrite Hfrs2, Hfrs0; reflexivity|].
split; [exact Eab|].
split; [exact Hbb2|].
split; [rewrite P2, R2b, E60; reflexivity|].
split; [rewrite P3, R3b, (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp|].
split; [rewrite P4, R4b, (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp|].
split; [rewrite P8, R8b, (AG 2%nat) by lia; rewrite E2; unfold w64, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite P9, R9b, E60; reflexivity|].
split; [rewrite P18, R18b, RF; reflexivity|].
split; [rewrite P19, R19b, E529; unfold w64; rewrite ESH; reflexivity|].
split; [rewrite P20, R20b, RF; reflexivity|].
split; [rewrite P21, R21b, E529, unsigned_lit_small by (unfold SB; lia); unfold w64; rewrite ESH; reflexivity|].
split; [rewrite P23, R23b, (AG 11%nat) by lia; exact E11|].
split; [rewrite P24, R24b, (AG 10%nat) by lia; exact E10|].
split; [rewrite P26, R26b, (AG 32%nat) by lia; rewrite E32; reflexivity|].
split.
{ (* the 13 saves: below sp0, far above the shadow band the call fills *)
  intros j Hj. rewrite (rdword_ext (aview SEGS (w_H W) (ms_mem ms1)) _ (spZ regs - 8 - 8 * j)).
  - exact (HSV j Hj).
  - intros k Hk. apply HKEEP; unfold SB; lia. }
split.
{ (* the flag word at F + 16376: application memory, outside the shadow band *)
  rewrite (rdword_ext (aview SEGS (w_H W) (ms_mem ms1)) _ (F + 16384 - 8)).
  - exact HFLW.
  - intros k Hk. apply HKEEP; unfold SB; lia. }
(* the frame-shadow bytes: [0, 0x1c) from the 28 inline stores, [0x1c, 0x475) from __asan_set_shadow_f8 *)
intros o Ho. rewrite ESH.
destruct (Z_lt_ge_dec o 28) as [Hlt | Hge].
- rewrite HKEEP by (unfold SB; lia). exact (HSHB o ltac:(lia)).
- replace (SB + F / 8 + o) with (SB + F / 8 + 28 + (o - 28)) by lia.
  rewrite (HFILL (o - 28) ltac:(lia)). f_equal. unfold s0_sh.
  repeat (rewrite (proj2 (Z.ltb_ge o _)) by lia). reflexivity.
Qed.

(* write permission of the tail's regions: the spill slots are in the entry's stack window, the frame-shadow cells
   and the mac object are in the own fake frame (in_frames, own = [(8, fpos)]). *)
Ltac s0_awr sp0 sp1 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp fp b0 bc lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]
  | lazymatch goal with U9 : bv_unsigned (ew _ 9) = sp1 |- _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
    [reflexivity | cbn [ew ewset Nat.eqb]; rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | ] end
  | lazymatch goal with U19 : bv_unsigned (ew _ 19) = _ |- _ =>
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat); [reflexivity | cbn [ew ewset Nat.eqb]; exact U19 | | ];
    [ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; eexists; eexists; split; [left; reflexivity|]; right;
      unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 8 / 8) with 2048;
      repeat match goal with F := frame_addr _ _ _ |- _ => fold F end; unfold shadow_addr; lia | ] end
  | lazymatch goal with U18 : bv_unsigned (ew _ 18) = _ |- _ =>
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat); [reflexivity | cbn [ew ewset Nat.eqb]; exact U18 | | ];
    [ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; eexists; eexists; split; [left; reflexivity|]; left;
      unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 8) with 16384;
      repeat match goal with F := frame_addr _ _ _ |- _ => fold F end; lia | ] end ].
(* set the write window of the i-th region of the symbolic state to [wlo, whi) (tac: the new window is writable) *)
Ltac s0_rewin HS i wlo whi tac :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth i (ss_mem ssx) s0_Rsp) in
    let HS3 := fresh "HS3" in
    pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r wlo whi) HS ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity)
      (region_ok_rewindow _ Ex _ r wlo whi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(tac)))
      as HS3;
    clear HS; rename HS3 into HS; norm_ss HS
  end.
(* a shadow-check obligation of a token run: the byte p + c of the input block is addressable (AR's block law) *)
Ltac s0_obl HJx p n E24 E26 Hpin2 :=
  unfold s0_Bx;
  lazymatch goal with |- range_addressable _ (U ?Ex (SOff 26 0)) (U _ (SOff 24 ?c)) ?len =>
    rewrite (U_atom_off Ex 24 p c);
    [ | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24 | lia | lia];
    eapply (obl_of_block SEGS _ (AR_laws_ok SEGS _) _ _ _ _ _ Ex (SOff 26 0) _ len p n (proj1 HJx) Hpin2);
    [ rewrite (U_atom Ex 26 SB);
      [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E26 | unfold SB; lia]
    | lia | lia ]
  end.
(* the new write window of a frame-shadow region / of the mac region is present (AR's frame law at the run's state) *)
Ltac s0_fswin HJ Hfin2 U19 :=
  let o := fresh "o" in let Ho := fresh "Ho" in let HSP := fresh "HSP" in
  intros o Ho; cbn [YP09.r_base base_val ms_mem restrict ew ewset Nat.eqb]; rewrite U19; apply (apresent_writable SEGS);
  destruct (al_frames _ _ (AR_laws_ok SEGS _) _ _ _ _ _ 8 _ (proj1 HJ) Hfin2) as (_ & _ & _ & HSP);
  repeat match goal with F := frame_addr _ _ _ |- _ => fold F in HSP end;
  lazymatch goal with |- context [SHADOW_OFF + ?q / 8 + o] =>
    replace (SHADOW_OFF + q / 8 + o) with (shadow_addr q + o) by (unfold shadow_addr; lia) end;
  apply (proj1 (HSP o ltac:(change (fs_frame_bytes 8 / 8) with 2048; lia))).
Ltac s0_macwin HJ Hfin2 U18 :=
  let o := fresh "o" in let Ho := fresh "Ho" in let HFP := fresh "HFP" in
  intros o Ho; cbn [YP09.r_base base_val ms_mem restrict ew ewset Nat.eqb]; rewrite U18; apply (apresent_writable SEGS);
  destruct (al_frames _ _ (AR_laws_ok SEGS _) _ _ _ _ _ 8 _ (proj1 HJ) Hfin2) as (_ & _ & HFP & _);
  repeat match goal with F := frame_addr _ _ _ |- _ => fold F in HFP end;
  lazymatch goal with |- apresent _ _ ?a => apply (proj1 (HFP a ltac:(change (fs_frame_bytes 8) with 16384; lia))) end.
(* the value of the chunk at offset od of the i-th region, as a val_mem fact V *)
Ltac s0_fld HS i od V :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth i (ss_mem ssx) s0_Rsp) in
    let HR := fresh "HR" in
    pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HR;
    lazymatch r with YP09.mkRegion (Some ?k) ?lo ?hi ?wlo ?whi ?cs =>
      lazymatch eval vm_compute in (find (fun c => Z.eqb (YP09.c_off c) od) cs) with
      | Some (YP09.mkChunk _ (CVal ?w ?e)) =>
        pose proof (YC4b.field_of_region_any Ex _ k _ cs lo hi wlo whi od w e HR eq_refl
          ltac:(repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V
      end end;
    clear HR; cbn [ms_mem restrict ew ewset Nat.eqb N.to_nat Pos.to_nat] in V;
    rewrite ?s0_lit_byte in V by lia
  end.
(* pin s7 = n to the literal k of the case *)
Ltac s0_pin HS k Hk :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_pi_pin_reg' Ex ssx msx (23%bv : bv 5) k HS
      ltac:(cbn [ms_regs restrict mkst]; lazymatch goal with R23 : getr _ 23 = w64 _ |- _ => rewrite R23, Hk; reflexivity end)
      eq_refl) as HS3;
    clear HS; rename HS3 into HS; norm_ss HS
  end.
(* the shadow table of the loop: the mac object [F + 0x70, F + 0x76), addressable once its cell holds 6 *)
Ltac s0_shok_mac V6 E26 ER R18 HF8x HFapp :=
  unfold sh_ok; apply Forall_cons; [|apply Forall_nil];
  lazymatch goal with |- shent_ok _ _ ?Ex (mrestrict _ ?mm) _ =>
  lazymatch type of R18 with getr _ _ = w64 ?F =>
    apply (shent_ok_of_range SEGS _ mm Ex s0_Bx 18 (F + 0x70) 6 F 0x70 0x76);
    [ apply range_addressable_partial; [| | lia];
      [ unfold shadow_of_addr; replace (F + 112) with ((F / 8 + 14) * 8) by lia; rewrite Z.div_mul by lia;
        apply (aview_of_val_mem1 SEGS); [replace (SHADOW_OFF + (F / 8 + 14)) with (SHADOW_OFF + F / 8 + 14) by lia; exact V6 | lia]
      | replace (F + 112) with ((F / 8 + 14) * 8) by lia; apply Z_mod_mult ]
    | unfold s0_Bx; rewrite (U_atom _ 26 SB); [unfold SB, SHADOW_OFF; reflexivity | cbn [ew ewset Nat.eqb]; exact E26 | unfold SB; lia]
    | rewrite (U_atom _ 18 F); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite (ER 18%nat 18%bv eq_refl), R18; reflexivity | lia]
    | lia | lia
    | intros x Hx; unfold SHADOW_OFF; lia ] end end.
Ltac s0_Ueq bs BS0 BSR e :=
  let EBk j := (cbn [ew ewset Nat.eqb]; lazymatch goal with EB : forall j, (j < 11)%nat -> ew _ (32 + j) = _ |- _ =>
                  exact (EB j ltac:(lia)) end) in
  lazymatch goal with |- U ?Ex _ = _ =>
  lazymatch e with
  | SAlu ALU_SRA (SAlu ALU_SLL (SOff 36 0) (SLit 56)) (SLit 48) =>
    rewrite (s0_U_s7v Ex 36 (bs (Z.of_nat 4)) ltac:(EBk 4%nat) (BSR _)); unfold sc_s7v; reflexivity
  | SAlu ALU_SRA (SAlu ALU_OR (SAlu ALU_SLL (SOff 36 0) (SLit 56)) (SAlu ALU_SLL (SOff 35 0) (SLit 48))) (SLit 48) =>
    rewrite (s0_U_step Ex 35 36 (bs (Z.of_nat 3)) (bs (Z.of_nat 4)) ltac:(EBk 3%nat) ltac:(EBk 4%nat) (BSR _) (BSR _));
    unfold sc_step; reflexivity
  | SAlu ALU_SRA (SAlu ALU_OR (SLit 0) (SAlu ALU_SLL (SOff 35 0) (SLit 48))) (SLit 48) =>
    rewrite (s0_U_step4 Ex 35 (bs (Z.of_nat 3)) ltac:(EBk 3%nat) (BSR _)); unfold sc_step; rewrite (BS0 4) by lia; reflexivity
  | SAlu ALU_ADD (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 33 0)) (SLit 0) =>
    rewrite (s0_U_u16 Ex 33 34 (bs (Z.of_nat 1)) (bs (Z.of_nat 2)) ltac:(EBk 1%nat) ltac:(EBk 2%nat) (BSR _) (BSR _));
    unfold sc_u16; reflexivity
  | SLit 0 =>
    rewrite U_SLit; change (zcanon 0) with 0; unfold sc_flags, sc_u16, sc_step, sc_s7v, sx16;
    repeat match goal with |- context [bs ?i] => rewrite (BS0 i) by lia end; first [reflexivity | lia]
  | SOff ?k ?c =>
    rewrite U_SOff; cbn [ew ewset Nat.eqb];
    repeat match goal with H : bv_unsigned (ew _ k) = _ |- context [bv_unsigned (ew _ k)] => rewrite H end;
    unfold sc_flags, sc_u16; repeat match goal with |- context [bs ?i] => rewrite (BS0 i) by lia end;
    pose proof (BSR 0); pose proof (BSR 1);
    unfold zcanon, M64; rewrite Z.mod_small by (unfold shadow_addr, SHADOW_OFF; lia); lia
  end end.
(* keep: every byte outside the written windows is the byte at 0x82a10 *)
Ltac s0_wr U9 U18 U19 :=
  let a := fresh "a" in let Ha := fresh "Ha" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a Ha (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hr; rewrite ?U9, ?U18, ?U19 in Hr;
      unfold s0_inW, shadow_addr; lia | ]);
  destruct Hin.
Ltac s0_keep U9 U18 U19 sp1 F :=
  lazymatch goal with
  | KEEP : forall a, _ -> _ -> aview ?sg ?Hh ?m0 a = aview _ _ ?mb a,
    HFr : frame_of ?Ex ?rs (mrestrict ?Hh ?m0) (mrestrict _ ?m') |- _ =>
    let K2 := fresh "KEEP" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ s0_inW sp1 F a -> aview sg Hh m' a = aview sg Hh mb a)
      by (apply (s0_keep_step Ex rs Hh mb m0 m' (s0_inW sp1 F) HFr); [s0_wr U9 U18 U19 | exact KEEP]);
    clear KEEP; rename K2 into KEEP
  end; clear_frames.
(* the 35 f3 bytes of the frame-shadow tail, from the chunks of region 1 *)
Ltac s0_tailb HS U19 :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth 1 (ss_mem ssx) s0_Rsp) in
    let HR := fresh "HR" in
    pose proof (st_ok_pi_region_nth Ex ssx msx 1 r HS ltac:(vm_compute; reflexivity)) as HR;
    lazymatch r with YP09.mkRegion (Some ?k) ?lo ?hi ?wlo ?whi ?cs =>
      let o := fresh "o" in let Ho := fresh "Ho" in let j := fresh "j" in let Hj := fresh "Hj" in
      intros o Ho;
      assert (Hj : exists j, (j < 35)%nat /\ o = 1141 + Z.of_nat j) by (exists (Z.to_nat (o - 1141)); split; lia);
      destruct Hj as (j & Hj & ->);
      do 35 (destruct j as [|j]; [
        lazymatch goal with |- aview _ _ _ (_ + (1141 + Z.of_nat ?jj)) = _ =>
          let od := eval vm_compute in (1141 + Z.of_nat jj) in
          change (1141 + Z.of_nat jj) with od;
          let V := fresh "V" in
          pose proof (YC4b.field_of_region_any Ex _ k _ cs lo hi wlo whi od 1 (SLit 18446744073709551603) HR eq_refl
            ltac:(repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
          cbn [ms_mem restrict ew ewset Nat.eqb N.to_nat Pos.to_nat] in V; rewrite s0_lit_byte in V by lia;
          rewrite U19 in V; unfold shadow_addr;
          apply (aview_of_val_mem1 SEGS); [exact V | lia]
        end | ]);
      lia
    end end.
(* a value read from a chunk equals the expected value v *)
Ltac s0_bnds :=
  try (match goal with B : forall i, 0 <= _ i < 256 |- _ => pose proof (B 0); pose proof (B 1);
    pose proof (B 2); pose proof (B 3); pose proof (B 4); pose proof (B 5); pose proof (B 6); pose proof (B 7);
    pose proof (B 8); pose proof (B 9); pose proof (B 10) end).
Ltac s0_modsimp :=
  repeat match goal with |- context [?x mod 2 ^ ?q] =>
    lazymatch x with context [Z.modulo _ _] => fail | _ =>
      rewrite (Z.mod_small x (2 ^ q)) by (s0_bnds; unfold shadow_addr, SHADOW_OFF; lia) end end.
Ltac s0_valeq :=
  lazymatch goal with |- ?v = bv_unsigned (sv_denot ?E ?e) mod 2 ^ (8 * Z.of_N ?w) =>
    change (bv_unsigned (sv_denot E e)) with (U E e) end;
  rewrite ?U_SOff, ?U_SLit; cbn [ew ewset Nat.eqb];
  repeat match goal with H : bv_unsigned (ew _ ?k) = _ |- context [bv_unsigned (ew _ ?k)] => rewrite H end;
  change (8 * Z.of_N 8) with 64; change (8 * Z.of_N 1) with 8; unfold zcanon, M64;
  unfold shadow_addr; s0_modsimp; lia.
(* a spill slot rdword from the chunks of region 0 (s1 = atom 9) *)
Ltac s0_spill HS U9 :=
  lazymatch goal with |- rdword _ (_ + ?off) = Some ?v =>
    let V := fresh "V" in s0_fld HS 0%nat off V; rewrite U9 in V;
    lazymatch type of V with val_mem _ _ _ _ ?val =>
      replace val with v in V by s0_valeq;
      apply (rdword_of_val_mem SEGS); [exact V | unfold shadow_addr, SHADOW_OFF; lia] end end.
(* the mac object [F + 0x70, F + 0x76) holds sc_macb bs, from the chunks of region 3 (s2 = atom 18) *)
Ltac s0_mac HS U18 BS0 BSR :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; cbn [length sc_macb] in Hj;
  do 6 (destruct j as [|j]; [
    cbn [nth sc_macb]; split; [| apply BSR];
    lazymatch goal with |- val_mem _ _ (?base + Z.of_nat ?jj) _ ?tv =>
      let od := eval vm_compute in (112 + Z.of_nat jj) in
      let V := fresh "V" in s0_fld HS 3%nat od V; rewrite U18 in V;
      let zj := eval vm_compute in (Z.of_nat jj) in change (Z.of_nat jj) with zj;
      lazymatch type of U18 with _ = ?Fv => replace (base + zj) with (Fv + od) by lia end;
      lazymatch type of V with val_mem _ _ _ _ ?val =>
        replace val with tv in V; [exact V | first [ reflexivity | (rewrite (BS0 _) by lia; reflexivity) | s0_valeq
          | (rewrite (BS0 _) by lia; s0_valeq) ]] end end | ]);
  lia.
(* a register at C1 *)
Ltac s0_reg HS ER regs2 bs BS0 BSR :=
  lazymatch goal with |- getr _ ?r = w64 ?v =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let Hr := fresh "Hr" in
    pose proof (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr; rewrite Hr; clear Hr;
    lazymatch e with
    | SOff ?k 0 =>
      lazymatch eval vm_compute in (Nat.ltb k 32) with
      | true => rewrite sv_denot_SOff0; cbn [ew ewset Nat.eqb];
                match goal with Rk : getr regs2 ?r' = w64 ?w |- _ =>
                  rewrite (ER k r' eq_refl), Rk; unfold w64; f_equal; lia end
      | false => rewrite denot_lit_U; unfold w64; f_equal; s0_Ueq bs BS0 BSR e
      end
    | _ => rewrite denot_lit_U; unfold w64; f_equal; s0_Ueq bs BS0 BSR e
    end end end.
Lemma s0_tail : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md p n T (POST : world SEGS -> config -> Prop)
fpos S2 regs2 mem2 md2,
sc_base0 SEGS B ameter_triv WK ly S W regs mem md p n T ->
s0_mid B WK ly S W regs mem md p n fpos S2 regs2 mem2 md2 ->
(forall E0, @sc_from_C1 fx rc SK SEGS B ameter_triv WK scene_geom_asan_ubsan
(mkRTCX SEGS ly S W regs mem md p n fpos (32 * ((spZ regs - 224) / 32)) E0 T) POST) ->
SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x16c)) mem2 (seg_rom SEGS)) md2) POST.
Proof.
intros ly S W regs mem md p n T POST fpos S2 regs2 mem2 md2 Hb HM HC1.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
destruct Hb as (HPRE & Hra & Ha0 & Ha1 & Hpn & Hfr0 & Hev0 & Hlive0 & HROD & HSNK & HFD & HSORT & HMO).
destruct HM as (HJ & Hfrs2 & Eab & Hbb & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R23 & R24 & R26 & HSAV & HFLAG & HSH).
pose proof HPRE as (HAR0 & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & HKhi & HKblk & HKimg & HKfr & _ & HPRES2 & _).
set (sp0 := spZ regs) in *.
set (sp1 := 32 * ((sp0 - 224) / 32)) in *.
set (F := frame_addr ly 8 fpos) in *.
assert (Hfin2 : In (8, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 8 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 8 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
fold F in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil.
change (fs_frame_bytes 8) with 16384 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (Hsp064 : 0 <= sp0 < 2 ^ 64) by (unfold sp0, spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr;
  change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
destruct (sp1_facts (sp0 - 224) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (Hsp1r & Hsp1al & _).
fold sp1 in Hsp1r, Hsp1al.
assert (HFq : F mod 8 = 0 /\ F / 8 = 4 * (F / 32)).
{ destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HFal) as [q Hq]. rewrite Hq. split.
  - replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult.
  - replace (q * 32) with ((4 * q) * 8) by lia. rewrite Z.div_mul by lia. replace (4 * q * 8) with (q * 32) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
assert (HF8x : F = 8 * (F / 8)) by (destruct HFq as (HFq1 & _); pose proof (Z.div_mod F 8 ltac:(lia)); lia).
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
(* the input bytes, read from the entry memory, 0 beyond the end *)
set (bs := fun i : Z => if (0 <=? i) && (i <? n) then match aview SEGS (w_H W) mem (p + i) with Some v => v | None => 0 end else 0).
assert (BSR : forall i, 0 <= bs i < 256).
{ intros i. unfold bs. destruct ((0 <=? i) && (i <? n)); [|lia].
  destruct (aview SEGS (w_H W) mem (p + i)) as [v|] eqn:Hv; [|lia].
  destruct (aview_byte SEGS _ _ _ _ Hv) as (b & _ & -> & Hr). lia. }
assert (BS0 : forall i, n <= i -> bs i = 0).
{ intros i Hi. unfold bs. rewrite (proj2 (Z.ltb_ge i n) Hi), andb_false_r. reflexivity. }
assert (BSV : forall i, 0 <= i < n -> aview SEGS (w_H W) mem (p + i) = Some (bs i) /\
  aview SEGS (w_H W) mem2 (p + i) = Some (bs i)).
{ intros i Hi. destruct Hpn as [(Hn0 & _) | (Hnpos & Hpin)]; [lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hpin) as (_ & _ & _ & _ & Hppres & _).
  assert (Hrq : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  pose proof (aview_some_of_apresent SEGS _ _ _ (proj1 (Hppres (p + i) ltac:(lia)))) as Hsome.
  assert (E1 : aview SEGS (w_H W) mem (p + i) = Some (bs i)).
  { unfold bs. rewrite (proj2 (Z.leb_le 0 i)) by lia. rewrite (proj2 (Z.ltb_lt i n)) by lia. cbn [andb].
    destruct (aview SEGS (w_H W) mem (p + i)); [reflexivity | exfalso; exact (Hsome eq_refl)]. }
  split; [exact E1|]. rewrite <- E1.
  apply (HKblk p n i Hpin); [rewrite Eab; exact Hpin | lia | apply inFP_nil]. }
(* ---- the environment and the symbolic state at 0x82a10 ---- *)
set (E := Eimg (Ereg regs2 (s0_extra bs))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs2 r).
{ intros k r Hk. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (EB : forall j, (j < 11)%nat -> ew E (32 + j) = Z_to_bv 64 (bs (Z.of_nat j))).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold s0_extra.
  rewrite (nth_indep _ _ (Z_to_bv 64 (bs (Z.of_nat 0)))) by (rewrite length_map, length_seq; exact Hj).
  rewrite (map_nth (fun j0 : nat => Z_to_bv 64 (bs (Z.of_nat j0)))), seq_nth by exact Hj. reflexivity. }
assert (Hsp1b : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite (ER 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite (ER 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8).
{ rewrite (ER 19%nat 19%bv eq_refl), R19; unfold w64, shadow_addr; apply unsigned_lit_small.
  pose proof (Z.div_le_upper_bound F 8 (2 ^ 47) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF; lia. }
assert (U23 : bv_unsigned (ew E 23) = n) by (rewrite (ER 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite (ER 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (UB : forall j, (j < 11)%nat -> bv_unsigned (ew E (32 + j)) = bs (Z.of_nat j))
  by (intros j Hj; rewrite (EB j Hj); apply unsigned_lit_small; pose proof (BSR (Z.of_nat j)); lia).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (U20 : bv_unsigned (ew E 20) = F) by (rewrite (ER 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF + F / 8 + 28).
{ rewrite (ER 21%nat 21%bv eq_refl), R21; unfold w64, shadow_addr; apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
assert (UB0 : bv_unsigned (ew E 32) = bs 0) by exact (UB 0%nat ltac:(lia)).
assert (UB1 : bv_unsigned (ew E 33) = bs 1) by exact (UB 1%nat ltac:(lia)).
assert (UB2 : bv_unsigned (ew E 34) = bs 2) by exact (UB 2%nat ltac:(lia)).
assert (UB3 : bv_unsigned (ew E 35) = bs 3) by exact (UB 3%nat ltac:(lia)).
assert (UB4 : bv_unsigned (ew E 36) = bs 4) by exact (UB 4%nat ltac:(lia)).
assert (UB5 : bv_unsigned (ew E 37) = bs 5) by exact (UB 5%nat ltac:(lia)).
assert (UB6 : bv_unsigned (ew E 38) = bs 6) by exact (UB 6%nat ltac:(lia)).
assert (UB7 : bv_unsigned (ew E 39) = bs 7) by exact (UB 7%nat ltac:(lia)).
assert (UB8 : bv_unsigned (ew E 40) = bs 8) by exact (UB 8%nat ltac:(lia)).
assert (UB9 : bv_unsigned (ew E 41) = bs 9) by exact (UB 9%nat ltac:(lia)).
assert (UB10 : bv_unsigned (ew E 42) = bs 10) by exact (UB 10%nat ltac:(lia)).
assert (HSgen : forall (c : nat) (f23 : afact) (FA : list (nat * afact)) (C : list acond),
  (c <= 11)%nat -> (c = 0%nat \/ (0 < Z.of_nat c <= n /\ In (p, n) (ablocks B ly S2) /\ bv_unsigned (ew E 24) = p)) ->
  afact_ok E 23 f23 -> atoms_ok E FA -> conds_ok E C ->
  st_ok_pi SEGS VAL E (s0_ss0 c f23 FA C) (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + 0x16c)) mem2 (seg_rom SEGS)))).
{ intros c f23 FA C Hc Hcase F23 HFA HC.
  rewrite restrict_mkst_fx. unfold s0_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - clear - Hc. do 12 (destruct c as [|c]; [vm_compute; reflexivity|]). lia.
  - unfold s0_rs0. repeat apply Forall_cons.
    + unfold region_ok, s0_Rsp. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HPRES2. lia.
    + unfold region_ok, s0_RfsT. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
      split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). replace (SHADOW_OFF + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; lia).
      apply (proj1 (HFSpres o ltac:(change (16384 / 8) with 2048; lia))).
    + unfold region_ok, s0_RfsE. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
      split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia | constructor].
    + unfold region_ok, s0_Rmac. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U18.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia | constructor].
    + destruct (Nat.eqb_spec c 0) as [->|Hc0]; [constructor|].
      destruct Hcase as [Hc0' | (Hcn & Hpin & U24)]; [exfalso; exact (Hc0 Hc0')|].
      constructor; [|constructor].
      unfold region_ok, s0_Rin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U24.
      pose proof (bv_unsigned_in_range 64 (ew E 24)) as Hp64. change (bv_modulus 64) with (2 ^ 64) in Hp64. rewrite U24 in Hp64.
      pose proof Hpin as Hpin0. rewrite Eab in Hpin0. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hpin0) as (_ & _ & Hpc & _).
      assert (Hrq : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold s0_in_chunks. apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as (j & <- & Hj). apply in_seq in Hj.
      apply (chunk_ok_val SEGS E _ p (Z.of_nat j) 1 (SOff (32 + j) 0) (bs (Z.of_nat j))).
      * cbn [sv_denot]. rewrite (EB j) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * pose proof (BSR (Z.of_nat j)). cbn. lia.
      * cbn. lia.
      * exact (proj1 (val_mem1_of_aview SEGS _ _ _ _ (proj2 (BSV (Z.of_nat j) ltac:(lia))))).
  - apply pairwise_disjoint_of_extents. unfold s0_rs0.
    destruct (Nat.eqb_spec c 0) as [->|Hc0].
    + cbn [Nat.eqb]. unfold s0_Rsp, s0_RfsT, s0_RfsE, s0_Rmac, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val app]. rewrite U9, U18, U19.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF in *.
      repeat split; lia.
    + destruct Hcase as [Hc0' | (Hcn & Hpin & U24)]; [exfalso; exact (Hc0 Hc0')|].
      replace (Nat.eqb c 0) with false by (symmetry; apply Nat.eqb_neq; exact Hc0).
      pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ p n 8 fpos HAR2 Hpin Hfin2) as Hsep. fold F in Hsep.
      unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 8) with 16384 in Hsep.
      pose proof Hpin as Hpin0. rewrite Eab in Hpin0. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hpin0) as (_ & Hp4 & Hpc & Hpapp & _).
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
      assert (Hrq : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
      unfold s0_Rsp, s0_RfsT, s0_RfsE, s0_Rmac, s0_Rin, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val app]. rewrite U9, U18, U19, U24.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF in *.
      repeat split; lia.
  - split; [|split; [exact HC | exact I]].
    apply atoms_ok_app; [|exact HFA].
    unfold s0_atoms0. cbn [atoms_ok map seq Nat.add].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U9; change (2 ^ 5) with 32; lia|].
    split; [unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U18; change (2 ^ 5) with 32; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U19; change (2 ^ 2) with 4;
      destruct HFq as (_ & HF8e); rewrite HF8e; unfold SHADOW_OFF;
      split; [lia|]; split; [replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia]|].
    split; [exact F23|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U26, Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF; lia|].
    repeat match goal with
    | |- afact_ok _ ?k (mkAF 0 255 0) /\ _ =>
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2];
        replace k with (32 + (k - 32))%nat by lia; rewrite (UB (k - 32)%nat) by lia;
        pose proof (BSR (Z.of_nat (k - 32))); rewrite Z.pow_0_r, Z.mod_1_r; lia|]
    end.
    exact I. }
clearbody E.
(* ---- the cut C1 from the facts each case establishes at 0x82c28 ---- *)
assert (EXIT : forall (regs3 : bvmap 5 word) mem3 md3,
  ajournal (SK := SK) SEGS B (sw_stk WK) sp0 [] ly S W mem md [(8, fpos)] ly S2 W mem3 md3 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s0_inW sp1 F a -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem2 a) ->
  (forall o, 0x475 <= o < 0x498 -> aview SEGS (w_H W) mem3 (shadow_addr F + o) = Some 0xf3) ->
  aview SEGS (w_H W) mem3 (shadow_addr F + 0xe) = Some 6 ->
  rdword (aview SEGS (w_H W) mem3) (sp1 + 0x10) = Some (shadow_addr F + 0x1c) ->
  rdword (aview SEGS (w_H W) mem3) (sp1 + 0x28) = Some F ->
  rdword (aview SEGS (w_H W) mem3) (sp1 + 0x30) = Some (F + 224) ->
  rdword (aview SEGS (w_H W) mem3) (sp1 + 0x38) = Some (F + 112) ->
  garr8 SEGS (mrestrict (w_H W) mem3) (F + 112) (sc_macb bs) ->
  getr regs3 2 = w64 sp1 -> getr regs3 3 = w64 (as_gp B) -> getr regs3 4 = w64 (as_tp B) ->
  getr regs3 8 = w64 sp0 -> getr regs3 9 = w64 sp1 -> getr regs3 18 = w64 F ->
  getr regs3 19 = w64 (shadow_addr F) -> getr regs3 25 = w64 (F + 32) -> getr regs3 26 = w64 SHADOW_OFF ->
  getr regs3 27 = w64 (F + 144) ->
  getr regs3 16 = w64 (sc_flags bs) -> getr regs3 24 = w64 (sc_u16 bs) ->
  getr regs3 21 = w64 (n - Z.min n 11) -> getr regs3 22 = w64 (p + Z.min n 11) ->
  getr regs3 23 = w64 (sc_step bs mod 2 ^ 64) -> getr regs3 20 = w64 (sc_s7v bs mod 2 ^ 64) ->
  SRr SEGS W (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 0x384)) mem3 (seg_rom SEGS)) md3) POST).
{ intros regs3 mem3 md3 HJ3 KEEP3 TAIL3 M63 SP10 SP28 SP30 SP38 MAC3 G2 G3 G4 G8 G9 G18 G19 G25 G26 G27 G16 G24 G21 G22 G23 G20.
  pose proof (HC1 (Eimg (Ereg regs []))) as HC. unfold sc_from_C1 in HC.
  specialize (HC ly S2 W regs3 mem3 md3 bs).
  replace (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 0x384)) mem3 (seg_rom SEGS)) md3)
    with (cfg_at SEGS (sg_pc_c1 scene_geom_asan_ubsan) regs3 mem3 md3)
    by (unfold cfg_at, scene_geom_asan_ubsan; cbn [sg_pc_c1]; unfold SEG_C1_off, AF_LLVMFuzzerTestOneInput, w64;
        rewrite Z.add_0_r; reflexivity).
  apply HC. clear HC.
  pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HKimg3 & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 8 fpos HAR3 Hfin2) as (_ & _ & HFP3 & HSP3).
  fold F in HFP3, HSP3. change (fs_frame_bytes 8) with 16384 in HFP3, HSP3. change (16384 / 8) with 2048 in HSP3.
  unfold cut_C1, sc_j, sc_frame, sc_saves, sc_shbg, sc_shr, sc_open, sc_img, sc_in, sc_PB, sc_F, rt_F, rt_FL, vat, sc_rest, sc_cur.
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T sg_cid sg_off_blki sg_off_mac sg_off_blk sg_off_expect sg_mac_n
       sg_sh_blki_lo sg_sh_blki_hi sg_sh_blk_lo sg_sh_blk_hi sg_sh_bg sg1_F sg1_shF sg1_shbase sg1_sp1 sg1_sp0 sg1_blki sg1_blk
       sg1_expect sg1_flags sg1_rest sg1_cur sg1_u16 sg1_s7v sg1_shexp sg1_Fsp sg1_mac sg1_step scene_geom_asan_ubsan].
  unfold RV_s0, RV_s1, RV_s2, RV_s3, RV_s4, RV_s5, RV_s6, RV_s7, RV_s8, RV_s9, RV_s10, RV_s11, RV_a6.
  fold sp0. fold sp1. fold F. change (fs_frame_bytes 8) with 16384. change (16384 / 8) with 2048.
  assert (KS : forall o, 0 <= o < 0x475 -> o <> 0xe -> aview SEGS (w_H W) mem3 (shadow_addr F + o) = Some (s0_sh o)).
  { intros o Ho Hne. rewrite KEEP3; [apply HSH; lia | unfold shadow_addr, SHADOW_OFF; lia | unfold s0_inW, shadow_addr, SHADOW_OFF; lia]. }
  split.
  { split; [exact HJ3|]. split; [exact Hfrs2|]. cbn [mo_le ameter_triv]. exact I. }
  split; [exact Eab|]. split; [exact Hbb|].
  split.
  { split.
    - rewrite (s0_rdword_kept (aview SEGS (w_H W) mem2)); [exact HFLAG|].
      intros i Hi. apply KEEP3; [lia | unfold s0_inW, shadow_addr, SHADOW_OFF; lia].
    - split.
      + intros a Ha. exact (proj1 (HFP3 a Ha)).
      + intros a Ha. replace a with (shadow_addr F + (a - shadow_addr F)) by lia. apply (proj1 (HSP3 (a - shadow_addr F) ltac:(lia))). }
  split.
  { intros j Hj. rewrite (s0_rdword_kept (aview SEGS (w_H W) mem2)); [apply HSAV; exact Hj|].
    intros i Hi. apply KEEP3; [lia | unfold s0_inW, shadow_addr, SHADOW_OFF; lia]. }
  split.
  { repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; intros o Ho;
    first [ apply TAIL3; lia
          | rewrite (KS o) by lia; f_equal; unfold s0_sh;
            repeat match goal with |- context [?a <? ?b] =>
              first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia] end;
            reflexivity ]. }
  split.
  { intros o Ho. rewrite (KS o) by lia. f_equal. unfold s0_sh.
    repeat match goal with |- context [?a <? ?b] =>
      first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia] end; reflexivity. }
  split.
  { intros o Ho. rewrite (KS o) by lia. f_equal. unfold s0_sh.
    repeat match goal with |- context [?a <? ?b] =>
      first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia] end; reflexivity. }
  split.
  { unfold block_shadow. split; [replace (F + 112) with ((F / 8 + 14) * 8) by lia; apply Z_mod_mult|]. split; [lia|].
    intros i Hi. change ((6 + 7) / 8) with 1 in Hi. assert (Hi0 : i = 0) by lia. subst i.
    unfold shadow_of_addr. replace (SHADOW_OFF + (F + 112) / 8 + 0) with (shadow_addr F + 0xe).
    - rewrite M63. reflexivity.
    - unfold shadow_addr. replace (F + 112) with ((F / 8 + 14) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  split.
  { split; [unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia|].
    split; [exact G3|]. split; [exact G4|].
    intros a Ha Hown Herr. rewrite <- (HROD a Ha Hown Herr).
    apply HKimg3; [| exact Hown | exact Herr | exact (fp_spares_closed [] a sink_closed_nil)].
    destruct Ha as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr]|].
    rewrite HWRLO, HWRHI in Hr. apply pa_relro_img. exact Hr. }
  split.
  { intros i Hi. split; [apply BSR|]. split.
    - intros Hin. split; [apply BSR|]. exact (proj1 (val_mem1_of_aview SEGS _ _ _ _ (proj1 (BSV i ltac:(lia))))).
    - intros Hni. apply BS0. lia. }
  split; [exact MAC3|].
  split; [exact G8|]. split; [exact G9|]. split; [exact G18|]. split; [exact SP28|]. split; [exact G19|].
  split; [exact G26|]. split; [exact G25|]. split; [exact G27|]. split; [exact SP30|]. split; [exact SP38|].
  split; [change (224 / 8) with 28; exact SP10|].
  split; [exact G16|]. split; [exact G24|]. split; [exact G21|]. split; [exact G22|]. split; [exact G23 | exact G20]. }
(* ---- the twelve cases of n: 0 .. 10 pin s7 = n to a literal; n >= 11 keeps it an atom (with n >> 26 = 0 assumed) ---- *)
assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (ER 26%nat 26%bv eq_refl), R26; reflexivity).
assert (NC0 : n = 0 \/ 0 < n) by lia.
destruct NC0 as [Hk | Hnpos];
[ pose proof (HSgen 0%nat (mkAF 0 0 0) [] [] ltac:(lia) ltac:(left; reflexivity)
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) I I) as HS; s0_pin HS 0 Hk
| destruct Hpn as [(Hn0 & _) | (_ & Hpin)]; [lia|];
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hpin) as (Hp16 & Hp4 & Hpc & Hpapp & _);
  assert (Hrq : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia);
  assert (U24 : bv_unsigned (ew E 24) = p) by (rewrite (ER 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia);
  assert (Hpin2 : In (p, n) (ablocks B ly S2)) by (rewrite Eab; exact Hpin);
  assert (E24 : ew E 24 = Z_to_bv 64 p) by (rewrite (ER 24%nat 24%bv eq_refl), R24; reflexivity);
  assert (F24 : atoms_ok E [(24%nat, mkAF 4096 140737479966720 4)])
    by (split; [unfold afact_ok; cbn [fst snd af_lo af_hi af_al2]; rewrite U24; change (2 ^ 4) with 16; lia | exact I]);
  assert (NC : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ 11 <= n) by lia;
  destruct NC as [Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|Hk]]]]]]]]]];
  [ pose proof (HSgen 1%nat (mkAF 1 1 0) _ [] ltac:(lia) ltac:(right; split; [lia|]; split; [exact Hpin2 | exact U24])
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) F24 I) as HS; s0_pin HS 1 Hk
  | pose proof (HSgen 2%nat (mkAF 2 2 0) _ [] ltac:(lia) ltac:(right; split; [lia|]; split; [exact Hpin2 | exact U24])
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) F24 I) as HS; s0_pin HS 2 Hk
  | pose proof (HSgen 3%nat (mkAF 3 3 0) _ [] ltac:(lia) ltac:(right; split; [lia|]; split; [exact Hpin2 | exact U24])
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) F24 I) as HS; s0_pin HS 3 Hk
  | pose proof (HSgen 4%nat (mkAF 4 4 0) _ [] ltac:(lia) ltac:(right; split; [lia|]; split; [exact Hpin2 | exact U24])
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) F24 I) as HS; s0_pin HS 4 Hk
  | pose proof (HSgen 5%nat (mkAF 5 5 0) _ [] ltac:(lia) ltac:(right; split; [lia|]; split; [exact Hpin2 | exact U24])
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) F24 I) as HS; s0_pin HS 5 Hk
  | pose proof (HSgen 6%nat (mkAF 6 6 0) _ [] ltac:(lia) ltac:(right; split; [lia|]; split; [exact Hpin2 | exact U24])
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) F24 I) as HS; s0_pin HS 6 Hk
  | pose proof (HSgen 7%nat (mkAF 7 7 0) _ [] ltac:(lia) ltac:(right; split; [lia|]; split; [exact Hpin2 | exact U24])
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) F24 I) as HS; s0_pin HS 7 Hk
  | pose proof (HSgen 8%nat (mkAF 8 8 0) _ [] ltac:(lia) ltac:(right; split; [lia|]; split; [exact Hpin2 | exact U24])
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) F24 I) as HS; s0_pin HS 8 Hk
  | pose proof (HSgen 9%nat (mkAF 9 9 0) _ [] ltac:(lia) ltac:(right; split; [lia|]; split; [exact Hpin2 | exact U24])
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) F24 I) as HS; s0_pin HS 9 Hk
  | pose proof (HSgen 10%nat (mkAF 10 10 0) _ [] ltac:(lia) ltac:(right; split; [lia|]; split; [exact Hpin2 | exact U24])
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) F24 I) as HS; s0_pin HS 10 Hk
  | pose proof (HSgen 11%nat (mkAF 11 (2 ^ 26 - 1) 0) _ [s0_c26] ltac:(lia) ltac:(right; split; [lia|]; split; [exact Hpin2 | exact U24])
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23, Z.pow_0_r, Z.mod_1_r; lia) F24
      ltac:(split; [apply s0_c26_ok; rewrite U23; lia | exact I])) as HS ] ].
all: assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ s0_inW sp1 F a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a)
  by reflexivity.
(* phase (i): plain run 0x82a10 .. 0x82aac: the 35 f3 stores of the frame-shadow tail, n >> 26, the shF + 0x1c spill *)
all: paj_run_to_shc RUNTOP HS HJ 0x208; [s0_awr sp0 sp1 |].
all: s0_keep U9 U18 U19 sp1 F.
(* phase (ii): the frame-shadow tail read-only, the token run through the input header to 0x82b90 *)
all: s0_rewin HS 1%nat 0 0 ltac:(intros o Ho; lia).
all: lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
  assert (SHOK : sh_ok SEGS s0_Bx [] Ex (mrestrict (w_H W) (ms_mem msx))) by constructor end.
all: paj_run_to_tok RUNTO HS HJ SHOK BAND_SPAN 0x2ec.
all: lazymatch goal with
  | |- range_addressable _ _ _ _ => s0_obl HJ p n E24 E26 Hpin2
  | |- awr_ok _ _ _ _ _ _ _ _ _ => s0_awr sp0 sp1
  | |- _ => idtac end.
all: s0_keep U9 U18 U19 sp1 F.
(* phase (iii): the mac cell and the mac object writable, the plain run to the loop head 0x82bd4 *)
all: clear SHOK.
all: s0_rewin HS 2%nat 0xe 0xf ltac:(s0_fswin HJ Hfin2 U19).
all: s0_rewin HS 3%nat 0x70 0x76 ltac:(s0_macwin HJ Hfin2 U18).
all: paj_run_to_shc RUNTOP HS HJ 0x330; [s0_awr sp0 sp1 |].
all: s0_keep U9 U18 U19 sp1 F.
(* phase (iv): the mac cell read-only, mac covered by its now open shadow, the token run of the 6-turn loop to C1 *)
all: s0_rewin HS 2%nat 0 0 ltac:(intros o Ho; lia).
all: s0_fld HS 2%nat 14 V6.
all: rewrite U19 in V6.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
  assert (SHOK : sh_ok SEGS s0_Bx [mkSHE 18 0x70 0x76] Ex (mrestrict (w_H W) (ms_mem msx)))
    by (s0_shok_mac V6 E26 ER R18 HF8x HFapp) end.
all: paj_run_to_tok RUNTO HS HJ SHOK BAND_SPAN 0x384.
all: lazymatch goal with
  | |- range_addressable _ _ _ _ => s0_obl HJ p n E24 E26 Hpin2
  | |- awr_ok _ _ _ _ _ _ _ _ _ => s0_awr sp0 sp1
  | |- _ => idtac end.
all: s0_keep U9 U18 U19 sp1 F.
(* ---- the cut C1 at 0x82c28 ---- *)
all: pmkst HS.
all: apply EXIT.
all: first
  [ exact HJ
  | exact KEEP
  | lazymatch goal with
    | |- forall o, _ -> aview _ _ _ (shadow_addr _ + o) = Some _ => s0_tailb HS U19
    | |- aview _ _ _ (shadow_addr _ + 14) = Some 6 =>
      let V := fresh "V" in s0_fld HS 2%nat 14 V; rewrite U19 in V; unfold shadow_addr;
      apply (aview_of_val_mem1 SEGS); [exact V | lia]
    | |- rdword _ _ = _ => s0_spill HS U9
    | |- garr8 _ _ _ _ => s0_mac HS U18 BS0 BSR
    | |- getr _ _ = _ => s0_reg HS ER regs2 bs BS0 BSR
    end ].
Qed.

Theorem llvmf_S0 : @seg_S0_stmt fx rc SK SEGS B ameter_triv WK scene_geom_asan_ubsan.
Proof.
unfold seg_S0_stmt.
intros ly S W regs mem md p n T POST Hb HC.
apply (s0_head ly S W regs mem md p n T POST Hb).
intros fpos S2 regs2 mem2 md2 HM.
apply (s0_tail ly S W regs mem md p n T POST fpos S2 regs2 mem2 md2 Hb HM).
intros E0. exact (HC fpos E0).
Qed.
End h.
End f.
End d.

(* ---- gate 6h: the theorem at scene's own sink head, musl's ofl_head 0x5f7190 of fuzz_scene.asan-ubsan (the value
   of lib/AU/P_LLVMFuzzerTestOneInput.v's scene_sink_head), passed by name, never by instance search. ---- *)
Definition s0_scene_sink_head : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head :=
{| OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sk_ofl_head := 0x5f7190 |}.
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition llvmf_S0_scene := @llvmf_S0 fx rc s0_scene_sink_head.
End s.

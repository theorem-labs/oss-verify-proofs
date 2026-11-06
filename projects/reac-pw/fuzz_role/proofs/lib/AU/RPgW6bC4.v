(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated for image A's code with the callee's same_but_materialized kept as same_io in the post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Call.v at 888d1ffb4c3 for reac-pw/fuzz_headamp image A: module paths changed, w_intrin_at renamed hd_intrin_at, role's RPgCfgChanges.cfg_segs_low replaced by HPgSteps.img_segs_low over headamp's segments; the two instances hd_memset_at / hd_memcpy_at are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgIntrin.v at 021dba8dbbd; hd_intrin_at renamed cb_intrin_at and stated over image B's segments (lib/AU/Img0U.v rsegs, lib/AU/HPgSteps.v img_segs_low, AR_laws from YG0q.AR_laws_ok), hd_memset_at / hd_memcpy_at renamed cb_memset_at / cb_memcpy_at with the entry pc made a parameter (image B's entries CB_ASAN_MEMSET 0x52228 and CB_ASAN_MEMCPY 0x51d8c stated as constants). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cKit.v at 80bf14ccf11 (PART 1, a segment's start facts at a cut); rs_ -> cb_, restated over lib/AU/HPgSeg.v (hsu_pre, hsu_core, hsu_E1, hsu_in, hsu_fsh_at) at image B's record headamp_himg_B: the frame for locals of class 4 (1024 bytes, 128 shadow bytes), the 116-byte prologue pattern in place of role's 52, R + 0x220 in place of 0x1a0, image B's three write ranges of hi_w1, the image fact segs_low taken from lib/AU/HPgSteps.v img_segs_low instead of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v at 80bf14ccf11 (w6_ctx, w6_caller_saved and Section seq only; w6_in as cb_in); w6_ -> cb_, the frame (4, pos) and R + 0x220 of image B, R's cells [R, R + 0x198), and the block post w6_post replaced by the shared layer's hdu_blk_postE (lib/AU/HPgSteps.v), rl_blk_post by hdu_blk_post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6a.v at 80bf14ccf11 (its generic helpers only: the list tactics, the register and location-list lemmas, the geometry of a cut, the image's first write range, the suffix and cursor lemmas, pp's image length, the cut's geometry and context, the core step, the input kept, the block step and the side tactics); w6_ -> cb_, over lib/AU/HPgSeg.v at image B: w6_geo with image B's frame (1024 / 128 bytes, R + 0x220) and the conjuncts F mod 32 = 0 and in_app pp, its head- and tail-specific cell lemmas replaced by write-set-free disjointness lemmas, w6_in_kept and the side tactics generalised over the write set, cb_blkE_step added for a block that writes. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 80bf14ccf11 (w6h_div, w6h_sh_e, w6h_e_mod8, w6h_bounds, w6h_callee, w6h_val_kept, w6h_chunk0, w6h_region_nth, w6h_chunks); w6h_ -> cb_, the shadow and alignment lemmas generalised over the offset, the bounds at class 4 (1024 bytes, 128 shadow bytes) and e62's 104 bytes at F + 0x210. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at f3898085bda (w7_post,
   w7_post_of_run), RPgW7bKit.v at f3898085bda (w7_kept, w7_hull, w7_ra_kept, w7_hull_kept, w7_strok, w7_strz and
   their lemmas), RPgCfgChanges.v at f3898085bda (kept_run), RPgW6aTail.v at f3898085bda (tl_byte, tl_val_of_chunk,
   tl_val_at), RPgW6aC2h.v at f3898085bda (c2_all256, c2_envz, c2_nz, c2_notin, c2_kio) and RPgW7bIter.v at
   f3898085bda (w7_cs_bv, w7_cs_out, w7_reg_eq), by way of lib/AU/HPgW6bC1k.v's and
   HPgW6bC1.v's hb1_* copies for reac-pw/fuzz_headamp's image B: moved here and renamed cb_* by the dedup, one copy
   kept for the equal helpers of 17 lib/AU files (HPgE0Base, HPgW7bBase, HPgW7bIter, HPgW6aTail, HPgW6aC2 and
   others); cb_val_at_rng is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgCaseB.v, with its module paths and module names changed; 425 of its 485 lines of code are new or changed and 1029 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bC4.v at 32f84792c2a6; for image B (fuzz_rate.asan-ubsan): the pcs, registers, real-frame cells and the pod object (e62 at F + 0x210) are image B's, the frame for locals is class 4 (1024 bytes), the run passes the UBSan T1 test of the cursor (decided by the atom range of a6), and the block statement is lib/AU/RtPgW6bBaseB.v's w6bb_c4. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6bC4B.v at a191d52e2a9a for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths changed (lib/AU/Img0.rsegs, lib/A/RPgBase and
   RPgCSpec, lib/AU/RPgSteps.v and RPgMem.v names); every pc, register and real-frame cell is role B's: the shadow
   offset is s11, the T1 test's 1 is s4 and the kind byte's address a6; the cells read are [R+0x130] (pp + 0x4000),
   [R+0x140] (pp) and [R+0x158] (&e62), so the entry state has one more atom (35 = pp) and three cell regions; at J
   s6 = pp + 0x4000, a5 = pp and a3 = the cursor; the block statement is lib/AU/RPgW6bBase.v's w6bb_c4_stmt. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the block lemma w6bb_c4 of
   lib/AU/RPgW6bBase.v, case 4 of ent_build's `switch (kind % 10)` (pod.h:326-330) inside LLVMFuzzerTestOneInput
   (0x80020), from its entry 0x80f34 to the join J 0x818d8. Proves no function (kind: segment lemma).

   THE CODE (registers as in RPgW6bBase.v: s1 = R, s11 = SHADOW_OFF, s2 = c the cursor, s6 = |r|, a6 = c - 1,
   t1 = |r| + 1, s4 = 1):
     0x80f34  beqz s6 -> 0x81338                     no byte left: v = 0
     0x80f38  a0 := s2 + 1; 0x80f3c bltu s4,a0 (the UBSan T1 test; the other arm 0x80f40 `j 0x82604`)
     0x80f44 .. 0x80f58  the instrumented check of s2 (NE-SLOW, slow block 0x81a98 `andi a1,s2,7; blt a1,a0`)
     0x80f50  ld s6,0x130(s1); 0x80f54 ld a5,0x140(s1)   between the check's load and its branch (pp + 0x4000, pp)
     0x80f5c  lbu a0,0(s2) (= v); t1 := t1 - 2; s2 := a6 + 2
     0x80f68 .. 0x80f80  a0 := (v - (v * 0xab >> 9) - 2 * (v * 0xab >> 9)) & 0xff   (= v mod 3, pod.h:327)
     0x80f84  j 0x81348
     0x81338  t1 := 0; a0 := 0; ld s6,0x130(s1); ld a5,0x140(s1)   (then 0x81348)
     0x81348  ld a1,0x158(s1) (= &e62); sw 2,0(a1) (e62.type = POD_BOOL); sw 4,4(a1) (e62.size = 4);
              sw a0,8(a1) (e62.body[0..4) = v mod 3); 0x81360 j 0x818d4
     0x818d4  a3 := s2; J 0x818d8
   THE PROOF is one engine run per arm (lib/Reusable/YCbn.v, the token engine that follows the NE-SLOW slow block
   itself and leaves one obligation `range_addressable ...` per check, paid by obl_of_range):
     the entry state (c4b_entry) has the extra atoms 32 = &e62 = F + 0x210, 33 = the value of [R+0x130] = pp + 0x4000,
     34 = the input byte, 35 = the value of [R+0x140] = pp; the regions are e62 (based at atom 32, write window
     [0, 12)), the three real-frame cells [R+0x130], [R+0x140] and [R+0x158] (based at s1, read only, inside the span
     [R+0x48, R+0x160) w6bb_inp keeps the input out of), and the input byte at s2 (based at atom 18, read only, only
     when a byte is left). The shadow entry [mkSHE 32 0 0x68] makes e62's write window safe against the shadow band
     (c4b_shok, from w6bb_in's range_addressable and in_app). With no byte left s6 is pinned to the literal 0, so
     `beqz` is taken and neither the T1 test nor the check runs; with a byte left the facts give s6 in [1, 2^47]
     (`beqz` falls through), s4 in [1, 1] and s2 in [2, 2^47 - 1], so the engine decides `bltu s4,a0` (1 < s2 + 1) by
     the atom ranges: the trap branch 0x80f3c is refuted by the run. The `mod 3` arithmetic is checked for all 256
     byte values by computation (c4b_all256, c4b_a0_val). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSteps RPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the entry state ========================================
   extra atoms: 32 = F + 0x210 (&e62), 33 = the value of [R+0x130] (pp + 0x4000), 34 = the input byte, 35 = the value
   of [R+0x140] (pp) *)
Definition c4b_extra (F pq m p : Z) : list word :=
  [Z_to_bv 64 (F + 0x210); Z_to_bv 64 pq; Z_to_bv 64 m; Z_to_bv 64 p].
Definition C4BBx : sv := SOff 27 0.
Definition C4Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition c4b_SH : list shent := [mkSHE 32 0 0x68].
(* e62 = [F+0x210, F+0x278): the block writes its first 12 bytes *)
Definition c4b_rE : YP09.region := YP09.mkRegion (Some 32%nat) 0 0x68 0 12 [].
(* [R+0x130] = pp + 0x4000 *)
Definition c4b_rQ : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x130 0x138 0 0 [YP09.mkChunk 0x130 (CVal 8 (SOff 33 0))].
(* [R+0x140] = pp *)
Definition c4b_rP : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x140 0x148 0 0 [YP09.mkChunk 0x140 (CVal 8 (SOff 35 0))].
(* [R+0x158] = F + 0x210 *)
Definition c4b_rA : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x158 0x160 0 0 [YP09.mkChunk 0x158 (CVal 8 (SOff 32 0))].
(* the input byte at the cursor *)
Definition c4b_rI : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition c4b_regs (byte : bool) : smem :=
  if byte then [c4b_rE; c4b_rQ; c4b_rP; c4b_rA; c4b_rI] else [c4b_rE; c4b_rQ; c4b_rP; c4b_rA].
(* every bound a closed numeral: s11 = SHADOW_OFF, the cursor s2, &e62, |r| in s6, the input byte, s4 = 1 *)
Definition c4b_facts1 : facts :=
  mkFacts [ (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (18%nat, mkAF 2 (2 ^ 47 - 1) 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 1024) 0); (22%nat, mkAF 1 (2 ^ 47) 0); (34%nat, mkAF 0 255 0);
            (20%nat, mkAF 1 1 0) ] [] [].
Definition c4b_facts0 : facts :=
  mkFacts [ (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (18%nat, mkAF 2 (2 ^ 47 - 1) 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 1024) 0) ] [] [].
Definition c4b_facts (byte : bool) : facts := if byte then c4b_facts1 else c4b_facts0.
Definition c4b_ss (byte : bool) : sstate := mkSS W6BB_D4 sr_atoms (c4b_regs byte) None (c4b_facts byte).

(* ======================================== the arithmetic ========================================
   a0 at 0x80f84, as the engine computes it from the input byte (atom 34): the `mul 0xab` / `srli 9` quotient
   q = v / 3, then v - q - 2 q, masked to a byte. *)
Definition c4b_q : sv := SAlu ALU_SRL (SMd M_MUL (SOff 34 0) (SLit 171)) (SLit 9).
Definition c4b_a0 : sv :=
  SAlu ALU_AND (SAlu ALU_SUB (SAlu ALU_SUB (SOff 34 0) c4b_q) (SAlu ALU_SLL c4b_q (SLit 1))) (SLit 255).
Lemma c4b_all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
split; [lia | apply in_seq; lia].
Qed.
(* every atom holds z *)
Definition c4b_envz (z : Z) : env := mkEnv (fun _ => Z_to_bv 64 z) (fun _ => []).
Lemma c4b_a0_val : forall E m, ew E 34 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E c4b_a0 = Z_to_bv 64 (m mod 3).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (c4b_envz m) c4b_a0);
  [unfold c4b_a0, c4b_q; cbn [sv_denot ew c4b_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (c4b_all256 (fun z => bv_unsigned (sv_denot (c4b_envz z) c4b_a0) =? bv_unsigned (Z_to_bv 64 (z mod 3)))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.

(* ======================================== small helpers ======================================== *)
Lemma c4b_af : forall E n v lo hi al, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof.
intros E n v lo hi al H Hv Hb Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H, unsigned_lit_small by lia. auto.
Qed.
Lemma c4b_u : forall regs extra (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ereg regs extra) n) = v.
Proof. intros regs extra n r v Hn Hr Hv. rewrite (ew_Ereg_nat regs extra n r Hn), Hr. apply unsigned_lit_small. lia. Qed.
(* byte k of a stored word is byte k of its low w bytes *)
Lemma c4b_byte : forall v (w k : nat), (k < w)%nat -> (w <= 8)%nat ->
Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) (8 * Z.of_nat k)) = Z_to_bv 8 (YO0f.le_byte v w k).
Proof.
intros v w k Hk Hw. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). change 256 with (2 ^ 8).
rewrite Z.mod_mod by lia.
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hi8|Hi8].
- rewrite !(Z.mod_pow2_bits_low _ 8 i) by lia. rewrite !Z.shiftr_spec by lia.
  rewrite (Z.mod_pow2_bits_low v 64) by lia. rewrite (Z.mod_pow2_bits_low v (8 * Z.of_nat w)) by lia. reflexivity.
- rewrite !(Z.mod_pow2_bits_high _ 8 i) by lia. reflexivity.
Qed.
Lemma c4b_val_of_chunk : forall E mem base off (n : N) e v,
YP09.chunk_ok rsegs E mem base (YP09.mkChunk off (CVal n e)) -> sv_denot E e = Z_to_bv 64 v -> (N.to_nat n <= 8)%nat ->
val_mem rsegs mem (base + off) (N.to_nat n) v.
Proof.
intros E mem base off n e v H He Hn k Hk. unfold YP09.chunk_ok in H.
cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
unfold YP09.byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal. apply c4b_byte; lia.
Qed.
Lemma c4b_nul0 : bv_unsigned NUL = 0.
Proof. unfold NUL. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma c4b_map_zeros : forall n, map (fun x : byte => bv_unsigned x) (zeros n) = repeat 0 n.
Proof.
induction n as [|n IH]; [reflexivity|].
unfold zeros in *. cbn [repeat map]. rewrite IH, c4b_nul0. reflexivity.
Qed.
(* the model's entry for case 4 (pod.h:326-330) *)
Lemma c4b_model : forall (b : byte) (r : list byte), bv_unsigned b mod 10 = 4 ->
  ent_build (b :: r) = (Ent POD_BOOL 4 (le32 (fst (fuzz_u8 r) mod 3)), snd (fuzz_u8 r)).
Proof.
intros b r H. unfold ent_build. cbn [fuzz_u8]. rewrite H.
destruct r as [|x r']; reflexivity.
Qed.
Lemma c4b_ent_mem : forall w, ent_mem (Ent POD_BOOL 4 (le32 w)) = le32 POD_BOOL ++ le32 4 ++ le32 w ++ zeros 92.
Proof.
intros w. unfold ent_mem. cbn [e_type e_size e_body]. rewrite length_le32. reflexivity.
Qed.

Ltac c4b_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).
Ltac c4b_b32 U := cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact U.
(* a register of the state after a run, as its symbolic value's denotation *)
Ltac c4b_regv HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity);
    cbn [sv_denot]; rewrite ?ew_ewset_other by lia
  end.
Ltac c4b_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; c4b_kio].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma c4b_val_at : forall E ss (H : word -> bool) ms i r off (n : N) e v b a,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) -> base_val E (YP09.r_base r) = b ->
sv_denot E e = Z_to_bv 64 v -> (N.to_nat n <= 8)%nat -> a = b + off ->
val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof.
intros E ss H ms i r off n e v b a HS Hi Hc Hb He Hn ->.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. specialize (Hok r (nth_error_In _ _ Hi)).
pose proof (YP09.region_ok_chunk rsegs E _ r _ Hok Hc) as Hck. rewrite Hb in Hck.
exact (c4b_val_of_chunk E _ b off n e v Hck He Hn).
Qed.

(* ---- the shadow entry over e62: e62 is in scope and lies outside the shadow band ---- *)
Lemma c4b_shok : forall (regs : bvmap 5 word) (H : word -> bool) mem (F pq m p : Z),
  getr regs 27 = w64 SHADOW_OFF -> in_app F 1024 ->
  range_addressable (aview rsegs H mem) SHADOW_OFF (F + 0x210) 104 ->
  sh_ok rsegs C4BBx c4b_SH (Ereg regs (c4b_extra F pq m p)) (mrestrict H mem).
Proof.
intros regs H mem F pq m p H27 Happ Hra.
set (E := Ereg regs (c4b_extra F pq m p)).
assert (U27 : U E (SOff 27 0) = SHADOW_OFF).
{ apply U_atom; [subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27 | unfold SHADOW_OFF; lia]. }
assert (U32 : U E (SOff 32 0) = F + 0x210).
{ apply U_atom; [subst E; exact (ew_Ereg_extra regs _ 0)|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. pose proof alloc_ceiling_val. lia. }
apply Forall_cons; [|apply Forall_nil]. unfold shent_ok. cbn [she_m she_lo she_hi].
unfold C4BBx. rewrite U27, U32. split.
- rewrite <- (aview_rd_of rsegs). replace (F + 0x210 + 0) with (F + 0x210) by lia. exact Hra.
- unfold app_apart. cbn [she_m she_lo she_hi]. unfold C4BBx. rewrite U27, U32.
  intros a Ha. change (Z.min 0 0x68) with 0 in Ha. change (Z.max 0 0x68) with 0x68 in Ha.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. pose proof alloc_ceiling_val. lia.
Qed.

(* ---- the entry state ---- *)
Lemma c4b_entry : forall (byte : bool) (W : world rsegs) (regs : bvmap 5 word) memc (R F c pq m p nl : Z),
  getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF -> getr regs 18 = w64 c -> getr regs 22 = w64 nl ->
  getr regs 20 = w64 1 ->
  2 <= c -> c <= 2 ^ 47 - 1 -> 0 <= pq < 2 ^ 64 -> 0 <= m < 256 -> 0 <= p < 2 ^ 64 ->
  4096 <= F -> F + 1024 <= alloc_ceiling -> alloc_ceiling <= R -> R + 0x200 <= 2 ^ 47 ->
  (byte = true -> 1 <= nl <= 2 ^ 47) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 pq ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 p ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 (F + 0x210) ->
  (forall o, 0 <= o < 12 -> apresent (w_H W) memc (F + 0x210 + o)) ->
  (byte = true -> val_mem rsegs (mrestrict (w_H W) memc) c 1 m /\
     (c + 1 <= R + 0x48 \/ R + 0x160 <= c) /\ (c + 1 <= F + 0x210 \/ F + 0x278 <= c)) ->
  st_ok rsegs (Ereg regs (c4b_extra F pq m p)) (c4b_ss byte)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 W6BB_D4) memc (seg_rom rsegs))).
Proof.
intros byte W regs memc R F c pq m p nl H9 H27 H18 H22 H20 Hc0 Hc1 Hpq Hm Hp HF0 HFc HcR HR1 Hnl V130 V140 V158
  Pe Hbyte.
pose proof alloc_ceiling_val as Hac.
rewrite restrict_mkst_fx.
set (E := Ereg regs (c4b_extra F pq m p)).
assert (U9 : bv_unsigned (ew E 9) = R) by (exact (c4b_u regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
assert (U18 : bv_unsigned (ew E 18) = c) by (exact (c4b_u regs _ 18 18%bv c eq_refl H18 ltac:(lia))).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E18 : ew E 18 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E22 : ew E 22 = Z_to_bv 64 nl) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E20 : ew E 20 = Z_to_bv 64 1) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E32 : ew E 32 = Z_to_bv 64 (F + 0x210)) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pq) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 m) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 p) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (U32 : bv_unsigned (ew E 32) = F + 0x210) by (rewrite E32; apply unsigned_lit_small; lia).
assert (RE : YP09.region_ok rsegs E (mrestrict (w_H W) memc) c4b_rE).
{ unfold YP09.region_ok, c4b_rE.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable rsegs). apply Pe. lia. }
assert (RQ : YP09.region_ok rsegs E (mrestrict (w_H W) memc) c4b_rQ).
{ unfold YP09.region_ok, c4b_rQ.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ R 0x130 8 (SOff 33 0) pq);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V130]. }
assert (RP : YP09.region_ok rsegs E (mrestrict (w_H W) memc) c4b_rP).
{ unfold YP09.region_ok, c4b_rP.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ R 0x140 8 (SOff 35 0) p);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V140]. }
assert (RA : YP09.region_ok rsegs E (mrestrict (w_H W) memc) c4b_rA).
{ unfold YP09.region_ok, c4b_rA.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ R 0x158 8 (SOff 32 0) (F + 0x210));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V158]. }
unfold c4b_ss. apply (entry_st_ok_full rsegs); try change (Ereg regs (c4b_extra F pq m p)) with E.
- apply regs_ok_Ereg.
- destruct byte; vm_compute; reflexivity.
- destruct byte; unfold c4b_regs; repeat apply Forall_cons; try apply Forall_nil; try assumption.
  destruct (Hbyte eq_refl) as (Vb & _ & _).
  unfold YP09.region_ok, c4b_rI.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U18.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ c 0 1 (SOff 34 0) m);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Vb.
- destruct byte; unfold c4b_regs, c4b_rE, c4b_rQ, c4b_rP, c4b_rA, c4b_rI;
    cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U18, ?U32.
  + destruct (Hbyte eq_refl) as (_ & D1 & D2). repeat split; first [exact I | lia].
  + repeat split; first [exact I | lia].
- unfold facts_ok. destruct byte; unfold c4b_facts, c4b_facts1, c4b_facts0;
    cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  + split; [|split; exact I]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
    * apply (c4b_af _ _ _ _ _ _ E27); unfold SHADOW_OFF;
        first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * apply (c4b_af _ _ _ _ _ _ E18); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * apply (c4b_af _ _ _ _ _ _ E32); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * pose proof (Hnl eq_refl) as Hnl'.
      apply (c4b_af _ _ _ _ _ _ E22); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * apply (c4b_af _ _ _ _ _ _ E34); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * apply (c4b_af _ _ _ _ _ _ E20); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
  + split; [|split; exact I]. split; [|split; [|split; [|exact I]]].
    * apply (c4b_af _ _ _ _ _ _ E27); unfold SHADOW_OFF;
        first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * apply (c4b_af _ _ _ _ _ _ E18); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
    * apply (c4b_af _ _ _ _ _ _ E32); first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)].
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ======================================== the block lemma ======================================== *)
Theorem w6bb_c4 : w6bb_c4_stmt B MT.
Proof using MTL.
unfold w6bb_c4_stmt, w6bb_case_stmt. cbv beta.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp b r Hctx HP Hin _.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & HRom).
unfold w6bb_in in Hin.
destruct Hin as (Hr2 & Hr3 & Hr4 & H9 & H27 & H19 & H18 & H16 & H22 & H6 & H20 & H13 & M48 & Mf0 & M110
  & M130 & M140 & M158 & Hkd & Hpp0 & Hpp1 & HF0 & HFc & HF32 & HFapp & Hez & Hra & Hhull & Hc1 & Hwin).
destruct Hwin as (Hg & Hrain & Hc0 & Hcb & Ham & Hhull2 & Hdis).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
pose proof alloc_ceiling_val as Hac.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF32' & _ & HFpres & _).
rewrite <- HFa in HFpres.
change (fs_frame_bytes 4) with 1024 in HFpres.
unfold T_SEG_STK, ASTACK in HspR.
assert (HcR : alloc_ceiling <= R) by lia.
assert (HR1 : R + 0x200 <= 2 ^ 47) by lia.
assert (Hpe : forall o, 0 <= o < 12 -> apresent (w_H W) memc (F + 0x210 + o))
  by (intros o Ho; exact (proj1 (HFpres (F + 0x210 + o) ltac:(lia)))).
assert (Hcmax : c + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
assert (Hpq : 0 <= pp + 0x4000 < 2 ^ 64) by lia.
assert (Hp : 0 <= pp < 2 ^ 64) by lia.
unfold cfg_at. change (w64 W6BB_D4) with (Z_to_bv 64 W6BB_D4).
destruct r as [|b1 r1].
- (* ============ no byte left: v = 0, 0x81338 .. J ============ *)
  pose proof (c4b_entry false W regs memc R F c (pp + 0x4000) 0 pp _ H9 H27 H18 H22 H20
    ltac:(lia) ltac:(cbn [length] in Hcmax; lia) Hpq ltac:(lia) Hp HF0 HFc HcR HR1
    ltac:(discriminate) M130 M140 M158 Hpe ltac:(discriminate)) as HS0.
  pose proof (st_ok_pin_lit rsegs _ _ _ (22%bv : bv 5) 0 HS0 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H22; reflexivity)) as HS.
  clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts c4b_ss] in HS.
  assert (SHOK : sh_ok rsegs C4BBx c4b_SH (Ereg regs (c4b_extra F (pp + 0x4000) 0 pp)) (mrestrict (w_H W) memc))
    by (apply (c4b_shok regs (w_H W) memc F (pp + 0x4000) 0 pp H27 HFapp Hra)).
  assert (HAE : env_agree 32 (Ereg regs (c4b_extra F (pp + 0x4000) 0 pp))
                  (Ereg regs (c4b_extra F (pp + 0x4000) 0 pp)))
    by apply env_agree_refl.
  assert (E32 : ew (Ereg regs (c4b_extra F (pp + 0x4000) 0 pp)) 32 = Z_to_bv 64 (F + 0x210))
    by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs (c4b_extra F (pp + 0x4000) 0 pp)) 33 = Z_to_bv 64 (pp + 0x4000))
    by exact (ew_Ereg_extra regs _ 1).
  assert (E35 : ew (Ereg regs (c4b_extra F (pp + 0x4000) 0 pp)) 35 = Z_to_bv 64 pp)
    by exact (ew_Ereg_extra regs _ 3).
  assert (U32 : bv_unsigned (ew (Ereg regs (c4b_extra F (pp + 0x4000) 0 pp)) 32) = F + 0x210)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (Ereg regs (c4b_extra F (pp + 0x4000) 0 pp)) 9) = R)
    by (exact (c4b_u regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  assert (U18 : bv_unsigned (ew (Ereg regs (c4b_extra F (pp + 0x4000) 0 pp)) 18) = c)
    by (exact (c4b_u regs _ 18 18%bv c eq_refl H18 ltac:(lia))).
  aj_run_to_tok w6bb_tbl_ok HS HJ SHOK C4Bspan W6BB_J.
  + (* the write rights of e62 *)
    lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ow) end.
    eapply (rl_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0x210);
      [ reflexivity | rewrite <- HFa; exact U32 | exact Hown
      | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    awr_ok_tac.
  + (* the leaf at J *)
    assert (KEEPR : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr w6bb_clob ->
      getr (ms_regs ms) rr = getr regs rr)
      by (eapply (regs_kept_of_st_ok rsegs _ _ ms regs (c4b_extra F (pp + 0x4000) 0 pp) (w_H W) _ HS);
          [env_agree_chain HAE | vm_compute; reflexivity]).
    assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x210 <= a < F + 0x21c) ->
      mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) a = mbyte rsegs (mrestrict (w_H W) memc) a).
    { intros a Ha Hn. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
      intros (rg & Hin & Hr). apply Hn. rewrite unsigned_lit_small in Hr by lia.
      cbn [ss_mem c4b_ss c4b_regs In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c4b_rE c4b_rQ c4b_rP c4b_rA] in Hr;
        rewrite ?U9, ?U32 in Hr; lia. }
    apply SRr_ret. red.
    exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
    split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
    split; [exact HJ|].
    split; [exact KEEPR|].
    split; [reflexivity|].
    split; [apply Permutation_refl|].
    split; [c4b_kio|].
    split; [apply mo_le_refl; exact MTL|].
    split; [intros a Ha Hn; unfold aview;
            rewrite (KEEPB a Ha ltac:(intros X; apply Hn; unfold w6bb_wr; right; right; right; lia)); reflexivity|].
    unfold w6bb_J_R. rewrite (c4b_model b (@nil byte) HP). cbn [fst snd fuzz_u8].
    split; [c4b_regv HS (22%bv : bv 5); rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [c4b_regv HS (15%bv : bv 5); rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [c4b_regv HS (13%bv : bv 5); rewrite U18; unfold w64; f_equal; cbn [length]; lia|].
    split; [c4b_regv HS (6%bv : bv 5); unfold w64; f_equal; cbn [length]; lia|].
    (* e62's 104 bytes *)
    assert (V0 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x210) 4 POD_BOOL)
      by (eapply (c4b_val_at _ _ (w_H W) ms 0%nat _ 0 4%N (SLit 2) POD_BOOL (F + 0x210) _);
          [exact HS | reflexivity | c4b_in | c4b_b32 U32 | reflexivity | cbn; lia | lia]).
    assert (V4 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x214) 4 4)
      by (eapply (c4b_val_at _ _ (w_H W) ms 0%nat _ 4 4%N (SLit 4) 4 (F + 0x210) _);
          [exact HS | reflexivity | c4b_in | c4b_b32 U32 | reflexivity | cbn; lia | lia]).
    assert (V8 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x218) 4 (0 mod 3))
      by (eapply (c4b_val_at _ _ (w_H W) ms 0%nat _ 8 4%N (SLit 0) (0 mod 3) (F + 0x210) _);
          [exact HS | reflexivity | c4b_in | c4b_b32 U32 | reflexivity | cbn; lia | lia]).
    assert (VZ : garr8 rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x21c) (repeat 0 92)).
    { apply garr8_zeros. intros a Ha. cbn [Z.of_nat] in Ha.
      rewrite (KEEPB a ltac:(lia) ltac:(lia)).
      replace a with (F + 0x210 + (a - (F + 0x210))) by lia. apply Hez. lia. }
    rewrite c4b_ent_mem, !map_app, c4b_map_zeros.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RPgMem.rm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0x210) 4%nat POD_BOOL V0)|].
    rewrite length_map, length_le32. replace (F + 0x210 + Z.of_nat 4) with (F + 0x214) by lia.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RPgMem.rm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0x214) 4%nat 4 V4)|].
    rewrite length_map, length_le32. replace (F + 0x214 + Z.of_nat 4) with (F + 0x218) by lia.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RPgMem.rm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0x218) 4%nat (0 mod 3) V8)|].
    rewrite length_map, length_le32. replace (F + 0x218 + Z.of_nat 4) with (F + 0x21c) by lia.
    exact VZ.
- (* ============ a byte: v = b1, 0x80f38 .. J ============ *)
  pose proof (Cursor.byte_range b1) as Hmb.
  assert (HD : c + 1 <= R + 0x48 \/ R + 0x160 <= c)
    by (pose proof (Hdis c ltac:(cbn [length]; lia)) as Hq; destruct Hq as (Hq1 & Hq2 & Hq3); lia).
  assert (HDF : c + 1 <= F + 0x210 \/ F + 0x278 <= c)
    by (pose proof (Hdis c ltac:(cbn [length]; lia)) as Hq; destruct Hq as (Hq1 & Hq2 & Hq3); lia).
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) c 1 (bv_unsigned b1))
    by (destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]; rewrite Z.add_0_r in Hv; exact Hv).
  pose proof (c4b_entry true W regs memc R F c (pp + 0x4000) (bv_unsigned b1) pp _ H9 H27 H18 H22 H20
    ltac:(lia) ltac:(cbn [length] in Hcmax; lia) Hpq Hmb Hp HF0 HFc HcR HR1
    ltac:(intros _; cbn [length] in Hcmax |- *; lia) M130 M140 M158 Hpe
    ltac:(intros _; split; [exact Hm0|]; split; [exact HD | exact HDF])) as HS.
  assert (SHOK : sh_ok rsegs C4BBx c4b_SH (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp))
                   (mrestrict (w_H W) memc))
    by (apply (c4b_shok regs (w_H W) memc F (pp + 0x4000) (bv_unsigned b1) pp H27 HFapp Hra)).
  assert (HAE : env_agree 32 (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp))
                  (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp))) by apply env_agree_refl.
  assert (E16 : ew (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp)) 16 = Z_to_bv 64 (c - 1))
    by (rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16).
  assert (E6 : ew (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp)) 6
                  = Z_to_bv 64 (Z.of_nat (length (b1 :: r1)) + 1))
    by (rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6).
  assert (E27 : ew (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp)) 27 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E18 : ew (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp)) 18 = Z_to_bv 64 c)
    by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E32 : ew (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp)) 32 = Z_to_bv 64 (F + 0x210))
    by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp)) 33 = Z_to_bv 64 (pp + 0x4000))
    by exact (ew_Ereg_extra regs _ 1).
  assert (E34 : ew (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp)) 34 = Z_to_bv 64 (bv_unsigned b1))
    by exact (ew_Ereg_extra regs _ 2).
  assert (E35 : ew (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp)) 35 = Z_to_bv 64 pp)
    by exact (ew_Ereg_extra regs _ 3).
  assert (U32 : bv_unsigned (ew (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp)) 32) = F + 0x210)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp)) 9) = R)
    by (exact (c4b_u regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  assert (U18 : bv_unsigned (ew (Ereg regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp)) 18) = c)
    by (exact (c4b_u regs _ 18 18%bv c eq_refl H18 ltac:(lia))).
  aj_run_to_tok w6bb_tbl_ok HS HJ SHOK C4Bspan W6BB_J.
  + (* the check's obligation: the input byte is addressable *)
    apply (obl_of_range rsegs (w_H W) memc _ C4BBx _ _ c (Z.of_nat (length (b1 :: r1))) Hrain).
    * exact (U_atom _ 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)).
    * rewrite (U_atom _ 18 c E18 ltac:(lia)). lia.
    * rewrite (U_atom _ 18 c E18 ltac:(lia)). cbn [length]. lia.
  + (* the write rights of e62 *)
    lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ow) end.
    eapply (rl_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0x210);
      [ reflexivity | rewrite <- HFa; exact U32 | exact Hown
      | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    awr_ok_tac.
  + (* the leaf at J *)
    assert (KEEPR : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr w6bb_clob ->
      getr (ms_regs ms) rr = getr regs rr)
      by (eapply (regs_kept_of_st_ok rsegs _ _ ms regs (c4b_extra F (pp + 0x4000) (bv_unsigned b1) pp) (w_H W) _ HS);
          [env_agree_chain HAE | vm_compute; reflexivity]).
    assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x210 <= a < F + 0x21c) ->
      mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) a = mbyte rsegs (mrestrict (w_H W) memc) a).
    { intros a Ha Hn. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
      intros (rg & Hin & Hr). apply Hn. rewrite unsigned_lit_small in Hr by lia.
      cbn [ss_mem c4b_ss c4b_regs In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c4b_rE c4b_rQ c4b_rP c4b_rA c4b_rI] in Hr;
        rewrite ?U9, ?U18, ?U32 in Hr; lia. }
    apply SRr_ret. red.
    exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
    split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
    split; [exact HJ|].
    split; [exact KEEPR|].
    split; [reflexivity|].
    split; [apply Permutation_refl|].
    split; [c4b_kio|].
    split; [apply mo_le_refl; exact MTL|].
    split; [intros a Ha Hn; unfold aview;
            rewrite (KEEPB a Ha ltac:(intros X; apply Hn; unfold w6bb_wr; right; right; right; lia)); reflexivity|].
    unfold w6bb_J_R. rewrite (c4b_model b (b1 :: r1) HP). cbn [fst snd fuzz_u8].
    split; [c4b_regv HS (22%bv : bv 5); rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [c4b_regv HS (15%bv : bv 5); rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [c4b_regv HS (13%bv : bv 5); rewrite E16, unsigned_lit_small by lia;
            unfold w64; f_equal; cbn [length]; lia|].
    split; [c4b_regv HS (6%bv : bv 5); rewrite E6, unsigned_lit_small by (cbn [length] in Hcmax |- *; lia);
            unfold w64; f_equal; cbn [length]; lia|].
    (* e62's 104 bytes *)
    assert (V0 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x210) 4 POD_BOOL)
      by (eapply (c4b_val_at _ _ (w_H W) ms 0%nat _ 0 4%N (SLit 2) POD_BOOL (F + 0x210) _);
          [exact HS | reflexivity | c4b_in | c4b_b32 U32 | reflexivity | cbn; lia | lia]).
    assert (V4 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x214) 4 4)
      by (eapply (c4b_val_at _ _ (w_H W) ms 0%nat _ 4 4%N (SLit 4) 4 (F + 0x210) _);
          [exact HS | reflexivity | c4b_in | c4b_b32 U32 | reflexivity | cbn; lia | lia]).
    assert (V8 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x218) 4 (bv_unsigned b1 mod 3)).
    { eapply (c4b_val_at _ _ (w_H W) ms 0%nat _ 8 4%N c4b_a0 (bv_unsigned b1 mod 3) (F + 0x210) _);
      [exact HS | reflexivity | c4b_in | c4b_b32 U32 | | cbn; lia | lia].
      apply c4b_a0_val; [rewrite ?ew_ewset_other by lia; exact E34 | exact Hmb]. }
    assert (VZ : garr8 rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x21c) (repeat 0 92)).
    { apply garr8_zeros. intros a Ha. cbn [Z.of_nat] in Ha.
      rewrite (KEEPB a ltac:(lia) ltac:(lia)).
      replace a with (F + 0x210 + (a - (F + 0x210))) by lia. apply Hez. lia. }
    rewrite c4b_ent_mem, !map_app, c4b_map_zeros.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RPgMem.rm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0x210) 4%nat POD_BOOL V0)|].
    rewrite length_map, length_le32. replace (F + 0x210 + Z.of_nat 4) with (F + 0x214) by lia.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RPgMem.rm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0x214) 4%nat 4 V4)|].
    rewrite length_map, length_le32. replace (F + 0x214 + Z.of_nat 4) with (F + 0x218) by lia.
    apply (proj2 (garr8_app rsegs _ _ _ _)). split;
      [exact (RPgMem.rm_bytes_of_val rsegs (w_H W) (ms_mem ms) (F + 0x218) 4%nat
                (bv_unsigned b1 mod 3) V8)|].
    rewrite length_map, length_le32. replace (F + 0x218 + Z.of_nat 4) with (F + 0x21c) by lia.
    exact VZ.
Qed.

End d.
End b.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 285 of its 313 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Close.v at dc0c32440025 for reac-pw/fuzz_rate's
   image A: module paths changed; rate's pcs (CL 0x82484 -> LATCH 0x82528), registers (s6 / s7 / s2 for role's
   s4 / s5 / s7) and real-frame cells (at R+0xe0, first R+0x110, the cursor R+0x100, &has_params R+0x88,
   &params_struct R+0x70 for role's R+0xa0 / 0xd0 / 0xc8 / 0x50 / 0x40); the real frame is 0x1e0 bytes; rm_ / rl_
   become rtm_ / rt_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW5Close.v at a66696a9b1d1 for the same
   unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; image B's pcs (CL 0x824c0 -> LATCH 0x82578),
   registers (s2 = &pp->len, s4 = the shadow offset, s9 = what is left of the input, which moves to t4) and real-frame
   cells (the shadow address of &pp->len R+0x170, the property count R+0xb0, pp + at R+0xa8, at R+0xa0, ~pp R+0x108,
   &has_params R+0x90, first R+0x160, &params_struct R+0x68); the two UBSan trap branches 0x824e0 / 0x824f0, decided
   by the atom ranges of at and ~pp; no real-frame cell is written; the real frame is 0x220 bytes; the prefix w5_
   becomes w5b_ and rtm_ becomes rtmb_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgW5CloseB.v, with its module paths, module names, addresses and numbers changed; 78 of its 318 lines of code are new or changed and 73 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Close.v at dc0c32440025 for reac-pw/fuzz_rate's
   image A: module paths changed; rate's pcs (CL 0x82484 -> LATCH 0x82528), registers (s6 / s7 / s2 for role's
   s4 / s5 / s7) and real-frame cells (at R+0xe0, first R+0x110, the cursor R+0x100, &has_params R+0x88,
   &params_struct R+0x70 for role's R+0xa0 / 0xd0 / 0xc8 / 0x50 / 0x40); the real frame is 0x1e0 bytes; rm_ / rl_
   become rtm_ / rt_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW5Close.v at a66696a9b1d1 for the same
   unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; image B's pcs (CL 0x824c0 -> LATCH 0x82578),
   registers (s2 = &pp->len, s4 = the shadow offset, s9 = what is left of the input, which moves to t4) and real-frame
   cells (the shadow address of &pp->len R+0x170, the property count R+0xb0, pp + at R+0xa8, at R+0xa0, ~pp R+0x108,
   &has_params R+0x90, first R+0x160, &params_struct R+0x68); the two UBSan trap branches 0x824e0 / 0x824f0, decided
   by the atom ranges of at and ~pp; no real-frame cell is written; the real frame is 0x220 bytes; the prefix w5_
   becomes w5b_ and rtm_ becomes rtmb_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW5CloseB.v at 2ebedbb4253d for reac-pw/fuzz_role's
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; role B's pcs
   (CL 0x81ccc -> LATCH 0x81d84, the trap branches 0x81cec / 0x81cf8), registers (s6 = &pp->len, s11 = the shadow
   offset, s4 = 1 the value of the two flag stores, what is left in s2 and the cursor in s8, which move to t3 / a7,
   the property index into t1) and real-frame cells (the shadow address of &pp->len R+0x148, the property count
   R+0x98, pp + at R+0x88, at R+0x90, ~pp R+0xf8, &has_params R+0x78, first R+0x138, &params_struct R+0x50); the real
   frame is 0x200 bytes; the kit names are lib/AU/RPgMem.v's rm_ and RPgW5Kit.v's w5_; the prefixes w5b_ / rtmb_ become
   w5_ / rm_. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses from the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): the params Struct's close, CL 0x81ccc ->
   LATCH 0x81d84, in LLVMFuzzerTestOneInput (pod.h:434-437). Proves no function (kind: segment lemma).

   THE CODE
     0x81ccc  ld a0,0x148(s1); lbu a0,0(a0); bnez a0 -> 0x8282c   the check of the 8-byte load of pp->len (R+0x148 =
                                                                  (pp+0x4000)>>3 + K); its error path is 0x8282c
     0x81cd8  a0 = 0x4001; t1 = |ps| (R+0x98); a4 = pp + 0x400c (R+0x78); a6 = at (R+0x90)
     0x81cec  bgeu a6,a0 -> 0x82604 (UBSan trap: at >= 16385)
     0x81cf0  a0 = ~pp (R+0xf8); a5 = pp + at (R+0x88)
     0x81cf8  bltu a0,a6 -> 0x82604 (UBSan trap: ~pp < at, pp + at wraps)
     0x81cfc  t3 = s2 (what is left); a7 = s8 (the cursor)
     0x81d04-0x81d14  the check of the first byte of the 4-byte store at pp + at (slow block 0x81dc4, error path
                      0x8297c); a1 = len (s6)
     0x81d18-0x81d28  the check of its last byte pp + at + 3 (slow block 0x81dd0, error path 0x82988)
     0x81d2c  subw a0,a1,a6; addi a0,a0,-8      len - at - 8
     0x81d34-0x81d4c  the four `sb` of pod_patch32(pp, at, len - at - 8)
     0x81d50  ld a0,0x138(s1) (first); 0x81d54 beqz a0 -> 0x81d84
     0x81d58-0x81d6c  first: the check of pp + 0x400c (slow block 0x81e28, error path 0x829c8), has_params := s4 = 1
     0x81d70-0x81d80  first: the check of pp + 0x4010 (R+0x50; slow block 0x81e38, error path 0x829d0),
                      params_struct := 1
   Every check is on pp's bytes, covered by the shadow entries (33, 0x4000, 0x4018) and (34, 0, 16) of
   w5_shent_blk (atom 33 = pp, atom 34 = pp + at): its shadow byte reads as 0, so each `bnez` is decided and the
   error paths are not reached. The two trap branches are decided by the closed-numeral ranges of the atoms at
   (35, [16, 5440]) and ~pp (37, [2^64 - 1 - 0x7fffff800000, 2^64 - 1 - 4096]). first is 0 or 1 by the start state;
   the walk takes the two values as two runs, so `beqz` is decided. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgMem RPgW5Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the start state at 0x81ccc: atoms 33 = pp, 34 = pp + atv, 35 = atv, 36 = len, 37 = ~pp (as an unsigned
   word), 38 = the property count; sp = s1's atom, s6 = &pp->len, s11 = the shadow offset, s4 = 1 ---- *)
Definition cl_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((22%bv : bv 5), SOff 33 0x4000); ((27%bv : bv 5), w5_Bx);
   ((20%bv : bv 5), SLit 1)].
Definition cl_slots (f : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x50 0x150 0 0
   [YP09.mkChunk 0x50 (CVal 8 (SOff 33 0x4010)); YP09.mkChunk 0x78 (CVal 8 (SOff 33 0x400c));
    YP09.mkChunk 0x88 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x90 (CVal 8 (SOff 35 0));
    YP09.mkChunk 0x98 (CVal 8 (SOff 38 0)); YP09.mkChunk 0xf8 (CVal 8 (SOff 37 0));
    YP09.mkChunk 0x138 (CVal 8 (SLit f)); YP09.mkChunk 0x148 (CVal 8 (w5_sh 33 0x4000))].
Definition cl_fields (f : Z) : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x4000 0x4018 0x400c (0x400c + 8 * f)
   [YP09.mkChunk 0x4000 (CVal 8 (SOff 36 0))].
Definition cl_at : YP09.region := YP09.mkRegion (Some 34%nat) 0 4 0 4 [].
Definition cl_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF W5_SB W5_SB 0);
           (33%nat, mkAF 4096 140737479966720 4); (34%nat, mkAF 4096 140737479966720 0);
           (35%nat, mkAF 16 5440 0); (36%nat, mkAF 16 5440 0);
           (37%nat, mkAF 18446603336229584895 18446744073709547519 0)]
   [] [].
Definition ss_cl (f : Z) : sstate := mkSS 0x81ccc (w5_sr cl_ov) [cl_slots f; cl_fields f; cl_at] None cl_facts.
Definition cl_SH : list shent := [mkSHE 33 0x4000 0x4018; mkSHE 34 0 16].
Definition cl_extra (pp atv len nps : Z) : list word :=
  [w64 W5_SB; w64 pp; w64 (pp + atv); w64 atv; w64 len; w64 (18446744073709551615 - pp); w64 nps].

(* the value the four `sb` store: len - atv - 8, as the engine computes it from `subw` and `addi` *)
Definition cl_X : sv := SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 35 0) (SLit 18446744073709551615)) (SLit (-8))) (SOff 36 0).
Lemma cl_zc : forall x q r, 0 <= r < 18446744073709551616 -> x = 18446744073709551616 * q + r -> zcanon x = r.
Proof.
intros x q r Hr Hx. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos x 18446744073709551616 q r Hr Hx).
Qed.
Lemma cl_U_X : forall E atv len, ew E 35 = Z_to_bv 64 atv -> ew E 36 = Z_to_bv 64 len ->
0 < atv < 2 ^ 32 -> 0 <= len < 2 ^ 32 -> atv + 8 <= len -> U E cl_X = len - atv - 8.
Proof.
intros E atv len H35 H36 Ha Hl Hal. unfold cl_X.
rewrite !U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite (U_atom E 35 atv H35), (U_atom E 36 len H36), !U_SLit by lia.
rewrite (zcanon_id 18446744073709551615) by (unfold M64; lia).
rewrite (cl_zc (atv * 18446744073709551615) (atv - 1) (18446744073709551616 - atv)) by lia.
rewrite (cl_zc (-8) (-1) (18446744073709551616 - 8)) by lia.
rewrite (cl_zc (18446744073709551616 - atv + (18446744073709551616 - 8)) 1 (18446744073709551616 - atv - 8)) by lia.
apply (cl_zc _ 1); lia.
Qed.
Lemma cl_U_Xs : forall E atv len k, ew E 35 = Z_to_bv 64 atv -> ew E 36 = Z_to_bv 64 len ->
0 < atv < 2 ^ 32 -> 0 <= len < 2 ^ 32 -> atv + 8 <= len -> (k = 8 \/ k = 16 \/ k = 24) ->
U E (SAlu ALU_SRL cl_X (SLit k)) = Z.shiftr (len - atv - 8) k.
Proof.
intros E atv len k H35 H36 Ha Hl Hal Hk. rewrite U_SAlu. cbn [zalu_raw]. rewrite (cl_U_X E atv len) by assumption.
rewrite U_SLit.
assert (HL : Z.land (zcanon k) 63 = k) by (destruct Hk as [-> | [-> | ->]]; reflexivity).
rewrite HL.
assert (0 <= Z.shiftr (len - atv - 8) k <= len - atv - 8).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). nia. }
apply zcanon_id. unfold M64. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma w5_close_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv len fsv nps nr cur : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 22 = w64 (pp + 0x4000) ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 20 = w64 1 -> getr regs 18 = w64 nr -> getr regs 24 = w64 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 (shadow_addr (pp + 0x4000)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x98) 8 nps ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x88) 8 (pp + atv) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x90) 8 atv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (18446744073709551615 - pp) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x78) 8 (pp + 0x400c) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 fsv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x50) 8 (pp + 0x4010) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 len ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x200 <= sp0 ->
  16 <= atv -> atv + 8 <= len -> len <= 5440 -> (fsv = 0 \/ fsv = 1) -> 0 <= nps < 2 ^ 64 -> 0 <= nr < 2 ^ 64 ->
  0 <= cur < 2 ^ 64 ->
  SRr rsegs W (cfg_at rsegs 0x81ccc regs memc mdc)
    (w5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x81d84
      [6; 10; 11; 12; 13; 14; 15; 16; 17; 28]%bv
      (fun a => (pp + atv <= a < pp + atv + 4) \/ (fsv = 1 /\ pp + 0x400c <= a < pp + 0x4014))
      (fun W2 regs2 mem2 =>
        rm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 (len - atv - 8)) /\
        (fsv = 1 -> rm_bytes rsegs (w_H W2) mem2 (pp + 0x400c) (Z_to_le_bytes 4 1) /\
                    rm_bytes rsegs (w_H W2) mem2 (pp + 0x4010) (Z_to_le_bytes 4 1)) /\
        getr regs2 6 = w64 nps /\ getr regs2 28 = w64 nr /\ getr regs2 17 = w64 cur)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv len fsv nps nr cur
  HJ Hpp Hfresh H2 H9 H22 H27 H20 H18 H24 V148 V98 V88 V90 Vf8 V78 V138 V50 Vlen HR16 HRlo HRhi Hat Hal Hlen Hfst
  Hnps Hnr Hcur.
pose proof w5_wx as Hwx. pose proof w5_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh.
assert (HSA : 0 <= shadow_addr (pp + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  pose proof (Z.div_pos (pp + 0x4000) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (pp + 0x4000) 8 (pp + 0x4000) ltac:(lia) ltac:(lia)). lia. }
set (E := Ereg regs (cl_extra pp atv len nps)).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = w64 nr) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E24 : ew E 24 = w64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E32 : ew E 32 = Z_to_bv 64 W5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 len) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = w64 (18446744073709551615 - pp)) by (subst E; exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = w64 nps) by (subst E; exact (ew_Ereg_extra regs _ 6)).
assert (HE : E = Ereg regs (cl_extra pp atv len nps)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs w5_Bx cl_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (w5_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4018 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (w5_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 34 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W5_SB) by (rewrite E32; apply unsigned_lit_small; unfold W5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = pp + atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = atv) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = len) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = 18446744073709551615 - pp) by (rewrite E37; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w5_sr cl_ov) regs).
{ apply (w5_regs_ok E regs (cl_extra pp atv len nps)); [exact HE|]. unfold cl_ov.
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_off E 33 pp 0x4000 E33) by lia. rewrite H22. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold w5_Bx. rewrite (w5_den_off E 32 W5_SB 0 E32) by (unfold W5_SB; lia).
    rewrite Z.add_0_r, H27. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd sv_denot]. rewrite H20. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E cl_facts).
{ split; [| split; [exact I | exact I]].
  cbn [cl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33, U34, U35, U36, U37.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ]. }
destruct Hfst as [-> | ->].
all: lazymatch goal with Vd : val_mem _ _ (_ + 0x138) 8 ?f |- _ =>
  assert (HS : st_ok rsegs E (ss_cl f) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81ccc) memc (seg_rom rsegs))));
  [ rewrite restrict_mkst_fx; unfold ss_cl; apply (w5_entry rsegs _ _ regs (cl_extra pp atv len nps) E); [exact HE| | | | |];
    [ exact HR0
    | vm_compute; reflexivity
    | unfold cl_slots, cl_fields, cl_at;
      repeat apply Forall_cons; try apply Forall_nil;
      first
      [ apply (rm_ro_region rsegs E (w_H W) memc 9 R); [ exact U9 | lia | lia | ];
        repeat apply Forall_cons; try apply Forall_nil;
        first
        [ apply (chunk_ok_val rsegs E _ R 0x50 8 (SOff 33 0x4010) (pp + 0x4010));
          [ rewrite (w5_den_off E 33 pp 0x4010 E33) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V50 ]
        | apply (chunk_ok_val rsegs E _ R 0x78 8 (SOff 33 0x400c) (pp + 0x400c));
          [ rewrite (w5_den_off E 33 pp 0x400c E33) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V78 ]
        | apply (chunk_ok_val rsegs E _ R 0x88 8 (SOff 34 0) (pp + atv));
          [ rewrite (w5_den_off E 34 (pp + atv) 0 E34) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V88 ]
        | apply (chunk_ok_val rsegs E _ R 0x90 8 (SOff 35 0) atv);
          [ rewrite (w5_den_off E 35 atv 0 E35) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V90 ]
        | apply (chunk_ok_val rsegs E _ R 0x98 8 (SOff 38 0) nps);
          [ rewrite (w5_den_off E 38 nps 0 E38) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V98 ]
        | apply (chunk_ok_val rsegs E _ R 0xf8 8 (SOff 37 0) (18446744073709551615 - pp));
          [ rewrite (w5_den_off E 37 (18446744073709551615 - pp) 0 E37) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vf8 ]
        | apply (chunk_ok_val rsegs E _ R 0x138 8 (SLit f) f);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vd ]
        | apply (chunk_ok_val rsegs E _ R 0x148 8 (w5_sh 33 0x4000) (shadow_addr (pp + 0x4000)));
          [ rewrite (w5_den_sh E 33 pp 0x4000 E33 E32) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V148 ] ]
      | apply (rm_rw_region rsegs E (w_H W) memc 33 pp);
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 36 0) len);
        [ rewrite (w5_den_off E 36 len 0 E36) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ]
      | apply (rm_rw_region rsegs E (w_H W) memc 34 (pp + atv));
        [ exact U34 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ] ]
    | unfold cl_slots, cl_fields, cl_at; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
      cbn [r_base r_lo r_hi base_val]; rewrite U9, U33, U34; repeat split; try exact I; lia
    | exact HFK ]
  | ] end.
all: unfold cfg_at; change (w64 0x81ccc) with (Z_to_bv 64 0x81ccc).
all: aj_run_to_tok w5_tbl_ok HS HJ Hsh w5_Bspan 0x81d84.
(* the write windows: the size word and the flag words in pp *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat pp);
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rl_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (pp + atv));
    [ reflexivity | exact U34
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rl_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ]).
(* the end state at 0x81d84 *)
all: apply SRr_ret; unfold w5_post.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
    exact (w5_regs_kept E Ef 40 (w5_sr cl_ov) (ss_regs ssf) regs (ms_regs msf)
             [6; 10; 11; 12; 13; 14; 15; 16; 17; 28]%bv HR0 HRf
             (env_agree_refl 40 E) ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply w5_same_io_wvb]|];
  split; [apply mo_le_refl; assumption|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hst := fresh "Hst" in let Hn := fresh "Hn" in
    intros a Ha Hst Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (w5_kept_run rsegs E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U33, ?U34 in Hb; apply Hn; lia | ]);
    destruct Hr
  | ] end.
(* what the piece wrote, from the end state's regions, and the three registers it set *)
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  let HM := fresh "HM" in pose proof HSf as (_ & _ & _ & _ & _ & _ & _ & (_ & HM & _) & _);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rs := fresh "Rs" in let Rf := fresh "Rf" in let Ra := fresh "Ra" in
  apply Forall_cons_iff in HM as [Rs HM]; apply Forall_cons_iff in HM as [Rf HM];
  apply Forall_cons_iff in HM as [Ra _];
  let Cs := fresh "Cs" in let Cf := fresh "Cf" in let Ca := fresh "Ca" in
  destruct Rs as (_ & _ & _ & Cs); destruct Rf as (_ & _ & _ & Cf); destruct Ra as (_ & _ & _ & Ca);
  cbn [r_chunks r_base base_val] in Cs, Cf, Ca; rewrite U9 in Cs; rewrite U33 in Cf; rewrite U34 in Ca;
  rewrite Forall_forall in Cs, Cf, Ca;
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _)
  end.
all: assert (M0 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 0) = Some (Z_to_bv 8 (len - atv - 8))).
all: try (rewrite <- (cl_U_X E atv len E35 E36) by lia; apply (w5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: assert (M1 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 1) =
  Some (Z_to_bv 8 (Z.shiftr (len - atv - 8) 8))).
all: try (rewrite <- (cl_U_Xs E atv len 8 E35 E36) by lia; apply (w5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: assert (M2 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 2) =
  Some (Z_to_bv 8 (Z.shiftr (len - atv - 8) 16))).
all: try (rewrite <- (cl_U_Xs E atv len 16 E35 E36) by lia; apply (w5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: assert (M3 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 3) =
  Some (Z_to_bv 8 (Z.shiftr (len - atv - 8) 24))).
all: try (rewrite <- (cl_U_Xs E atv len 24 E35 E36) by lia; apply (w5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: split;
  [ apply rm_bytes_aview; intros i Hi; rewrite length_Z_to_le_bytes in Hi;
    rewrite rm_nth_le_bytes by lia; unfold aview;
    destruct i as [|[|[|[|i]]]]; [| | | | lia];
    [ change (Z.of_nat 0) with 0; rewrite M0; cbn [option_map]; rewrite Z.mul_0_r, Z.shiftr_0_r; reflexivity
    | change (Z.of_nat 1) with 1; rewrite M1; reflexivity
    | change (Z.of_nat 2) with 2; rewrite M2; reflexivity
    | change (Z.of_nat 3) with 3; rewrite M3; reflexivity ]
  |].
all: split;
  [ intros Hf1; try discriminate Hf1; split; apply rm_bytes_of_val;
    first
    [ apply (val_of_chunk_ok rsegs E _ pp 0x400c 4 (SLit 1) 1);
      [ apply Cf; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | lia ]
    | apply (val_of_chunk_ok rsegs E _ pp 0x4010 4 (SLit 1) 1);
      [ apply Cf; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | lia ] ]
  |].
all: split;
  [ transitivity (sv_denot E (SOff 38 0));
    [ exact (HRf 6%bv) | rewrite (w5_den_off E 38 nps 0 E38) by lia; rewrite Z.add_0_r; reflexivity ] |].
all: split;
  [ transitivity (sv_denot E (SOff 18 0));
    [ exact (HRf 28%bv) | rewrite (w5_den_off E 18 nr 0 E18) by lia; rewrite Z.add_0_r; reflexivity ] |].
all: transitivity (sv_denot E (SOff 24 0));
  [ exact (HRf 17%bv) | rewrite (w5_den_off E 24 cur 0 E24) by lia; rewrite Z.add_0_r; reflexivity ].
Qed.
End c.

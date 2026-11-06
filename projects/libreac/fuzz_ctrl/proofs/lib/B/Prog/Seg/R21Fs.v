(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1421 of its 1489 lines of code are new or changed and 943 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R21.v, with its addresses changed; 121 of its 199 lines of code are new or changed and 1411 lines of the source are left out. *)
(* lib/B/Prog/Seg/R21Fs.v -- the NARROWED pre stretch of R21's tail (r21_tail_evt, Seg/R21.v:330), fuzz_ctrl image B
   (libreac v1.9.0).  The image-B twin of lib/A/Prog/Seg/R21Fs.v (image A, a Theorem Labs lane); single writer.
   rule 24: no function proved (a segment stretch).

   Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
     image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
       sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
     source run: lib/B/Prog/Seg/R21.v r21_tail_evt (:330-471), blob 54812916d1e4a55c3dac312e07f10606976d0d30 (the blob this tree had at release c5e779efe8c);
     source stretch: lib/B/Prog/Seg/R21F.v c094b33a83e8cc77f6c945e4486d692eedccb020 (the blob this tree had at release c5e779efe8c), r21_tail_pre_F (:357-459)
       (the h <> 0 guard on the rng premises of S5 + 20, the name pointer and its shadow byte, and the rows narrowed to
       the bytes both arms read: auditor a Theorem Labs lane, 2026-10-29 09:00Z, and a Theorem Labs lane's S5 items; the h <> 0 guard
       on the value premise of that shadow byte, K280: auditor a Theorem Labs lane, 2026-10-29 10:38Z);
     tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
           lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
     compare: r21_tail_pre_F_of_Fs re-derives R21F.r21_tail_pre_F, pinned term for term by
       r21_tail_pre_F_of_Fs_verbatim (constr_eq against the type of R21F.r21_tail_pre_F).

   WHY (the narrowed-stretch rule, a Theorem Labs lane 04:23Z, relayed by a Theorem Labs lane 04:34Z): R21F.v's r21_tail_pre_F carries
   the source run's whole premise list, so that the glue can re-derive R21.r21_tail_evt.  Its h <> 0 premise HN has
   25 conjuncts, but the stretch's own script (R21F.v, proof of r21_tail_pre_F) destructs HN and reads only three of
   them: the byte at S5 + 20 (R20), the name pointer at mr + 280 (R280) and 0 < nm < 2 ^ 64 (Hnm).  The other 22
   conjuncts (the two strings' bytes and addressability, end_in_app / app_mem, stk lo spv and its bounds, the two
   window separations, asan_cells / shadow_rw / ro_agree, GOT_CF / CF + 250 / CF + 245 -- R21F.v:377-389) and the
   binders spv / lo / sx with `sp = Z_to_bv 64 spv` and `0 <= spv < 2 ^ 64` are premises of the plain
   strcmp_wrap_contract, which the stretch never applies: it stops AT the wrapper trampoline entry
   STRCMP_WRAP = 0x42aa0 (call pc 0x81c54, return pc 0x81c58), and astrcmp_realizes has no cell premise.

   WHAT IS HERE (it follows image B's own Seg/R21F.v -- its binders, its 14 rng premises, its two continuations and
   its script; image A's lib/A/Prog/Seg/R21Fs.v was the model only for the narrowing, not for the rows or the post)
   - r21_tail_pre_Fs: r21_tail_pre_F with exactly those premises dropped; the same binders otherwise, the same rng
     premises (S5 + 20, the name pointer [mr + 280, mr + 288) and its shadow byte guarded by h <> 0, as in R21F.v),
     the same value premise K280 on that shadow byte, guarded by h <> 0 as in R21F.v, the same two continuations
     (h = 0 at 0x81c60, h <> 0 at the wrapper entry), the same script (R21F.v's, word for word, with the HN destruct
     narrowed).
   - r21_tail_pre_F_of_Fs: R21F.r21_tail_pre_F re-derived from r21_tail_pre_Fs, and its pin
     r21_tail_pre_F_of_Fs_verbatim (constr_eq against the type of R21F.r21_tail_pre_F): the narrowed stretch is
     provably the same stretch, so the glue consumes r21_tail_pre_Fs.
   The seg_R21_a5c stretches of R21F.v (r21_a5c_next_F :65-87, r21_a5c_last_F :89-108) are NOT narrowed and need no
   twin: they stop at no callee (0x81ac0 -> 0x816ec, resp. -> 0x81b00), they touch no memory, and their only
   premises are s6 = Z_to_bv 64 bz with 0 <= bz <= 5 (resp. s6 = Z_to_bv 64 6) -- no wrapper cell conjunct
   (GOT_CF / CF + 250 / CF + 245) and no rng premise at all.  r21_tail_post_F does not exist in image B: the h <> 0
   arm of r21_tail_pre_F ends in the source run's own continuation at the callee entry.  The rng rows are
   R21Fs.rng.tsv (those of r21_tail_pre_F).

   CLOSURE: Seg/R21F.v and the sources it Requires, nothing else. *)
(* rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcEmit RcDecl RcParseLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import strcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot RHelp RtmB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R21 R21F.
(* Last: StepF's step / if_true (evtF goals) shadow Step's (evt goals), as in R21F.v. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF ExecF_all StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.

(* R21F.v's two local tactics of the tail stretch (Local there), verbatim. *)
Local Ltac r21F_shfix :=
  repeat match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (MState.unsigned_lit x) by lia
  end.

Local Ltac r21F_beq_refl :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; apply R21.r21_eqb_refl]
  end.

Lemma r21_tail_pre_Fs :
  forall (RNG : footprint) (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A S5 mr fw maj mnr pat h nm : Z),
    s1 = Z_to_bv 64 A -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 S5)) ->
    ov_read_bytes rsegs m (wa (A + 32)) 8 = Some (le8 (Z_to_bv 64 0)) ->
    ov_read_bytes rsegs m (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 mr)) ->
    ov_read_bytes rsegs m (wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    (h <> 0 -> ov_read_bytes rsegs m (wa (Z.shiftr (mr + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0]) ->
    ov_read_bytes rsegs m (wa S5) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (mr + 266)) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (S5 + 36)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (S5 + 22)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (mr + 268)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (S5 + 24)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (mr + 270)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (S5 + 26)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 272)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 56)) 4 = Some (le4 (Z_to_bv 64 h)) ->
    (h <> 0 ->
       ov_read_bytes rsegs m (wa (S5 + 20)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes rsegs m (wa (mr + 280)) 8 = Some (le8 (Z_to_bv 64 nm)) /\ 0 < nm < 2 ^ 64) ->
    rng RNG (A + 32) 8 -> rng RNG (A + 144) 8 -> rng RNG (A + 272) 8 ->
    rng RNG S5 3 -> rng RNG (S5 + 22) 6 -> rng RNG (S5 + 36) 1 -> rng RNG (mr + 56) 4 -> rng RNG (mr + 266) 8 ->
    rng RNG (Z.shiftr (mr + 266) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 268) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 270) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 272) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 56) 3 + ASAN_K) 1 ->
    (h <> 0 -> rng RNG (S5 + 20) 1 /\ rng RNG (mr + 280) 8 /\ rng RNG (Z.shiftr (mr + 280) 3 + ASAN_K) 1) ->
    (h = 0 -> forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word), a0' = Z_to_bv 64 0 ->
       evtF rsegs RNG Q
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs))) ->
    (h <> 0 -> forall R : bvmap 5 word,
       getr R 1 = Z_to_bv 64 0x81c58 -> getr R 10 = Z_to_bv 64 (S5 + 3) -> getr R 11 = Z_to_bv 64 nm ->
       getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
       getr R 19 = s3 -> getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 -> getr R 24 = s8 ->
       getr R 25 = s9 -> getr R 26 = s10 ->
       Q (MS R F (Z_to_bv 64 STRCMP_WRAP) fc None m (seg_rom rsegs))) ->
    evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b00) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A S5 mr fw maj mnr pat h nm -> -> HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R144 R32 R272 R2 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN
    Rg32 Rg144 Rg272 RgS5 RgS22 RgS36 Rgm56 Rgm266 RgK266 RgK268 RgK270 RgK272 RgK56 GHN K0 Kbf.
  step. step. step. if_true.                    (* 81b00 ld 144; 81b04 lbu 2; 81b08 bnez *)
  step. step. if_true.                          (* 81b10 ld 32; 81b14 beqz *)
  step. step. step. step. r21F_shfix.           (* 81b1c ld 272; addi 266; srli; add *)
  step. step. step. step. if_true.              (* 81b2c lb; 81b30 ld 144; 81b34 lhu 0; 81b38 beqz *)
  step. step. r21F_beq_refl.                    (* 81b40 lhu; 81b44 beq *)
  step. step. step. if_true.                    (* 81b4c ld 144; 81b50 lbu 36; 81b54 bnez *)
  step. step. step. step. r21F_shfix.           (* 81b5c ld 272; addi 268; srli; add *)
  step. step. step. step. if_true.              (* 81b6c lb; 81b70 ld 144; 81b74 lhu 22; 81b78 beqz *)
  step. step. r21F_beq_refl.                    (* 81b80 lhu; 81b84 beq *)
  step. step. step. step. r21F_shfix.           (* 81b8c ld 272; addi 270; srli; add *)
  step. step. step. step. if_true.              (* 81b9c lb; 81ba0 ld 144; 81ba4 lhu 24; 81ba8 beqz *)
  step. step. r21F_beq_refl.                    (* 81bb0 lhu; 81bb4 beq *)
  step. step. step. step. r21F_shfix.           (* 81bbc ld 272; addi 272; srli; add *)
  step. step. step. step. if_true.              (* 81bcc lb; 81bd0 ld 144; 81bd4 lhu 26; 81bd8 beqz *)
  step. step. r21F_beq_refl.                    (* 81be0 lhu; 81be4 beq *)
  step. step. step. step. r21F_shfix.           (* 81bec ld 272; addi 56; srli; add *)
  step. step. if_true.                          (* 81bfc lb; 81c00 beqz *)
  step. step.                                   (* 81c08 lw; 81c0c beqz a0,81c60 *)
  destruct (Z.eq_dec h 0) as [E0 | E0].
  - if_true_by (eq_trans (R21.r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_eq h 0) E0)).
    eapply (K0 E0).
    exact (R21.r21_eqb_eq _ _ (eq_trans (R21.r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_eq h 0) E0))).
  - if_false_by (eq_trans (R21.r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_neq h 0) E0)).
    destruct (HN E0) as (R20 & R280 & Hnm).
    destruct (GHN E0) as (RgS20 & Rgm280 & RgK280). specialize (K280 E0).
    step. step. step. if_true.                  (* 81c10 ld 144; 81c14 lbu 20; 81c18 bnez *)
    step. step. step. step. r21F_shfix.         (* 81c20 ld 272; addi 280; srli; add *)
    step. step. if_true.                        (* 81c30 lbu (check); 81c34 beqz *)
    step. step. step. step.                     (* 81c3c ld a1,0(a0); 81c40 ld 144; 81c44 addi 3; 81c48 bnez *)
    if_true_by (f_equal negb (R21.r21_eqb0 nm Hnm)).
    step.                                       (* 81c54 jal wrapper_strcmp, ra = 0x81c58 *)
    apply evtF_done.
    apply (Kbf E0); first [ reflexivity | f_equal; lia ].
Qed.

(* R21F.v's r21_tail_pre_F, re-derived from the narrowed stretch: every premise of r21_tail_pre_Fs is a premise of
   r21_tail_pre_F (HN gives its first three conjuncts). *)
Lemma r21_tail_pre_F_of_Fs :
  forall (RNG : footprint) (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv lo A S5 mr fw maj mnr pat h nm : Z) (sx : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= spv < 2 ^ 64 -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 S5)) ->
    ov_read_bytes rsegs m (wa (A + 32)) 8 = Some (le8 (Z_to_bv 64 0)) ->
    ov_read_bytes rsegs m (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 mr)) ->
    ov_read_bytes rsegs m (wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    (h <> 0 -> ov_read_bytes rsegs m (wa (Z.shiftr (mr + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0]) ->
    ov_read_bytes rsegs m (wa S5) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (mr + 266)) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (S5 + 36)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (S5 + 22)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (mr + 268)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (S5 + 24)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (mr + 270)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (S5 + 26)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 272)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 56)) 4 = Some (le4 (Z_to_bv 64 h)) ->
    (h <> 0 ->
       ov_read_bytes rsegs m (wa (S5 + 20)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes rsegs m (wa (mr + 280)) 8 = Some (le8 (Z_to_bv 64 nm)) /\ 0 < nm < 2 ^ 64 /\
       bytes_at rsegs m (S5 + 3) (sx ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sx /\
       bytes_at rsegs m nm (sx ++ [Z_to_bv 8 0]) /\
       Z.of_nat (strcmp_k sx sx) + 1 <= 2^40 /\
       addressable m (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       end_in_app (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       addressable m nm (Z.of_nat (strcmp_k sx sx) + 1) /\ end_in_app nm (Z.of_nat (strcmp_k sx sx) + 1) /\
       app_mem (S5 + 3 + 7) /\ app_mem (nm + 7) /\
       stk rsegs m lo spv /\ lo + STRCMP_WRAP_K <= spv /\ HIGHMEM_BEG <= lo /\ spv <= APPMEM_END /\
       (S5 + 3 + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= S5 + 3) /\
       (nm + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= nm) /\
       asan_cells m /\ shadow_rw m /\ MN.ro_agree rsegs m /\
       bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
       bytes_at rsegs m (CF + 250) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 245) [Z_to_bv 8 0]) ->
    rng RNG (A + 32) 8 -> rng RNG (A + 144) 8 -> rng RNG (A + 272) 8 ->
    rng RNG S5 3 -> rng RNG (S5 + 22) 6 -> rng RNG (S5 + 36) 1 -> rng RNG (mr + 56) 4 -> rng RNG (mr + 266) 8 ->
    rng RNG (Z.shiftr (mr + 266) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 268) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 270) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 272) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 56) 3 + ASAN_K) 1 ->
    (h <> 0 -> rng RNG (S5 + 20) 1 /\ rng RNG (mr + 280) 8 /\ rng RNG (Z.shiftr (mr + 280) 3 + ASAN_K) 1) ->
    (h = 0 -> forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word), a0' = Z_to_bv 64 0 ->
       evtF rsegs RNG Q
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs))) ->
    (h <> 0 -> forall R : bvmap 5 word,
       getr R 1 = Z_to_bv 64 0x81c58 -> getr R 10 = Z_to_bv 64 (S5 + 3) -> getr R 11 = Z_to_bv 64 nm ->
       getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
       getr R 19 = s3 -> getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 -> getr R 24 = s8 ->
       getr R 25 = s9 -> getr R 26 = s10 ->
       Q (MS R F (Z_to_bv 64 STRCMP_WRAP) fc None m (seg_rom rsegs))) ->
    evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b00) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo A S5 mr fw maj mnr pat h nm sx Esp Es1 Es10 Hsp HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R144 R32 R272 R2 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN
    Rg32 Rg144 Rg272 RgS5 RgS22 RgS36 Rgm56 Rgm266 RgK266 RgK268 RgK270 RgK272 RgK56 GHN K0 Kbf.
  apply (r21_tail_pre_Fs RNG Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m A S5 mr fw maj mnr pat h nm Es1 Es10 HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
           R144 R32 R272 R2 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56);
    [| exact Rg32 | exact Rg144 | exact Rg272 | exact RgS5 | exact RgS22 | exact RgS36 | exact Rgm56 | exact Rgm266
     | exact RgK266 | exact RgK268 | exact RgK270 | exact RgK272 | exact RgK56 | exact GHN | exact K0 | exact Kbf].
  intros E0. destruct (HN E0) as (R20 & R280 & Hnm & _). exact (conj R20 (conj R280 Hnm)).
Qed.

(* The pin: r21_tail_pre_F_of_Fs states R21F.r21_tail_pre_F term for term (constr_eq: syntactic). *)
Lemma r21_tail_pre_F_of_Fs_verbatim : True.
Proof.
  let A := type of R21F.r21_tail_pre_F in let B := type of r21_tail_pre_F_of_Fs in constr_eq A B.
  exact I.
Qed.

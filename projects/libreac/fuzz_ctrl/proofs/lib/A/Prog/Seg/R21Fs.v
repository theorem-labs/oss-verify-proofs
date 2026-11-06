(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1421 of its 1489 lines of code are new or changed and 943 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R21.v, with its module paths, module names, addresses and numbers changed; 148 of its 199 lines of code are new or changed and 1438 lines of the source are left out. *)
(* lib/A/Prog/Seg/R21Fs.v -- the NARROWED pre stretch of R21's tail (r21_tail_evt, Seg/R21.v:203), fuzz_ctrl image A
   (libreac v1.9.0).  Written by a Theorem Labs lane, the glue owner of stage seg_R21; single writer.
   rule 24: no function proved (a segment stretch).

   WHY (the narrowed-stretch rule, a Theorem Labs lane 04:23Z, relayed by a Theorem Labs lane 04:34Z): a Theorem Labs lane's
   Seg/R21F.v r21_tail_pre_F carries the source run's whole premise list, so that its of_pre_post pin can re-derive
   R21.r21_tail_evt.  Its h <> 0 premise HN has 25 conjuncts, but the stretch's own script (R21F.v, proof of
   r21_tail_pre_F) destructs HN and reads only three of them: the byte at S5 + 20 (R20), the name pointer at
   mr + 280 (R280) and 0 < nm < 2 ^ 64 (Hnm).  The other 22 conjuncts (the two strings' bytes and addressability,
   end_in_app / app_mem, stk lo spv and its bounds, the two window separations, asan_cells / shadow_rw / ro_agree,
   GOT_CF / CF + 250 / CF + 245) and the binders spv / lo / sx with `sp = Z_to_bv 64 spv` and `0 <= spv < 2 ^ 64`
   are premises of the plain strcmp_wrap_contract, which the stretch never applies (it stops AT the wrapper entry).

   WHAT IS HERE
   - r21_tail_pre_Fs: r21_tail_pre_F with exactly those premises dropped; the same binders otherwise, the same rng
     premises, the same post, the same script (R21F.v's, word for word, with the HN destruct narrowed).
   - r21_tail_pre_F_of_Fs: a Theorem Labs lane's r21_tail_pre_F re-derived from r21_tail_pre_Fs, and its pin
     r21_tail_pre_F_of_Fs_verbatim (constr_eq against the type of R21F.r21_tail_pre_F): the narrowed stretch is
     provably the same stretch, so the glue consumes r21_tail_pre_Fs.
   r21_tail_post_F (R21F.v) is an empty stretch at the return pc and is not narrowed (the glue does not use it: the
   strcmp rule's continuation is the exit cut itself).  The rng rows are R21Fs.rng.tsv (a working note, not in this delivery; those of r21_tail_pre_F).

   CLOSURE: Seg/R21F.v and the sources it Requires, nothing else. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import strcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNorm BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3Norm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R21 R21F.
(* Last: StepF's step / if_true (evtF goals) shadow Step's and Tac's (evt goals), as in R21F.v. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The binding table (ctrlgate dcb362e1c42f; a Theorem Labs lane 07:0xZ): each name below is defined in a doubled Lib / Reusable
   family, so it is bound here, by full path, to exactly the copy `About` reports in this file's context (the core
   Lib copies, which the Imports above bind); the elaborated statements are unchanged, as the constr_eq pin checks. *)
Local Notation wa := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa) (only parsing).
Local Notation le2 := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le2) (only parsing).
Local Notation le4 := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le4) (only parsing).
Local Notation le8 := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8) (only parsing).
Local Notation bytes_at := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at) (only parsing).
Local Notation MS := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS) (only parsing).
Local Notation getr := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.getr) (only parsing).
Local Notation seg_rom := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom) (only parsing).
Local Notation mkR := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR) (only parsing).
Local Notation stk := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk) (only parsing).
Local Notation rng := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng) (only parsing).
Local Notation footprint := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.footprint) (only parsing).
Local Ltac step := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
Local Ltac if_true := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.if_true.
Local Ltac if_true_by H := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.if_true_by H.
Local Ltac if_false_by H := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.if_false_by H.

Lemma r21_tail_pre_Fs :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A S5 mr fw maj mnr pat h nm w144 : Z),
    s1 = Z_to_bv 64 A -> s5 = Z_to_bv 64 S5 -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= A -> A + 152 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 w144)) ->
    ov_read_bytes rsegs m (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 mr)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
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
    (* the segment's own reads, one rng per load; the h <> 0 reads guarded by h <> 0 as the source guards them *)
    rng RNG (S5 + 2) 1 -> rng RNG (A + 144) 8 -> rng RNG (A + 112) 8 ->
    rng RNG (Z.shiftr (mr + 266) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 268) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 270) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 272) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 56) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 280) 3 + ASAN_K) 1 ->
    rng RNG S5 2 -> rng RNG (mr + 266) 2 -> rng RNG (S5 + 36) 1 ->
    rng RNG (S5 + 22) 2 -> rng RNG (mr + 268) 2 -> rng RNG (S5 + 24) 2 -> rng RNG (mr + 270) 2 ->
    rng RNG (S5 + 26) 2 -> rng RNG (mr + 272) 2 -> rng RNG (mr + 56) 4 ->
    (h <> 0 -> rng RNG (S5 + 20) 1 /\ rng RNG (mr + 280) 8) ->
    evtF rsegs RNG
      (fun ms' =>
         (h = 0 /\ exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs) /\ getr R 10 = Z_to_bv 64 0 /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 w144 /\
            getr R 22 = s6 /\ getr R 25 = s9) \/
         (h <> 0 /\ exists (c5 c6 c7 c12 c13 c14 c15 c16 c17 c28 c29 c30 c31 : word),
            ms' = MS (mkR (Z_to_bv 64 0x81ac0) sp gp tp c5 c6 c7 s0 s1
                          (Z_to_bv 64 (S5 + 3)) (Z_to_bv 64 nm) c12 c13 c14 c15 c16 c17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 w144) c28 c29 c30 c31)
                     F (Z_to_bv 64 STRCMP_WRAP) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81990) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A S5 mr fw maj mnr pat h nm w144 -> -> -> HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R2 R144 R112 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN
    G2 G144 G112 GK266 GK268 GK270 GK272 GK56 GK280 G0 GM266 G36 G22 GM268 G24 GM270 G26 GM272 GM56 GHN.
  step. step. step. if_true.            (* 81990 lbu; 81994 ld s11; 81998 bnez *)
  step. step. step. step. r21_shfix.     (* 819a0 ld; addi 266; srli; add *)
  step. step. step. if_true.           (* 819b0 lb (check); 819b4 lhu; 819b8 beqz *)
  step. step. r21F_tail_beq_refl.        (* 819c0 lhu; 819c4 beq *)
  step. step. if_true.                                         (* 819cc lbu 36; 819d0 bnez *)
  step. step. step. step. r21_shfix.                           (* 819d8 .. 819e4 *)
  step. step. step. if_true.                                   (* 819e8 lb; 819ec lhu 22; 819f0 beqz *)
  step. step. r21F_tail_beq_refl.                               (* 819f8 lhu; 819fc beq *)
  step. step. step. step. r21_shfix.                           (* 81a04 .. 81a10 *)
  step. step. step. if_true.                                   (* 81a14 lb; 81a18 lhu 24; 81a1c beqz *)
  step. step. r21F_tail_beq_refl.                               (* 81a24 lhu; 81a28 beq *)
  step. step. step. step. r21_shfix.                           (* 81a30 .. 81a3c *)
  step. step. step. if_true.                                   (* 81a40 lb; 81a44 lhu 26; 81a48 beqz *)
  step. step. r21F_tail_beq_refl.                               (* 81a50 lhu; 81a54 beq *)
  step. step. step. step. r21_shfix.                           (* 81a5c .. 81a68 *)
  step. step. if_true.                                         (* 81a6c lb; 81a70 beqz *)
  step. step.                           (* 81a78 lw; 81a7c beqz a0,81ac8 *)
  destruct (Z.eq_dec h 0) as [E0 | E0].
  - if_true_by (eq_trans (r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_eq h 0) E0)).
    subst h. apply evtF_done. left. split; [reflexivity|]. eexists. split; [reflexivity|].
    do 10 (split; [reflexivity|]). reflexivity.
  - if_false_by (eq_trans (r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_neq h 0) E0)).
    destruct (HN E0) as (R20 & R280 & Hnm).
    destruct (GHN E0) as (G20 & G280).
    step. step. if_true.                                       (* 81a80 lbu 20; 81a84 bnez *)
    step. step. step. step. r21_shfix.                         (* 81a8c .. 81a98 *)
    step. step. if_true.               (* 81a9c lbu (check); 81aa0 beqz *)
    step. step. step.                  (* 81aa8 ld a1; 81aac addi a0,s5,3; 81ab0 bnez *)
    if_true_by (f_equal negb (r21_eqb0 nm Hnm)).
    step.                               (* 81abc jal wrapper_strcmp, ra = 0x81ac0 *)
    apply evtF_done. right. split; [exact E0|]. do 13 eexists. reflexivity.
Qed.

(* a Theorem Labs lane's r21_tail_pre_F (R21F.v), re-derived from the narrowed stretch: every premise of r21_tail_pre_Fs is a
   premise of r21_tail_pre_F (HN gives its first three conjuncts). *)
Lemma r21_tail_pre_F_of_Fs :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv lo A S5 mr fw maj mnr pat h nm w144 : Z) (sx : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s5 = Z_to_bv 64 S5 -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= spv < 2 ^ 64 -> 0 <= A -> A + 152 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 w144)) ->
    ov_read_bytes rsegs m (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 mr)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
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
       asan_cells m /\ shadow_rw m /\ MNr21.ro_agree rsegs m /\
       bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
       bytes_at rsegs m (CF + 250) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 245) [Z_to_bv 8 0]) ->
    (* the segment's own reads, one rng per load; the h <> 0 reads guarded by h <> 0 as the source guards them *)
    rng RNG (S5 + 2) 1 -> rng RNG (A + 144) 8 -> rng RNG (A + 112) 8 ->
    rng RNG (Z.shiftr (mr + 266) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 268) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 270) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 272) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 56) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 280) 3 + ASAN_K) 1 ->
    rng RNG S5 2 -> rng RNG (mr + 266) 2 -> rng RNG (S5 + 36) 1 ->
    rng RNG (S5 + 22) 2 -> rng RNG (mr + 268) 2 -> rng RNG (S5 + 24) 2 -> rng RNG (mr + 270) 2 ->
    rng RNG (S5 + 26) 2 -> rng RNG (mr + 272) 2 -> rng RNG (mr + 56) 4 ->
    (h <> 0 -> rng RNG (S5 + 20) 1 /\ rng RNG (mr + 280) 8) ->
    evtF rsegs RNG
      (fun ms' =>
         (h = 0 /\ exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs) /\ getr R 10 = Z_to_bv 64 0 /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 w144 /\
            getr R 22 = s6 /\ getr R 25 = s9) \/
         (h <> 0 /\ exists (c5 c6 c7 c12 c13 c14 c15 c16 c17 c28 c29 c30 c31 : word),
            ms' = MS (mkR (Z_to_bv 64 0x81ac0) sp gp tp c5 c6 c7 s0 s1
                          (Z_to_bv 64 (S5 + 3)) (Z_to_bv 64 nm) c12 c13 c14 c15 c16 c17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 w144) c28 c29 c30 c31)
                     F (Z_to_bv 64 STRCMP_WRAP) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81990) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo A S5 mr fw maj mnr pat h nm w144 sx Esp Es1 Es5 Es10 Hsp HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R2 R144 R112 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN
    G2 G144 G112 GK266 GK268 GK270 GK272 GK56 GK280 G0 GM266 G36 G22 GM268 G24 GM270 G26 GM272 GM56 GHN.
  apply (r21_tail_pre_Fs RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m A S5 mr fw maj mnr pat h nm w144 Es1 Es5 Es10 HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
           R2 R144 R112 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56);
    [| exact G2 | exact G144 | exact G112 | exact GK266 | exact GK268 | exact GK270 | exact GK272 | exact GK56
     | exact GK280 | exact G0 | exact GM266 | exact G36 | exact G22 | exact GM268 | exact G24 | exact GM270
     | exact G26 | exact GM272 | exact GM56 | exact GHN].
  intros E0. destruct (HN E0) as (R20 & R280 & Hnm & _). exact (conj R20 (conj R280 Hnm)).
Qed.

(* The pin: r21_tail_pre_F_of_Fs states a Theorem Labs lane's R21F.r21_tail_pre_F term for term (constr_eq: syntactic). *)
Lemma r21_tail_pre_F_of_Fs_verbatim : True.
Proof.
  let A := type of R21F.r21_tail_pre_F in let B := type of r21_tail_pre_F_of_Fs in constr_eq A B.
  exact I.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 2439 of its 2555 lines of code are new or changed and 895 lines of the source are left out. *)
(* Segment F2 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan build of libreac v1.9.0, image B), frame-loop turn
   j: from the return point 0x81f50 of F1's allocation call to the return point 0x81f78 of the checked memcpy
   (len > 0) or to the return point 0x82048 of the reac_ctrl_parse call 0x82044 (len = 0).
     0x81f50 mv s2,a0            s2 = Phi (the block F1's allocation returned)
     0x81f54 beqz s4,0x81f60     len = 0: to 0x81f60
     0x81f58 bnez s2,0x81f60     len > 0: Phi <> 0 (HB), so the abort edge 0x81f5c `j 0x82fa4` is not taken
     0x81f60 sd s5,224(s1)       the cursor spill [A + 224] = p + body (FTURN)
     0x81f64 beqz s4,0x82020     len = 0: to the short parse block 0x82020
     0x81f68 mv a0,s2 / mv a1,s5 / mv a2,s4 / 0x81f74 jal checked_memcpy (0x52164)
       the len bytes of the frame body at p + body into Phi (FTURN's Phi bytes), returning to 0x81f78 (F3's entry)
     0x82020-0x82034 sb zero,22..25(s3); li a0,4; sb a0,26(s3)  the five frame shadow bytes S(fr) + 22 .. 26 mark
       the 36 parse-record bytes [fr + 176, fr + 212) usable
     0x82038 mv a0,s2 / mv a1,s4 / 0x82040 ld a2,280(s1) / 0x82044 jal reac_ctrl_parse ([A+280] = fr + 176,
       FLI), returning to 0x82048
   v1.9.0 against the patched image: the cursor is in s5 (was s9) and its spill is [A + 224] (was [A + 216]); the
   parse calls read the record pointer from the spill [A+280] (the patched image had it in s6, `mv a2,s6`); the
   parse block is at 0x82020 / 0x81f94 (was 0x81fb0 / 0x81f24); the checked memcpy is at 0x52164 and
   reac_ctrl_parse at 0x83e04 (the _c.v constants of a working branch).
   The parse block (stores + call, at 0x82020 or at its long-frame twin 0x81f94) is f2_parse_seg, used here and by
   F3: lib/B/Prog/Seg/R9.v's parse-record stores and call (a working branch be153b10cd3) re-pinned to the
   frame-loop record fr + 176, its side-stack package built at the call from FRA by Tac_fsfree.fra_fp, the run
   stepped on the normalized memory (MemNorm, R4.v's r4_run) since the contract takes mem_inv.  The memcpy stage is
   lib/B/Prog/Seg/R8.v's (a working branch 72cb827d72b) checked_memcpy run re-pinned to the frame copy.  The head
   run 0x81f50 -> 0x82020 / 0x81f68 is on the real memory (sl_run_lib); FRA and ENT move across its store
   [A + 224, A + 232) by F1.f1_fra_spill.  Callees: checked_memcpy by its contract asan_memcpy_c.v (proved in tree
   by asan_memcpy.asan_memcpy_holds); reac_ctrl_parse by its contract reac_ctrl_parse_c.v, a Section hypothesis (a
   member of SlotLink's callee_contracts; its proof file is not in this tree).  Cuts: the official SlotInv.v
   Inv_B81f50_at (entry, pc 0x81f50), Inv_B81f78_at (pc 0x81f78) and Inv_B82048_at (pc 0x82048) (exits).
   rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_parse_c RcAsanFP asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c memcmp_c asan_memcpy_c asan_memcpy.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcLay.
Import ListNotations.
Open Scope Z_scope.

Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_parse_c.
Module RFP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module ASM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.memcmp_c.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module MCC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpy_c.

(* A byte store of a register whose value is not a literal: the engine's cell_of_bytes knows le8 / le4 / le2 / a
   singleton / le1 (zxb b), not le1 of a register; le1 v is [Z_to_bv 8 (bv_unsigned v)] by conversion
   (lib/B/Prog/Seg/R9.v's override). *)
Local Ltac fix_lit_store ::=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb ?b))) _) => idtac
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
  | _ => idtac
  end.

(* ---- branch facts ---- *)

Lemma f2_eqb0 : bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) = true.
Proof. reflexivity. Qed.

Lemma f2_eqb_nz : forall x, 0 < x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof. intros x Hx. rewrite (bv_eqb_lit x 0) by lia. apply Z.eqb_neq. lia. Qed.

Lemma f2_neqb0 : forall x, 0 < x < 2 ^ 64 -> negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0)) = true.
Proof. intros x Hx. rewrite (f2_eqb_nz x Hx). reflexivity. Qed.

Lemma f2_neqb00 : negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) = false.
Proof. reflexivity. Qed.

(* ---- the head run 0x81f50 -> 0x82020 (len = 0) and 0x81f50 -> 0x81f68 (len > 0), with the store [A + 224] ---- *)

Lemma f2_head0 :
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S : Z),
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= S < 2 ^ 64 -> wr_at rsegs m (A + 224) 8 ->
    evt rsegs
      (fun ms' => exists m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 a0 s3
                                          (Z_to_bv 64 0) (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x82020) fc None m' (seg_rom rsegs) /\
         munch [(A + 224, A + 232)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 224) (le8 (Z_to_bv 64 S)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0)
               (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81f50) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A S
    HA0 HA1 HS HW.
  pose proof (munch_refl [(A + 224, A + 232)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (wr_at_store_ok rsegs m (A + 224) 8 0 8 HW ltac:(lia) ltac:(lia)) as HS1.
  replace (A + 224 + 0) with (A + 224) in HS1 by lia.
  (* 0x81f50 mv s2,a0 ; 0x81f54 beqz s4 (taken) *)
  step. step. first [if_true_by f2_eqb0 | if_true].
  (* 0x81f60 sd s5,224(s1) ; 0x81f64 beqz s4 (taken) *)
  step. step. first [if_true_by f2_eqb0 | if_true].
  apply evt_done. eexists. split; [reflexivity|].
  split; [apply munch_write; [exact MU | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]|].
  split; [apply wmono_write; exact WM|].
  apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.

Lemma f2_head1 :
  forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S N phi : Z),
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= S < 2 ^ 64 -> 0 < N < 2 ^ 64 -> 0 < phi < 2 ^ 64 ->
    wr_at rsegs m (A + 224) 8 ->
    evt rsegs
      (fun ms' => exists m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 phi) a1 a2 a3 a4 a5
                                          a6 a7 (Z_to_bv 64 phi) s3 (Z_to_bv 64 N) (Z_to_bv 64 S) s6 s7 s8 s9 s10
                                          s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x81f68) fc None m' (seg_rom rsegs) /\
         munch [(A + 224, A + 232)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 224) (le8 (Z_to_bv 64 S)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 phi) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 N)
               (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81f50) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A S N phi
    HA0 HA1 HS HN Hphi HW.
  pose proof (munch_refl [(A + 224, A + 232)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (wr_at_store_ok rsegs m (A + 224) 8 0 8 HW ltac:(lia) ltac:(lia)) as HS1.
  replace (A + 224 + 0) with (A + 224) in HS1 by lia.
  (* 0x81f50 mv s2,a0 ; 0x81f54 beqz s4 (not taken) ; 0x81f58 bnez s2 (taken) *)
  step. step. first [if_false_by (f2_eqb_nz N HN) | if_false].
  step. first [if_true_by (f2_neqb0 phi Hphi) | if_true].
  (* 0x81f60 sd s5,224(s1) ; 0x81f64 beqz s4 (not taken) *)
  step. step. first [if_false_by (f2_eqb_nz N HN) | if_false].
  apply evt_done. eexists. split; [reflexivity|].
  split; [apply munch_write; [exact MU | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]|].
  split; [apply wmono_write; exact WM|].
  apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.

(* ---- the five record-shadow stores 0x82020-0x82034 / 0x81f94-0x81fa8 ---- *)
Lemma f2_st :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (pc0 pc1 : Z),
    (pc0 = 0x82020 /\ pc1 = 0x82038) \/ (pc0 = 0x81f94 /\ pc1 = 0x81fac) ->
    rw_cells rsegs m (bv_unsigned s3 + 22) [CB 5 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' : word) (m1 : word -> option byte) (b0 b1 b2 b3 b4 : byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 pc1) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 22, bv_unsigned s3 + 27)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 22) [b0; b1; b2; b3; b4] /\
         bv_signed b0 = 0 /\ bv_signed b1 = 0 /\ bv_signed b2 = 0 /\ bv_signed b3 = 0 /\ bv_signed b4 = 4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk pc0 pc1 Hpc HC HMI.
  pose proof (munch_refl [(bv_unsigned s3 + 22, bv_unsigned s3 + 27)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  destruct Hpc as [[-> ->] | [-> ->]]; do 6 step;
    (apply evt_done; do 2 eexists; do 5 eexists;
     split; [reflexivity|];
     split; [exact MU|]; split; [exact WM|]; split; [exact HMI|];
     split; [destruct HC as ((_ & Hb) & _); cbn [cells_bytes cbytes app] in Hb; exact Hb|];
     repeat split; vm_compute; reflexivity).
Qed.

(* ---- the reac_ctrl_parse call from its entry, by the contract, for an even return address ---- *)
Lemma f2_parse_at : PC.reac_ctrl_parse_contract ->
  forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv phi N o FS ret : Z) (fr50 junk : list byte),
    a0 = Z_to_bv 64 phi -> a1 = Z_to_bv 64 N -> a2 = Z_to_bv 64 o -> sp = Z_to_bv 64 spv ->
    ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    0 <= phi < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 ->
    spv < 2 ^ 64 -> spv mod 16 = 0 -> PC.REAC_CTRL_PARSE_K <= spv ->
    HIGHMEM_BEG <= spv - PC.REAC_CTRL_PARSE_K -> spv <= APPMEM_END ->
    stk rsegs m (spv - PC.REAC_CTRL_PARSE_K) spv ->
    mem_inv rsegs m ->
    length fr50 = 50%nat ->
    (50 <= N -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ (phi + 50 <= spv - PC.REAC_CTRL_PARSE_K \/ spv <= phi)) ->
    (forall i, In i (RP.cp_rd N fr50) -> mrd rsegs m (wa (phi + Z.of_nat i)) = nth_error fr50 i) ->
    o mod 4 = 0 -> o + 36 <= 2 ^ 64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= spv - PC.REAC_CTRL_PARSE_K \/ spv <= o) ->
    (50 <= N -> o + 36 <= phi \/ phi + 50 <= o) ->
    asan_cells m -> shadow_rw m ->
    addressable m (spv - PC.REAC_CTRL_PARSE_K) PC.REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m phi 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= BW.GOT_CF \/ BW.CF + 256 <= o) ->
    addressable m PC.REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m BW.REAL_BCMP (le8 (wa BW.BCMP)) ->
    bytes_at rsegs m BW.REAL_MEMCMP (le8 (wa MC.MEMCMP)) ->
    bytes_at rsegs m BW.GOT_CF (le8 (wa BW.CF)) ->
    bytes_at rsegs m (BW.CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (BW.CF + 255) [Z_to_bv 8 1] ->
    RFP.fp [1%nat] m (bv_unsigned tp) FS (spv - PC.REAC_CTRL_PARSE_K) spv
      (PC.reac_ctrl_parse_W o spv) (PC.reac_ctrl_parse_D phi N o) ->
    PC.reac_ctrl_parse_tls m (bv_unsigned tp) FS (spv - PC.REAC_CTRL_PARSE_K) spv ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 ret) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 21 = s5 /\
         getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 (fst (RP.ctrlparse N fr50)) /\
         munch (PC.reac_ctrl_parse_fp o spv ++ RFP.fp_w [1%nat] FS ++
                [(shadow_addr (spv - PC.REAC_CTRL_PARSE_K), shadow_addr spv)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (spv - PC.REAC_CTRL_PARSE_K) spv /\
         asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' o [CB 36 (snd (RP.ctrlparse N fr50))] /\
         addressable m' (spv - PC.REAC_CTRL_PARSE_K) PC.REAC_CTRL_PARSE_K /\
         RFP.fp [1%nat] m' (bv_unsigned tp) FS (spv - PC.REAC_CTRL_PARSE_K) spv
           (PC.reac_ctrl_parse_W o spv) (PC.reac_ctrl_parse_D phi N o))
      (MS (mkR (Z_to_bv 64 ret) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 PC.REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).
Proof.
  intros PARSE sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi N o FS ret fr50 junk -> -> -> -> Hret Hretr Hphi HN Ho Ho0 Hsp64 Hsp16 HspK HHM HAE
    ST HMI HL50 HF50 HRD Ho4 Ho36 RWo HoS HoF HAC HSW ADw ADf ADo HoApp HoCF ADbc
    HBC1 HBC2 HBC3 HBC4 HBC5 FPp TLS.
  unfold PC.reac_ctrl_parse_contract in PARSE. cbv zeta in PARSE.
  assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply MState.unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv)
    by (apply MState.unsigned_lit; unfold PC.REAC_CTRL_PARSE_K in HspK; lia).
  eapply evt_cut.
  { eapply PARSE with (f := phi) (n := N) (o := o) (S := spv) (FS := FS) (fr := fr50) (junk := junk).
    all: rewrite ?Ephi, ?EN, ?Esp.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hsp16.
    - exact HspK.
    - exact ST.
    - exact HMI.
    - exact HL50.
    - exact HF50.
    - exact HRD.
    - intros _. split; [exact Ho4|]. split; [exact Ho36|]. split; [exact RWo|].
      split; [exact HoS | exact HoF].
    - exact HAC.
    - exact HSW.
    - exact HHM.
    - exact HAE.
    - exact ADw.
    - exact ADf.
    - intros _. split; [exact ADo|]. split; [exact HoApp | exact HoCF].
    - exact ADbc.
    - exact HBC1.
    - exact HBC2.
    - exact HBC3.
    - exact HBC4.
    - exact HBC5.
    - exact FPp.
    - exact TLS. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & STc & RWc & ACc & SWc & ADc & FPc & TLc).
  subst ms'.
  rewrite ?Ephi, ?EN, ?Esp in MU, STc, RWc, ADc, FPc.
  replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret)
    by (symmetry; apply ret_pc_even; [lia | exact Hret]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STc|].
  split; [exact ACc|]. split; [exact SWc|].
  split; [exact (RWc Ho0)|]. split; [exact ADc | exact FPc].
Qed.

(* 0x82038 / 0x81fac: mv a0,s2 ; mv a1,s4 ; ld a2,280(s1) ; jal reac_ctrl_parse, returning to 0x82048 / 0x81fbc.
   The record pointer o is the spill [A + 280] (FLI), which the load reads (the patched image had `mv a2,s6`). *)
Lemma f2_pcall : PC.reac_ctrl_parse_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv phi N o FS pcm pcr A : Z) (fr50 junk : list byte),
    (pcm = 0x82038 /\ pcr = 0x82048) \/ (pcm = 0x81fac /\ pcr = 0x81fbc) ->
    s2 = Z_to_bv 64 phi -> s4 = Z_to_bv 64 N -> s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 spv ->
    0 <= A -> A + 448 <= 2 ^ 64 -> ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    0 <= phi < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 ->
    spv < 2 ^ 64 -> spv mod 16 = 0 -> PC.REAC_CTRL_PARSE_K <= spv ->
    HIGHMEM_BEG <= spv - PC.REAC_CTRL_PARSE_K -> spv <= APPMEM_END ->
    stk rsegs m (spv - PC.REAC_CTRL_PARSE_K) spv ->
    mem_inv rsegs m ->
    length fr50 = 50%nat ->
    (50 <= N -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ (phi + 50 <= spv - PC.REAC_CTRL_PARSE_K \/ spv <= phi)) ->
    (forall i, In i (RP.cp_rd N fr50) -> mrd rsegs m (wa (phi + Z.of_nat i)) = nth_error fr50 i) ->
    o mod 4 = 0 -> o + 36 <= 2 ^ 64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= spv - PC.REAC_CTRL_PARSE_K \/ spv <= o) ->
    (50 <= N -> o + 36 <= phi \/ phi + 50 <= o) ->
    asan_cells m -> shadow_rw m ->
    addressable m (spv - PC.REAC_CTRL_PARSE_K) PC.REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m phi 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= BW.GOT_CF \/ BW.CF + 256 <= o) ->
    addressable m PC.REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m BW.REAL_BCMP (le8 (wa BW.BCMP)) ->
    bytes_at rsegs m BW.REAL_MEMCMP (le8 (wa MC.MEMCMP)) ->
    bytes_at rsegs m BW.GOT_CF (le8 (wa BW.CF)) ->
    bytes_at rsegs m (BW.CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (BW.CF + 255) [Z_to_bv 8 1] ->
    RFP.fp [1%nat] m (bv_unsigned tp) FS (spv - PC.REAC_CTRL_PARSE_K) spv
      (PC.reac_ctrl_parse_W o spv) (PC.reac_ctrl_parse_D phi N o) ->
    PC.reac_ctrl_parse_tls m (bv_unsigned tp) FS (spv - PC.REAC_CTRL_PARSE_K) spv ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 pcr) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 21 = s5 /\
         getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 (fst (RP.ctrlparse N fr50)) /\
         munch (PC.reac_ctrl_parse_fp o spv ++ RFP.fp_w [1%nat] FS ++
                [(shadow_addr (spv - PC.REAC_CTRL_PARSE_K), shadow_addr spv)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (spv - PC.REAC_CTRL_PARSE_K) spv /\
         asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' o [CB 36 (snd (RP.ctrlparse N fr50))] /\
         addressable m' (spv - PC.REAC_CTRL_PARSE_K) PC.REAC_CTRL_PARSE_K /\
         RFP.fp [1%nat] m' (bv_unsigned tp) FS (spv - PC.REAC_CTRL_PARSE_K) spv
           (PC.reac_ctrl_parse_W o spv) (PC.reac_ctrl_parse_D phi N o))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pcm) fc None m (seg_rom rsegs)).
Proof.
  intros PARSE ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi N o FS pcm pcr A fr50 junk Hpc Hs2 Hs4 Hs1 Hsp HA0 HA1 HRD. intros.
  subst s1.
  destruct Hpc as [[-> ->] | [-> ->]];
    (step; step; step; step;
     eapply (f2_parse_at PARSE) with (spv := spv) (phi := phi) (N := N) (o := o) (FS := FS) (fr50 := fr50)
       (junk := junk);
     solve [reflexivity | assumption | lia]).
Qed.

(* ---- the checked memcpy 0x81f68-0x81f74: mv a0,s2 ; mv a1,s5 ; mv a2,s4 ; jal checked_memcpy ---- *)
Lemma f2_mcpy_evt : MCC.asan_memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv S N phi lo : Z) (src junk : list byte),
    sp = Z_to_bv 64 spv -> s2 = Z_to_bv 64 phi -> s4 = Z_to_bv 64 N -> s5 = Z_to_bv 64 S ->
    0 <= phi < 2 ^ 64 -> 0 <= S < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    bytes_at rsegs m S src -> length src = Z.to_nat N ->
    rw_cells rsegs m phi [CB (Z.to_nat N) junk] ->
    (phi = S \/ S + N <= phi \/ phi + N <= S) ->
    N <= 2 ^ 40 ->
    addressable m S N -> addressable m phi N -> end_in_app S N -> end_in_app phi N ->
    (N = 0 \/ app_mem (S + 7) /\ app_mem (phi + 7)) ->
    (phi + N <= RT_LO \/ RT_HI <= phi) ->
    (phi + N <= spv - 2224 \/ spv <= phi) -> (S + N <= spv - 2224 \/ spv <= S) ->
    stk rsegs m lo spv -> lo + 2224 <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81f78) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 21 = s5 /\
         getr R 26 = s10 /\ getr R 27 = s11 /\
         munch [(phi, phi + N); (spv - 2224, spv)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' phi [CB (Z.to_nat N) src] /\ bytes_at rsegs m' S src)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81f68) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv S N phi lo src junk -> -> -> -> Hphi HS HN Hspv
    HbS HLsrc RWd HAL HNb AS AD ES ED APP HRT HSEPd HSEPs ST HLO HHM HAE HAC HSW HMI.
  unfold MCC.asan_memcpy_contract in MCPY. cbv zeta in MCPY.
  assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply MState.unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  assert (ESv : bv_unsigned (Z_to_bv 64 S) = S) by (apply MState.unsigned_lit; lia).
  step. step. step. step.
  eapply evt_cut.
  { eapply MCPY with (src := src) (junk := junk) (lo := lo).
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HbS.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HLsrc.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact RWd.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HAL.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HNb.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact AS.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact AD.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact ES.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact ED.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact APP.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HRT.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. unfold MCC.ASAN_MEMCPY_K. exact HSEPd.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. unfold MCC.ASAN_MEMCPY_K. exact HSEPs.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact ST.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. unfold MCC.ASAN_MEMCPY_K. exact HLO.
    - exact HHM.
    - rewrite ?Ephi, ?EN, ?Esp, ?ESv. exact HAE.
    - exact HAC.
    - exact HSW.
    - exact HMI. }
  intros ms' PO. unfold MCC.asan_memcpy_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & STc & RWc & HBc & AC' & SW').
  subst ms'.
  unfold MCC.ASAN_MEMCPY_K in MU.
  rewrite ?Ephi, ?EN, ?Esp in MU. rewrite ?Esp in STc. rewrite ?Ephi, ?EN in RWc. rewrite ?ESv in HBc.
  replace (ret_pc (Z_to_bv 64 0x81f78)) with (Z_to_bv 64 0x81f78)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STc|].
  split; [exact AC'|]. split; [exact SW'|]. split; [exact RWc | exact HBc].
Qed.

(* ==== the segment lemmas ==== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs F1.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Open Scope Z_scope.

(* ---- helpers of lib/B/Prog/Seg/R4.v and R9.v (two working branches) ---- *)

Lemma f2_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof. intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))). Qed.

Lemma f2_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma f2_addr_keepW : forall W m m' p n, addressable m p n -> LF.munch W m m' ->
  (forall i, 0 <= i < n -> LF.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

Lemma f2_out_dec : forall W x, LF.outside W x \/ ~ LF.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [LF.outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

Lemma f2_not_out2 : forall lo1 hi1 lo2 hi2 x, ~ LF.outside [(lo1, hi1); (lo2, hi2)] x ->
  lo1 <= x < hi1 \/ lo2 <= x < hi2.
Proof. intros lo1 hi1 lo2 hi2 x H. cbn [LF.outside] in H. lia. Qed.

Lemma f2_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma f2_sf8 : forall fr, fr mod 32 = 0 -> 8 * (Sfr fr - ASAN_K) = fr.
Proof. intros fr H. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma f2_fsh : forall fr k, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> 0 <= k < FRAME_SHADOW ->
  in_shadow (Sfr fr + k).
Proof.
  intros fr k Happ Hk. pose proof FRAME_BYTES_val. pose proof FRAME_SHADOW_val.
  rewrite <- f2_sh8. apply shadow_of_app. apply Happ. lia.
Qed.

(* A spill at A + off read as the bytes at that address, for the A register 9 holds. *)
Lemma f2_spill_q64 : forall (regs : bvmap 5 word) m off v A,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) Hr9 HA0 HA1 Hoff.
  assert (HA'eq : A' = A).
  { pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
    pose proof Hq as Hqb. destruct Hqb as (Hq0 & Hq1 & _).
    rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    rewrite (Z.mod_small A) in Hm by lia.
    assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity.
    rewrite HP in *. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

Lemma f2_ag_ok : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 0x5fe000)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f2_ag_lo : forall a, in_globals AF.frame_AG a -> 0 <= a < 0x5fe000.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) f2_ag_ok (lo, len) Hin) as H. cbn [fst snd] in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma f2_sa_lo : forall a, 0 <= a < 0x5fe000 -> ASAN_K <= shadow_addr a < ASAN_K + 785408.
Proof. intros a Ha. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma f2_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f2_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f2_ro_false : forall x : word, 0x5fe000 <= bv_unsigned x -> Lib.Mem.ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
  destruct (KindBGlue.kb_find_segment _ _ _ _ E) as (Hin & Hlo & Hhi).
  pose proof (proj1 (forallb_forall _ _) f2_img_top s Hin) as Hs. cbv beta in Hs. apply Z.leb_le in Hs.
  pose proof (N2Z.is_nonneg (seg_size s)). exfalso. lia.
Qed.

Lemma f2_ro_wa : forall a, 0x5fe000 <= a < 2 ^ 64 -> Lib.Mem.ro_addr rsegs (wa a) = false.
Proof. intros a Ha. apply f2_ro_false. rewrite wa_unsigned by lia. lia. Qed.

Lemma f2_shadow_gt : forall a, in_shadow a -> 0x5fe000 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. Qed.

Lemma f2_srw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (f2_shadow_gt a Ha) as Hr. split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (f2_ro_wa a Hr)). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f2_srw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (f2_shadow_gt a Ha) as Hr. split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (f2_ro_wa a Hr)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f2_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (f2_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f2_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (f2_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f2_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 HR H. unfold asan_cells in *.
  assert (TB : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) Hb)).
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply TB; assumption.
Qed.

Lemma f2_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite <- (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma f2_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

(* The class-1 cells of the side stack in closed form (R9.v). *)
Lemma f2_M1 : ASM.fs_M 1%nat = 8192.
Proof. reflexivity. Qed.

Lemma f2_hint1 : forall FS, ASM.fs_hint FS 1%nat = FS + 8.
Proof. intros FS. unfold ASM.fs_hint. cbn [Z.of_nat]. lia. Qed.

Lemma f2_flag1 : forall FS, ASM.fs_flag FS 1%nat 0 = FS + 20480.
Proof.
  intros FS. unfold ASM.fs_flag.
  replace (2 ^ 15) with 32768 by reflexivity.
  replace (2 ^ (15 - Z.of_nat 1)) with 16384 by reflexivity. lia.
Qed.

Lemma f2_frame1_0 : forall FS, ASM.fs_frame FS 1%nat 0 = FS + 1085440.
Proof. intros FS. unfold ASM.fs_frame. replace (2 ^ 20) with 1048576 by reflexivity. cbn [Z.of_nat]. lia. Qed.

Lemma f2_frame1_M : forall FS, ASM.fs_frame FS 1%nat (ASM.fs_M 1%nat) = FS + 2134016.
Proof.
  intros FS. unfold ASM.fs_frame, ASM.fs_B. rewrite f2_M1.
  replace (2 ^ 20) with 1048576 by reflexivity. cbn [Z.of_nat]. lia.
Qed.

(* The write set of the parse block: the five record-shadow bytes, the record, the callee window, the class-1
   side-stack cells and the shadow of the class-1 frames and of the window.  f2_W2 is the call's part. *)
Definition f2_W2 (o spv FS : Z) : list LF.ivl :=
  [(o, o + 36); (spv - 8800, spv);
   (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016));
   (shadow_addr (spv - 8800), shadow_addr spv)].
Definition f2_W (sh o spv FS : Z) : list LF.ivl := (sh, sh + 5) :: f2_W2 o spv FS.

Lemma f2_W2_sub : forall o spv FS, o <> 0 ->
  LF.sub_fp (PC.reac_ctrl_parse_fp o spv ++ RFP.fp_w [1%nat] FS ++
             [(shadow_addr (spv - PC.REAC_CTRL_PARSE_K), shadow_addr spv)]) (f2_W2 o spv FS).
Proof.
  intros o spv FS Ho x Hx. unfold f2_W2 in Hx. cbn [LF.outside] in Hx.
  unfold PC.reac_ctrl_parse_fp, PC.REAC_CTRL_PARSE_K, RFP.fp_w, RFP.fp_w1.
  rewrite (proj2 (Z.eqb_neq o 0) Ho).
  cbn [flat_map app].
  rewrite f2_hint1, f2_flag1, f2_frame1_0, f2_frame1_M, f2_M1.
  cbn [LF.outside].
  repeat split; try exact I; lia.
Qed.

Lemma f2_W_sub : forall sh o spv FS, o <> 0 ->
  LF.sub_fp (PC.reac_ctrl_parse_fp o spv ++ RFP.fp_w [1%nat] FS ++
             [(shadow_addr (spv - PC.REAC_CTRL_PARSE_K), shadow_addr spv)]) (f2_W sh o spv FS).
Proof.
  intros sh o spv FS Ho x Hx. apply (f2_W2_sub o spv FS Ho). unfold f2_W in Hx. cbn [LF.outside] in Hx.
  exact (proj2 Hx).
Qed.

Lemma f2_W_sub5 : forall sh o spv FS, LF.sub_fp [(sh, sh + 5)] (f2_W sh o spv FS).
Proof. intros sh o spv FS x Hx. unfold f2_W in Hx. cbn [LF.outside] in Hx. cbn [LF.outside]. tauto. Qed.

Lemma f2_out2 : forall o spv FS x,
  (x < o \/ o + 36 <= x) ->
  (x < spv - 8800 \/ spv <= x) ->
  (x < FS + 8 \/ FS + 16 <= x) ->
  (x < FS + 20480 \/ FS + 28672 <= x) ->
  (x < FS + 1085440 \/ FS + 2134016 <= x) ->
  (x < shadow_addr (FS + 1085440) \/ shadow_addr (FS + 2134016) <= x) ->
  (x < shadow_addr (spv - 8800) \/ shadow_addr spv <= x) ->
  LF.outside (f2_W2 o spv FS) x.
Proof. intros. unfold f2_W2. cbn [LF.outside]. repeat split; try exact I; lia. Qed.

Lemma f2_out : forall sh o spv FS x,
  (x < sh \/ sh + 5 <= x) ->
  (x < o \/ o + 36 <= x) ->
  (x < spv - 8800 \/ spv <= x) ->
  (x < FS + 8 \/ FS + 16 <= x) ->
  (x < FS + 20480 \/ FS + 28672 <= x) ->
  (x < FS + 1085440 \/ FS + 2134016 <= x) ->
  (x < shadow_addr (FS + 1085440) \/ shadow_addr (FS + 2134016) <= x) ->
  (x < shadow_addr (spv - 8800) \/ shadow_addr spv <= x) ->
  LF.outside (f2_W sh o spv FS) x.
Proof. intros. unfold f2_W, f2_W2. cbn [LF.outside]. repeat split; try exact I; lia. Qed.

Lemma f2_sh_out : forall lo hi x, lo mod 8 = 0 -> hi mod 8 = 0 -> (x < lo \/ hi <= x) ->
  shadow_addr x < shadow_addr lo \/ shadow_addr hi <= shadow_addr x.
Proof. intros lo hi x Hl Hh Hx. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma f2_out_app : forall sh o spv FS x,
  app_mem x ->
  (forall a, FS + 1085440 <= a < FS + 2134016 -> app_mem a) ->
  (forall a, spv - 8800 <= a < spv -> app_mem a) ->
  (x < sh \/ sh + 5 <= x) ->
  (x < o \/ o + 36 <= x) ->
  (x < spv - 8800 \/ spv <= x) ->
  (x < FS + 8 \/ FS + 16 <= x) ->
  (x < FS + 20480 \/ FS + 28672 <= x) ->
  (x < FS + 1085440 \/ FS + 2134016 <= x) ->
  LF.outside (f2_W sh o spv FS) x.
Proof.
  intros sh o spv FS x Hx Hf Hw H1 H2 H3 H4 H5 H6.
  apply f2_out; try assumption.
  - destruct (Z_lt_le_dec x (shadow_addr (FS + 1085440))) as [H|H]; [left; exact H|].
    destruct (Z_lt_le_dec x (shadow_addr (FS + 2134016))) as [H'|H']; [|right; exact H'].
    exfalso. apply (app_not_shadow x Hx).
    pose proof (shadow_of_app (FS + 1085440) (Hf (FS + 1085440) ltac:(lia))) as Hs1.
    pose proof (shadow_of_app (FS + 2134016 - 1) (Hf (FS + 2134016 - 1) ltac:(lia))) as Hs2.
    unfold shadow_addr, in_shadow, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *.
    Z.div_mod_to_equations. lia.
  - destruct (Z_lt_le_dec x (shadow_addr (spv - 8800))) as [H|H]; [left; exact H|].
    destruct (Z_lt_le_dec x (shadow_addr spv)) as [H'|H']; [|right; exact H'].
    exfalso. apply (app_not_shadow x Hx).
    pose proof (shadow_of_app (spv - 8800) (Hw (spv - 8800) ltac:(lia))) as Hs1.
    pose proof (shadow_of_app (spv - 1) (Hw (spv - 1) ltac:(lia))) as Hs2.
    unfold shadow_addr, in_shadow, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *.
    Z.div_mod_to_equations. lia.
Qed.

(* fp and its tls premise across the block's five shadow-byte stores (R9.v). *)
Lemma f2_fp_drop : forall cs m TP FS lo hi r W0 D,
  RFP.fp cs m TP FS lo hi (r :: W0) D -> RFP.fp cs m TP FS lo hi W0 D.
Proof.
  intros cs m TP FS lo hi r W0 D (DT & TS & C & T & DB & k & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & HWd & HDd).
  exists DT, TS, C, T, DB, k.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
  split; [exact (proj2 (proj1 (fl_dj_cons r W0 _) HWd)) | exact HDd].
Qed.

Lemma f2_fp_keep : forall cs m m' TP FS lo hi a b W0 D W',
  RFP.fp cs m TP FS lo hi ((a, b) :: W0) D -> LF.munch W' m m' -> LF.wmono rsegs m m' ->
  LF.sub_fp W' [(a, b)] -> (forall x, a <= x < b -> in_shadow x) ->
  RFP.fp cs m' TP FS lo hi ((a, b) :: W0) D.
Proof.
  intros cs m m' TP FS lo hi a b W0 D W'
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & HDd) Hm Hw Hs Hsh.
  exists DT, TS, C, T, DB, k.
  pose proof HWd as Hw0. unfold RFP.fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
  cbn [RFP.fp_tls app] in Hw0.
  repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
  assert (BEL : forall x, FS <= x < FS + ASM.FS_SIZE -> LF.outside W' x).
  { intros x Hx. apply (fl_out_lo W' a b x Hs).
    destruct (Z_lt_le_dec x a) as [H|H]; [left; exact H|].
    destruct (Z_lt_le_dec x b) as [H'|H']; [|right; exact H'].
    exfalso. exact (app_not_shadow x (proj1 (proj2 (proj2 (proj2 HP))) x Hx) (Hsh x ltac:(lia))). }
  unfold ASM.asan_tls_cells in HT.
  destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18
    & T19).
  split.
  { unfold ASM.asan_tls_cells.
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [exact T6|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [destruct T11 as (tb & te & T11); exists tb, te; fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [exact T18|]. fl_cell Hm Hs. }
  split; [fl_cell Hm Hs|].
  split.
  { unfold ASM.fs_place in *. destruct HP as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|].
    split; [exact P3|]. split; [exact P4|]. eapply stk_transport; [exact P5 | exact Hm | exact Hw |].
    intros x Hx. left. apply BEL. exact Hx. }
  split; [eapply fl_bytes; [exact H88 | exact Hm | intros x Hx; apply BEL; rewrite ?length_le8 in Hx;
                             unfold ASM.FS_SIZE; lia]|].
  split; [eapply fl_bytes; [exact H96 | exact Hm | intros x Hx; apply BEL; cbn [length] in Hx;
                             unfold ASM.FS_SIZE; lia]|].
  split; [exact (Forall_impl _ (fun c => fl_cls W' m m' FS c BEL Hm) HCL)|].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma f2_tls_keep : forall cs m m' TP FS lo hi a b W0 D W' X,
  RFP.fp cs m TP FS lo hi ((a, b) :: W0) D -> LF.munch W' m m' -> LF.sub_fp W' [(a, b)] ->
  (forall DT TS C T DB k, ASM.asan_tls_cells m TP DT TS C T DB k ->
     RFP.fp_dj (RFP.fp_tls TP DT TS C T DB k) X) ->
  forall DT TS C T DB k, ASM.asan_tls_cells m' TP DT TS C T DB k ->
    RFP.fp_dj (RFP.fp_tls TP DT TS C T DB k) X.
Proof.
  intros cs m m' TP FS lo hi a b W0 D W' X
    (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _) Hm Hs Htls DT TS C T DB k HT.
  pose proof HT0 as HT0c.
  pose proof HWd as Hw0. unfold RFP.fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
  cbn [RFP.fp_tls app] in Hw0.
  repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
  assert (OUT : forall a' b', RcLay.ly_dj a b a' b' -> forall x, a' <= x < b' -> LF.outside W' x)
    by (intros a' b' Hab x Hx; apply (fl_out_lo W' a b x Hs); unfold RcLay.ly_dj in Hab; lia).
  destruct HT0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17
    & A18 & A19).
  destruct HT as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17
    & B18 & B19).
  assert (EDT : DT0 = DT) by (apply (fl_le8_eq W' m m' (TP - 8) DT0 DT A3 B3 Hm); fl_tls_out OUT).
  assert (Ek : k0 = k) by (apply (fl_le4_eq W' m m' ASM.TSD_KEY k0 k A6 B6 A7 B7 Hm); fl_tls_out OUT).
  assert (ETS : TS0 = TS) by (apply (fl_le8_eq W' m m' (TP - 88) TS0 TS A8 B8 Hm); fl_tls_out OUT).
  subst DT0 k0 TS0.
  assert (EC : C0 = C) by (apply (fl_le8_eq W' m m' (bv_unsigned TS + 8 * k) C0 C A9 B9 Hm); fl_tls_out OUT).
  subst C0.
  assert (ET : T0 = T) by (apply (fl_le8_eq W' m m' (bv_unsigned C + 152) T0 T A10 B10 Hm); fl_tls_out OUT).
  assert (EDB : DB0 = DB) by (apply (fl_le8_eq W' m m' (TP + 8) DB0 DB A17 B17 Hm); fl_tls_out OUT).
  subst T0 DB0.
  exact (Htls DT TS C T DB k HT0c).
Qed.

(* The side stack after the call: a_fs_ok rebuilt from the contract's own fp post (R9.v). *)
Lemma f2_fs_ok : forall m m' TP FS lo hi W D W',
  AC.a_fs_ok m FS ->
  RFP.fp [1%nat] m' TP FS lo hi W D ->
  LF.munch W' m m' ->
  (forall x, FS <= x < FS + 8 -> LF.outside W' x) ->
  (forall x, FS + 16 <= x < FS + 88 -> LF.outside W' x) ->
  (forall x, FS + 4096 <= x < FS + 20480 -> LF.outside W' x) ->
  (forall x, FS + 28672 <= x < FS + 36864 -> LF.outside W' x) ->
  AC.a_fs_ok m' FS.
Proof.
  intros m m' TP FS lo hi W D W' (K1 & K2 & K3 & K4 & K5)
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFSlo & HA & HWd & HDd) MU O1 O2 O3 O4.
  assert (HSZ' : ASM.FS_SIZE = 11571200) by reflexivity.
  pose proof HP as HP'. destruct HP' as (P1 & P2 & P3 & P4 & P5).
  assert (HFS64 : FS + 11571200 <= 2 ^ 64).
  { pose proof (P4 (FS + ASM.FS_SIZE - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha. lia. }
  assert (HM1 : AC.a_fs_M 1%nat = 8192) by reflexivity.
  inversion HCL as [|c0 l0 Hc1 Hrest Heq]; subst.
  destruct Hc1 as (_ & h & flags & HH & HF & HFl & HFb).
  rewrite f2_M1 in HFl.
  split.
  { intros a Ha. destruct P5 as (_ & _ & Hs). destruct (Hs a ltac:(unfold AC.FS_SIZE in Ha; lia)) as (Hw & Hb).
    split; [exact Hw | exact Hb]. }
  split.
  { replace 20 with (bv_unsigned (Z_to_bv 64 20)) by reflexivity.
    exact (KindBGlue.bytes_at_le8_word rsegs m' (FS + 88) (Z_to_bv 64 20) H88). }
  split.
  { destruct H96 as (_ & _ & Hb). pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as E.
    replace (FS + 96 + Z.of_nat 0) with (FS + 96) in E by lia. exact E. }
  split.
  { intros c Hc. destruct (Nat.eq_dec c 1) as [->|Hne].
    - exists (bv_unsigned h).
      replace (AC.a_fs_hint FS 1) with (ASM.fs_hint FS 1%nat) by (unfold AC.a_fs_hint, ASM.fs_hint; reflexivity).
      exact (KindBGlue.bytes_at_le8_word rsegs m' _ h HH).
    - destruct (K4 c Hc) as (h' & Hh). exists h'.
      apply (KindBGlue.kb_word_munch rsegs m m' W' _ h' Hh MU).
      intros j Hj. unfold AC.a_fs_hint.
      assert (Hcn : Z.of_nat c <> 1) by (intros Hcc; apply Hne; lia).
      split; [lia|].
      destruct (Z.eq_dec (Z.of_nat c) 0) as [E0|E0].
      + apply O1. lia.
      + apply O2. lia. }
  { intros c j Hc Hj. destruct (Nat.eq_dec c 1) as [->|Hne].
    - rewrite HM1 in Hj.
      assert (Hlen : (Z.to_nat j < length flags)%nat) by lia.
      destruct HF as (_ & _ & Hb).
      destruct (nth_error flags (Z.to_nat j)) as [bb|] eqn:En;
        [|exfalso; apply nth_error_None in En; lia].
      pose proof (Hb (Z.to_nat j) Hlen) as E. rewrite En in E.
      replace (ASM.fs_flag FS 1%nat 0 + Z.of_nat (Z.to_nat j)) with (AC.a_fs_flag FS 1%nat j) in E
        by (unfold ASM.fs_flag, AC.a_fs_flag; lia).
      pose proof (proj1 (Forall_forall _ _) HFb bb (nth_error_In _ _ En)) as Hb01.
      destruct Hb01 as [Eb|Eb]; subst bb; [left | right]; exact E.
    - assert (Hcn : Z.of_nat c <> 1) by (intros Hcc; apply Hne; lia).
      assert (Hc10 : Z.of_nat c <= 10) by lia.
      assert (Hp : 2 ^ (15 - Z.of_nat c) = 2 * 2 ^ (14 - Z.of_nat c)).
      { replace (15 - Z.of_nat c) with (Z.succ (14 - Z.of_nat c)) by lia. rewrite Z.pow_succ_r by lia. lia. }
      assert (Hq0 : 0 < 2 ^ (14 - Z.of_nat c)) by (apply Z.pow_pos_nonneg; lia).
      unfold AC.a_fs_M in Hj.
      assert (Hrange : FS + 4096 <= AC.a_fs_flag FS c j < FS + 20480 \/
                       FS + 28672 <= AC.a_fs_flag FS c j < FS + 36864).
      { unfold AC.a_fs_flag. replace (2 ^ 15) with 32768 by reflexivity.
        destruct (Z.eq_dec (Z.of_nat c) 0) as [E0|E0].
        - left. rewrite E0 in Hp, Hj |- *. replace (2 ^ (14 - 0)) with 16384 in Hj by reflexivity.
          replace (2 ^ (15 - 0)) with 32768 by reflexivity. lia.
        - right. assert (Hq2 : 2 ^ (14 - Z.of_nat c) <= 4096).
          { replace 4096 with (2 ^ 12) by reflexivity. apply Z.pow_le_mono_r; lia. }
          lia. }
      assert (Hb64 : 0 <= AC.a_fs_flag FS c j < 2 ^ 64) by lia.
      assert (Hout : LF.outside W' (AC.a_fs_flag FS c j)) by (destruct Hrange; [apply O3 | apply O4]; lia).
      rewrite (KindBGlue.mbyte_munch rsegs W' m m' _ MU Hb64 Hout).
      exact (K5 c j Hc Hj). }
Qed.

(* The parse record [fr + 176, fr + 212) is addressable after the five shadow stores [0, 0, 0, 0, 4] at
   S(fr) + 22 .. S(fr) + 26 (R9.v's r9_addr_rec at the frame-loop record). *)
Lemma f2_addr_rec : forall m fr (b0 b1 b2 b3 b4 : byte),
  fr mod 8 = 0 -> 0 <= fr -> fr + 212 <= APPMEM_END ->
  (forall a, fr + 176 <= a < fr + 212 -> app_mem a) ->
  bytes_at rsegs m (shadow_addr fr + 22) [b0; b1; b2; b3; b4] ->
  bv_signed b0 = 0 -> bv_signed b1 = 0 -> bv_signed b2 = 0 -> bv_signed b3 = 0 -> bv_signed b4 = 4 ->
  addressable m (fr + 176) 36.
Proof.
  intros m fr b0 b1 b2 b3 b4 H8 H0 HE Happ (_ & _ & Hb) E0 E1 E2 E3 E4.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|].
  assert (Esh : shadow_addr (fr + 176 + i) = shadow_addr fr + 22 + i / 8).
  { unfold shadow_addr. replace (fr + 176 + i) with (i + (fr / 8 + 22) * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. Z.div_mod_to_equations. lia. }
  assert (Hk : 0 <= i / 8 <= 4) by (Z.div_mod_to_equations; lia).
  pose proof (Hb (Z.to_nat (i / 8)) ltac:(cbn [length]; lia)) as E.
  rewrite Z2Nat.id in E by lia. rewrite <- Esh in E.
  assert (Hmod : (fr + 176 + i) mod 8 = i mod 8).
  { replace (fr + 176 + i) with (i + (fr / 8 + 22) * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.mod_add by lia. reflexivity. }
  destruct (Z.eq_dec (i / 8) 0) as [K|K];
    [rewrite K in E; cbn in E; exists b0; split; [exact E | left; exact E0]|].
  destruct (Z.eq_dec (i / 8) 1) as [K'|K'];
    [rewrite K' in E; cbn in E; exists b1; split; [exact E | left; exact E1]|].
  destruct (Z.eq_dec (i / 8) 2) as [K2|K2];
    [rewrite K2 in E; cbn in E; exists b2; split; [exact E | left; exact E2]|].
  destruct (Z.eq_dec (i / 8) 3) as [K3|K3];
    [rewrite K3 in E; cbn in E; exists b3; split; [exact E | left; exact E3]|].
  assert (K4 : i / 8 = 4) by lia. rewrite K4 in E. cbn in E. exists b4. split; [exact E|].
  right. rewrite E4, Hmod. Z.div_mod_to_equations. lia.
Qed.

(* fp and its tls premise across a byte-wise agreeing memory (the MemNorm normalization; R9.v). *)
Lemma f2_atls_tr : forall m m0 TP DT TS C T DB k,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  ASM.asan_tls_cells m TP DT TS C T DB k -> ASM.asan_tls_cells m0 TP DT TS C T DB k.
Proof.
  intros m m0 TP DT TS C T DB k TB H. unfold ASM.asan_tls_cells in *.
  destruct H as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18
    & T19).
  split; [apply TB; exact T1|]. split; [apply TB; exact T2|]. split; [apply TB; exact T3|].
  split; [apply TB; exact T4|]. split; [apply TB; exact T5|]. split; [exact T6|].
  split; [apply TB; exact T7|]. split; [apply TB; exact T8|]. split; [apply TB; exact T9|].
  split; [apply TB; exact T10|].
  split; [destruct T11 as (tb & te & Hb); exists tb, te; apply TB; exact Hb|].
  split; [apply TB; exact T12|]. split; [apply TB; exact T13|]. split; [apply TB; exact T14|].
  split; [apply TB; exact T15|]. split; [apply TB; exact T16|]. split; [apply TB; exact T17|].
  split; [exact T18 | apply TB; exact T19].
Qed.

Lemma f2_fp_tr : forall cs m m0 TP FS lo hi W D,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  (stk rsegs m FS (FS + ASM.FS_SIZE) -> stk rsegs m0 FS (FS + ASM.FS_SIZE)) ->
  RFP.fp cs m TP FS lo hi W D -> RFP.fp cs m0 TP FS lo hi W D.
Proof.
  intros cs m m0 TP FS lo hi W D TB TS0
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & HDd).
  exists DT, TS, C, T, DB, k.
  split; [exact (f2_atls_tr m m0 TP DT TS C T DB k TB HT)|].
  split; [apply TB; exact HTP|].
  split.
  { unfold ASM.fs_place in *. destruct HP as (P1 & P2 & P3 & P4 & P5).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. exact (TS0 P5). }
  split; [apply TB; exact H88|]. split; [apply TB; exact H96|].
  split.
  { apply Forall_forall. intros c Hc.
    pose proof (proj1 (Forall_forall _ _) HCL c Hc) as (Hcc & h & flags & HH & HF & HFl & HFb).
    split; [exact Hcc|].
    exists h, flags. split; [apply TB; exact HH|]. split; [apply TB; exact HF|].
    split; [exact HFl | exact HFb]. }
  split; [exact HFS|]. split; [exact HA|]. split; [exact HWd | exact HDd].
Qed.

(* The image's LOAD segments map, page-rounded, one run of pages covering [2 ^ 21, GT): an address of that range
   lies on an image page, so a heap block (above 2 ^ 21, on no image page) lies above GT (R9.v). *)
Definition f2_pages_b : bool :=
  existsb (fun s => (Z.of_N (seg_base s) / 4096 * 4096 <=? 2 ^ 21) &&
                    (0x5fe000 <=? (Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4095) / 4096 * 4096)) rsegs.

Lemma f2_pages_true : f2_pages_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f2_on_page : forall a, 2 ^ 21 <= a < 0x5fe000 -> AC.a_on_img_page a.
Proof.
  intros a Ha. pose proof f2_pages_true as H. unfold f2_pages_b in H.
  apply existsb_exists in H. destruct H as (s & Hin & Hs).
  apply andb_prop in Hs. destruct Hs as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin|]. lia.
Qed.

(* The two write ranges of the checked memcpy: the destination and the callee window. *)
Lemma f2_out_mc : forall phi N sp x, (x < phi \/ phi + N <= x) -> (x < sp - 2224 \/ sp <= x) ->
  LF.outside [(phi, phi + N); (sp - 2224, sp)] x.
Proof. intros. cbn [LF.outside]. repeat split; try exact I; lia. Qed.

Lemma f2_mc_not_out : forall phi N sp x, ~ LF.outside [(phi, phi + N); (sp - 2224, sp)] x ->
  phi <= x < phi + N \/ sp - 2224 <= x < sp.
Proof. intros phi N sp x H. cbn [LF.outside] in H. lia. Qed.

Lemma f2_not_out : forall W x, ~ LF.outside W x -> exists r, In r W /\ fst r <= x < snd r.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; [exfalso; apply H; exact I|].
  cbn [LF.outside] in H.
  destruct (Z_le_gt_dec lo x) as [H1|H1].
  - destruct (Z_lt_ge_dec x hi) as [H2|H2].
    + exists (lo, hi). split; [left; reflexivity | cbn [fst snd]; lia].
    + assert (HA : ~ (lo <= x < hi)) by lia.
      destruct (IH x ltac:(tauto)) as (r & Hin & Hr). exists r. split; [right; exact Hin | exact Hr].
  - assert (HA : ~ (lo <= x < hi)) by lia.
    destruct (IH x ltac:(tauto)) as (r & Hin & Hr). exists r. split; [right; exact Hin | exact Hr].
Qed.

Lemma f2_sh_in : forall lo hi x, lo < hi -> app_mem lo -> app_mem (hi - 1) ->
  (hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo) ->
  shadow_addr lo <= x < shadow_addr hi -> in_shadow x.
Proof.
  intros lo hi x Hlh A1 A2 Hone Hx.
  unfold app_mem, in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
    APPMEM_END in *.
  destruct A1 as [A1|A1]; destruct A2 as [A2|A2]; destruct Hone as [Hone|Hone];
    Z.div_mod_to_equations; lia.
Qed.

Lemma f2_shadow_vs_app : forall y lo hi, in_shadow y -> app_mem lo -> app_mem (hi - 1) -> lo < hi ->
  (hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo) -> y < lo \/ hi <= y.
Proof.
  intros y lo hi Hy A1 A2 Hlh Hone.
  unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *.
  destruct Hy as [Hy|Hy]; destruct A1 as [A1|A1]; destruct A2 as [A2|A2]; destruct Hone as [Hone|Hone]; lia.
Qed.

Lemma f2_rd_of_w : forall (m : word -> option byte) (a : Z), 0 <= a < 2 ^ 64 ->
  ~ AC.a_in_img a -> writable_at rsegs m a -> exists bb, mrd rsegs m (wa a) = Some bb.
Proof.
  intros m a Ha Hni Hw.
  assert (Efs : find_segment rsegs (bv_unsigned (wa a)) 1 = None).
  { destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:Es; [|reflexivity].
    exfalso. apply Hni. destruct (KindBGlue.kb_find_segment _ _ _ _ Es) as (Hin & Hlo & Hhi).
    rewrite wa_unsigned in Hlo, Hhi by lia.
    exists s. split; [exact Hin|]. lia. }
  unfold YP09.writable_at in Hw. change (Z_to_bv 64 a) with (wa a) in Hw.
  destruct (m (wa a)) as [bb|] eqn:E.
  - exists bb. unfold mrd. rewrite E. reflexivity.
  - exfalso. apply Hw. unfold wview. rewrite E, Efs. reflexivity.
Qed.

Lemma f2_cp_rd_lt : forall n fr50 i, In i (RP.cp_rd n fr50) -> (i < 50)%nat.
Proof.
  intros n fr50 i Hi. unfold RP.cp_rd in Hi.
  destruct (negb (50 <=? n)); [cbn in Hi; exfalso; exact Hi|].
  destruct (negb (RP.cp_v fr50 12 =? 0x88)); [cbn in Hi; destruct Hi as [<-|[]]; lia|].
  destruct (negb (RP.cp_v fr50 13 =? 0x19)); [cbn in Hi; destruct Hi as [<-|[<-|[]]]; lia|].
  apply in_app_or in Hi. destruct Hi as [Hi|Hi].
  - apply in_seq in Hi. lia.
  - destruct (RP.cp_rec fr50); [|cbn in Hi; exfalso; exact Hi].
    apply in_app_or in Hi. destruct Hi as [Hi|Hi].
    + cbn in Hi. destruct Hi as [<-|[<-|[<-|[]]]]; lia.
    + apply in_app_or in Hi. destruct Hi as [Hi|Hi].
      * destruct (RP.cp_v fr50 32 =? 0x12); cbn in Hi;
          [destruct Hi as [<-|[]]; lia | exfalso; exact Hi].
      * destruct (RP.cp_kind fr50 =? 6); cbn in Hi;
          [destruct Hi as [<-|[<-|[<-|[]]]]; lia | exfalso; exact Hi].
Qed.

(* The bytes a mrd of a byte list reads. *)
Lemma f2_mrd_of : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  mrd rsegs m (wa (a + Z.of_nat i)) = nth_error bs i.
Proof. intros m a bs i (_ & _ & Hb) Hi. exact (Hb i Hi). Qed.

(* A sub-range of a bytes_at list (a Theorem Labs lane's F3.v (a version not in this delivery)). *)
Lemma f2_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj H Hkj.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as (_ & H).
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn jj (skipn k bs)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

(* A byte that a munch keeps. *)
Lemma f2_mb_keep : forall W m m' x, LF.munch W m m' -> 0 <= x < 2 ^ 64 -> LF.outside W x ->
  mbyte rsegs m' x = mbyte rsegs m x.
Proof.
  intros W m m' x MU Hx Ho. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
  rewrite MState.unsigned_lit by lia. exact Ho.
Qed.

(* The parse output record t_B of every turn has 36 bytes. *)
Lemma f2_tB_len : forall inp j, length (t_B inp j) = 36%nat.
Proof.
  intros inp j. unfold t_B. apply RP.ctrlparse_length.
Qed.

Lemma f2_tg_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.

(* The turn's record length: 0 <= len <= 65535 (the 1- or 2-byte header, capped by the bytes left). *)
Lemma f2_flen_rng : forall g j, 0 <= flen g j <= 65535.
Proof.
  intros g j. pose proof (fc_range (g_in g) j) as R.
  pose proof (inb_range (g_in g) (fc (g_in g) j)) as R1.
  pose proof (inb_range (g_in g) (fc (g_in g) j + 1)) as R2.
  unfold flen, t_len, f_len, f_L, f_h, f_left in *.
  destruct (2 <=? nlen (g_in g) - fc (g_in g) j); lia.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* reac_ctrl_parse, taken on its lib/B contract (a member of SlotLink.callee_contracts), never on its code. A normal
   callee premise, discharged at the top through callee_contracts_holds by the v1.9 image-B proof
   reac_ctrl_parse_holds (lib/B/Prog/reac_ctrl_parse.v of a working branch, not in this delivery). *)
Hypothesis HPARSE : PC.reac_ctrl_parse_contract.

(* The run lemma: an evt on the normalized memory, lifted to SR on the real configuration (R4.v's r4_run). *)
Lemma f2_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> ro_agree rsegs mem ->
  evt rsegs (fun ms => exists R pc' m0', ms = MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs) /\ K R pc' m0')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m0' regs' m' md', K R pc' m0' -> (forall r, getr regs' r = getr R r) ->
     mem_rel rsegs m' m0' -> ro_same rsegs mem m' -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hro HE HK.
  pose proof (evt_normalize rsegs _ (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs) f2_wx Hro HE)
    as HE'.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE' | exact Hh |].
  intros ms' md' (can & (s0 & (R & pc' & m0' & Es0 & HKR) & Hrel & Hsame) & Heq) Hmat.
  subst s0.
  destruct can as [cr cf cp cs cv cc cm co].
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
  subst.
  apply (HK _ _ _ regs' _ md' HKR); [apply KindBGlue.kb_getr_eqv; exact HR | exact E8 | exact Hsame | exact Hmat].
Qed.

(* FRA across a run whose write set W avoids the cells FRA reads outside the frame and keeps every shadow byte
   readable (R4.v's r4_fra). *)
Lemma f2_fra_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) ->
  (forall x, fr <= x < fr + 24 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 56 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 336 <= x < bv_unsigned (getr regs 9) + 344 -> LF.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> LF.outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> LF.outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  bytes_at rsegs mem' (g_p g) (g_in g) ->
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem' (g_p g) (g_n g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HAG' HWA' HFSR HIN1' HIN2' E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - pose proof (f1_relro_range a Hin). lia.
    - pose proof (f1_relro_range a Hin). lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA448|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hfsrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + exact (HFSR Hfsrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (f1_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|]. split; [exact HIN1' | exact HIN2'].
Qed.

(* ---- the parse block: 0x82020 (short frame, len < 50) / 0x81f94 (long frame) -> reac_ctrl_parse ->
   0x82048 / 0x81fbc ----
   f2_PB is the frame-loop state both entries carry (the FCUTP facts of the turn, LK, FC, s6 = 1, the
   first-fragment state and the records); the continuation receives it at the return point together with FPS
   (the parse output t_B at fr + 176 and its 36 addressable bytes) and a0 = t_k.  The record pointer fr + 176 the
   call takes in a2 is read from FLI's spill [A + 280] (0x82040 / 0x81fb4 `ld a2,280(s1)`).  The write set is the
   five record-shadow bytes, the record, the callee window [sp - 8800, sp), the class-1 side-stack cells and the
   shadow of the class-1 frames and of the window (f2_W); the heap invariant is re-derived by AC.a_laws_fs_store;
   FRA moves by f2_fra_run, ENT by ent_munch, the bundles by F1's bundle moves (lib/B/Prog/Seg/R9.v's seg_R9,
   re-pinned). *)
Definition f2_PB (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ rg regs 18 phi /\ rg regs 20 (flen g j) /\
  FTURN g j phi regs m /\ LK g fr j regs m /\ FC g fr j regs m /\ rg regs 22 1 /\ FSj g fr j regs m /\
  REC0 g fr j m.

Lemma f2_parse_seg : forall (pc0 pcm pcr : Z) (j : nat) (g : ghost) regs mem md fr phi,
  (pc0 = 0x82020 /\ pcm = 0x82038 /\ pcr = 0x82048 /\ flen g j < 50) \/
  (pc0 = 0x81f94 /\ pcm = 0x81fac /\ pcr = 0x81fbc /\ 50 <= flen g j) ->
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md ->
  f2_PB g j phi fr regs mem ->
  (forall regs' mem' md',
     FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md' ->
     ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md' ->
     f2_PB g j phi fr regs' mem' -> FPS g fr j mem' -> a0v regs' (t_k (g_in g) j) ->
     SR rsegs (mkCfg (mkst regs' (Z_to_bv 64 pcr) mem' (seg_rom rsegs)) md') (Post B APIf ra g)) ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 pc0) mem (seg_rom rsegs)) md) (Post B APIf ra g).
Proof.
  intros pc0 pcm pcr j g regs mem md fr phi Hpc HFRA HENT HPB Hexit.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  assert (Hpc01 : (pc0 = 0x82020 /\ pcm = 0x82038) \/ (pc0 = 0x81f94 /\ pcm = 0x81fac)) by (clear - Hpc; lia).
  assert (Hpcm : (pcm = 0x82038 /\ pcr = 0x82048) \/ (pcm = 0x81fac /\ pcr = 0x81fbc)) by (clear - Hpc; lia).
  clear Hpc.
  destruct HPB as (Hgn & Hj & HHB & Hr18 & Hr20 & HFT & HLK & HFC & Hr22 & HFSj & HREC).
  pose proof HFT as (H224 & H232 & HPHI & HPHIl).
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  clear Hs5.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKv : PC.REAC_CTRL_PARSE_K = 8800) by reflexivity.
  assert (HFSsz : ASM.FS_SIZE = 11571200) by reflexivity.
  assert (HFSsz2 : AC.FS_SIZE = 11571200) by reflexivity.
  rewrite Haspz in Hlo, Hstkw.
  pose proof (Hplace 8800 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
  assert (HADw : forall a, sp - 8800 <= a < sp -> addressable mem a 1).
  { intros a Ha. apply HWA; [lia|]. destruct Hsep as [Hs|Hs]; lia. }
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  (* ---- the frame is application memory above the image ---- *)
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, AC.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (f1_lw_fs_place (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FSb HAH Hw
                  HFSr) as (HGTb & _ & _ & HFapp).
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (Hfre : 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HGT : AC.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  assert (HLH : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (f2_sf8 fr Hfrm) as HSf8.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  (* ---- the live heap block (Phi, a_size len) ---- *)
  assert (HInblk : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (unfold hb1; cbn [app]; left; reflexivity).
  destruct (f1_lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
              (AC.a_size (flen g j)) HAH HInblk) as (Hp16 & Hp4096 & Hpstklo & HEDd & Hblkb).
  destruct (f2_flen_rng g j) as (HN0 & HNb).
  set (L := AC.a_size (flen g j)) in *.
  assert (HL : L = Z.max (flen g j) 1) by reflexivity.
  assert (HL1 : 1 <= L) by lia.
  assert (HLN : flen g j <= L) by lia.
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  (* ---- the call's class-1 side-stack package, built from FRA (Tac_fsfree's fra_fp) ---- *)
  assert (Ho0 : (fr + 176 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (HWl : PC.reac_ctrl_parse_W (fr + 176) (AC.aspZ regs) =
                [(sp - PC.REAC_CTRL_PARSE_K, sp); (fr + 176, fr + 176 + 36)]).
  { unfold PC.reac_ctrl_parse_W. rewrite Ho0, Haspz. reflexivity. }
  destruct (fra_fp B APIf ra g fr (hb1 phi L) regs mem md [1%nat] PC.REAC_CTRL_PARSE_K
              ((Sfr fr + 22, Sfr fr + 27) :: PC.reac_ctrl_parse_W (fr + 176) (AC.aspZ regs))
              (PC.reac_ctrl_parse_D phi (flen g j) (fr + 176)) HFRA)
    as (FS & FPp & TLSp & HDJfr & HFSfr).
  { intros cc Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; lia. }
  { rewrite HKv, HFN. lia. }
  { intros w Hw. cbn [In] in Hw. rewrite HWl in Hw. cbn [In] in Hw.
    destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    - right; right. unfold Sfr. lia.
    - left. rewrite HKv. lia.
    - right; left. lia. }
  { intros d Hd. unfold PC.reac_ctrl_parse_D in Hd. rewrite Ho0 in Hd.
    destruct (flen g j <? 50) eqn:E50; cbn [app In] in Hd.
    - destruct Hd as [<-|[]]; cbn [fst snd]. right; left. lia.
    - apply Z.ltb_ge in E50.
      destruct Hd as [<-|[<-|[]]]; cbn [fst snd].
      + right; right. split; [lia|]. exists phi, L.
        split; [unfold hb1; cbn [app]; left; reflexivity | lia].
      + right; left. lia. }
  rewrite Haspz in FPp, TLSp.
  rewrite f2_frame1_M in HFSfr.
  (* ---- the side stack ---- *)
  pose proof FPp as FPp0.
  destruct FPp0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HTc & HTPw & HPl & H88c & H96c & HCLs & HFSlo & HAwin &
                    HWdj & HDdj).
  rewrite HKv in HFSlo, HAwin.
  pose proof HPl as HPl0. destruct HPl0 as (HFS0 & HFSmod & HFSgt & HFSapp & HFSstk).
  unfold ASM.ASAN_GT in HFSgt.
  assert (HFS64 : FS + 11571200 <= 2 ^ 64).
  { pose proof (HFSapp (FS + ASM.FS_SIZE - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha. lia. }
  assert (HFSlow : FS + 11571200 <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(lia)) as H1. pose proof (HFSapp (FS + ASM.FS_SIZE - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (EFS : bv_unsigned (Z_to_bv 64 FS) = FS) by (apply MState.unsigned_lit; lia).
  assert (HFSw : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS)
    by (rewrite <- EFS; exact (KindBGlue.bytes_at_le8_word rsegs mem _ (Z_to_bv 64 FS) HTPw)).
  pose proof (HfsS FS HFSw ltac:(lia)) as HFS36.
  destruct (f1_lw_fs_place (APIf rc) (hb1 phi L ++ g_H g) mem md FS HAH HFSw ltac:(lia))
    as (_ & HFSend & _ & _).
  (* ---- the numeric separations ---- *)
  assert (HSfrD : Sfr fr + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= Sfr fr) by lia.
  assert (HShm : Sfr fr + FRAME_SHADOW <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 + 785408 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  assert (HshFS1 : 2147450880 + 785408 <= shadow_addr (FS + 1085440))
    by (clear - HFSgt; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
  assert (HshSP1 : 2147450880 + 785408 <= shadow_addr (sp - 8800))
    by (clear - Hsphm HFN; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
  assert (Hrec22 : shadow_addr (fr + 176) = Sfr fr + 22) by (rewrite <- (f2_sh8 fr 22); f_equal; lia).
  assert (Hrec27 : shadow_addr (fr + 216) = Sfr fr + 27) by (rewrite <- (f2_sh8 fr 27); f_equal; lia).
  assert (M176 : (fr + 176) mod 8 = 0) by (clear - Hfr8; Z.div_mod_to_equations; lia).
  assert (M216 : (fr + 216) mod 8 = 0) by (clear - Hfr8; Z.div_mod_to_equations; lia).
  assert (MFS1 : (FS + 1085440) mod 8 = 0) by (clear - HFSmod; Z.div_mod_to_equations; lia).
  assert (MFS2 : (FS + 2134016) mod 8 = 0) by (clear - HFSmod; Z.div_mod_to_equations; lia).
  assert (MSP1 : (sp - 8800) mod 8 = 0) by (clear - Hspm; Z.div_mod_to_equations; lia).
  assert (MSP : sp mod 8 = 0) by (clear - Hspm; Z.div_mod_to_equations; lia).
  assert (HappA : forall x, A <= x < A + 448 -> app_mem x)
    by (intros x Hx; unfold app_mem; right; lia).
  assert (HappS : forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> app_mem x)
    by (intros x Hx; unfold app_mem; right; lia).
  assert (HappFS1 : forall a, FS + 1085440 <= a < FS + 2134016 -> app_mem a)
    by (intros a Ha; apply HFSapp; lia).
  (* ---- the frame body and the heap block ---- *)
  assert (Hfrdj : forall x, fr <= x < fr + FRAME_BYTES -> ~ (phi <= x < phi + L)).
  { intros x Hx Hin. destruct (Hblkb x Hin) as (_ & _ & _ & _ & Hfsx).
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal x Hx) as Hr. lia.
    - apply Hfsx. exact (Hfs x Hx). }
  assert (Hblkfs : forall a, phi <= a < phi + L -> ~ (FS <= a < FS + 11571200)).
  { intros a Ha Hin. destruct (Hblkb a Ha) as (_ & _ & _ & _ & Hfsx). apply Hfsx.
    exists FS. split; [lia|]. split; [exact HFSw | unfold AC.FS_SIZE; lia]. }
  assert (Hfrd : forall a, fr <= a < fr + FRAME_BYTES -> exists bb, mrd rsegs mem (wa a) = Some bb).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hw). exact (proj2 (Hw a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      pose proof (f1_lw_fs_state_ok (APIf rc) (hb1 phi L ++ g_H g) mem md FSb HAH Hw HFSr) as Hok.
      destruct (f1_lw_fs_ok_cells _ _ Hok a ltac:(lia)) as (_ & bb & Hb). exists bb. exact Hb. }
  assert (Hfstk : stk rsegs mem fr (fr + FRAME_BYTES)).
  { split; [lia|]. split; [lia|]. intros a Ha. split; [exact (Hfrw a Ha) | exact (Hfrd a Ha)]. }
  (* ---- the normalized memory the run is stepped on ---- *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  pose proof (f2_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  pose proof (f2_stk_rel mem (normalize rsegs mem) (sp - FN_STACK) sp HR0 ltac:(lia) Hstkw) as ST0.
  pose proof (f2_stk_rel mem (normalize rsegs mem) fr (fr + FRAME_BYTES) HR0 ltac:(lia) Hfstk) as Hfstk0.
  pose proof (f2_stk_rel mem (normalize rsegs mem) FS (FS + ASM.FS_SIZE) HR0 ltac:(lia) HFSstk) as HFSstk0.
  assert (TBr : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (TBb : forall a bs, bytes_at rsegs (normalize rsegs mem) a bs -> bytes_at rsegs mem a bs)
    by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (HbvS3 : bv_unsigned (getr regs 19) = Sfr fr)
    by (unfold rg in Hr19; rewrite Hr19; apply MState.unsigned_lit; lia).
  assert (Hshstk : stk rsegs (normalize rsegs mem) (Sfr fr + 22) (Sfr fr + 27)).
  { split; [lia|]. split; [lia|]. intros a Ha. apply HSW0.
    replace a with (Sfr fr + (a - Sfr fr)) by lia. apply f2_fsh; [exact Happ' | lia]. }
  destruct (stk_bytes rsegs (normalize rsegs mem) (Sfr fr + 22) (Sfr fr + 27) Hshstk ltac:(lia))
    as (junk5 & Hjl5 & Hjb5).
  assert (RW5 : rw_cells rsegs (normalize rsegs mem) (Sfr fr + 22) [CB 5 junk5]).
  { replace 5%nat with (length junk5) by lia. apply f2_rw_CB; [exact Hjb5|].
    replace (Z.of_nat (length junk5)) with (Sfr fr + 27 - (Sfr fr + 22)) by lia.
    exact (f2_wr_stk _ _ _ Hshstk). }
  (* the 50 header bytes the parse reads, on a long frame *)
  assert (HPHIg : 50 <= flen g j -> bytes_at rsegs mem phi (t_g (g_in g) j))
    by (intros H50; exact (t_g_of_phi mem phi (g_in g) j HPHI H50)).
  assert (HPHIl' : Z.of_nat (length (t_phi (g_in g) j)) = flen g j).
  { rewrite t_phi_length. unfold flen. lia. }
  apply (f2_run regs (Z_to_bv 64 pc0) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 pcr /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\
       getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\ getr R 21 = getr regs 21 /\
       getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
       getr R 10 = Z_to_bv 64 (t_k (g_in g) j) /\
       LF.munch (f2_W (Sfr fr + 22) (fr + 176) sp FS) (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\
       stk rsegs m0' (sp - 8800) sp /\ stk rsegs m0' FS (FS + ASM.FS_SIZE) /\ shadow_rw m0' /\
       addressable m0' (sp - 8800) 8800 /\
       bytes_at rsegs m0' (fr + 176) (t_B (g_in g) j) /\
       (exists b0 b1 b2 b3 b4 : byte, bytes_at rsegs m0' (Sfr fr + 22) [b0; b1; b2; b3; b4] /\
          bv_signed b0 = 0 /\ bv_signed b1 = 0 /\ bv_signed b2 = 0 /\ bv_signed b3 = 0 /\ bv_signed b4 = 4) /\
       RFP.fp [1%nat] m0' (AC.as_tp AC.ASYMS) FS (sp - PC.REAC_CTRL_PARSE_K) sp
         (PC.reac_ctrl_parse_W (fr + 176) sp) (PC.reac_ctrl_parse_D phi (flen g j) (fr + 176)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite f1_mkR_of.
    eapply evt_cut.
    { apply (f2_st (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
               (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
               (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
               (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
               (getr regs 31) fp_regs fp_csr (normalize rsegs mem) junk5 pc0 pcm Hpc01).
      - rewrite HbvS3. exact RW5.
      - exact HMI0. }
    intros ms' (a0' & m1 & bb0 & bb1 & bb2 & bb3 & bb4 & Ems & MU1 & WM1 & MI1 & HB5 & EB0 & EB1 & EB2 &
                EB3 & EB4).
    subst ms'. rewrite HbvS3 in MU1, HB5.
    (* ---- the premises of reac_ctrl_parse, on the memory after the five metadata stores ---- *)
    assert (W1sub : LF.sub_fp [(Sfr fr + 22, Sfr fr + 27)] [(Sfr fr + 22, Sfr fr + 27)])
      by (intros x Hx; exact Hx).
    assert (Hshr : forall x, Sfr fr + 22 <= x < Sfr fr + 27 -> in_shadow x).
    { intros x Hx. replace x with (Sfr fr + (x - Sfr fr)) by lia. apply f2_fsh; [exact Happ' | lia]. }
    assert (TB1 : forall a bs, bytes_at rsegs mem a bs -> 0 <= a ->
               a + Z.of_nat (length bs) <= 2147450880 -> bytes_at rsegs m1 a bs).
    { intros a bs Hb Ha Hlen. eapply fl_bytes; [apply TBr; exact Hb | exact MU1 |].
      intros x Hx. apply KindBGlue.outside_one. left. lia. }
    assert (Hblklh : phi + L <= 2147450880 \/ 17592186044416 + 2147450880 <= phi).
    { pose proof (proj1 (Hblkb phi ltac:(lia))) as A1.
      pose proof (proj1 (Hblkb (phi + L - 1) ltac:(lia))) as A2.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2.
      destruct A1 as [A1|A1]; destruct A2 as [A2|A2]; lia. }
    (* the frame body after the stores; the 36 record bytes as a writable cell block *)
    assert (Hfstk1 : stk rsegs m1 fr (fr + FRAME_BYTES)).
    { eapply stk_transport_disjoint; [exact Hfstk0 | exact MU1 | exact WM1 |].
      cbn [LF.disjoint_from]. split; [lia | exact I]. }
    destruct (stk_split rsegs m1 fr (fr + 176) (fr + FRAME_BYTES) Hfstk1 ltac:(lia)) as (_ & Hf2).
    destruct (stk_split rsegs m1 (fr + 176) (fr + 212) (fr + FRAME_BYTES) Hf2 ltac:(lia)) as (Hrecs & _).
    destruct (stk_bytes rsegs m1 (fr + 176) (fr + 212) Hrecs ltac:(lia)) as (junk36 & Hjl36 & Hjb36).
    assert (RW36 : rw_cells rsegs m1 (fr + 176) [CB 36 junk36]).
    { replace 36%nat with (length junk36) by lia. apply f2_rw_CB; [exact Hjb36|].
      replace (Z.of_nat (length junk36)) with (fr + 212 - (fr + 176)) by lia.
      exact (f2_wr_stk _ _ _ Hrecs). }
    (* the 50 header bytes at Phi after the stores *)
    assert (Hfr50b : 50 <= flen g j -> forall i, (i < 50)%nat ->
              mrd rsegs m1 (wa (phi + Z.of_nat i)) = nth_error (t_g (g_in g) j) i).
    { intros H50 i Hi.
      assert (Hg1 : bytes_at rsegs m1 phi (t_g (g_in g) j)).
      { eapply fl_bytes; [apply TBr; exact (HPHIg H50) | exact MU1 |].
        rewrite f2_tg_len. intros x Hx. apply KindBGlue.outside_one.
        destruct Hblklh as [H|H]; [left | right]; lia. }
      apply (f2_mrd_of m1 phi (t_g (g_in g) j) i Hg1). rewrite f2_tg_len. exact Hi. }
    (* the runtime cells the callee and its bcmp wrapper read *)
    pose proof (AsanRTInv.RT_real_cells _ _ _ HRT) as HREAL.
    pose proof (AsanRTInv.RT_cf_cells _ _ _ HRT) as HCF.
    (* the two real-function slots, found in RT_REALS by computation (positions change between images) *)
    assert (HinB : In (BW.REAL_BCMP, BW.BCMP) RT_REALS).
    { assert (H : existsb (fun p => (fst p =? BW.REAL_BCMP) && (snd p =? BW.BCMP)) RT_REALS = true)
        by (vm_compute; reflexivity).
      apply existsb_exists in H. destruct H as ((a & b) & Hin & Hab).
      apply andb_true_iff in Hab as (H1 & H2). apply Z.eqb_eq in H1, H2. cbn [fst snd] in H1, H2.
      subst a b. exact Hin. }
    assert (HinM : In (BW.REAL_MEMCMP, MC.MEMCMP) RT_REALS).
    { assert (H : existsb (fun p => (fst p =? BW.REAL_MEMCMP) && (snd p =? MC.MEMCMP)) RT_REALS = true)
        by (vm_compute; reflexivity).
      apply existsb_exists in H. destruct H as ((a & b) & Hin & Hab).
      apply andb_true_iff in Hab as (H1 & H2). apply Z.eqb_eq in H1, H2. cbn [fst snd] in H1, H2.
      subst a b. exact Hin. }
    assert (HBCMP1 : bytes_at rsegs m1 BW.REAL_BCMP (le8 (wa BW.BCMP))).
    { pose proof (proj1 (Forall_forall _ _) HREAL _ HinB) as H. cbn [fst snd] in H.
      unfold BW.REAL_BCMP, BW.BCMP. apply TB1; [exact H | lia | rewrite length_le8; lia]. }
    assert (HMCMP1 : bytes_at rsegs m1 BW.REAL_MEMCMP (le8 (wa MC.MEMCMP))).
    { pose proof (proj1 (Forall_forall _ _) HREAL _ HinM) as H. cbn [fst snd] in H.
      unfold BW.REAL_MEMCMP, MC.MEMCMP. apply TB1; [exact H | lia | rewrite length_le8; lia]. }
    destruct HCF as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7 & CF8).
    assert (HGCF1 : bytes_at rsegs m1 BW.GOT_CF (le8 (wa BW.CF))).
    { unfold BW.GOT_CF, BW.CF. unfold RT_GOT_CF, RT_CF in CF1.
      apply TB1; [exact CF1 | lia | rewrite length_le8; lia]. }
    assert (HCF240 : bytes_at rsegs m1 (RT_CF + 240)
              (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0]))
      by (apply TB1; [exact CF7 | unfold RT_CF; lia | cbn [cf_b map length]; unfold RT_CF; lia]).
    assert (HCF254 : bytes_at rsegs m1 (BW.CF + 254) [Z_to_bv 8 1]).
    { destruct HCF240 as (_ & _ & Hb). split; [unfold BW.CF; lia|].
      split; [cbn [length]; unfold BW.CF; lia|].
      intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
      pose proof (Hb 14%nat ltac:(cbn [cf_b map length]; lia)) as E.
      replace (BW.CF + 254 + Z.of_nat 0) with (RT_CF + 240 + Z.of_nat 14) by (unfold BW.CF, RT_CF; lia).
      rewrite E. cbn [cf_b map nth_error]. reflexivity. }
    assert (HCF255 : bytes_at rsegs m1 (BW.CF + 255) [Z_to_bv 8 1]).
    { destruct HCF240 as (_ & _ & Hb). split; [unfold BW.CF; lia|].
      split; [cbn [length]; unfold BW.CF; lia|].
      intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
      pose proof (Hb 15%nat ltac:(cbn [cf_b map length]; lia)) as E.
      replace (BW.CF + 255 + Z.of_nat 0) with (RT_CF + 240 + Z.of_nat 15) by (unfold BW.CF, RT_CF; lia).
      rewrite E. cbn [cf_b map nth_error]. reflexivity. }
    assert (HAC1 : asan_cells m1).
    { eapply fl_asan_cells; [exact (f2_cells_rel mem (normalize rsegs mem) HR0
                                     (AsanRTInv.RT_cells _ _ _ HRT)) | exact MU1 |].
      intros x Hx. apply KindBGlue.outside_one. left. unfold RT_LO, RT_HI in Hx. lia. }
    assert (HSW1 : shadow_rw m1).
    { intros a Ha. destruct (HSW0 a Ha) as (Hv & bb & Hb). split; [apply WM1; exact Hv|].
      destruct (Z_le_gt_dec (Sfr fr + 22) a) as [H1|H1].
      - destruct (Z_lt_ge_dec a (Sfr fr + 27)) as [H2|H2].
        + apply (f1_ba_rd m1 (Sfr fr + 22) _ a HB5). cbn [length]. lia.
        + exists bb. unfold mrd in *. rewrite (MU1 (wa a)); [exact Hb|].
          rewrite wa_unsigned by (destruct (in_shadow_range a Ha); lia).
          apply KindBGlue.outside_one. lia.
      - exists bb. unfold mrd in *. rewrite (MU1 (wa a)); [exact Hb|].
        rewrite wa_unsigned by (destruct (in_shadow_range a Ha); lia).
        apply KindBGlue.outside_one. lia. }
    (* the addressable windows *)
    assert (ADwm : addressable mem (sp - 8800) 8800).
    { split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi.
      destruct (HADw (sp - 8800 + i) ltac:(lia)) as (_ & _ & _ & HA1).
      pose proof (HA1 0 ltac:(lia)) as Hab.
      replace (sp - 8800 + i + 0) with (sp - 8800 + i) in Hab by lia. exact Hab. }
    assert (ADw1 : addressable m1 (sp - PC.REAC_CTRL_PARSE_K) PC.REAC_CTRL_PARSE_K).
    { rewrite HKv. apply (f2_addr_keepW [(Sfr fr + 22, Sfr fr + 27)] (normalize rsegs mem) m1
                            (sp - 8800) 8800 (f2_addr_rel mem (normalize rsegs mem) _ _ HR0 ADwm) MU1).
      intros i Hi. apply KindBGlue.outside_one.
      pose proof (f2_sh_out (fr + 176) (fr + 216) (sp - 8800 + i) M176 M216
                    ltac:(clear - Hsep Hi HFBv; destruct Hsep as [H|H]; lia)) as Hs.
      rewrite Hrec22, Hrec27 in Hs. lia. }
    assert (ADphi1 : 50 <= flen g j -> addressable m1 phi 50).
    { intros H50.
      assert (ADm : addressable mem phi 50).
      { replace phi with (phi + 0) by lia.
        exact (addressable_sub mem phi L 0 50 (proj2 HHB) ltac:(lia) ltac:(lia) ltac:(lia)). }
      apply (f2_addr_keepW [(Sfr fr + 22, Sfr fr + 27)] (normalize rsegs mem) m1 phi 50
               (f2_addr_rel mem (normalize rsegs mem) _ _ HR0 ADm) MU1).
      intros i Hi. apply KindBGlue.outside_one.
      pose proof (f2_sh_out (fr + 176) (fr + 216) (phi + i) M176 M216
                    ltac:(pose proof (Hfrdj (phi + i)) as Hd; clear - Hd Hi H50 HLN HFBv; lia)) as Hs.
      rewrite Hrec22, Hrec27 in Hs. lia. }
    assert (ADrec1 : addressable m1 (fr + 176) 36).
    { unfold Sfr in HB5. exact (f2_addr_rec m1 fr bb0 bb1 bb2 bb3 bb4 Hfr8 ltac:(lia) ltac:(lia)
                  ltac:(intros a Ha; apply Happ'; lia) HB5 EB0 EB1 EB2 EB3 EB4). }
    assert (ADbc1 : addressable m1 PC.REAC_CTRL_PARSE_BC 6).
    { assert (ADbcm : addressable mem PC.REAC_CTRL_PARSE_BC 6).
      { split; [unfold PC.REAC_CTRL_PARSE_BC; lia|]. split; [lia|].
        split; [unfold PC.REAC_CTRL_PARSE_BC; lia|].
        intros i Hi.
        destruct (HAG (PC.REAC_CTRL_PARSE_BC + i) ltac:(exists 0x21200, 7; split;
                        [unfold AF.frame_AG; cbn [In]; tauto | unfold PC.REAC_CTRL_PARSE_BC; lia]))
          as (_ & _ & _ & HA1).
        pose proof (HA1 0 ltac:(lia)) as Hab.
        replace (PC.REAC_CTRL_PARSE_BC + i + 0) with (PC.REAC_CTRL_PARSE_BC + i) in Hab by lia. exact Hab. }
      apply (f2_addr_keepW [(Sfr fr + 22, Sfr fr + 27)] (normalize rsegs mem) m1
               PC.REAC_CTRL_PARSE_BC 6 (f2_addr_rel mem (normalize rsegs mem) _ _ HR0 ADbcm) MU1).
      intros i Hi. apply KindBGlue.outside_one. left.
      pose proof (f2_sa_lo (PC.REAC_CTRL_PARSE_BC + i) ltac:(unfold PC.REAC_CTRL_PARSE_BC; lia)) as Hsa.
      unfold ASAN_K in Hsa. lia. }
    (* the side-stack state after the stores *)
    assert (FP0 : RFP.fp [1%nat] (normalize rsegs mem) (AC.as_tp AC.ASYMS) FS
                    (sp - PC.REAC_CTRL_PARSE_K) sp
                    ((Sfr fr + 22, Sfr fr + 27) :: PC.reac_ctrl_parse_W (fr + 176) sp)
                    (PC.reac_ctrl_parse_D phi (flen g j) (fr + 176))).
    { apply (f2_fp_tr _ mem); [exact TBr | | exact FPp].
      intros _. exact HFSstk0. }
    assert (FP1 : RFP.fp [1%nat] m1 (AC.as_tp AC.ASYMS) FS (sp - PC.REAC_CTRL_PARSE_K) sp
                    ((Sfr fr + 22, Sfr fr + 27) :: PC.reac_ctrl_parse_W (fr + 176) sp)
                    (PC.reac_ctrl_parse_D phi (flen g j) (fr + 176)))
      by exact (f2_fp_keep _ _ _ _ _ _ _ _ _ _ _ _ FP0 MU1 WM1 W1sub Hshr).
    assert (TLS1 : PC.reac_ctrl_parse_tls m1 (AC.as_tp AC.ASYMS) FS (sp - PC.REAC_CTRL_PARSE_K) sp).
    { unfold PC.reac_ctrl_parse_tls. intros DT TS C T DB k HT.
      apply (f2_tls_keep _ (normalize rsegs mem) m1 _ FS _ _ _ _ _ _ _ _ FP0 MU1 W1sub); [|exact HT].
      intros DT' TS' C' T' DB' k' HT'.
      apply TLSp. exact (f2_atls_tr (normalize rsegs mem) mem _ _ _ _ _ _ _ TBb HT'). }
    assert (HbvTP : bv_unsigned (getr regs 4) = AC.as_tp AC.ASYMS)
      by (rewrite Hr4; apply MState.unsigned_lit; unfold AC.as_tp, AC.ASYMS; cbn; lia).
    (* the record pointer the call loads (0x82040 / 0x81fb4 `ld a2,280(s1)`): FLI's spill [A + 280] = fr + 176,
       which the five shadow stores keep *)
    assert (H280 : q64 mem (A + 280) (fr + 176)).
    { destruct HLK as (_ & _ & _ & HFLIx).
      destruct HFLIx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HS280 & _).
      exact (f2_spill_q64 regs mem 280 (fr + 176) A HS280 Hr9 ltac:(lia) ltac:(lia) ltac:(lia)). }
    assert (H280m1 : q64 m1 (A + 280) (fr + 176)).
    { unfold q64 in *. eapply fl_bytes; [apply TBr; exact H280 | exact MU1 |].
      rewrite length_le8. intros x Hx. apply KindBGlue.outside_one. right. lia. }
    pose proof (bytes_at_ov_read rsegs m1 (A + 280) (le8 (Z_to_bv 64 (fr + 176))) 0 8 H280m1
                  ltac:(rewrite length_le8; lia)) as RD280.
    cbn [Z.of_nat] in RD280. rewrite Z.add_0_r, skipn_O, firstn_all2 in RD280 by (rewrite length_le8; lia).
    eapply evt_mono.
    + apply (f2_pcall HPARSE) with (spv := sp) (phi := phi) (N := flen g j) (o := fr + 176)
        (FS := FS) (fr50 := t_g (g_in g) j) (junk := junk36) (pcm := pcm) (pcr := pcr) (A := A).
      * exact Hpcm.
      * unfold rg in Hr18. exact Hr18.
      * unfold rg in Hr20. exact Hr20.
      * unfold rg in Hr9. exact Hr9.
      * unfold rg in Hr2. exact Hr2.
      * lia.
      * lia.
      * exact RD280.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact Hspm.
      * lia.
      * lia.
      * lia.
      * rewrite HKv.
        destruct (stk_split rsegs (normalize rsegs mem) (sp - FN_STACK) (sp - 8800) sp ST0 ltac:(lia))
          as (_ & Hs).
        eapply stk_transport_disjoint; [exact Hs | exact MU1 | exact WM1 |].
        cbn [LF.disjoint_from]. split; [lia | exact I].
      * exact MI1.
      * apply f2_tg_len.
      * intros H50. split; [lia|]. split; [lia|]. left. rewrite HKv. lia.
      * intros i Hi. destruct (Z_lt_le_dec (flen g j) 50) as [Hs|Hb].
        -- exfalso. unfold RP.cp_rd in Hi. rewrite (proj2 (Z.leb_gt 50 (flen g j)) Hs) in Hi. cbn in Hi.
           exact Hi.
        -- exact (Hfr50b Hb i (f2_cp_rd_lt _ _ _ Hi)).
      * clear - Hfr8. Z.div_mod_to_equations; lia.
      * lia.
      * exact RW36.
      * rewrite HKv. lia.
      * intros H50. destruct (Z_le_gt_dec (fr + 212) phi) as [H|H]; [left; lia|].
        right. destruct (Z_le_gt_dec (phi + L) (fr + 176)) as [H2|H2]; [lia|].
        exfalso. exact (Hfrdj (Z.max phi (fr + 176)) ltac:(lia) ltac:(lia)).
      * exact HAC1.
      * exact HSW1.
      * exact ADw1.
      * exact ADphi1.
      * exact ADrec1.
      * apply Happ'. lia.
      * right. unfold BW.CF. lia.
      * exact ADbc1.
      * exact HBCMP1.
      * exact HMCMP1.
      * exact HGCF1.
      * exact HCF254.
      * exact HCF255.
      * rewrite HbvTP. exact (f2_fp_drop _ _ _ _ _ _ _ _ _ FP1).
      * rewrite HbvTP. exact TLS1.
    + intros ms2 (R & m' & Hms & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P22 & P21 & P26 & P27 & P10 &
                  MU2 & WM2 & MI2 & ST2 & AC2 & SW2 & RW2 & ADc2 & FP2).
      exists R, (Z_to_bv 64 pcr), m'. split; [exact Hms|].
      split; [reflexivity|].
      split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P18|]. split; [exact P19|]. split; [exact P20|].
      split; [exact P22|]. split; [exact P21|]. split; [exact P26|]. split; [exact P27|].
      split; [exact P10|].
      assert (MU2' : LF.munch (f2_W2 (fr + 176) sp FS) m1 m')
        by exact (LF.munch_weaken _ _ _ _ (f2_W2_sub (fr + 176) sp FS ltac:(lia)) MU2).
      split.
      { assert (MU1' : LF.munch [(Sfr fr + 22, Sfr fr + 22 + 5)] (normalize rsegs mem) m1)
          by (replace (Sfr fr + 22 + 5) with (Sfr fr + 27) by lia; exact MU1).
        eapply LF.munch_trans.
        - exact (LF.munch_weaken _ _ _ _ (f2_W_sub5 (Sfr fr + 22) (fr + 176) sp FS) MU1').
        - exact (LF.munch_weaken _ _ _ _ (f2_W_sub (Sfr fr + 22) (fr + 176) sp FS ltac:(lia)) MU2). }
      split; [exact (LF.wmono_trans rsegs _ _ _ WM1 WM2)|].
      split; [rewrite HKv in ST2; exact ST2|].
      pose proof FP2 as FP2c. rewrite HbvTP in FP2c.
      split.
      { destruct FP2 as (DT2 & TS2 & C2 & T2 & DB2 & k2 & HT2 & HTP2 & HPl2 & _).
        destruct HPl2 as (_ & _ & _ & _ & HS2). exact HS2. }
      split; [exact SW2|].
      split; [rewrite HKv in ADc2; exact ADc2|].
      split.
      { destruct RW2 as ((Hwf & Hb) & _). cbn [cbytes cells_bytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
      split.
      { exists bb0, bb1, bb2, bb3, bb4.
        split; [|split; [exact EB0 | split; [exact EB1 | split; [exact EB2 | split; [exact EB3 | exact EB4]]]]].
        eapply fl_bytes; [exact HB5 | exact MU2' |].
        intros x Hx. cbn [length] in Hx.
        assert (Hsha : in_shadow x) by (apply Hshr; lia).
        apply f2_out2.
        - exact (f2_shadow_vs_app _ (fr + 176) (fr + 176 + 36) Hsha ltac:(apply Happ'; lia)
                   ltac:(apply Happ'; lia) ltac:(lia) ltac:(destruct HLH as [H|H]; lia)).
        - exact (f2_shadow_vs_app _ (sp - 8800) sp Hsha ltac:(apply HAwin; lia) ltac:(apply HAwin; lia)
                   ltac:(lia) ltac:(right; lia)).
        - exact (f2_shadow_vs_app _ (FS + 8) (FS + 16) Hsha ltac:(apply HFSapp; lia)
                   ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
        - exact (f2_shadow_vs_app _ (FS + 20480) (FS + 28672) Hsha ltac:(apply HFSapp; lia)
                   ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
        - exact (f2_shadow_vs_app _ (FS + 1085440) (FS + 2134016) Hsha ltac:(apply HFSapp; lia)
                   ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
        - assert (Ex : x = shadow_addr (fr + 8 * (x - Sfr fr))) by (rewrite f2_sh8; lia).
          pose proof (f2_sh_out (FS + 1085440) (FS + 2134016) (fr + 8 * (x - Sfr fr)) MFS1 MFS2 ltac:(lia)) as Hs.
          rewrite <- Ex in Hs. exact Hs.
        - assert (Ex : x = shadow_addr (fr + 8 * (x - Sfr fr))) by (rewrite f2_sh8; lia).
          pose proof (f2_sh_out (sp - 8800) sp (fr + 8 * (x - Sfr fr)) MSP1 MSP
                        ltac:(destruct Hsep as [H|H]; lia)) as Hs.
          rewrite <- Ex in Hs. exact Hs. }
      exact FP2c.
  - intros R pc' m0' regs'' mem' md'
      (Hpc' & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K22 & K21 & K26 & K27 & K10 &
       MU0 & WM0 & STw0 & STFS0 & SW0' & ADw0 & HRecB & HRecS & FPm0)
      Hreg HRel Hsame Hmat.
    clear Hpc01 Hpcm.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 (t_k (g_in g) j)) by (rewrite Hreg; exact K10).
    (* ---- back from the normalized memory to the real one ---- *)
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    pose proof (f2_stk_back mem' m0' (sp - 8800) sp HRel ltac:(lia) STw0) as STw.
    pose proof (f2_stk_back mem' m0' FS (FS + ASM.FS_SIZE) HRel ltac:(lia) STFS0) as STFS.
    pose proof (f2_srw_back mem' m0' HRel SW0') as SW'.
    assert (TBb2 : forall a bs, bytes_at rsegs m0' a bs -> bytes_at rsegs mem' a bs)
      by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem' m0' a bs HRel) Hb)).
    assert (HRecR : bytes_at rsegs mem' (fr + 176) (t_B (g_in g) j)) by (apply TBb2; exact HRecB).
    destruct HRecS as (cb0 & cb1 & cb2 & cb3 & cb4 & HRecS & EC0 & EC1 & EC2 & EC3 & EC4).
    assert (HRecSR : bytes_at rsegs mem' (Sfr fr + 22) [cb0; cb1; cb2; cb3; cb4]) by (apply TBb2; exact HRecS).
    assert (FPm : RFP.fp [1%nat] mem' (AC.as_tp AC.ASYMS) FS (sp - PC.REAC_CTRL_PARSE_K) sp
                    (PC.reac_ctrl_parse_W (fr + 176) sp) (PC.reac_ctrl_parse_D phi (flen g j) (fr + 176)))
      by exact (f2_fp_tr [1%nat] m0' mem' _ _ _ _ _ _ TBb2 (fun _ => STFS) FPm0).
    pose proof (f2_addr_back mem' m0' (sp - 8800) 8800 HRel ADw0) as ADw'.
    assert (Hblkfr : forall i, 0 <= i < L -> phi + i < fr \/ fr + FRAME_BYTES <= phi + i).
    { intros i Hi. destruct (Z_lt_le_dec (phi + i) fr) as [H|H]; [left; exact H|].
      destruct (Z_lt_le_dec (phi + i) (fr + FRAME_BYTES)) as [H2|H2]; [|right; exact H2].
      exfalso. exact (Hfrdj (phi + i) ltac:(lia) ltac:(lia)). }
    (* ---- every written byte is readable after the run ---- *)
    assert (RDW : forall x, ~ LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) x ->
              exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. destruct (f2_not_out _ _ Hx) as (r & Hin & Hr).
      unfold f2_W, f2_W2 in Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd] in Hr.
      - assert (Hs : in_shadow x)
          by (replace x with (Sfr fr + (x - Sfr fr)) by lia; apply f2_fsh; [exact Happ' | lia]).
        exact (proj2 (SW' x Hs)).
      - apply (f1_ba_rd mem' (fr + 176) _ x HRecR). rewrite f2_tB_len. lia.
      - destruct STw as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - destruct STFS as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - destruct STFS as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - destruct STFS as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - assert (Hs : in_shadow x)
          by exact (f2_sh_in (FS + 1085440) (FS + 2134016) x ltac:(lia) ltac:(apply HFSapp; lia)
                      ltac:(apply HFSapp; lia) ltac:(destruct HFSlow as [H|H]; lia) Hr).
        exact (proj2 (SW' x Hs)).
      - assert (Hs : in_shadow x)
          by exact (f2_sh_in (sp - 8800) sp x ltac:(lia) ltac:(apply HAwin; lia) ltac:(apply HAwin; lia)
                      ltac:(right; lia) Hr).
        exact (proj2 (SW' x Hs)). }
    (* ---- the heap invariant and stklo, by the side-stack store law ---- *)
    assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
      by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
    assert (HFSuniq : forall b', AC.a_in_fs AC.ASYMS mem b' -> FS <= b' < FS + AC.FS_SIZE).
    { intros b' (cc & Hcc & Hw & Hrr).
      assert (Ecc : cc = FS).
      { assert (Hb1 : bytes_at rsegs mem (AC.as_tp AC.ASYMS) (le8 (Z_to_bv 64 cc)))
          by exact (KindBGlue.word_mem_le8 rsegs mem (AC.as_tp AC.ASYMS) cc Hw ltac:(lia)
                      ltac:(unfold AC.as_tp, AC.ASYMS; cbn; lia) ltac:(unfold AC.as_tp, AC.ASYMS; cbn; lia)).
        assert (Hb2 : bytes_at rsegs mem (AC.as_tp AC.ASYMS) (le8 (Z_to_bv 64 FS)))
          by exact (KindBGlue.word_mem_le8 rsegs mem (AC.as_tp AC.ASYMS) FS HFSw ltac:(lia)
                      ltac:(unfold AC.as_tp, AC.ASYMS; cbn; lia) ltac:(unfold AC.as_tp, AC.ASYMS; cbn; lia)).
        pose proof (fl_le8_eq [] mem mem (AC.as_tp AC.ASYMS) (Z_to_bv 64 cc) (Z_to_bv 64 FS) Hb1 Hb2
                      (LF.munch_refl [] mem) (fun x _ => I)) as E.
        pose proof (f_equal bv_unsigned E) as E'.
        rewrite !MState.unsigned_lit in E' by lia. exact E'. }
      subst cc. unfold AC.FS_SIZE. lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ AC.a_store_ok (hb1 phi L ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (FS <= q < FS + AC.FS_SIZE) ->
              ~ (exists bb, FS <= bb < FS + AC.FS_SIZE /\ q = shadow_addr bb) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hnok Hnfs Hnsh.
      destruct (f2_out_dec (f2_W (Sfr fr + 22) (fr + 176) sp FS) q) as [Ho|Hno].
      - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
      - exfalso. destruct (f2_not_out _ _ Hno) as (r & Hin & Hr).
        assert (Ebb : shadow_addr (8 * (q - 2147450880)) = q)
          by (unfold shadow_addr, ASAN_K; rewrite Z.mul_comm, Z.div_mul by lia; lia).
        unfold f2_W, f2_W2 in Hin. cbn [In] in Hin.
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd] in Hr.
        + destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
          * apply Hnok. right. right. right. exists (8 * (q - 2147450880)).
            split; [symmetry; exact Ebb|]. right. left. apply Hreal. lia.
          * apply Hnsh. exists (8 * (q - 2147450880)).
            split; [exact (HFSuniq _ (Hfs (8 * (q - 2147450880)) ltac:(lia))) | symmetry; exact Ebb].
        + destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
          * apply Hnok. right. left. apply Hreal. lia.
          * apply Hnfs. exact (HFSuniq _ (Hfs q ltac:(lia))).
        + apply Hnok. right. left. lia.
        + apply Hnfs. unfold AC.FS_SIZE. lia.
        + apply Hnfs. unfold AC.FS_SIZE. lia.
        + apply Hnfs. unfold AC.FS_SIZE. lia.
        + apply Hnsh. exists (8 * (q - 2147450880)).
          split; [unfold AC.FS_SIZE; unfold shadow_addr, ASAN_K in Hr; Z.div_mod_to_equations; lia
                 | symmetry; exact Ebb].
        + apply Hnok. right. right. right. exists (8 * (q - 2147450880)).
          split; [symmetry; exact Ebb|]. right. left.
          unfold shadow_addr, ASAN_K in Hr. Z.div_mod_to_equations. lia. }
    assert (HFSOK : AC.a_fs_ok mem FS)
      by exact (f1_lw_fs_state_ok (APIf rc) (hb1 phi L ++ g_H g) mem md FS HAH HFSw ltac:(lia)).
    assert (HFSOK' : AC.a_fs_ok mem' FS).
    { apply (f2_fs_ok mem mem' (AC.as_tp AC.ASYMS) FS (sp - PC.REAC_CTRL_PARSE_K) sp
               (PC.reac_ctrl_parse_W (fr + 176) sp) (PC.reac_ctrl_parse_D phi (flen g j) (fr + 176))
               (f2_W (Sfr fr + 22) (fr + 176) sp FS) HFSOK FPm MU).
      - intros x Hx. apply f2_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | destruct HFSlow as [H|H]; lia | lia | lia | lia | lia | lia].
      - intros x Hx. apply f2_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | destruct HFSlow as [H|H]; lia | lia | lia | lia | lia | lia].
      - intros x Hx. apply f2_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | destruct HFSlow as [H|H]; lia | lia | lia | lia | lia | lia].
      - intros x Hx. apply f2_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | destruct HFSlow as [H|H]; lia | lia | lia | lia | lia | lia]. }
    destruct (f1_lw_fs_store (APIf rc) (hb1 phi L ++ g_H g) mem mem' md FS HAH HFSw
                ltac:(lia) Hagree Hwrit HFSOK') as (HAH' & HOWN'' & HSTK' & HSTKhi').
    (* ---- FRA at the memory after the run ---- *)
    assert (HDJ : rt_disjoint (f2_W (Sfr fr + 22) (fr + 176) sp FS)).
    { unfold AsanRTInv.rt_disjoint, f2_W, f2_W2, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
        RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM,
        RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
      cbn [LF.disjoint_from]. repeat split; first [exact I | lia]. }
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
      { split; [lia|]. split; [lia|]. intros a Ha. apply SW'.
        replace a with (Sfr fr + (a - Sfr fr)) by lia. apply f2_fsh; [exact Happ' | lia]. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. f_equal. lia. }
    assert (HimgOut : forall y, 2147450880 <= y < 2147450880 + 785408 ->
              LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) y).
    { intros y Hy. apply f2_out;
        clear - Hy HSK HLH Hsphm HFN HFSlow HFS64 HshFS1 HshSP1 HLMv HHMv HFBv;
        first [ lia | destruct HLH as [H|H]; lia | destruct HFSlow as [H|H]; lia ]. }
    assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (f2_sa_lo a (f2_ag_lo a Ha)) as Hsa. unfold ASAN_K in Hsa.
      apply (f2_addr_keepW (f2_W (Sfr fr + 22) (fr + 176) sp FS) mem mem' a 1 (HAG a Ha) MU).
      intros i Hi. replace (a + i) with a by lia. apply HimgOut. lia. }
    assert (HWlo : forall x, 0 <= x < 6283264 -> LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) x)
      by (intros x Hx; apply f2_out; lia).
    assert (HWhdr : forall x, fr <= x < fr + 24 -> LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) x).
    { intros x Hx. apply f2_out_app; [apply Happ'; lia | exact HappFS1 | exact HAwin
        | destruct HSfrD as [H|H]; lia | lia | destruct Hsep as [H|H]; lia | lia | lia | lia]. }
    assert (HWsel : forall x, bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 56 ->
              LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) x).
    { intros x Hx. rewrite HbvA in Hx. apply f2_out_app; [apply HappA; lia | exact HappFS1 | exact HAwin
        | lia | lia | lia | lia | lia | lia]. }
    assert (HWspill : forall x, bv_unsigned (getr regs 9) + 336 <= x < bv_unsigned (getr regs 9) + 344 ->
              LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) x).
    { intros x Hx. rewrite HbvA in Hx. apply f2_out_app; [apply HappA; lia | exact HappFS1 | exact HAwin
        | lia | lia | lia | lia | lia | lia]. }
    assert (HWsaved : forall x, g_S g - 104 <= x < g_S g ->
              LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) x).
    { intros x Hx. apply f2_out_app; [apply HappS; lia | exact HappFS1 | exact HAwin
        | lia | lia | lia | lia | lia | lia]. }
    assert (HWwin : forall x, g_S g - AF.SLOT_STACK <= x < g_S g ->
              LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) x \/
              exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. destruct (f2_out_dec (f2_W (Sfr fr + 22) (fr + 176) sp FS) x) as [Ho|Hno];
        [left; exact Ho | right; exact (RDW x Hno)]. }
    assert (HoutFR : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 176 <= x < fr + 212) ->
              LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) x).
    { intros x Hx Hx2. apply f2_out_app; [apply Happ'; lia | exact HappFS1 | exact HAwin
        | destruct HSfrD as [H|H]; lia | lia | destruct Hsep as [H|H]; lia | lia | lia | lia]. }
    assert (HoutAPP : forall x, app_mem x -> x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
              ~ AC.a_in_fs AC.ASYMS mem x -> ~ (fr <= x < fr + FRAME_BYTES) ->
              LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) x).
    { intros x Hx Hxlo Hxfs Hxfr.
      assert (HxFS : ~ (FS <= x < FS + 11571200))
        by (intros Hc; apply Hxfs; apply (a_fs_in AC.ASYMS mem FS x HFSw); lia).
      pose proof Hx as Hx'. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hx'.
      apply f2_out_app; [exact Hx | exact HappFS1 | exact HAwin | | | | | |].
      all: clear - Hx' HSK HShm Hxfr Hxlo Hlo HFN HxFS HFBv HFSv; lia. }
    assert (HoutFRsh : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 176 <= x < fr + 216) ->
              LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) (shadow_addr x)).
    { intros x Hx Hx2.
      assert (Hsha : in_shadow (shadow_addr x)) by (apply shadow_of_app; apply Happ'; lia).
      apply f2_out.
      - pose proof (f2_sh_out (fr + 176) (fr + 216) x M176 M216 ltac:(lia)) as Hs.
        rewrite Hrec22, Hrec27 in Hs. lia.
      - exact (f2_shadow_vs_app _ (fr + 176) (fr + 176 + 36) Hsha ltac:(apply Happ'; lia)
                 ltac:(apply Happ'; lia) ltac:(lia) ltac:(destruct HLH as [H|H]; lia)).
      - exact (f2_shadow_vs_app _ (sp - 8800) sp Hsha ltac:(apply HAwin; lia) ltac:(apply HAwin; lia)
                 ltac:(lia) ltac:(right; lia)).
      - exact (f2_shadow_vs_app _ (FS + 8) (FS + 16) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (f2_shadow_vs_app _ (FS + 20480) (FS + 28672) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (f2_shadow_vs_app _ (FS + 1085440) (FS + 2134016) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (f2_sh_out (FS + 1085440) (FS + 2134016) x MFS1 MFS2 ltac:(lia)).
      - exact (f2_sh_out (sp - 8800) sp x MSP1 MSP ltac:(destruct Hsep as [H|H]; lia)). }
    assert (HoutSH : forall y, app_mem y -> y < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
              ~ AC.a_in_fs AC.ASYMS mem y -> ~ (fr <= y < fr + FRAME_BYTES) ->
              LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) (shadow_addr y)).
    { intros y Hy Hylo Hyfs Hyfr.
      assert (Hsha : in_shadow (shadow_addr y)) by (apply shadow_of_app; exact Hy).
      assert (HyFS : ~ (FS <= y < FS + 11571200))
        by (intros Hc; apply Hyfs; apply (a_fs_in AC.ASYMS mem FS y HFSw); lia).
      apply f2_out.
      - pose proof (f2_sh_out (fr + 176) (fr + 216) y M176 M216 ltac:(lia)) as Hs.
        rewrite Hrec22, Hrec27 in Hs. lia.
      - exact (f2_shadow_vs_app _ (fr + 176) (fr + 176 + 36) Hsha ltac:(apply Happ'; lia)
                 ltac:(apply Happ'; lia) ltac:(lia) ltac:(destruct HLH as [H|H]; lia)).
      - exact (f2_shadow_vs_app _ (sp - 8800) sp Hsha ltac:(apply HAwin; lia) ltac:(apply HAwin; lia)
                 ltac:(lia) ltac:(right; lia)).
      - exact (f2_shadow_vs_app _ (FS + 8) (FS + 16) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (f2_shadow_vs_app _ (FS + 20480) (FS + 28672) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (f2_shadow_vs_app _ (FS + 1085440) (FS + 2134016) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (f2_sh_out (FS + 1085440) (FS + 2134016) y MFS1 MFS2 ltac:(lia)).
      - exact (f2_sh_out (sp - 8800) sp y MSP1 MSP ltac:(lia)). }
    (* the input block: an entry block, so app memory below stklo, outside the frame and the side stack *)
    assert (HINb : forall x, g_p g <= x < g_p g + g_n g ->
              app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
              ~ AC.a_in_fs AC.ASYMS mem x /\ ~ (fr <= x < fr + FRAME_BYTES)).
    { intros x Hx.
      destruct (Hinblk ltac:(lia)) as (Hin & _).
      destruct (f1_lw_blocks (APIf rc) (hb1 phi L ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hstk2 & _ & Hall).
      destruct (Hall x Hx) as (Happq & _ & _ & _ & Hnfs).
      split; [exact Happq|]. split; [lia|]. split; [exact Hnfs|].
      intros Hc. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
      - pose proof (Hreal x Hc) as Hr. lia.
      - exact (Hnfs (Hfs x Hc)). }
    destruct (fra_in_keep_sh g mem mem' (f2_W (Sfr fr + 22) (fr + 176) sp FS) Hinb Hinblk MU
                ltac:(intros x Hx; destruct (HINb x Hx) as (H1 & H2 & H3 & H4);
                      split; [apply HoutAPP | apply HoutSH]; assumption)) as (HIN1' & HIN2').
    assert (HoutWINsh : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
              ~ (sp - 8800 <= a < sp) ->
              LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) (shadow_addr a)).
    { intros a Ha Hafr Hawin.
      assert (Haapp : app_mem a) by (apply HappS; lia).
      assert (Hsha : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Haapp).
      apply f2_out.
      - pose proof (f2_sh_out (fr + 176) (fr + 216) a M176 M216 ltac:(lia)) as Hs.
        rewrite Hrec22, Hrec27 in Hs. lia.
      - exact (f2_shadow_vs_app _ (fr + 176) (fr + 176 + 36) Hsha ltac:(apply Happ'; lia)
                 ltac:(apply Happ'; lia) ltac:(lia) ltac:(destruct HLH as [H|H]; lia)).
      - exact (f2_shadow_vs_app _ (sp - 8800) sp Hsha ltac:(apply HAwin; lia) ltac:(apply HAwin; lia)
                 ltac:(lia) ltac:(right; lia)).
      - exact (f2_shadow_vs_app _ (FS + 8) (FS + 16) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (f2_shadow_vs_app _ (FS + 20480) (FS + 28672) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (f2_shadow_vs_app _ (FS + 1085440) (FS + 2134016) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (f2_sh_out (FS + 1085440) (FS + 2134016) a MFS1 MFS2 ltac:(lia)).
      - exact (f2_sh_out (sp - 8800) sp a MSP1 MSP ltac:(lia)). }
    assert (HWA' : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
              addressable mem' a 1).
    { intros a Ha1 Ha2.
      destruct (Z_le_gt_dec (sp - 8800) a) as [HL0|HL0]; [destruct (Z_lt_ge_dec a sp) as [HU|HU]|].
      - replace a with (sp - 8800 + (a - (sp - 8800))) by lia.
        apply (addressable_sub mem' (sp - 8800) 8800); [exact ADw' | lia | lia | lia].
      - apply (f2_addr_keepW (f2_W (Sfr fr + 22) (fr + 176) sp FS) mem mem' a 1 (HWA a Ha1 Ha2) MU).
        intros i Hi. replace (a + i) with a by lia. apply HoutWINsh; lia.
      - apply (f2_addr_keepW (f2_W (Sfr fr + 22) (fr + 176) sp FS) mem mem' a 1 (HWA a Ha1 Ha2) MU).
        intros i Hi. replace (a + i) with a by lia. apply HoutWINsh; lia. }
    (* ENT across the run: no written byte is one ENT reads *)
    assert (HKEPT : forall x, ent_kept g x -> LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) x).
    { intros x Hk.
      destruct Hk as [(q & kk & i & Hin & Hni & Hi & ->) |
                      [Hik | [Habk | [(bq & Hor & ->) | (q & kk & i & Hin & Hni & Hi & ->)]]]].
      - destruct (f1_lw_blocks (APIf rc) (hb1 phi L ++ g_H g) mem md q kk HAH
                    (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hqstk & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        apply HoutAPP; [exact Happq | lia | exact Hnfs |].
        intros Hc. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
        + pose proof (Hreal (q + i) Hc) as Hr. lia.
        + exact (Hnfs (Hfs (q + i) Hc)).
      - apply HWlo. pose proof (img_below_GT x Hik) as Hx. unfold AC.GT in Hx. lia.
      - apply f2_out_app; [unfold app_mem; right; lia | exact HappFS1 | exact HAwin
          | lia | lia | lia | lia | lia | lia].
      - assert (Hb0 : (0 <= bq < 6283264) \/ (g_S g <= bq < APPMEM_END)).
        { destruct Hor as [Hi|Hr]; [left; pose proof (img_below_GT bq Hi) as Hx; unfold AC.GT in Hx; lia
                                   | right; exact Hr]. }
        assert (Hbapp : app_mem bq)
          by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; destruct Hb0; lia).
        assert (Hsha : in_shadow (shadow_addr bq)) by (apply shadow_of_app; exact Hbapp).
        apply f2_out.
        + pose proof (f2_sh_out (fr + 176) (fr + 216) bq M176 M216 ltac:(destruct Hb0; lia)) as Hs.
          rewrite Hrec22, Hrec27 in Hs. lia.
        + exact (f2_shadow_vs_app _ (fr + 176) (fr + 176 + 36) Hsha ltac:(apply Happ'; lia)
                   ltac:(apply Happ'; lia) ltac:(lia) ltac:(destruct HLH as [H|H]; lia)).
        + exact (f2_shadow_vs_app _ (sp - 8800) sp Hsha ltac:(apply HAwin; lia) ltac:(apply HAwin; lia)
                   ltac:(lia) ltac:(right; lia)).
        + exact (f2_shadow_vs_app _ (FS + 8) (FS + 16) Hsha ltac:(apply HFSapp; lia)
                   ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
        + exact (f2_shadow_vs_app _ (FS + 20480) (FS + 28672) Hsha ltac:(apply HFSapp; lia)
                   ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
        + exact (f2_shadow_vs_app _ (FS + 1085440) (FS + 2134016) Hsha ltac:(apply HFSapp; lia)
                   ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
        + exact (f2_sh_out (FS + 1085440) (FS + 2134016) bq MFS1 MFS2 ltac:(destruct Hb0; lia)).
        + exact (f2_sh_out (sp - 8800) sp bq MSP1 MSP ltac:(destruct Hb0; lia)).
      - (* ENT append #1: the shadow of an entry block (app memory below stklo, off the side stack and the
           frame) *)
        destruct (f1_lw_blocks (APIf rc) (hb1 phi L ++ g_H g) mem md q kk HAH
                    (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hqstk & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        apply HoutSH; [exact Happq | lia | exact Hnfs |].
        intros Hc. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
        + pose proof (Hreal (q + i) Hc) as Hr'. lia.
        + exact (Hnfs (Hfs (q + i) Hc)). }
    assert (HENT' : ENT APIf g (hb1 phi L) mem' md).
    { eapply ent_munch with (W := f2_W (Sfr fr + 22) (fr + 176) sp FS) (mem := mem);
        [exact HENT | exact HAH | apply (proj1 (fr_munch_ul _ _ _)); exact MU |
         intros x Hk; apply (proj2 (fr_outside_lib _ _)); exact (HKEPT x Hk) |
         exact HSTK' | exact HSTKhi' | intros a _ Ho; exact (proj2 (HOWN'' a) Ho)]. }
    assert (HENT'' : ENT APIf g (hb1 phi L) mem' md') by (eapply ent_mat; [exact HENT' | exact Hmat]).
    (* FSREC (side arm) *)
    assert (HFSR : FSREC fr mem -> FSREC fr mem').
    { intros (FSb & jj & Htpb & HFSbr & Hj6 & Hfrj & Hflag & Htail).
      assert (EFSb : FSb = FS).
      { pose proof (KindBGlue.word_mem_le8 rsegs mem (AC.as_tp AC.ASYMS) FSb Htpb ltac:(lia)
                      ltac:(unfold AC.as_tp, AC.ASYMS; cbn; lia)
                      ltac:(unfold AC.as_tp, AC.ASYMS; cbn; lia)) as Hb1.
        pose proof (KindBGlue.word_mem_le8 rsegs mem (AC.as_tp AC.ASYMS) FS HFSw ltac:(lia)
                      ltac:(unfold AC.as_tp, AC.ASYMS; cbn; lia)
                      ltac:(unfold AC.as_tp, AC.ASYMS; cbn; lia)) as Hb2.
        pose proof (fl_le8_eq [] mem mem (AC.as_tp AC.ASYMS) (Z_to_bv 64 FSb) (Z_to_bv 64 FS) Hb1 Hb2
                      (LF.munch_refl [] mem) (fun x _ => I)) as E.
        pose proof (f_equal (bv_unsigned (n:=64)) E) as E'.
        rewrite !MState.unsigned_lit in E' by lia. exact E'. }
      subst FSb.
      assert (HM6 : ASM.fs_M 6 = 256) by reflexivity.
      assert (HB6 : ASM.fs_B 6 = 4096) by reflexivity.
      assert (Hfl : ASM.fs_flag FS 6 jj = FS + 36352 + jj) by (unfold ASM.fs_flag; cbn; lia).
      assert (Hfrv : fr = FS + 6328320 + jj * 4096)
        by (rewrite Hfrj; unfold ASM.fs_frame, ASM.fs_B; cbn; lia).
      rewrite HM6 in Hj6.
      exists FS, jj.
      split.
      { intros k Hk.
        assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                     = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
        { apply MU. rewrite MState.unsigned_lit by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
          apply HWlo. unfold AC.as_tp, AC.ASYMS; cbn; lia. }
        unfold mbyte. rewrite Hm. exact (Htpb k Hk). }
      split; [exact HFSbr|]. split; [rewrite HM6; exact Hj6|]. split; [exact Hfrj|].
      split.
      { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx.
        apply f2_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | lia | lia | lia | lia | lia | lia]. }
      { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx.
        rewrite HB6 in Hx.
        apply f2_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | lia | lia | lia | lia | lia | lia]. } }
    assert (HFRAm : FRA B APIf ra g fr (hb1 phi L) regs'' mem' md)
      by (apply (f2_fra_run g fr (hb1 phi L) regs regs'' mem mem' md (f2_W (Sfr fr + 22) (fr + 176) sp FS)
                   HFRA MU WM HRO' HDJ HAH' HSTK' (fun a Ha => proj2 (SW' a Ha)) Hshnew);
          assumption).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi L) regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi L) regs'' regs'' mem' md md' HFRAm);
        try reflexivity. exact Hmat. }
    (* ---- the bundles at the exit, read off the kept bytes ---- *)
    assert (KB : forall x, 0 <= x < 2 ^ 64 -> LF.outside (f2_W (Sfr fr + 22) (fr + 176) sp FS) x ->
              mbyte rsegs mem' x = mbyte rsegs mem x)
      by (intros x Hx Ho; exact (f2_mb_keep _ mem mem' x MU Hx Ho)).
    assert (KA : forall x, A <= x < A + 448 -> mbyte rsegs mem' x = mbyte rsegs mem x).
    { intros x Hx. apply KB; [lia|]. apply f2_out_app; [apply HappA; lia | exact HappFS1 | exact HAwin
        | lia | lia | lia | lia | lia | lia]. }
    assert (KF : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 176 <= x < fr + 212) ->
              mbyte rsegs mem' x = mbyte rsegs mem x)
      by (intros x Hx Hx2; apply KB; [lia | exact (HoutFR x Hx Hx2)]).
    assert (KFS : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 176 <= x < fr + 216) ->
              mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
    { intros x Hx Hx2. apply KB; [|exact (HoutFRsh x Hx Hx2)].
      pose proof (in_shadow_range _ (shadow_of_app x (Happ' x Hx))). lia. }
    assert (KI : forall x, KNC.KIND_NAME <= x < KNC.KIND_NAME + 112 ->
              mbyte rsegs mem' x = mbyte rsegs mem x /\
              mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
    { intros x Hx. unfold KNC.KIND_NAME in Hx.
      pose proof (f2_sa_lo x ltac:(lia)) as Hsa. unfold ASAN_K in Hsa.
      split; (apply KB; [lia|]); [apply HWlo; lia | apply HimgOut; lia]. }
    assert (E9' : getr regs'' 9 = getr regs 9) by exact E9.
    assert (HLK' : LK g fr j regs'' mem').
    { apply (f1_lk_move g fr j regs regs'' mem mem' A HLK Hr9 ltac:(lia) ltac:(lia) E9 E27).
      - intros x Hx. apply KA. lia.
      - intros x Hx. apply KF; lia.
      - intros x Hx. apply KFS; unfold fragb in Hx; lia.
      - exact KI.
      - exact (fra_stk B APIf ra g fr _ regs'' mem' md' HFRA'). }
    assert (HFC' : FC g fr j regs'' mem').
    { destruct HFC as (S232 & R21 & R20).
      split; [apply (f1_spill_keep regs regs'' mem mem' A 232 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
              [intros x Hx; apply KA; lia | exact S232]|].
      split; [unfold rg in *; rewrite E21; exact R21 | unfold rg in *; rewrite E20; exact R20]. }
    assert (HFT' : FTURN g j phi regs'' mem').
    { split; [apply (f1_spill_keep regs regs'' mem mem' A 224 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
              [intros x Hx; apply KA; lia | exact H224]|].
      split; [apply (f1_spill_keep regs regs'' mem mem' A 232 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
              [intros x Hx; apply KA; lia | exact H232]|].
      split; [|exact HPHIl].
      apply (f1_keep_bytes mem mem' _ _ HPHI). rewrite HPHIl'. intros x Hx.
      destruct (Hblkb x ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
      apply KB; [unfold app_mem in Happq; lia|].
      apply HoutAPP; [exact Happq | lia | exact Hnfs | intros Hc; exact (Hfrdj x Hc ltac:(lia))]. }
    assert (HHB' : HB mem' phi (flen g j)).
    { split; [exact (proj1 HHB)|].
      apply (f2_addr_keepW (f2_W (Sfr fr + 22) (fr + 176) sp FS) mem mem' phi L (proj2 HHB) MU).
      intros i Hi.
      destruct (Hblkb (phi + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
      apply HoutSH; [exact Happq | lia | exact Hnfs | intros Hc; exact (Hfrdj (phi + i) Hc ltac:(lia))]. }
    assert (HFSj' : FSj g fr j regs'' mem').
    { apply (f1_fsj_move g fr j regs regs'' mem mem' HFSj); intros x Hx; [apply KF; lia | apply KFS; lia]. }
    assert (HREC' : REC0 g fr j mem').
    { apply (f1_rec0_move g fr j mem mem' HREC). intros x Hx. apply KF; lia. }
    assert (HFPS' : FPS g fr j mem').
    { split; [exact HRecR|].
      unfold Sfr in HRecSR.
      exact (f2_addr_rec mem' fr cb0 cb1 cb2 cb3 cb4 Hfr8 ltac:(lia) ltac:(lia)
               ltac:(intros a Ha; apply Happ'; lia) HRecSR EC0 EC1 EC2 EC3 EC4). }
    apply (Hexit regs'' mem' md' HFRA' HENT'').
    + split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB'|].
      split; [unfold rg in *; rewrite E18; exact Hr18|].
      split; [unfold rg in *; rewrite E20; exact Hr20|].
      split; [exact HFT'|]. split; [exact HLK'|]. split; [exact HFC'|].
      split; [unfold rg in *; rewrite E22; exact Hr22|].
      split; [exact HFSj' | exact HREC'].
    + exact HFPS'.
    + unfold a0v, rg. exact E10.
Qed.


(* ---- the checked memcpy stage 0x81f68 -> checked_memcpy -> 0x81f78 (len > 0) ----
   f2_MB is the state at 0x81f68 after the head run: the entry cut's facts with the cursor spill [A + 224] = p +
   body written.  The copy moves the len frame bytes at p + body (f1_IN's input bytes, a sub-range of the input
   block) into Phi; its write set is the destination [Phi, Phi + len) (in the live block hb1) and the callee window
   [sp - 2224, sp) (above stklo), both stores a_laws_store allows.  The run is on the normalized memory (MemNorm;
   the contract takes mem_inv).  The exit is the official Inv_B81f78_at (pc 0x81f78; FCUT with FTURN: the copied
   bytes at Phi). *)
Definition f2_MB (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ rg regs 18 phi /\ rg regs 20 (flen g j) /\
  spill regs m 224 (g_p g + t_body (g_in g) j) /\ LK g fr j regs m /\ FC g fr j regs m /\
  rg regs 22 1 /\ FSj g fr j regs m /\ REC0 g fr j m /\ f1_IN g m /\ 0 < flen g j.

Lemma f2_mcpy_seg : forall (j : nat) (g : ghost) regs mem md fr phi,
  Hat B APIf ra (Inv_B81f78_at B APIf ra) j ->
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md ->
  f2_MB g j phi fr regs mem ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 0x81f68) mem (seg_rom rsegs)) md) (Post B APIf ra g).
Proof.
  intros j g regs mem md fr phi Hx08 HFRA HENT HMB.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct HMB as (Hgn & Hj & HHB & Hr18 & Hr20 & H224 & HLK & HFC & Hr22 & HFSj & HREC & HIN & Hpos).
  pose proof (proj1 FF) as SEGS.
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  clear Hs5.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  destruct (f2_flen_rng g j) as (HN0 & HNb).
  set (L := AC.a_size (flen g j)) in *.
  assert (HL : L = Z.max (flen g j) 1) by reflexivity.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS (hb1 phi L ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  assert (HFSsz2 : AC.FS_SIZE = 11571200) by reflexivity.
  rewrite Haspz in Hlo, Hstkw.
  pose proof (Hplace 2224 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  (* ---- the frame ---- *)
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (f1_lw_fs_place (APIf rc) (hb1 phi L ++ g_H g) mem md FSb HAH Hw HFSr)
        as (_ & _ & _ & HFapp).
      apply HFapp. lia. }
  assert (Hfre : 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    clear - H1 H2 HLMv HHMv HAPPv HFBv. unfold app_mem in *. lia. }
  (* ---- the destination block (Phi, a_size len): above GT, below stklo ---- *)
  assert (HInblk : In (phi, L) (hb1 phi L ++ g_H g)) by (unfold hb1; cbn [app]; left; reflexivity).
  destruct (f1_lw_blocks (APIf rc) (hb1 phi L ++ g_H g) mem md phi L HAH HInblk)
    as (Hp16 & Hp4096 & Hpstklo & HEDd & Hblkb).
  pose proof (AC.a_laws_block_high _ _ _ _ _ ALAWS (hb1 phi L ++ g_H g) mem md phi L HAH HInblk) as Hphi21.
  pose proof (AC.a_laws_block_end _ _ _ _ _ ALAWS (hb1 phi L ++ g_H g) mem md phi L HAH HInblk ltac:(lia))
    as Hphi7.
  assert (HblkGT : forall a, phi <= a < phi + L -> 0x5fe000 <= a).
  { intros a Ha. destruct (Z_lt_le_dec a 0x5fe000) as [Hlt|Hge]; [|exact Hge].
    exfalso. destruct (Hblkb a Ha) as (_ & _ & _ & Hpg & _). apply Hpg. apply f2_on_page. lia. }
  pose proof (HblkGT phi ltac:(lia)) as HphiGT.
  assert (Happ0 : app_mem phi) by exact (proj1 (Hblkb phi ltac:(lia))).
  assert (Happ1 : app_mem (phi + L - 1)) by exact (proj1 (Hblkb (phi + L - 1) ltac:(lia))).
  assert (Hblklh : phi + L <= LOWMEM_END \/ HIGHMEM_BEG <= phi) by (unfold app_mem in Happ0, Happ1; lia).
  assert (Hfrdj : forall x, fr <= x < fr + FRAME_BYTES -> ~ (phi <= x < phi + L)).
  { intros x Hx Hin. destruct (Hblkb x Hin) as (_ & _ & _ & _ & Hfsx).
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal x Hx) as Hr. lia.
    - apply Hfsx. exact (Hfs x Hx). }
  (* ---- the source: len bytes of the input block at p + body ---- *)
  destruct HIN as (HinH0 & HaddrIN & HbytesIN).
  assert (Egn : g_n g = nlen (g_in g)) by reflexivity.
  assert (Hlen_in : Z.of_nat (length (g_in g)) = g_n g) by reflexivity.
  pose proof (fc_range (g_in g) j) as Rc.
  assert (Hbl : 0 <= t_body (g_in g) j /\ t_body (g_in g) j + flen g j <= g_n g).
  { rewrite Egn. unfold flen, t_body, t_len, f_body, f_len, f_h, f_left in *. lia. }
  assert (Hn0 : 0 < g_n g) by lia.
  pose proof (HinH0 Hn0) as HinH.
  assert (HinH' : In (g_p g, g_n g) (hb1 phi L ++ g_H g)) by (apply in_or_app; right; exact HinH).
  destruct (f1_lw_blocks (APIf rc) (hb1 phi L ++ g_H g) mem md (g_p g) (g_n g) HAH HinH')
    as (_ & Hp4096' & Hpn & HEDs & Hinbb).
  pose proof (AC.a_laws_block_end _ _ _ _ _ ALAWS (hb1 phi L ++ g_H g) mem md (g_p g) (g_n g) HAH HinH' Hn0)
    as Hp7.
  assert (Hdisj : phi + L <= g_p g \/ g_p g + g_n g <= phi)
    by exact (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md phi L (g_p g) (g_n g) HAH HinH).
  assert (HSRC : bytes_at rsegs mem (g_p g + t_body (g_in g) j) (t_phi (g_in g) j)).
  { pose proof (f2_ba_sub mem (g_p g) (g_in g) (Z.to_nat (t_body (g_in g) j)) (Z.to_nat (flen g j)) HbytesIN
                  ltac:(unfold flen in *; lia)) as H.
    rewrite Z2Nat.id in H by lia. exact H. }
  assert (HPHIl : length (t_phi (g_in g) j) = Z.to_nat (flen g j)) by exact (t_phi_length (g_in g) j).
  assert (Hinapp : forall x, g_p g <= x < g_p g + g_n g -> app_mem x) by (intros x Hx; exact (proj1 (Hinbb x Hx))).
  set (S0 := g_p g + t_body (g_in g) j) in *.
  assert (HS0 : S0 = g_p g + t_body (g_in g) j) by reflexivity.
  pose proof HaddrIN as (HpZ & HnZ & HpnZ & _).
  assert (HS7 : app_mem (S0 + 7)).
  { destruct (Z_lt_le_dec (S0 + 7) (g_p g + g_n g)) as [H|H]; [apply Hinapp; lia|].
    pose proof (Hinapp (g_p g + g_n g - 1) ltac:(lia)) as H1.
    clear - H1 Hp7 H Hbl HS0 Hpos HLMv HHMv HAPPv. unfold app_mem in *. lia. }
  assert (HD7 : app_mem (phi + 7)).
  { destruct (Z_lt_le_dec (phi + 7) (phi + L)) as [H|H]; [exact (proj1 (Hblkb (phi + 7) ltac:(lia)))|].
    clear - Happ1 Hphi7 H HL HLMv HHMv HAPPv. unfold app_mem in *. lia. }
  assert (HESrc : end_in_app S0 (flen g j)).
  { right. destruct (Z_lt_le_dec (S0 + flen g j) (g_p g + g_n g)) as [H|H]; [apply Hinapp; lia|].
    destruct HEDs as [H0|H0]; [lia|]. replace (S0 + flen g j) with (g_p g + g_n g) by lia. exact H0. }
  assert (HEDst : end_in_app phi (flen g j)).
  { right. destruct (Z_lt_le_dec (phi + flen g j) (phi + L)) as [H|H];
      [exact (proj1 (Hblkb (phi + flen g j) ltac:(lia)))|].
    destruct HEDd as [H0|H0]; [lia|]. replace (phi + flen g j) with (phi + L) by lia. exact H0. }
  assert (ADS : addressable mem S0 (flen g j))
    by exact (addressable_sub mem (g_p g) (g_n g) (t_body (g_in g) j) (flen g j) HaddrIN ltac:(lia) ltac:(lia)
                ltac:(lia)).
  assert (ADD : addressable mem phi (flen g j)).
  { pose proof (addressable_sub mem phi L 0 (flen g j) (proj2 HHB) ltac:(lia) ltac:(lia) ltac:(lia)) as H.
    rewrite Z.add_0_r in H. exact H. }
  (* ---- the normalized memory the copy runs on ---- *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  pose proof (f2_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  pose proof (f2_stk_rel mem (normalize rsegs mem) (sp - FN_STACK) sp HR0 ltac:(lia) Hstkw) as ST0.
  assert (TBr : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (Hblkstk : stk rsegs mem phi (phi + flen g j)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hblkb a ltac:(lia)) as (_ & Hw & Hni & _ & _).
    split; [exact Hw | exact (f2_rd_of_w mem a ltac:(lia) Hni Hw)]. }
  pose proof (f2_stk_rel mem (normalize rsegs mem) phi (phi + flen g j) HR0 ltac:(lia) Hblkstk) as Hblkstk0.
  destruct (stk_bytes rsegs (normalize rsegs mem) phi (phi + flen g j) Hblkstk0 ltac:(lia))
    as (junkN & HjlN & HjbN).
  assert (RWN : rw_cells rsegs (normalize rsegs mem) phi [CB (Z.to_nat (flen g j)) junkN]).
  { replace (Z.to_nat (flen g j)) with (length junkN) by lia. apply f2_rw_CB; [exact HjbN|].
    replace (Z.of_nat (length junkN)) with (phi + flen g j - phi) by lia.
    exact (f2_wr_stk _ _ _ Hblkstk0). }
  destruct HFC as (S232 & R21 & R20).
  apply (f2_run regs (Z_to_bv 64 0x81f68) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x81f78 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\
       getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\ getr R 21 = getr regs 21 /\
       getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
       LF.munch [(phi, phi + flen g j); (sp - 2224, sp)] (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\
       stk rsegs m0' (sp - FN_STACK) sp /\ shadow_rw m0' /\
       rw_cells rsegs m0' phi [CB (Z.to_nat (flen g j)) (t_phi (g_in g) j)])
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite f1_mkR_of.
    eapply evt_mono.
    + apply (f2_mcpy_evt asan_memcpy.asan_memcpy_holds) with (spv := sp) (S := S0) (N := flen g j) (phi := phi)
        (lo := sp - FN_STACK)
        (src := t_phi (g_in g) j) (junk := junkN).
      * exact Hr2.
      * exact Hr18.
      * exact Hr20.
      * exact R21.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact (TBr _ _ HSRC).
      * exact HPHIl.
      * exact RWN.
      * destruct Hdisj as [H|H]; [right; right | right; left]; lia.
      * lia.
      * exact (f2_addr_rel mem (normalize rsegs mem) _ _ HR0 ADS).
      * exact (f2_addr_rel mem (normalize rsegs mem) _ _ HR0 ADD).
      * exact HESrc.
      * exact HEDst.
      * right. split; [exact HS7 | exact HD7].
      * right. unfold RT_HI. lia.
      * left. lia.
      * left. lia.
      * exact ST0.
      * lia.
      * lia.
      * lia.
      * exact (f2_cells_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_cells _ _ _ HRT)).
      * exact HSW0.
      * exact HMI0.
    + intros ms2 (R & m' & Hms & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P22 & P21 & P26 & P27 &
                  MU2 & WM2 & MI2 & ST2 & AC2 & SW2 & RW2 & HBs2).
      exists R, (Z_to_bv 64 0x81f78), m'. split; [exact Hms|].
      split; [reflexivity|].
      split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P18|]. split; [exact P19|]. split; [exact P20|].
      split; [exact P22|]. split; [exact P21|]. split; [exact P26|]. split; [exact P27|].
      split; [exact MU2|]. split; [exact WM2|]. split; [exact ST2|]. split; [exact SW2 | exact RW2].
  - intros R pc' m0' regs'' mem' md'
      (Hpc' & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K22 & K21 & K26 & K27 & MU0 & WM0 & STw0 & SW0' & RW0)
      Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    (* ---- back from the normalized memory to the real one ---- *)
    set (W := [(phi, phi + flen g j); (sp - 2224, sp)]) in *.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    pose proof (f2_stk_back mem' m0' (sp - FN_STACK) sp HRel ltac:(lia) STw0) as STw.
    pose proof (f2_srw_back mem' m0' HRel SW0') as SW'.
    assert (HPHI' : bytes_at rsegs mem' phi (t_phi (g_in g) j)).
    { destruct RW0 as ((_ & Hb) & _). cbn [cbytes cells_bytes] in Hb. rewrite app_nil_r in Hb.
      exact (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) Hb). }
    (* ---- the write set W and what lies outside it ---- *)
    assert (HOUT : forall x, (x < phi \/ phi + flen g j <= x) -> (x < sp - 2224 \/ sp <= x) -> LF.outside W x)
      by (intros x H1 H2; exact (f2_out_mc phi (flen g j) sp x H1 H2)).
    assert (HoutSH : forall y, in_shadow y -> LF.outside W y).
    { intros y Hy. apply HOUT.
      - pose proof (f2_shadow_vs_app y phi (phi + L) Hy Happ0 Happ1 ltac:(lia) Hblklh). lia.
      - exact (f2_shadow_vs_app y (sp - 2224) sp Hy ltac:(unfold app_mem; lia) ltac:(unfold app_mem; lia)
                 ltac:(lia) ltac:(right; lia)). }
    assert (HoutSHa : forall a, app_mem a -> LF.outside W (shadow_addr a))
      by (intros a Ha; exact (HoutSH _ (shadow_of_app a Ha))).
    assert (KB : forall x, 0 <= x < 2 ^ 64 -> LF.outside W x -> mbyte rsegs mem' x = mbyte rsegs mem x)
      by (intros x Hx Ho; exact (f2_mb_keep _ mem mem' x MU Hx Ho)).
    assert (KBS : forall a, app_mem a -> mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
    { intros a Ha. pose proof (in_shadow_range _ (shadow_of_app a Ha)). apply KB; [lia | exact (HoutSHa a Ha)]. }
    (* ---- the heap invariant, by the store law ---- *)
    assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
              ~ AC.a_store_ok (hb1 phi L ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
              mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hnok. destruct (f2_out_dec W a) as [Ho|Hno].
      - apply MU. rewrite MState.unsigned_lit by exact Ha. exact Ho.
      - exfalso. apply Hnok. destruct (f2_mc_not_out _ _ _ _ Hno) as [Hb|Hs].
        + left. exists phi, L. split; [exact HInblk | lia].
        + right. left. lia. }
    assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
      by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
    destruct (f1_lw_store (APIf rc) (hb1 phi L ++ g_H g) mem mem' md HAH Hagree Hwrit)
      as (HAH' & HOWN'' & HSTK' & HSTKhi').
    (* ---- FRA at the memory after the copy ---- *)
    assert (HDJ : rt_disjoint [(phi, phi + flen g j); (sp - 2224, sp)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
        RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM,
        RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
      cbn [LF.disjoint_from]. repeat split; first [exact I | lia]. }
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
      { split; [clear - Hfre HAPPv HFBv HFSv; unfold Sfr, shadow_addr, ASAN_K; Z.div_mod_to_equations; lia|].
        split; [clear - Hfre HAPPv HFBv HFSv; unfold Sfr, shadow_addr, ASAN_K; Z.div_mod_to_equations; lia|].
        intros a Ha. apply SW'.
        replace a with (Sfr fr + (a - Sfr fr)) by lia. apply f2_fsh; [exact Happ | lia]. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. f_equal. lia. }
    assert (HWlo : forall x, 0 <= x < 6283264 -> LF.outside W x) by (intros x Hx; apply HOUT; lia).
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> LF.outside W x).
    { intros x Hx. pose proof (Hfrdj x Hx) as Hd. apply HOUT; [lia | destruct Hsep as [H|H]; lia]. }
    assert (HWAr : forall x, A <= x < A + 448 -> LF.outside W x) by (intros x Hx; apply HOUT; lia).
    assert (HWS : forall x, g_S g - 104 <= x < g_S g -> LF.outside W x) by (intros x Hx; apply HOUT; lia).
    assert (HWwin : forall x, g_S g - AF.SLOT_STACK <= x < g_S g ->
              LF.outside W x \/ exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. destruct (f2_out_dec W x) as [Ho|Hno]; [left; exact Ho|right].
      destruct (f2_mc_not_out _ _ _ _ Hno) as [Hb|Hs]; [lia|].
      destruct STw as (_ & _ & Hs2). exact (proj2 (Hs2 x ltac:(lia))). }
    assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (f2_ag_lo a Ha) as Hal.
      apply (f2_addr_keepW W mem mem' a 1 (HAG a Ha) MU). intros i Hi. apply HoutSHa.
      unfold app_mem. lia. }
    assert (HWA' : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
              addressable mem' a 1).
    { intros a Ha1 Ha2. apply (f2_addr_keepW W mem mem' a 1 (HWA a Ha1 Ha2) MU). intros i Hi. apply HoutSHa.
      unfold app_mem. lia. }
    assert (HFSR : FSREC fr mem -> FSREC fr mem').
    { intros (FSb & jj & Htpb & HFSbr & Hj6 & Hfrj & Hflag & Htail).
      destruct (f1_lw_fs_place (APIf rc) (hb1 phi L ++ g_H g) mem md FSb HAH Htpb HFSbr)
        as (HGTb & HFSend & _ & HFapp).
      assert (KFS1 : forall x, FSb <= x < FSb + AC.FS_SIZE -> mbyte rsegs mem' x = mbyte rsegs mem x).
      { intros x Hx. unfold AC.FS_SIZE in Hx. apply KB; [lia|]. apply HOUT; [|lia].
        destruct (Z_lt_le_dec x phi) as [H|H]; [left; exact H|].
        destruct (Z_lt_le_dec x (phi + flen g j)) as [H'|H']; [|right; exact H'].
        exfalso. destruct (Hblkb x ltac:(lia)) as (_ & _ & _ & _ & Hnfs). apply Hnfs.
        exists FSb. split; [exact HFSbr|]. split; [exact Htpb | unfold AC.FS_SIZE; lia]. }
      assert (HM6 : ASM.fs_M 6 = 256) by reflexivity.
      assert (HB6 : ASM.fs_B 6 = 4096) by reflexivity.
      assert (Hfl : ASM.fs_flag FSb 6 jj = FSb + 36352 + jj) by (unfold ASM.fs_flag; cbn; lia).
      assert (Hfrv : fr = FSb + 6328320 + jj * 4096)
        by (rewrite Hfrj; unfold ASM.fs_frame, ASM.fs_B; cbn; lia).
      rewrite HM6 in Hj6.
      exists FSb, jj.
      split.
      { intros k Hk. rewrite KB.
        - exact (Htpb k Hk).
        - unfold AC.as_tp, AC.ASYMS; cbn; lia.
        - apply HWlo. unfold AC.as_tp, AC.ASYMS; cbn; lia. }
      split; [exact HFSbr|]. split; [rewrite HM6; exact Hj6|]. split; [exact Hfrj|].
      split.
      - apply (f1_keep_bytes mem mem'); [exact Hflag|]. cbn [length]. intros x Hx. apply KFS1.
        unfold AC.FS_SIZE. lia.
      - apply (f1_keep_bytes mem mem'); [exact Htail|]. rewrite length_le8. intros x Hx. apply KFS1.
        lia. }
    destruct (fra_in_keep_sh g mem mem' W Hinb Hinblk MU
                ltac:(intros x Hx; split;
                      [ apply HOUT; [destruct Hdisj as [H|H]; lia | lia]
                      | apply HoutSHa; exact (Hinapp x Hx) ])) as (HIN1' & HIN2').
    assert (HFRAm : FRA B APIf ra g fr (hb1 phi L) regs'' mem' md).
    { apply (f2_fra_run g fr (hb1 phi L) regs regs'' mem mem' md W HFRA MU WM HRO' HDJ HAH' HSTK'
               (fun a Ha => proj2 (SW' a Ha)) Hshnew HWlo).
      - intros x Hx. apply HWfr. lia.
      - intros x Hx. rewrite HbvA in Hx. apply HWAr. lia.
      - intros x Hx. rewrite HbvA in Hx. apply HWAr. lia.
      - exact HWS.
      - exact HWwin.
      - exact HAG'.
      - exact HWA'.
      - exact HFSR.
      - exact HIN1'.
      - exact HIN2'.
      - exact E2.
      - exact E3.
      - exact E4.
      - exact E8.
      - exact E9.
      - exact E19.
      - exact E26. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi L) regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi L) regs'' regs'' mem' md md' HFRAm); try reflexivity.
      exact Hmat. }
    (* ---- ENT across the copy ---- *)
    assert (HKEPT : forall x, ent_kept g x -> LF.outside W x).
    { intros x Hk.
      destruct Hk as [(q & kk & i & Hin & Hni & Hi & ->) |
                      [Hik | [Habk | [(bq & Hor & ->) | (q & kk & i & Hin & Hni & Hi & ->)]]]].
      - destruct (f1_lw_blocks (APIf rc) (hb1 phi L ++ g_H g) mem md q kk HAH
                    (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hqstk & _ & _).
        pose proof (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md phi L q kk HAH Hin) as Hqd.
        apply HOUT; [destruct Hqd as [H|H]; lia | lia].
      - apply HWlo. pose proof (img_below_GT x Hik) as Hx. unfold AC.GT in Hx. lia.
      - apply HOUT; lia.
      - apply HoutSHa. destruct Hor as [Hi|Hr].
        + pose proof (img_below_GT bq Hi) as Hx. unfold AC.GT in Hx. unfold app_mem. lia.
        + unfold app_mem. lia.
      - (* ENT append #1: the copy writes no shadow byte *)
        destruct (f1_lw_blocks (APIf rc) (hb1 phi L ++ g_H g) mem md q kk HAH
                    (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & _ & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & _).
        exact (HoutSHa _ Happq). }
    assert (HENT' : ENT APIf g (hb1 phi L) mem' md).
    { eapply ent_munch with (W := W) (mem := mem);
        [exact HENT | exact HAH | apply (proj1 (fr_munch_ul _ _ _)); exact MU |
         intros x Hk; apply (proj2 (fr_outside_lib _ _)); exact (HKEPT x Hk) |
         exact HSTK' | exact HSTKhi' | intros a _ Ho; exact (proj2 (HOWN'' a) Ho)]. }
    assert (HENT'' : ENT APIf g (hb1 phi L) mem' md') by (eapply ent_mat; [exact HENT' | exact Hmat]).
    (* ---- the bundles at 0x81f78 ---- *)
    assert (KA : forall x, A <= x < A + 448 -> mbyte rsegs mem' x = mbyte rsegs mem x)
      by (intros x Hx; apply KB; [lia | apply HWAr; lia]).
    assert (KF : forall x, fr <= x < fr + FRAME_BYTES -> mbyte rsegs mem' x = mbyte rsegs mem x)
      by (intros x Hx; apply KB; [lia | apply HWfr; lia]).
    assert (KI : forall x, KNC.KIND_NAME <= x < KNC.KIND_NAME + 112 ->
              mbyte rsegs mem' x = mbyte rsegs mem x /\
              mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
    { intros x Hx. unfold KNC.KIND_NAME in Hx. split.
      - apply KB; [lia | apply HWlo; lia].
      - apply KBS. unfold app_mem. lia. }
    assert (HLK' : LK g fr j regs'' mem').
    { apply (f1_lk_move g fr j regs regs'' mem mem' A HLK Hr9 ltac:(lia) ltac:(lia) E9 E27).
      - intros x Hx. apply KA. lia.
      - intros x Hx. apply KF. lia.
      - intros x Hx. apply KBS. apply Happ. unfold fragb in Hx. lia.
      - exact KI.
      - exact (fra_stk B APIf ra g fr _ regs'' mem' md' HFRA'). }
    assert (HFC' : FC g fr j regs'' mem').
    { split; [apply (f1_spill_keep regs regs'' mem mem' A 232 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
              [intros x Hx; apply KA; lia | exact S232]|].
      split; [unfold rg in *; rewrite E21; exact R21 | unfold rg in *; rewrite E20; exact R20]. }
    assert (HFT' : FTURN g j phi regs'' mem').
    { split; [apply (f1_spill_keep regs regs'' mem mem' A 224 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
              [intros x Hx; apply KA; lia | exact H224]|].
      split; [apply (f1_spill_keep regs regs'' mem mem' A 232 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
              [intros x Hx; apply KA; lia | exact S232]|].
      split; [exact HPHI'|]. rewrite HPHIl. unfold flen in *. lia. }
    assert (HHB' : HB mem' phi (flen g j)).
    { split; [exact (proj1 HHB)|].
      apply (f2_addr_keepW W mem mem' phi L (proj2 HHB) MU).
      intros i Hi. apply HoutSHa. exact (proj1 (Hblkb (phi + i) ltac:(lia))). }
    assert (HFSj' : FSj g fr j regs'' mem').
    { apply (f1_fsj_move g fr j regs regs'' mem mem' HFSj); intros x Hx;
        [apply KF; lia | apply KBS; apply Happ; lia]. }
    assert (HREC' : REC0 g fr j mem').
    { apply (f1_rec0_move g fr j mem mem' HREC). intros x Hx. apply KF. lia. }
    rewrite <- SEGS. apply Hx08.
    unfold Inv_B81f78_at, FCUT, FCUTP, CUTST.
    exists phi, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB'|].
    split; [unfold rg in *; rewrite E18; exact Hr18|].
    split; [unfold rg in *; rewrite E20; exact Hr20|].
    split; [exact HFT'|].
    split; [exact HLK'|]. split; [exact HFC'|].
    split; [unfold rg in *; rewrite E22; exact Hr22|].
    split; [exact HFSj' | exact HREC'].
Qed.

(* ==== seg_F2 (S_F2) ====
   From 0x81f50 (the allocation's return, turn j; cut Inv_B81f50_at): the head run 0x81f50 -> 0x82020 (len = 0) /
   0x81f68 (len > 0) on the real memory (sl_run_lib), which writes the cursor spill [A + 224] = p + body (FRA and
   ENT move across it by F1.f1_fra_spill, the bundles by F1's moves), then the short parse block f2_parse_seg (len =
   0, exit Inv_B82048_at, pc 0x82048) or the copy f2_mcpy_seg (len > 0, exit Inv_B81f78_at, pc 0x81f78). *)
Lemma seg_F2 : forall j : nat,
  Hat B APIf ra (Inv_B81f78_at B APIf ra) j -> Hat B APIf ra (Inv_B82048_at B APIf ra) j ->
  Hat B APIf ra (Inv_B81f50_at B APIf ra) j.
Proof.
  intros j Hx08 Hxd8 g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & Ha0 & HHB & HLK & HFC & HIN &
                    HFSj & HREC & Hs6).
  subst c.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  clear Hs5.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS _ mem md HAH) as Hhigh.
  destruct (f2_flen_rng g j) as (HN0 & HNb). unfold flen in HN0, HNb.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HInblk : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (unfold hb1; cbn [app]; left; reflexivity).
  destruct (f1_lw_blocks (APIf rc) _ mem md phi _ HAH HInblk) as (_ & Hp4096 & Hpstklo & _ & _).
  assert (HL : AC.a_size (flen g j) = Z.max (flen g j) 1) by reflexivity.
  destruct HFC as (S232 & R21 & R20).
  pose proof HIN as (HinH0 & HaddrIN & HbytesIN).
  pose proof (fc_range (g_in g) j) as Rc.
  assert (Egn : g_n g = nlen (g_in g)) by reflexivity.
  assert (Hbody : 0 <= t_body (g_in g) j <= g_n g)
    by (rewrite Egn; unfold t_body, f_body, f_h, f_left in *; lia).
  assert (HSv : 0 <= g_p g + t_body (g_in g) j < 2 ^ 64).
  { destruct HaddrIN as (Hp0 & Hn0' & Hpn' & _). lia. }
  assert (HWR : wr_at rsegs mem (A + 224) 8).
  { pose proof Hwin as (_ & _ & Hw).
    split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (Hw (A + 224 + i) ltac:(lia))). }
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x81f50) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 (if t_len (g_in g) j =? 0 then 0x82020 else 0x81f68) /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = Z_to_bv 64 phi /\
       getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
       LF.munch [(A + 224, A + 232)] mem mem' /\ LF.wmono rsegs mem mem' /\
       bytes_at rsegs mem' (A + 224) (le8 (Z_to_bv 64 (g_p g + t_body (g_in g) j))))
    (Post B APIf ra g)).
  { exact Hhalt. }
  { rewrite f1_mkR_of.
    pose proof Hr9 as R9. pose proof Ha0 as R10. pose proof R20 as R20'. pose proof R21 as R21'.
    unfold a0v, rg in R9, R10, R20', R21'.
    rewrite R9, R10, R20', R21'.
    destruct (Z.eq_dec (t_len (g_in g) j) 0) as [E0|N0].
    - rewrite E0.
      eapply evt_mono; [apply f2_head0; [lia | lia | exact HSv | exact HWR] |].
      intros ms' (m' & -> & MU & WM & HBt).
      do 3 eexists. split; [reflexivity|].
      split; [reflexivity|].
      do 12 (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM | exact HBt].
    - rewrite (proj2 (Z.eqb_neq _ _) N0).
      eapply evt_mono; [apply f2_head1; [lia | lia | exact HSv | lia | | exact HWR] |].
      { destruct HHB as (Hphi0 & _).
        lia. }
      intros ms' (m' & -> & MU & WM & HBt).
      do 3 eexists. split; [reflexivity|].
      split; [reflexivity|].
      do 12 (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM | exact HBt]. }
  intros R pc' mem1 regs'' md'
    (Hpc & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K22 & K21 & K26 & K27 & MU1 & WM1 & HB224) Hreg Hmat.
  subst pc'.
  assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E18 : getr regs'' 18 = Z_to_bv 64 phi) by (rewrite Hreg; exact K18).
  assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact K20).
  assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
  assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
  (* ---- the spill store [A + 224, A + 232) ---- *)
  assert (KM1 : forall x, 0 <= x < 2 ^ 64 -> ~ (A + 224 <= x < A + 232) -> mbyte rsegs mem1 x = mbyte rsegs mem x).
  { intros x Hx Hn. unfold mbyte. rewrite (MU1 (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. cbn [LF.outside]. split; [lia | exact I]. }
  (* F1's lemmas speak the UL engine's write-set predicates (Tac_slot's ULFr); the run gave the lib/Lib ones *)
  pose proof (proj1 (fr_munch_ul _ _ _) MU1) as MU1u.
  assert (WM1u : ULFr.wmono rsegs mem mem1) by exact WM1.
  assert (HWIN1 : stk rsegs mem1 (g_S g - AF.SLOT_STACK) (g_S g)).
  { apply (f1_stk_tr _ mem mem1 _ _ Hwin MU1u WM1u). intros x Hx.
    destruct (Z_lt_le_dec x (A + 224)) as [Hl|Hl]; [left; cbn [ULFr.outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec x (A + 232)) as [Hh|Hh].
    - right. apply (f1_ba_rd mem1 (A + 224) _ x HB224). rewrite length_le8. cbn. lia.
    - left. cbn [ULFr.outside]. split; [lia | exact I]. }
  destruct (f1_fra_spill B APIf ra empty FF g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem mem1 md md'
              A 224 232 HFRA HENT Hr9 HA64 ltac:(lia) ltac:(lia) ltac:(lia) MU1u WM1u HWIN1 Hmat
              E2 E3 E4 E8 E9 E19 E26) as (HFRA2 & HENT2).
  (* ---- the bundles after the store ---- *)
  assert (KSH : forall a, app_mem a -> mbyte rsegs mem1 (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
  { intros a Ha. pose proof (in_shadow_range _ (shadow_of_app a Ha)) as Hr.
    pose proof (shadow_of_app a Ha) as Hs.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs.
    apply KM1; [lia|]. lia. }
  assert (Hfre : fr + FRAME_BYTES <= A) by exact Hfa.
  assert (Hfr0 : 0 <= fr).
  { pose proof (bytes_at_bound rsegs mem fr (le8 (Z_to_bv 64 0x41b58ab3)) Hhdr1) as (Hf0 & _). lia. }
  (* the frame bytes are app memory (real arm: above stklo; side arm: in the FakeStack) *)
  assert (Happ : forall x, fr <= x < fr + FRAME_BYTES -> app_mem x).
  { intros x Hx. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal x Hx). unfold app_mem. lia.
    - destruct (Hfs x Hx) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (f1_lw_fs_place (APIf rc) _ mem md FSb HAH Hw HFSr) as (_ & _ & _ & HFapp).
      apply HFapp. lia. }
  assert (HLK1 : LK g fr j regs'' mem1).
  { apply (f1_lk_move g fr j regs regs'' mem mem1 A HLK Hr9 ltac:(lia) ltac:(lia) E9 E27).
    - intros x Hx. apply KM1; lia.
    - intros x Hx. apply KM1; lia.
    - intros x Hx. apply KSH. apply Happ. unfold fragb in Hx. lia.
    - intros x Hx. split; [apply KM1 | apply KSH]; pose proof (f1_kn_relro x Hx) as Hr;
        pose proof (f1_relro_range x Hr); [lia | lia | unfold app_mem; lia].
    - exact (fra_stk B APIf ra g fr _ regs'' mem1 md' HFRA2). }
  assert (S232' : spill regs'' mem1 232 (t_left (g_in g) j - t_h (g_in g) j)).
  { apply (f1_spill_keep regs regs'' mem mem1 A 232 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9); [|exact S232].
    intros x Hx. apply KM1; lia. }
  assert (HFC1 : FC g fr j regs'' mem1).
  { split; [exact S232'|].
    split; [unfold rg in *; rewrite E21; exact R21 | unfold rg in *; rewrite E20; exact R20]. }
  assert (H2241 : spill regs'' mem1 224 (g_p g + t_body (g_in g) j)).
  { exists A. split; [unfold rg in *; rewrite E9; exact Hr9 | exact HB224]. }
  assert (HFSj1 : FSj g fr j regs'' mem1).
  { apply (f1_fsj_move g fr j regs regs'' mem mem1 HFSj); intros x Hx;
      [apply KM1; lia | apply KSH; apply Happ; lia]. }
  assert (HREC1 : REC0 g fr j mem1).
  { apply (f1_rec0_move g fr j mem mem1 HREC). intros x Hx. apply KM1; lia. }
  assert (HHB1 : HB mem1 phi (flen g j)).
  { split; [exact (proj1 HHB)|].
    destruct (f1_lw_blocks (APIf rc) _ mem md phi _ HAH HInblk) as (_ & _ & _ & _ & Hblkb).
    apply (f1_addr_keep mem mem1 _ _ (proj2 HHB)). intros i Hi. apply KSH.
    exact (proj1 (Hblkb (phi + i) ltac:(lia))). }
  assert (Hr221 : rg regs'' 22 1) by (unfold rg in *; rewrite E22; exact Hs6).
  assert (Hr181 : rg regs'' 18 phi) by exact E18.
  assert (Hr201 : rg regs'' 20 (flen g j)) by (unfold rg in *; rewrite E20; exact R20).
  destruct (Z.eq_dec (t_len (g_in g) j) 0) as [E0|N0].
  - (* len = 0: the short parse block 0x82020 -> reac_ctrl_parse -> 0x82048 *)
    replace (if t_len (g_in g) j =? 0 then 0x82020 else 0x81f68) with 0x82020 by (rewrite E0; reflexivity).
    assert (Enil : t_phi (g_in g) j = []).
    { apply length_zero_iff_nil. rewrite t_phi_length. rewrite E0. reflexivity. }
    apply (f2_parse_seg 0x82020 0x82038 0x82048 j g regs'' mem1 md' fr phi).
    + left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. unfold flen. lia.
    + exact HFRA2.
    + exact HENT2.
    + split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB1|]. split; [exact Hr181|].
      split; [exact Hr201|].
      split.
      { split; [exact H2241|]. split; [exact S232'|].
        rewrite Enil. split.
        { split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi. cbn [length] in Hi. lia. }
        cbn [length Z.of_nat]. lia. }
      split; [exact HLK1|]. split; [exact HFC1|]. split; [exact Hr221|]. split; [exact HFSj1 | exact HREC1].
    + intros regs' mem' md'' HFRA' HENT' HPB' HFPS' Ha0'.
      destruct HPB' as (Hgn' & Hj' & HHB' & Hr18' & Hr20' & HFT' & HLK' & HFC' & Hr22' & HFSj' & HREC').
      rewrite <- SEGS. apply Hxd8.
      unfold Inv_B82048_at, FCUT, FCUTP, CUTST.
      exists phi, regs', mem', md'', fr.
      split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn'|]. split; [exact Hj'|]. split; [exact HHB'|]. split; [exact Hr18'|].
      split; [exact Hr20'|]. split; [exact HFT'|].
      split; [exact HLK'|]. split; [exact Hr22'|]. split; [exact HFSj'|]. split; [exact HREC'|].
      split; [exact HFPS'|]. split; [exact Ha0'|]. unfold flen. lia.
  - (* len > 0: the copy 0x81f68 -> checked_memcpy -> 0x81f78 *)
    replace (if t_len (g_in g) j =? 0 then 0x82020 else 0x81f68) with 0x81f68
      by (rewrite (proj2 (Z.eqb_neq _ _) N0); reflexivity).
    apply (f2_mcpy_seg j g regs'' mem1 md' fr phi Hx08 HFRA2 HENT2).
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB1|]. split; [exact Hr181|].
    split; [exact Hr201|]. split; [exact H2241|].
    split; [exact HLK1|]. split; [exact HFC1|]. split; [exact Hr221|]. split; [exact HFSj1|].
    split; [exact HREC1|].
    split.
    + apply (f1_in_move g mem mem1 HIN). intros x Hx.
      assert (Hn0 : 0 < g_n g) by lia.
      destruct (f1_lw_blocks (APIf rc) _ mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror (HinH0 Hn0)))) as (_ & Hp4 & Hpn & _ & Hinbb).
      split; [apply KM1; lia | apply KSH; exact (proj1 (Hinbb x Hx))].
    + unfold flen. lia.
Qed.

End S.

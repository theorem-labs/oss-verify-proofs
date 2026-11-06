(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 877 of its 987 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R8.v, with its module names, addresses and numbers changed; 1340 of its 1650 lines of code are new or changed and 677 lines of the source are left out. *)
(* Segment R9 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x8177c, 0x817a0],
   10 instructions, cut Inv_B8177c -> cut Inv_B817a4 (plan-asan-ubsan.md section 2, row R9; section 4, PARSE =
   reac_ctrl_parse, 0x83e04).
   rule 24: no function proved (a slot segment).

   The code writes the five metadata bytes of the parse record: the four bytes at [S(fr) + 296, S(fr) + 300) to 0
   (0x8177c-0x81788 `sb zero,296..299(s3)`, s3 = S(fr)) and the byte at S(fr) + 300 to 4 (0x8178c `li s5,4`,
   0x81790 `sb s5,300(s3)`), which marks the 36 bytes [fr + 2368, fr + 2404) addressable (the first four granules
   fully, the fifth for its first four bytes).  It then calls reac_ctrl_parse (PARSE@0x817a0) on the fresh buffer
   Phi (0x81794 `mv a0,s4`), its length n_b (0x81798 `mv a1,s2`; v1.8 had s9) and that record (0x8179c
   `ld a2,184(s1)`, the spill [A + 184] = fr + 2368 written at 0x814c4/0x814c8; v1.8 had [A + 152]).  The range
   owns no instrumented shadow check of section 1.6 and no UBSan trap branch of section 1.7.

   r9_st is the Lib-level run of the six metadata stores, r9_call the run of the three argument moves and the call
   taken on its lib/B contract reac_ctrl_parse_c.v (a Section hypothesis, never its code); seg_R9 composes them and
   lifts the pair to the cuts.  The contract needs mem_inv, so the run is stepped on the normalized memory
   (MemNorm) and carried back to the real memory by evt_normalize + AsanLift.evt_SR_canon_lazy (r4_run, R8's
   local copy of seg R4's), as in R3 / R4.  The write set is the five shadow bytes, the parse record, the callee's
   stack window [sp - 8800, sp), the class-1 side-stack bytes the callee's own __asan_stack_malloc_1 may use, and
   the shadow of that window; the heap invariant is re-derived once by AC.a_laws_fs_store (every written byte is
   a_store_ok, a side-stack byte or the shadow of one), with a_fs_ok rebuilt from the contract's own fp post.

   Cuts: seg_R9 is S_R9, official entry Inv_B8177c_at and official exit Inv_B817a4_at.  The call's class-1
   side-stack package (fp [1] over the parse window, reac_ctrl_parse_tls, the class-1 frames below fr) is built at
   the entry from FRA by Tac_fsfree's fra_fp, with this segment's five shadow bytes [S(fr) + 296, S(fr) + 301) at
   the head of its write list (inside the frame's shadow), and carried across the five stores by r9_fp_keep /
   r9_tls_keep.  The callee window's addressability is FRA's slot-window conjunct (the window is apart from the
   frame, fra_frame).  RBE, the input facts, ENT and FSREC move across the run because the write set misses the
   save area, the image, the input block and the bytes those facts name (r9_RBE_keep, fra_in_keep_sh, ent_munch,
   r9_fsrec).

   The official Inv_B8177c_at carries the turn records at fr + 2176 / fr + 2256, the frame bytes rt_F at Phi
   (from which the segment computes a0 = rt_k) and the fragment record's 72 addressable bytes, s2 = n_b and
   s11 = 32 (both callee-saved, kept by the call into the exit).  The b = 5 fragment fact of the exit is a model
   fact (r9_fgrf5: the fragment state is z72 before turn 5).  The parse record's own addressability is NOT
   assumed: the segment's five stores create it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_parse_c RcAsanFP asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c memcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcLay RcPortsLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmit RcEmitLib RcSynth RcSynthLib RcFinLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcFrag RcFragLib reac_ctrl_build_as_c.
Import ListNotations.
Open Scope Z_scope.

Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_parse_c.
Module RFP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module ASM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.memcmp_c.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module RBAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.

(* A byte store of a register whose value is not a literal (0x81790 `sb s5,300(s3)`): the engine's cell_of_bytes
   knows le8 / le4 / le2 / a singleton / le1 (zxb b), not le1 of a register.  le1 v is [Z_to_bv 8 (bv_unsigned v)]
   by conversion, so one extra branch serves it (the image-B twin of lib/B/Prog/Seg/A4.v's override). *)
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

(* ---- the run of the six metadata stores 0x8177c-0x81790 ---- *)
Lemma r9_st :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    rw_cells rsegs m (bv_unsigned s3 + 296) [CB 5 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (s5' : word) (m1 : word -> option byte) (b0 b1 b2 b3 b4 : byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5' s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81794) fc None m1 (seg_rom rsegs) /\ s5' = Z_to_bv 64 4 /\
         munch [(bv_unsigned s3 + 296, bv_unsigned s3 + 301)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 296) [b0; b1; b2; b3; b4] /\
         bv_signed b0 = 0 /\ bv_signed b1 = 0 /\ bv_signed b2 = 0 /\ bv_signed b3 = 0 /\ bv_signed b4 = 4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8177c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk HC HMI.
  pose proof (munch_refl [(bv_unsigned s3 + 296, bv_unsigned s3 + 301)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  do 6 step.
  apply evt_done. do 2 eexists. do 5 eexists.
  split; [reflexivity|].
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|].
  split.
  { destruct HC as ((_ & Hb) & _). cbn [cells_bytes cbytes app] in Hb. exact Hb. }
  repeat split; vm_compute; reflexivity.
Qed.

(* ---- the run of the three argument moves and the call 0x81794-0x817a0 ---- *)
Lemma r9_call : PC.reac_ctrl_parse_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A phi N o FS : Z) (fr50 junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s4 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N ->
    0 <= A -> A + 192 <= 2 ^ 64 ->
    0 <= phi < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 ->
    spv < 2 ^ 64 -> spv mod 16 = 0 -> PC.REAC_CTRL_PARSE_K <= spv ->
    HIGHMEM_BEG <= spv - PC.REAC_CTRL_PARSE_K -> spv <= APPMEM_END ->
    ro_cells rsegs m (bv_unsigned s1 + 184) [C8 (Z_to_bv 64 o)] ->
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
         ms' = MS R F (Z_to_bv 64 0x817a4) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (fst (RP.ctrlparse N fr50)) /\ getr R 20 = s4 /\ getr R 21 = s5 /\
         getr R 25 = s9 /\ getr R 18 = s2 /\ getr R 27 = s11 /\
         munch (PC.reac_ctrl_parse_fp o spv ++ RFP.fp_w [1%nat] FS ++
                [(shadow_addr (spv - PC.REAC_CTRL_PARSE_K), shadow_addr spv)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (spv - PC.REAC_CTRL_PARSE_K) spv /\
         asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' o [CB 36 (snd (RP.ctrlparse N fr50))] /\
         addressable m' (spv - PC.REAC_CTRL_PARSE_K) PC.REAC_CTRL_PARSE_K /\
         RFP.fp [1%nat] m' (bv_unsigned tp) FS (spv - PC.REAC_CTRL_PARSE_K) spv
           (PC.reac_ctrl_parse_W o spv) (PC.reac_ctrl_parse_D phi N o))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x81794) fc None m (seg_rom rsegs)).
Proof.
  intros PARSE ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A phi N o FS fr50 junk -> -> -> -> HA0 HA192 Hphi HN Ho Ho0 Hsp64 Hsp16 HspK HHM HAE
    RO ST HMI HL50 HF50 HRD Ho4 Ho36 RWo HoS HoF HAC HSW ADw ADf ADo HoApp HoCF ADbc
    HBC1 HBC2 HBC3 HBC4 HBC5 FPp TLS.
  unfold PC.reac_ctrl_parse_contract in PARSE. cbv zeta in PARSE.
  assert (HK : PC.REAC_CTRL_PARSE_K = 8800) by reflexivity.
  assert (HAPP : APPMEM_END = 140737488355328) by reflexivity.
  assert (Hsp0 : 0 <= spv) by lia.
  assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply MState.unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply MState.unsigned_lit; lia).
  rewrite EA in RO.
  step. step. step. step.
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
  replace (ret_pc (Z_to_bv 64 0x817a4)) with (Z_to_bv 64 0x817a4)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STc|].
  split; [exact ACc|]. split; [exact SWc|].
  split; [exact (RWc Ho0)|]. split; [exact ADc | exact FPc].
Qed.

(* ---- the write set of the segment, and the cells it misses ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R8.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
(* seg R4's helpers (r4_run, r4_fra, ...), in R8's local copy re-fitted to v1.9 *)
Module R4m := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.R8.
Open Scope Z_scope.

(* The class-1 cells of the side stack, in closed form: the hint word [FS + 8, FS + 16), the 2 ^ 13 flag bytes
   [FS + 20480, FS + 28672) and the 2 ^ 13 frames of 128 bytes [FS + 1085440, FS + 2134016). *)
Lemma r9_M1 : ASM.fs_M 1%nat = 8192.
Proof. reflexivity. Qed.

Lemma r9_hint1 : forall FS, ASM.fs_hint FS 1%nat = FS + 8.
Proof. intros FS. unfold ASM.fs_hint. cbn [Z.of_nat]. lia. Qed.

Lemma r9_flag1 : forall FS, ASM.fs_flag FS 1%nat 0 = FS + 20480.
Proof.
  intros FS. unfold ASM.fs_flag.
  replace (2 ^ 15) with 32768 by reflexivity.
  replace (2 ^ (15 - Z.of_nat 1)) with 16384 by reflexivity. lia.
Qed.

Lemma r9_frame1_0 : forall FS, ASM.fs_frame FS 1%nat 0 = FS + 1085440.
Proof. intros FS. unfold ASM.fs_frame. replace (2 ^ 20) with 1048576 by reflexivity. cbn [Z.of_nat]. lia. Qed.

Lemma r9_frame1_M : forall FS, ASM.fs_frame FS 1%nat (ASM.fs_M 1%nat) = FS + 2134016.
Proof.
  intros FS. unfold ASM.fs_frame, ASM.fs_B. rewrite r9_M1.
  replace (2 ^ 20) with 1048576 by reflexivity. cbn [Z.of_nat]. lia.
Qed.

Definition r9_W (sh o spv FS : Z) : list LF.ivl :=
  [(sh, sh + 5); (o, o + 36); (spv - 8800, spv);
   (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016));
   (shadow_addr (spv - 8800), shadow_addr spv)].

(* The contract's footprint is a sub-list of r9_W, so the callee's munch weakens to it. *)
Lemma r9_W_sub : forall sh o spv FS, o <> 0 ->
  LF.sub_fp (PC.reac_ctrl_parse_fp o spv ++ RFP.fp_w [1%nat] FS ++
             [(shadow_addr (spv - PC.REAC_CTRL_PARSE_K), shadow_addr spv)]) (r9_W sh o spv FS).
Proof.
  intros sh o spv FS Ho x Hx. unfold r9_W in Hx. cbn [LF.outside] in Hx.
  unfold PC.reac_ctrl_parse_fp, PC.REAC_CTRL_PARSE_K, RFP.fp_w, RFP.fp_w1.
  rewrite (proj2 (Z.eqb_neq o 0) Ho).
  cbn [flat_map app].
  rewrite r9_hint1, r9_flag1, r9_frame1_0, r9_frame1_M, r9_M1.
  cbn [LF.outside].
  repeat split; try exact I; lia.
Qed.

Lemma r9_W_sub5 : forall sh o spv FS, LF.sub_fp [(sh, sh + 5)] (r9_W sh o spv FS).
Proof. intros sh o spv FS x Hx. unfold r9_W in Hx. cbn [LF.outside] in Hx. cbn [LF.outside]. tauto. Qed.

(* Membership of r9_W, from the eight range tests. *)
Lemma r9_out : forall sh o spv FS x,
  (x < sh \/ sh + 5 <= x) ->
  (x < o \/ o + 36 <= x) ->
  (x < spv - 8800 \/ spv <= x) ->
  (x < FS + 8 \/ FS + 16 <= x) ->
  (x < FS + 20480 \/ FS + 28672 <= x) ->
  (x < FS + 1085440 \/ FS + 2134016 <= x) ->
  (x < shadow_addr (FS + 1085440) \/ shadow_addr (FS + 2134016) <= x) ->
  (x < shadow_addr (spv - 8800) \/ shadow_addr spv <= x) ->
  LF.outside (r9_W sh o spv FS) x.
Proof. intros. unfold r9_W. cbn [LF.outside]. repeat split; try exact I; lia. Qed.

(* A shadow byte of an address outside an eight-aligned range is outside that range's shadow. *)
Lemma r9_sh_out : forall lo hi x, lo mod 8 = 0 -> hi mod 8 = 0 -> (x < lo \/ hi <= x) ->
  shadow_addr x < shadow_addr lo \/ shadow_addr hi <= shadow_addr x.
Proof. intros lo hi x Hl Hh Hx. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* An application byte is never a shadow byte, so it misses the two shadow ranges of r9_W. *)
Lemma r9_out_app : forall sh o spv FS x,
  app_mem x ->
  (forall a, FS + 1085440 <= a < FS + 2134016 -> app_mem a) ->
  (forall a, spv - 8800 <= a < spv -> app_mem a) ->
  (x < sh \/ sh + 5 <= x) ->
  (x < o \/ o + 36 <= x) ->
  (x < spv - 8800 \/ spv <= x) ->
  (x < FS + 8 \/ FS + 16 <= x) ->
  (x < FS + 20480 \/ FS + 28672 <= x) ->
  (x < FS + 1085440 \/ FS + 2134016 <= x) ->
  LF.outside (r9_W sh o spv FS) x.
Proof.
  intros sh o spv FS x Hx Hf Hw H1 H2 H3 H4 H5 H6.
  apply r9_out; try assumption.
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

(* ---- fp and its tls premise across the segment's five shadow-byte stores ----
   RcAsanFPLib's fl_fp / fl_tls move them across a write inside the callee window [lo, hi); this segment writes
   five shadow bytes instead, so the entry cut carries that range as the head of fp's W list and the two lemmas
   below are fl_fp / fl_tls with that range in place of the window (the side stack's own bytes are application
   memory, so a shadow byte never lies in them). *)
Lemma r9_fp_drop : forall cs m TP FS lo hi r W0 D,
  RFP.fp cs m TP FS lo hi (r :: W0) D -> RFP.fp cs m TP FS lo hi W0 D.
Proof.
  intros cs m TP FS lo hi r W0 D (DT & TS & C & T & DB & k & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & HWd & HDd).
  exists DT, TS, C, T, DB, k.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
  split; [exact (proj2 (proj1 (fl_dj_cons r W0 _) HWd)) | exact HDd].
Qed.

Lemma r9_fp_keep : forall cs m m' TP FS lo hi a b W0 D W',
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

Lemma r9_tls_keep : forall cs m m' TP FS lo hi a b W0 D W' X,
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

(* ---- the side stack after the call: a_fs_ok rebuilt ----
   The class-1 hint word and flag bytes are read off the contract's own fp post (fp_cls); every other class keeps
   its hint word and flag bytes by the munch (the run writes inside [FS, FS + 36864) only class 1's hint word and
   flag bytes); the presence of the region, the header word and the needs_gc byte are fp's own. *)
Lemma r9_fs_ok : forall m m' TP FS lo hi W D W',
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
  rewrite r9_M1 in HFl.
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

(* ---- the parse record is addressable after the five metadata stores ----
   [S(fr) + 296, S(fr) + 301) = [0, 0, 0, 0, 4] is the shadow of [fr + 2368, fr + 2408): the first 32 bytes are in
   granules with shadow 0, the last 4 bytes (fr + 2400 .. fr + 2403) in a granule with shadow 4 > their offset. *)
Lemma r9_addr_rec : forall m fr (b0 b1 b2 b3 b4 : byte),
  fr mod 8 = 0 -> 0 <= fr -> fr + 2404 <= APPMEM_END ->
  (forall a, fr + 2368 <= a < fr + 2404 -> app_mem a) ->
  bytes_at rsegs m (shadow_addr fr + 296) [b0; b1; b2; b3; b4] ->
  bv_signed b0 = 0 -> bv_signed b1 = 0 -> bv_signed b2 = 0 -> bv_signed b3 = 0 -> bv_signed b4 = 4 ->
  addressable m (fr + 2368) 36.
Proof.
  intros m fr b0 b1 b2 b3 b4 H8 H0 HE Happ (_ & _ & Hb) E0 E1 E2 E3 E4.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|].
  assert (Esh : shadow_addr (fr + 2368 + i) = shadow_addr fr + 296 + i / 8).
  { unfold shadow_addr. replace (fr + 2368 + i) with (i + (fr / 8 + 296) * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. Z.div_mod_to_equations. lia. }
  assert (Hk : 0 <= i / 8 <= 4) by (Z.div_mod_to_equations; lia).
  pose proof (Hb (Z.to_nat (i / 8)) ltac:(cbn [length]; lia)) as E.
  rewrite Z2Nat.id in E by lia. rewrite <- Esh in E.
  assert (Hmod : (fr + 2368 + i) mod 8 = i mod 8).
  { replace (fr + 2368 + i) with (i + (fr / 8 + 296) * 8) by (Z.div_mod_to_equations; lia).
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

(* ---- fp and its tls premise across a byte-wise agreeing memory (the MemNorm normalization) ---- *)
Lemma r9_atls_tr : forall m m0 TP DT TS C T DB k,
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

Lemma r9_fp_tr : forall cs m m0 TP FS lo hi W D,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  (stk rsegs m FS (FS + ASM.FS_SIZE) -> stk rsegs m0 FS (FS + ASM.FS_SIZE)) ->
  RFP.fp cs m TP FS lo hi W D -> RFP.fp cs m0 TP FS lo hi W D.
Proof.
  intros cs m m0 TP FS lo hi W D TB TS0
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & HDd).
  exists DT, TS, C, T, DB, k.
  split; [exact (r9_atls_tr m m0 TP DT TS C T DB k TB HT)|].
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

(* The image's LOAD segments map, page-rounded, one run of pages: the last one alone covers [2 ^ 21, GT).  So an
   address of that range lies on an image page, and a heap block's bytes (which lie on none) are above GT. *)
Definition r9_pages_b : bool :=
  existsb (fun s => (Z.of_N (seg_base s) / 4096 * 4096 <=? 2 ^ 21) &&
                    (0x5fe000 <=? (Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4095) / 4096 * 4096)) rsegs.

Lemma r9_pages_true : r9_pages_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r9_on_page : forall a, 2 ^ 21 <= a < 0x5fe000 -> AC.a_on_img_page a.
Proof.
  intros a Ha. pose proof r9_pages_true as H. unfold r9_pages_b in H.
  apply existsb_exists in H. destruct H as (s & Hin & Hs).
  apply andb_prop in Hs. destruct Hs as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin|]. lia.
Qed.

(* An address the write set covers lies in one of its ranges. *)
Lemma r9_not_out : forall W x, ~ LF.outside W x -> exists r, In r W /\ fst r <= x < snd r.
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

(* The shadow of an application range that stays inside one half of AppMem is shadow memory. *)
Lemma r9_sh_in : forall lo hi x, lo < hi -> app_mem lo -> app_mem (hi - 1) ->
  (hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo) ->
  shadow_addr lo <= x < shadow_addr hi -> in_shadow x.
Proof.
  intros lo hi x Hlh A1 A2 Hone Hx.
  unfold app_mem, in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
    APPMEM_END in *.
  destruct A1 as [A1|A1]; destruct A2 as [A2|A2]; destruct Hone as [Hone|Hone];
    Z.div_mod_to_equations; lia.
Qed.

(* A shadow byte lies outside every application range that stays inside one half of AppMem. *)
Lemma r9_shadow_vs_app : forall y lo hi, in_shadow y -> app_mem lo -> app_mem (hi - 1) -> lo < hi ->
  (hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo) -> y < lo \/ hi <= y.
Proof.
  intros y lo hi Hy A1 A2 Hlh Hone.
  unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *.
  destruct Hy as [Hy|Hy]; destruct A1 as [A1|A1]; destruct A2 as [A2|A2]; destruct Hone as [Hone|Hone]; lia.
Qed.

(* Off the image a writable byte is a raw byte of the overlay, so it reads: wview has no segment to fall back on. *)
Lemma r9_rd_of_w : forall (m : word -> option byte) (a : Z), 0 <= a < 2 ^ 64 ->
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

(* Every index reac_ctrl_parse reads of its 50-byte header lies in that header. *)
Lemma r9_cp_rd_lt : forall n fr50 i, In i (RP.cp_rd n fr50) -> (i < 50)%nat.
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

(* ---- model facts of the turn: the lengths of the round-trip values, the fragment state before turn 5 ---- *)

Lemma r9_row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img. destruct (Lib.Image.image_bytes rsegs (CAT + CAT_ROW * i) 296) eqn:E;
    [exact (Lib.Image.image_bytes_length rsegs 296 _ _ E) | apply repeat_length].
Qed.

Lemma r9_rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, RBAP.ba_X, RcLay.ly_Z.
  assert (HZ : length (if mrow inp =? 0 then RcLay.ly_zero
                       else if RcSynth.rc (rt_mb inp) b =? 1 then RcSynth.synth (rt_mb inp) b (rt_nb inp)
                       else RcLay.ly_zero) = 32%nat).
  { destruct (mrow inp =? 0); [reflexivity|].
    destruct (RcSynth.rc (rt_mb inp) b =? 1); [|reflexivity].
    apply RcSynthLib.rs_synth_len. apply r9_row_len. }
  destruct (b <=? 1); [apply RcFinLib.rcf_stamp32_len; exact HZ | exact HZ].
Qed.

(* n_b <> 0: 124 <= n_b <= 1492 and the emitted frame F_b has n_b bytes (RtmB's rb_rtn). *)
Lemma r9_rtn : forall inp b, rt_n inp b <> 0 ->
  124 <= rt_n inp b <= 1492 /\ length (rt_F inp b) = Z.to_nat (rt_n inp b).
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  pose proof E as E'. unfold rt_E, RBAP.ba_E in E'. apply andb_true_iff in E' as [Ew _].
  destruct (RcEmitLib.em_wok_range _ Ew) as [R _].
  split; [lia|].
  unfold rt_F, RcEmit.em_fr, RcEmit.em_hdr, box6. unfold rt_n. rewrite E.
  rewrite !length_app, OUR_length, length_map, r9_rtX_len, repeat_length. cbn [length]. lia.
Qed.

(* The turn records: 38 identity bytes and 72 fragment bytes at every turn (R6's r6_rid_len / r6_rfg_len). *)
Lemma r9_rid_len : forall inp b, length (RID inp b) = 38%nat.
Proof.
  intros inp b. unfold RID. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst];
    first [exact IH | apply RcIdentModel.ING_length; exact IH].
Qed.

Lemma r9_rtg_len : forall inp x, length (rt_g inp x) = 50%nat.
Proof. intros inp x. unfold rt_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. Qed.

Lemma r9_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb fg_next]; [|exact Hs].
  assert (Hn : 1 <= RcFrag.fg_n g <= 22).
  { unfold RcFrag.fg_fr in Efr.
    apply andb_prop in Efr as [Efr _]. apply andb_prop in Efr as [Efr H22]. apply andb_prop in Efr as [_ H1].
    apply Z.leb_le in H22. apply Z.leb_le in H1. lia. }
  destruct (RcFrag.bat g 19 =? 1).
  - cbn [fg_next]. unfold RcFrag.fg_first, RcFrag.fg_body, RcFrag.bsl.
    rewrite !length_app, !length_firstn, !length_skipn, Hs, Hg. cbn [length]. lia.
  - destruct (RcFrag.fg_keep st g) eqn:Ek; cbn [negb].
    + assert (HT : RcFrag.fg_T st g <= 64).
      { unfold RcFrag.fg_keep in Ek. apply andb_prop in Ek as [_ HT]. apply Z.leb_le in HT. exact HT. }
      destruct (RcFrag.fg_close st g); cbn [negb fg_next];
        apply RcFragLib.rf_clear_length; apply RcFragLib.rf_fg_join_length; assumption.
    + cbn [fg_next]. apply RcFragLib.rf_clear_length. exact Hs.
Qed.

Lemma r9_rfg_len : forall inp b, length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RFG. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [snd];
    first [exact IH | apply r9_fgst_len; [exact IH | apply r9_rtg_len]].
Qed.

(* The fragment state is still the zero record z72 at every turn b <= 5: only the turns 5 and 6 change it
   (rt_st's `(x =? 5) || (x =? 6)` arm), and b <= 5 means no earlier turn was one of those. *)
Lemma r9_rfg_z72 : forall inp b, (b <= 5)%nat -> RFG inp b = z72.
Proof.
  intros inp b. unfold RFG. induction b as [|b IH]; intros Hb; [reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [apply IH; lia|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [snd]; [apply IH; lia|].
  destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)) eqn:E5; cbn [snd]; [|apply IH; lia].
  exfalso. apply orb_true_iff in E5 as [E|E]; apply Z.eqb_eq in E; lia.
Qed.

(* With the zero fragment state the fragment class is never FgClose: fg_keep reads the state's byte 6 (the
   "have fragment" flag), which is 0 in z72, so the class is FgNone / FgFirst / FgDrop and fg_ret is 0. *)
Lemma r9_fgrf_z72 : forall len g, fg_rf len z72 g = 0.
Proof.
  intros len g. unfold fg_rf, fcls, RcFrag.fg_class.
  cbn [Z.eqb orb negb].
  destruct (RcFrag.fg_fr len g); cbn [negb]; [|reflexivity].
  destruct (RcFrag.bat g 19 =? 1); [reflexivity|].
  assert (Hk : RcFrag.fg_keep z72 g = false).
  { unfold RcFrag.fg_keep, RcFrag.fg_hf. replace (RcFrag.bat z72 6) with 0 by reflexivity.
    cbn [Z.eqb negb andb]. reflexivity. }
  rewrite Hk. cbn [negb]. reflexivity.
Qed.

Lemma r9_fgrf5 : forall inp, fg_rf (rt_n inp 5) (RFG inp 5) (rt_g inp 5) = 0.
Proof. intros inp. rewrite (r9_rfg_z72 inp 5%nat ltac:(lia)). apply r9_fgrf_z72. Qed.

(* nth_error of a prefix inside it. *)
Lemma r9_nth_firstn : forall (l : list byte) (n i : nat), (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  induction l as [|x l IH]; intros n i Hi; [rewrite firstn_nil; reflexivity|].
  destruct n as [|n]; [lia|]. cbn [firstn]. destruct i as [|i]; [reflexivity|].
  cbn [nth_error]. apply IH. lia.
Qed.

(* addressable back across the MemNorm normalization (R6's r6_addr_back). *)
Lemma r9_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

(* The catalogue row the round trip passes, and its 296 bytes. *)
Lemma r9_mrow_rng : forall inp, CAT <= mrow inp <= CAT + 296 * 10 /\ mrow inp mod 8 = 0.
Proof.
  intros inp. unfold mrow, istar, CAT_ROW, CAT_N, CAT.
  pose proof (Z.mod_pos_bound (mode inp / 2) 11 ltac:(lia)) as Hb.
  set (k := (mode inp / 2) mod 11) in *.
  split; [lia|].
  replace (0x9f620 + 296 * k) with ((81604 + 37 * k) * 8) by lia.
  apply Z_mod_mult.
Qed.

Lemma r9_mb_len : forall inp, length (rt_mb inp) = 296%nat.
Proof. intros inp. unfold rt_mb. apply r9_row_len. Qed.

(* RBE across a run whose write set misses the save area [A, A + 448) (the 21 spills, PRA, [A+152], [A+112] and
   [A+160] included), everything below GT (the image bytes: the row table, the box, the catalogue row and the row
   name) and the shadow bytes of out[], the identity record, our[], the row name and (adopt 10) the fragment record
   fr + 2256 (the addressability conjuncts). *)
Lemma r9_RBE_keep : forall g fr regs regs' W m m' A,
  RBE g fr regs m -> LF.munch W m m' ->
  rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  (forall x, A <= x < A + 448 -> LF.outside W x) ->
  (forall x, 0 <= x < AC.GT -> LF.outside W x) ->
  (forall x, 0 <= x < AC.GT -> LF.outside W (shadow_addr x)) ->
  (forall i, 0 <= i < 1492 -> LF.outside W (shadow_addr (fr + 544 + i))) ->
  (forall i, 0 <= i < 38 -> LF.outside W (shadow_addr (fr + 2176 + i))) ->
  (forall i, 0 <= i < 6 -> LF.outside W (shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < 72 -> LF.outside W (shadow_addr (fr + 2256 + i))) ->
  RBE g fr regs' m'.
Proof.
  intros g fr regs regs' W m m' A H MU H9 HA0 HA1 E9 HWA HWlo HWsh HOUTsh HIDsh HOURsh HFGsh.
  destruct H as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
    S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUT & HA2176 & HNM & HOUR & HTBL & HBOX & HMROW &
    HPRA & S152 & S112 & HA2256 & S160).
  unfold PRA in HPRA.
  destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
  assert (K : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Ho0 Ho1 (A1 & HA1' & Hq).
    assert (E : A1 = A) by (apply (R4m.r4_spill_A regs m off v A A1 HA1' Hq H9); lia). subst A1.
    exists A. split; [unfold rg in *; rewrite E9; exact H9|].
    unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
    intros x Hx. apply HWA. lia. }
  assert (KB : forall a bs, 0 <= a -> a + Z.of_nat (length bs) <= AC.GT ->
            bytes_at rsegs m a bs -> bytes_at rsegs m' a bs).
  { intros a bs H0 H1 Hb. eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply HWlo. lia. }
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  assert (HCATv : CAT = 652832) by reflexivity.
  pose proof (r9_mrow_rng (g_in g)) as Hmr.
  unfold RBE.
  do 21 (split; [apply K; [lia | lia | assumption]|]).
  split; [unfold OUTA in *; exact (R4m.r4_addr_keep W m m' (fr + 544) 1492 HOUT MU HOUTsh)|].
  split; [exact (R4m.r4_addr_keep W m m' (fr + 2176) 38 HA2176 MU HIDsh)|].
  split.
  { intros Hc. destruct (HNM Hc) as (Hok & Hbytes & Haddr & Hpos & Hhi).
    split; [exact Hok|]. split; [apply KB; [lia | lia | exact Hbytes]|].
    split; [|split; [exact Hpos | exact Hhi]].
    apply (R4m.r4_addr_keep W m m' _ _ Haddr MU). intros i Hi. apply HWsh. lia. }
  split; [exact (R4m.r4_addr_keep W m m' (fr + 2624) 6 HOUR MU HOURsh)|].
  split; [apply KB; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
                    | exact HTBL]|].
  split; [apply KB; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
                    | exact HBOX]|].
  split; [apply KB; [lia | rewrite r9_mb_len; lia | exact HMROW]|].
  split; [unfold PRA; do 10 (split; [apply K; [lia | lia | assumption]|]); apply K; [lia | lia | assumption]|].
  split; [apply K; [lia | lia | exact S152]|].
  split; [apply K; [lia | lia | exact S112]|].
  split; [exact (R4m.r4_addr_keep W m m' (fr + 2256) 72 HA2256 MU HFGsh)|].
  apply K; [lia | lia | exact S160].
Qed.

Section R9.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee reac_ctrl_parse (PARSE@0x817a0), taken on its lib/B contract (reac_ctrl_parse_c.v), never on
   its code. *)
Hypothesis PARSE : PC.reac_ctrl_parse_contract.

(* The allocator-law fields this file reads, in the shape its use sites take, read through SlotInv's LawFields
   (lw_*: each generated law is taken apart once there).  a_laws_fs_store has no LawFields lemma; r9_fs_store
   takes it apart here, once, by decompose (so an appended conjunct changes no line). *)
Lemma r9_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ end_in_app p n /\
  (forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ AC.a_in_img a /\
     ~ AC.a_on_img_page a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [H1 H2 H3 H4 H5].
  exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.

Lemma r9_fs_place : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ FS mod 4096 = 0 /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md FS HAH Hw HFS.
  destruct (lw_fs_place (APIf rc) H mem md FS HAH Hw HFS) as [H1 H2 H3 H4].
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma r9_fs_state : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> AC.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw HFS. exact (lw_fs_ok (APIf rc) H mem md FS HAH Hw HFS).
Qed.

(* a_fs_ok's first conjunct: every side-stack byte is writable and present. *)
Lemma r9_fs_ok_cells : forall mem FS, AC.a_fs_ok mem FS ->
  forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b.
Proof. intros mem FS H. exact (lw_fs_bytes mem FS H). Qed.

Lemma r9_fs_store : forall H mem mem' md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md FS HAH Hw HFS Hag Hwr Hok.
  decompose [and] (AC.a_laws_fs_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md FS HAH
                     Hw HFS Hag Hwr Hok).
  refine (conj _ (conj _ (conj _ _))); assumption.
Qed.

Lemma seg_R9 : forall b : nat,
  Hat B APIf ra (Inv_B817a4_at B APIf ra) b -> Hat B APIf ra (Inv_B8177c_at B APIf ra) b.
Proof.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hb6 & HHB & Hr22 & HOUR & HCUR &
                    HRBE & Hr21 & Hnz & Hr20 & HrN & Hsp184 & HIDB & HFGB & HPHI & HAD2256 & Hr27).
  subst c.
  destruct (fra_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKv : PC.REAC_CTRL_PARSE_K = 8800) by reflexivity.
  assert (HFSsz : ASM.FS_SIZE = 11571200) by reflexivity.
  assert (HFSsz2 : AC.FS_SIZE = 11571200) by reflexivity.
  rewrite Haspz in Hlo, Hstkw.
  pose proof (Hplace 8800 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
  (* the parse window is inside the slot window and apart from the frame, so FRA's window conjunct gives its
     pointwise addressability (what AC.a_call_pre asks for) *)
  assert (HADw : forall a, sp - 8800 <= a < sp -> addressable mem a 1).
  { intros a Ha. apply HWA; [lia|]. destruct Hsep as [Hs|Hs]; lia. }
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  destruct Hsp184 as (A2 & HA2 & Hq184).
  assert (HA2e : A2 = A)
    by (apply (R4m.r4_spill_A regs mem 184 (fr + 2368) A A2 HA2 Hq184 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A2.
  (* ---- the frame is application memory above the image ---- *)
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, AC.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (r9_fs_place (hb1 phi (rnb g b) ++ g_H g) mem md FSb HAH Hw HFSr)
        as (HGTb & _ & _ & HFapp).
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (Hfre : 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HGT : AC.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  assert (HLH : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (R4m.r4_sf8 fr Hfrm) as HSf8.
  (* ---- the live heap block ---- *)
  assert (HInblk : In (phi, rnb g b) (hb1 phi (rnb g b) ++ g_H g))
    by (unfold hb1; cbn [app]; left; reflexivity).
  destruct (r9_blocks (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH HInblk)
    as (Hp16 & Hp4096 & Hpstklo & HEDd & Hblkb).
  pose proof (AC.a_laws_block_high _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH HInblk)
    as Hp21.
  (* n_b <> 0, so the emitted frame has 124 <= n_b <= 1492 bytes (r9_rtn) *)
  assert (Hnz' : rt_n (g_in g) (Z.of_nat b) <> 0) by exact Hnz.
  destruct (r9_rtn (g_in g) (Z.of_nat b) Hnz') as (HNb0 & HFlen).
  assert (HNb : 124 <= rnb g b <= 1492) by exact HNb0.
  assert (HFlenZ : Z.of_nat (length (rt_F (g_in g) (Z.of_nat b))) = rnb g b)
    by (rewrite HFlen; unfold rnb; lia).
  assert (HN1 : 1 <= rnb g b) by lia.
  assert (HGTphi : AC.GT <= phi).
  { destruct (Z_lt_le_dec phi 0x5fe000) as [Hlt|Hge]; [|unfold AC.GT; lia].
    exfalso. destruct (Hblkb phi ltac:(lia)) as (_ & _ & _ & Hpg & _).
    apply Hpg. apply r9_on_page. lia. }
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh, HGTphi.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HSzA : AC.a_size (rnb g b) = rnb g b) by (unfold AC.a_size; lia).
  (* the call's class-1 side-stack package, built from FRA (Tac_fsfree's fra_fp): the writes are this segment's
     five shadow bytes (in the frame's shadow), the callee window and the parse record (in the frame); the data
     ranges are the record and, on a long frame, the 50 header bytes at Phi (inside the live block) *)
  assert (Ho0 : (fr + 2368 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (HDl : PC.reac_ctrl_parse_D phi (rnb g b) (fr + 2368) = [(phi, phi + 50); (fr + 2368, fr + 2368 + 36)]).
  { unfold PC.reac_ctrl_parse_D. rewrite Ho0.
    replace (rnb g b <? 50) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  assert (HWl : PC.reac_ctrl_parse_W (fr + 2368) (AC.aspZ regs) =
                [(sp - PC.REAC_CTRL_PARSE_K, sp); (fr + 2368, fr + 2368 + 36)]).
  { unfold PC.reac_ctrl_parse_W. rewrite Ho0, Haspz. reflexivity. }
  destruct (fra_fp B APIf ra g fr (hb1 phi (rnb g b)) regs mem md [1%nat] PC.REAC_CTRL_PARSE_K
              ((Sfr fr + 296, Sfr fr + 301) :: PC.reac_ctrl_parse_W (fr + 2368) (AC.aspZ regs))
              (PC.reac_ctrl_parse_D phi (rnb g b) (fr + 2368)) HFRA)
    as (FS & FPp & TLSp & HDJfr & HFSfr).
  { intros cc Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; lia. }
  { rewrite HKv, HFN. lia. }
  { intros w Hw. cbn [In] in Hw. rewrite HWl in Hw. cbn [In] in Hw.
    destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd].
    - right; right. unfold Sfr. lia.
    - left. rewrite HKv. lia.
    - right; left. lia. }
  { intros d Hd. rewrite HDl in Hd. cbn [In] in Hd.
    destruct Hd as [<-|[<-|[]]]; cbn [fst snd].
    - right; right. split; [lia|]. exists phi, (rnb g b).
      split; [unfold hb1; cbn [app]; left; reflexivity | lia].
    - right; left. lia. }
  rewrite Haspz in FPp, TLSp.
  rewrite r9_frame1_M in HFSfr.

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
  destruct (r9_fs_place (hb1 phi (rnb g b) ++ g_H g) mem md FS HAH HFSw ltac:(lia))
    as (_ & HFSend & _ & _).
  (* ---- the numeric separations ---- *)
  assert (HSfrD : Sfr fr + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= Sfr fr) by lia.
  assert (HShm : Sfr fr + FRAME_SHADOW <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 + 785408 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  assert (HshFS1 : 2147450880 + 785408 <= shadow_addr (FS + 1085440))
    by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
  assert (HshSP1 : 2147450880 + 785408 <= shadow_addr (sp - 8800))
    by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
  assert (Hrec296 : shadow_addr (fr + 2368) = Sfr fr + 296) by (rewrite <- (R4m.r4_sh8 fr 296); f_equal; lia).
  assert (Hrec301 : shadow_addr (fr + 2408) = Sfr fr + 301) by (rewrite <- (R4m.r4_sh8 fr 301); f_equal; lia).
  assert (HappA : forall x, A <= x < A + 448 -> app_mem x)
    by (intros x Hx; unfold app_mem; right; lia).
  assert (HappS : forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> app_mem x)
    by (intros x Hx; unfold app_mem; right; lia).
  assert (HappFS1 : forall a, FS + 1085440 <= a < FS + 2134016 -> app_mem a)
    by (intros a Ha; apply HFSapp; lia).
  (* ---- the frame body and the heap block as stacks ---- *)
  assert (Hfrdj : forall x, fr <= x < fr + FRAME_BYTES -> ~ (phi <= x < phi + rnb g b)).
  { intros x Hx Hin. destruct (Hblkb x Hin) as (_ & _ & _ & _ & Hfsx).
    destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal x Hx) as Hr. lia.
    - apply Hfsx. exact (Hfs x Hx). }
  assert (Hblkfs : forall a, phi <= a < phi + rnb g b -> ~ (FS <= a < FS + 11571200)).
  { intros a Ha Hin. destruct (Hblkb a Ha) as (_ & _ & _ & _ & Hfsx). apply Hfsx.
    exists FS. split; [lia|]. split; [exact HFSw | unfold AC.FS_SIZE; lia]. }
  assert (Hblkrd : forall a, phi <= a < phi + rnb g b -> exists bb, mrd rsegs mem (wa a) = Some bb).
  { intros a Ha. destruct (Hblkb a Ha) as (_ & Hw & Hni & _ & _).
    exact (r9_rd_of_w mem a ltac:(lia) Hni Hw). }
  assert (Hblkstk : stk rsegs mem phi (phi + rnb g b)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    split; [exact (proj1 (proj2 (Hblkb a Ha))) | exact (Hblkrd a Ha)]. }
  assert (Hfrd : forall a, fr <= a < fr + FRAME_BYTES -> exists bb, mrd rsegs mem (wa a) = Some bb).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hw). exact (proj2 (Hw a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (r9_fs_ok_cells mem FSb (r9_fs_state (hb1 phi (rnb g b) ++ g_H g) mem md FSb HAH Hw HFSr) a
                  ltac:(lia)) as (_ & bb & Hb).
      exists bb. exact Hb. }
  assert (Hfstk : stk rsegs mem fr (fr + FRAME_BYTES)).
  { split; [lia|]. split; [lia|]. intros a Ha. split; [exact (Hfrw a Ha) | exact (Hfrd a Ha)]. }
  (* ---- the normalized memory the run is stepped on ---- *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  pose proof (R4m.r4_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  pose proof (R4m.r4_stk_rel mem (normalize rsegs mem) (sp - FN_STACK) sp HR0 ltac:(lia) Hstkw) as ST0.
  pose proof (R4m.r4_stk_rel mem (normalize rsegs mem) fr (fr + FRAME_BYTES) HR0 ltac:(lia) Hfstk) as Hfstk0.
  pose proof (R4m.r4_stk_rel mem (normalize rsegs mem) phi (phi + rnb g b) HR0 ltac:(lia) Hblkstk) as Hblkstk0.
  pose proof (R4m.r4_stk_rel mem (normalize rsegs mem) FS (FS + ASM.FS_SIZE) HR0 ltac:(lia) HFSstk) as HFSstk0.
  assert (TBr : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (TBb : forall a bs, bytes_at rsegs (normalize rsegs mem) a bs -> bytes_at rsegs mem a bs)
    by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (HbvS3 : bv_unsigned (getr regs 19) = Sfr fr)
    by (unfold rg in Hr19; rewrite Hr19; apply MState.unsigned_lit; lia).
  (* the five metadata bytes of the record, as a writable cell block *)
  assert (Hshstk : stk rsegs (normalize rsegs mem) (Sfr fr + 296) (Sfr fr + 301)).
  { split; [lia|]. split; [lia|]. intros a Ha. apply HSW0.
    replace a with (Sfr fr + (a - Sfr fr)) by lia. apply R4m.r4_fsh; [exact Happ' | lia]. }
  destruct (stk_bytes rsegs (normalize rsegs mem) (Sfr fr + 296) (Sfr fr + 301) Hshstk ltac:(lia))
    as (junk5 & Hjl5 & Hjb5).
  assert (RW5 : rw_cells rsegs (normalize rsegs mem) (Sfr fr + 296) [CB 5 junk5]).
  { replace 5%nat with (length junk5) by lia. apply R4m.r4_rw_CB; [exact Hjb5|].
    replace (Z.of_nat (length junk5)) with (Sfr fr + 301 - (Sfr fr + 296)) by lia.
    exact (R4m.r4_wr_stk _ _ _ Hshstk). }
  rewrite SEGS.
  apply (R4m.r4_run regs (Z_to_bv 64 0x8177c) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x817a4 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26 /\
       getr R 10 = Z_to_bv 64 (rt_k (g_in g) (Z.of_nat b)) /\ getr R 20 = getr regs 20 /\
       getr R 21 = Z_to_bv 64 4 /\ getr R 25 = getr regs 25 /\ getr R 18 = getr regs 18 /\
       getr R 27 = getr regs 27 /\
       LF.munch (r9_W (Sfr fr + 296) (fr + 2368) sp FS) (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\
       stk rsegs m0' (sp - 8800) sp /\ stk rsegs m0' FS (FS + ASM.FS_SIZE) /\ shadow_rw m0' /\
       addressable m0' (sp - 8800) 8800 /\
       (exists bs, bytes_at rsegs m0' (fr + 2368) bs /\ length bs = 36%nat) /\
       RFP.fp [1%nat] m0' (AC.as_tp AC.ASYMS) FS (sp - PC.REAC_CTRL_PARSE_K) sp
         (PC.reac_ctrl_parse_W (fr + 2368) sp) (PC.reac_ctrl_parse_D phi (rnb g b) (fr + 2368)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite R4m.r4_mkR_of.
    eapply evt_cut.
    { apply (r9_st (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
               (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
               (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
               (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
               (getr regs 31) fp_regs fp_csr (normalize rsegs mem) junk5).
      - rewrite HbvS3. exact RW5.
      - exact HMI0. }
    intros ms' (s5' & m1 & bb0 & bb1 & bb2 & bb3 & bb4 & Ems & Es5 & MU1 & WM1 & MI1 & HB5 & EB0 & EB1 & EB2 &
                EB3 & EB4).
    subst ms'. rewrite HbvS3 in MU1, HB5.
    (* ---- the premises of reac_ctrl_parse, on the memory after the five metadata stores ---- *)
    assert (W1sub : LF.sub_fp [(Sfr fr + 296, Sfr fr + 301)] [(Sfr fr + 296, Sfr fr + 301)])
      by (intros x Hx; exact Hx).
    assert (Hshr : forall x, Sfr fr + 296 <= x < Sfr fr + 301 -> in_shadow x).
    { intros x Hx. replace x with (Sfr fr + (x - Sfr fr)) by lia. apply R4m.r4_fsh; [exact Happ' | lia]. }
    assert (TB1 : forall a bs, bytes_at rsegs mem a bs -> 0 <= a ->
               a + Z.of_nat (length bs) <= 2147450880 -> bytes_at rsegs m1 a bs).
    { intros a bs Hb Ha Hlen. eapply fl_bytes; [apply TBr; exact Hb | exact MU1 |].
      intros x Hx. apply KindBGlue.outside_one. left. lia. }
    assert (Hblklh : phi + rnb g b <= 2147450880 \/ 17592186044416 + 2147450880 <= phi).
    { pose proof (proj1 (Hblkb phi ltac:(lia))) as A1.
      pose proof (proj1 (Hblkb (phi + rnb g b - 1) ltac:(lia))) as A2.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2.
      destruct A1 as [A1|A1]; destruct A2 as [A2|A2]; lia. }
    (* the frame body and the heap block after the stores *)
    assert (Hfstk1 : stk rsegs m1 fr (fr + FRAME_BYTES)).
    { eapply stk_transport_disjoint; [exact Hfstk0 | exact MU1 | exact WM1 |].
      cbn [LF.disjoint_from]. split; [lia | exact I]. }
    destruct (stk_split rsegs m1 fr (fr + 2368) (fr + FRAME_BYTES) Hfstk1 ltac:(lia)) as (_ & Hf2).
    destruct (stk_split rsegs m1 (fr + 2368) (fr + 2404) (fr + FRAME_BYTES) Hf2 ltac:(lia)) as (Hrecs & _).
    destruct (stk_bytes rsegs m1 (fr + 2368) (fr + 2404) Hrecs ltac:(lia)) as (junk36 & Hjl36 & Hjb36).
    assert (RW36 : rw_cells rsegs m1 (fr + 2368) [CB 36 junk36]).
    { replace 36%nat with (length junk36) by lia. apply R4m.r4_rw_CB; [exact Hjb36|].
      replace (Z.of_nat (length junk36)) with (fr + 2404 - (fr + 2368)) by lia.
      exact (R4m.r4_wr_stk _ _ _ Hrecs). }
    (* the 50 header bytes the parse reads are the first 50 of the emitted frame at Phi (n_b >= 124) *)
    assert (Hrtg : rt_g (g_in g) (Z.of_nat b) = firstn 50 (rt_F (g_in g) (Z.of_nat b))).
    { unfold rt_g, fr50. rewrite firstn_app.
      replace (50 - length (rt_F (g_in g) (Z.of_nat b)))%nat with 0%nat by lia.
      cbn [firstn]. rewrite app_nil_r. reflexivity. }
    assert (HPHI1 : bytes_at rsegs m1 phi (rt_F (g_in g) (Z.of_nat b))).
    { eapply fl_bytes; [apply TBr; exact HPHI | exact MU1 |].
      rewrite HFlenZ. intros x Hx. apply KindBGlue.outside_one.
      destruct Hblklh as [H|H]; [left | right]; lia. }
    assert (Hfr50l : length (rt_g (g_in g) (Z.of_nat b)) = 50%nat) by apply r9_rtg_len.
    assert (Hfr50b : forall i, (i < 50)%nat ->
              mrd rsegs m1 (wa (phi + Z.of_nat i)) = nth_error (rt_g (g_in g) (Z.of_nat b)) i).
    { intros i Hi. destruct HPHI1 as (_ & _ & Hb). rewrite Hrtg, r9_nth_firstn by lia.
      apply Hb. lia. }
    (* the runtime cells the callee and its bcmp wrapper read *)
    pose proof (AsanRTInv.RT_real_cells _ _ _ HRT) as HREAL.
    pose proof (AsanRTInv.RT_cf_cells _ _ _ HRT) as HCF.
    assert (HinB : In (0xa2610, 0x98930) RT_REALS)
      by (apply (nth_error_In _ 2%nat); unfold RT_REALS; reflexivity).
    assert (HinM : In (0xa2608, 0x98a00) RT_REALS)
      by (apply (nth_error_In _ 9%nat); unfold RT_REALS; reflexivity).
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
    { eapply fl_asan_cells; [exact (R4m.r4_cells_rel mem (normalize rsegs mem) HR0
                                     (AsanRTInv.RT_cells _ _ _ HRT)) | exact MU1 |].
      intros x Hx. apply KindBGlue.outside_one. left. unfold RT_LO, RT_HI in Hx. lia. }
    assert (HSW1 : shadow_rw m1).
    { intros a Ha. destruct (HSW0 a Ha) as (Hv & bb & Hb). split; [apply WM1; exact Hv|].
      destruct (Z_le_gt_dec (Sfr fr + 296) a) as [H1|H1].
      - destruct (Z_lt_ge_dec a (Sfr fr + 301)) as [H2|H2].
        + apply (R4m.r4_ba_rd m1 (Sfr fr + 296) _ a HB5). cbn [length]. lia.
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
    { rewrite HKv. apply (R4m.r4_addr_keep [(Sfr fr + 296, Sfr fr + 301)] (normalize rsegs mem) m1
                            (sp - 8800) 8800 (R4m.r4_addr_rel mem (normalize rsegs mem) _ _ HR0 ADwm) MU1).
      intros i Hi. apply KindBGlue.outside_one.
      pose proof (r9_sh_out (fr + 2368) (fr + 2408) (sp - 8800 + i) ltac:(Z.div_mod_to_equations; lia)
                    ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as Hs.
      rewrite Hrec296, Hrec301 in Hs. lia. }
    assert (ADphi1 : 50 <= rnb g b -> addressable m1 phi 50).
    { intros H50.
      assert (ADm : addressable mem phi 50).
      { replace phi with (phi + 0) by lia.
        exact (addressable_sub mem phi (AC.a_size (rnb g b)) 0 50 (proj2 HHB) ltac:(lia) ltac:(lia)
                 ltac:(lia)). }
      apply (R4m.r4_addr_keep [(Sfr fr + 296, Sfr fr + 301)] (normalize rsegs mem) m1 phi 50
               (R4m.r4_addr_rel mem (normalize rsegs mem) _ _ HR0 ADm) MU1).
      intros i Hi. apply KindBGlue.outside_one.
      pose proof (r9_sh_out (fr + 2368) (fr + 2408) (phi + i) ltac:(Z.div_mod_to_equations; lia)
                    ltac:(Z.div_mod_to_equations; lia) ltac:(pose proof (Hfrdj (phi + i)); lia)) as Hs.
      rewrite Hrec296, Hrec301 in Hs. lia. }
    assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (ADrec1 : addressable m1 (fr + 2368) 36)
      by exact (r9_addr_rec m1 fr bb0 bb1 bb2 bb3 bb4 Hfr8 ltac:(lia) ltac:(lia)
                  ltac:(intros a Ha; apply Happ'; lia) HB5 EB0 EB1 EB2 EB3 EB4).
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
      apply (R4m.r4_addr_keep [(Sfr fr + 296, Sfr fr + 301)] (normalize rsegs mem) m1
               PC.REAC_CTRL_PARSE_BC 6 (R4m.r4_addr_rel mem (normalize rsegs mem) _ _ HR0 ADbcm) MU1).
      intros i Hi. apply KindBGlue.outside_one. left.
      pose proof (R4m.r4_sa_lo (PC.REAC_CTRL_PARSE_BC + i) ltac:(unfold PC.REAC_CTRL_PARSE_BC; lia)) as Hsa.
      unfold ASAN_K in Hsa. lia. }
    (* the side-stack state after the stores *)
    assert (FP0 : RFP.fp [1%nat] (normalize rsegs mem) (AC.as_tp AC.ASYMS) FS
                    (sp - PC.REAC_CTRL_PARSE_K) sp
                    ((Sfr fr + 296, Sfr fr + 301) :: PC.reac_ctrl_parse_W (fr + 2368) sp)
                    (PC.reac_ctrl_parse_D phi (rnb g b) (fr + 2368))).
    { apply (r9_fp_tr _ mem); [exact TBr | | exact FPp].
      intros _. exact HFSstk0. }
    assert (FP1 : RFP.fp [1%nat] m1 (AC.as_tp AC.ASYMS) FS (sp - PC.REAC_CTRL_PARSE_K) sp
                    ((Sfr fr + 296, Sfr fr + 301) :: PC.reac_ctrl_parse_W (fr + 2368) sp)
                    (PC.reac_ctrl_parse_D phi (rnb g b) (fr + 2368)))
      by exact (r9_fp_keep _ _ _ _ _ _ _ _ _ _ _ _ FP0 MU1 WM1 W1sub Hshr).
    assert (TLS1 : PC.reac_ctrl_parse_tls m1 (AC.as_tp AC.ASYMS) FS (sp - PC.REAC_CTRL_PARSE_K) sp).
    { unfold PC.reac_ctrl_parse_tls. intros DT TS C T DB k HT.
      apply (r9_tls_keep _ (normalize rsegs mem) m1 _ FS _ _ _ _ _ _ _ _ FP0 MU1 W1sub); [|exact HT].
      intros DT' TS' C' T' DB' k' HT'.
      apply TLSp. exact (r9_atls_tr (normalize rsegs mem) mem _ _ _ _ _ _ _ TBb HT'). }
    assert (HbvTP : bv_unsigned (getr regs 4) = AC.as_tp AC.ASYMS)
      by (rewrite Hr4; apply MState.unsigned_lit; unfold AC.as_tp, AC.ASYMS; cbn; lia).
    eapply evt_mono.
    + apply (r9_call PARSE) with (spv := sp) (A := A) (phi := phi) (N := rnb g b) (o := fr + 2368)
        (FS := FS) (fr50 := rt_g (g_in g) (Z.of_nat b)) (junk := junk36).
      * unfold rg in Hr2. exact Hr2.
      * unfold rg in Hr9. exact Hr9.
      * unfold rg in Hr20. exact Hr20.
      * unfold rg in HrN. exact HrN.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact Hspm.
      * lia.
      * lia.
      * lia.
      * rewrite HbvA. apply R4m.r4_ro8.
        eapply fl_bytes; [apply TBr; exact Hq184 | exact MU1 |].
        intros x Hx. rewrite length_le8 in Hx. apply KindBGlue.outside_one. lia.
      * rewrite HKv.
        destruct (stk_split rsegs (normalize rsegs mem) (sp - FN_STACK) (sp - 8800) sp ST0 ltac:(lia))
          as (_ & Hs).
        eapply stk_transport_disjoint; [exact Hs | exact MU1 | exact WM1 |].
        cbn [LF.disjoint_from]. split; [lia | exact I].
      * exact MI1.
      * exact Hfr50l.
      * intros H50. split; [lia|]. split; [lia|]. left. rewrite HKv. lia.
      * intros i Hi. pose proof (r9_cp_rd_lt _ _ _ Hi) as Hlt. exact (Hfr50b i Hlt).
      * Z.div_mod_to_equations; lia.
      * lia.
      * exact RW36.
      * rewrite HKv. lia.
      * intros H50. destruct (Z_le_gt_dec (fr + 2404) phi) as [H|H]; [left; lia|].
        right. destruct (Z_le_gt_dec (phi + rnb g b) (fr + 2368)) as [H2|H2]; [lia|].
        exfalso. exact (Hfrdj (Z.max phi (fr + 2368)) ltac:(lia) ltac:(lia)).
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
      * rewrite HbvTP. exact (r9_fp_drop _ _ _ _ _ _ _ _ _ FP1).
      * rewrite HbvTP. exact TLS1.
    + intros ms2 (R & m' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P22 & P23 & P24 & P26 & P10 & P20 & P21 &
                  P25 & P18 & P27 & MU2 & WM2 & MI2 & ST2 & AC2 & SW2 & RW2 & ADc2 & FP2).
      exists R, (Z_to_bv 64 0x817a4), m'. split; [exact Hms|].
      split; [reflexivity|].
      split; [exact P2|]. split; [exact P3|].
      split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|].
      split; [exact P22|]. split; [exact P23|].
      split; [exact P24|]. split; [exact P26|].
      split; [exact P10|].
      split; [exact P20|].
      split; [exact (eq_trans P21 Es5)|].
      split; [exact P25|].
      split; [exact P18|].
      split; [exact P27|].
      split.
      { assert (MU1' : LF.munch [(Sfr fr + 296, Sfr fr + 296 + 5)] (normalize rsegs mem) m1)
          by (replace (Sfr fr + 296 + 5) with (Sfr fr + 301) by lia; exact MU1).
        eapply LF.munch_trans.
        - exact (LF.munch_weaken _ _ _ _ (r9_W_sub5 (Sfr fr + 296) (fr + 2368) sp FS) MU1').
        - exact (LF.munch_weaken _ _ _ _ (r9_W_sub (Sfr fr + 296) (fr + 2368) sp FS ltac:(lia)) MU2). }
      split; [exact (LF.wmono_trans rsegs _ _ _ WM1 WM2)|].
      split; [rewrite HKv in ST2; exact ST2|].
      pose proof FP2 as FP2c. rewrite HbvTP in FP2c.
      split.
      { destruct FP2 as (DT2 & TS2 & C2 & T2 & DB2 & k2 & HT2 & HTP2 & HPl2 & _).
        destruct HPl2 as (_ & _ & _ & _ & HS2). exact HS2. }
      split; [exact SW2|].
      split; [rewrite HKv in ADc2; exact ADc2|].
      split.
      { destruct RW2 as ((Hwf & Hb) & _). cbn [cells_wf cell_wf] in Hwf.
        cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
        exists (snd (RP.ctrlparse (rnb g b) (rt_g (g_in g) (Z.of_nat b)))).
        split; [exact Hb | exact (proj1 Hwf)]. }
      exact FP2c.
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K22 & K23 & K24 & K26 & K10 & K20 & K21 & K25 & K18 & K27 &
       MU0 & WM0 & STw0 & STFS0 & SW0' & ADw0 & HRec & FPm0)
      Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 (rt_k (g_in g) (Z.of_nat b))) by (rewrite Hreg; exact K10).
    assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (E21 : getr regs'' 21 = Z_to_bv 64 4) by (rewrite Hreg; exact K21).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    (* ---- back from the normalized memory to the real one ---- *)
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    pose proof (R4m.r4_stk_back mem' m0' (sp - 8800) sp HRel ltac:(lia) STw0) as STw.
    pose proof (R4m.r4_stk_back mem' m0' FS (FS + ASM.FS_SIZE) HRel ltac:(lia) STFS0) as STFS.
    pose proof (R4m.r4_srw_back mem' m0' HRel SW0') as SW'.
    assert (TBb2 : forall a bs, bytes_at rsegs m0' a bs -> bytes_at rsegs mem' a bs)
      by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem' m0' a bs HRel) Hb)).
    destruct HRec as (bs36 & Hbs36 & Hlen36).
    assert (HRecR : bytes_at rsegs mem' (fr + 2368) bs36) by (apply TBb2; exact Hbs36).
    assert (FPm : RFP.fp [1%nat] mem' (AC.as_tp AC.ASYMS) FS (sp - PC.REAC_CTRL_PARSE_K) sp
                    (PC.reac_ctrl_parse_W (fr + 2368) sp) (PC.reac_ctrl_parse_D phi (rnb g b) (fr + 2368)))
      by exact (r9_fp_tr [1%nat] m0' mem' _ _ _ _ _ _ TBb2 (fun _ => STFS) FPm0).
    pose proof (r9_addr_back mem' m0' (sp - 8800) 8800 HRel ADw0) as ADw'.
    (* the block's place, in the forms lia can use *)
    assert (Hblkfr : forall i, 0 <= i < rnb g b -> phi + i < fr \/ fr + FRAME_BYTES <= phi + i).
    { intros i Hi. destruct (Z_lt_le_dec (phi + i) fr) as [H|H]; [left; exact H|].
      destruct (Z_lt_le_dec (phi + i) (fr + FRAME_BYTES)) as [H2|H2]; [|right; exact H2].
      exfalso. exact (Hfrdj (phi + i) ltac:(lia) ltac:(lia)). }
    assert (Hblkfs' : forall i, 0 <= i < rnb g b -> phi + i < FS \/ FS + 11571200 <= phi + i).
    { intros i Hi. destruct (Z_lt_le_dec (phi + i) FS) as [H|H]; [left; exact H|].
      destruct (Z_lt_le_dec (phi + i) (FS + 11571200)) as [H2|H2]; [|right; exact H2].
      exfalso. exact (Hblkfs (phi + i) ltac:(lia) ltac:(lia)). }
    (* ---- every written byte is readable after the run ---- *)
    assert (RDW : forall x, ~ LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) x ->
              exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. destruct (r9_not_out _ _ Hx) as (r & Hin & Hr).
      unfold r9_W in Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd] in Hr.
      - assert (Hs : in_shadow x)
          by (replace x with (Sfr fr + (x - Sfr fr)) by lia; apply R4m.r4_fsh; [exact Happ' | lia]).
        exact (proj2 (SW' x Hs)).
      - apply (R4m.r4_ba_rd mem' (fr + 2368) bs36 x HRecR). rewrite Hlen36. lia.
      - destruct STw as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - destruct STFS as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - destruct STFS as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - destruct STFS as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - assert (Hs : in_shadow x)
          by exact (r9_sh_in (FS + 1085440) (FS + 2134016) x ltac:(lia) ltac:(apply HFSapp; lia)
                      ltac:(apply HFSapp; lia) ltac:(destruct HFSlow as [H|H]; lia) Hr).
        exact (proj2 (SW' x Hs)).
      - assert (Hs : in_shadow x)
          by exact (r9_sh_in (sp - 8800) sp x ltac:(lia) ltac:(apply HAwin; lia) ltac:(apply HAwin; lia)
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
              ~ AC.a_store_ok (hb1 phi (rnb g b) ++ g_H g)
                  (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (FS <= q < FS + AC.FS_SIZE) ->
              ~ (exists bb, FS <= bb < FS + AC.FS_SIZE /\ q = shadow_addr bb) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hnok Hnfs Hnsh.
      destruct (R4m.r4_out_dec (r9_W (Sfr fr + 296) (fr + 2368) sp FS) q) as [Ho|Hno].
      - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
      - exfalso. destruct (r9_not_out _ _ Hno) as (r & Hin & Hr).
        assert (Ebb : shadow_addr (8 * (q - 2147450880)) = q)
          by (unfold shadow_addr, ASAN_K; rewrite Z.mul_comm, Z.div_mul by lia; lia).
        unfold r9_W in Hin. cbn [In] in Hin.
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
      by exact (r9_fs_state (hb1 phi (rnb g b) ++ g_H g) mem md FS HAH HFSw ltac:(lia)).
    assert (HFSOK' : AC.a_fs_ok mem' FS).
    { apply (r9_fs_ok mem mem' (AC.as_tp AC.ASYMS) FS (sp - PC.REAC_CTRL_PARSE_K) sp
               (PC.reac_ctrl_parse_W (fr + 2368) sp) (PC.reac_ctrl_parse_D phi (rnb g b) (fr + 2368))
               (r9_W (Sfr fr + 296) (fr + 2368) sp FS) HFSOK FPm MU).
      - intros x Hx. apply r9_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | destruct HFSlow as [H|H]; lia | lia | lia | lia | lia | lia].
      - intros x Hx. apply r9_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | destruct HFSlow as [H|H]; lia | lia | lia | lia | lia | lia].
      - intros x Hx. apply r9_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | destruct HFSlow as [H|H]; lia | lia | lia | lia | lia | lia].
      - intros x Hx. apply r9_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | destruct HFSlow as [H|H]; lia | lia | lia | lia | lia | lia]. }
    destruct (r9_fs_store (hb1 phi (rnb g b) ++ g_H g) mem mem' md FS HAH HFSw
                ltac:(lia) Hagree Hwrit HFSOK') as (HAH' & _ & HSTK' & _).
    (* ---- FRA at the memory after the run ---- *)
    assert (HDJ : rt_disjoint (r9_W (Sfr fr + 296) (fr + 2368) sp FS)).
    { unfold AsanRTInv.rt_disjoint, r9_W, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF,
        RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN.
      cbn [LF.disjoint_from]. repeat split; first [exact I | lia]. }
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
      { split; [lia|]. split; [lia|]. intros a Ha. apply SW'.
        replace a with (Sfr fr + (a - Sfr fr)) by lia. apply R4m.r4_fsh; [exact Happ' | lia]. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia.
      reflexivity. }
    assert (HimgOut : forall y, 2147450880 <= y < 2147450880 + 785408 ->
              LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) y).
    { intros y Hy. apply r9_out;
        first [ lia | destruct HLH as [H|H]; lia | destruct HFSlow as [H|H]; lia ]. }
    assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (R4m.r4_sa_lo a (R4m.r4_ag_lo a Ha)) as Hsa. unfold ASAN_K in Hsa.
      apply (R4m.r4_addr_keep (r9_W (Sfr fr + 296) (fr + 2368) sp FS) mem mem' a 1 (HAG a Ha) MU).
      intros i Hi. replace (a + i) with a by lia. apply HimgOut. lia. }
    (* the cells FRA reads outside the frame are all outside the write set *)
    assert (HWlo : forall x, 0 <= x < 6283264 -> LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) x)
      by (intros x Hx; apply r9_out; lia).
    assert (HWhdr : forall x, fr <= x < fr + 24 -> LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) x).
    { intros x Hx. apply r9_out_app; [apply Happ'; lia | exact HappFS1 | exact HAwin
        | destruct HSfrD as [H|H]; lia | lia | destruct Hsep as [H|H]; lia | lia | lia | lia]. }
    assert (HWsel : forall x, bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 56 ->
              LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) x).
    { intros x Hx. rewrite HbvA in Hx. apply r9_out_app; [apply HappA; lia | exact HappFS1 | exact HAwin
        | lia | lia | lia | lia | lia | lia]. }
    assert (HWspill : forall x, bv_unsigned (getr regs 9) + 336 <= x < bv_unsigned (getr regs 9) + 344 ->
              LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) x).
    { intros x Hx. rewrite HbvA in Hx. apply r9_out_app; [apply HappA; lia | exact HappFS1 | exact HAwin
        | lia | lia | lia | lia | lia | lia]. }
    assert (HWsaved : forall x, g_S g - 104 <= x < g_S g ->
              LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) x).
    { intros x Hx. apply r9_out_app; [apply HappS; lia | exact HappFS1 | exact HAwin
        | lia | lia | lia | lia | lia | lia]. }
    assert (HWwin : forall x, g_S g - AF.SLOT_STACK <= x < g_S g ->
              LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) x \/
              exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx. destruct (R4m.r4_out_dec (r9_W (Sfr fr + 296) (fr + 2368) sp FS) x) as [Ho|Hno];
        [left; exact Ho | right; exact (RDW x Hno)]. }
    (* a frame byte outside the parse record, and any app byte below stklo outside the frame and the side stack,
       are outside the write set; so is the shadow byte of such a byte *)
    assert (HoutFR : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 2368 <= x < fr + 2404) ->
              LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) x).
    { intros x Hx Hx2. apply r9_out_app; [apply Happ'; lia | exact HappFS1 | exact HAwin
        | destruct HSfrD as [H|H]; lia | lia | destruct Hsep as [H|H]; lia | lia | lia | lia]. }
    assert (HoutAPP : forall x, app_mem x -> x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
              ~ AC.a_in_fs AC.ASYMS mem x -> ~ (fr <= x < fr + FRAME_BYTES) ->
              LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) x).
    { intros x Hx Hxlo Hxfs Hxfr.
      assert (HxFS : ~ (FS <= x < FS + 11571200))
        by (intros Hc; apply Hxfs; apply (a_fs_in AC.ASYMS mem FS x HFSw); lia).
      pose proof Hx as Hx'. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hx'.
      apply r9_out_app; [exact Hx | exact HappFS1 | exact HAwin | lia | lia | lia | lia | lia | lia]. }
    assert (HoutFRsh : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 2368 <= x < fr + 2408) ->
              LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) (shadow_addr x)).
    { intros x Hx Hx2.
      assert (Hsha : in_shadow (shadow_addr x)) by (apply shadow_of_app; apply Happ'; lia).
      apply r9_out.
      - pose proof (r9_sh_out (fr + 2368) (fr + 2408) x ltac:(Z.div_mod_to_equations; lia)
                      ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as Hs.
        rewrite Hrec296, Hrec301 in Hs. lia.
      - exact (r9_shadow_vs_app _ (fr + 2368) (fr + 2368 + 36) Hsha ltac:(apply Happ'; lia)
                 ltac:(apply Happ'; lia) ltac:(lia) ltac:(destruct HLH as [H|H]; lia)).
      - exact (r9_shadow_vs_app _ (sp - 8800) sp Hsha ltac:(apply HAwin; lia) ltac:(apply HAwin; lia)
                 ltac:(lia) ltac:(right; lia)).
      - exact (r9_shadow_vs_app _ (FS + 8) (FS + 16) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (r9_shadow_vs_app _ (FS + 20480) (FS + 28672) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (r9_shadow_vs_app _ (FS + 1085440) (FS + 2134016) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (r9_sh_out (FS + 1085440) (FS + 2134016) x ltac:(Z.div_mod_to_equations; lia)
                 ltac:(Z.div_mod_to_equations; lia) ltac:(lia)).
      - exact (r9_sh_out (sp - 8800) sp x ltac:(Z.div_mod_to_equations; lia)
                 ltac:(Z.div_mod_to_equations; lia) ltac:(destruct Hsep as [H|H]; lia)). }
    assert (HoutSH : forall y, app_mem y -> y < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
              ~ AC.a_in_fs AC.ASYMS mem y -> ~ (fr <= y < fr + FRAME_BYTES) ->
              LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) (shadow_addr y)).
    { intros y Hy Hylo Hyfs Hyfr.
      assert (Hsha : in_shadow (shadow_addr y)) by (apply shadow_of_app; exact Hy).
      assert (HyFS : ~ (FS <= y < FS + 11571200))
        by (intros Hc; apply Hyfs; apply (a_fs_in AC.ASYMS mem FS y HFSw); lia).
      apply r9_out.
      - pose proof (r9_sh_out (fr + 2368) (fr + 2408) y ltac:(Z.div_mod_to_equations; lia)
                      ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as Hs.
        rewrite Hrec296, Hrec301 in Hs. lia.
      - exact (r9_shadow_vs_app _ (fr + 2368) (fr + 2368 + 36) Hsha ltac:(apply Happ'; lia)
                 ltac:(apply Happ'; lia) ltac:(lia) ltac:(destruct HLH as [H|H]; lia)).
      - exact (r9_shadow_vs_app _ (sp - 8800) sp Hsha ltac:(apply HAwin; lia) ltac:(apply HAwin; lia)
                 ltac:(lia) ltac:(right; lia)).
      - exact (r9_shadow_vs_app _ (FS + 8) (FS + 16) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (r9_shadow_vs_app _ (FS + 20480) (FS + 28672) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (r9_shadow_vs_app _ (FS + 1085440) (FS + 2134016) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (r9_sh_out (FS + 1085440) (FS + 2134016) y ltac:(Z.div_mod_to_equations; lia)
                 ltac:(Z.div_mod_to_equations; lia) ltac:(lia)).
      - exact (r9_sh_out (sp - 8800) sp y ltac:(Z.div_mod_to_equations; lia)
                 ltac:(Z.div_mod_to_equations; lia) ltac:(lia)). }
    (* the input block: an entry block, so app memory below stklo, outside the frame and the side stack *)
    assert (HINb : forall x, g_p g <= x < g_p g + g_n g ->
              app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
              ~ AC.a_in_fs AC.ASYMS mem x /\ ~ (fr <= x < fr + FRAME_BYTES)).
    { intros x Hx.
      destruct (Hinblk ltac:(lia)) as (Hin & _).
      destruct (r9_blocks (hb1 phi (rnb g b) ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hstk2 & _ & Hall).
      destruct (Hall x Hx) as (Happq & _ & _ & _ & Hnfs).
      split; [exact Happq|]. split; [lia|]. split; [exact Hnfs|].
      intros Hc. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
      - pose proof (Hreal x Hc) as Hr. lia.
      - exact (Hnfs (Hfs x Hc)). }
    destruct (fra_in_keep_sh g mem mem' (r9_W (Sfr fr + 296) (fr + 2368) sp FS) Hinb Hinblk MU
                ltac:(intros x Hx; destruct (HINb x Hx) as (H1 & H2 & H3 & H4);
                      split; [apply HoutAPP | apply HoutSH]; assumption)) as (HIN1' & HIN2').
    (* the shadow byte of a slot-window address outside the frame and outside the callee window *)
    assert (HoutWINsh : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
              ~ (sp - 8800 <= a < sp) ->
              LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) (shadow_addr a)).
    { intros a Ha Hafr Hawin.
      assert (Haapp : app_mem a) by (apply HappS; lia).
      assert (Hsha : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Haapp).
      apply r9_out.
      - pose proof (r9_sh_out (fr + 2368) (fr + 2408) a ltac:(Z.div_mod_to_equations; lia)
                      ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as Hs.
        rewrite Hrec296, Hrec301 in Hs. lia.
      - exact (r9_shadow_vs_app _ (fr + 2368) (fr + 2368 + 36) Hsha ltac:(apply Happ'; lia)
                 ltac:(apply Happ'; lia) ltac:(lia) ltac:(destruct HLH as [H|H]; lia)).
      - exact (r9_shadow_vs_app _ (sp - 8800) sp Hsha ltac:(apply HAwin; lia) ltac:(apply HAwin; lia)
                 ltac:(lia) ltac:(right; lia)).
      - exact (r9_shadow_vs_app _ (FS + 8) (FS + 16) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (r9_shadow_vs_app _ (FS + 20480) (FS + 28672) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (r9_shadow_vs_app _ (FS + 1085440) (FS + 2134016) Hsha ltac:(apply HFSapp; lia)
                 ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
      - exact (r9_sh_out (FS + 1085440) (FS + 2134016) a ltac:(Z.div_mod_to_equations; lia)
                 ltac:(Z.div_mod_to_equations; lia) ltac:(lia)).
      - exact (r9_sh_out (sp - 8800) sp a ltac:(Z.div_mod_to_equations; lia)
                 ltac:(Z.div_mod_to_equations; lia) ltac:(lia)). }
    (* the slot window outside the frame stays addressable: inside the callee window the callee's own post gives
       it, outside it no shadow byte of such an address is written *)
    assert (HWA' : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
              addressable mem' a 1).
    { intros a Ha1 Ha2.
      destruct (Z_le_gt_dec (sp - 8800) a) as [HL|HL]; [destruct (Z_lt_ge_dec a sp) as [HU|HU]|].
      - replace a with (sp - 8800 + (a - (sp - 8800))) by lia.
        apply (addressable_sub mem' (sp - 8800) 8800); [exact ADw' | lia | lia | lia].
      - apply (R4m.r4_addr_keep (r9_W (Sfr fr + 296) (fr + 2368) sp FS) mem mem' a 1 (HWA a Ha1 Ha2) MU).
        intros i Hi. replace (a + i) with a by lia. apply HoutWINsh; lia.
      - apply (R4m.r4_addr_keep (r9_W (Sfr fr + 296) (fr + 2368) sp FS) mem mem' a 1 (HWA a Ha1 Ha2) MU).
        intros i Hi. replace (a + i) with a by lia. apply HoutWINsh; lia. }
    (* ENT across the run: no written byte is one ENT reads (ent_kept's fifth case, the shadow of an entry
       block's byte, by HoutSH: the byte is app memory below stklo, off the side stack and the frame) *)
    assert (HKEPT : forall x, ent_kept g x -> LF.outside (r9_W (Sfr fr + 296) (fr + 2368) sp FS) x).
    { intros x Hk.
      destruct Hk as [(q & kk & i & Hin & Hni & Hi & ->) |
                      [Hik | [Habk | [(bq & Hor & ->) | (q & kk & i & Hin & Hni & Hi & ->)]]]].
      - destruct (r9_blocks (hb1 phi (rnb g b) ++ g_H g) mem md q kk HAH
                    (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hqstk & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        apply HoutAPP; [exact Happq | lia | exact Hnfs |].
        intros Hc. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
        + pose proof (Hreal (q + i) Hc) as Hr. lia.
        + exact (Hnfs (Hfs (q + i) Hc)).
      - apply HWlo. pose proof (img_below_GT x Hik) as Hx. unfold AC.GT in Hx. lia.
      - apply r9_out_app; [unfold app_mem; right; lia | exact HappFS1 | exact HAwin
          | lia | lia | lia | lia | lia | lia].
      - assert (Hb0 : (0 <= bq < 6283264) \/ (g_S g <= bq < APPMEM_END)).
        { destruct Hor as [Hi|Hr]; [left; pose proof (img_below_GT bq Hi) as Hx; unfold AC.GT in Hx; lia
                                   | right; exact Hr]. }
        assert (Hbapp : app_mem bq)
          by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; destruct Hb0; lia).
        assert (Hsha : in_shadow (shadow_addr bq)) by (apply shadow_of_app; exact Hbapp).
        apply r9_out.
        + pose proof (r9_sh_out (fr + 2368) (fr + 2408) bq ltac:(Z.div_mod_to_equations; lia)
                        ltac:(Z.div_mod_to_equations; lia) ltac:(destruct Hb0; lia)) as Hs.
          rewrite Hrec296, Hrec301 in Hs. lia.
        + exact (r9_shadow_vs_app _ (fr + 2368) (fr + 2368 + 36) Hsha ltac:(apply Happ'; lia)
                   ltac:(apply Happ'; lia) ltac:(lia) ltac:(destruct HLH as [H|H]; lia)).
        + exact (r9_shadow_vs_app _ (sp - 8800) sp Hsha ltac:(apply HAwin; lia) ltac:(apply HAwin; lia)
                   ltac:(lia) ltac:(right; lia)).
        + exact (r9_shadow_vs_app _ (FS + 8) (FS + 16) Hsha ltac:(apply HFSapp; lia)
                   ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
        + exact (r9_shadow_vs_app _ (FS + 20480) (FS + 28672) Hsha ltac:(apply HFSapp; lia)
                   ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
        + exact (r9_shadow_vs_app _ (FS + 1085440) (FS + 2134016) Hsha ltac:(apply HFSapp; lia)
                   ltac:(apply HFSapp; lia) ltac:(lia) ltac:(destruct HFSlow as [H|H]; lia)).
        + exact (r9_sh_out (FS + 1085440) (FS + 2134016) bq ltac:(Z.div_mod_to_equations; lia)
                   ltac:(Z.div_mod_to_equations; lia) ltac:(destruct Hb0; lia)).
        + exact (r9_sh_out (sp - 8800) sp bq ltac:(Z.div_mod_to_equations; lia)
                   ltac:(Z.div_mod_to_equations; lia) ltac:(destruct Hb0; lia)).
      - destruct (r9_blocks (hb1 phi (rnb g b) ++ g_H g) mem md q kk HAH
                    (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hqstk & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        apply HoutSH; [exact Happq | lia | exact Hnfs |].
        intros Hc. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
        + pose proof (Hreal (q + i) Hc) as Hr. lia.
        + exact (Hnfs (Hfs (q + i) Hc)). }
    destruct (r9_fs_store (hb1 phi (rnb g b) ++ g_H g) mem mem' md FS HAH HFSw
                ltac:(lia) Hagree Hwrit HFSOK') as (_ & HOWN'' & _ & HSTKhi').
    assert (HENT' : ENT APIf g (hb1 phi (rnb g b)) mem' md).
    { eapply ent_munch with (W := r9_W (Sfr fr + 296) (fr + 2368) sp FS) (mem := mem);
        [exact HENT | exact HAH | apply (proj1 (fr_munch_ul _ _ _)); exact MU |
         intros x Hk; apply (proj2 (fr_outside_lib _ _)); exact (HKEPT x Hk) |
         exact HSTK' | exact HSTKhi' | intros a _ Ho; exact (proj2 (HOWN'' a) Ho)]. }
    assert (HENT'' : ENT APIf g (hb1 phi (rnb g b)) mem' md') by (eapply ent_mat; [exact HENT' | exact Hmat]).
    (* FSREC (side arm): the tp word is below GT, the class-6 flag byte and the slot's last word are side-stack
       bytes the run does not write *)
    assert (HFSR : FSREC fr mem -> FSREC fr mem').
    { intros (FSb & j & Htpb & HFSbr & Hj & Hfrj & Hflag & Htail).
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
      assert (Hfl : ASM.fs_flag FS 6 j = FS + 36352 + j) by (unfold ASM.fs_flag; cbn; lia).
      assert (Hfrv : fr = FS + 6328320 + j * 4096)
        by (rewrite Hfrj; unfold ASM.fs_frame, ASM.fs_B; cbn; lia).
      rewrite HM6 in Hj.
      exists FS, j.
      split.
      { intros k Hk.
        assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                     = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
        { apply MU. rewrite MState.unsigned_lit by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
          apply HWlo. unfold AC.as_tp, AC.ASYMS; cbn; lia. }
        unfold mbyte. rewrite Hm. exact (Htpb k Hk). }
      split; [exact HFSbr|]. split; [rewrite HM6; exact Hj|]. split; [exact Hfrj|].
      split.
      { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx.
        apply r9_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | lia | lia | lia | lia | lia | lia]. }
      { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx.
        rewrite HB6 in Hx.
        apply r9_out_app; [apply HFSapp; lia | exact HappFS1 | exact HAwin
          | lia | lia | lia | lia | lia | lia]. } }
    assert (HFRAm : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md)
      by (apply (R4m.r4_fra B APIf ra empty FF g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md
                   (r9_W (Sfr fr + 296) (fr + 2368) sp FS)
                   HFRA MU WM HRO' HDJ HAH' HSTK' (fun a Ha => proj2 (SW' a Ha)) Hshnew);
          assumption).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md' HFRAm);
        try reflexivity. exact Hmat. }
    (* RBE at the exit *)
    assert (HRBE' : RBE g fr regs'' mem').
    { apply (r9_RBE_keep g fr regs regs'' (r9_W (Sfr fr + 296) (fr + 2368) sp FS) mem mem' A HRBE MU Hr9);
        [lia | lia | exact E9 | | | | | | |].
      - intros x Hx. apply r9_out_app; [apply HappA; lia | exact HappFS1 | exact HAwin
          | lia | lia | lia | lia | lia | lia].
      - intros x Hx. apply HWlo. unfold AC.GT in Hx. lia.
      - intros x Hx. apply HimgOut.
        pose proof (R4m.r4_sa_lo x ltac:(unfold AC.GT in Hx; lia)) as Hsa. unfold ASAN_K in Hsa. lia.
      - intros i Hi. apply HoutFRsh; lia.
      - intros i Hi. apply HoutFRsh; lia.
      - intros i Hi. apply HoutFRsh; lia.
      - intros i Hi. apply HoutFRsh; lia. }
    pose proof HRBE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R24 & R16 & R96 & R120 & _).
    (* the turn records and the frame bytes at Phi, kept by the run *)
    assert (HIDB' : IDBr g fr (RID (g_in g) b) mem').
    { unfold IDBr in *. eapply fl_bytes; [exact HIDB | exact MU |]. rewrite r9_rid_len.
      intros x Hx. apply HoutFR; lia. }
    assert (HFGB' : FGBr g fr (RFG (g_in g) b) mem').
    { unfold FGBr in *. eapply fl_bytes; [exact HFGB | exact MU |]. rewrite r9_rfg_len.
      intros x Hx. apply HoutFR; lia. }
    assert (HPHI' : bytes_at rsegs mem' phi (rt_F (g_in g) (Z.of_nat b))).
    { eapply fl_bytes; [exact HPHI | exact MU |]. rewrite HFlenZ. intros x Hx.
      destruct (Hblkb x ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
      apply HoutAPP; [exact Happq | lia | exact Hnfs | intros Hc; exact (Hfrdj x Hc ltac:(lia))]. }
    assert (HOUR' : OURb g fr mem').
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. apply HoutFR; lia. }
    assert (HCUR' : CUR g 7 regs'').
    { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
    assert (HHB' : HB mem' phi (rnb g b)).
    { split; [exact (proj1 HHB)|].
      apply (R4m.r4_addr_keep (r9_W (Sfr fr + 296) (fr + 2368) sp FS) mem mem' phi
               (AC.a_size (rnb g b)) (proj2 HHB) MU).
      intros i Hi. rewrite HSzA in Hi.
      destruct (Hblkb (phi + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
      apply HoutSH; [exact Happq | lia | exact Hnfs | intros Hc; exact (Hfrdj (phi + i) Hc ltac:(lia))]. }
    (* ---- the exit cut ---- *)
    rewrite <- SEGS. apply Hexit. exists phi, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|]. split; [exact Hb6|].
    split; [exact HHB'|].
    split; [unfold rg in *; rewrite E22; exact Hr22|].
    split; [exact HOUR'|].
    split; [exact HCUR'|].
    split; [exact HRBE'|].
    split; [unfold rg; exact E21|].
    split; [unfold a0v, rg; exact E10|].
    split.
    { (* RF g fr b phi regs'' mem' *)
      split; [|unfold rg in *; rewrite E18; exact HrN].
      split; [|split; [exact Hnz|split; [unfold rg in *; rewrite E20; exact Hr20 | exact HPHI']]].
      split; [exact Hb6|]. split; [exact HCUR'|]. split; [exact HOUR'|].
      split; [unfold rg in *; rewrite E22; exact Hr22|]. split; [exact HIDB' | exact HFGB']. }
    split; [exact R24|]. split; [exact R16|]. split; [exact R96|]. split; [exact R120|].
    split.
    { apply (R4m.r4_addr_keep (r9_W (Sfr fr + 296) (fr + 2368) sp FS) mem mem' (fr + 2256) 72 HAD2256 MU).
      intros i Hi. apply HoutFRsh; lia. }
    split; [intros _; exact (r9_fgrf5 (g_in g))|].
    unfold rg in *. rewrite E27. exact Hr27.
Qed.
End R9.

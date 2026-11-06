(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1665 of its 1776 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F5.v, with its module paths, module names and addresses changed; 169 of its 248 lines of code are new or changed and 1697 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0 (the image of Seg/F6F.v's header:
   pinned (internal path), sha256
   aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d). FACTS ed6b6b7b0ab, PAU pau-libreac-v190.
   Source: Seg/F6.v 5a9c598d249e (the blob this tree had at release c5e779efe8c) (F6.f6_ebc_evt, F6.v:1418, proof :1449-1507); a Theorem Labs lane's footprint twin of the
   same run: Seg/F6F.v (an earlier version, blob 61c2fb6fc482, not in this delivery) (f6_ebc_evt_F, on a working branch e1ece7d93f27 and on the
   glue base a working branch eb89fed7fac). Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c),
   lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2.
   rule 24: no function proved (a re-cut of an already-proved v1.9 run; input to the ported walk only).

   ---- SPLIT STRETCHES for F6.f6_ebc_evt (a Theorem Labs lane ruling 00:45Z; shape fixed by a Theorem Labs lane 00:48Z and by
   segF-v19-spec.md (a working note, not in this delivery); a Theorem Labs lane granted this file to
   a Theorem Labs lane at 04:01Z). The cgif-form walk applies a Theorem Labs lane's treac_ctrl_parse_spec at the
   `jal reac_ctrl_parse` at 0x81f60 (return 0x81f64), so the run is cut there. Both stretches are cut from
   F6.f6_ebc_evt's own script; no new obligation:
   - f6_ebc_pre_F: the source's binders and its 23 premises, RNG first, and the four instructions 0x81f54
     mv a0,s7 ; 0x81f58 mv a1,s2 ; 0x81f5c li a2,0 ; 0x81f60 jal, ending in the CALLEE ENTRY state (pc =
     REAC_CTRL_PARSE = 0x83578, ra = 0x81f64, a0 = f, a1 = n, a2 = 0, every other register and the memory as at
     0x81f54). This is the source's `step. step. step. step.` (F6.v:1477). No instruction of the stretch reads or
     writes memory (instruction fetch is not an access), so no rng premise is appended, and it holds for every
     footprint RNG. The callee contract does not appear.
   - f6_ebc_pre_Fs: the NARROWED pre stretch (a Theorem Labs lane's narrowed-stretch rule, 04:23Z via a Theorem Labs lane 04:34Z):
     the same four steps and conclusion, with only the premises those steps use, which is none. Its binders are
     the source's except FS and bs, which occur only in premises. The cgif-form glue (lib/A/ACtlG/F6_ebc.v)
     consumes this one: the source's premises name the frame route's side stack (fp, reac_ctrl_parse_tls), the
     MemNorm read-only agreement and the stk window, which have no source at the walk's cut.
     f6_ebc_pre_F_of_Fs re-derives the full f6_ebc_pre_F from it; f6_ebc_pre_F_of_Fs_verbatim pins its type to
     the type of f6_ebc_pre_F by constr_eq.
   - f6_ebc_post_F: the zero-step stretch from the RETURN pc 0x81f64 at a universally quantified canonical
     register map (Regs6ss.mkR_of regs; ra is not a binder), whose premises are exactly the machine-level facts
     the source's conclusion reads right after the contract: the seventeen register values (ra = 0x81f64, sp, gp,
     tp, s0, s1, a0 = the parse result, s2 .. s11) and the source post's munch / wmono / ro_agree / stk /
     shadow_rw / addressable / fp facts of the memory. This is the source's `apply LE.evt_done. exists ...` tail
     (F6.v:1494-1506). No access, so no rng premise. As Seg/R10AF.v's r10a_call34_post_F does, the start keeps
     the source's Fr (float registers) and fc (fcsr) binders instead of fp_regs / fp_csr, so that
     f6_ebc_of_pre_post can rebuild F6.f6_ebc_evt for the source's own Fr and fc (the no-weakening pin). The glue
     does not consume it: the return pc 0x81f64 is the stage's exit cut (ACtl.v seg_F6_ebc, C_A81f64_at), so the
     glue applies the exit cut to treac_ctrl_parse_spec's post directly.
   - f6_ebc_of_pre_post: f6_ebc_pre_F and f6_ebc_post_F at ExecF.RNG_all with the PLAIN contract
     (reac_ctrl_parse_contract, F6.v's Section hypothesis HPARSE) in the source's own first premise position
     re-derive F6.f6_ebc_evt; f6_ebc_of_pre_post_verbatim pins its type to the type of F6.f6_ebc_evt by
     constr_eq. Its middle part is the source's own text: the normalization of the premises (F6.v:1452-1475),
     the contract through MemNorm.evt_normalize (F6.v:1478-1485) and the transport of the post back to the real
     memory (F6.v:1486-1506).

   EVERY CHANGED SITE, against the source script (F6.v:1449-1507):
   1. f6_ebc_pre_F and f6_ebc_pre_Fs: the conclusion is the callee entry state as an equation (`ms' = MS ...`),
      closed by `apply evtF_done. reflexivity.`, as Seg/R10AF.v's r10a_call34_pre_F is.
   2. f6_ebc_pre_F_of_Fs: `exact` of f6_ebc_pre_Fs at the same binders (its premises are not used).
   3. f6_ebc_post_F's proof: `apply evtF_done`, the source's witnesses (the registers the call does not keep,
      read from regs) and F6.f6_mkR_expand to write Regs6ss.mkR_of regs as the explicit map.
   4. f6_ebc_of_pre_post: the source's `step. step. step. step.` is replaced by the evt_cut through
      f6_ebc_pre_F (evtF_evt at RNG_all), taken first, before the source's normalization block (which only
      derives facts of m, the memory both before and after the four steps); the source's
      `apply LE.evt_done. exists ...` tail is replaced by f6_ebc_post_F (evtF_evt at RNG_all), whose memory
      premises are the source's own transports (F6.v:1500-1506, unchanged).

   SIX TWIN MODULES (porter a Theorem Labs lane, 04:24Z): this file names YK11's content only through the alias AK11 of
   the full path of ctrl's copy lib/A/Reusable/YK11 (the copy F6.v's statements are written over); it names no
   content of YI04 / YI16 / YK1b / YM05 / YO09. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib RcModel RcLib RcParse RcAsanLib RcLay
  RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_kind_name_c memcmp_c bcmp_wrap_c
  asan_stack_malloc_c RcAsanFP reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 F6.
(* Last: StepF's step (evtF goals) shadows lib.Lib Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module F6sLE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module AK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

(* ---- 0x81f54 .. 0x81f60: the three argument moves and the jal, to reac_ctrl_parse's entry, under the
   source's binders and premises (none of which the four steps use). ---- *)
Lemma f6_ebc_pre_F :
  forall (RNG : footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n S FS : Z) (bs : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    asan_cells m -> shadow_rw m ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S) (reac_ctrl_parse_D f n 0) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81f64) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v
                               (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                               (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3 t4 t5 t6)
                          Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (AK11.seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f54) fc None m (AK11.seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m f n S FS bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  (* 0x81f54 mv a0,s7 ; 0x81f58 mv a1,s2 ; 0x81f5c li a2,0 ; 0x81f60 jal reac_ctrl_parse *)
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* ---- the NARROWED pre stretch: the same four steps with only the premises they use (none); the glue
   consumes this one. ---- *)
Lemma f6_ebc_pre_Fs :
  forall (RNG : footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n S : Z),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81f64) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v
                               (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                               (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3 t4 t5 t6)
                          Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (AK11.seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f54) fc None m (AK11.seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6 Fr fc m f n S.
  (* 0x81f54 mv a0,s7 ; 0x81f58 mv a1,s2 ; 0x81f5c li a2,0 ; 0x81f60 jal reac_ctrl_parse *)
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* The full pre stretch back from the narrowed one. *)
Lemma f6_ebc_pre_F_of_Fs :
  forall (RNG : footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n S FS : Z) (bs : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    asan_cells m -> shadow_rw m ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S) (reac_ctrl_parse_D f n 0) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81f64) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v
                               (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                               (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3 t4 t5 t6)
                          Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (AK11.seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f54) fc None m (AK11.seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m f n S FS bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  exact (f6_ebc_pre_Fs RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11
           t3 t4 t5 t6 Fr fc m f n S).
Qed.

(* The pin of the narrowed stretch: f6_ebc_pre_F_of_Fs states f6_ebc_pre_F's type, term for term. *)
Example f6_ebc_pre_F_of_Fs_verbatim : True.
Proof.
  let a := type of f6_ebc_pre_F in let b := type of f6_ebc_pre_F_of_Fs in constr_eq a b.
  exact I.
Qed.

(* ---- the return stretch at 0x81f64: no instruction; the source's post from the facts it holds after the
   contract. ---- *)
Lemma f6_ebc_post_F :
  forall (RNG : footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (gp tp s0 s1v s3 s4 s5 s6 s8v s9 s10 s11 : word) (Fr : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (f n S FS : Z) (bs : list byte),
    AK11.getr regs 1 = Z_to_bv 64 0x81f64 -> AK11.getr regs 2 = Z_to_bv 64 S ->
    AK11.getr regs 3 = gp -> AK11.getr regs 4 = tp -> AK11.getr regs 8 = s0 -> AK11.getr regs 9 = s1v ->
    AK11.getr regs 10 = Z_to_bv 64 (fst (ctrlparse n bs)) -> AK11.getr regs 18 = Z_to_bv 64 n ->
    AK11.getr regs 19 = s3 -> AK11.getr regs 20 = s4 -> AK11.getr regs 21 = s5 -> AK11.getr regs 22 = s6 ->
    AK11.getr regs 23 = Z_to_bv 64 f -> AK11.getr regs 24 = s8v -> AK11.getr regs 25 = s9 ->
    AK11.getr regs 26 = s10 -> AK11.getr regs 27 = s11 ->
    munch (f6_PW S FS) m mem -> wmono rsegs m mem -> ro_agree rsegs mem ->
    stk rsegs mem (S - REAC_CTRL_PARSE_K) S -> shadow_rw mem ->
    addressable mem (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    fp [1%nat] mem (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S)
      (reac_ctrl_parse_D f n 0) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81f64) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1v
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81f64) fc None m' (AK11.seg_rom rsegs) /\
         munch (f6_PW S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S)
           (reac_ctrl_parse_D f n 0))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81f64) fc None mem (AK11.seg_rom rsegs)).
Proof.
  intros RNG regs mem gp tp s0 s1v s3 s4 s5 s6 s8v s9 s10 s11 Fr fc m f n S FS bs
    K1 K2 K3 K4 K8 K9 K10 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 MU WM RO ST SR AD FP.
  apply evtF_done.
  exists (AK11.getr regs 5), (AK11.getr regs 6), (AK11.getr regs 7), (AK11.getr regs 11), (AK11.getr regs 12),
    (AK11.getr regs 13), (AK11.getr regs 14), (AK11.getr regs 15), (AK11.getr regs 16), (AK11.getr regs 17),
    (AK11.getr regs 28), (AK11.getr regs 29), (AK11.getr regs 30), (AK11.getr regs 31), mem.
  split.
  { rewrite F6.f6_mkR_expand, K1, K2, K3, K4, K8, K9, K10, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27.
    reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [exact RO|]. split; [exact ST|].
  split; [exact SR|]. split; [exact AD | exact FP].
Qed.

(* ---- the two stretches and the PLAIN contract rebuild F6.f6_ebc_evt. ---- *)
Lemma f6_ebc_of_pre_post : reac_ctrl_parse_contract ->
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n S FS : Z) (bs : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    asan_cells m -> shadow_rw m ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S) (reac_ctrl_parse_D f n 0) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    F6sLE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81f64) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1v
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81f64) fc None m' (AK11.seg_rom rsegs) /\
         munch (f6_PW S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S)
           (reac_ctrl_parse_D f n 0))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f54) fc None m (AK11.seg_rom rsegs)).
Proof.
  intros HPARSE0 ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m f n S FS bs
    Hf Hn HS HS16 HHI HAPP HST HRO Hlen Hbig HRD HAC HSW HWA HFA HBC H1 H2 H3 H4 H5 HFP HTLS.
  (* CHANGED (site 4): the source's `step. step. step. step.` is the pre stretch, taken first (the source's
     normalization block below derives facts of m only, the memory at both ends of the four steps) *)
  eapply F6sLE.evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    exact (f6_ebc_pre_F RNG_all ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11
             t3 t4 t5 t6 Fr fc m f n S FS bs
             Hf Hn HS HS16 HHI HAPP HST HRO Hlen Hbig HRD HAC HSW HWA HFA HBC H1 H2 H3 H4 H5 HFP HTLS). }
  intros ms0 ->.
  (* the source's premises on the normalized memory (F6.v:1452-1475, unchanged) *)
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (HSKl : 0x5fe000 <= S - REAC_CTRL_PARSE_K) by (unfold HIGHMEM_BEG in HHI; lia).
  pose proof (proj1 (f6_stk_iff m (normalize rsegs m) (S - REAC_CTRL_PARSE_K) S REL HSKl ltac:(lia)) HST)
    as HSTn.
  pose proof (mem_inv_normalize rsegs m) as HMIn.
  assert (HRDn : forall i, In i (cp_rd n bs) ->
            mrd rsegs (normalize rsegs m) (wa (f + Z.of_nat i)) = nth_error bs i).
  { intros i Hi. rewrite <- (mrd_rel rsegs m _ _ REL). exact (HRD i Hi). }
  pose proof (f6_cells_rel m _ REL HAC) as HACn.
  pose proof (proj1 (f6_sw_iff m _ REL) HSW) as HSWn.
  pose proof (proj1 (f6_addr_iff m _ _ _ REL) HWA) as HWAn.
  assert (HFAn : 50 <= n -> addressable (normalize rsegs m) f 50)
    by (intros Hb; exact (proj1 (f6_addr_iff m _ _ _ REL) (HFA Hb))).
  pose proof (proj1 (f6_addr_iff m _ _ _ REL) HBC) as HBCn.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H1) as H1n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H2) as H2n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H3) as H3n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H4) as H4n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H5) as H5n.
  pose proof (proj1 (f6_fp_iff _ m _ _ _ _ _ _ _ REL) HFP) as HFPn.
  assert (HTLSn : reac_ctrl_parse_tls (normalize rsegs m) (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S).
  { intros DT TS C T DB k HT. apply HTLS. exact (proj2 (f6_tls_iff m _ _ _ _ _ _ _ _ REL) HT). }
  clear HST HRD HAC HSW HWA HFA HBC H1 H2 H3 H4 H5 HFP HTLS.
  (* the contract through evt_normalize (F6.v:1478-1485, unchanged) *)
  pose proof HPARSE0 as HP. unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE in HP.
  eapply F6sLE.evt_cut.
  { eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact HRO |].
    eapply HP with (f := f) (n := n) (o := 0) (S := S) (FS := FS) (fr := bs) (junk := []).
    all: try reflexivity.
    all: try assumption.
    all: try lia.
    all: try (intros Ho; exfalso; apply Ho; reflexivity). }
  (* the post back to the real memory (F6.v:1486-1499, unchanged) *)
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    E & MU & WM & MI & ST & _ & ACm & SR & AD & FP & _) & HREL & HROs).
  subst s0'.
  destruct HREL as (Er & Ef & Epc & Esvc & Erv & Efc & Erom & Hrel).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in Er, Ef, Epc, Esvc, Erv,
    Efc, Erom, Hrel.
  set (mm' := ms_mem ms') in Hrel, HROs.
  rewrite (f6_ms_eta ms' Esvc), Er, Ef, Epc, Erv, Efc, Erom.
  replace (ret_pc (Z_to_bv 64 0x81f64)) with (Z_to_bv 64 0x81f64)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* CHANGED (site 4): the source's `apply LE.evt_done. exists ...` tail is the post stretch; its memory
     premises are the source's transports (F6.v:1500-1506, unchanged) *)
  apply (evtF_evt rsegs RNG_all).
  apply (f6_ebc_post_F RNG_all
           (mkR (Z_to_bv 64 0x81f64) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1v
                (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3' t4' t5' t6')
           mm' gp tp s0 s1v s3 s4 s5 s6 s8v s9 s10 s11 Fr fc m f n S FS bs);
    try reflexivity.
  - exact (munch_rel rsegs (f6_PW S FS) m (normalize rsegs m) mm' m0' REL Hrel HROs MU).
  - exact (wmono_rel rsegs m (normalize rsegs m) mm' m0' REL Hrel HROs WM).
  - exact (ro_agree_same rsegs m mm' HRO HROs).
  - exact (proj2 (f6_stk_iff mm' m0' (S - REAC_CTRL_PARSE_K) S Hrel HSKl ltac:(lia)) ST).
  - exact (proj2 (f6_sw_iff mm' m0' Hrel) SR).
  - exact (proj2 (f6_addr_iff mm' m0' _ _ Hrel) AD).
  - exact (proj2 (f6_fp_iff _ mm' m0' _ _ _ _ _ _ Hrel) FP).
Qed.

(* The pin: f6_ebc_of_pre_post states F6.f6_ebc_evt's type, term for term (after F6.v's Section hypothesis HPARSE,
   the plain parse contract, in the same first premise position). *)
Example f6_ebc_of_pre_post_verbatim : True.
Proof.
  let a := type of F6.f6_ebc_evt in let b := type of f6_ebc_of_pre_post in constr_eq a b.
  exact I.
Qed.

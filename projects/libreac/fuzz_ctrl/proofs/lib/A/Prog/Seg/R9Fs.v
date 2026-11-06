(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2170 of its 2292 lines of code are new or changed and 889 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R9.v; 108 of its 198 lines of code are new or changed and 2202 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R9.v 149252a8846b (the blob this tree had at release c5e779efe8c) (r9_call :1258), beside
   Seg/R9F.v blob a731621e2c6f (r9_call_F :153), at df99ee9b0bc. Callee: lib/A/Prog/reac_ctrl_parse_c.v blob
   16c204a84a2a (REAC_CTRL_PARSE = 0x83578, reac_ctrl_parse_contract :38).
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   rule 24: no function proved (kind: segment split lemma). *)

(* The SPLIT of R9.r9_call at its call of reac_ctrl_parse (split rule (a), a Theorem Labs lane 04:01Z; shape: SPLIT STRETCHES of
   segF-v19-spec.md (a working note, not in this delivery)). reac_ctrl_parse is a cgif-form fake-stack callee: the glue
   (lib/A/ACtlG/R9.v) cuts the run AT the call and consumes the call through a Theorem Labs lane's treac_ctrl_parse_spec
   (lib/A/Prog/C_reac_ctrl_parse.v (at head lib/A/Prog/C_reac_ctrl_parse.v:63) (an earlier version, blob 57b1c193d726, not in this delivery)), never through the plain contract.

   The run r9_call is 0x81670 mv a0,s8 ; 0x81674 mv a1,s2 ; 0x81678 ld a2,56(s1) ; 0x8167c jal ra,reac_ctrl_parse.
   - r9_call_pre_Fs: the NARROWED pre stretch (narrowed-stretch rule, a Theorem Labs lane via a Theorem Labs lane 04:23Z). It carries
     only the premises the four steps use: the spill base bounds (0 <= A, A + 64 <= 2^64), the 8-byte spill load at
     A + 56 (ov_read_bytes), and its one footprint premise ExecF.rng RNG (A + 56) 8. It ends at the CALLEE ENTRY
     state: pc = REAC_CTRL_PARSE, ra = 0x81680, a0 = s8, a1 = s2, a2 = o. The glue consumes this lemma.
   - r9_call_pre_F: the FULL-premise pre stretch (spec item 1): R9.r9_call's binders and premises after PARSE, in
     R9.r9_call's order, with (RNG : ExecF.footprint) first and the one rng premise appended. It is proved ONLY by
     r9_call_pre_Fs at sp := S, s2 := n, s8 := f. The callee contract does not appear in it.
   - No post stretch: the call returns to 0x81680, which is r9_call's own end pc and the segment's exit cut
     (C_A81680_at), so <r>_post_F is empty.
   - r9_call_of_pre_post: the PLAIN contract reac_ctrl_parse_contract composed with r9_call_pre_F at ExecF.RNG_all
     re-derives R9.r9_call exactly (the contract is applied as R9.v:1303-1318 applies it after its four steps).
   Pins (constr_eq is syntactic, not up to conversion):
   - r9_call_pre_F_of_Fs_pin: the conclusion of r9_call_pre_F after its premises IS the conclusion of r9_call_pre_Fs
     at sp := Z_to_bv 64 S, s2 := Z_to_bv 64 n, s8 := Z_to_bv 64 f.
   - r9_call_pre_F_prems_pin: the premises of r9_call_pre_F after RNG are R9.r9_call's premises after PARSE, one by
     one, followed by exactly the one premise ExecF.rng RNG (A + 56) 8.
   - r9_call_of_pre_post_verbatim: the type of r9_call_of_pre_post IS the type of R9.r9_call (the no-weakening
     check).
   R9.v is unchanged apart from comment text. R9F.v's code is unchanged since release c5e779efe8c (comments edited); it differs from the source blob above: 5 of its code lines changed or removed, 385 added. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmit RcEmitLib RcSynth RcSynthLib RcFinLib RcLay
  RcIdentModel RcFrag RcReply reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs Tac_fsfree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Tac Bytes.
(* The segment file itself (the source run R9.r9_call, and the alias LE of lib.Lib Exec). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R9.
(* Last but YK11: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11.getr and YK11's segment names, as R9.v and Seg/R9F.v do. *)
Import YK11.
Open Scope Z_scope.

Section RunFs.
Context {fx : YK11.FPState}.

(* ---- 1. The narrowed pre stretch: 0x81670 -> the entry of reac_ctrl_parse, ra = 0x81680. ---- *)
Lemma r9_call_pre_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2 s3i s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A o : Z),
    0 <= A -> A + 64 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    ExecF.rng RNG (A + 56) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81680) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) s8 s2 (Z_to_bv 64 o)
                               a3 a4 a5 a6 a7 s2 s3i s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2 s3i s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2 s3i s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A o HA0 HAhi HRDcur Rld.
  (* the spill base does not wrap: solve_accs needs it for the ld at s1 + 56 *)
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  (* 0x81670 mv a0,s8 ; 0x81674 mv a1,s2 ; 0x81678 ld a2,56(s1) ; 0x8167c jal reac_ctrl_parse *)
  step. step. step. step.
  apply ExecF.evtF_done.
  reflexivity.
Qed.

(* ---- 2. The full-premise pre stretch: R9.r9_call's binders and premises (after PARSE), RNG first, the one rng
   premise appended; proved only by r9_call_pre_Fs. ---- *)
Lemma r9_call_pre_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint: the stretch's one data access, the 8-byte spill load at A + 56 (0x81678) *)
    ExecF.rng RNG (A + 56) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                               (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS Rld.
  exact (r9_call_pre_Fs RNG ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 (Z_to_bv 64 n)
           s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6 Fr fc m A o HA0 HAhi HRDcur Rld).
Qed.

(* ---- 3. No post stretch (the return pc 0x81680 is r9_call's end pc and the exit cut). The plain contract composed
   with the pre stretch re-derives R9.r9_call. ---- *)
Lemma r9_call_of_pre_post :
  reac_ctrl_parse_contract ->
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81680) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse n bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f n o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros PARSE ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
  (* the pre stretch at RNG_all: 0x81670 -> the entry of reac_ctrl_parse *)
  eapply evt_cut.
  { eapply ExecF.evtF_evt,
      (r9_call_pre_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11
         t3 t4 t5 t6 Fr fc m A f n o S FS bs junk Hf Hn Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD
         Hocell HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS).
    (* the spill cell [A + 56] the stretch reads *)
    apply ExecF.rng_all; lia. }
  intros ms0 E0. cbv beta in E0. subst ms0.
  (* the call, on the plain contract, as R9.v:1303-1318 takes it after its four steps *)
  pose proof PARSE as HP. unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE in HP.
  eapply evt_cut.
  { eapply HP with (f := f) (n := n) (o := o) (S := S) (FS := FS) (fr := bs) (junk := junk);
      try reflexivity; try lia; try assumption.
    - intros _. exact Hocell.
    - intros _. split; [exact Hoaddr|]. split; [exact Hoapp | exact HoCF]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
    E & MU & WM & MI & ST & Hrw & Hac & HSW' & Hadr & FP & Htls).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81680)) with (Z_to_bv 64 0x81680)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact (Hrw Honz)|].
  split; [exact HSW'|]. split; [exact Hadr | exact FP].
Qed.

(* ---- The pins. ---- *)
(* The conclusion of a type, after all its leading (non-dependent) premises. *)
Ltac r9Fs_concl t := lazymatch t with _ -> ?u => r9Fs_concl u | _ => t end.

(* a = P1 -> ... -> Pk -> C (C not an arrow), b = Q1 -> ... -> Qk -> R -> D: checks Pi == Qi for each i, R == r, and
   that D is an ExecF.evtF (so b has exactly one premise more than a). *)
Ltac r9Fs_same_prems a b r :=
  lazymatch a with
  | ?P -> ?a' => lazymatch b with ?Q -> ?b' => constr_eq P Q; r9Fs_same_prems a' b' r end
  | _ => lazymatch b with ?R -> ?d => constr_eq R r; lazymatch d with ExecF.evtF _ _ _ _ => idtac end end
  end.

(* The conclusion of r9_call_pre_F after its premises is r9_call_pre_Fs's conclusion at sp := S, s2 := n,
   s8 := f. *)
Example r9_call_pre_F_of_Fs_pin : True.
Proof.
  assert (G : forall (RNG : ExecF.footprint)
                (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
                (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
                True); [|exact I].
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk.
  let c := type of (r9_call_pre_F RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11
                      t3 t4 t5 t6 Fr fc m A f n o S FS bs junk) in
  let d := type of (r9_call_pre_Fs RNG ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7
                      (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6 Fr fc m A o) in
  let cc := r9Fs_concl c in
  let dc := r9Fs_concl d in
  constr_eq cc dc.
  exact I.
Qed.

(* The premises of r9_call_pre_F after RNG are R9.r9_call's premises after PARSE, then the one rng premise. *)
Example r9_call_pre_F_prems_pin : True.
Proof.
  lazymatch type of R9.r9_call with ?PP -> ?TT =>
    constr_eq PP reac_ctrl_parse_contract;
    assert (G : PP -> forall RNG : ExecF.footprint, TT); [|exact I]
  end.
  intros HP RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk.
  lazymatch goal with |- ?ga =>
    let tb := type of (r9_call_pre_F RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10
                         s11 t3 t4 t5 t6 Fr fc m A f n o S FS bs junk) in
    r9Fs_same_prems ga tb (ExecF.rng RNG (A + 56) 8)
  end.
  exact (R9.r9_call HP ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
           Fr fc m A f n o S FS bs junk).
Qed.

Example r9_call_of_pre_post_verbatim : True.
Proof.
  let a := type of R9.r9_call in let b := type of r9_call_of_pre_post in constr_eq a b.
  exact I.
Qed.

End RunFs.

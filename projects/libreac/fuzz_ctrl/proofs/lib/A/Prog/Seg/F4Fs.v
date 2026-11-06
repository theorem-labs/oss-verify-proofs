(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 823 of its 864 lines of code are new or changed and 970 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F3F.v, with its module paths, module names and addresses changed; 553 of its 762 lines of code are new or changed and 655 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F4.v 2d4003b98bbc (the blob this tree had at release c5e779efe8c) at 51a11dec84a (its runs f4_dbc_call
   :2183 and f4_dbc_calln :2246, Section S, Hypothesis HPARSE : reac_ctrl_parse_contract :66); the import block and
   the f4_ba_rel tactic are Seg/F4F.v's (blob 057dfbd37441); the plain callee contract is
   lib/A/Prog/reac_ctrl_parse_c.v blob 16c204a84a2a, reac_ctrl_parse_contract :38.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: <r>_of_pre_post (r = f4_dbc_call, f4_dbc_calln) re-derives F4.<r> from <r>_pre_F and <r>_post_F at
   ExecF.RNG_all and the PLAIN callee contract between them; <r>_of_pre_post_verbatim checks by constr_eq that its
   type is the type of F4.<r> after F4's own first premise (Hypothesis HPARSE : reac_ctrl_parse_contract, F4.v:66).
   <r>_pre_F_of_Fs / <r>_post_F_of_Fs re-derive <r>_pre_F / <r>_post_F from the narrowed <r>_pre_Fs / <r>_post_Fs,
   and their _verbatim pins check by constr_eq that each has the type of the full _F.
   Mechanical re-run, route (a) (lead 22:15Z), SPLIT STRETCHES (a Theorem Labs lane 00:45Z), NARROWED STRETCHES (a Theorem Labs lane
   04:23Z); input to the ported walk only. rule 24: no function proved. *)
(* SPLIT at the call `jal reac_ctrl_parse` (call pc 0x81e80, callee reac_ctrl_parse_c.REAC_CTRL_PARSE = 0x83578,
   return pc 0x81e84). The callee contract is the PLAIN one, a Section Hypothesis in HPARSE's position.
   - <r>_pre_F / <r>_pre_Fs : 0x81e74 `mv a0,s7` ; 0x81e78 `li a1,0` ; 0x81e7c `ld a2,248(s1)` ; 0x81e80
     `jal reac_ctrl_parse`, up to the callee ENTRY state (pc = REAC_CTRL_PARSE, ra = 0x81e84, a0 = f, a1 = 0,
     a2 = o). Cut from F4.v:2226 (`step. step. step. step.`; F4F.v:231-235 is the same stretch over StepF). One
     access: the 8-byte load at A + 248, so one rng premise. No contract premise. _F carries the source run's whole
     premise list (source order) plus that rng premise; _Fs carries only what the four steps use: 0 <= A,
     A + 256 <= 2 ^ 64 (the address form of the load), the source's own read fact HRDcur (F4.v:2189 / :2252) and
     the rng premise. For f4_dbc_calln the stretch runs on the caller's REAL memory m, whose read fact is calln's
     own premise (F4.v:2252), so f4_dbc_calln_pre_Fs is f4_dbc_call_pre_Fs's text.
   - <r>_post_F / <r>_post_Fs : the source run ENDS at the return pc 0x81e84 (F4.v:2236 `apply evt_done`), so the
     post stretch has ZERO instructions (ExecF.evtF_done) and no rng premise. Start: the concrete state at the
     return pc with the canonical register map Regs6ss.mkR_of regs and the callee post's memory as a universally
     bound `mem`. _Fs premises: the register values the source post pins (getr regs k, k = 1, 2, 3, 4, 8, 9, 10,
     18 .. 27), then the contract-post facts the source post keeps (F4.v:2239-2240 for call; F4.v:2317-2329 for
     calln), over `mem` against the base `m`, each as the source states it. The source post's existential
     registers are getr regs 5/6/7/11..17/28..31. _F = the source's binders and whole premise list (source order),
     then the _Fs premises.
   DEVIATIONS from the spec's post_F template (SPLIT STRETCHES item 2):
   (1) the float map and fcsr stay the source's binders (Fr, fc) instead of fp_regs / fp_csr (the F17F deviation,
       same reason): F4.<r> quantifies over them, so a start pinned at fp_regs / fp_csr would make <r>_of_pre_post
       weaker than F4.<r> and the no-weakening pin would fail. Instantiate Fr := fp_regs, fc := fp_csr for the walk.
   (2) ra IS mentioned (getr regs 1 = Z_to_bv 64 0x81e84): the source run ends at the return point itself, and
       the source post pins ra = 0x81e84 (F4.v:2207 / :2266), so the zero-instruction post stretch must have it.
   (3) _F's binders are ALL the source's binders (F4.v:2184-2185 / :2247-2248) after RNG / regs / mem, including
       the registers the post overwrites; _Fs binds only those its premises and post name.
   CHANGED STEP (f4_dbc_calln only): F4.f4_dbc_calln normalizes at 0x81e74 (it runs F4.f4_dbc_call on
   normalize rsegs m and comes back by MemNorm.evt_normalize, F4.v:2283-2305). In the split the four pre steps run
   on the REAL m (HRDcur is on m, so F4.v:2290's ov_read_rel transfer is not used), and the normalization point
   moves to the callee entry 0x83578: there the plain contract is applied on m0 := normalize rsegs m with F4.v's
   premise transfers (:2287-2304, without the ov_read one), MemNorm.evt_normalize is applied at the callee entry
   state (its side condition is wx_apart rsegs = true, F4.v:2305; it names no pc), and the post comes back by the
   transfers of F4.v:2307-2329, composed with F4.f4_dbc_call's own selection of the contract post (F4.v:2231-2240:
   rw_cells by the contract's (o <> 0 -> ...) at o <> 0, which F4.v:2286 gives by lia from 0x5fe000 <= o). No
   new fact. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F4.
(* Required, NOT imported at file level: StepF's step / Exec names must not shadow the evt engine's, because
   <r>_of_pre_post below states F4.<r>'s text. The stretches live in Module PF, which imports them (in F4F.v's
   order, then YK11, so PF's vocabulary is F4F.v's) with module-local visibility. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF StepF RngBytes.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

(* F4.v's Section S starts at its line 58, so its Ltac definitions are section-local and not exported: this is
   F4F.v's copy (F4F.v:65-67), the same body under the same name. *)
Ltac f4_ba_rel R :=
  first [ apply (proj1 (bytes_at_rel rsegs _ _ _ _ R)); assumption
        | apply (proj2 (bytes_at_rel rsegs _ _ _ _ R)); assumption ].

Module PF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Import YK11.
(* ExecF / StepF open bv_scope; the stretches are stated in Z, as F4.v is. *)
Open Scope Z_scope.

(* The canonical register map, expanded (F17F.v f17F_mkR_of_expand's text). *)
Lemma f4F_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* A concrete register map is its own canonical map (F17F.v f17F_mkR_of_mkR's text). *)
Lemma f4F_mkR_of_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
    x23 x24 x25 x26 x27 x28 x29 x30 x31 : word,
  Regs6ss.mkR_of (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                     x25 x26 x27 x28 x29 x30 x31)
  = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
      x28 x29 x30 x31.
Proof. intros. reflexivity. Qed.

(* ======================================== f4_dbc_call ======================================== *)

(* ---- PRE: 0x81e74 `mv a0,s7` ; 0x81e78 `li a1,0` ; 0x81e7c `ld a2,248(s1)` ; 0x81e80 `jal reac_ctrl_parse`,
   up to the callee entry state. The source's binders and whole premise list (F4.v:2184-2204), then the rng
   premise of the load. ---- *)
Lemma f4_dbc_call_pre_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= 0 -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd 0 bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= 0 -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= 0 -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    ExecF.rng RNG (A + 248) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                               (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
                        Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS R248.
  (* the same region as R248, in the address form the code computes it (ld a2,248(s1)) *)
  assert (R248' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 A) + 248) 8)
    by (rewrite MState.unsigned_lit by lia; exact R248).
  (* 0x81e74 mv a0,s7 ; 0x81e78 li a1,0 ; 0x81e7c ld a2,248(s1) ; 0x81e80 jal reac_ctrl_parse *)
  step. step. step. step.
  apply ExecF.evtF_done. reflexivity.
Qed.

(* ---- PRE, narrowed: only what the four steps use. The glue consumes this one. ---- *)
Lemma f4_dbc_call_pre_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S : Z),
    0 <= A -> A + 256 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    ExecF.rng RNG (A + 248) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                               (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
                        Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S HA0 HAhi HRDcur R248.
  assert (R248' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 A) + 248) 8)
    by (rewrite MState.unsigned_lit by lia; exact R248).
  (* 0x81e74 mv a0,s7 ; 0x81e78 li a1,0 ; 0x81e7c ld a2,248(s1) ; 0x81e80 jal reac_ctrl_parse *)
  step. step. step. step.
  apply ExecF.evtF_done. reflexivity.
Qed.

Lemma f4_dbc_call_pre_F_of_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= 0 -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd 0 bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= 0 -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= 0 -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    ExecF.rng RNG (A + 248) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                               (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
                        Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS R248.
  exact (f4_dbc_call_pre_Fs RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A f o S HA0 HAhi HRDcur R248).
Qed.

Example f4_dbc_call_pre_F_of_Fs_verbatim : True.
Proof.
  let A := type of f4_dbc_call_pre_F in let B := type of f4_dbc_call_pre_F_of_Fs in constr_eq A B; exact I.
Qed.

(* ---- POST: zero instructions; the source run ends at the return pc 0x81e84 (F4.v:2236-2240). The source's
   binders and whole premise list (F4.v:2184-2204), then the register values and the contract-post facts. ---- *)
Lemma f4_dbc_call_post_F :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= 0 -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd 0 bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= 0 -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= 0 -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    getr regs 1 = Z_to_bv 64 0x81e84 -> getr regs 2 = Z_to_bv 64 S -> getr regs 3 = gp -> getr regs 4 = tp ->
    getr regs 8 = s0 -> getr regs 9 = Z_to_bv 64 A -> getr regs 10 = Z_to_bv 64 (fst (ctrlparse 0 bs)) ->
    getr regs 18 = s2i -> getr regs 19 = s3i -> getr regs 20 = s4 -> getr regs 21 = s5 -> getr regs 22 = s6 ->
    getr regs 23 = Z_to_bv 64 f -> getr regs 24 = s8 -> getr regs 25 = s9 -> getr regs 26 = s10 ->
    getr regs 27 = s11 ->
    munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem ->
    stk rsegs mem (S - REAC_CTRL_PARSE_K) S -> rw_cells rsegs mem o [CB 36 (snd (ctrlparse 0 bs))] ->
    shadow_rw mem -> addressable mem (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    fp [1%nat] mem (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
       (reac_ctrl_parse_D f 0 o) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f 0 o))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81e84) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS
    E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM ST Hrw HSW' Hadr FP.
  rewrite f4F_mkR_of_expand, E1, E2, E3, E4, E8, E9, E10, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  (* zero instructions: the source's `apply evt_done` (F4.v:2236) and its post (F4.v:2237-2240) *)
  apply ExecF.evtF_done.
  exists (getr regs 5), (getr regs 6), (getr regs 7), (getr regs 11), (getr regs 12), (getr regs 13),
    (getr regs 14), (getr regs 15), (getr regs 16), (getr regs 17), (getr regs 28), (getr regs 29),
    (getr regs 30), (getr regs 31), mem.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact Hrw|].
  split; [exact HSW'|]. split; [exact Hadr | exact FP].
Qed.

(* ---- POST, narrowed: the register values and the contract-post facts only. The glue consumes this one. ---- *)
Lemma f4_dbc_call_post_Fs :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (gp tp s0 s2i s3i s4 s5 s6 s8 s9 s10 s11 : word) (Fr : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (A f o S FS : Z) (bs : list byte),
    getr regs 1 = Z_to_bv 64 0x81e84 -> getr regs 2 = Z_to_bv 64 S -> getr regs 3 = gp -> getr regs 4 = tp ->
    getr regs 8 = s0 -> getr regs 9 = Z_to_bv 64 A -> getr regs 10 = Z_to_bv 64 (fst (ctrlparse 0 bs)) ->
    getr regs 18 = s2i -> getr regs 19 = s3i -> getr regs 20 = s4 -> getr regs 21 = s5 -> getr regs 22 = s6 ->
    getr regs 23 = Z_to_bv 64 f -> getr regs 24 = s8 -> getr regs 25 = s9 -> getr regs 26 = s10 ->
    getr regs 27 = s11 ->
    munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem ->
    stk rsegs mem (S - REAC_CTRL_PARSE_K) S -> rw_cells rsegs mem o [CB 36 (snd (ctrlparse 0 bs))] ->
    shadow_rw mem -> addressable mem (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    fp [1%nat] mem (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
       (reac_ctrl_parse_D f 0 o) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f 0 o))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81e84) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem gp tp s0 s2i s3i s4 s5 s6 s8 s9 s10 s11 Fr fc m A f o S FS bs
    E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM ST Hrw HSW' Hadr FP.
  rewrite f4F_mkR_of_expand, E1, E2, E3, E4, E8, E9, E10, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  apply ExecF.evtF_done.
  exists (getr regs 5), (getr regs 6), (getr regs 7), (getr regs 11), (getr regs 12), (getr regs 13),
    (getr regs 14), (getr regs 15), (getr regs 16), (getr regs 17), (getr regs 28), (getr regs 29),
    (getr regs 30), (getr regs 31), mem.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact Hrw|].
  split; [exact HSW'|]. split; [exact Hadr | exact FP].
Qed.

Lemma f4_dbc_call_post_F_of_Fs :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= 0 -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd 0 bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= 0 -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= 0 -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    getr regs 1 = Z_to_bv 64 0x81e84 -> getr regs 2 = Z_to_bv 64 S -> getr regs 3 = gp -> getr regs 4 = tp ->
    getr regs 8 = s0 -> getr regs 9 = Z_to_bv 64 A -> getr regs 10 = Z_to_bv 64 (fst (ctrlparse 0 bs)) ->
    getr regs 18 = s2i -> getr regs 19 = s3i -> getr regs 20 = s4 -> getr regs 21 = s5 -> getr regs 22 = s6 ->
    getr regs 23 = Z_to_bv 64 f -> getr regs 24 = s8 -> getr regs 25 = s9 -> getr regs 26 = s10 ->
    getr regs 27 = s11 ->
    munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem ->
    stk rsegs mem (S - REAC_CTRL_PARSE_K) S -> rw_cells rsegs mem o [CB 36 (snd (ctrlparse 0 bs))] ->
    shadow_rw mem -> addressable mem (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    fp [1%nat] mem (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
       (reac_ctrl_parse_D f 0 o) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f 0 o))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81e84) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS
    E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM ST Hrw HSW' Hadr FP.
  exact (f4_dbc_call_post_Fs RNG regs mem gp tp s0 s2i s3i s4 s5 s6 s8 s9 s10 s11 Fr fc m A f o S FS bs
           E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM ST Hrw HSW' Hadr FP).
Qed.

Example f4_dbc_call_post_F_of_Fs_verbatim : True.
Proof.
  let A := type of f4_dbc_call_post_F in let B := type of f4_dbc_call_post_F_of_Fs in constr_eq A B; exact I.
Qed.

(* ======================================== f4_dbc_calln ======================================== *)

(* ---- PRE on the caller's real memory m: the same four steps; calln's binders and whole premise list
   (F4.v:2247-2263), then the rng premise of the load. ---- *)
Lemma f4_dbc_calln_pre_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    ExecF.rng RNG (A + 248) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                               (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
                        Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Ho4 Hocell Howin
    HAC HSW HHI HAPP HWA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS R248.
  assert (R248' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 A) + 248) 8)
    by (rewrite MState.unsigned_lit by lia; exact R248).
  (* 0x81e74 mv a0,s7 ; 0x81e78 li a1,0 ; 0x81e7c ld a2,248(s1) ; 0x81e80 jal reac_ctrl_parse *)
  step. step. step. step.
  apply ExecF.evtF_done. reflexivity.
Qed.

(* ---- PRE, narrowed: f4_dbc_call_pre_Fs's text (the stretch reads m, whose fact HRDcur is calln's own,
   F4.v:2252). The glue consumes this one. ---- *)
Lemma f4_dbc_calln_pre_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S : Z),
    0 <= A -> A + 256 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    ExecF.rng RNG (A + 248) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                               (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
                        Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S HA0 HAhi HRDcur R248.
  assert (R248' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 A) + 248) 8)
    by (rewrite MState.unsigned_lit by lia; exact R248).
  (* 0x81e74 mv a0,s7 ; 0x81e78 li a1,0 ; 0x81e7c ld a2,248(s1) ; 0x81e80 jal reac_ctrl_parse *)
  step. step. step. step.
  apply ExecF.evtF_done. reflexivity.
Qed.

Lemma f4_dbc_calln_pre_F_of_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    ExecF.rng RNG (A + 248) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                               (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
                        Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Ho4 Hocell Howin
    HAC HSW HHI HAPP HWA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS R248.
  exact (f4_dbc_calln_pre_Fs RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A f o S HA0 HAhi HRDcur R248).
Qed.

Example f4_dbc_calln_pre_F_of_Fs_verbatim : True.
Proof.
  let A := type of f4_dbc_calln_pre_F in let B := type of f4_dbc_calln_pre_F_of_Fs in constr_eq A B; exact I.
Qed.

(* ---- POST: zero instructions at the return pc 0x81e84 (F4.v:2315-2329). calln's binders and whole premise list
   (F4.v:2247-2263), then the register values and the post facts calln keeps, over `mem` against m. ---- *)
Lemma f4_dbc_calln_post_F :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    getr regs 1 = Z_to_bv 64 0x81e84 -> getr regs 2 = Z_to_bv 64 S -> getr regs 3 = gp -> getr regs 4 = tp ->
    getr regs 8 = s0 -> getr regs 9 = Z_to_bv 64 A -> getr regs 10 = Z_to_bv 64 (fst (ctrlparse 0 bs)) ->
    getr regs 18 = s2i -> getr regs 19 = s3i -> getr regs 20 = s4 -> getr regs 21 = s5 -> getr regs 22 = s6 ->
    getr regs 23 = Z_to_bv 64 f -> getr regs 24 = s8 -> getr regs 25 = s9 -> getr regs 26 = s10 ->
    getr regs 27 = s11 ->
    munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem -> ro_same rsegs m mem ->
    stk rsegs mem (S - REAC_CTRL_PARSE_K) S -> rw_cells rsegs mem o [CB 36 (snd (ctrlparse 0 bs))] ->
    shadow_rw mem -> addressable mem (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    stk rsegs mem FS (FS + FS_SIZE) -> fp_cls mem FS 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81e84) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Ho4 Hocell Howin
    HAC HSW HHI HAPP HWA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS
    E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM RO' ST RW SW AD STF CLS.
  rewrite f4F_mkR_of_expand, E1, E2, E3, E4, E8, E9, E10, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  (* zero instructions: F4.v:2315-2329's witnesses and conjuncts, at the return pc *)
  apply ExecF.evtF_done.
  exists (getr regs 5), (getr regs 6), (getr regs 7), (getr regs 11), (getr regs 12), (getr regs 13),
    (getr regs 14), (getr regs 15), (getr regs 16), (getr regs 17), (getr regs 28), (getr regs 29),
    (getr regs 30), (getr regs 31), mem.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ST|]. split; [exact RW|].
  split; [exact SW|]. split; [exact AD|]. split; [exact STF | exact CLS].
Qed.

(* ---- POST, narrowed: the register values and the post facts only. The glue consumes this one. ---- *)
Lemma f4_dbc_calln_post_Fs :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (gp tp s0 s2i s3i s4 s5 s6 s8 s9 s10 s11 : word) (Fr : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (A f o S FS : Z) (bs : list byte),
    getr regs 1 = Z_to_bv 64 0x81e84 -> getr regs 2 = Z_to_bv 64 S -> getr regs 3 = gp -> getr regs 4 = tp ->
    getr regs 8 = s0 -> getr regs 9 = Z_to_bv 64 A -> getr regs 10 = Z_to_bv 64 (fst (ctrlparse 0 bs)) ->
    getr regs 18 = s2i -> getr regs 19 = s3i -> getr regs 20 = s4 -> getr regs 21 = s5 -> getr regs 22 = s6 ->
    getr regs 23 = Z_to_bv 64 f -> getr regs 24 = s8 -> getr regs 25 = s9 -> getr regs 26 = s10 ->
    getr regs 27 = s11 ->
    munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem -> ro_same rsegs m mem ->
    stk rsegs mem (S - REAC_CTRL_PARSE_K) S -> rw_cells rsegs mem o [CB 36 (snd (ctrlparse 0 bs))] ->
    shadow_rw mem -> addressable mem (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    stk rsegs mem FS (FS + FS_SIZE) -> fp_cls mem FS 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81e84) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem gp tp s0 s2i s3i s4 s5 s6 s8 s9 s10 s11 Fr fc m A f o S FS bs
    E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM RO' ST RW SW AD STF CLS.
  rewrite f4F_mkR_of_expand, E1, E2, E3, E4, E8, E9, E10, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  apply ExecF.evtF_done.
  exists (getr regs 5), (getr regs 6), (getr regs 7), (getr regs 11), (getr regs 12), (getr regs 13),
    (getr regs 14), (getr regs 15), (getr regs 16), (getr regs 17), (getr regs 28), (getr regs 29),
    (getr regs 30), (getr regs 31), mem.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ST|]. split; [exact RW|].
  split; [exact SW|]. split; [exact AD|]. split; [exact STF | exact CLS].
Qed.

Lemma f4_dbc_calln_post_F_of_Fs :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    getr regs 1 = Z_to_bv 64 0x81e84 -> getr regs 2 = Z_to_bv 64 S -> getr regs 3 = gp -> getr regs 4 = tp ->
    getr regs 8 = s0 -> getr regs 9 = Z_to_bv 64 A -> getr regs 10 = Z_to_bv 64 (fst (ctrlparse 0 bs)) ->
    getr regs 18 = s2i -> getr regs 19 = s3i -> getr regs 20 = s4 -> getr regs 21 = s5 -> getr regs 22 = s6 ->
    getr regs 23 = Z_to_bv 64 f -> getr regs 24 = s8 -> getr regs 25 = s9 -> getr regs 26 = s10 ->
    getr regs 27 = s11 ->
    munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem -> ro_same rsegs m mem ->
    stk rsegs mem (S - REAC_CTRL_PARSE_K) S -> rw_cells rsegs mem o [CB 36 (snd (ctrlparse 0 bs))] ->
    shadow_rw mem -> addressable mem (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    stk rsegs mem FS (FS + FS_SIZE) -> fp_cls mem FS 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81e84) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Ho4 Hocell Howin
    HAC HSW HHI HAPP HWA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS
    E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM RO' ST RW SW AD STF CLS.
  exact (f4_dbc_calln_post_Fs RNG regs mem gp tp s0 s2i s3i s4 s5 s6 s8 s9 s10 s11 Fr fc m A f o S FS bs
           E1 E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 MU WM RO' ST RW SW AD STF CLS).
Qed.

Example f4_dbc_calln_post_F_of_Fs_verbatim : True.
Proof.
  let A := type of f4_dbc_calln_post_F in let B := type of f4_dbc_calln_post_F_of_Fs in constr_eq A B; exact I.
Qed.

End PF.

Section F4Fs.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
(* The plain callee contract, as F4.v:66 takes it (unit-copy names, as F4.v). *)
Hypothesis HPARSE : reac_ctrl_parse_contract.

(* ---- f4_dbc_call: the two stretches at RNG_all, with the plain contract between them (F4.v:2227-2235),
   re-derive F4.f4_dbc_call. ---- *)
Lemma f4_dbc_call_of_pre_post :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= 0 -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd 0 bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= 0 -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= 0 -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f 0 o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS.
  (* stretch 1 at RNG_all: 0x81e74 .. 0x81e80, to the callee entry *)
  eapply LE.evt_cut.
  { apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    apply (PF.f4_dbc_call_pre_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6
             s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m A f o S FS bs junk); try assumption.
    apply ExecF.rng_all; lia. }
  intros ms' ->.
  (* the call, with the plain contract: F4.f4_dbc_call's own application (F4.v:2227-2235) *)
  pose proof HPARSE as HP. unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE in HP.
  eapply evt_cut.
  { eapply HP with (f := f) (n := 0) (o := o) (S := S) (FS := FS) (fr := bs) (junk := junk);
      try reflexivity; try assumption; try lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
    E & MU & WM & MI & ST & Hrw & Hac & HSW' & Hadr & FP & Htls).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81e84)) with (Z_to_bv 64 0x81e84)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (Hrw Honz) as RW.
  (* stretch 2 at RNG_all (zero instructions), at the canonical form of the state the callee returned in *)
  rewrite <- (PF.f4F_mkR_of_mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
    (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7' s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11
    tt3 tt4 tt5 tt6).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (PF.f4_dbc_call_post_F ExecF.RNG_all _ m' ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5
           s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m A f o S FS bs junk);
    try reflexivity; assumption.
Qed.

(* ---- f4_dbc_calln: stretch 1 on the real m; the contract on normalize rsegs m at the callee entry with
   F4.f4_dbc_calln's premise transfers (F4.v:2283-2304, without the ov_read one) and MemNorm.evt_normalize there
   (F4.v:2305); the post transfers of F4.v:2307-2329; stretch 2 at RNG_all. ---- *)
Lemma f4_dbc_calln_of_pre_post :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Ho4 Hocell Howin
    HAC HSW HHI HAPP HWA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
  (* stretch 1 at RNG_all, on the caller's real memory m: 0x81e74 .. 0x81e80, to the callee entry *)
  eapply LE.evt_cut.
  { apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    apply (PF.f4_dbc_calln_pre_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6
             s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m A f o S FS bs junk); try assumption.
    apply ExecF.rng_all; lia. }
  intros ms' ->.
  (* the call at the callee entry, on the normalized memory (the CHANGED step: F4.v normalizes at 0x81e74) *)
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  set (m0 := normalize rsegs m) in REL.
  pose proof HPARSE as HP. unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE in HP.
  (* the contract at the entry state, as F4.f4_dbc_call applies it (F4.v:2229-2230: n := 0, fr := bs; its
     0 <= o and o <> 0 from calln's 0x5fe000 <= o, F4.v:2286) *)
  assert (HC := HP (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 f)
                  (Z_to_bv 64 0) (Z_to_bv 64 o) a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11
                  t3 t4 t5 t6 Fr fc m0 f 0 o S FS bs junk eq_refl eq_refl eq_refl eq_refl
                  Hf ltac:(lia) ltac:(lia) HS HS16 HSK).
  (* F4.v:2287-2304's premise transfers, without :2290 (the ov_read one; stretch 1 used HRDcur on m) *)
  pose proof (f4_stk_rel m m0 (S - REAC_CTRL_PARSE_K) S REL ltac:(unfold REAC_CTRL_PARSE_K, HIGHMEM_BEG in *; lia) HST)
    as HST0.
  specialize (HC HST0 (mem_inv_normalize rsegs m) Hlen).
  specialize (HC ltac:(intros Hb; exfalso; lia)).
  specialize (HC ltac:(intros i Hi; change (cp_rd 0 bs) with (@nil nat) in Hi; destruct Hi)).
  specialize (HC ltac:(intros _; split; [exact Ho4|]; split; [lia|]; split;
    [ destruct Hocell as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | f4_ba_rel REL]|];
      apply (wr_at_norm rsegs m m0 o _ REL Hw); intros i Hi; apply f4_ro_gt; cbn in Hi; lia
    | split; [exact Howin | intros Hb; exfalso; lia]])).
  specialize (HC (f4_cells_rel m m0 REL HAC) (f4_shrw_rel m m0 REL HSW) HHI HAPP (f4_addr_rel m m0 _ _ REL HWA)).
  specialize (HC ltac:(intros Hb; exfalso; lia)).
  specialize (HC ltac:(intros _; split; [exact (f4_addr_rel m m0 _ _ REL Hoaddr) | split; [exact Hoapp | exact HoCF]])).
  specialize (HC (f4_addr_rel m m0 _ _ REL HBC)).
  specialize (HC ltac:(f4_ba_rel REL) ltac:(f4_ba_rel REL) ltac:(f4_ba_rel REL) ltac:(f4_ba_rel REL)
                 ltac:(f4_ba_rel REL)).
  specialize (HC (f4_fp_rel _ m m0 _ _ _ _ _ _ REL HFP)).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply HTLS; exact (proj2 (f4_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  (* MemNorm.evt_normalize at the callee entry state (F4.v:2305) *)
  pose proof (evt_normalize rsegs _ _ Fr _ fc None m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN.
  eapply LE.evt_cut; [exact HN|].
  (* the post transfers of F4.v:2307-2329, on the contract's post as F4.f4_dbc_call selects it (F4.v:2231-2240) *)
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m0' &
    E0 & MU0 & WM0 & MI0 & ST0 & RW0 & AC0 & SW0 & AD0 & FP0 & FL0) & Hrel & Hro').
  subst s0'.
  destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
  destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes, EFc,
    ERom, HR', Hro'.
  subst r' f' p' sv' rv' fc' ro'.
  pose proof (munch_rel rsegs _ m m0 m' m0' REL HR' Hro' MU0) as MU.
  pose proof (wmono_rel rsegs m m0 m' m0' REL HR' Hro' WM0) as WM.
  pose proof (f4_stk_back m' m0' _ _ HR' ST0) as ST.
  assert (RW : rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))]).
  { destruct (RW0 ltac:(lia)) as ((Hwf & Hb) & Hw). split; [split; [exact Hwf | f4_ba_rel HR']|].
    exact (wr_at_rel rsegs m' m0' o _ HR' Hw). }
  pose proof (f4_shrw_back m' m0' HR' SW0) as SW.
  pose proof (f4_addr_back m' m0' _ _ HR' AD0) as AD.
  destruct FP0 as (DT & TS & C & T & DB & k & _ & _ & Hpl & _ & _ & Hcls & _).
  assert (STF : stk rsegs m' FS (FS + FS_SIZE)).
  { destruct Hpl as (_ & _ & _ & _ & P5). exact (f4_stk_back m' m0' _ _ HR' P5). }
  pose proof (proj2 (f4_cls_rel m' m0' FS 1 HR') (Forall_inv Hcls)) as CLS.
  replace (ret_pc (Z_to_bv 64 0x81e84)) with (Z_to_bv 64 0x81e84)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* stretch 2 at RNG_all (zero instructions), at the canonical form of the state the callee returned in *)
  lazymatch goal with
  | |- LE.evt _ ?Q _ =>
      change (LE.evt rsegs Q
                (MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                         (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7' s2i s3i s4 s5 s6
                         (Z_to_bv 64 f) s8 s9 s10 s11 tt3 tt4 tt5 tt6)
                    Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs)))
  end.
  rewrite <- (PF.f4F_mkR_of_mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
    (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7' s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11
    tt3 tt4 tt5 tt6).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (PF.f4_dbc_calln_post_F ExecF.RNG_all _ m' ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5
           s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m A f o S FS bs junk);
    try reflexivity; assumption.
Qed.

(* The pins, inside the section so that both types are read against the same {fx} / {LS} / {rc} and against the
   same plain-contract premise (HPARSE is still a hypothesis here, so <r>_of_pre_post's type is the statement
   itself): <r>_of_pre_post states F4.<r>'s text after F4's own first premise, the plain parse contract
   (F4.v:66, Hypothesis HPARSE), term for term (constr_eq: syntactic, not up to conversion). *)
Example f4_dbc_call_of_pre_post_verbatim : True.
Proof.
  lazymatch type of F4.f4_dbc_call with ?P -> ?A =>
    constr_eq P reac_ctrl_parse_contract;
    let B := type of f4_dbc_call_of_pre_post in constr_eq A B
  end.
  exact I.
Qed.

Example f4_dbc_calln_of_pre_post_verbatim : True.
Proof.
  lazymatch type of F4.f4_dbc_calln with ?P -> ?A =>
    constr_eq P reac_ctrl_parse_contract;
    let B := type of f4_dbc_calln_of_pre_post in constr_eq A B
  end.
  exact I.
Qed.

End F4Fs.

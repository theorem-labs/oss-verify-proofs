(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 540 of its 622 lines of code are new or changed and 2475 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F20.v; 186 of its 245 lines of code are new or changed and 563 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F20.v blob 1cf48b422ebf (the blob this tree had at release c5e779efe8c) (the step script F20.v:496-545,
   inside seg_F20). Companion twin: Seg/F20F.v blob 4527ef54d8e7 (f20_call_evt_F, the call half).
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   rule 24: no function proved (stage glue of a walk; this file is one segment's head run).

   WHY THIS FILE EXISTS. Segment F20 (0x82418 -> 0x824b4) has NO `_F` of record for its head stretch
   0x82418 -> 0x824ac. segment-runs-A.tsv (a working note, not in this delivery) names only two runs for
   F20, `sl_run_lib:206` and `f20_call_evt:341`: the first is not a run lemma (it concludes SR and takes an
   Exec.evt as a premise, so F20F.rng.tsv (a working note, not in this delivery) marks it blocked_plain), and the second covers only the call half
   0x824ac -> 0x824b4. F20.v runs the head INLINE inside seg_F20 (F20.v:496-545), so a Theorem Labs lane's mechanical
   re-run had nothing to re-state there. `f20_head_F` below is that inline stretch, cut out and re-stepped over
   lib/Lib/StepF with a universally quantified footprint RNG, by the same route as Seg/F11F.v.

   THE PIN. There is no source run lemma for this stretch to `constr_eq` against (that is the whole reason for
   this file), so the check is a PROVED corollary instead of an Example: `f20_of_head_call` is the plain
   Lib.Exec.evt from 0x82418 to 0x824b4 that `f20_head_F` composed with `F20F.f20_call_evt_F` re-derives at
   ExecF.RNG_all, i.e. exactly what F20.seg_F20's inline stretch plus its CALL assert (F20.v:455-472) produce.
   Its premises are the head's and the call's together, with the register pins F20.v's `subst_slot` chain
   (F20.v:487-489) puts on the state: s1 = A, a0 = 0, s4 = s6 = phi + 18, s7 = phi, s8 = t_k, s10 = ASAN_K.

   NO LIFT IS CITED by the consumer of this file, and no `<f>_SRr_at` and no `_hid` placeholder: F20F's
   `f20_call_evt_F` spans the `jal` at 0x824b0 and discharges `reac_ctrl_checksum_verify_contract_F` itself with
   the callee's own closed theorem `reac_ctrl_checksum_verify_F.reac_ctrl_checksum_verify_F_holds`, so the caller
   obligation at the call site is that contract's premises, not a lift's.

   F20.v and F20F.v are UNCHANGED by this file; it Requires them and the sources only.

   THE RUN, instruction by instruction (F20.v:496-545; the same comments, kept in the proof):
     0x82418 bnez a0        a0 = 0 on the F19 fall-through, not taken
     0x8241c-0x82428        addi/srli/add/lb: the shadow byte of phi+14 (the cut carries it as 0)
     0x8242c ld a1,248(s1)  the parsed-record pointer fr + 176 (the [A+248] prologue spill)
     0x82430 lhu a1,20(a1)  its is_8819 field, the u16 at fr + 196
     0x82434 bnez a2        the shadow byte is 0, not taken
     0x82438-0x82444        the shadow byte of phi+15
     0x82448 lbu a2,14(s7)  the record byte phi+14 = v14
     0x8244c bnez a3        not taken
     0x82450-0x82458        lbu a0 = v15 ; slli ; or: the 16-bit field (v15 << 8) | v14
     0x8245c bne a0,a1      equal to the carried field16 = v14 + 256 * v15, not taken
     0x82460-0x8246c        the shadow byte of phi+16
     0x82470 bnez a1        not taken
     0x82474 lbu a0 = v16 ; 0x82478 beqz a0: the case split on v16
       v16 = 0:  0x82484-0x82490 the shadow byte of phi+17 ; 0x82494 bnez a1 not taken ;
                 lbu a0 = v17 ; seqz a0 ; addi a1,s8,-1 ; seqz a1 ; 0x824a8 bne not taken (the carried equation)
       v16 <> 0: 0x8247c li a0,0 ; 0x82480 j 0x823f4 ; 0x824a0 addi a1,s8,-1 ; 0x824a4 seqz a1 ;
                 0x824a8 bne not taken (the same carried equation, with v16 =? 0 false)
   It READS memory (ten accesses, one `rng` premise each: see F20Fs.rng.tsv) and WRITES NONE: the end memory is
   the start memory, so the consumer lifts it with the plain Reusable.YA0nR.SRr_fevt. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_checksum_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame MState Regs6ss RegisterBridge Exec Cells Step Tac Bytes.
(* The source segment (its byte readers rd1 / rd2 / rd8 and its arithmetic steps) and the call half's twin. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F20.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F20F.
(* StepF after the old engine: its step / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* YK11 last, as in F20.v (its seg_rom). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11.
Import ListNotations.
Local Open Scope Z_scope.

(* F20.v:175-177, the one local tactic the head stretch needs: the `srli` of a literal address. *)
Ltac ush := match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3] => rewrite (unsigned_lit X) by lia
  end.

(* RNG_all over a range whose bounds the lemma's own premises decide; the shadow ranges come in the
   `Z.shiftr a 3 + ASAN_K` shape, so the shift is turned into a division first (Seg/F11F.v f11F_sh_all is the
   same step for the `shadow_addr` shape). *)
Ltac f20s_rng1 :=
  try (rewrite ?Z.shiftr_div_pow2 by lia);
  try (change (2 ^ 3) with 8);
  try (unfold ASAN_K);
  try (unfold GOT_CELL_K);
  try (unfold CELL_K);
  try (unfold APPMEM_END);
  try Z.div_mod_to_equations;
  lia.
Ltac f20s_rng_all := apply ExecF.rng_all; f20s_rng1.

(* ---- The head, 0x82418 -> 0x824ac, under a footprint. ---- *)
Lemma f20_head_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi A fr tk v14 v15 v16 v17 field16 : Z),
    0 < phi -> phi + 50 <= 2 ^ 64 ->
    0 <= A -> A + 256 <= 2 ^ 64 -> 0 <= fr -> fr + 198 <= 2 ^ 64 -> 0 <= tk < 2 ^ 64 ->
    0 <= v14 < 256 -> 0 <= v15 < 256 -> 0 <= v16 < 256 -> 0 <= v17 < 256 ->
    field16 = v14 + 256 * v15 ->
    (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if tk =? 1 then 1 else 0) ->
    q64 m (A + 248) (fr + 176) ->
    u16 m (fr + 196) field16 ->
    b8 m (phi + 14) v14 -> b8 m (phi + 15) v15 -> b8 m (phi + 16) v16 -> b8 m (phi + 17) v17 ->
    b8 m (Z.shiftr (phi + 14) 3 + ASAN_K) 0 ->
    b8 m (Z.shiftr (phi + 15) 3 + ASAN_K) 0 ->
    b8 m (Z.shiftr (phi + 16) 3 + ASAN_K) 0 ->
    b8 m (Z.shiftr (phi + 17) 3 + ASAN_K) 0 ->
    ExecF.rng RNG (A + 248) 8 ->
    ExecF.rng RNG (fr + 196) 2 ->
    ExecF.rng RNG (phi + 14) 1 ->
    ExecF.rng RNG (phi + 15) 1 ->
    ExecF.rng RNG (phi + 16) 1 ->
    ExecF.rng RNG (phi + 17) 1 ->
    ExecF.rng RNG (Z.shiftr (phi + 14) 3 + ASAN_K) 1 ->
    ExecF.rng RNG (Z.shiftr (phi + 15) 3 + ASAN_K) 1 ->
    ExecF.rng RNG (Z.shiftr (phi + 16) 3 + ASAN_K) 1 ->
    ExecF.rng RNG (Z.shiftr (phi + 17) 3 + ASAN_K) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' : word),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                       a0' a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (phi + 18)) s5 (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 phi)
                       (Z_to_bv 64 tk) s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x824ac) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
               (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 (phi + 18)) s5 (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 phi)
               (Z_to_bv 64 tk) s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82418) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s9 s11 t3 t4 t5 t6 Fr fc m
    phi A fr tk v14 v15 v16 v17 field16
    Hphi0 Hphi50 HA0 HA256 Hfr0 Hfr198 Rtk Rv14 Rv15 Rv16 Rv17 Heq1 Heq2
    Hq248 Hfield Hb14 Hb15 Hb16 Hb17 Hsh14 Hsh15 Hsh16 Hsh17
    R248 RFLD Rb14 Rb15 Rb16 Rb17 RS14 RS15 RS16 RS17.
  (* the shadow ranges in the `a / 8 + ASAN_K` shape the loads take after unsigned_lit (Seg/F11F.v does the
     same with f11F_sh_rng / f11F_sh_rng') *)
  assert (RD14 : ExecF.rng RNG ((phi + 14) / 8 + ASAN_K) 1).
  { replace ((phi + 14) / 8) with (Z.shiftr (phi + 14) 3)
      by (rewrite Z.shiftr_div_pow2 by lia; reflexivity). exact RS14. }
  assert (RD15 : ExecF.rng RNG ((phi + 15) / 8 + ASAN_K) 1).
  { replace ((phi + 15) / 8) with (Z.shiftr (phi + 15) 3)
      by (rewrite Z.shiftr_div_pow2 by lia; reflexivity). exact RS15. }
  assert (RD16 : ExecF.rng RNG ((phi + 16) / 8 + ASAN_K) 1).
  { replace ((phi + 16) / 8) with (Z.shiftr (phi + 16) 3)
      by (rewrite Z.shiftr_div_pow2 by lia; reflexivity). exact RS16. }
  assert (RD17 : ExecF.rng RNG ((phi + 17) / 8 + ASAN_K) 1).
  { replace ((phi + 17) / 8) with (Z.shiftr (phi + 17) 3)
      by (rewrite Z.shiftr_div_pow2 by lia; reflexivity). exact RS17. }
  (* the byte readers the Lib engine's loads consume (F20.v:39-58) *)
  pose proof (F20.rd1 m _ _ Hsh14) as RDs14. pose proof (F20.rd1 m _ _ Hsh15) as RDs15.
  pose proof (F20.rd1 m _ _ Hsh16) as RDs16. pose proof (F20.rd1 m _ _ Hsh17) as RDs17.
  pose proof (F20.rd1 m _ _ Hb14) as RDb14. pose proof (F20.rd1 m _ _ Hb15) as RDb15.
  pose proof (F20.rd1 m _ _ Hb16) as RDb16. pose proof (F20.rd1 m _ _ Hb17) as RDb17.
  pose proof (F20.rd8 m _ _ Hq248) as RDkp.
  pose proof (F20.rd2 m _ _ Hfield) as RDfield.
  (* the landing state at 0x824ac, as F20.v's CALL assert (F20.v:455-472) states it *)
  match goal with |- ExecF.evtF _ _ ?Qg _ => set (Q := Qg) end.
  assert (FIN : forall b0 b1 b2 b3 b4 b5 b6 : word,
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 a7
               s2 s3 (Z_to_bv 64 (phi + 18)) s5 (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 phi)
               (Z_to_bv 64 tk) s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x824ac) fc None m (seg_rom rsegs))).
  { intros b0 b1 b2 b3 b4 b5 b6. apply ExecF.evtF_done. subst Q. cbv beta.
    exists b0, b1, b2, b3, b4, b5, b6. reflexivity. }
  (* 0x82418 bnez a0 : a0 = 0, not taken *)
  step. if_false.
  (* 0x8241c addi ; srli ; add ; lb a2 shadow(phi+14) *)
  step. step. step. ush.
  step.
  (* 0x8242c ld a1,248(s1) ; 0x82430 lhu a1,20(a1) ; 0x82434 bnez a2 (=0) not taken *)
  step. step. step. if_false.
  (* 0x82438 addi ; srli ; add ; lb a3 shadow(phi+15) *)
  step. step. step. ush.
  step.
  (* 0x82448 lbu a2,14(s7)=v14 ; 0x8244c bnez a3 (=0) not taken ; 0x82450 lbu a0=v15 ; slli ; or *)
  step. step. if_false. step. step. step.
  (* 0x8245c bne a0,a1 : (v15<<8)|v14 = field16 (Heq1), not taken *)
  step. rewrite (F20.cmp16_eq v14 v15 field16 Rv14 Rv15 Heq1), bv_eqb_refl; cbn [negb]; cbv iota.
  (* 0x82460 addi ; srli ; add ; lb a1 shadow(phi+16) *)
  step. step. step. ush.
  step.
  (* 0x82470 bnez a1 (=0) not taken ; 0x82474 lbu a0=v16 ; 0x82478 beqz a0 *)
  step. if_false. step. step. rewrite (F20.zxb8 v16) by lia.
  destruct (Z.eq_dec v16 0) as [Hv16|Hv16].
  - (* v16 = 0 : beqz taken to 0x82484 *)
    subst v16. rewrite bv_eqb_refl. cbv iota.
    (* 0x82484 addi ; srli ; add ; lb a1 shadow(phi+17) *)
    step. step. step. ush.
    step.
    (* bnez a1 (=0) ; lbu a0=v17 ; seqz a0 ; addi a1,s8,-1 ; seqz a1 ; bne (Heq2) *)
    step. if_false. step. step. step. step. step.
    rewrite (F20.seqz_v17 v17 Rv17), (F20.seqz_vs8 tk Rtk).
    replace (0 =? 0) with true in Heq2 by reflexivity. cbv iota in Heq2.
    rewrite Heq2, bv_eqb_refl; cbn [negb]; cbv iota.
    apply FIN.
  - (* v16 <> 0 : beqz not taken, fall to 0x8247c *)
    rewrite (F20.eqb0_false v16) by lia. cbv iota.
    (* 0x8247c li a0,0 ; 0x82480 j 823f4 ; 0x824a0 addi a1,s8,-1 ; 0x824a4 seqz a1 ; 0x824a8 bne (Heq2) *)
    step. step. step. step. step.
    rewrite (F20.seqz_vs8 tk Rtk).
    replace (v16 =? 0) with false in Heq2 by (symmetry; apply Z.eqb_neq; exact Hv16). cbv iota in Heq2.
    rewrite <- Heq2, bv_eqb_refl; cbn [negb]; cbv iota.
    apply FIN.
Qed.

(* ---- THE PIN. The plain Lib.Exec.evt of the whole segment body 0x82418 -> 0x824b4 that `f20_head_F` and
   `F20F.f20_call_evt_F` re-derive together at ExecF.RNG_all. This is what F20.seg_F20 produces inline at
   F20.v:496-545 (its step script) and F20.v:455-472 (its CALL assert), with the register pins F20.v's
   subst_slot chain puts on the state. Proved exactly as F20F.f20_call_evt_of_F proves its own corollary
   (F20F.v:133-139): ExecF.evtF_evt of the composition, each `rng` premise by ExecF.rng_all. ---- *)
Lemma f20_of_head_call :
  forall (ra0 gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi A fr lo sp tk v14 v15 v16 v17 field16 : Z) (blk : list byte),
    0 <= sp < 2 ^ 64 ->
    0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    0 <= A -> A + 256 <= 2 ^ 64 -> 0 <= fr -> fr + 198 <= 2 ^ 64 -> 0 <= tk < 2 ^ 64 ->
    0 <= v14 < 256 -> 0 <= v15 < 256 -> 0 <= v16 < 256 -> 0 <= v17 < 256 ->
    field16 = v14 + 256 * v15 ->
    (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if tk =? 1 then 1 else 0) ->
    q64 m (A + 248) (fr + 176) ->
    u16 m (fr + 196) field16 ->
    b8 m (phi + 14) v14 -> b8 m (phi + 15) v15 -> b8 m (phi + 16) v16 -> b8 m (phi + 17) v17 ->
    b8 m (Z.shiftr (phi + 14) 3 + ASAN_K) 0 ->
    b8 m (Z.shiftr (phi + 15) 3 + ASAN_K) 0 ->
    b8 m (Z.shiftr (phi + 16) 3 + ASAN_K) 0 ->
    b8 m (Z.shiftr (phi + 17) 3 + ASAN_K) 0 ->
    length blk = 32%nat -> bytes_at rsegs m (phi + 18) blk ->
    stk rsegs m lo sp ->
    asan_cells m -> shadow_rw m -> addressable m (phi + 18) 32 ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (if blocksum blk =? 0 then 0 else -1)) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (phi + 18)) s5 (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 phi)
                       (Z_to_bv 64 tk) s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x824b4) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo sp)
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
               (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 (phi + 18)) s5 (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 phi)
               (Z_to_bv 64 tk) s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82418) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s9 s11 t3 t4 t5 t6 Fr fc m
    phi A fr lo sp tk v14 v15 v16 v17 field16 blk
    Rsp Hphi0 HpE Hpsp Hlo Hlo16 HA0 HA256 Hfr0 Hfr198 Rtk Rv14 Rv15 Rv16 Rv17 Heq1 Heq2
    Hq248 Hfield Hb14 Hb15 Hb16 Hb17 Hsh14 Hsh15 Hsh16 Hsh17
    Lblk Hblk Hstk HAC HSW Hadr.
  unfold APPMEM_END in HpE.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  eapply ExecF.evtF_cut.
  { apply (f20_head_F ExecF.RNG_all ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s5 s9 s11 t3 t4 t5 t6 Fr fc m phi A fr tk v14 v15 v16 v17 field16);
      try assumption; try lia; f20s_rng_all. }
  intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & a6' & E). subst ms'.
  apply (f20_call_evt_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0' a1' a2' a3' a4' a5' a6' a7
           s2 s3 (Z_to_bv 64 (phi + 18)) s5 (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 tk) s9
           (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6 Fr fc m phi A lo sp blk);
    try assumption; try lia; f20s_rng_all.
Qed.

(* ---- Route (C) twin of a Theorem Labs lane's F20F.f20_call_evt_F, WITHOUT its `shadow_rw m` premise (the Seg *F.v twin rule
   of a Theorem Labs lane 12:52Z: an F20F twin goes in this lane's existing beside-file; Seg/F20F.v is unchanged apart from comment text).
   BASE: f20_call_evt_F at a Theorem Labs lane's fold a working branch 4bae33fdf54, Seg/F20F.v blob
   4527ef54d8e (= a working branch 1899bed1aee's blob), lines 45-105, with exactly these changes: the premise `shadow_rw m` and
   its intro name HSW removed, and the call cut through the callee's narrowed footprint contract
   reac_ctrl_checksum_verify_contract_F_on (premise dropped; a Theorem Labs lane 9509908083d, LANDED.md (a working note, not in this delivery), 11:38Z) and its proof
   reac_ctrl_checksum_verify_F.reac_ctrl_checksum_verify_F_holds_on (a Theorem Labs lane 36bfd511da3, LANDED.md (a working note, not in this delivery), 11:12Z, a Theorem Labs lane
   SIGNED) instead of reac_ctrl_checksum_verify_F_holds.  REGION: none.  The two instructions (mv a0,s7; jal) touch no
   data, and the old proof passed HSW only to the callee, whose _F_on form has no shadow premise (it reads the 32
   record bytes' shadow from addressable).  a Theorem Labs lane's f20_call_evt_on (Seg/F20.v (a version not in this delivery; written on a working branch 4488b0c2fd2))
   is the plain Lib.Exec.evt form of the same stretch; the stage glue needs this footprint form. ---- *)
Module CKVFon := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_checksum_verify_F.

Lemma f20_call_evt_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi A lo sp : Z) (blk : list byte),
    0 <= sp < 2 ^ 64 ->
    0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    length blk = 32%nat -> bytes_at rsegs m (phi + 18) blk ->
    stk rsegs m lo sp ->
    asan_cells m -> addressable m (phi + 18) 32 ->
    ExecF.rng RNG (sp - 16) 16 ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (phi + 18) 32 ->
    ExecF.rng RNG ((phi + 18) / 8 + ASAN_K) ((phi + 49) / 8 - (phi + 18) / 8 + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (if blocksum blk =? 0 then 0 else -1)) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x824b4) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo sp)
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x824ac) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi A lo sp blk Rsp Hp0 HpE Hpsp Hlo Hlo16 Lblk Hblk Hstk HAC Hadr RFr RGOT RCK RDAT RSH.
  assert (Esp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  (* 0x824ac mv a0,s7 ; 0x824b0 jal reac_ctrl_checksum_verify *)
  step. step.
  eapply ExecF.evtF_cut.
  { eapply CKVFon.reac_ctrl_checksum_verify_F_holds_on with (p := phi) (lo := lo) (bs := blk);
      unfold REAC_CTRL_CHECKSUM_VERIFY_FRAME; rewrite ?Esp.
    - lia.
    - unfold APPMEM_END in HpE. lia.
    - reflexivity.
    - exact Lblk.
    - exact Hblk.
    - exact Hstk.
    - lia.
    - left. lia.
    - exact HAC.
    - exact Hadr.
    - outW. unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia.
    - exact RFr.
    - exact RGOT.
    - exact RCK.
    - exact RDAT.
    - exact RSH. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & _ & ST'). subst ms'.
  unfold REAC_CTRL_CHECKSUM_VERIFY_FRAME in MU, ST'. rewrite Esp in MU, ST'.
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.
  apply ExecF.evtF_done.
  do 7 eexists. exists m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

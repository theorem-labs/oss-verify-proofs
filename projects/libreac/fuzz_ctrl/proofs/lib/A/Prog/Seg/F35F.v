(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2962 of its 3089 lines of code are new or changed and 884 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F36.v, with its module names changed; 585 of its 687 lines of code are new or changed and 2987 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F35.v 17bd7a8f7c8f (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F35.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F35.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only.
   DEVIATION from the spec's "the _F takes the callee's _contract_F in the SAME position": the callee premise of
   f35_evt_F / f35_call_F is `bcmp_wrap_F_at RNG`, bcmp_wrap_c.v's bcmp_wrap_contract_F body at THIS footprint
   (bcmp_wrap_F_at_owner proves the two are the same text), appended last. That is strictly narrower than the
   forall-RNG contract, and the _of_F corollaries take Seg/F35.v's own plain HBC, so the pins below are plain. *)
(* The footprint (ExecF.evtF) twins of the two run lemmas of segment F35 of fuzz_ctrl LLVMFuzzerTestOneInput (asan
   build of image A, libreac v1.9.0): 0x82888-0x8289c, the bcmp wrapper call of the row_of_block loop, for the cut-free
   twin SegCF/F35.v, not in this delivery (RECIPE.md (a working note, not in this delivery): a hand re-walk with StepF).

   Each f35_<run>_F is Seg/F35.v's f35_<run> with the run an evtF under a footprint RNG.  F35's own instructions make
   no memory access: 0x82888 `beqz a0` is a branch, 0x8288c `li a2,32`, 0x82890 `mv a0,s6` and 0x82894 `mv a1,s9`
   are register moves, and 0x82898 `jal wrapper_bcmp` writes ra only.  So every rng premise below is the wrapper's,
   at the call 0x82898, as its footprint contract bcmp_wrap_F_at asks, with L = a0 = s6, R = a1 = s9 and
   N = a2 = 32:
   - rng_bytes RNG (the contract's route-1 weakening, lib/Lib/RngBytes.v);
   - rng RNG 0x10000 0x5ee000: the image (the wrapper's code and the runtime cells it reads);
   - rng RNG (sp - 4560) 4560: the wrapper's own stack window [sp - BCMP_WRAP_K, sp);
   - rng RNG L 32 and rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + 31) / 8) + 8 - 8 * (shadow_addr L / 8)):
     the 32 block bytes (phi + 18 at the segment's cut) and their aligned shadow words (the wrapper's range check
     loads whole aligned 8-byte shadow words);
   - rng RNG R 32 and the same shadow-word span at R: the 32-byte row slot (fr + 64 at the segment's cut).
   f35_evt_F is f35_evt (the run on a memory with mem_inv); f35_call_F is f35_call (the same run from a memory with
   ro_agree only, made on the normalized memory through MemNormF.evtF_normalize_ro, the evtF form of
   MemNorm.evt_normalize).  The mem_rel transports f35_call needs (f35_stk_rel, f35_srw_rel, f35_addr_rel,
   f35_cells_rel and their base f35_ro_lo / f35_ro_false) are copies of Seg/F35.v's, with the same text.
   f35_evt_of_F and f35_call_of_F re-derive Seg/F35.v's Exec.evt statements at RNG_all (ExecF.evtF_evt, every rng
   premise by rng_all) under Seg/F35.v's plain contract BW.bcmp_wrap_contract.  SegCF/F35.v checks, by conversion,
   that they prove Seg/F35.v's f35_evt and f35_call as stated there (f35_evt_mirror, f35_call_mirror), so this file
   stays a mirror of the halts segment: a change to either statement in Seg/F35.v breaks that check.

   v1.9 (libreac v1.9.0): every pc is the v1.8 one + 0xac (b8refit, map b8refit-v190.tsv (a working note, not in this delivery)), and the six runtime
   constants below are Seg/F35.v's v1.9 values (bcmp_wrap_c.v / memcmp_c.v, a Theorem Labs lane 3eade53eef2).  The image range
   [0x10000, 0x5ee000) of bcmp_wrap_contract_F and the read-only top 0x5fe000 are the same on v1.9.  No other line
   changes: F35's instructions and the wrapper's footprint are the same five instructions and the same ranges.

   The wrapper's footprint contract.  bcmp_wrap_c.v's bcmp_wrap_contract_F (the text Seg/F31F.v copies as
   BWF.bcmp_wrap_contract_F) quantifies over every footprint, so it does not follow from the plain contract, and
   Seg/F35.v's statements may not assume more than the plain one.  bcmp_wrap_F_at RNG is that contract's body at one
   footprint, read in bcmp_wrap_c.v's name environment (module F35BW); bcmp_wrap_F_at_owner proves by conversion that
   it is the owner's text, and bcmp_wrap_F_at_all proves it at RNG_all from the plain contract with
   ExecF_all.evt_evtF_all.  A caller at a smaller footprint (the twin) takes bcmp_wrap_F_at RNG from
   bcmp_wrap_c.v's bcmp_wrap_contract_F through bcmp_wrap_F_at_owner.

   rule 24: no function proved.  The only callee assumption is Seg/F35.v's own HBC (the plain contract, a Section
   Hypothesis of the two corollaries); no Axiom, no Parameter. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require memcmp_c bcmp_wrap_c.
(* For the _of_F_verbatim pins only (Require, not Import: F35.v's own helper copies must not shadow this file's). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F35.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* Loaded here, imported below after the mem_rel transports (which keep Seg/F35.v's name environment) and after the
   contract text: StepF's step / if_false and ExecF's evtF_done must be the last to match. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF StepF ExecF_all RngBytes.
Import ListNotations.
(* Seg/F35.v's alias of the image-A YK11. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module EFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF_all.

(* The owner's own constants, by name: Seg/F35.v states its runs with its Local Definition copies, so the _of_F
   corollaries must name THOSE constants for the constr_eq pins to hold (a same-valued copy here would be a
   different constant). Notation, not Definition: it expands to Seg/F35.v's constant at parse time. *)
Local Notation BCMP := F35.BCMP.
Local Notation REAL_BCMP := F35.REAL_BCMP.
Local Notation REAL_MEMCMP := F35.REAL_MEMCMP.
Local Notation GOT_CF := F35.GOT_CF.
Local Notation CF := F35.CF.
Local Notation MEMCMP := F35.MEMCMP.
Local Notation memcmp_model := SF.memcmp_model.

(* ---------------- the wrapper's run on the normalized memory ----------------
   The wrapper's contract asks mem_inv of the caller's memory; a cut carries only ro_agree (FRA, push 5b).  The
   run is made on the normalized memory (MemNorm.evt_normalize, as SlotInv.v says), and every premise and post
   fact moves across mem_rel: they read bytes through mrd (equal everywhere, mrd_rel) and the writability of bytes
   at or above GT = 0x5fe000 (no read-only byte is there, f35_ro_lo).  F36's bridge (a working branch). *)
Local Definition f35_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Local Lemma f35_rsegs_top : f35_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma f35_find_below : forall segs top x n s,
  f35_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold f35_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma f35_ro_lo : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < 0x5fe000.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (f35_find_below rsegs 0x5fe000 (bv_unsigned a) 1 s f35_rsegs_top E ltac:(lia)) as [L|L];
    [exact L | discriminate L].
Qed.

Lemma f35_ro_false : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [|reflexivity].
  pose proof (f35_ro_lo _ E) as L. rewrite wa_unsigned in L by lia. lia.
Qed.

Lemma f35_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi R Hlo.
  split; intros (H0 & H1 & H); (split; [exact H0|]); (split; [exact H1|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb);
    (assert (E : ro_addr rsegs (wa a) = false) by (apply f35_ro_false; lia)).
  - split; [rewrite (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite <- (mrd_rel rsegs m m0 _ R). exact Hb.
  - split; [rewrite <- (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite (mrd_rel rsegs m m0 _ R). exact Hb.
Qed.

Lemma f35_srw_rel : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 R. unfold shadow_rw.
  split; intros H a Ha; destruct (H a Ha) as (Hw & b & Hb);
    (assert (E : ro_addr rsegs (wa a) = false)
       by (apply f35_ro_false; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha;
           lia)).
  - split; [rewrite (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite <- (mrd_rel rsegs m m0 _ R). exact Hb.
  - split; [rewrite <- (wview_rel_rw rsegs m m0 _ R E); exact Hw|].
    exists b. rewrite (mrd_rel rsegs m m0 _ R). exact Hb.
Qed.

Lemma f35_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n R.
  assert (MR : forall a, mrd rsegs m a = mrd rsegs m0 a) by (intros a; exact (mrd_rel rsegs m m0 a R)).
  unfold addressable, addr_byte. setoid_rewrite MR. reflexivity.
Qed.

Lemma f35_cells_rel : forall m m0, mem_rel rsegs m m0 -> (asan_cells m <-> asan_cells m0).
Proof.
  intros m m0 R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs m0 a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m m0 a bs R)).
  unfold asan_cells. setoid_rewrite BR. reflexivity.
Qed.

(* ---------------- the bcmp wrapper's footprint contract at one footprint ----------------
   The body of bcmp_wrap_c.v's bcmp_wrap_contract_F for one RNG, read in bcmp_wrap_c.v's name environment (its
   imports, then its own definitions, then RngBytes and ExecF), so the names are bcmp_wrap_c's (BCMP_WRAP_K,
   BCMP_WRAP, REAL_BCMP, ...), memcmp_c's MEMCMP and StrFun's memcmp_model, as in Seg/F31F.v's BWF. *)
Module F35BW.
Import ListNotations.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
  LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State
  LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Arr
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Bytes.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
(* Z_scope, as in Seg/F31F.v's BWF: the elaborated term is bcmp_wrap_c.v's (its bv_scope captures no literal of
   this text). *)
Open Scope Z_scope.

Definition bcmp_wrap_F_at (RNG : footprint) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  let L := bv_unsigned a0 in let R := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m L ls ->
  bytes_at rsegs m R rs ->
  memcmp_model ls rs (Z.to_nat N) = Some v ->
  mem_inv rsegs m ->
  (N <= 2^40)%Z -> addressable m L N -> addressable m R N -> end_in_app L N -> end_in_app R N ->
  (N = 0 \/ app_mem (L + 7))%Z -> (N = 0 \/ app_mem (R + 7))%Z ->
  (L + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L)%Z ->
  (R + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + BCMP_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw m ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  rng_bytes RNG ->
  rng RNG 0x10000 0x5ee000 ->
  rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
  rng RNG L N -> (N = 0 \/ rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + N - 1) / 8) + 8 - 8 * (shadow_addr L / 8))) ->
  rng RNG R N -> (N = 0 \/ rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + N - 1) / 8) + 8 - 8 * (shadow_addr R / 8))) ->
  evtF rsegs RNG (bcmp_wrap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs)).

(* It is the owner's text: bcmp_wrap_c.v's bcmp_wrap_contract_F is bcmp_wrap_F_at at every footprint, by
   conversion. *)
Lemma bcmp_wrap_F_at_owner : bcmp_wrap_contract_F <-> forall RNG, bcmp_wrap_F_at RNG.
Proof. split; intros H RNG; exact (H RNG). Qed.
End F35BW.

Notation bcmp_wrap_F_at := F35BW.bcmp_wrap_F_at.

(* Last: StepF's step / if_false and ExecF's evtF_done / evtF_cut / evtF_mono match evtF goals and shadow Step's and
   Exec's evt ones; then the image-A YK11 again (Seg/X12F.v's pilot fix 4), and Z_scope on top (ExecF / StepF
   re-open bv_scope on Import). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Import AYK.
Open Scope Z_scope.

(* At RNG_all the footprint contract is the plain one: every Exec run is an ExecF run under RNG_all. *)
Lemma bcmp_wrap_F_at_all : BW.bcmp_wrap_contract -> bcmp_wrap_F_at RNG_all.
Proof.
  unfold BW.bcmp_wrap_contract, F35BW.bcmp_wrap_F_at. cbv zeta. intros HBC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v lo
    BL BR HM HMI HN ADL ADR EL ER AL AR SL SR HST HK HLO HSP HC HSR HRB HRM HGCF HCF1 HCF2 _ _ _ _ _ _ _.
  apply EFA.evt_evtF_all.
  exact (HBC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs
           v lo BL BR HM HMI HN ADL ADR EL ER AL AR SL SR HST HK HLO HSP HC HSR HRB HRM HGCF HCF1 HCF2).
Qed.

(* The contract's shadow-word span at P with N = 32 (written P + 32 - 1 there) from the run's premise at P + 31. *)
Local Ltac f35_shadow_rng H :=
  first [ exact H
        | eapply rng_sub; [exact H | |]; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia ].

(* ===================== the machine runs ===================== *)

(* 0x82888 with a0 = 1: beqz is not taken; the three argument instructions, then the bcmp wrapper on the 32 bytes
   at L = phi + 18 and R = fr + 64.  No instruction of F35 touches memory; the rng premises are the wrapper's
   footprint at 0x82898 (bcmp_wrap_F_at). *)
Lemma f35_evt_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (L R : Z) (ls rs : list byte) (v lo : Z),
    a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 L -> s9 = Z_to_bv 64 R ->
    0 <= L -> L + 32 < 2 ^ 64 -> 0 <= R -> R + 32 < 2 ^ 64 ->
    bytes_at rsegs m L ls -> bytes_at rsegs m R rs ->
    memcmp_model ls rs 32 = Some v ->
    mem_inv rsegs m -> addressable m L 32 -> addressable m R 32 ->
    app_mem (L + 32) -> app_mem (R + 32) -> app_mem (L + 7) -> app_mem (R + 7) ->
    (L + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BW.BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* the bcmp wrapper's footprint at 0x82898: the image, its stack window, the 32 bytes at L and at R, and the
       aligned shadow words of each *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - BW.BCMP_WRAP_K) BW.BCMP_WRAP_K ->
    rng RNG L 32 ->
    rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + 31) / 8) + 8 - 8 * (shadow_addr L / 8)) ->
    rng RNG R 32 ->
    rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + 31) / 8) + 8 - 8 * (shadow_addr R / 8)) ->
    bcmp_wrap_F_at RNG ->
    evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8289c) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BW.BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82888) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m L R ls rs v lo -> -> -> HL0 HL1 HR0 HR1 HBL HBR Hmm HMI HADL HADR
    HaL32 HaR32 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255
    Hrb RIMG RSTK RL RLs RR RRs HF.
  (* 0x82888 beqz a0 (a0 = 1): not taken *)
  step. try if_false.
  (* 0x8288c li a2,32; 0x82890 mv a0,s6; 0x82894 mv a1,s9; 0x82898 jal wrapper_bcmp *)
  step. step. step. step.
  pose proof HF as HB. unfold F35BW.bcmp_wrap_F_at in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 32) = 32) by (apply unsigned_lit; lia).
  assert (EL0 : bv_unsigned (Z_to_bv 64 (L + 0)) = L) by (rewrite Z.add_0_r; apply unsigned_lit; lia).
  assert (ER0 : bv_unsigned (Z_to_bv 64 (R + 0)) = R) by (rewrite Z.add_0_r; apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HB with (ls := ls) (rs := rs) (v := v) (lo := lo).
    all: rewrite ?EL, ?ER, ?E32, ?EL0, ?ER0.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 32) with 32%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL32.
    - right; exact HaR32.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255.
    - exact Hrb.
    - exact RIMG.
    - exact RSTK.
    - exact RL.
    - right; f35_shadow_rng RLs.
    - exact RR.
    - right; f35_shadow_rng RRs. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & _ & _).
  subst ms'.
  match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] =>
      replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity])
  end.
  apply evtF_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* The wrapper's run from a memory that agrees with the image on its read-only bytes (a cut carries ro_agree, not
   mem_inv): f35_evt_F run on the normalized memory (MemNormF.evtF_normalize_ro keeps RNG), with every premise and
   post fact moved across mem_rel (F36's f36_call_norm).  The rng premises are f35_evt_F's: the normalized memory
   changes no address. *)
Lemma f35_call_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (L R : Z) (ls rs : list byte) (v lo : Z),
    a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 L -> s9 = Z_to_bv 64 R ->
    0 <= L -> L + 32 < 2 ^ 64 -> 0 <= R -> R + 32 < 2 ^ 64 ->
    bytes_at rsegs m L ls -> bytes_at rsegs m R rs ->
    memcmp_model ls rs 32 = Some v ->
    ro_agree rsegs m -> addressable m L 32 -> addressable m R 32 ->
    app_mem (L + 32) -> app_mem (R + 32) -> app_mem (L + 7) -> app_mem (R + 7) ->
    (L + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BW.BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* the bcmp wrapper's footprint at 0x82898, as in f35_evt_F *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - BW.BCMP_WRAP_K) BW.BCMP_WRAP_K ->
    rng RNG L 32 ->
    rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + 31) / 8) + 8 - 8 * (shadow_addr L / 8)) ->
    rng RNG R 32 ->
    rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + 31) / 8) + 8 - 8 * (shadow_addr R / 8)) ->
    bcmp_wrap_F_at RNG ->
    evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8289c) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BW.BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82888) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m L R ls rs v lo E0 E6 E9 HL0 HL1 HR0 HR1 HBL HBR Hmm HRO HADL HADR
    HaL32 HaR32 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255
    Hrb RIMG RSTK RL RLs RR RRs HF.
  pose proof (mem_rel_normalize rsegs m HRO) as Rn.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m (normalize rsegs m) a bs Rn)).
  assert (Hlo : 0x5fe000 <= lo) by (unfold HIGHMEM_BEG in Hlo2; lia).
  eapply evtF_mono.
  { eapply (MNF.evtF_normalize_ro RNG _ _ Fr _ fc None m (seg_rom rsegs) HRO).
    apply (f35_evt_F RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             Fr fc (normalize rsegs m) L R ls rs v lo E0 E6 E9 HL0 HL1 HR0 HR1).
    - apply BR. exact HBL.
    - apply BR. exact HBR.
    - exact Hmm.
    - exact (mem_inv_normalize rsegs m).
    - apply (proj1 (f35_addr_rel m _ _ _ Rn)). exact HADL.
    - apply (proj1 (f35_addr_rel m _ _ _ Rn)). exact HADR.
    - exact HaL32.
    - exact HaR32.
    - exact HaL7.
    - exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - apply (proj1 (f35_stk_rel m _ _ _ Rn Hlo)). exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - apply (proj1 (f35_cells_rel m _ Rn)). exact HAC.
    - apply (proj1 (f35_srw_rel m _ Rn)). exact HSW.
    - apply BR. exact HRB.
    - apply BR. exact HRM.
    - apply BR. exact HGC.
    - apply BR. exact HC254.
    - apply BR. exact HC255.
    - exact Hrb.
    - exact RIMG.
    - exact RSTK.
    - exact RL.
    - exact RLs.
    - exact RR.
    - exact RRs.
    - exact HF. }
  intros s (s0' & HQ & REL & SAME).
  destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0' &
                  E & MU & WM & _ & ST & _ & _).
  subst s0'.
  destruct s as [R' F' pc' sv' rv' fc' m' ro'].
  unfold ms_rel, MS in REL.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in REL, SAME.
  destruct REL as (ER & EF & Epc & Esv & Erv & Efc & Erom & RM).
  subst R' F' pc' sv' rv' fc' ro'.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m' m0' Rn RM SAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m' m0' Rn RM SAME WM)|].
  split; [exact (ro_agree_same rsegs m m' HRO SAME)|].
  apply (proj2 (f35_stk_rel m' m0' _ _ RM Hlo)). exact ST.
Qed.

(* ===================== Seg/F35.v's statements, at RNG_all ===================== *)

Section F35F.
(* Seg/F35.v's Section Hypothesis HBC (the plain contract): the corollaries take the footprint contract at RNG_all
   from it (bcmp_wrap_F_at_all). *)
Hypothesis HBC : BW.bcmp_wrap_contract.

(* Seg/F35.v's f35_evt statement: f35_evt_F at RNG_all. *)
Lemma f35_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (L R : Z) (ls rs : list byte) (v lo : Z),
    a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 L -> s9 = Z_to_bv 64 R ->
    0 <= L -> L + 32 < 2 ^ 64 -> 0 <= R -> R + 32 < 2 ^ 64 ->
    bytes_at rsegs m L ls -> bytes_at rsegs m R rs ->
    memcmp_model ls rs 32 = Some v ->
    mem_inv rsegs m -> addressable m L 32 -> addressable m R 32 ->
    app_mem (L + 32) -> app_mem (R + 32) -> app_mem (L + 7) -> app_mem (R + 7) ->
    (L + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BW.BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8289c) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BW.BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82888) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m L R ls rs v lo E0 E6 E9 HL0 HL1 HR0 HR1 HBL HBR Hmm HMI HADL HADR
    HaL32 HaR32 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  apply (evtF_evt rsegs RNG_all).
  apply (f35_evt_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           Fr fc m L R ls rs v lo); try assumption;
    first [ exact (bcmp_wrap_F_at_all HBC) | intros ? ? ? ? ?; exact I | apply rng_all ];
    unfold HIGHMEM_BEG, APPMEM_END, BW.BCMP_WRAP_K, shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia.
Qed.

(* Seg/F35.v's f35_call statement: f35_call_F at RNG_all. *)
Lemma f35_call_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (L R : Z) (ls rs : list byte) (v lo : Z),
    a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 L -> s9 = Z_to_bv 64 R ->
    0 <= L -> L + 32 < 2 ^ 64 -> 0 <= R -> R + 32 < 2 ^ 64 ->
    bytes_at rsegs m L ls -> bytes_at rsegs m R rs ->
    memcmp_model ls rs 32 = Some v ->
    ro_agree rsegs m -> addressable m L 32 -> addressable m R 32 ->
    app_mem (L + 32) -> app_mem (R + 32) -> app_mem (L + 7) -> app_mem (R + 7) ->
    (L + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BW.BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8289c) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BW.BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82888) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m L R ls rs v lo E0 E6 E9 HL0 HL1 HR0 HR1 HBL HBR Hmm HRO HADL HADR
    HaL32 HaR32 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  apply (evtF_evt rsegs RNG_all).
  apply (f35_call_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           Fr fc m L R ls rs v lo); try assumption;
    first [ exact (bcmp_wrap_F_at_all HBC) | intros ? ? ? ? ?; exact I | apply rng_all ];
    unfold HIGHMEM_BEG, APPMEM_END, BW.BCMP_WRAP_K, shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia.
Qed.

End F35F.

(* The pins: each *_of_F states Seg/F35.v's v1.9 text, term for term (constr_eq: syntactic, not up to conversion).
   Both are stated under Seg/F35.v's own Section Hypothesis HBC, so the discharged premise is the same one. *)
Lemma f35_evt_of_F_verbatim : True.
Proof.
  let a := type of F35.f35_evt in let b := type of f35_evt_of_F in constr_eq a b.
  exact I.
Qed.

Lemma f35_call_of_F_verbatim : True.
Proof.
  let a := type of F35.f35_call in let b := type of f35_call_of_F in constr_eq a b.
  exact I.
Qed.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)

(* ===================== route (C): the `_on` twins (a Theorem Labs lane 09:20Z; wave a Theorem Labs lane, frozen form 09:38Z) =====================
   Writer a Theorem Labs lane (a Theorem Labs lane's hand-off 12:54Z, ASSIGN.md (a working note, not in this delivery)). ADDITIVE: every line above is unchanged, and every old
   lemma keeps its statement and its own proof. rule 24: no function proved. f35_evt_F_on / f35_call_F_on are
   f35_evt_F / f35_call_F's own proofs re-run under a narrowed shadow premise, against a Theorem Labs lane's narrowed footprint
   contract (bcmp_wrap_c_on.v's bcmp_wrap_contract_F_on, read at one footprint as bcmp_wrap_F_at_on, the twin of
   bcmp_wrap_F_at; bcmp_wrap_F_at_on_owner proves by conversion that it is the owner's text).
   PRE shadow_rw m -> A.ShadowRwOn.shadow_rw_on (f35_evt_F_shadow_R L R) m. F35's five instructions make no memory
   access, so the run reads and stores no shadow byte of its own; the wrapper's range checks at the call 0x82898
   (a0 = L, a1 = R, a2 = 32) read the aligned shadow words of its two strings, the callee's own region
   bcmp_wrap_shadow_R L R 32, and the wrapper stores no shadow byte (bcmp_wrap_post_on keeps every region).
   POST (f35_evt_F_on) shadow_rw m' -> forall P, shadow_rw_on P m -> shadow_rw_on P m'. f35_call_F_on moves the
   region across mem_rel by ShadowRwOnT.shadow_rw_on_rel, in place of this file's whole-shadow f35_srw_rel; its post
   has no shadow fact. f35_evt_of_F / f35_call_of_F get no twin: their only users are the constr_eq pins above
   (a Theorem Labs lane 11:53Z: a pin is not a user). *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT.
Module BWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c_on.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module SROT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.

(* The body of bcmp_wrap_c_on.v's bcmp_wrap_contract_F_on for one RNG: F35BW's text with the leaf's narrowed shadow
   premise and its post, read in the leaf's name environment. *)
Module F35BWO.
Import ListNotations.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
  LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State
  LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Arr
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Bytes.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c_on.
Open Scope Z_scope.

Definition bcmp_wrap_F_at_on (RNG : footprint) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  let L := bv_unsigned a0 in let R := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m L ls ->
  bytes_at rsegs m R rs ->
  memcmp_model ls rs (Z.to_nat N) = Some v ->
  mem_inv rsegs m ->
  (N <= 2^40)%Z -> addressable m L N -> addressable m R N -> end_in_app L N -> end_in_app R N ->
  (N = 0 \/ app_mem (L + 7))%Z -> (N = 0 \/ app_mem (R + 7))%Z ->
  (L + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L)%Z ->
  (R + N <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + BCMP_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw_on (bcmp_wrap_shadow_R L R N) m ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  rng_bytes RNG ->
  rng RNG 0x10000 0x5ee000 ->
  rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
  rng RNG L N -> (N = 0 \/ rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + N - 1) / 8) + 8 - 8 * (shadow_addr L / 8))) ->
  rng RNG R N -> (N = 0 \/ rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + N - 1) / 8) + 8 - 8 * (shadow_addr R / 8))) ->
  evtF rsegs RNG (bcmp_wrap_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs)).

(* It is the owner's text: bcmp_wrap_c_on.v's bcmp_wrap_contract_F_on is bcmp_wrap_F_at_on at every footprint, by
   conversion. *)
Lemma bcmp_wrap_F_at_on_owner : bcmp_wrap_contract_F_on <-> forall RNG, bcmp_wrap_F_at_on RNG.
Proof. split; intros H RNG; exact (H RNG). Qed.
End F35BWO.

Notation bcmp_wrap_F_at_on := F35BWO.bcmp_wrap_F_at_on.

(* The shadow bytes the run needs present through its premise: the wrapper's region at 0x82898 (L, R, N = 32). *)
Definition f35_evt_F_shadow_R (L R : Z) : Z -> Prop := BWO.bcmp_wrap_shadow_R L R 32.

(* f35_call_F's run is f35_evt_F's on the normalized memory; mem_rel moves the region's bytes unchanged. *)
Definition f35_call_F_shadow_R (L R : Z) : Z -> Prop := f35_evt_F_shadow_R L R.

(* f35_evt_F under the narrowed premise, against the narrowed footprint contract. *)
Lemma f35_evt_F_on :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (L R : Z) (ls rs : list byte) (v lo : Z),
    a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 L -> s9 = Z_to_bv 64 R ->
    0 <= L -> L + 32 < 2 ^ 64 -> 0 <= R -> R + 32 < 2 ^ 64 ->
    bytes_at rsegs m L ls -> bytes_at rsegs m R rs ->
    memcmp_model ls rs 32 = Some v ->
    mem_inv rsegs m -> addressable m L 32 -> addressable m R 32 ->
    app_mem (L + 32) -> app_mem (R + 32) -> app_mem (L + 7) -> app_mem (R + 7) ->
    (L + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BW.BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> SRO.shadow_rw_on (f35_evt_F_shadow_R L R) m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* the bcmp wrapper's footprint at 0x82898, as in f35_evt_F *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - BW.BCMP_WRAP_K) BW.BCMP_WRAP_K ->
    rng RNG L 32 ->
    rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + 31) / 8) + 8 - 8 * (shadow_addr L / 8)) ->
    rng RNG R 32 ->
    rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + 31) / 8) + 8 - 8 * (shadow_addr R / 8)) ->
    bcmp_wrap_F_at_on RNG ->
    evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8289c) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BW.BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ (forall P, SRO.shadow_rw_on P m -> SRO.shadow_rw_on P m'))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82888) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m L R ls rs v lo -> -> -> HL0 HL1 HR0 HR1 HBL HBR Hmm HMI HADL HADR
    HaL32 HaR32 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255
    Hrb RIMG RSTK RL RLs RR RRs HF.
  (* 0x82888 beqz a0 (a0 = 1): not taken *)
  step. try if_false.
  (* 0x8288c li a2,32; 0x82890 mv a0,s6; 0x82894 mv a1,s9; 0x82898 jal wrapper_bcmp *)
  step. step. step. step.
  pose proof HF as HB. unfold F35BWO.bcmp_wrap_F_at_on in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 32) = 32) by (apply unsigned_lit; lia).
  assert (EL0 : bv_unsigned (Z_to_bv 64 (L + 0)) = L) by (rewrite Z.add_0_r; apply unsigned_lit; lia).
  assert (ER0 : bv_unsigned (Z_to_bv 64 (R + 0)) = R) by (rewrite Z.add_0_r; apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HB with (ls := ls) (rs := rs) (v := v) (lo := lo).
    all: rewrite ?EL, ?ER, ?E32, ?EL0, ?ER0.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 32) with 32%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL32.
    - right; exact HaR32.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255.
    - exact Hrb.
    - exact RIMG.
    - exact RSTK.
    - exact RL.
    - right; f35_shadow_rng RLs.
    - exact RR.
    - right; f35_shadow_rng RRs. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & _ & _).
  subst ms'.
  match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] =>
      replace (ret_pc (Z_to_bv 64 z)) with (Z_to_bv 64 z) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity])
  end.
  apply evtF_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* f35_call_F under the narrowed premise: f35_evt_F_on on the normalized memory, the region moved across mem_rel by
   ShadowRwOnT.shadow_rw_on_rel (in place of f35_srw_rel). *)
Lemma f35_call_F_on :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (L R : Z) (ls rs : list byte) (v lo : Z),
    a0 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 L -> s9 = Z_to_bv 64 R ->
    0 <= L -> L + 32 < 2 ^ 64 -> 0 <= R -> R + 32 < 2 ^ 64 ->
    bytes_at rsegs m L ls -> bytes_at rsegs m R rs ->
    memcmp_model ls rs 32 = Some v ->
    ro_agree rsegs m -> addressable m L 32 -> addressable m R 32 ->
    app_mem (L + 32) -> app_mem (R + 32) -> app_mem (L + 7) -> app_mem (R + 7) ->
    (L + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 32 <= bv_unsigned sp - BW.BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BW.BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> SRO.shadow_rw_on (f35_call_F_shadow_R L R) m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* the bcmp wrapper's footprint at 0x82898, as in f35_evt_F *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - BW.BCMP_WRAP_K) BW.BCMP_WRAP_K ->
    rng RNG L 32 ->
    rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + 31) / 8) + 8 - 8 * (shadow_addr L / 8)) ->
    rng RNG R 32 ->
    rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + 31) / 8) + 8 - 8 * (shadow_addr R / 8)) ->
    bcmp_wrap_F_at_on RNG ->
    evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8289c) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BW.BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82888) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m L R ls rs v lo E0 E6 E9 HL0 HL1 HR0 HR1 HBL HBR Hmm HRO HADL HADR
    HaL32 HaR32 HaL7 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255
    Hrb RIMG RSTK RL RLs RR RRs HF.
  pose proof (mem_rel_normalize rsegs m HRO) as Rn.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m (normalize rsegs m) a bs Rn)).
  assert (Hlo : 0x5fe000 <= lo) by (unfold HIGHMEM_BEG in Hlo2; lia).
  eapply evtF_mono.
  { eapply (MNF.evtF_normalize_ro RNG _ _ Fr _ fc None m (seg_rom rsegs) HRO).
    apply (f35_evt_F_on RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             Fr fc (normalize rsegs m) L R ls rs v lo E0 E6 E9 HL0 HL1 HR0 HR1).
    - apply BR. exact HBL.
    - apply BR. exact HBR.
    - exact Hmm.
    - exact (mem_inv_normalize rsegs m).
    - apply (proj1 (f35_addr_rel m _ _ _ Rn)). exact HADL.
    - apply (proj1 (f35_addr_rel m _ _ _ Rn)). exact HADR.
    - exact HaL32.
    - exact HaR32.
    - exact HaL7.
    - exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - apply (proj1 (f35_stk_rel m _ _ _ Rn Hlo)). exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - apply (proj1 (f35_cells_rel m _ Rn)). exact HAC.
    - exact (SROT.shadow_rw_on_rel _ m _ Rn HSW).
    - apply BR. exact HRB.
    - apply BR. exact HRM.
    - apply BR. exact HGC.
    - apply BR. exact HC254.
    - apply BR. exact HC255.
    - exact Hrb.
    - exact RIMG.
    - exact RSTK.
    - exact RL.
    - exact RLs.
    - exact RR.
    - exact RRs.
    - exact HF. }
  intros s (s0' & HQ & REL & SAME).
  destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0' &
                  E & MU & WM & _ & ST & _ & _).
  subst s0'.
  destruct s as [R' F' pc' sv' rv' fc' m' ro'].
  unfold ms_rel, MS in REL.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in REL, SAME.
  destruct REL as (ER & EF & Epc & Esv & Erv & Efc & Erom & RM).
  subst R' F' pc' sv' rv' fc' ro'.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m' m0' Rn RM SAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m' m0' Rn RM SAME WM)|].
  split; [exact (ro_agree_same rsegs m m' HRO SAME)|].
  apply (proj2 (f35_stk_rel m' m0' _ _ RM Hlo)). exact ST.
Qed.

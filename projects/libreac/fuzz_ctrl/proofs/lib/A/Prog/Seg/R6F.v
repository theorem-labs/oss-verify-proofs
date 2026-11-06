(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v; 180 of its 324 lines of code are new or changed and 1653 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R6.v 46f7b58814c2 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: r6_evt_of_F re-derives R6.r6_evt at ExecF.RNG_all; r6_evt_of_F_verbatim checks by constr_eq that its
   type is the type of R6.r6_evt after R6.r6_evt's own first premise (the plain callee contract).
   Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) twin of the one run lemma of Seg/R6.v (r6_evt :69; the segment-runs-A.tsv row S_R6 is marked
   "no stated run lemma in Appendix A", and this is the run the file holds): the same run (the four argument spill
   loads at [A + 112], [A + 168], [A + 104], [A + 96], mv a2,s7, the two li and the call of reac_ctrl_build_as at
   0x815e8), with the same post-state predicate, re-stepped with lib.Lib StepF as an ExecF.evtF under a universally
   quantified footprint RNG. The segment's own accesses are the four 8-byte spill loads, so it carries four plain
   rng premises; every other region is the callee's and is passed through its footprint contract
   reac_ctrl_build_as_contract_F (lib/A/Prog/reac_ctrl_build_as_c.v:135) in the SAME position where R6.r6_evt takes
   the plain reac_ctrl_build_as_contract (the signed form of that contract, a Theorem Labs lane e25b8b0aa71, auditor
   a Theorem Labs lane). One of its footprint premises is a forall-memory form (rng_bytes RNG) and one is the thread-cell
   premise over THIS run's memory m, quantified over DT TS C T DB kk: both are
   passed through UNCHANGED, as the spec's callee rule says. R6.v itself is unchanged apart from comment text. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcPorts RcBox RcSynth RcSynthLib RcLay
  RcFin RcFinLib RcEmit RcEmitLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_build_as_c reac_box_model_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
(* The segment file itself. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R6.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals); rng_bytes is a lib.Lib leaf over ExecF. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* ---- r6_evt (R6.v:69) in footprint form. The segment's own regions (choice (a): the regions its own premises
   name) are the four 8-byte spill cells the four ld instructions read:
     rng RNG (A + 96) 8    0x815dc ld a5,96(s1)    the count word 0x1234
     rng RNG (A + 104) 8   0x815d8 ld a4,104(s1)   round_trip.box 0x21140
     rng RNG (A + 112) 8   0x815cc ld a1,112(s1)   the catalogue row md
     rng RNG (A + 168) 8   0x815d4 ld a3,168(s1)   our[] = d
   The remaining premises are reac_ctrl_build_as_contract_F's own, at this call's arguments (Lo = spv - K, S = spv,
   md = mdv, b = bb, d = d, s = 0x21140, o = o, FS = FS). ---- *)
Lemma r6_evt_F : BA.reac_ctrl_build_as_contract_F ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A spv TPv o mdv bb d FS n len Rv : Z) (Eb : bool) (mb nb db sb junk : list byte),
    n = bm_uw mdv (firstn 8 (skipn 16 mb)) ->
    len = 52 + 36 * n ->
    Eb = PB.ba_E n mb bb ->
    Rv = (if PB.ba_go o mdv bb && Eb then len else 0) ->
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 spv -> tp = Z_to_bv 64 TPv -> s7 = Z_to_bv 64 bb ->
    a0 = Z_to_bv 64 o ->
    0 <= A -> A + 176 <= 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= mdv < 2 ^ 64 -> 0 <= bb <= 6 ->
    0 <= d < 2 ^ 64 -> 0 <= TPv < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 0x1234)) ->
    bytes_at rsegs m (A + 104) (le8 (Z_to_bv 64 0x21140)) ->
    bytes_at rsegs m (A + 112) (le8 (Z_to_bv 64 mdv)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 d)) ->
    spv mod 16 = 0 ->
    stk rsegs m (spv - BA.REAC_CTRL_BUILD_AS_K) spv ->
    bytes_at rsegs m (BA.BA_FR + 72) PB.ba_tbl ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv (BA.BA_FR + 72) (BA.BA_FR + 240) ->
    length db = 6%nat -> bytes_at rsegs m d db ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv d (d + 6) ->
    length sb = 6%nat -> bytes_at rsegs m 0x21140 sb ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv 0x21140 (0x21140 + 6) ->
    (mdv <> 0 -> mdv mod 8 = 0 /\ mdv + 296 <= 2 ^ 64 /\ length mb = 296%nat /\ bytes_at rsegs m mdv mb /\
                 ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv mdv (mdv + 296)) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       name_ok nb /\ bytes_at rsegs m (rname mb) nb /\
       ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (o <> 0 -> o + 1492 <= 2 ^ 64) ->
    (PB.ba_go o mdv bb && Eb = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\
       ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv o (o + len) /\
       ly_dj o (o + len) (BA.BA_FR + 72) (BA.BA_FR + 240) /\ ly_dj o (o + len) mdv (mdv + 296) /\
       (((bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0) ->
          ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) 0x21140 (0x21140 + 6)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= spv - BA.REAC_CTRL_BUILD_AS_K -> spv <= APPMEM_END ->
    addressable m (spv - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K ->
    addressable m BA.BA_SW 56 -> addressable m (BA.BA_FR + 72) 168 -> addressable m d 6 ->
    addressable m 0x21140 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (0x21140 + 6) /\ app_mem (0x21140 + 7) ->
    (mdv <> 0 -> addressable m mdv 296) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       addressable m (rname mb) (Z.of_nat (length nb))) ->
    (PB.ba_go o mdv bb && Eb = true ->
       addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (bb = 1 -> addressable m RBM.JOIN_0014 32) ->
    (bb = 2 -> addressable m RBM.JOIN_0013 32) ->
    fp [0%nat; 1%nat] m TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv
      [(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)]
      [(BA.BA_FR + 72, BA.BA_FR + 240); (mdv, mdv + 296); (d, d + 6); (0x21140, 0x21140 + 6); (o, o + Rv)] ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    BA.reac_ctrl_build_as_tls m TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv ->
    (* footprint: the segment's own four spill loads, then the callee's regions *)
    ExecF.rng RNG (A + 96) 8 ->
    ExecF.rng RNG (A + 104) 8 ->
    ExecF.rng RNG (A + 112) 8 ->
    ExecF.rng RNG (A + 168) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG 0x7fffa000 0xbdc00 ->
    ExecF.rng RNG (spv - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K ->
    ExecF.rng RNG (shadow_addr (spv - BA.REAC_CTRL_BUILD_AS_K) / 8 * 8)
      (shadow_addr (spv - 1) / 8 * 8 + 8 - shadow_addr (spv - BA.REAC_CTRL_BUILD_AS_K) / 8 * 8) ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG FS FS_SIZE ->
    ExecF.rng RNG (shadow_addr FS / 8 * 8)
      (shadow_addr (FS + FS_SIZE - 1) / 8 * 8 + 8 - shadow_addr FS / 8 * 8) ->
    (forall (DT TS C T DB : word) (kk : Z),
       asan_tls_cells m TPv DT TS C T DB kk ->
       Forall (fun r => ExecF.rng RNG (fst r) (snd r - fst r)) (fp_tls TPv DT TS C T DB kk)) ->
    (mdv <> 0 -> ExecF.rng RNG mdv 296 /\
       ExecF.rng RNG (shadow_addr mdv / 8 * 8) (shadow_addr (mdv + 295) / 8 * 8 + 8 - shadow_addr mdv / 8 * 8)) ->
    ExecF.rng RNG d 6 ->
    ExecF.rng RNG (shadow_addr d / 8 * 8) (shadow_addr (d + 5) / 8 * 8 + 8 - shadow_addr d / 8 * 8) ->
    ExecF.rng RNG 0x21140 6 ->
    ExecF.rng RNG (shadow_addr 0x21140 / 8 * 8)
      (shadow_addr (0x21140 + 5) / 8 * 8 + 8 - shadow_addr 0x21140 / 8 * 8) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       ExecF.rng RNG (rname mb) (Z.of_nat (length nb)) /\
       ExecF.rng RNG (shadow_addr (rname mb) / 8 * 8)
         (shadow_addr (rname mb + Z.of_nat (length nb) - 1) / 8 * 8 + 8 - shadow_addr (rname mb) / 8 * 8)) ->
    (PB.ba_go o mdv bb && Eb = true -> ExecF.rng RNG o len /\
       ExecF.rng RNG (shadow_addr o / 8 * 8) (shadow_addr (o + len - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x815ec) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Rv)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x815ec) fc None m' (seg_rom rsegs)
         /\ munch ([(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)] ++ fp_w [0%nat; 1%nat] FS ++
                   [(shadow_addr (spv - BA.REAC_CTRL_BUILD_AS_K), shadow_addr spv)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (spv - BA.REAC_CTRL_BUILD_AS_K) spv
         /\ asan_cells m' /\ shadow_rw m'
         /\ addressable m' (spv - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K
         /\ fp [0%nat; 1%nat] m' TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv
              [(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)]
              [(BA.BA_FR + 72, BA.BA_FR + 240); (mdv, mdv + 296); (d, d + 6); (0x21140, 0x21140 + 6); (o, o + Rv)]
         /\ (forall x, o <= x < o + Rv -> exists bx, mrd rsegs m' (wa x) = Some bx)
         /\ (PB.ba_go o mdv bb && Eb = true ->
               bytes_at rsegs m' o (em_fr db sb 0x1234 (Z_to_bv 8 205) (Z_to_bv 8 234) (PB.ba_X mdv mb nb bb) len)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815cc) fc None m (seg_rom rsegs)).
Proof.
  intros BUILD_F RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A spv TPv o mdv bb d FS n len Rv Eb mb nb db sb junk
    Hn Hlen HEb HRv -> -> -> -> -> HA0 HA1 Ho Hmd Hbb Hd HTP Hspv C96 C104 C112 C168
    H16 ST HBA HBAdj Hdbl HD HDdj Hsbl HS HSdj HM HNM Hobnd HO HMI HAC HSW HHM HAE HAW HSW56 HAWba HAWd HAWs
    HDapp HSapp HMa HNa HOa HJ14 HJ13 HFP HFPN HTLS
    R96 R104 R112 R168 Rbytes Rimg Rlow Rwin Rwins Rgot Rcell Rfs Rfss Rtls Rmd Rd Rds Rs Rss Rnm Ro.
  (* the spill base does not wrap: solve_accs needs it for the four ld at s1 + 96 / 104 / 112 / 168 *)
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply MState.unsigned_lit; lia).
  pose proof (r6_q64_ro m (A + 96) 0x1234 C96) as RW96.
  pose proof (r6_q64_ro m (A + 104) 0x21140 C104) as RW104.
  pose proof (r6_q64_ro m (A + 112) mdv C112) as RW112.
  pose proof (r6_q64_ro m (A + 168) d C168) as RW168.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  subst Rv Eb len n.
  (* Speed: at a load, StepF's solve_acc1 tries the [rng] hypotheses and Step's solve_load_base the [ro_cells] ones
     newest first, and each wrong one costs lia calls that fail only after case-splitting the whole context (23-25 min
     of this file's build). Moving the load's own pair last makes the first candidate the right one. *)
  move R112 at bottom. move RW112 at bottom.
  step.                                (* 815cc ld a1,112(s1) *)
  step.                                (* 815d0 mv a2,s7 *)
  move R168 at bottom. move RW168 at bottom.
  step.                                (* 815d4 ld a3,168(s1) *)
  move R104 at bottom. move RW104 at bottom.
  step.                                (* 815d8 ld a4,104(s1) *)
  move R96 at bottom. move RW96 at bottom.
  step.                                (* 815dc ld a5,96(s1) *)
  step.                                (* 815e0 li a6,0 *)
  step.                                (* 815e4 li a7,0 *)
  step.                                (* 815e8 jal 847e4 reac_ctrl_build_as *)
  eapply ExecF.evtF_cut.
  { eapply BUILD_F with (o := o) (md := mdv) (b := bb) (d := d) (s := 0x21140) (ns := 0)
      (mb := mb) (nb := nb) (db := db) (sb := sb) (junk := junk) (FS := FS).
    all: rewrite ?MState.unsigned_lit by lia.
    all: try assumption.
    all: try reflexivity.
    all: try lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  Eq & MU & WM & MI & STp & ACp & SWp & AWp & FPp & _ & HOut).
  subst ms'.
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  assert (Etp : bv_unsigned (Z_to_bv 64 TPv) = TPv) by (apply MState.unsigned_lit; lia).
  rewrite ?Esp in MU. rewrite ?Esp in STp. rewrite ?Esp in AWp.
  rewrite ?Esp, ?Etp in FPp.
  replace (ret_pc (Z_to_bv 64 0x815ec)) with (Z_to_bv 64 0x815ec)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STp|].
  split; [exact ACp|]. split; [exact SWp|]. split; [exact AWp|]. split; [exact FPp|].
  split.
  { intros x Hx. revert Hx.
    destruct (PB.ba_go o mdv bb && PB.ba_E (bm_uw mdv (firstn 8 (skipn 16 mb))) mb bb) eqn:HE;
      intros Hx; [|lia].
    destruct (HOut eq_refl) as (Hb & Hw & _).
    assert (Hmdne : mdv <> 0).
    { apply andb_true_iff in HE as [Hgo _]. unfold PB.ba_go in Hgo.
      apply andb_true_iff in Hgo as [Hg1 _]. apply andb_true_iff in Hg1 as [_ Hg2].
      apply negb_true_iff, Z.eqb_neq in Hg2. exact Hg2. }
    destruct (HM Hmdne) as (_ & _ & Hmbl & _ & _).
    destruct (em_wok_range _ Hw) as (Hnr & _).
    eapply (r6_present m' o _ x).
    + exact Hb.
    + apply r6_emfr_len; [exact Hdbl | exact Hsbl | exact (r6_baX_len mdv mb nb bb Hmbl) | lia].
    + lia. }
  (* the emitted frame: the count word c16 is [A + 96] = 0x1234, loaded into a5 at 0x815dc *)
  intros HE. destruct (HOut HE) as (Hb & _).
  match type of Hb with bytes_at _ _ _ (em_fr _ _ ?c _ _ _ _) =>
    replace c with 0x1234 in Hb by (vm_compute; reflexivity) end.
  exact Hb.
Qed.

(* R6.r6_evt's statement after its callee premise, re-derived from r6_evt_F at ExecF.RNG_all. Every rng premise is
   rng_all: the bounds of the four spill cells come from this lemma's own A bounds, the callee's from the plain
   premises it already carries (the window, the addressable ranges and the side-stack placement of fp), and each
   shadow cover from BA.ba_rng_all_shcov. The two forall-memory premises hold at RNG_all because RNG_all admits
   every access. *)
Lemma r6_evt_of_F : BA.reac_ctrl_build_as_contract_F ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A spv TPv o mdv bb d FS n len Rv : Z) (Eb : bool) (mb nb db sb junk : list byte),
    n = bm_uw mdv (firstn 8 (skipn 16 mb)) ->
    len = 52 + 36 * n ->
    Eb = PB.ba_E n mb bb ->
    Rv = (if PB.ba_go o mdv bb && Eb then len else 0) ->
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 spv -> tp = Z_to_bv 64 TPv -> s7 = Z_to_bv 64 bb ->
    a0 = Z_to_bv 64 o ->
    0 <= A -> A + 176 <= 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= mdv < 2 ^ 64 -> 0 <= bb <= 6 ->
    0 <= d < 2 ^ 64 -> 0 <= TPv < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 0x1234)) ->
    bytes_at rsegs m (A + 104) (le8 (Z_to_bv 64 0x21140)) ->
    bytes_at rsegs m (A + 112) (le8 (Z_to_bv 64 mdv)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 d)) ->
    spv mod 16 = 0 ->
    stk rsegs m (spv - BA.REAC_CTRL_BUILD_AS_K) spv ->
    bytes_at rsegs m (BA.BA_FR + 72) PB.ba_tbl ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv (BA.BA_FR + 72) (BA.BA_FR + 240) ->
    length db = 6%nat -> bytes_at rsegs m d db ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv d (d + 6) ->
    length sb = 6%nat -> bytes_at rsegs m 0x21140 sb ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv 0x21140 (0x21140 + 6) ->
    (mdv <> 0 -> mdv mod 8 = 0 /\ mdv + 296 <= 2 ^ 64 /\ length mb = 296%nat /\ bytes_at rsegs m mdv mb /\
                 ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv mdv (mdv + 296)) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       name_ok nb /\ bytes_at rsegs m (rname mb) nb /\
       ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (o <> 0 -> o + 1492 <= 2 ^ 64) ->
    (PB.ba_go o mdv bb && Eb = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\
       ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv o (o + len) /\
       ly_dj o (o + len) (BA.BA_FR + 72) (BA.BA_FR + 240) /\ ly_dj o (o + len) mdv (mdv + 296) /\
       (((bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0) ->
          ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) 0x21140 (0x21140 + 6)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= spv - BA.REAC_CTRL_BUILD_AS_K -> spv <= APPMEM_END ->
    addressable m (spv - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K ->
    addressable m BA.BA_SW 56 -> addressable m (BA.BA_FR + 72) 168 -> addressable m d 6 ->
    addressable m 0x21140 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (0x21140 + 6) /\ app_mem (0x21140 + 7) ->
    (mdv <> 0 -> addressable m mdv 296) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       addressable m (rname mb) (Z.of_nat (length nb))) ->
    (PB.ba_go o mdv bb && Eb = true ->
       addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (bb = 1 -> addressable m RBM.JOIN_0014 32) ->
    (bb = 2 -> addressable m RBM.JOIN_0013 32) ->
    fp [0%nat; 1%nat] m TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv
      [(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)]
      [(BA.BA_FR + 72, BA.BA_FR + 240); (mdv, mdv + 296); (d, d + 6); (0x21140, 0x21140 + 6); (o, o + Rv)] ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    BA.reac_ctrl_build_as_tls m TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x815ec) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Rv)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x815ec) fc None m' (seg_rom rsegs)
         /\ munch ([(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)] ++ fp_w [0%nat; 1%nat] FS ++
                   [(shadow_addr (spv - BA.REAC_CTRL_BUILD_AS_K), shadow_addr spv)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (spv - BA.REAC_CTRL_BUILD_AS_K) spv
         /\ asan_cells m' /\ shadow_rw m'
         /\ addressable m' (spv - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K
         /\ fp [0%nat; 1%nat] m' TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv
              [(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)]
              [(BA.BA_FR + 72, BA.BA_FR + 240); (mdv, mdv + 296); (d, d + 6); (0x21140, 0x21140 + 6); (o, o + Rv)]
         /\ (forall x, o <= x < o + Rv -> exists bx, mrd rsegs m' (wa x) = Some bx)
         /\ (PB.ba_go o mdv bb && Eb = true ->
               bytes_at rsegs m' o (em_fr db sb 0x1234 (Z_to_bv 8 205) (Z_to_bv 8 234) (PB.ba_X mdv mb nb bb) len)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815cc) fc None m (seg_rom rsegs)).
Proof.
  intros BUILD_F ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A spv TPv o mdv bb d FS n len Rv Eb mb nb db sb junk
    Hn Hlen HEb HRv Es1 Esp0 Etp0 Es7 Ea0 HA0 HA1 Ho Hmd Hbb Hd HTP Hspv C96 C104 C112 C168
    H16 ST HBA HBAdj Hdbl HD HDdj Hsbl HS HSdj HM HNM Hobnd HO HMI HAC HSW HHM HAE HAW HSW56 HAWba HAWd HAWs
    HDapp HSapp HMa HNa HOa HJ14 HJ13 HFP HFPN HTLS.
  pose proof ST as (STlo & SThi & _).
  pose proof HFP as FP'.
  destruct FP' as (DT0 & TS0 & C0 & T0 & DB0 & k0 & TLS0 & HTP0 & HFS & H88 & H96 & HCLS & HFSlo & HAPP & DJW & DJD).
  pose proof HFS as (FSpos & FS4096 & FSGT & FSAPP & FSSTK).
  pose proof HAW as (AW0 & AW1 & AW2 & _).
  pose proof HAWd as (AD0 & AD1 & AD2 & _).
  pose proof HAWs as (AS0 & AS1 & AS2 & _).
  eapply ExecF.evtF_evt,
    (r6_evt_F BUILD_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
       s10 s11 t3 t4 t5 t6 F fc m A spv TPv o mdv bb d FS n len Rv Eb mb nb db sb junk); try assumption.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  (* the callee's own footprint premises, by the discharge script of
     BA.reac_ctrl_build_as_contract_of_F (lib/A/Prog/reac_ctrl_build_as_c.v:223) *)
  - unfold rng_bytes; intros; exact I.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold BA.REAC_CTRL_BUILD_AS_K in *; lia.
  - apply BA.ba_rng_all_shcov; unfold BA.REAC_CTRL_BUILD_AS_K, APPMEM_END in *; lia.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - apply ExecF.rng_all; unfold BA.REAC_CTRL_BUILD_AS_K, APPMEM_END, FS_SIZE in *; lia.
  - apply BA.ba_rng_all_shcov; unfold BA.REAC_CTRL_BUILD_AS_K, APPMEM_END, FS_SIZE in *; lia.
  - intros DT TS C T DB kk HC.
    unfold asan_tls_cells in HC.
    destruct HC as (C1 & C2 & C3 & C4 & C5 & Hkk & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 &
                    C17 & C18 & C19).
    destruct C11 as (tb0 & te0 & C11).
    destruct C3 as (B3 & B3' & _). destruct C4 as (B4 & B4' & _). destruct C8 as (B8 & B8' & _).
    destruct C9 as (B9 & B9' & _). destruct C10 as (B10 & B10' & _). destruct C17 as (B17 & B17' & _).
    destruct C19 as (B19 & B19' & _). destruct C11 as (B11 & B11' & _).
    rewrite length_le8 in B3', B4', B8', B9', B10', B17', B19'. rewrite !app_length, !length_le8 in B11'.
    unfold fp_tls, TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY,
      VERBOSITY, DTLS_TPOFF.
    repeat (apply Forall_cons; [cbn [fst snd]; apply ExecF.rng_all; lia|]). apply Forall_nil.
  - intros Hmdne. pose proof (HMa Hmdne) as (M0 & _ & M2 & _).
    split; [apply ExecF.rng_all | apply BA.ba_rng_all_shcov]; unfold APPMEM_END in *; lia.
  - apply ExecF.rng_all; unfold APPMEM_END in *; lia.
  - apply BA.ba_rng_all_shcov; unfold APPMEM_END in *; lia.
  - apply ExecF.rng_all; unfold APPMEM_END in *; lia.
  - apply BA.ba_rng_all_shcov; unfold APPMEM_END in *; lia.
  - intros Hmdne Hnm. pose proof (HNa Hmdne Hnm) as (N0 & N1 & N2 & _).
    split; [apply ExecF.rng_all | apply BA.ba_rng_all_shcov]; unfold APPMEM_END in *; lia.
  - intros HE. pose proof (HOa HE) as ((O0 & O1 & O2 & _) & _ & _).
    split; [apply ExecF.rng_all | apply BA.ba_rng_all_shcov]; unfold APPMEM_END in *; lia.
Qed.

(* The pin: r6_evt_of_F states R6.r6_evt's v1.9 text after R6.r6_evt's own first premise, the plain callee
   contract BA.reac_ctrl_build_as_contract; this corollary carries the footprint contract in that place
   (constr_eq is syntactic, not up to conversion). *)
Example r6_evt_of_F_verbatim : True.
Proof.
  lazymatch type of R6.r6_evt with ?P -> ?A =>
    constr_eq P BA.reac_ctrl_build_as_contract;
    lazymatch type of r6_evt_of_F with ?Q -> ?B =>
      constr_eq Q BA.reac_ctrl_build_as_contract_F; constr_eq A B
    end
  end.
  exact I.
Qed.

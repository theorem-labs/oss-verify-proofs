(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 414 of its 429 lines of code are new or changed and 233 lines of the source are left out. *)
(* ctrl_lay_block, image A (asan, entry 0x855f4): region R3 of the cgif glue (0x85828, the return of
   reac_box_model_block, -> 0x858f4, after the class-1 flag release).  A Theorem Labs lane.  Re-base plan
   ctrl_lay_block-rebase.md section 3 R3, sections 4 and 5 (a working note, not in this delivery).

   R3's run is k5 -> k6 -> k7 -> the release.  The glue applies the stretch lemmas with Section L's memory
   m := normalize m2 (m2 = TMB's return memory): that is the re-base, no copy needed for it.  This file adds what
   the glue's journal step (ProgWorld.v ctl_release_of_free_law_stmt :485-500: every byte the run writes is an
   awr_byte or the flag byte) needs and the stretches do not state:
   - lay_F_R3_box_arm / lay_F_R3_cpy: RE-BASED copy of stretch k = 5 (ctrl_lay_block_F_5.v lay_F5_box_arm
     :284-328, lay_F5_cpy :201-278).  The original post (lay_F5_post_args) keeps only LC's coarse write set
     (ctrl_lay_block.v:924, lay_X :557: class-0/1 hint words, flag arrays, other frames, the window's shadow -- not
     awr).  The exact set is the memcpy contract's own munch `MUc` (ctrl_lay_block_F_5.v:268-270); the copy adds it to
     the post (lay_F_R3_post_args).
   - ly_args_F_R3_g0: stretch k = 6 (ctrl_lay_block_F_6.v ly_args_F :269-300) at g = 0, the only case the contract
     allows (C_ctrl_lay_block.v:112 `getr regs 13 = w64 0`): one `step` (the `beqz s3` at 0x85840, taken); the copy's
     post states the memory unchanged (the original hides it, ctrl_lay_block_F_6.v:256).
   - lay_F_R3_release: the inline class-1 flag release, `ld a0,120(s2)` (0x858ec) and `sb zero,0(a0)` (0x858f0),
     which no stretch takes (k = 7 stops at 0x858ec, k = 8 starts at 0x858f4).  Re-stepped from ly_epi_side
     (ctrl_lay_block.v:1460-1488) verbatim: the ro_cells of the flag-pointer word, the load, the tracked flag cell
     and its store_ok, the store.  Footprint: the word (frb + 120) 8 and the flag byte fa 1.
   k7 (ctrl_lay_block_F_7.v) needs no copy: its post already states its exact writes (:117).

   DIFF AGAINST ctrl_lay_block_F_5.v (not in this delivery; for the auditor a Theorem Labs lane; instruction proofs VERBATIM):
   - Section L5 -> L5R; every `lay_F5_` name -> `lay_F_R3_` (the four Section L wrappers :152-182 unchanged
     otherwise); lay_F5_post_args -> lay_F_R3_post_args (one more parameter mc0, one more conjunct `munch ... mc0
     mc'`).
   - lay_F_R3_cpy: post `lay_F_R3_post_args mc ...`; final `split; [exact FI2 | exact LC2]` -> `split; [exact FI2 |
     split; [exact LC2 |]]` closed by `exact MUc` (or munch_weaken onto the same two ranges).
   - lay_F_R3_box_arm: post `lay_F_R3_post_args mc ...`; the r <> 1 arm adds `apply munch_refl`.
   - lay_F5_box_arm_of_F is not copied.
   No Section L helper is re-proved.

   ROUTE (a) CONDITIONS (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z, via a Theorem Labs lane); re-based copy allowed by a Theorem Labs lane 23:53Z
   (instruction proofs verbatim, re-proved helpers named: none):
   1. Each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and
      no new proof obligation.
   2. The _F output feeds ONLY the ported cgif-form walk.  No W_cutfree_ok, no cut-free twin, no LSCPS join, no
      top-level claim.
   3. The source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
      wrong-image cell.  The re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes.
   4. Every _F carries provenance in its header and goes to the auditor a Theorem Labs lane
      who signs it against its proved run before it counts.
   5. A StepF "footprint: access <a> width <n> not covered by any [rng] hypothesis" error means STOP and report
      it: never widen the footprint to make it pass.

   PROVENANCE.
   - image root (internal path)
     -> (internal path)
   - ELF sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd
   - compare: fuzz_ctrl.objdump.txt (a working note, not in this delivery), ctrl_lay_block 0x855f4 .. 0x85988
   - FACTS of record ed6b6b7b0ab (origin/regen/libreac-v190-on-338), PAU (internal path)
   - copied from ctrl_lay_block_F_5.v (not in this delivery) (a working branch 7e0119cf3f3) and ctrl_lay_block_F_6.v (not in this delivery)
     (a working branch 77cd0613fcf), merged 9d33dba1444; the release from ctrl_lay_block.v ly_epi_side at
     a working branch d69f7c708f6. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import ctrl_lay_block_F_common.
(* The skeleton's Require list, repeated in its order (Import is not transitive; lib.Lib ExecF StepF LAST, so StepF's
   step / if_false / finish / store_done shadow the evt engine's). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth
  RcSynthLib RcLay RcLayLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c reac_box_model_block_c ctrl_lay_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import ctrl_lay_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF asan_memcpy_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* stretch k = 7, Required qualified (the region run below composes it) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ctrl_lay_block_F_7.
(* Local copy of ctrl_lay_block.v:215's store hook: the base made it Local (a Theorem Labs lane; from a working branch c9390e308b8); this file's rd_mono steps need it. *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.
Import ListNotations.
Open Scope Z_scope.

(* ---- the inline class-1 flag release, 0x858ec -> 0x858f4 (ctrl_lay_block.v ly_epi_side :1460-1488) ----
   Pre: k = 7's post state (lay_F_pre_release, ctrl_lay_block_F_7.v:108-120): s2 = frb, the flag-pointer word at
   frb + 120 holds fa (bytes_at, F_7:119); the flag byte fa is present and writable at m'.  Post: pc 0x858f4, a0 =
   the loaded word, the flag byte is 0, and the only byte written is fa. *)
Lemma lay_F_R3_release : forall (RNG : ExecF.footprint)
    (xra x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27
     x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (frb fa : Z) (m' : word -> option byte),
  0 <= frb -> frb + 128 <= 2 ^ 64 -> 0 <= fa -> fa + 1 <= 2 ^ 64 ->
  bytes_at rsegs m' (frb + 120) (le8 (Z_to_bv 64 fa)) ->
  wview rsegs m' (wa fa) <> None -> (exists b, mrd rsegs m' (wa fa) = Some b) ->
  mem_inv rsegs m' ->
  ExecF.rng RNG (frb + 120) 8 -> ExecF.rng RNG fa 1 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists (a0' : word) (m'' : word -> option byte),
       ms = MS (mkR xra x2 x3 x4 x5 x6 x7 x8 x9 a0' x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 frb)
                    x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x858f4) fc None m'' (seg_rom rsegs) /\
       munch [(fa, fa + 1)] m' m'' /\ wmono rsegs m' m'' /\ rd_mono m' m'' /\ mem_inv rsegs m'' /\
       rw_cells rsegs m'' fa [C1 (Z_to_bv 8 0)])
    (MS (mkR xra x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 frb)
             x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x858ec) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG xra x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc frb fa m' Hfrb0 Hfrb1 Hfa0 Hfa1 HFB FWa (fb & Hfb) MIc RW120 RWFA.
  pose proof (munch_refl [(fa, fa + 1)] m') as MUcc.
  pose proof (wmono_refl rsegs m') as WMcc.
  pose proof (rd_mono_refl m') as RMcc.
  (* ly_epi_side :1460-1464: the flag-pointer word as a read-only cell for the load *)
  assert (HRO : ro_cells rsegs m' (frb + 120) [C8 (Z_to_bv 64 fa)]) by (apply bytes_ro8; exact HFB).
  (* 0x858ec ld a0,120(s2) *)
  step.
  (* :1466-1476: the flag byte as a tracked cell *)
  assert (HFc : rw_cells rsegs m' fa [C1 fb])
    by (split; [split|];
        [ cbn [cells_wf cell_wf]; tauto
        | cbn [cells_bytes cbytes app]; split; [lia|];
          split; [cbn [length Z.of_nat Pos.of_succ_nat]; lia|];
          intros i Hi; cbn [length] in Hi; assert (i = 0%nat) by lia; subst i;
          cbn [nth_error]; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; exact Hfb
        | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]; split; [lia|]; split; [lia|];
          intros i Hi; assert (i = 0) by lia; subst i; rewrite Z.add_0_r; exact FWa ]).
  (* :1477-1480 *)
  assert (HSf : store_ok rsegs m' (wa fa) 1 = true)
    by (eapply wv_store_ok; [ intros i Hi; assert (i = 0) by lia; subst i; rewrite Z.add_0_r; exact FWa
                            | apply wmono_refl | lia | lia ]).
  (* 0x858f0 sb zero,0(a0): the release store (tracked: StepF's step runs mem_after_store on HFc) *)
  step.
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => store_done
  | _ => idtac
  end.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  split; [exact MUcc|]. split; [exact WMcc|]. split; [exact RMcc|]. split; [exact MIc | exact HFc].
Qed.

Section L5R.
  (* Section L's Variables (ctrl_lay_block.v:404-405), verbatim. *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr ob tb mb nb gb : list byte).

  Local Notation S := (bv_unsigned sp).
  Local Notation K := CTRL_LAY_BLOCK_K.

  (* Section L's Hypotheses (ctrl_lay_block.v:410-474), verbatim.  The four callee / runtime contracts of Section L
     (HSM, MEMS, MEMC, BOX) are NOT taken here: this stretch contains only the checked copy, and takes a Theorem Labs lane's
     footprint contract asan_memcpy_contract_F for it (MEMCF below). *)
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Rmd : 0 <= md < 2^64.
  Hypothesis Rg : 0 <= g < 2^64.
  Hypothesis SP16 : S mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (S - K) S.
  Hypothesis DJ1 : ly_dj (S - K) S (p + 18) (p + 50).
  Hypothesis DJ2 : ly_dj (S - K) S f (f + 24).
  Hypothesis DJ3 : ly_k fr = 2 -> ly_dj (S - K) S (ly_tm fr) (ly_tm fr + 32).
  Hypothesis DJ3g : g <> 0 -> ly_al fr <> 0 -> ly_dj (S - K) S g (g + ly_al fr).
  Hypothesis DJ3m : 3 <= ly_k fr <= 9 -> md <> 0 ->
    ly_dj (S - K) S md (md + 296) /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       ly_dj (S - K) S (rname mb) (rname mb + Z.of_nat (length nb))).
  Hypothesis F8 : f mod 8 = 0.
  Hypothesis F24 : f + 24 <= 2^64.
  Hypothesis FL : length fr = 24%nat.
  Hypothesis FB : bytes_at rsegs m f fr.
  Hypothesis K9 : ly_k fr <= 9.
  Hypothesis AOL : ly_ao fr + ly_al fr <= 32.
  Hypothesis TM : ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm fr) tb.
  Hypothesis P0 : p <> 0.
  Hypothesis P50 : p + 50 <= 2^64.
  Hypothesis BLK : rw_cells rsegs m (p + 18) [CB 32 ob].
  Hypothesis DB1 : ly_dj (p + 18) (p + 50) f (f + 24).
  Hypothesis DB2 : ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32).
  Hypothesis DB3 : 3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296).
  Hypothesis DBN : 3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) ->
    has mb <> 0 -> rname mb <> 0 -> ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb)).
  Hypothesis MDP : 3 <= ly_k fr <= 9 -> md <> 0 ->
    md mod 8 = 0 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       name_ok nb /\ bytes_at rsegs m (rname mb) nb).
  Hypothesis GP : g <> 0 -> ly_al fr <> 0 ->
    Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= S - K.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW0 : addressable m (S - K) K.
  Hypothesis AF : addressable m f 24.
  Hypothesis AR : addressable m (p + 18) 32.
  Hypothesis AP50 : app_mem (p + 50).
  Hypothesis ARDJ : p + 50 <= RT_LO \/ RT_HI <= p + 18.
  Hypothesis ATM : ly_k fr = 2 -> addressable m (ly_tm fr) 32.
  Hypothesis AG : g <> 0 -> ly_al fr <> 0 ->
    addressable m g (ly_al fr) /\ app_mem (g + ly_al fr) /\ app_mem (g + 7) /\ app_mem (p + 25 + ly_ao fr).
  Hypothesis AMD : 3 <= ly_k fr <= 9 -> md <> 0 ->
    addressable m md 296 /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       addressable m (rname mb) (Z.of_nat (length nb))).
  Hypothesis AJ5 : ly_k fr = 5 -> addressable m JOIN_0014 32.
  Hypothesis AJ6 : ly_k fr = 6 -> addressable m JOIN_0013 32.
  Hypothesis FP0 : fp [0%nat; 1%nat] m (bv_unsigned tp) FS (S - K) S
    (ctrl_lay_block_W p S) (ctrl_lay_block_D p f).
  Hypothesis FPT : ly_k fr = 2 -> fp_dj [(ly_tm fr, ly_tm fr + 32)] (fp_w [0%nat; 1%nat] FS).
  Hypothesis FPG : g <> 0 -> ly_al fr <> 0 -> fp_dj [(g, g + ly_al fr)] (fp_w [0%nat; 1%nat] FS).
  Hypothesis FPM : 3 <= ly_k fr <= 9 -> md <> 0 ->
    fp_dj [(md, md + 296)] (fp_w [0%nat; 1%nat] FS) /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)).
  Hypothesis TLS0 : ctrl_lay_block_tls m (bv_unsigned tp) FS (S - K) S.

  (* The one callee contract this stretch applies, in footprint form, owned and proved by a Theorem Labs lane
     (lib/A/Prog/asan_memcpy_cF.v): taken by name, of exactly its type, never restated. *)
  Hypothesis MEMCF : asan_memcpy_contract_F.

  Local Notation SP2 := ((S - 128) / 32 * 32).

  (* Section L's predicates, applied to this section's variables (they are Section L members, so outside L they
     carry the variables they use; the argument lists are ctrl_lay_block.vo's). *)
  Local Notation FK := (ctrl_lay_block.FK sp FS).
  Local Notation FI := (ctrl_lay_block.FI sp tp p f FS).
  Local Notation LC := (ctrl_lay_block.LC ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS fr).
  Local Notation BASE := (ctrl_lay_block.BASE md fr tb mb nb).

  (* Section L's helper lemmas, re-exposed in their in-section shape (same proofs, nothing re-proved: each is the
     Section L constant applied to this section's variables and hypotheses). *)
  Lemma lay_F_R3_LC_addr_p : forall mc gj X, LC mc gj X -> addressable mc (p + 18) 32.
  Proof.
    exact (LC_addr_p ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f md g FS fr tb mb nb gb
             Rp Rf Rmd Rg SP16 DJ1 FL K9 TM P0 MDP HHM AR FP0).
  Qed.

  Lemma lay_F_R3_app_blk : forall x, p + 18 <= x <= p + 50 -> app_mem x.
  Proof.
    exact (app_blk sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg FL TM MDP AR AP50).
  Qed.

  Lemma lay_F_R3_stk_shrink : forall mm lo hi hi', stk rsegs mm lo hi -> lo <= hi' <= hi -> stk rsegs mm lo hi'.
  Proof.
    exact (stk_shrink sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg FL K9 TM P0 MDP).
  Qed.

  Lemma lay_F_R3_fk_spc : forall frb sfr spc j w120, FK frb sfr spc j w120 -> S - 256 <= spc <= S - 128.
  Proof.
    exact (fk_spc sp tp m p f md g FS fr tb mb nb gb
             Rp Rf Rmd Rg SP16 ST0 FL K9 TM P0 MDP SR0 HHM HAE AW0 FP0).
  Qed.

  Lemma lay_F_R3_LC_FI_memcpy : forall mc m' gj X X' D N frb sfr spc j w120,
    LC mc gj X -> FI mc frb sfr spc j w120 -> p + 18 <= D -> D + N <= p + 50 -> 0 <= N ->
    munch [(D, D + N); (spc - ASAN_MEMCPY_K, spc)] mc m' -> wmono rsegs mc m' -> mem_inv rsegs m' ->
    stk rsegs m' (S - K) spc -> rw_cells rsegs m' (p + 18) [CB 32 X'] ->
    LC m' gj X' /\ FI m' frb sfr spc j w120.
  Proof.
    exact (LC_FI_memcpy ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f md g FS fr tb mb nb gb
             Rp Rf Rmd Rg SP16 ST0 DJ1 DJ2 DJ3m FL K9 TM P0 DB1 DB3 DBN MDP SR0 HHM HAE AW0 AR ARDJ AMD FP0 FPM).
  Qed.

  (* The copy's post: lay_F5_post_args (ctrl_lay_block_F_5.v:187-196) plus the exact write set from the pre memory
     mc0: the memcpy contract's own munch (asan_memcpy_c.v:16-17, `MUc` at ctrl_lay_block_F_5.v:268-270); on the
     r <> 1 arm the memory is unchanged (munch_refl). *)
  Definition lay_F_R3_post_args (mc0 : word -> option byte) (frb sfr spc j : Z) (w120 : word)
      : machine_state -> Prop :=
    fun ms' => exists (mc' : word -> option byte) (gj' : list byte)
                 (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
      ms' = MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
                    x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f)
                    (Z_to_bv 64 (p + 18)) x22 x23
                    (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
                    x28 x29 x30 x31)
               F (Z_to_bv 64 0x85840) fc None mc' (seg_rom rsegs) /\
      FI mc' frb sfr spc j w120 /\ LC mc' gj' BASE /\
      munch [(p + 18, p + 18 + 32); (spc - ASAN_MEMCPY_K, spc)] mc0 mc'.

  (* 0x8583c: the checked copy of the 32 bytes at src (the box result at frb + 32) into the output block, then the
     ly_args entry at 0x85840.  Footprint re-run of ly_cpy (ctrl_lay_block.v:1932-1993) up to its hand-over to
     ly_args; the only access-bearing step is the call, which goes through asan_memcpy_contract_F. *)
  Lemma lay_F_R3_cpy : forall (RNG : footprint) (mc : word -> option byte) (gj X sb : list byte)
      (src frb sfr spc j : Z)
      (w120 xra x5 x6 x7 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
    FI mc frb sfr spc j w120 -> LC mc gj X ->
    bytes_at rsegs mc src sb -> length sb = 32%nat -> sb = BASE -> 0 <= src < 2^64 ->
    (src + 32 <= p + 18 \/ p + 50 <= src) ->
    addressable mc src 32 -> app_mem (src + 32) -> (src + 32 <= S - K \/ spc <= src) ->
    (* the copy's own footprint premises (plan row k = 5) *)
    RngBytes.rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (spc - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    rng RNG (p + 18) 32 -> rng RNG src 32 ->
    sh_word_rng RNG (spc - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    sh_word_rng RNG (p + 18) 32 -> sh_word_rng RNG src 32 ->
    evtF rsegs RNG (lay_F_R3_post_args mc frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               (Z_to_bv 64 (p + 18)) (Z_to_bv 64 src) (Z_to_bv 64 32) x13 x14 x15 x16 x17
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) x22 x23
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x8583c) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj X sb src frb sfr spc j w120 xra x5 x6 x7 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31
      FIH LCH SB SL ESB RS DS AS AE DSW RB RIMG RSPW RROW RSRC SHSP SHROW SHSRC.
    pose proof (lay_F_R3_LC_addr_p mc gj X LCH) as ARc.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FBc).
    pose proof (lay_F_R3_fk_spc frb sfr spc j w120 (proj1 FIH)) as Hspc.
    pose proof FIH as (_ & _ & ACc & SRc & _).
    step.
    assert (U18 : bv_unsigned (Z_to_bv 64 (p + 18)) = p + 18) by (apply unsigned_lit; lia).
    assert (U32 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
    assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 spc) = spc)
      by (apply unsigned_lit; pose proof HHM; unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in *;
          pose proof (zr_word sp) as Rsp; unfold inr64 in Rsp; lia).
    pose proof MEMCF as HM. unfold asan_memcpy_contract_F in HM. cbv zeta in HM.
    eapply evtF_cut.
    { eapply HM with (RNG := RNG) (src := sb) (lo := S - K).
      all: rewrite ?U18, ?U32, ?US, ?USP; unfold ASAN_MEMCPY_K.
      - exact SB.
      - exact SL.
      - exact BK.
      - lia.
      - lia.
      - exact AS.
      - exact ARc.
      - right. exact AE.
      - right. apply lay_F_R3_app_blk. lia.
      - right. split; [apply (acl_app_in mc src 32 7 AS); lia | apply lay_F_R3_app_blk; lia].
      - pose proof ARDJ as AJ. unfold RT_LO, RT_HI in *. lia.
      - pose proof DJ1 as D1. unfold ly_dj, CTRL_LAY_BLOCK_K in D1. lia.
      - unfold CTRL_LAY_BLOCK_K in DSW. lia.
      - apply (lay_F_R3_stk_shrink mc (S - K) (S + -128) spc ST). unfold CTRL_LAY_BLOCK_K. lia.
      - unfold CTRL_LAY_BLOCK_K. lia.
      - exact HHM.
      - pose proof HAE. lia.
      - exact ACc.
      - exact SRc.
      - exact MI.
      - exact RB.
      - exact RIMG.
      - exact RSPW.
      - exact RROW.
      - exact RSRC.
      - exact SHROW.
      - exact SHSRC.
      - exact SHSP. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MUc & WMc & MIc & STc & RWc & _ & _ & _).
    rewrite U18, U32, USP in MUc. rewrite USP in STc. rewrite U18, U32 in RWc.
    change (Z.to_nat 32) with 32%nat in RWc.
    rewrite ESB in RWc.
    destruct (lay_F_R3_LC_FI_memcpy mc m' gj X BASE (p + 18) 32 frb sfr spc j w120 LCH FIH
                ltac:(lia) ltac:(lia) ltac:(lia) MUc WMc MIc STc RWc) as (LC2 & FI2).
    rewrite (ret_pc_even 0x85840) by lia.
    apply evtF_done. unfold lay_F_R3_post_args.
    do 20 eexists. split; [reflexivity|]. split; [exact FI2 | split; [exact LC2 |]].
    first [ exact MUc
          | eapply munch_weaken; [| exact MUc]; intros x Hx; cbn [outside] in Hx |- *; unfold ASAN_MEMCPY_K in *; lia ].
  Qed.

  (* 0x85828 -> 0x85840: `li a1,1; bne a0,a1,0x85840`.  r <> 1 (the callee found no model, or md = 0): BASE is
     ly_zero and the zeroed output block already holds BASE, so the run is at the ly_args entry; r = 1: three moves
     (a2 = 32, a0 = s5 = p + 18, a1 = s7 = frb + 32) and the checked copy of the box result.  Footprint re-run of
     ly_box's KB continuation (ctrl_lay_block.v:4141-4157). *)
  Lemma lay_F_R3_box_arm : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte)
      (r frb sfr spc j : Z) (w120 : word)
      (xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    FI mc frb sfr spc j w120 -> LC mc gj ly_zero -> addressable mc (frb + 32) 32 ->
    -1 <= r <= 1 -> (r = 1 -> bytes_at rsegs mc (frb + 32) BASE /\ length BASE = 32%nat) ->
    (r <> 1 -> BASE = ly_zero) ->
    0 <= frb + 32 < 2 ^ 64 -> app_mem (frb + 64) ->
    (frb + 64 <= p + 18 \/ p + 50 <= frb + 32) -> (frb + 64 <= S - K \/ spc <= frb + 32) ->
    (* the stretch's own window, then the copy's own premises (plan row k = 5) *)
    rng RNG (S - K) K ->
    RngBytes.rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (spc - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    rng RNG (p + 18) 32 -> rng RNG (frb + 32) 32 ->
    sh_word_rng RNG (spc - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    sh_word_rng RNG (p + 18) 32 -> sh_word_rng RNG (frb + 32) 32 ->
    evtF rsegs RNG (lay_F_R3_post_args mc frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
               (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18))
               (Z_to_bv 64 md) (Z_to_bv 64 (frb + 32))
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               t3' t4' t5' t6')
          F (Z_to_bv 64 0x85828) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj r frb sfr spc j w120 xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      FI' LC' AO' RR R1 Rn1 RO AE DP DW RWIN RB RIMG RSPW RROW RSRC SHSP SHROW SHSRC.
    assert (RC : r = -1 \/ r = 0 \/ r = 1) by (clear -RR; lia).
    destruct RC as [E|[E|E]]; subst r; step; step;
      try (lazymatch goal with |- context [bv_eqb ?u ?v] =>
             let e := eval vm_compute in (bv_eqb u v) in change (bv_eqb u v) with e end);
      cbn [negb]; cbv iota.
    1, 2: (* r <> 1: BASE = ly_zero, so the zeroed output block already holds BASE *)
      rewrite <- (Rn1 ltac:(clear; lia)) in LC';
      apply evtF_done; unfold lay_F_R3_post_args; do 20 eexists;
      (split; [reflexivity|]); split; [exact FI' | split; [exact LC' | apply munch_refl]].
    (* r = 1: the output block holds BASE; copy it to p + 18 *)
    destruct (R1 eq_refl) as (SB & SL).
    step. step. step.
    replace (frb + 64) with (frb + 32 + 32) in AE, DP, DW by ring.
    eapply lay_F_R3_cpy;
      [exact FI' | exact LC' | exact SB | exact SL | reflexivity | exact RO | exact DP | exact AO' | exact AE
       | exact DW | exact RB | exact RIMG | exact RSPW | exact RROW | exact RSRC | exact SHSP | exact SHROW
       | exact SHSRC].
  Qed.

  Local Notation LAY := (ctrl_lay_block.LAY md g fr tb mb nb gb).

  (* ---- stretch k = 6 at g = 0 (ctrl_lay_block_F_6.v ly_args_F :269-300, its g = 0 arm :295-300) ----
     The post: ly_args_F_post (ctrl_lay_block_F_6.v:255-263) with the memory fixed to the pre memory mc0. *)
  Definition ly_args_F_R3_post (mc0 : word -> option byte) (gj : list byte) (frb sfr spc j : Z) (w120 : word)
      : machine_state -> Prop :=
    fun ms' => exists (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
      ms' = MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
                    x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) x19 x20 x21 x22 x23
                    (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
                    x28 x29 x30 x31)
               F (Z_to_bv 64 0x85884) fc None mc0 (seg_rom rsegs) /\
      FI mc0 frb sfr spc j w120 /\ LC mc0 gj LAY.

  Lemma ly_args_F_R3_g0 : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z)
      (w120 : word) (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
    g = 0 -> FI mc frb sfr spc j w120 -> LC mc gj BASE ->
    evtF rsegs RNG (ly_args_F_R3_post mc gj frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f)
               (Z_to_bv 64 (p + 18)) x22 x23
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85840) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31
      Hg0 FIH LCH.
    step. rewrite (rc_eqb g 0) by lia.
    destruct (Z.eqb_spec g 0) as [G0|G0]; cbv iota; [| exfalso; exact (G0 Hg0)].
    apply evtF_done. unfold ly_args_F_R3_post. do 21 eexists.
    split; [reflexivity|]. split; [exact FIH|].
    replace LAY with BASE; [exact LCH|].
    unfold ctrl_lay_block.LAY, ctrl_lay_block.BASE, ly_lay. rewrite (proj2 (Z.eqb_eq g 0) G0). reflexivity.
  Qed.

  (* ---- the region's whole run (0x85828, the box call's return, -> 0x858f4, after the class-1 flag release):
     lay_F_R3_box_arm (k = 5), ly_args_F_R3_g0 (k = 6 at g = 0), stretch k = 7 (ctrl_lay_block_F_7.v
     ctrl_lay_block_F_7) and lay_F_R3_release.  The glue lifts this ONE run with Section L's memory
     m := normalize m2 (m2 = reac_box_model_block's return memory) and steps the journal with
     ProgWorld.ctl_release_of_free_law over it: the post states the exact write set (the memcpy's, k = 7's and the
     flag byte), the flag byte 0, and the cells stretch k = 8 takes (the saved registers, the laid-down block). ---- *)
  Definition lay_F_R3_end (mc0 : word -> option byte) (gj : list byte) (frb spc j : Z) (w120 : word)
      : machine_state -> Prop :=
    fun ms' => exists (xra x5 x6 x7 a0' x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                      (mc1 : word -> option byte) (gj1 : list byte) (m3 m4 : word -> option byte),
      ms' = MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
                    a0' x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 frb) x19 x20 x21 x22 x23
                    (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
                    x28 x29 x30 x31)
               F (Z_to_bv 64 0x858f4) fc None m4 (seg_rom rsegs) /\
      (* k = 5 / k = 6: the memcpy's write set, the ly_args / EPI_T bundle at mc1 *)
      munch [(p + 18, p + 18 + 32); (spc - ASAN_MEMCPY_K, spc)] mc0 mc1 /\
      FI mc1 frb frb spc j w120 /\ LC mc1 gj1 LAY /\
      (* k = 7 (lay_F_pre_release, ctrl_lay_block_F_7.v:117-120) *)
      munch [(shadow_addr frb, shadow_addr frb + 16); (frb, frb + 8)] mc1 m3 /\
      wmono rsegs mc1 m3 /\ rd_mono mc1 m3 /\
      (* the release (lay_F_R3_release) *)
      munch [(fs_flag FS 1 j, fs_flag FS 1 j + 1)] m3 m4 /\ wmono rsegs m3 m4 /\ rd_mono m3 m4 /\
      mem_inv rsegs m4 /\ rw_cells rsegs m4 (fs_flag FS 1 j) [C1 (Z_to_bv 8 0)] /\
      w120 = Z_to_bv 64 (fs_flag FS 1 j).

  Lemma lay_F_R3_run : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte)
      (r frb sfr spc j : Z) (w120 : word)
      (xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    FI mc frb sfr spc j w120 -> LC mc gj ly_zero -> addressable mc (frb + 32) 32 ->
    -1 <= r <= 1 -> (r = 1 -> bytes_at rsegs mc (frb + 32) BASE /\ length BASE = 32%nat) ->
    (r <> 1 -> BASE = ly_zero) ->
    0 <= frb + 32 < 2 ^ 64 -> app_mem (frb + 64) ->
    (frb + 64 <= p + 18 \/ p + 50 <= frb + 32) -> (frb + 64 <= S - K \/ spc <= frb + 32) ->
    rng RNG (S - K) K ->
    RngBytes.rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (spc - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    rng RNG (p + 18) 32 -> rng RNG (frb + 32) 32 ->
    sh_word_rng RNG (spc - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    sh_word_rng RNG (p + 18) 32 -> sh_word_rng RNG (frb + 32) 32 ->
    g = 0 -> sfr <> 0 ->
    rng RNG frb 24 -> rng RNG (shadow_addr frb) 16 ->
    rng RNG (frb + 120) 8 -> rng RNG (fs_flag FS 1 j) 1 ->
    evtF rsegs RNG (lay_F_R3_end mc gj frb spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
               (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18))
               (Z_to_bv 64 md) (Z_to_bv 64 (frb + 32))
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               t3' t4' t5' t6')
          F (Z_to_bv 64 0x85828) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj r frb sfr spc j w120 xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      FI0 LC0 AO0 RR R1 Rn1 RO AE DP DW RWIN RB RIMG RSPW RROW RSRC SHSP SHROW SHSRC Hg0 Hsfr RFRB RSHA R120 RFA.
    (* the side frame: FK's second disjunct *)
    pose proof FI0 as (HK & _).
    destruct HK as [(E0 & _) | (Hj & Efr & Esfr & Espc & Ew)]; [exfalso; exact (Hsfr E0)|].
    (* k = 5 *)
    eapply evtF_cut.
    { exact (lay_F_R3_box_arm RNG mc gj r frb sfr spc j w120 xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7'
               t3' t4' t5' t6' FI0 LC0 AO0 RR R1 Rn1 RO AE DP DW RWIN RB RIMG RSPW RROW RSRC SHSP SHROW SHSRC). }
    intros ms1 (mc1 & gj1 & y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y22 & y23
                & y28 & y29 & y30 & y31 & -> & FI1 & LC1 & MU1).
    (* k = 6 at g = 0 *)
    eapply evtF_cut.
    { exact (ly_args_F_R3_g0 RNG mc1 gj1 frb sfr spc j w120 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23
               y28 y29 y30 y31 Hg0 FI1 LC1). }
    intros ms2 (z1 & z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z19 & z20 & z21 & z22 & z23
                & z28 & z29 & z30 & z31 & -> & FI2 & LC2).
    (* k = 7 *)
    eapply evtF_cut.
    { exact (ctrl_lay_block_F_7.ctrl_lay_block_F_7 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
               p f md g FS fr tb mb nb gb Rp Rf Rmd Rg SP16 ST0 FL K9 TM P0 MDP SR0 HHM HAE AW0 FP0
               RNG mc1 gj1 frb sfr spc j w120 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z19 z20 z21 z22 z23
               z28 z29 z30 z31 RWIN RFRB RSHA FI2 Hsfr LC2). }
    intros ms3 (a0' & m3 & -> & MU3 & WM3 & RM3 & MI3 & FB3 & _).
    subst sfr w120.
    assert (EfM1 : fs_M 1 = 8192) by reflexivity.
    assert (Efa : fs_flag FS 1 j = FS + 20480 + j) by (unfold fs_flag; cbn; lia).
    assert (Efr' : frb = FS + 1085440 + j * 128) by (rewrite Efr; unfold fs_frame, fs_B; cbn; lia).
    rewrite EfM1 in Hj.
    pose proof FP0 as (_ & _ & _ & _ & _ & _ & _ & _ & (FSpos & _ & _ & _ & _) & _ & _ & _ & HFS0 & _).
    unfold FS_SIZE in HFS0. assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity. rewrite EK in HFS0.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    (* the flag byte is present and writable at m3: fp's side stack at mc1, kept by k = 7 *)
    pose proof FI2 as (_ & _ & _ & _ & FPc & _).
    pose proof FPc as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & PStkc) & _).
    pose proof (stk_mono mc1 m3 _ _ PStkc WM3 RM3) as PStk3.
    unfold FS_SIZE in PStk3.
    assert (FWa : wview rsegs m3 (wa (fs_flag FS 1 j)) <> None)
      by (apply (stk_wv m3 FS (FS + 11571200)); [exact PStk3 | lia]).
    destruct (rd_of_stk m3 FS (FS + 11571200) PStk3 (fs_flag FS 1 j) ltac:(lia)) as (fb & Hfb).
    (* the release *)
    eapply evtF_cut.
    { eapply lay_F_R3_release with (frb := frb) (fa := fs_flag FS 1 j);
        [ lia | lia | lia | lia | exact FB3 | exact FWa | exists fb; exact Hfb | exact MI3 | exact R120 | exact RFA ]. }
    intros ms4 (a0'' & m4 & -> & MU4 & WM4 & RM4 & MI4 & HF4).
    apply evtF_done. unfold lay_F_R3_end.
    exists z1, z5, z6, z7, a0'', z11, z12, z13, z14, z15, z16, z17, z19, z20, z21, z22, z23, z28, z29, z30, z31,
      mc1, gj1, m3, m4.
    split; [reflexivity|]. split; [exact MU1|]. split; [exact FI2|]. split; [exact LC2|].
    split; [exact MU3|]. split; [exact WM3|]. split; [exact RM3|].
    split; [exact MU4|]. split; [exact WM4|]. split; [exact RM4|]. split; [exact MI4|]. split; [exact HF4 | reflexivity].
  Qed.

End L5R.


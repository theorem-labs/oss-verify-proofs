(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 517 of its 532 lines of code are new or changed and 233 lines of the source are left out. *)
(* ctrl_lay_block, image A (asan, entry 0x855f4): RE-BASED copy of stretch k = 2 for region R2 of the cgif glue
   (0x8566c -> 0x85718 -> the box call 0x85824), plus the box call's `jal` (0x85824).  A Theorem Labs lane.

   WHY A COPY (re-base plan ctrl_lay_block-rebase.md sections 1, 4 (a working note, not in this delivery)).
   Every stretch lemma is closed over Section L's memory variable `m`, so the glue re-bases a stretch by applying it
   with m := normalize m_R, the cut's return memory (no copy needed for that).  What the glue also needs is the
   EXACT write set of the region's run, for the journal step (ProgWorld.v ajournal_of_fsteps_stmt :262-274: every
   byte of the munch set must be an awr_byte, YCbq.v:460-464).  ctrl_lay_block_F_2.v's post carries only LC's coarse
   set [(p+18,p+50); (S-K,S)] ++ lay_X (ctrl_lay_block.v:557, :924), which contains the class-0/1 hint words, flag
   arrays, other frames and the window's shadow (not awr).  The exact set is computed inside the proof
   (ctrl_lay_block_F_2.v:370-375, `MUd`) and cleared at :452.  This copy keeps MUd and adds it to the post:
       munch [(S - K, S); (frb, frb + 24); (frb / 8 + ASAN_K, frb / 8 + ASAN_K + 12); (p + 18, p + 50)] mc mc'
   where mc is the stretch's pre memory (the region's base).  Every byte is awr: the window, the own class-1 frame
   and its shadow (in_frames own after the malloc), and the output block (twr_ok).

   DIFF AGAINST ctrl_lay_block_F_2.v (not in this delivery; for the auditor a Theorem Labs lane; instruction proofs VERBATIM):
   - Section F2 -> F2R; lay_F_disp_post -> lay_F_R2_disp_post (one more parameter mc0, one more conjunct
     `munch ... mc0 mc'`); lay_F_2_fwords -> lay_F_R2_fwords; lay_F_2 -> lay_F_R2.
   - lay_F_R2_fwords: `clear MUd MUe MUp MUc SUBms.` (F_2:452) -> `clear MUe MUp MUc SUBms.`; the final
     `split; [exact LCc | exact AMm]` -> `split; [exact LCc | split; [exact AMm | exact MUd]]`.
   - lay_F_R2: `apply (lay_F_2_fwords ...` -> `apply (lay_F_R2_fwords ...`.  The four steps before it write no memory,
     so its pre memory is fwords' pre memory.
   - lay_F_2_of_F is not copied (the copy's statement adds a conjunct; the _of_F check of record stays F_2's).
   - New: lay_F_R2_jal, the `jal 85b44 <reac_box_model_block>` at 0x85824 (ctrl_lay_block.v ly_boxcall at head :4098-4100,
     the fourth `step`), which no stretch takes: one `step`, no data access, memory unchanged.
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
   - copied from ctrl_lay_block_F_2.v (not in this delivery) (a working branch c269486c810, merged 9d33dba1444), itself re-run
     from ctrl_lay_block.v (from a working branch d69f7c708f6; at head lib/A/Prog/ctrl_lay_block.v: ly_pro_go :3091-3092, fwords :2613-2848,
     ly_kb :2850-2887; ly_boxcall :4098-4100 for the jal). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import ctrl_lay_block_F_common.
(* Coq's Import is not transitive and the skeleton requires without exporting, so its Require list is repeated
   here, in the skeleton's order (lib.Lib ExecF StepF LAST, so StepF's step / if_false / finish / store_done
   shadow the evt engine's).  COMMON-CANDIDATE: the skeleton could `Require Export` instead. *)
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
(* stretch k = 3, Required qualified (the region run below composes it) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ctrl_lay_block_F_3.
(* Local copy of ctrl_lay_block.v:215's store hook: the base made it Local (a Theorem Labs lane c9390e308b8); this file's rd_mono steps need it. *)
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

(* The `jal 85b44 <reac_box_model_block>` at 0x85824 (ctrl_lay_block.v ly_boxcall :3955-3957: the fourth `step`,
   which takes the jal; the stretch k = 3 stops before it).  ra := 0x85828, pc := 0x85b44 (REAC_BOX_MODEL_BLOCK),
   every other register and the memory unchanged; no data access, so any footprint. *)
Lemma lay_F_R2_jal : forall (RNG : ExecF.footprint)
    (xra x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
     x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mc : word -> option byte),
  ExecF.evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x85828) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
                              x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None mc (seg_rom rsegs))
    (MS (mkR xra x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Z_to_bv 64 0x85824) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG xra x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc mc.
  step.
  apply ExecF.evtF_done. unfold REAC_BOX_MODEL_BLOCK. reflexivity.
Qed.

Section F2R.
  (* Section L's variables and hypotheses of ctrl_lay_block.v, verbatim, except that the four callee contracts
     (HSM, MEMS, MEMC, BOX) are replaced by the ONE this stretch applies: asan_memset_contract_F, of exactly
     a Theorem Labs lane's type (lib/A/Prog/asan_memset_cF.v), by name, never restated. *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr ob tb mb nb gb : list byte).

  Local Notation S := (bv_unsigned sp).
  Local Notation K := CTRL_LAY_BLOCK_K.

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

  (* The ONE callee contract this stretch applies, as a Section hypothesis of exactly its type. *)
  Hypothesis MEMSF : asan_memset_contract_F.

  Local Notation SP2 := ((S - 128) / 32 * 32).

  (* ---- Section L's predicates and helpers, at this section's variables (nothing is restated) ---- *)
  Local Notation FKx := (FK sp FS).
  Local Notation WfX := (Wf sp FS).
  Local Notation SAVESx := (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).
  Local Notation lay_Xx := (lay_X sp FS).
  Local Notation BIx := (BI ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS).
  Local Notation MEx := (ME ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS fr).
  Local Notation FIx := (FI sp tp p f FS).
  Local Notation LCx := (LC ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS fr).
  Local Notation SP2_factsx :=
    (SP2_facts sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg SP16 FL K9 TM P0 MDP).
  Local Notation STW0x := (STW0 sp m ST0).
  Local Notation fk_factsx :=
    (fk_facts sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg SP16 ST0 FL K9 TM P0 MDP SR0 HHM HAE AW0 FP0).
  Local Notation lay_Wf_subx :=
    (lay_Wf_sub sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg SP16 ST0 FL K9 TM P0 MDP SR0 HHM HAE AW0 FP0).
  Local Notation lay_row_out_Wfx :=
    (lay_row_out_Wf sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg SP16 ST0 DJ1 FL K9 TM P0 MDP SR0 HHM HAE AW0 AR FP0).
  Local Notation lay_addr_keepx :=
    (lay_addr_keep sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg SP16 FL K9 TM P0 MDP HHM AR FP0).
  Local Notation lay_fw_rtx :=
    (lay_fw_rt sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg SP16 ST0 FL K9 TM P0 MDP SR0 HHM HAE AW0 AR FP0).
  Local Notation lay_acx :=
    (lay_ac sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg FL K9 TM P0 MDP AC0 HHM ARDJ FP0).
  Local Notation lay_f_outx :=
    (lay_f_out sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg DJ2 FL K9 TM P0 DB1 MDP HHM HAE AF FP0).
  Local Notation lay_out_fpw_dx := (lay_out_fpw_d sp tp m p f FS FP0).
  Local Notation LC_introx :=
    (LC_intro ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f md g FS fr mb nb Rp Rf Rmd Rg DJ3m DB3 DBN MDP ARDJ AMD FPM).
  Local Notation lay_rw_consx :=
    (lay_rw_cons sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg FL TM MDP).

  (* ---- the copy's post: lay_F_disp_post (ctrl_lay_block_F_2.v:175-184) plus the exact write set from the pre
     memory mc0 (MUd, ctrl_lay_block_F_2.v:370-375) ---- *)
  Definition lay_F_R2_disp_post (mc0 : word -> option byte) (frb sfr spc j : Z) (w120 : word)
      : machine_state -> Prop :=
    fun ms' => exists (mc : word -> option byte) (gj : list byte)
                      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      ms' = MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
                    x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f)
                    (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md) (Z_to_bv 64 p)
                    (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
                    x28 x29 x30 x31)
               F (Z_to_bv 64 0x85718) fc None mc (seg_rom rsegs) /\
      FIx mc frb sfr spc j w120 /\ LCx mc gj ly_zero /\ addressable mc (frb + 32) 32 /\
      munch [(S - K, S); (frb, frb + 24); (frb / 8 + ASAN_K, frb / 8 + ASAN_K + 12); (p + 18, p + 50)] mc0 mc.


  (* ---- this file's copies of Section L's Ltacs (they are Section-local there), over evtF ---- *)
  Ltac lay_wv :=
    let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii;
    first
      [ solve [ match goal with
                | SW : forall i, 0 <= i < 12 -> wview rsegs m (wa (?sb + i)) <> None |- wview _ _ (wa ?x) <> None =>
                    replace x with (sb + (x - sb)) by lia; apply SW; lia end ]
      | solve [ match goal with
                | FW : forall i, 0 <= i < 96 -> wview rsegs m (wa (?fb + i)) <> None |- wview _ _ (wa ?x) <> None =>
                    replace x with (fb + (x - fb)) by lia; apply FW; lia end ]
      | solve [ apply STW0x; unfold CTRL_LAY_BLOCK_K in *; lia ]
      | match goal with |- ?G => fail 100 "WVFAIL" G end ].
  Ltac wst a n :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) n = true)
          by (eapply wv_store_ok; [ lay_wv | eassumption | lia | lia ])
    end.

  (* ---- 0x8569c -> 0x85718 (fwords :2491-2721, then ly_kb :2723-2755 for the DISP_T bundle) ---- *)
  Lemma lay_F_R2_fwords : forall (RNG : ExecF.footprint) (frb sfr spc j n : Z) (w120 : word)
      (mc : word -> option byte)
      (xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    FKx frb sfr spc j w120 -> 0 <= n <= 1 -> (n = 0 \/ 0 <= j < fs_M 1) ->
    BIx (WfX frb j n) frb sfr w120 mc ->
    RngBytes.rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (S - K) K ->
    ExecF.rng RNG frb 24 ->
    ExecF.rng RNG (shadow_addr frb) 16 ->
    ExecF.rng RNG (spc - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG (p + 18) 32 ->
    sh_word_rng RNG (p + 18) 32 ->
    sh_word_rng RNG (spc - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.evtF rsegs RNG (lay_F_R2_disp_post mc frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) s5 (Z_to_bv 64 md) (Z_to_bv 64 p)
                 s8 (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x8569c) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG frb sfr spc j n w120 mc xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      HK Hn Hnj HB RBY RIMG RSTK RFRB RFSH RMSK RROW RROWS RMSKS.
    pose proof SP2_factsx as (SP2m & SP2lo & SP2hi).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_factsx frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & Hspc & FW & FAP & FRA & SW12 & SHlo & SHhi).
    unfold LOWMEM_END in SHlo. unfold HIGHMEM_BEG in SHhi.
    assert (SHub : frb / 8 + ASAN_K + 12 <= 2 ^ 64) by lia.
    assert (S8 : S mod 8 = 0) by (pose proof SP16 as H16; clear -H16; Z.div_mod_to_equations; lia).
    assert (SKv : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    assert (Rfrb : 0 <= frb < 2 ^ 64).
    { pose proof (FAP 0 ltac:(lia)) as Hap0. rewrite Z.add_0_r in Hap0.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap0. lia. }
    assert (Rspc : 0 <= spc < 2 ^ 64) by (destruct Hspc as [E|E]; rewrite E; lia).
    (* the frame-shadow range premise in the form the stores take it (shadow_addr frb = frb / 8 + ASAN_K) *)
    pose proof RFSH as RFSH'. unfold shadow_addr in RFSH'.
    destruct HB as (MU & WM & RM & MI & SV & F120 & AWc & FPc & TLc).
    pose proof (stk_mono m mc (S - K) S ST0 WM RM) as STK.
    unfold Wf in MU. unfold shadow_addr in MU.
    pose proof (munch_refl [(S - K, S); (frb, frb + 24); (frb / 8 + ASAN_K, frb / 8 + ASAN_K + 12)] mc) as MUc.
    pose proof (wmono_refl rsegs mc) as WMc. pose proof (rd_mono_refl mc) as RMc.
    (* window store at SP2 + 24 *)
    assert (HSw : store_ok rsegs mc (wa (SP2 + 24)) 8 = true)
      by (eapply wv_store_ok; [ intros ii Hii; apply STW0x; unfold CTRL_LAY_BLOCK_K in *; lia
                              | exact WM | lia | lia ]).
    step. store_done.
    do 7 step.
    wst frb 8%nat. step. store_done.
    wst (frb + 8) 8%nat. step. store_done.
    wst (frb + 16) 8%nat. step. store_done.
    step. step.
    rewrite (unsigned_lit frb) by lia. rewrite rc_shr3.
    wst (frb / 8 + ASAN_K) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 1) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 2) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 3) 1%nat. step. store_done.
    step.
    wst (frb / 8 + ASAN_K + 8) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 9) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 10) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 11) 1%nat. step. store_done.
    step.
    (* capture the 8 frame-shadow cells so the 4 middle zeros survive for the box addressability. *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      assert (RDB : forall jj, 0 <= jj < Z.of_nat 8 ->
                      exists b, mrd rsegs mg (wa (frb / 8 + ASAN_K + jj)) = Some b) end.
    { intros jj Hjj. apply RM.
      pose proof (FAP (8 * jj) ltac:(lia)) as Hap.
      pose proof (proj2 (SR0 (shadow_addr (frb + 8 * jj)) (rt_app_shadow (frb + 8 * jj) Hap))) as [bb Hbb].
      exists bb. replace (frb / 8 + ASAN_K + jj) with (shadow_addr (frb + 8 * jj)); [exact Hbb|].
      rewrite sh_add8 by exact FR8. unfold shadow_addr. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      destruct (lay_bytes_exist mg 8%nat (frb / 8 + ASAN_K) ltac:(lia) ltac:(lia) RDB) as (bs8 & Lbs8 & HB4) end.
    do 8 (destruct bs8 as [|? bs8]; [cbn in Lbs8; lia|]). destruct bs8; [|cbn in Lbs8; lia].
    wst (frb / 8 + ASAN_K + 4) 1%nat. step.
    apply (bytes_at_write_inside rsegs _ (frb / 8 + ASAN_K) _ 4 (le1 (Z_to_bv 64 0))) in HB4;
      [| lia | rewrite length_le1; cbn [length]; lia].
    rewrite ?le1_lit_byte in HB4.
    store_done. change (Z.to_nat 4) with 4%nat in HB4.
    cbn [upd_bytes firstn skipn app length Nat.add Nat.sub le1 Z_to_le_bytes] in HB4.
    wst (frb / 8 + ASAN_K + 5) 1%nat. step.
    apply (bytes_at_write_inside rsegs _ (frb / 8 + ASAN_K) _ 5 (le1 (Z_to_bv 64 0))) in HB4;
      [| lia | rewrite length_le1; cbn [length]; lia].
    rewrite ?le1_lit_byte in HB4.
    store_done. change (Z.to_nat 5) with 5%nat in HB4.
    cbn [upd_bytes firstn skipn app length Nat.add Nat.sub le1 Z_to_le_bytes] in HB4.
    wst (frb / 8 + ASAN_K + 6) 1%nat. step.
    apply (bytes_at_write_inside rsegs _ (frb / 8 + ASAN_K) _ 6 (le1 (Z_to_bv 64 0))) in HB4;
      [| lia | rewrite length_le1; cbn [length]; lia].
    rewrite ?le1_lit_byte in HB4.
    store_done. change (Z.to_nat 6) with 6%nat in HB4.
    cbn [upd_bytes firstn skipn app length Nat.add Nat.sub le1 Z_to_le_bytes] in HB4.
    wst (frb / 8 + ASAN_K + 7) 1%nat. step.
    apply (bytes_at_write_inside rsegs _ (frb / 8 + ASAN_K) _ 7 (le1 (Z_to_bv 64 0))) in HB4;
      [| lia | rewrite length_le1; cbn [length]; lia].
    rewrite ?le1_lit_byte in HB4.
    store_done. change (Z.to_nat 7) with 7%nat in HB4.
    cbn [upd_bytes firstn skipn app length Nat.add Nat.sub le1 Z_to_le_bytes] in HB4.
    do 3 step.
    step.
    (* now at ASAN_MEMSET (0x524c4): the checked memset of the row [p+18, p+50), through the _F contract. *)
    pose proof (lay_Wf_subx frb sfr spc j n w120 HK Hn Hnj) as SUBf. unfold Wf, shadow_addr in SUBf.
    pose proof (munch_weaken _ _ _ _ SUBf MU) as MUe.
    pose proof (lay_acx _ _ MU SUBf) as AC1.
    pose proof (shadow_rw_mono m _ SR0 WM RM) as SR1.
    pose proof (acl_rw _ m _ (p + 18) [CB 32 ob] BLK MU WM
                  ltac:(intros x Hx; cbn [cells_size csize Nat.add] in Hx; change (Z.of_nat 32) with 32 in Hx;
                        apply (lay_row_out_Wfx frb sfr spc j n w120 x HK Hn Hnj); lia)) as RW1.
    pose proof (lay_addr_keepx _ (p + 18) (p + 50) (p + 18) 32 MUe
                  ltac:(right; left; reflexivity) AR ltac:(lia) ltac:(lia)
                  ltac:(unfold ly_dj in DJ1; unfold CTRL_LAY_BLOCK_K in *; lia)
                  ltac:(unfold ly_dj in DJ1; unfold CTRL_LAY_BLOCK_K in *; lia)) as AD1.
    assert (SPCr : S - 256 <= spc <= S - 128)
      by (destruct HK as [(_ & _ & Esp) | (_ & _ & _ & Esp & _)]; subst spc; lia).
    destruct (stk_split rsegs _ (S - K) spc S STK ltac:(unfold CTRL_LAY_BLOCK_K in *; lia)) as [STKlo STKhi].
    assert (Ed : bv_unsigned (Z_to_bv 64 (p + 18)) = p + 18) by (apply unsigned_lit; lia).
    assert (Ev : bv_unsigned (Z_to_bv 64 0) = 0) by (apply unsigned_lit; lia).
    assert (En : bv_unsigned (Z_to_bv 64 32) = 32) by (apply unsigned_lit; lia).
    assert (Es : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; lia).
    pose proof MEMSF as HM. unfold asan_memset_contract_F, ASAN_MEMSET_K in HM. cbv zeta in HM.
    eapply ExecF.evtF_cut.
    { eapply (HM RNG) with (lo := S - K) (junk := ob).
      all: rewrite ?Ed, ?Ev, ?En, ?Es.
      - change (Z.to_nat 32) with 32%nat. exact RW1.
      - lia.
      - exact AD1.
      - right. replace (p + 18 + 32) with (p + 50) by lia. exact AP50.
      - right. replace (p + 18 + 7) with (p + 18 + 7) by lia.
        exact (acl_app_in m (p + 18) 32 7 AR ltac:(lia)).
      - replace (p + 18 + 32) with (p + 50) by lia. exact ARDJ.
      - unfold ly_dj in DJ1. unfold CTRL_LAY_BLOCK_K in *.
        destruct DJ1 as [DJ|DJ]; [right | left]; lia.
      - exact STKlo.
      - unfold CTRL_LAY_BLOCK_K in *. lia.
      - exact HHM.
      - lia.
      - exact AC1.
      - exact SR1.
      - exact MI.
      - exact RBY.
      - exact RIMG.
      - exact RMSK.
      - exact RROW.
      - exact RROWS.
      - exact RMSKS. }
    intros ms' POST.
    destruct POST as (u0 & u1 & u2 & pa1 & pa2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & mp &
                      Ems & MUp & WMp & MIp & STp & RWp & ACp & SRp).
    subst ms'. rewrite ?Ed, ?Ev, ?En, ?Es in MUp. rewrite Es in STp. rewrite ?Ed, ?Ev, ?En in RWp.
    unfold ASAN_MEMSET_K in MUp. replace (p + 18 + 32) with (p + 50) in MUp by lia.
    replace (ret_pc (Z_to_bv 64 546584)) with (Z_to_bv 64 546584)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    lazymatch type of MUp with munch _ ?mg _ => assert (RMp : rd_mono mg mp) end.
    { apply (rd_mono_list _ _ _ MUp). constructor; [|constructor; [|constructor]]; cbn [fst snd].
      - intros y Hy. pose proof RWp as RWc. destruct RWc as [[_ HBrow] _].
        cbn [cells_bytes cbytes] in HBrow. rewrite app_nil_r in HBrow.
        apply (rd_of_bytes _ _ _ HBrow). rewrite repeat_length. clear -Hy. lia.
      - intros y Hy. apply (rd_of_stk _ _ _ STp). clear -Hy SPCr. unfold CTRL_LAY_BLOCK_K. lia. }
    assert (SUBms : sub_fp [(p + 18, p + 50); (spc - 2208, spc)] (ctrl_lay_block_W p S ++ lay_Xx)).
    { intros x Hx. unfold ctrl_lay_block_W, lay_X in Hx. apply acl_out_app_inv in Hx. destruct Hx as (HW & _).
      cbn [outside] in HW. destruct HW as (Hwin & Hrow & _). cbn [outside].
      split; [exact Hrow|]. split; [clear -Hwin SPCr; unfold CTRL_LAY_BLOCK_K in *; lia | exact I]. }
    assert (MUd : munch [(S - K, S); (frb, frb + 24); (frb / 8 + ASAN_K, frb / 8 + ASAN_K + 12); (p + 18, p + 50)]
                    mc mp).
    { eapply munch_trans; [eapply munch_weaken; [|exact MUc] | eapply munch_weaken; [|exact MUp]].
      - intros x Hx. cbn [outside] in Hx |- *. tauto.
      - intros x (Hw & _ & _ & Hr & _). cbn [outside].
        split; [exact Hr | split; [clear -Hw SPCr; unfold CTRL_LAY_BLOCK_K in *; lia | exact I]]. }
    destruct (lay_fw_rtx frb sfr spc j w120 mc mp HK FPc TLc AWc MUd (wmono_trans rsegs _ _ _ WMc WMp)
                (rd_mono_trans _ _ _ RMc RMp)) as (FPp & TLp & AWp).
    (* ME at 0x85718, exactly as fwords hands it to KB *)
    assert (MEp : MEx frb sfr w120 mp).
    { unfold ME.
      split; [ eapply munch_trans; [exact MUe | eapply munch_weaken; [exact SUBms | exact MUp]] | ].
      split; [ eapply wmono_trans; [exact WM | exact WMp] | ].
      split; [ eapply rd_mono_trans; [exact RM | exact RMp] | ].
      split; [ exact MIp | ].
      split; [ exact ACp | ].
      split; [ exact SRp | ].
      split; [ exact (stk_mono _ mp (S - K) S STK WMp RMp) | ].
      split.
      { eapply rw_cells_transport; [exact SV | exact MUp | exact WMp |].
        cbn [disjoint_from cells_size csize Nat.add SAVES]. split; [|split; [|exact I]];
          clear -DJ1 SPCr; unfold ly_dj in DJ1; unfold CTRL_LAY_BLOCK_K in *; lia. }
      split; [ change ly_zero with (repeat (Z_to_bv 8 0) 32); exact RWp | ].
      split.
      { eapply fl_bytes;
          [ exact FB
          | eapply munch_trans; [exact MUe | eapply munch_weaken; [exact SUBms | exact MUp]]
          | intros x Hx; apply (lay_f_outx x); rewrite FL in Hx; lia ]. }
      split.
      { intros Hs. specialize (F120 Hs).
        destruct HK as [(E0 & _) | (Hj & Efr & _ & Esp & _)]; [exfalso; exact (Hs E0)|].
        replace (fs_M 1) with 8192 in Hj by reflexivity.
        pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFSlo & _ & _ & _).
        unfold FS_SIZE in P4, HFSlo.
        assert (B : fs_frame FS 1 0 <= frb /\ frb + 128 <= fs_frame FS 1 (fs_M 1) /\ frb + 128 <= FS + 2134016).
        { rewrite Efr. unfold fs_frame, fs_B, fs_M. cbn [Z.of_nat Pos.of_succ_nat].
          change (2 ^ 1) with 2. change (2 ^ (14 - 1)) with 8192. change (2 ^ 20) with 1048576. clear -Hj. lia. }
        destruct B as (B1 & B2 & B3).
        pose proof (P4 (frb + 120) ltac:(clear -B3 FRlo; lia)) as A120.
        pose proof (P4 (frb + 127) ltac:(clear -B3 FRlo; lia)) as A127.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A120, A127.
        pose proof (lay_out_fpw_dx (p + 18) (p + 50) (p + 18) ltac:(right; left; reflexivity) ltac:(clear; lia)) as O18.
        cbn [fp_w flat_map fp_w1 app outside] in O18. destruct O18 as (_ & _ & _ & _ & _ & _ & O18 & _).
        pose proof (bytes_at_transport rsegs _ _ _ _ _ F120 MUc) as F120a.
        rewrite length_le8 in F120a. change (Z.of_nat 8) with 8 in F120a. cbn [disjoint_from] in F120a.
        specialize (F120a ltac:(split; [|split; [|split; [|exact I]]]; clear -B3 HFSlo A120 A127 SHlo SHhi; lia)).
        pose proof (bytes_at_transport rsegs _ _ _ _ _ F120a MUp) as F120b.
        rewrite length_le8 in F120b. change (Z.of_nat 8) with 8 in F120b. cbn [disjoint_from] in F120b.
        apply F120b. split; [|split; [|exact I]]; clear -O18 B1 B2 B3 HFSlo SKv Esp SP2lo; lia. }
      split.
      { eapply lay_addr_keepx; [ eapply munch_trans; [exact MUe | eapply munch_weaken; [exact SUBms | exact MUp]]
                               | right; left; reflexivity | exact AR | lia | lia
                               | unfold ly_dj in DJ1; unfold CTRL_LAY_BLOCK_K in *; lia
                               | unfold ly_dj in DJ1; unfold CTRL_LAY_BLOCK_K in *; lia ]. }
      split.
      { eapply lay_addr_keepx; [ eapply munch_trans; [exact MUe | eapply munch_weaken; [exact SUBms | exact MUp]]
                               | left; reflexivity | exact AF | lia | lia
                               | unfold ly_dj in DJ2; unfold CTRL_LAY_BLOCK_K in *; lia
                               | unfold ly_dj in DJ2, DB1; unfold CTRL_LAY_BLOCK_K in *; lia ]. }
      split.
      { pose proof (acl_app_in m (p + 18) 32 0 AR ltac:(lia)) as Ap18u. rewrite Z.add_0_r in Ap18u.
        pose proof AP50 as AP50u.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ap18u, AP50u.
        cbn [upd_bytes firstn skipn length Nat.add Nat.sub] in HB4.
        pose proof (bytes_at_transport rsegs _ _ mp _ _ HB4 MUp
                      ltac:(cbn [disjoint_from fst snd length]; change (Z.of_nat 8) with 8;
                            split; [|split; [|exact I]]; clear -Ap18u AP50u SHlo SHhi HHM' SKv SPCr; lia)) as HB4p.
        lazymatch type of HB4p with bytes_at _ _ _ (?x0 :: ?x1 :: ?x2 :: ?x3 :: ?rest) =>
          pose proof (proj2 (proj1 (bytes_at_app rsegs mp (frb / 8 + ASAN_K) [x0; x1; x2; x3] rest) HB4p)) as HB4s end.
        cbn [length] in HB4s. change (Z.of_nat 4) with 4 in HB4s.
        try rewrite (unsigned_lit 0) in HB4s by (clear; lia).
        apply (lay_addr_zero mp (frb + 32) 32 4).
        - clear -Rfrb. lia.
        - clear -FR8. Z.div_mod_to_equations. lia.
        - clear. lia.
        - clear -FRhi SP2hi HAE'. unfold APPMEM_END. lia.
        - intros i Hi. replace (frb + 32 + i) with (frb + (32 + i)) by (clear; lia). apply FAP. clear -Hi. lia.
        - replace (shadow_addr (frb + 32)) with (frb / 8 + ASAN_K + 4)
            by (clear -FR8; unfold shadow_addr; Z.div_mod_to_equations; lia).
          exact HB4s. }
      split; [exact FPp|]. split; [exact TLp | exact AWp]. }
    (* ly_kb (:2723-2755): ME and FK give the DISP_T bundle *)
    clear MUe MUp MUc SUBms.
    destruct MEp as (MUm & WMm & RMm & MIm & ACm & SRm & STKm & SVm & RWm & FBm & F120m & ADrm & ADfm & AMm
                     & FPm & TLm & AWom).
    destruct (stk_split rsegs mp (S - K) (S - 96) S STKm ltac:(unfold CTRL_LAY_BLOCK_K in *; lia)) as [STlo _].
    destruct (stk_carve rsegs mp (S - K) (S - 96) 32 STlo ltac:(change (Z.of_nat 32) with 32;
                unfold CTRL_LAY_BLOCK_K in *; lia)) as [STc [gj Hgj]].
    change (Z.of_nat 32) with 32 in STc, Hgj.
    assert (LCc : LCx mp gj ly_zero).
    { apply LC_introx.
      - replace (bv_unsigned sp + -128) with (S - 96 - 32) by lia.
        apply lay_rw_consx; [exact Hgj|]. cbn [csize]. change (Z.of_nat 32) with 32.
        replace (S - 96 - 32 + 32) with (S - 96) by lia. exact SVm.
      - replace (bv_unsigned sp + -128) with (S - 96 - 32) by lia. exact STc.
      - eapply munch_weaken; [|exact MUm]. intros x Hx. unfold ctrl_lay_block_W. cbn [outside app] in Hx |- *.
        tauto.
      - exact WMm.
      - exact MIm.
      - exact RWm.
      - exact FBm. }
    assert (FIc : FIx mp frb sfr spc j w120).
    { split; [exact HK|]. split; [exact F120m|]. split; [exact ACm|]. split; [exact SRm|].
      split; [exact FPm|]. split; [exact TLm | exact AWom]. }
    apply ExecF.evtF_done. unfold lay_F_R2_disp_post.
    do 18 eexists.
    split; [reflexivity | ]. split; [exact FIc | ]. split; [exact LCc | split; [exact AMm | exact MUd]].
  Qed.


  (* ---- 0x8566c -> 0x85718: ly_pro_go's side-frame arm (:2967-2968) and the stretch above ---- *)
  Lemma lay_F_R2 : forall (RNG : ExecF.footprint) (frb sfr spc j : Z) (w120 : word) (mc : word -> option byte)
      (xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    FKx frb sfr spc j w120 -> sfr <> 0 -> 0 <= j < fs_M 1 ->
    BIx (WfX frb j 1) frb sfr w120 mc ->
    RngBytes.rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (S - K) K ->
    ExecF.rng RNG frb 24 ->
    ExecF.rng RNG (shadow_addr frb) 16 ->
    ExecF.rng RNG (spc - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG (p + 18) 32 ->
    sh_word_rng RNG (p + 18) 32 ->
    sh_word_rng RNG (spc - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.evtF rsegs RNG (lay_F_R2_disp_post mc frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
                 (Z_to_bv 64 frb) a1' a2' a3' a4' a5' a6' a7'
                 s2 (Z_to_bv 64 g) (Z_to_bv 64 f) s5 (Z_to_bv 64 md) (Z_to_bv 64 p)
                 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x8566c) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG frb sfr spc j w120 mc xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      HK Hs Hj HB RBY RIMG RSTK RFRB RFSH RMSK RROW RROWS RMSKS.
    pose proof SP2_factsx as (SP2m & SP2lo & SP2hi).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_factsx frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & Hspc & FW & FAP & FRA & SW12 & SHlo & SHhi).
    assert (Rfrb : 0 < frb < 2 ^ 64).
    { pose proof (FAP 0 ltac:(lia)) as Hap0. rewrite Z.add_0_r in Hap0.
      pose proof FP0 as (_ & _ & _ & _ & _ & _ & _ & _ & (P1 & _) & _).
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap0. lia. }
    (* the side-frame arm: FK's second disjunct (the a0 = 0 arm is the glue's, refuted by the room premise) *)
    assert (Esfr : sfr = frb /\ spc = SP2)
      by (destruct HK as [(E0 & _) | (_ & _ & E1 & E2 & _)]; [exfalso; exact (Hs E0) | split; [exact E1 | exact E2]]).
    destruct Esfr as (Esfr & Espc). subst sfr. subst spc.
    (* 0x8566c mv s2,a0 ; 0x85670 j ; 0x85678 mv s9,s2 ; 0x8567c bnez s2 *)
    step. step. step. step.
    rewrite (rc_neq0_64 frb) by lia. cbn [negb]. cbv iota.
    apply (lay_F_R2_fwords RNG frb frb SP2 j 1 w120 mc xra t0' t1' t2' (Z_to_bv 64 frb) a1' a2' a3' a4' a5' a6' a7'
             t3' t4' t5' t6');
      [ exact HK | lia | right; exact Hj | exact HB | exact RBY | exact RIMG | exact RSTK | exact RFRB
      | exact RFSH | exact RMSK | exact RROW | exact RROWS | exact RMSKS ].
  Qed.

  (* ---- the region's whole run (0x8566c -> the callee's entry 0x85b44, ra = 0x85828): lay_F_R2, then stretch
     k = 3 (ctrl_lay_block_F_3.v ctrl_lay_block_F_3, the 3 <= k <= 9 dispatch and the box-call moves), then
     lay_F_R2_jal.  The glue lifts this ONE run with Section L's memory m := normalize m1 (m1 = the return memory of
     __asan_stack_malloc_1).  k = 3 and the jal keep the memory, so the write set is k = 2's (MUd). ---- *)
  Definition lay_F_R2_box_pre (mc0 : word -> option byte) (frb sfr spc j : Z) (w120 : word)
      : machine_state -> Prop :=
    fun ms' => exists (mc : word -> option byte) (gj : list byte)
                      (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      ms' = MS (mkR (Z_to_bv 64 0x85828) (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
                    (Z_to_bv 64 md) (Z_to_bv 64 (ly_bb (ly_k fr))) (Z_to_bv 64 (frb + 32))
                    x13 x14 x15 x16 x17
                    (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md)
                    (Z_to_bv 64 (frb + 32)) (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb)
                    (Z_to_bv 64 ASAN_K) s11 x28 x29 x30 x31)
               F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None mc (seg_rom rsegs) /\
      FIx mc frb sfr spc j w120 /\ LCx mc gj ly_zero /\ addressable mc (frb + 32) 32 /\
      munch [(S - K, S); (frb, frb + 24); (frb / 8 + ASAN_K, frb / 8 + ASAN_K + 12); (p + 18, p + 50)] mc0 mc.

  Lemma lay_F_R2_run : forall (RNG : ExecF.footprint) (frb sfr spc j : Z) (w120 : word) (mc : word -> option byte)
      (xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    FKx frb sfr spc j w120 -> sfr <> 0 -> 0 <= j < fs_M 1 ->
    BIx (WfX frb j 1) frb sfr w120 mc ->
    RngBytes.rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (S - K) K ->
    ExecF.rng RNG frb 24 ->
    ExecF.rng RNG (shadow_addr frb) 16 ->
    ExecF.rng RNG (spc - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG (p + 18) 32 ->
    sh_word_rng RNG (p + 18) 32 ->
    sh_word_rng RNG (spc - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG f 24 -> ExecF.rng RNG (shadow_addr f) 3 ->
    3 <= ly_k fr <= 9 ->
    ExecF.evtF rsegs RNG (lay_F_R2_box_pre mc frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
                 (Z_to_bv 64 frb) a1' a2' a3' a4' a5' a6' a7'
                 s2 (Z_to_bv 64 g) (Z_to_bv 64 f) s5 (Z_to_bv 64 md) (Z_to_bv 64 p)
                 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x8566c) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG frb sfr spc j w120 mc xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      HK Hs Hj HB RBY RIMG RSTK RFRB RFSH RMSK RROW RROWS RMSKS RF RSHF KB.
    eapply ExecF.evtF_cut.
    { exact (lay_F_R2 RNG frb sfr spc j w120 mc xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
               HK Hs Hj HB RBY RIMG RSTK RFRB RFSH RMSK RROW RROWS RMSKS). }
    intros ms1 (mc1 & gj & y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31
                & -> & FI1 & LC1 & AO1 & MU1).
    eapply ExecF.evtF_cut.
    { exact (ctrl_lay_block_F_3.ctrl_lay_block_F_3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
               p f md g FS fr tb mb nb gb Rp Rf Rmd Rg SP16 DJ2 F8 F24 FL K9 TM P0 MDP HHM AF AR FP0
               RNG mc1 gj frb sfr spc j w120 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31
               RSTK RF RSHF RIMG KB FI1 LC1 AO1). }
    intros ms2 (z1 & z5 & z6 & z7 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & -> & FI2 & LC2 & AO2 & _).
    eapply ExecF.evtF_cut; [apply lay_F_R2_jal |].
    intros ms3 ->. apply ExecF.evtF_done. unfold lay_F_R2_box_pre.
    exists mc1, gj, z5, z6, z7, z13, z14, z15, z16, z17, z28, z29, z30, z31.
    split; [reflexivity|]. split; [exact FI2|]. split; [exact LC2|]. split; [exact AO2 | exact MU1].
  Qed.


End F2R.


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 99 of its 112 lines of code are new or changed and 235 lines of the source are left out. *)
(* ctrl_lay_block, image A (asan, entry 0x855f4): stretch k = 1 of the footprint (_F) re-run of its proved v1.9
   run.  pc range 0x855f4 -> 0x85668; it ENDS AT THE CUT `jal 3d72c <__asan_stack_malloc_1>` (0x85668), which is
   the fake-stack allocator EVENT: this stretch does NOT take that instruction, so `ra` still holds the entry `ra`
   in the post state and the glue applies cgif's `astack_malloc_realizes segs B cid` for class 1 there (the a0 = 0
   arm is refuted by the room premise).
   Source of the script: lib/A/Prog/ctrl_lay_block.v `ly_pro_go` :2757-2996, script prefix :2763-2792; the last
   `step` of :2792 takes the jal and so belongs to the cut, not to this stretch.  Split of record:
   ctrl_lay_block-stretches.md (a working note, not in this delivery) ("none" inside the stretch:
   it contains no call at all).  Shared skeleton: lib/A/Prog/ctrl_lay_block_F_common.v.

   PROVENANCE (as the skeleton states it).
   - image root (internal path)
     -> (internal path)
   - ELF sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd
   - compare: the objdump listing shipped beside the image,
     fuzz_ctrl.objdump.txt (a working note, not in this delivery), ctrl_lay_block at 0x855f4 .. 0x85988;
     the 30 pcs of this stretch are 0x855f4, 0x855f8, 0x855fc .. 0x85628 (the 12 saves), 0x8562c, 0x85630,
     0x85634 .. 0x85660, 0x85664, and it stops at 0x85668
   - FACTS of record ed6b6b7b0ab (origin/regen/libreac-v190-on-338), PAU (internal path)
   - the stretch is re-run from ctrl_lay_block.v at a working branch d69f7c708f6

   ROUTE (a) CONDITIONS (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z, via a Theorem Labs lane) -- they bind this file:
   1. Each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and no
      new proof obligation.
   2. The _F output feeds ONLY the ported cgif-form walk.  No W_cutfree_ok, no cut-free twin, no LSCPS join, no
      top-level claim.
   3. The source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
      wrong-image cell.  The re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes: the four the
      stretch reads are GOT_UAR 0x9fb28 and GOT_CELL_K 0x9fad0 (the two GOT slots the auipc pair addresses at
      0x8564c and 0x85650) and the runtime words they point at, UAR 0xa8880 and CELL_K 0xa8878.
   4. Every _F carries provenance in its header and goes to the auditor a Theorem Labs lane
      who signs it against its proved run before it counts.
   5. A StepF "footprint: access <a> width <n> not covered by any [rng] hypothesis" error means STOP and report it:
      never widen the footprint to make it pass. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import ctrl_lay_block_F_common.

(* COMMON-CANDIDATE: ctrl_lay_block_F_common.v uses `Require Import`, and Import is not transitive, so the
   skeleton's Require list has to be repeated here, in the skeleton's order (lib.Lib ExecF StepF LAST, so StepF's
   step / if_false / finish / store_done shadow the evt engine's).  Making the skeleton's Requires
   `Require Export` would delete this block from every stretch file.  Nobody edits the skeleton. *)
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
Section K1.
  (* Section L's variables, as far as this stretch names them (ctrl_lay_block.v :404-405). *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g : Z).

  Local Notation S := (bv_unsigned sp).
  Local Notation K := CTRL_LAY_BLOCK_K.
  Local Notation SP2 := ((S - 128) / 32 * 32).

  (* Section L's hypotheses this stretch uses, by name and of exactly their type: ctrl_lay_block.v :415 ST0,
     :446 MI0, :448 AC0, :450 HHM, :451 HAE.  No stretch-only hypothesis is added. *)
  Hypothesis ST0 : stk rsegs m (S - K) S.
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis HHM : HIGHMEM_BEG <= S - K.
  Hypothesis HAE : S <= APPMEM_END.

  (* The post of this stretch, at the cut pc 0x85668 (= 546408): the state ly_pro_go has built when it is about to
     take the class-1 frame request.  a0 = 96 (the frame size L), sp = s1 = SP2, s0 = the entry sp, s3 = g, s4 = f,
     s6 = md, s7 = p, s10 = ASAN_K; ra and s2 s5 s8 s9 s11 are the entry ones (the jal is NOT taken here); the
     memory holds the 13 prologue stores and carries the facts ly_pro_go has at :2768-2771 and from carve_frame.
     Writing it over the section variables is ctrl_lay_block.v's own convention at a stage boundary (KB :596-600,
     fwords :2495-2499 put the entry `sp` in the s0 slot). *)
  Definition lay_F_pre_smalloc : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (mg : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 SP2) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
                    (Z_to_bv 64 96) a1' a2' (Z_to_bv 64 g) a4' a5' a6' a7'
                    s2 (Z_to_bv 64 g) (Z_to_bv 64 f) s5 (Z_to_bv 64 md) (Z_to_bv 64 p) s8 s9
                    (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
               F (Z_to_bv 64 546408) fc None mg (seg_rom rsegs) /\
      munch [(S - K, S)] m mg /\ wmono rsegs m mg /\ rd_mono m mg /\ mem_inv rsegs mg /\
      rw_cells rsegs mg (S - 96) (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).

  (* The rng premises are the plan's row k = 1: the stack window [S - K, S) of the stk premise (the 13 stores),
     and the four runtime cells the two auipc/ld pairs read, as their 8- or 4-byte ranges.  The stretch reads no
     image constant (the jump table at 0x211b4 belongs to k = 3 / k = 4), so there is no image range here. *)
  Lemma ctrl_lay_block_F_1 : forall (RNG : ExecF.footprint),
    ExecF.rng RNG (S - K) K -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG GOT_UAR 8 -> ExecF.rng RNG UAR 4 ->
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m0 : word -> option byte), m0 = m ->
    ExecF.evtF rsegs RNG lay_F_pre_smalloc
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 g)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m0 (seg_rom rsegs)).
  Proof.
    intros RNG RWIN RGCK RCK RGUA RUA t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m0 Em0.
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in RGCK, RCK, RGUA, RUA.
    (* ---- ly_pro_go :2763-2792, verbatim apart from the SP2_facts step below ---- *)
    unfold CTRL_LAY_BLOCK.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (SP2f : SP2 mod 32 = 0 /\ S - 160 <= SP2 <= S - 128) by (Z.div_mod_to_equations; lia).
    destruct SP2f as (SP2m & SP2lo & SP2hi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    assert (MU : munch [(S - K, S)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    destruct (stk_split rsegs m0 _ (S - 128) _ ST0c ltac:(lia)) as [STa STb]. clear ST0c.
    carve_frame 96%nat STb.
    step.
    assert (HS0 : store_ok rsegs m0 (wa (S + -128)) 8 = true).
    { eapply wv_store_ok; [ | apply wmono_refl | lia | lia]. intros i Hi.
      apply (stk_wv m0 (S - 128) (S + -96)); [exact STb | lia]. }
    step. store_done.
    do 12 step.
    step. step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = SP2)
      by (rewrite unsigned_lit, land_align32 by lia; f_equal; f_equal; lia).
    rewrite EA.
    (* s0 = sp (the entry sp), s1 = sp = SP2 *)
    do 12 step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step.
    (* ---- 0x85668: the cut.  ly_pro_go's :2792 second `step` takes the jal; this stretch stops here. ---- *)
    apply evtF_done. unfold lay_F_pre_smalloc.
    replace (S - 96) with (S + -96) by lia.
    do 14 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI | exact FR].
  Qed.

  (* The recipe's step 4: the _F statement is the old one plus footprint premises, nothing weaker. *)
  Corollary ctrl_lay_block_F_1_of_F :
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m0 : word -> option byte), m0 = m ->
    Exec.evt rsegs lay_F_pre_smalloc
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 g)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m0 Em0.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END, CTRL_LAY_BLOCK_K in HHM', HAE'.
    eapply evtF_evt. eapply (ctrl_lay_block_F_1 ExecF.RNG_all).
    - unfold CTRL_LAY_BLOCK_K. lay_F_all.
    - unfold GOT_CELL_K. lay_F_all.
    - unfold CELL_K. lay_F_all.
    - unfold GOT_UAR. lay_F_all.
    - unfold UAR. lay_F_all.
    - exact Em0.
  Qed.

End K1.

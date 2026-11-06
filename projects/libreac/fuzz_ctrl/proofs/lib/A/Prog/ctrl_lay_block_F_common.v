(* ctrl_lay_block, image A (asan, entry 0x855f4): the SHARED SKELETON of the footprint (_F) re-run of its proved
   v1.9 run.  This file holds only what every stretch file needs: the Require / Import order (lib.Lib ExecF StepF
   LAST, so StepF's step / if_false / finish / store_done shadow the evt engine's), the provenance header, and the
   few helper restatements the stretch scripts share.  The stretches themselves live one per file in
   lib/A/Prog/ctrl_lay_block_F_<k>.v (one writer per file); the split of record, with the pc range, the source lemma
   and script lines, the boundary call and the rng premises of each stretch, is
   ctrl_lay_block-stretches.md (a working note, not in this delivery).
   ctrl_lay_block.v itself is unchanged apart from comment text; its own theorem still uses it.

   WHY THE FUNCTION IS SPLIT, AND WHERE.  The run calls __asan_stack_malloc_1 (0x85668), so it is not one silent
   run: that call is an allocator EVENT, and the cgif-form bridge lifts only silent runs.  The cuts are exactly the
   events (a Theorem Labs lane, 22:57Z):
     - 0x85668  jal 3d72c <__asan_stack_malloc_1>   -- the fake-stack allocator event
     - 0x85824  jal 85b44 <reac_box_model_block>    -- a program callee that itself takes a fake-stack frame
     - 0x858ec / 0x858f0  ld a0,120(s2) ; sb zero,0(a0)  -- the inline class-1 flag release
   The glue applies cgif's rule at each: astack_malloc_realizes (fake-frame arm; the a0 = 0 arm is refuted by the
   room premise), reac_box_model_block_contract, astack_free_law / frame_flag_lawP.
   The checked fill and copy helpers stay INSIDE a stretch: __asan_memset (0x85714) and __asan_memcpy (0x8583c and
   0x85880) are applied through a Theorem Labs lane's shared footprint contracts asan_memset_contract_F (lib/A/Prog/
   asan_memset_cF.v) and asan_memcpy_contract_F (lib/A/Prog/asan_memcpy_cF.v), taken as Section hypotheses of
   exactly their type and applied with NAMED arguments (RNG := ...).  No stretch file walks a runtime or libc
   callee, and no stretch file restates a runtime contract: musl and the ASan runtime are written once in the
   shared core, and a Theorem Labs lane owns and proves those two contracts.

   ROUTE (a) CONDITIONS (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z, via a Theorem Labs lane) -- they bind every stretch file:
   1. Each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and no
      new proof obligation.
   2. The _F output feeds ONLY the ported cgif-form walk.  No W_cutfree_ok, no cut-free twin, no LSCPS join, no
      top-level claim.
   3. The source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
      wrong-image cell.  The re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes.
   4. Every _F carries provenance in its header and goes to the auditor a Theorem Labs lane
      who signs it against its proved run before it counts.
   5. A StepF "footprint: access <a> width <n> not covered by any [rng] hypothesis" error means STOP and report it:
      never widen the footprint to make it pass.

   PROVENANCE.
   - image root (internal path)
     -> (internal path)
   - ELF sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd (sha256sum of that unstripped
     target; the stripped asan/fuzz_ctrl of the same tree has the same sha)
   - compare: the objdump listing shipped beside the image,
     fuzz_ctrl.objdump.txt (a working note, not in this delivery), ctrl_lay_block at 0x855f4 .. 0x85988
   - FACTS of record ed6b6b7b0ab (origin/regen/libreac-v190-on-338), PAU
     (internal path), built with zfactsbuild.sh
   - stretches re-run from ctrl_lay_block.v at a working branch d69f7c708f6 (4176 lines; Section L from
     :403; Theorem ctrl_lay_block_holds :4169)

   NOTE ON THE IMPORT ORDER (for the auditor).  F5F.v's `Import YK11` is deliberately NOT used here.  YK11 is the UL
   engine's register layer; F5F.v needs it because its runs are stated over Regs6ss.mkR_of / YK11.getr.
   ctrl_lay_block.v is a lib.Lib file: its states are MState.MS (Frame.mkR ...) and it never mentions getr, so
   importing YK11 would add a dependency the proved run does not have.  For the same reason there is no mkR_expand
   restatement in this file: Frame.mkR is already the register map StepF reads. *)

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
(* The two shared footprint contracts the stretches apply at the checked fill / copy calls: stated by their owner
   (a Theorem Labs lane, through a Theorem Labs lane's ctrl bridge e9f2c8f46ec), never restated here.  A stretch file takes
   asan_memset_contract_F / asan_memcpy_contract_F as Section hypotheses of exactly these types.  They bring
   ImgBounds (IMG_LO = 0x10000, IMG_HI = 0x5fe000) and RngBytes.rng_bytes with them. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF asan_memcpy_cF.

(* Last: StepF's step / if_false / finish / store_done (evtF goals) shadow the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The store_ok obligation of a store inside a present, writable stack window, in a memory that is write-monotone
   over the one the window is stated at.  Every stretch's stores into the function's window [S - K, S), into the
   frame [frb, frb + 96) and into the frame's shadow go through this (it is ctrl_lay_block.v's wv_store_ok with the
   per-byte side condition read off a stk premise, so the stretch scripts keep their own `wst` shape). *)
Lemma lay_F_stk_store_ok : forall (m m' : word -> option byte) (lo hi a : Z) (n : nat),
  stk rsegs m lo hi -> wmono rsegs m m' -> lo <= a -> a + Z.of_nat n <= hi ->
  store_ok rsegs m' (wa a) n = true.
Proof.
  intros m m' lo hi a n HS HW Ha Hb.
  pose proof HS as (Hlo & Hhi & _).
  eapply wv_store_ok; [ | exact HW | lia | lia ].
  intros i Hi. exact (stk_wv m lo hi (a + i) HS ltac:(lia)).
Qed.

(* The store_ok obligation of a store whose bytes are writable one by one at the base memory (the frame words and the
   frame-shadow bytes, whose writability comes from fk_facts' `forall i, 0 <= i < 96 -> wview ... <> None` and from
   shadow_rw, not from a stk premise). *)
Lemma lay_F_pw_store_ok : forall (m m' : word -> option byte) (base a : Z) (len : Z) (n : nat),
  (forall i, 0 <= i < len -> wview rsegs m (wa (base + i)) <> None) -> wmono rsegs m m' ->
  base <= a -> 0 <= a -> a + Z.of_nat n <= base + len -> a + Z.of_nat n <= 2 ^ 64 ->
  store_ok rsegs m' (wa a) n = true.
Proof.
  intros m m' base a len n HW HM Hba Ha Hn H64.
  eapply wv_store_ok; [ | exact HM | lia | lia ].
  intros i Hi. replace (a + i) with (base + (a - base + i)) by lia. apply HW. lia.
Qed.

(* Assert the store_ok fact for the store about to be taken, from a stk premise in the context.  The stretch files
   use this where ctrl_lay_block.v's Section-local `wst` used `lay_wv`; `lo` and `hi` name the window. *)
Ltac lay_F_wst_stk lo hi a n :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa a) n = true)
        by (eapply (lay_F_stk_store_ok _ mm lo hi a n); [ eassumption | eassumption | lia | lia ])
  end.

(* Discharge an `ExecF.rng RNG_all lo len` premise of an `_of_F` corollary. *)
Ltac lay_F_all := apply rng_all; lia.

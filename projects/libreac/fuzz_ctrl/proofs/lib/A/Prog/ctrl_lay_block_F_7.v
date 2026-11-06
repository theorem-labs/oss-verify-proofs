(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 182 of its 195 lines of code are new or changed and 235 lines of the source are left out. *)
(* ctrl_lay_block, image A (asan, entry 0x855f4): stretch k = 7 of the footprint (_F) re-run of its proved v1.9 run.
   Range 0x85884 -> 0x858ec; it ends at the CUT that is the inline class-1 flag release (ld a0,120(s2) at 0x858ec ;
   sb zero,0(a0) at 0x858f0), which the cgif-form glue covers with astack_free_law / frame_flag_lawP.  No call runs
   inside this stretch.

   SOURCE OF RECORD.  ctrl_lay_block.v (same text on this base; sha256
   853f889215408ed0e66499e73c9609cb98e889eb4b9a42c4db6fb8163462dbb8) lemma ly_epi_side :1387-1582, script prefix
   :1397-1459 (the shadow bytes 4..7 <- 0xf8, the header word at [frb, frb + 8), the beqz s2 side arm, then the 16
   shadow bytes of the 128-byte side frame <- 0xf5), plus the flag-word bytes_at of :1462-1464 (the fl_bytes step
   that reads the flag pointer the release loads).  The script is re-stepped with lib/Lib/StepF's step over
   ExecF.evtF, with four changes: the intros, fk_facts with explicit arguments, munch_refl with two ranges, and fl_bytes without bytes_ro8.  The split of record is
   ctrl_lay_block-stretches.md (a working note, not in this delivery); the recipe is
   segF-rerun-recipe.md (a working note, not in this delivery).

   PROVENANCE (route (a) condition 4).
   - image root (internal path)
     -> (internal path)
   - ELF sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd
   - compare: fuzz_ctrl.objdump.txt (a working note, not in this delivery), ctrl_lay_block 0x855f4 .. 0x85988
     (this stretch: 0x85884 li a0,-8 .. 0x858e8 sb a0,11(s8), stopping before 0x858ec ld a0,120(s2))
   - FACTS of record ed6b6b7b0ab (origin/regen/libreac-v190-on-338), PAU (internal path)
   - the run is re-stepped from ctrl_lay_block.v at a working branch d69f7c708f6

   ROUTE (a) CONDITIONS (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z, via a Theorem Labs lane):
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

   FOOTPRINT.  The stretch writes 4 + 16 shadow bytes at [shadow_addr frb, shadow_addr frb + 16) and the 8-byte
   header word at [frb, frb + 8); it reads nothing (the flag-pointer load at 0x858ec is the cut).  Its rng premises
   are the plan's row: (S - K) K, frb 24, (shadow_addr frb) 16. *)

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import ctrl_lay_block_F_common.
(* The skeleton's Require list, repeated in its order because the skeleton uses Require Import, not Require Export:
   Import is not transitive, so without this the names of ctrl_lay_block / ExecF / StepF are not in scope here.
   COMMON-CANDIDATE: make ctrl_lay_block_F_common.v's Require lines Require Export. *)
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
(* Last: StepF's step / if_false / finish / store_done (evtF goals) shadow the evt engine's. *)
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

Section K7.
  (* Section L's Variables, in Section L's order (ob is not used by any predicate this stretch names). *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr tb mb nb gb : list byte).

  Local Notation S := (bv_unsigned sp).
  Local Notation K := CTRL_LAY_BLOCK_K.
  Local Notation SP2 := ((S - 128) / 32 * 32).

  (* Section L's Hypotheses, by name and type: exactly the ones ctrl_lay_block.fk_facts and
     ctrl_lay_block.frame_shadow_rwcells take, which are the only Section L members this stretch applies. *)
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Rmd : 0 <= md < 2^64.
  Hypothesis Rg : 0 <= g < 2^64.
  Hypothesis SP16 : S mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (S - K) S.
  Hypothesis FL : length fr = 24%nat.
  Hypothesis K9 : ly_k fr <= 9.
  Hypothesis TM : ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm fr) tb.
  Hypothesis P0 : p <> 0.
  Hypothesis MDP : 3 <= ly_k fr <= 9 -> md <> 0 ->
    md mod 8 = 0 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       name_ok nb /\ bytes_at rsegs m (rname mb) nb).
  Hypothesis SR0 : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= S - K.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW0 : addressable m (S - K) K.
  Hypothesis FP0 : fp [0%nat; 1%nat] m (bv_unsigned tp) FS (S - K) S
    (ctrl_lay_block_W p S) (ctrl_lay_block_D p f).

  (* Section L's predicates and lemmas, applied to this section's variables (they are Section L members, so outside
     Section L they carry the variables Section L discharged into them). *)
  Local Notation FI := (ctrl_lay_block.FI sp tp p f FS).
  Local Notation LC := (ctrl_lay_block.LC ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS fr).
  Local Notation LAY := (ctrl_lay_block.LAY md g fr tb mb nb gb).
  Local Notation fk_facts :=
    (ctrl_lay_block.fk_facts sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg SP16 ST0 FL K9 TM P0 MDP SR0 HHM HAE
       AW0 FP0).
  Local Notation frame_shadow_rwcells :=
    (ctrl_lay_block.frame_shadow_rwcells sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg FL K9 TM P0 MDP).

  (* The state at the cut (pc 0x858ec), the plan's lay_F_pre_release: s2 = sfr = frb, s8 = shadow_addr frb,
     s9 = frb, sp = spc, a0 scratch; the memory is mc with the header word at [frb, frb + 8) and the 16 released
     shadow bytes [shadow_addr frb, shadow_addr frb + 16) written, and nothing else (munch); the 12 tracked frame
     shadow bytes read 0xf5 = 245 (the ASan released-frame byte); the flag-pointer word at frb + 120 the release is
     about to load is still le8 w120. *)
  Definition lay_F_pre_release (mc : word -> option byte) (frb sfr spc : Z) (w120 : word)
      (xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
      : machine_state -> Prop :=
    fun ms' => exists (a0' : word) (m' : word -> option byte),
      ms' = MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
                    a0' x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) x19 x20 x21 x22 x23
                    (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
                    x28 x29 x30 x31)
               F (Z_to_bv 64 0x858ec) fc None m' (seg_rom rsegs) /\
      munch [(shadow_addr frb, shadow_addr frb + 16); (frb, frb + 8)] mc m' /\
      wmono rsegs mc m' /\ rd_mono mc m' /\ mem_inv rsegs m' /\
      bytes_at rsegs m' (frb + 120) (le8 w120) /\
      rw_cells rsegs m' (shadow_addr frb) (repeat (C1 (Z_to_bv 8 245)) 12).

  (* ctrl_lay_block.v's Section-local Ltacs this script uses, over StepF's evtF goals (ly_epi_out :1226,
     tsh :1105-1117, ly_epi_ush :1229-1237).

     ADAPTATION, for the auditor.  ctrl_lay_block.v's `tsh frb FSW o k` is, over the evt engine, the store_ok
     assertion, one `step`, the `wa (shadow_addr frb + Z.of_nat k)` renaming, `rewrite le1_byte` and
     `mem_after_store`.  StepF's own `step` already ends in `mem_after_store_opt`, which normalizes the literal
     store byte (norm_lit_store_bytes / norm_lit_byte_mod256) and runs `mem_after_store` against the tracked
     rw_cells of the shadow block, so over evtF a tracked shadow store is exactly `step` and the four extra tactics
     have nothing left to do (`rewrite le1_byte` fails: there is no `le1` left).  The untracked stores -- the four
     shadow bytes 12..15 beyond the 12-byte tracked block, and the 8-byte header word -- keep the source's shape:
     the store_ok assertion (which carries mem_inv through the store) and `step; store_done`. *)
  Ltac ly_epi_out := cbn [outside]; repeat (split; [lia|]); exact I.

  (* An untracked shadow byte store at offset o (the side frame's shadow beyond the 12 tracked bytes). *)
  Ltac ly_epi_ush frb FSW o :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (store_ok rsegs mm (wa (shadow_addr frb + o)) 1 = true) as HSo
        by (eapply wv_store_ok;
            [ let ii := fresh in let Hii := fresh in intros ii Hii;
              assert (ii = 0) by lia; subst ii; rewrite Z.add_0_r; unfold shadow_addr; apply FSW; lia
            | eassumption | lia | lia ])
    end;
    step; store_done.

  (* The stretch: ly_epi_side's script from its entry state at 0x85884 to the flag-pointer load at 0x858ec. *)
  Lemma ctrl_lay_block_F_7 : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte)
      (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    rng RNG (S - K) K -> rng RNG frb 24 -> rng RNG (shadow_addr frb) 16 ->
    FI mc frb sfr spc j w120 -> sfr <> 0 -> LC mc gj LAY ->
    evtF rsegs RNG
      (lay_F_pre_release mc frb sfr spc w120 xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23
         x28 x29 x30 x31)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) x19 x20 x21 x22 x23
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85884) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23
      x28 x29 x30 x31 RWIN RFRB RSHA (HK & HFLAG & ACc & SRc & FPc & TLc & AWo) Hsfr LCH.
    pose proof (fk_facts frb sfr spc j w120 HK) as (FR8 & _ & _ & _ & FW & FAP & _ & _ & FSlo & _).
    specialize (HFLAG Hsfr).
    destruct HK as [(E0 & _ & _)|(Hj & Efr & Esfr & Espc & Ew)]; [exfalso; exact (Hsfr E0)|].
    subst sfr spc w120.
    pose proof FP0 as (_ & _ & _ & _ & _ & _ & _ & _ & (FSpos & _ & PGT & PApp & PStk) & _ & _ & _ & HFS0 & _).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    assert (EH : HIGHMEM_BEG = 17594333495296) by reflexivity.
    assert (EA : APPMEM_END = 140737488355328) by reflexivity.
    assert (EL : LOWMEM_END = 2147450880) by reflexivity.
    assert (EAK : ASAN_K = 2147450880) by reflexivity.
    assert (EZ : FS_SIZE = 11571200) by reflexivity.
    assert (EGT : ASAN_GT = 6283264) by reflexivity.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    assert (EfM1 : fs_M 1 = 8192) by reflexivity.
    assert (EfM0 : fs_M 0 = 16384) by reflexivity.
    assert (EfH0 : fs_hint FS 0 = FS) by (unfold fs_hint; cbn; lia).
    assert (EfH1 : fs_hint FS 1 = FS + 8) by (unfold fs_hint; cbn; lia).
    assert (EfL0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn; lia).
    assert (EfL1 : fs_flag FS 1 0 = FS + 20480) by (unfold fs_flag; cbn; lia).
    assert (Efa : fs_flag FS 1 j = FS + 20480 + j) by (unfold fs_flag; cbn; lia).
    assert (EfF0 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn; lia).
    assert (EfF1 : fs_frame FS 1 (fs_M 1) = FS + 2134016) by (unfold fs_frame, fs_B; cbn; lia).
    assert (Efr' : frb = FS + 1085440 + j * 128) by (rewrite Efr; unfold fs_frame, fs_B; cbn; lia).
    rewrite EfM1 in Hj. clear Efr.
    set (fa := fs_flag FS 1 j) in *. clearbody fa.
    assert (SHlo : 0 <= shadow_addr frb) by (unfold shadow_addr; lia).
    assert (SHL : LOWMEM_END <= shadow_addr frb) by (unfold shadow_addr; lia).
    assert (SHtop : shadow_addr frb + 16 <= HIGHMEM_BEG) by (unfold shadow_addr; Z.div_mod_to_equations; lia).
    assert (SHFS : shadow_addr frb + 16 <= FS \/ FS + FS_SIZE <= shadow_addr frb).
    { destruct (app_range FS FS_SIZE ltac:(lia) (fun i Hi => PApp (FS + i) ltac:(lia))) as [Hlo|Hhi]; lia. }
    clear FSlo.
    (* The side stack and the flag pointer are hidden behind a conjunction while the stores run: a bytes_at, a
       ro_cells or a stk hypothesis about the current memory is transported (with its lia side conditions) at every
       store, and these two are needed only at the flag-pointer word. *)
    pose proof FPc as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & PStkc) & _).
    pose proof (conj PStkc I) as PStkH. clear PStkc.
    pose proof (conj HFLAG I) as HFLAGh. clear HFLAG.
    assert (FSW16 : forall i, 0 <= i < 16 -> wview rsegs m (wa (frb / 8 + ASAN_K + i)) <> None).
    { intros i Hi. replace (frb / 8 + ASAN_K + i) with (shadow_addr (frb + 8 * i))
        by (rewrite sh_add8 by exact FR8; unfold shadow_addr; lia).
      exact (proj1 (SR0 _ (rt_app_shadow _ (PApp (frb + 8 * i) ltac:(lia))))). }
    assert (FWa : wview rsegs m (wa fa) <> None) by exact (stk_wv m FS (FS + FS_SIZE) fa PStk ltac:(lia)).
    pose proof LCH as (_ & _ & _ & WMc & MIc & _ & _).
    destruct (frame_shadow_rwcells mc frb FR8 ltac:(lia) FAP SRc) as (junk & _ & HSH).
    (* The flag byte [fa, fa + 1) is written after the cut, so this stretch's footprint is the two ranges only. *)
    pose proof (munch_refl [(shadow_addr frb, shadow_addr frb + 16); (frb, frb + 8)] mc) as MUcc.
    pose proof (wmono_refl rsegs mc) as WMcc.
    pose proof (rd_mono_refl mc) as RMcc.
    (* 0x85884 li a0,-8 ; 0x85888 .. 0x85894 the four sb into the frame's shadow bytes 4..7 (tracked). *)
    step. step. step. step. step.
    (* 0x85898 lui ; 0x8589c addiw: the header word 0x45e0360e. *)
    step. step.
    (* 0x858a0 sd a0,0(s9): the header word at [frb, frb + 8), untracked. *)
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HM8 : store_ok rsegs mm (wa frb) 8 = true)
        by (eapply wv_store_ok; [ intros i Hi; apply FW; lia | eassumption | lia | lia ]) end.
    step. store_done.
    (* 0x858a4 beqz s2: the side arm (s2 = sfr = frb <> 0). *)
    step. rewrite (rc_eqb frb 0) by lia. rewrite (proj2 (Z.eqb_neq frb 0) Hsfr). cbv iota.
    (* 0x858a8 li a0,-11, then the 16 sb that release the side frame's shadow: 4..7, 0..3, 12..15, 8..11. *)
    step.
    step. step. step. step.
    step. step. step. step.
    ly_epi_ush frb FSW16 12. ly_epi_ush frb FSW16 13. ly_epi_ush frb FSW16 14. ly_epi_ush frb FSW16 15.
    step. step. step. step.
    (* pc 0x858ec: the flag-pointer load is the cut.  The word it reads is still the one FI carries (fl_bytes of
       the source script :1462-1464, without the bytes_ro8 the load itself needs). *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HFB : bytes_at rsegs mm (frb + 120) (le8 (Z_to_bv 64 fa)))
        by (eapply fl_bytes;
            [ exact (proj1 HFLAGh) | exact MUcc
            | intros x Hx; rewrite length_le8 in Hx; ly_epi_out ]) end.
    apply evtF_done. unfold lay_F_pre_release. cbv beta.
    do 2 eexists. split; [reflexivity|].
    split; [exact MUcc|]. split; [exact WMcc|]. split; [exact RMcc|]. split; [exact MIc|].
    split; [exact HFB | exact HSH].
  Qed.

  (* The recipe's step 4 check: with RNG_all the _F statement is the old evt one, nothing weaker. *)
  Corollary ctrl_lay_block_F_7_of_F : forall (mc : word -> option byte) (gj : list byte)
      (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    FI mc frb sfr spc j w120 -> sfr <> 0 -> LC mc gj LAY ->
    evt rsegs
      (lay_F_pre_release mc frb sfr spc w120 xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23
         x28 x29 x30 x31)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) x19 x20 x21 x22 x23
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85884) fc None mc (seg_rom rsegs)).
  Proof.
    intros mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23
      x28 x29 x30 x31 HFI Hsfr LCH.
    pose proof (fk_facts frb sfr spc j w120 (proj1 HFI)) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & _ & _).
    pose proof FP0 as (_ & _ & _ & _ & _ & _ & _ & _ & (FSpos & _) & _).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    assert (EH : HIGHMEM_BEG = 17594333495296) by reflexivity.
    assert (EAK : ASAN_K = 2147450880) by reflexivity.
    assert (HSP2 : SP2 <= S) by (Z.div_mod_to_equations; lia).
    apply (evtF_evt rsegs RNG_all).
    apply (ctrl_lay_block_F_7 RNG_all mc gj frb sfr spc j w120); try assumption.
    - apply rng_all; lia.
    - apply rng_all; lia.
    - apply rng_all; [unfold shadow_addr; lia | unfold shadow_addr; Z.div_mod_to_equations; lia].
  Qed.
End K7.

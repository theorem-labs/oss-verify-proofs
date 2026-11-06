(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 164 of its 188 lines of code are new or changed and 224 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_catalogue_match.v (source commit d69f7c708f6, proved on FACTS ed6b6b7b0ab) by the
   same script over lib/Lib/StepF; image fuzz_ctrl v1.9.0 asan, ELF fuzz_ctrl.debug sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd; route (a) of 22:20Z; for the cgif-form walk
   C_reac_box_catalogue_match.v only.

   Stretch S1 of the walk: the SILENT run from the entry 0x84498 to the __asan_stack_malloc_2 call at 0x84504, in the
   state the `jal` sees before it executes. The source run lemma is cm_entry (reac_box_catalogue_match.v:918), whose
   script runs THROUGH that call (it applies the section hypothesis HSM, asan_stack_malloc_2_contract, with evt_cut
   after the 28th step). This file re-runs its first 27 steps -- the same tactics, a new lemma boundary at the call:
   cm_entry_F stops at the `jal` and hands the state to the post predicate cmS1K, which states the facts the script
   has there (munch / wmono / rd_mono / mem_inv / asan_cells / shadow_rw of the reached memory, the carved stack
   window and the 12 saved registers). The walk then takes the allocator event itself (cgif's astack_malloc_realizes),
   so neither the contract nor the arms that follow it are re-run here. The 27 steps make no instrumented shadow
   check, so no rng premise names a shadow byte.

   Accesses of the run, one rng premise each (recipe order): (a) the stack window of the `stk` premise ST, written by
   `sd zero,0(sp)` at S-128 and by the 12 callee-saved stores in [S-96, S); (b) the four runtime cells it loads:
   GOT_CELL_K and the CELL_K it points at (ASAN_K), GOT_UAR and the UAR flag word (4 bytes). No image constant is
   read on this stretch, so there is no image range premise. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse
  RcMatch RcMatchLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_box_model_block_c reac_box_model_block
  reac_box_catalogue_match_c reac_box_catalogue_match_lib.
(* Route (C): the narrowed premise (shadow_rw_on, ShadowRwOnT.shadow_rw_on_mem_mono) and the source run's CA and
   cmSAVES (Required, not Imported) for Section MatchF1On below. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match.
(* Last: StepF's step / store_done (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
(* The store hook the scripts below use (StepF's store_done calls it): also transport rd_mono across a store. Text of
   lib/A/Prog/MemMono.v (at head lib/A/Prog/MemMono.v:207-217, global there; a Local version from a working branch 8bac67328ab), Local here. *)
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

(* The call site: `jal ra, 0x3d8bc <__asan_stack_malloc_2>` at 0x84504 (objdump of fuzz_ctrl.debug). *)
Definition CM_STACK_MALLOC_CALL : Z := 0x84504.

Module CM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match.

(* ---------------------------------------------------------------------------------------------------------- *)
(* Route (C) (frozen form, a Theorem Labs lane 10:49Z): the `_on` forms of this file's SR-dependent declarations. Section
   MatchF1's binders and premises with `SR : shadow_rw m` narrowed to `SR_on : shadow_rw_on R m`
   (R = reac_box_catalogue_match_shadow_R f len S FS, a Theorem Labs lane's, reac_box_catalogue_match_c.v); cm_entry_F_on is
   cm_entry_F's script with one changed step: the shadow fact of the reached memory is
   ShadowRwOnT.shadow_rw_on_mem_mono at R. CA and cmSAVES are the source run's (reac_box_catalogue_match.v:230, 291,
   the same text as Section MatchF1's); CA's two bounds are re-derived in the script by CA_facts' / cm_CA_lo's
   proofs. The old statements below are corollaries of these (Section MatchF1). *)
Section MatchF1On.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis MI : mem_inv rsegs m.
Hypothesis AC : asan_cells m.
Hypothesis SR_on : shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.

Local Abbreviation CA := (CM.CA S).
Local Abbreviation cmSAVES := (CM.cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).

(* cmS1K with its shadow fact narrowed to R. *)
Definition cmS1K_on (Q : machine_state -> Prop) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : Prop :=
  forall mc : word -> option byte,
    munch [(S - 9136, S)] m mc -> wmono rsegs m mc -> rd_mono m mc -> mem_inv rsegs mc ->
    asan_cells mc -> shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) mc ->
    stk rsegs mc (S - 9136) (S - 96) -> rw_cells rsegs mc (S - 96) cmSAVES ->
    Q (MS (mkR ra (Z_to_bv 64 CA) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
              (Z_to_bv 64 192) (wa CELL_K) (sx32 (wa 1)) a3 a4 a5 a6 a7
              s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CM_STACK_MALLOC_CALL) fc None mc (seg_rom rsegs)).

Lemma cm_entry_F_on : forall (Q : machine_state -> Prop) (RNG : footprint)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  cmS1K_on Q t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ->
  rng RNG (S - 9136) 9136 ->
  rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 -> rng RNG GOT_UAR 8 -> rng RNG UAR 4 ->
  evtF rsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).
Proof.
  intros Q RNG t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 K RW RGCK RCK RGUA RUA.
  unfold GOT_CELL_K, CELL_K, GOT_UAR, UAR in RGCK, RCK, RGUA, RUA.
  unfold REAC_BOX_CATALOGUE_MATCH.
  assert (STbox : stk rsegs m (S - 9136) S /\ True) by (split; [exact ST | exact I]).
  assert (CAF : CA mod 32 = 0 /\ S - 160 <= CA <= S - 128)
    by (unfold CM.CA; Z.div_mod_to_equations; lia).
  destruct CAF as (CA32 & CAlo & CAhi).
  assert (CAF2 : S - 144 <= CA <= S - 128)
    by (unfold CM.CA; pose proof S16 as H16; Z.div_mod_to_equations; lia).
  destruct CAF2 as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  pose proof AC as (CK & GCK & _ & _ & _ & UA & GUA & _).
  unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
  apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
  assert (MU : munch [(S - 9136, S)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  assert (RM : rd_mono m m) by apply rd_mono_refl.
  pose proof ST as ST0.
  carve_frame 96%nat ST0.
  (* 0x84498 addi sp,sp,-128 *)
  step.
  assert (HSz : store_ok rsegs m (wa (S - 128)) 8 = true)
    by (eapply wv_store_ok; [intros i Hi; apply (stk_wv m (S - 9136) (S - 96)); [exact ST0 | lia] |
        apply wmono_refl | lia | lia]).
  (* 0x8449c sd zero,0(sp) *)
  step. store_done.
  (* 0x844a0 .. 0x844cc: sd ra,120(sp) .. sd s10,32(sp) *)
  do 12 step.
  (* 0x844d0 addi s0,sp,128 ; 0x844d4 andi sp,sp,-32 *)
  step. step.
  assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = CA).
  { rewrite unsigned_lit by lia. rewrite land_align32 by lia. unfold CM.CA.
    replace (S + -128) with (S - 128) by lia. reflexivity. }
  rewrite EA.
  (* 0x844d8 mv s1,sp .. 0x844f4 ld s5,0(a1) *)
  do 8 step.
  (* 0x844f8 mv s3,a0 ; 0x844fc beqz a2 (the UAR flag is 1: not taken, the fake-stack arm) *)
  step. step.
  replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
  (* 0x84500 li a0,192 -- the state at 0x84504, the `jal __asan_stack_malloc_2`. *)
  step.
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (AC0 : asan_cells mc) by
        (apply (fl_asan_cells [(S - 9136, S)] m mc AC MU); intros x Hx; unfold RT_LO, RT_HI in Hx;
         cbn [outside]; split; [clear -Hx HHM'; lia | exact I]);
      pose proof (A.ShadowRwOnT.shadow_rw_on_mem_mono _ m mc SR_on WM RM) as SR0;
      apply evtF_done; apply (K mc)
  end; assumption.
Qed.

(* cm_entry_of_F at the `_on` continuation. *)
Lemma cm_entry_of_F_on : forall (Q : machine_state -> Prop)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  cmS1K_on Q t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).
Proof.
  intros Q t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 K.
  eapply evtF_evt, (cm_entry_F_on Q RNG_all t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 K).
  - apply rng_all; lia.
  - apply rng_all; unfold GOT_CELL_K; lia.
  - apply rng_all; unfold CELL_K; lia.
  - apply rng_all; unfold GOT_UAR; lia.
  - apply rng_all; unfold UAR; lia.
Qed.

End MatchF1On.

Section MatchF1.
(* The binders and premises of reac_box_catalogue_match.v's Section Match, unchanged. *)
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis MI : mem_inv rsegs m.
Hypothesis AC : asan_cells m.
Hypothesis SR : shadow_rw m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.

(* reac_box_catalogue_match.v:230, 232, 337: the aligned frame pointer and its two bounds, verbatim. *)
Definition CA : Z := (S - 128) / 32 * 32.

Lemma CA_facts : CA mod 32 = 0 /\ S - 160 <= CA <= S - 128.
Proof. unfold CA. Z.div_mod_to_equations. lia. Qed.

Lemma cm_CA_lo : S - 144 <= CA <= S - 128.
Proof. unfold CA. pose proof S16 as H16. Z.div_mod_to_equations. lia. Qed.

(* reac_box_catalogue_match.v:291: the 12 callee-saved registers stored at [S-96, S), s10..ra ascending. *)
Definition cmSAVES : list cell :=
  [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* The post predicate at the call (pc 0x84504), i.e. the state the cm_entry script has at its 28th step: sp = s1 = CA
   (the 32-aligned frame pointer), s0 = S, a0 = 192 (the class-2 frame size the allocator is asked for), a1 = CELL_K
   (the runtime cell the shadow offset was loaded from), a2 = the UAR flag word (1, so the fake-stack arm is the one
   taken), s3 = f, s4 = len, s5 = ASAN_K; the reached memory mc differs from m only inside the stack window, keeps
   the write and read relations, the memory invariant and the ASan runtime cells, and carries the carved window
   [S-9136, S-96) and the 12 saves at [S-96, S). *)
Definition cmS1K (Q : machine_state -> Prop) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : Prop :=
  forall mc : word -> option byte,
    munch [(S - 9136, S)] m mc -> wmono rsegs m mc -> rd_mono m mc -> mem_inv rsegs mc ->
    asan_cells mc -> shadow_rw mc ->
    stk rsegs mc (S - 9136) (S - 96) -> rw_cells rsegs mc (S - 96) cmSAVES ->
    Q (MS (mkR ra (Z_to_bv 64 CA) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
              (Z_to_bv 64 192) (wa CELL_K) (sx32 (wa 1)) a3 a4 a5 a6 a7
              s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CM_STACK_MALLOC_CALL) fc None mc (seg_rom rsegs)).

(* The _F form of cm_entry's first stretch: 0x84498 -> 0x84504, by the script of reac_box_catalogue_match.v's
   cm_entry over StepF's step, stopped at the `jal`. *)
Lemma cm_entry_F : forall (Q : machine_state -> Prop) (RNG : footprint)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  cmS1K Q t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ->
  rng RNG (S - 9136) 9136 ->
  rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 -> rng RNG GOT_UAR 8 -> rng RNG UAR 4 ->
  evtF rsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).
Proof.
  intros Q RNG t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 K RW RGCK RCK RGUA RUA.
  (* cm_entry_F_on at any FS (0; the old statement names no FS): SR gives SR_on, and the old continuation K takes
     the shadow fact of the reached memory from SR (wmono / rd_mono from m). *)
  eapply (cm_entry_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S 0); try eassumption.
  - exact (shadow_rw_on_of_shadow_rw _ m SR).
  - intros mc MU WM RM MIc ACc _ STc RWc.
    exact (K mc MU WM RM MIc ACc (shadow_rw_mono m mc SR WM RM) STc RWc).
Qed.

(* The corollary at the new boundary (recipe step 4): with ExecF.rng_all the _F statement gives back the old
   lib.Lib Exec.evt run of this stretch, so cm_entry_F is that run plus footprint premises, nothing weaker. *)
Lemma cm_entry_of_F : forall (Q : machine_state -> Prop)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  cmS1K Q t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).
Proof.
  intros Q t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 K.
  eapply (cm_entry_of_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S 0); try eassumption.
  - exact (shadow_rw_on_of_shadow_rw _ m SR).
  - intros mc MU WM RM MIc ACc _ STc RWc.
    exact (K mc MU WM RM MIc ACc (shadow_rw_mono m mc SR WM RM) STc RWc).
Qed.

End MatchF1.

(* Route (C): the assumptions of the `_on` stretch the glue uses. *)
Check cm_entry_F_on.
Print Assumptions cm_entry_F_on.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 602 of its 619 lines of code are new or changed and 231 lines of the source are left out. *)
(* ctrl_lay_block, image A (asan, entry 0x855f4): ROUTE (C) twin of region R3's run (0x85828, the return of
   reac_box_model_block, -> 0x858f4, after the class-1 flag release).  A Theorem Labs lane (a Theorem Labs lane),
   brief (a working note, not in this delivery).
   rule 24: no function proved.  This file proves no function (kind: segment lemma).

   lay_F_R3_run_on is lay_F_R3_run (ctrl_lay_block_F_R3.v (at head lib/A/Prog/ctrl_lay_block_F_R3.v:476-555; from a working branch 63a02bb46d7)) in
   the route (C) form of record (a Theorem Labs lane's ASSIGN.md (a working note, not in this delivery; its form frozen by a Theorem Labs lane 09:38Z) + the 10:34Z amendment):
   - PRE: the run has TWO universal shadow_rw premises, the Section's `SR0 : shadow_rw m` (ctrl_lay_block_F_R3.v:191)
     and the `shadow_rw mc` conjunct of its FI premise (ctrl_lay_block.v:1100, at the region's start memory mc).
     The Section's SR0 is DROPPED: once its consumers are re-proved (below) no shadow byte is read or stored through
     it (its one access, F_7.v:204, takes the run's start memory instead, see (3)).  FI's conjunct becomes the premise
     `shadow_rw_on (lay_F_R3_shadow_R FS p) mc` (R3 below) beside FI_on mc (FI without that conjunct).  The callee
     contract asan_memcpy_contract_F becomes a Theorem Labs lane's asan_memcpy_contract_F_on (lib/A/Prog/asan_memcpy_cF_on.v,
     83ab88c3325), by name.
   - POST: FI's conjunct leaves the post (FI_on) and the post gains the transport
     `forall P, shadow_rw_on P mc0 -> shadow_rw_on P m4` from the region's START memory mc0 to its END memory m4
     (a Theorem Labs lane's request, 12:58Z).
   - lay_F_R3_shadow_R_sub proves R3 a subset of a Theorem Labs lane's ctrl_lay_block_shadow_R (lib/A/Prog/ctrl_lay_block_c.v:392,
     a working branch 0bf62760c4a, blob c36731db371), binders in its order (S FS p f md g fr mb nb a).

   R3 = lay_F_R3_shadow_R FS p = asan_stack_malloc_shadow_R FS 1 (the shadow of the class-1 fake-stack block) \/
        sh_word_on (p + 18) 32 (the aligned shadow words of the output block).
   DERIVATION (for the auditor a Theorem Labs lane; every shadow use in the original, verified against the source; a Theorem Labs lane's table
   shadow-rw-consumers-A.md row 419 (a working note, not in this delivery)):
   (1) READS by the callee: F_R3.v:299 takes FI's `shadow_rw mc` (SRc) into asan_memcpy_contract_F's shadow premise
       (F_R3.v:329), the copy of the box result [frb + 32, frb + 64) into [p + 18, p + 50) (src = frb + 32,
       F_R3.v:396-400).  In the _on contract that premise is `shadow_rw_on (asan_memcpy_shadow_R a0 a1 a2)`
       (asan_memcpy_c_on.v:25) = sh_word_on (frb + 32) 32 \/ sh_word_on (p + 18) 32; on the side frame
       (frb = fs_frame FS 1 j, FS mod 4096 = 0) the first is inside the class-1 block (lay_on_frame_out_block,
       lay_F_R3_memcpy_R below).
   (2) READS + presence for the tracked release, the 12 shadow bytes [shadow_addr frb, + 12): stretch k = 7
       (ctrl_lay_block_F_7.v:207) takes FI's `shadow_rw mc1` into frame_shadow_rwcells (ctrl_lay_block.v:990-1014:
       mrd present :1006, wview :1013) for the rw_cells block the 0xf5 stores run against.
   (3) STORES, the 16 shadow bytes [shadow_addr frb, + 16) of the frame release (F_7.v:213-228; bytes 12..15
       untracked through ly_epi_ush): F_7.v:201-204 `FSW16` from the Section's SR0 (wview at m), used with
       wmono m -> store-time memory.  The copy takes the same 16 wview facts at the stretch's start memory mc1
       from R3 (the run's premise carried to mc1 by the transport of k = 5 / k = 6), used with wmono mc1 ->
       store-time memory (WMcc); the stores are the same instructions.
   (4) through fk_facts / fk_spc only (their non-shadow conjuncts, no shadow access): F_R3.v:237-241 (fk_spc),
       :243-251 (LC_FI_memcpy, which also transports FI's shadow_rw by fl_shadow_rw, ctrl_lay_block.v:1664), F_7.v:163.
   Bytes (2) and (3) are the side frame's (sfr <> 0, F_R3.v:479), inside the class-1 block (lay_on_frame_sh_block,
   ctrl_lay_block_F_R2_on.v).  The release (F_R3.v:79-129) touches only the flag byte fs_flag FS 1 j (not shadow)
   and k = 6 at g = 0 (F_R3.v:417-436) is one register-only step.  The frame index is a binder of the run, so the
   region names the class-1 block, as asan_stack_malloc_c_on.v and ctrl_lay_block_shadow_R do; the real-frame arm
   is not taken (sfr <> 0), so the window's shadow is NOT in R3: lay_F_R3_box_arm_on takes `sfr <> 0` (DIFF below).

   RE-PROVED HELPERS (re-based copy allowance, a Theorem Labs lane 23:53Z: instruction proofs verbatim; each named here):
   - from ctrl_lay_block_F_R2_on.v (Required qualified): FI_on (FI minus its shadow_rw conjunct) and fk_facts_on
     (fk_facts minus its frame-shadow conjunct :520, no shadow premise).
   - fk_spc_on (ctrl_lay_block.v:1603-1608), fk_facts -> fk_facts_on.
   - FI_keep_on (ctrl_lay_block.v:1652-1669), FI -> FI_on: the fl_shadow_rw bullet (:1664) goes with the conjunct.
   - LC_FI_memcpy_on (ctrl_lay_block.v:1750-1787), fk_spc -> fk_spc_on, FI -> FI_on, FI_keep -> FI_keep_on.
   - frame_shadow_rwcells_on (ctrl_lay_block.v:990-1014): premise `shadow_rw mm` -> shadow_rw_on of the 12 bytes
     [shadow_addr frb, + 12) it reads (two uses, :1006 and :1013, now give the membership).
   - ctrl_lay_block_F_7_on (ctrl_lay_block_F_7.v:147-240) with its Section-local Ltacs ly_epi_out / ly_epi_ush
     (F_7.v:133-144) verbatim: FI -> FI_on plus the premise shadow_rw_on R3 mc (DIFF below).
   NEW: lay_on_frame_out_block, lay_F_R3_memcpy_R.
   Section L's wrappers lay_F_R3_LC_addr_p / lay_F_R3_app_blk / lay_F_R3_stk_shrink (F_R3.v:221-235) are Local
   Notations of the same Section L constants here (nothing re-proved).

   DIFF AGAINST ctrl_lay_block_F_R3.v (instruction proofs VERBATIM):
   - Section L5R -> L5R_on; Hypothesis SR0 removed; MEMCF : asan_memcpy_contract_F -> asan_memcpy_contract_F_on.
   - lay_F_R3_post_args -> lay_F_R3_post_args_on, ly_args_F_R3_post -> ly_args_F_R3_post_on, lay_F_R3_end ->
     lay_F_R3_end_on: FI -> FI_on; post_args_on and end_on add the last conjunct, the transport from mc0.
   - lay_F_R3_cpy_on: premise `shadow_rw_on (asan_memcpy_shadow_R (p + 18) src 32) mc` (SRM) after FI_on; `exact SRc`
     -> `exact SRM`; the memcpy post's transport conjunct SRT closes the new post conjunct.
   - lay_F_R3_box_arm_on: premises `shadow_rw_on R3 mc` and `sfr <> 0` after FI_on; the r <> 1 arms close the
     transport by the identity; the r = 1 arm gives lay_F_R3_cpy_on SRM by lay_F_R3_memcpy_R.
   - ly_args_F_R3_g0_on: FI -> FI_on.
   - lay_F_R3_run_on: premise `shadow_rw_on R3 mc` after FI_on; stretch k = 7 -> ctrl_lay_block_F_7_on, given R3 at
     mc1 by k = 5's transport; FI2's destruct pattern one component fewer; the release is
     ctrl_lay_block_F_R3.lay_F_R3_release (no shadow, not copied); the final split adds the transport
     (k = 5's, then A.ShadowRwOnT.shadow_rw_on_mem_mono over k = 7's and the release's wmono / rd_mono).
   - ctrl_lay_block_F_7_on vs ctrl_lay_block_F_7: premise `shadow_rw_on R3 mc` (SRc) after FI_on; fk_facts ->
     fk_facts_on (one destruct component fewer); FRB (the 16 frame bytes in the block, lay_on_frame_sh_block, before
     `clear Efr`); FSW16 at mc from SRc (was at m from SR0); frame_shadow_rwcells -> frame_shadow_rwcells_on with
     the 12-byte region from SRc (FRB12); `unfold lay_F_pre_release` -> `unfold ctrl_lay_block_F_7.lay_F_pre_release`.

   PROVENANCE: as ctrl_lay_block_F_R3.v (image root (internal path), ELF
   sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd, FACTS of record ed6b6b7b0ab). *)
(* FIRST, before ctrl_lay_block_F_common loads ctrl_lay_block: A.ShadowRwOnT Requires A.Prog.MemMono, whose non-local
   `Ltac footprint_after_store ::=` (MemMono.v:207) would otherwise replace ctrl_lay_block's (ctrl_lay_block.v:215),
   which carries ctrl_lay_block.rd_mono hypotheses across the stores of stretch k = 7 (as in
   ctrl_lay_block_F_R2_on.v, where this was measured). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOnT.
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
(* route (C): the region-restricted shadow_rw (a Theorem Labs lane's leaf), its transports, the regions of the callees *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import sh_word_on asan_stack_malloc_c_on
  asan_memcpy_c_on asan_memcpy_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* FI_on / fk_facts_on / lay_on_frame_sh_block (R2's twin file), the release and stretch k = 7's post (no shadow,
   not copied), Required qualified *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ctrl_lay_block_F_R2_on ctrl_lay_block_F_R3
  ctrl_lay_block_F_7.
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
Local Open Scope Z_scope.

(* ---- R3, and its subset proof against a Theorem Labs lane's ctrl_lay_block_shadow_R ---- *)
Definition lay_F_R3_shadow_R (FS p : Z) (a : Z) : Prop :=
  asan_stack_malloc_shadow_R FS 1%nat a \/ sh_word_on (p + 18) 32 a.

Lemma lay_F_R3_shadow_R_sub : forall (S FS p f md g : Z) (fr mb nb : list byte) (a : Z),
  lay_F_R3_shadow_R FS p a -> ctrl_lay_block_shadow_R S FS p f md g fr mb nb a.
Proof.
  intros S FS p f md g fr mb nb a [H|H]; unfold ctrl_lay_block_shadow_R.
  - right; right; left; exact H.
  - right; right; right; left; exact H.
Qed.

(* The aligned shadow words of the box output [fs_frame FS 1 j + 32, + 32) of a class-1 frame (j < fs_M 1, FS a
   multiple of 4096) lie in the shadow of the class-1 block, asan_stack_malloc_shadow_R FS 1. *)
Lemma lay_on_frame_out_block : forall (FS j a : Z), FS mod 4096 = 0 -> 0 <= j < fs_M 1 ->
  sh_word_on (fs_frame FS 1 j + 32) 32 a -> asan_stack_malloc_shadow_R FS 1%nat a.
Proof.
  intros FS j a HF Hj (_ & Ha). replace (fs_M 1) with 8192 in Hj by reflexivity.
  unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in Ha.
  unfold asan_stack_malloc_shadow_R, fs_frame, fs_B, shadow_addr in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
  change (2 ^ 20) with 1048576 in *. change (2 ^ 1) with 2 in *.
  unfold ASAN_K in *.
  Z.div_mod_to_equations. lia.
Qed.

Section L5R_on.
  (* Section L's Variables (ctrl_lay_block.v:404-405), verbatim. *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr ob tb mb nb gb : list byte).

  Local Notation S := (bv_unsigned sp).
  Local Notation K := CTRL_LAY_BLOCK_K.

  (* Section L's Hypotheses (ctrl_lay_block.v:410-474), verbatim, EXCEPT SR0, which this run no longer uses (header,
     "PRE").  The four callee / runtime contracts of Section L are NOT taken; the checked copy takes a Theorem Labs lane's
     route (C) footprint contract asan_memcpy_contract_F_on (MEMCF below). *)
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

  (* The one callee contract this run applies, route (C) footprint form, owned and proved by a Theorem Labs lane
     (lib/A/Prog/asan_memcpy_cF_on.v): taken by name, of exactly its type, never restated. *)
  Hypothesis MEMCF : asan_memcpy_contract_F_on.

  Local Notation SP2 := ((S - 128) / 32 * 32).

  (* Section L's predicates, applied to this section's variables (as ctrl_lay_block_F_R3.v:214-217), with FI_on for
     FI (ctrl_lay_block_F_R2_on.v). *)
  Local Notation FK := (ctrl_lay_block.FK sp FS).
  Local Notation FI_on := (ctrl_lay_block_F_R2_on.FI_on sp tp p f FS).
  Local Notation LC := (ctrl_lay_block.LC ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS fr).
  Local Notation BASE := (ctrl_lay_block.BASE md fr tb mb nb).
  Local Notation LAY := (ctrl_lay_block.LAY md g fr tb mb nb gb).
  Local Notation lay_F_pre_release := (ctrl_lay_block_F_7.lay_F_pre_release sp gp tp s11 F fc).

  (* Section L's helper lemmas at this section's variables and hypotheses (Section L constants applied; the
     argument lists are ctrl_lay_block.vo's / ctrl_lay_block_F_R2_on.vo's). *)
  Local Notation lay_F_R3_LC_addr_p :=
    (ctrl_lay_block.LC_addr_p ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f md g FS fr tb mb nb gb
       Rp Rf Rmd Rg SP16 DJ1 FL K9 TM P0 MDP HHM AR FP0).
  Local Notation lay_F_R3_app_blk := (ctrl_lay_block.app_blk sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg FL TM MDP AR AP50).
  Local Notation lay_F_R3_stk_shrink :=
    (ctrl_lay_block.stk_shrink sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg FL K9 TM P0 MDP).
  Local Notation fk_facts_on :=
    (ctrl_lay_block_F_R2_on.fk_facts_on sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg SP16 ST0 FL K9 TM P0 MDP
       HHM HAE AW0 FP0).
  Local Notation SP2_facts :=
    (ctrl_lay_block.SP2_facts sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg SP16 FL K9 TM P0 MDP).
  Local Notation W_shadow_out :=
    (ctrl_lay_block.W_shadow_out sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg SP16 FL K9 TM P0 MDP HHM AR).
  Local Notation FI_out120 := (ctrl_lay_block.FI_out120 sp tp m p f FS FP0).
  Local Notation lay_out_rt :=
    (ctrl_lay_block.lay_out_rt sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg FL K9 TM P0 MDP HHM ARDJ FP0).
  Local Notation LC_intro :=
    (ctrl_lay_block.LC_intro ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f md g FS fr mb nb Rp Rf Rmd Rg DJ3m DB3 DBN
       MDP ARDJ AMD FPM).
  Local Notation bytes_at_of_rd :=
    (ctrl_lay_block.bytes_at_of_rd sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg FL K9 TM P0 MDP).

  (* ---- re-proved helpers (header, RE-PROVED HELPERS) ---- *)

  (* fk_spc (ctrl_lay_block.v:1603-1608), fk_facts -> fk_facts_on. *)
  Lemma fk_spc_on : forall frb sfr spc j w120, FK frb sfr spc j w120 -> S - 256 <= spc <= S - 128.
  Proof.
    intros frb sfr spc j w120 HK. pose proof SP2_facts as (_ & HAlo & HAhi).
    pose proof (fk_facts_on frb sfr spc j w120 HK) as (_ & _ & H3 & H4 & _).
    destruct HK as [(_ & E1 & E2) | (_ & _ & _ & E2 & _)]; lia.
  Qed.

  (* FI_keep (ctrl_lay_block.v:1652-1669), FI -> FI_on (its fl_shadow_rw bullet :1664 goes with the conjunct). *)
  Lemma FI_keep_on : forall mc mc' W' frb sfr spc j w120, FI_on mc frb sfr spc j w120 ->
    munch W' mc mc' -> wmono rsegs mc mc' -> sub_fp W' (ctrl_lay_block_W p S) ->
    (forall x, FS <= x < FS + FS_SIZE -> outside W' x \/ exists b, mrd rsegs mc' (wa x) = Some b) ->
    FI_on mc' frb sfr spc j w120.
  Proof.
    intros mc mc' W' frb sfr spc j w120 (HK & H120 & AC & FP & TL & HA) MU WM Hs HRD.
    assert (SHo : forall x, in_shadow x -> outside W' x) by (intros x Hx; apply Hs, W_shadow_out, Hx).
    split; [exact HK|]. split; [|split; [|split; [|split]]].
    - intros Hs0. apply (fl_bytes W' mc mc' _ _ (H120 Hs0) MU). intros x Hx. rewrite length_le8 in Hx.
      apply Hs. exact (FI_out120 frb sfr spc j w120 HK Hs0 x ltac:(cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia)).
    - apply (fl_asan_cells W' mc mc' AC MU). intros x Hx. apply (lay_out_rt W' x); [|exact Hx].
      intros y Hy. apply Hs. exact (outside_app_l _ _ y Hy).
    - exact (fl_fp_W [0%nat; 1%nat] mc mc' (bv_unsigned tp) FS (S - K) S _ _ W' FP MU WM Hs HRD).
    - unfold ctrl_lay_block_tls in *.
      exact (fl_tls_W [0%nat; 1%nat] mc mc' (bv_unsigned tp) FS (S - K) S _ _ W' _ FP MU Hs TL).
    - intros x Hx Hf. exact (fl_addressable W' mc mc' x 1 (HA x Hx Hf) MU SHo).
  Qed.

  (* LC_FI_memcpy (ctrl_lay_block.v:1750-1787), fk_spc -> fk_spc_on, FI -> FI_on, FI_keep -> FI_keep_on. *)
  Lemma LC_FI_memcpy_on : forall mc m' gj X X' D N frb sfr spc j w120,
    LC mc gj X -> FI_on mc frb sfr spc j w120 -> p + 18 <= D -> D + N <= p + 50 -> 0 <= N ->
    munch [(D, D + N); (spc - ASAN_MEMCPY_K, spc)] mc m' -> wmono rsegs mc m' -> mem_inv rsegs m' ->
    stk rsegs m' (S - K) spc -> rw_cells rsegs m' (p + 18) [CB 32 X'] ->
    LC m' gj X' /\ FI_on m' frb sfr spc j w120.
  Proof.
    intros mc m' gj X X' D N frb sfr spc j w120 (FR & ST & MU & WM & MI & BK & Bf) FIH HD1 HD2 HN MUc WMc MIc STc BKc.
    pose proof (fk_spc_on frb sfr spc j w120 (proj1 FIH)) as Hspc.
    pose proof DJ1 as D1. pose proof DJ2 as D2. pose proof DB1 as D3.
    unfold ly_dj, CTRL_LAY_BLOCK_K in D1, D2. unfold ly_dj in D3. unfold ASAN_MEMCPY_K in *.
    unfold CTRL_LAY_BLOCK_K in *.
    destruct (ly_rw_cb _ _ _ _ _ BKc) as (XL & XB & _).
    assert (RD : forall x, ~ outside [(D, D + N); (spc - 2224, spc)] x -> exists b, mrd rsegs m' (wa x) = Some b).
    { intros x Hx. cbn [outside] in Hx.
      destruct (Z_lt_le_dec x D) as [L|L]; [|destruct (Z_lt_le_dec x (D + N)) as [L2|L2]].
      - apply (rd_of_stk m' (S - 4512) spc STc). lia.
      - apply (rd_of_bytes m' (p + 18) X' XB). rewrite XL. lia.
      - apply (rd_of_stk m' (S - 4512) spc STc). lia. }
    assert (SUB : sub_fp [(D, D + N); (spc - 2224, spc)] (ctrl_lay_block_W p S)).
    { intros x Hx. unfold ctrl_lay_block_W, CTRL_LAY_BLOCK_K in Hx. cbn [outside] in *. lia. }
    split.
    - apply LC_intro.
      + apply (rw_cells_transport rsegs _ mc m' _ _ FR MUc WMc).
        unfold SAVES. cbn [disjoint_from cells_size csize]. lia.
      + apply (fl_stk _ mc m' _ _ ST MUc WMc). intros x Hx.
        destruct (Z_lt_le_dec x spc) as [L|L].
        * right. apply (rd_of_stk m' (S - 4512) spc STc). lia.
        * left. cbn [outside]. lia.
      + apply (munch_trans _ m mc m' MU). eapply munch_weaken; [|exact MUc].
        intros x Hx. cbn [app outside] in Hx |- *. lia.
      + exact (wmono_trans rsegs m mc m' WM WMc).
      + exact MIc.
      + exact BKc.
      + apply (bytes_at_transport rsegs _ mc m' f fr Bf MUc). rewrite FL. cbn [disjoint_from]. lia.
    - apply (FI_keep_on mc m' _ frb sfr spc j w120 FIH MUc WMc SUB). intros x _.
      destruct (rc_outside_dec [(D, D + N); (spc - 2224, spc)] x) as [Ho|Ho];
        [left; exact Ho | right; exact (RD x Ho)].
  Qed.

  (* frame_shadow_rwcells (ctrl_lay_block.v:990-1014): the premise `shadow_rw mm` -> the 12 shadow bytes it reads. *)
  Lemma frame_shadow_rwcells_on : forall (mm : word -> option byte) (frb : Z),
    frb mod 8 = 0 -> frb + 96 <= APPMEM_END ->
    (forall i, 0 <= i < 96 -> app_mem (frb + i)) ->
    shadow_rw_on (fun a => shadow_addr frb <= a < shadow_addr frb + 12) mm ->
    exists junk, length junk = 12%nat /\ rw_cells rsegs mm (shadow_addr frb) [CB 12 junk].
  Proof.
    intros mm frb Hm Hhi Happ Hsr.
    assert (Hshlo : 0 <= shadow_addr frb).
    { pose proof (Happ 0 ltac:(lia)) as A0. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A0.
      unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
    assert (Hshhi : shadow_addr frb + 12 <= 2^64).
    { unfold shadow_addr, ASAN_K, APPMEM_END in *. Z.div_mod_to_equations. lia. }
    assert (Hin : forall i, 0 <= i < 12 -> in_shadow (shadow_addr frb + i)).
    { intros i Hi. replace (shadow_addr frb + i) with (shadow_addr (frb + 8 * i))
        by (rewrite sh_add8 by exact Hm; reflexivity).
      apply rt_app_shadow. apply Happ. lia. }
    assert (Hrd : forall i, (i < 12)%nat -> exists b, mrd rsegs mm (wa (shadow_addr frb + Z.of_nat i)) = Some b).
    { intros i Hi. destruct (Hsr (shadow_addr frb + Z.of_nat i) ltac:(cbv beta; lia) (Hin (Z.of_nat i) ltac:(lia)))
        as (_ & b & Hb). exists b. exact Hb. }
    destruct (bytes_at_of_rd 12 mm (shadow_addr frb) Hshlo ltac:(cbn [Z.of_nat]; lia) Hrd) as (junk & Hjl & Hjba).
    exists junk. split; [exact Hjl|].
    split; [split|].
    - cbn [cells_wf cell_wf]. split; [exact Hjl | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hjba.
    - cbn [cells_size csize]. split; [exact Hshlo|]. split; [cbn [Z.of_nat]; lia|].
      intros i Hi. cbn [Z.of_nat] in Hi.
      exact (proj1 (Hsr (shadow_addr frb + i) ltac:(cbv beta; lia) (Hin i ltac:(lia)))).
  Qed.

  (* ---- stretch k = 7 (ctrl_lay_block_F_7.v:122-240), with its Section-local Ltacs (F_7.v:133-144) verbatim ---- *)
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

  Lemma ctrl_lay_block_F_7_on : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte)
      (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    rng RNG (S - K) K -> rng RNG frb 24 -> rng RNG (shadow_addr frb) 16 ->
    FI_on mc frb sfr spc j w120 -> shadow_rw_on (lay_F_R3_shadow_R FS p) mc -> sfr <> 0 -> LC mc gj LAY ->
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
      x28 x29 x30 x31 RWIN RFRB RSHA (HK & HFLAG & ACc & FPc & TLc & AWo) SRc Hsfr LCH.
    pose proof (fk_facts_on frb sfr spc j w120 HK) as (FR8 & _ & _ & _ & FW & FAP & _ & FSlo & _).
    specialize (HFLAG Hsfr).
    destruct HK as [(E0 & _ & _)|(Hj & Efr & Esfr & Espc & Ew)]; [exfalso; exact (Hsfr E0)|].
    subst sfr spc w120.
    (* route (C): the side frame's 16 shadow bytes are in the class-1 block, so in R3 *)
    pose proof (fun i Hi => ctrl_lay_block_F_R2_on.lay_on_frame_sh_block FS j i Hj Hi) as FRB.
    rewrite <- Efr in FRB.
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
    (* route (C): the 16 wview facts at the stretch's start memory mc, from SRc (was: at m, from SR0) *)
    assert (FSW16 : forall i, 0 <= i < 16 -> wview rsegs mc (wa (frb / 8 + ASAN_K + i)) <> None).
    { intros i Hi. replace (frb / 8 + ASAN_K + i) with (shadow_addr (frb + 8 * i))
        by (rewrite sh_add8 by exact FR8; unfold shadow_addr; lia).
      exact (proj1 (SRc _ (or_introl (FRB i Hi)) (rt_app_shadow _ (PApp (frb + 8 * i) ltac:(lia))))). }
    assert (FRB12 : forall a, shadow_addr frb <= a < shadow_addr frb + 12 -> lay_F_R3_shadow_R FS p a).
    { intros a Ha. left. replace a with (shadow_addr (frb + 8 * (a - shadow_addr frb)))
        by (rewrite sh_add8 by exact FR8; lia).
      apply FRB. lia. }
    assert (FWa : wview rsegs m (wa fa) <> None) by exact (stk_wv m FS (FS + FS_SIZE) fa PStk ltac:(lia)).
    pose proof LCH as (_ & _ & _ & WMc & MIc & _ & _).
    destruct (frame_shadow_rwcells_on mc frb FR8 ltac:(lia) FAP (shadow_rw_on_mono _ _ mc FRB12 SRc))
      as (junk & _ & HSH).
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
    apply evtF_done. unfold ctrl_lay_block_F_7.lay_F_pre_release. cbv beta.
    do 2 eexists. split; [reflexivity|].
    split; [exact MUcc|]. split; [exact WMcc|]. split; [exact RMcc|]. split; [exact MIc|].
    split; [exact HFB | exact HSH].
  Qed.

  (* The memcpy's region at its call (header (1)): asan_memcpy_shadow_R (asan_memcpy_c_on.v:25) at a0 = p + 18,
     a1 = frb + 32, a2 = 32, on the side frame, is inside R3. *)
  Lemma lay_F_R3_memcpy_R : forall frb sfr spc j w120, FK frb sfr spc j w120 -> sfr <> 0 ->
    forall a, asan_memcpy_shadow_R (Z_to_bv 64 (p + 18)) (Z_to_bv 64 (frb + 32)) (Z_to_bv 64 32) a ->
      lay_F_R3_shadow_R FS p a.
  Proof.
    intros frb sfr spc j w120 HK Hs a H.
    destruct HK as [(E0 & _) | (Hj & Efr & _)]; [exfalso; exact (Hs E0)|].
    pose proof FP0 as (_ & _ & _ & _ & _ & _ & _ & _ & (FSpos & FS4K & _ & PApp & _) & _).
    assert (Ar : app_mem (frb + 32)).
    { apply PApp. rewrite Efr. replace (fs_M 1) with 8192 in Hj by reflexivity.
      unfold fs_frame, fs_B, FS_SIZE. cbn [Z.of_nat Pos.of_succ_nat]. change (2 ^ 20) with 1048576.
      change (2 ^ 1) with 2. lia. }
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ar.
    unfold asan_memcpy_shadow_R in H.
    rewrite (unsigned_lit (p + 18)) in H by lia. rewrite (unsigned_lit 32) in H by lia.
    rewrite (unsigned_lit (frb + 32)) in H by lia.
    destruct H as [H|H]; [left | right; exact H].
    subst frb. exact (lay_on_frame_out_block FS j a FS4K Hj H).
  Qed.

  (* The copy's post: lay_F_R3_post_args (ctrl_lay_block_F_R3.v:256-267) with FI_on, plus the transport from the pre
     memory mc0. *)
  Definition lay_F_R3_post_args_on (mc0 : word -> option byte) (frb sfr spc j : Z) (w120 : word)
      : machine_state -> Prop :=
    fun ms' => exists (mc' : word -> option byte) (gj' : list byte)
                 (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
      ms' = MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
                    x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f)
                    (Z_to_bv 64 (p + 18)) x22 x23
                    (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
                    x28 x29 x30 x31)
               F (Z_to_bv 64 0x85840) fc None mc' (seg_rom rsegs) /\
      FI_on mc' frb sfr spc j w120 /\ LC mc' gj' BASE /\
      munch [(p + 18, p + 18 + 32); (spc - ASAN_MEMCPY_K, spc)] mc0 mc' /\
      (forall P : Z -> Prop, shadow_rw_on P mc0 -> shadow_rw_on P mc').

  (* 0x8583c: the checked copy of the 32 bytes at src (the box result at frb + 32) into the output block, then the
     ly_args entry at 0x85840 (ctrl_lay_block_F_R3.v:272-351). *)
  Lemma lay_F_R3_cpy_on : forall (RNG : footprint) (mc : word -> option byte) (gj X sb : list byte)
      (src frb sfr spc j : Z)
      (w120 xra x5 x6 x7 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
    FI_on mc frb sfr spc j w120 ->
    shadow_rw_on (asan_memcpy_shadow_R (Z_to_bv 64 (p + 18)) (Z_to_bv 64 src) (Z_to_bv 64 32)) mc ->
    LC mc gj X ->
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
    evtF rsegs RNG (lay_F_R3_post_args_on mc frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               (Z_to_bv 64 (p + 18)) (Z_to_bv 64 src) (Z_to_bv 64 32) x13 x14 x15 x16 x17
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) x22 x23
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x8583c) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj X sb src frb sfr spc j w120 xra x5 x6 x7 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31
      FIH SRM LCH SB SL ESB RS DS AS AE DSW RB RIMG RSPW RROW RSRC SHSP SHROW SHSRC.
    pose proof (lay_F_R3_LC_addr_p mc gj X LCH) as ARc.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FBc).
    pose proof (fk_spc_on frb sfr spc j w120 (proj1 FIH)) as Hspc.
    pose proof FIH as (_ & _ & ACc & _).
    step.
    assert (U18 : bv_unsigned (Z_to_bv 64 (p + 18)) = p + 18) by (apply unsigned_lit; lia).
    assert (U32 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
    assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 spc) = spc)
      by (apply unsigned_lit; pose proof HHM; unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in *;
          pose proof (zr_word sp) as Rsp; unfold inr64 in Rsp; lia).
    pose proof MEMCF as HM. unfold asan_memcpy_contract_F_on in HM. cbv zeta in HM.
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
      - exact SRM.
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
                -> & MUc & WMc & MIc & STc & RWc & _ & _ & SRT).
    rewrite U18, U32, USP in MUc. rewrite USP in STc. rewrite U18, U32 in RWc.
    change (Z.to_nat 32) with 32%nat in RWc.
    rewrite ESB in RWc.
    destruct (LC_FI_memcpy_on mc m' gj X BASE (p + 18) 32 frb sfr spc j w120 LCH FIH
                ltac:(lia) ltac:(lia) ltac:(lia) MUc WMc MIc STc RWc) as (LC2 & FI2).
    rewrite (ret_pc_even 0x85840) by lia.
    apply evtF_done. unfold lay_F_R3_post_args_on.
    do 20 eexists. split; [reflexivity|]. split; [exact FI2 | split; [exact LC2 | split; [| exact SRT]]].
    first [ exact MUc
          | eapply munch_weaken; [| exact MUc]; intros x Hx; cbn [outside] in Hx |- *; unfold ASAN_MEMCPY_K in *; lia ].
  Qed.

  (* 0x85828 -> 0x85840: `li a1,1; bne a0,a1,0x85840` (ctrl_lay_block_F_R3.v:357-401). *)
  Lemma lay_F_R3_box_arm_on : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte)
      (r frb sfr spc j : Z) (w120 : word)
      (xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    FI_on mc frb sfr spc j w120 -> shadow_rw_on (lay_F_R3_shadow_R FS p) mc -> sfr <> 0 ->
    LC mc gj ly_zero -> addressable mc (frb + 32) 32 ->
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
    evtF rsegs RNG (lay_F_R3_post_args_on mc frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
               (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18))
               (Z_to_bv 64 md) (Z_to_bv 64 (frb + 32))
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               t3' t4' t5' t6')
          F (Z_to_bv 64 0x85828) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj r frb sfr spc j w120 xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      FI' SR' Hs' LC' AO' RR R1 Rn1 RO AE DP DW RWIN RB RIMG RSPW RROW RSRC SHSP SHROW SHSRC.
    assert (RC : r = -1 \/ r = 0 \/ r = 1) by (clear -RR; lia).
    destruct RC as [E|[E|E]]; subst r; step; step;
      try (lazymatch goal with |- context [bv_eqb ?u ?v] =>
             let e := eval vm_compute in (bv_eqb u v) in change (bv_eqb u v) with e end);
      cbn [negb]; cbv iota.
    1, 2: (* r <> 1: BASE = ly_zero, so the zeroed output block already holds BASE; the memory is unchanged *)
      rewrite <- (Rn1 ltac:(clear; lia)) in LC';
      apply evtF_done; unfold lay_F_R3_post_args_on; do 20 eexists;
      (split; [reflexivity|]); split; [exact FI' | split; [exact LC' | split; [apply munch_refl | exact (fun P H => H)]]].
    (* r = 1: the output block holds BASE; copy it to p + 18 *)
    destruct (R1 eq_refl) as (SB & SL).
    step. step. step.
    replace (frb + 64) with (frb + 32 + 32) in AE, DP, DW by ring.
    eapply lay_F_R3_cpy_on;
      [exact FI' | exact (shadow_rw_on_mono _ _ mc (lay_F_R3_memcpy_R frb sfr spc j w120 (proj1 FI') Hs') SR')
       | exact LC' | exact SB | exact SL | reflexivity | exact RO | exact DP | exact AO' | exact AE
       | exact DW | exact RB | exact RIMG | exact RSPW | exact RROW | exact RSRC | exact SHSP | exact SHROW
       | exact SHSRC].
  Qed.

  (* ---- stretch k = 6 at g = 0 (ctrl_lay_block_F_R3.v:407-436), FI -> FI_on; memory unchanged ---- *)
  Definition ly_args_F_R3_post_on (mc0 : word -> option byte) (gj : list byte) (frb sfr spc j : Z) (w120 : word)
      : machine_state -> Prop :=
    fun ms' => exists (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
      ms' = MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
                    x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) x19 x20 x21 x22 x23
                    (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
                    x28 x29 x30 x31)
               F (Z_to_bv 64 0x85884) fc None mc0 (seg_rom rsegs) /\
      FI_on mc0 frb sfr spc j w120 /\ LC mc0 gj LAY.

  Lemma ly_args_F_R3_g0_on : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z)
      (w120 : word) (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
    g = 0 -> FI_on mc frb sfr spc j w120 -> LC mc gj BASE ->
    evtF rsegs RNG (ly_args_F_R3_post_on mc gj frb sfr spc j w120)
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
    apply evtF_done. unfold ly_args_F_R3_post_on. do 21 eexists.
    split; [reflexivity|]. split; [exact FIH|].
    replace LAY with BASE; [exact LCH|].
    unfold ctrl_lay_block.LAY, ctrl_lay_block.BASE, ly_lay. rewrite (proj2 (Z.eqb_eq g 0) G0). reflexivity.
  Qed.

  (* ---- the region's whole run (0x85828 -> 0x858f4): lay_F_R3_box_arm_on (k = 5), ly_args_F_R3_g0_on (k = 6 at
     g = 0), ctrl_lay_block_F_7_on (k = 7) and ctrl_lay_block_F_R3.lay_F_R3_release.  The post: lay_F_R3_end
     (ctrl_lay_block_F_R3.v:444-462) with FI_on and the transport from mc0 to the end memory m4. ---- *)
  Definition lay_F_R3_end_on (mc0 : word -> option byte) (gj : list byte) (frb spc j : Z) (w120 : word)
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
      FI_on mc1 frb frb spc j w120 /\ LC mc1 gj1 LAY /\
      (* k = 7 (lay_F_pre_release, ctrl_lay_block_F_7.v:117-120) *)
      munch [(shadow_addr frb, shadow_addr frb + 16); (frb, frb + 8)] mc1 m3 /\
      wmono rsegs mc1 m3 /\ rd_mono mc1 m3 /\
      (* the release (lay_F_R3_release) *)
      munch [(fs_flag FS 1 j, fs_flag FS 1 j + 1)] m3 m4 /\ wmono rsegs m3 m4 /\ rd_mono m3 m4 /\
      mem_inv rsegs m4 /\ rw_cells rsegs m4 (fs_flag FS 1 j) [C1 (Z_to_bv 8 0)] /\
      w120 = Z_to_bv 64 (fs_flag FS 1 j) /\
      (* route (C): every shadow region present at the start memory mc0 is present at the end memory m4 *)
      (forall P : Z -> Prop, shadow_rw_on P mc0 -> shadow_rw_on P m4).

  Lemma lay_F_R3_run_on : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte)
      (r frb sfr spc j : Z) (w120 : word)
      (xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    FI_on mc frb sfr spc j w120 -> shadow_rw_on (lay_F_R3_shadow_R FS p) mc ->
    LC mc gj ly_zero -> addressable mc (frb + 32) 32 ->
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
    evtF rsegs RNG (lay_F_R3_end_on mc gj frb spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
               (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18))
               (Z_to_bv 64 md) (Z_to_bv 64 (frb + 32))
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               t3' t4' t5' t6')
          F (Z_to_bv 64 0x85828) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj r frb sfr spc j w120 xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      FI0 SRc LC0 AO0 RR R1 Rn1 RO AE DP DW RWIN RB RIMG RSPW RROW RSRC SHSP SHROW SHSRC Hg0 Hsfr RFRB RSHA R120 RFA.
    (* the side frame: FK's second disjunct *)
    pose proof FI0 as (HK & _).
    destruct HK as [(E0 & _) | (Hj & Efr & Esfr & Espc & Ew)]; [exfalso; exact (Hsfr E0)|].
    (* k = 5 *)
    eapply evtF_cut.
    { exact (lay_F_R3_box_arm_on RNG mc gj r frb sfr spc j w120 xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7'
               t3' t4' t5' t6' FI0 SRc Hsfr LC0 AO0 RR R1 Rn1 RO AE DP DW RWIN RB RIMG RSPW RROW RSRC SHSP SHROW
               SHSRC). }
    intros ms1 (mc1 & gj1 & y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y22 & y23
                & y28 & y29 & y30 & y31 & -> & FI1 & LC1 & MU1 & SRT1).
    (* k = 6 at g = 0 *)
    eapply evtF_cut.
    { exact (ly_args_F_R3_g0_on RNG mc1 gj1 frb sfr spc j w120 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23
               y28 y29 y30 y31 Hg0 FI1 LC1). }
    intros ms2 (z1 & z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z19 & z20 & z21 & z22 & z23
                & z28 & z29 & z30 & z31 & -> & FI2 & LC2).
    (* k = 7, with R3 at mc1 from k = 5's transport *)
    eapply evtF_cut.
    { exact (ctrl_lay_block_F_7_on RNG mc1 gj1 frb sfr spc j w120 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z19
               z20 z21 z22 z23 z28 z29 z30 z31 RWIN RFRB RSHA FI2 (SRT1 _ SRc) Hsfr LC2). }
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
    pose proof FI2 as (_ & _ & _ & FPc & _).
    pose proof FPc as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & PStkc) & _).
    pose proof (stk_mono mc1 m3 _ _ PStkc WM3 RM3) as PStk3.
    unfold FS_SIZE in PStk3.
    assert (FWa : wview rsegs m3 (wa (fs_flag FS 1 j)) <> None)
      by (apply (stk_wv m3 FS (FS + 11571200)); [exact PStk3 | lia]).
    destruct (rd_of_stk m3 FS (FS + 11571200) PStk3 (fs_flag FS 1 j) ltac:(lia)) as (fb & Hfb).
    (* the release *)
    eapply evtF_cut.
    { eapply ctrl_lay_block_F_R3.lay_F_R3_release with (frb := frb) (fa := fs_flag FS 1 j);
        [ lia | lia | lia | lia | exact FB3 | exact FWa | exists fb; exact Hfb | exact MI3 | exact R120 | exact RFA ]. }
    intros ms4 (a0'' & m4 & -> & MU4 & WM4 & RM4 & MI4 & HF4).
    apply evtF_done. unfold lay_F_R3_end_on.
    exists z1, z5, z6, z7, a0'', z11, z12, z13, z14, z15, z16, z17, z19, z20, z21, z22, z23, z28, z29, z30, z31,
      mc1, gj1, m3, m4.
    split; [reflexivity|]. split; [exact MU1|]. split; [exact FI2|]. split; [exact LC2|].
    split; [exact MU3|]. split; [exact WM3|]. split; [exact RM3|].
    split; [exact MU4|]. split; [exact WM4|]. split; [exact RM4|]. split; [exact MI4|].
    split; [exact HF4|]. split; [reflexivity|].
    intros P HP.
    exact (A.ShadowRwOnT.shadow_rw_on_mem_mono P m3 m4
             (A.ShadowRwOnT.shadow_rw_on_mem_mono P mc1 m3 (SRT1 P HP) WM3 RM3) WM4 RM4).
  Qed.

End L5R_on.

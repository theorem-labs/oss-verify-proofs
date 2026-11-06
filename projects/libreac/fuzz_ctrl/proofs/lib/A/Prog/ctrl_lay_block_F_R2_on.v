(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 821 of its 838 lines of code are new or changed and 231 lines of the source are left out. *)
(* ctrl_lay_block, image A (asan, entry 0x855f4): ROUTE (C) twin of region R2's run (0x8566c -> 0x85718 -> the box
   call 0x85824, then the `jal` to reac_box_model_block).  A Theorem Labs lane (a Theorem Labs lane),
   brief (a working note, not in this delivery).
   rule 24: no function proved.  This file proves no function (kind: segment lemma).

   lay_F_R2_run_on is lay_F_R2_run (ctrl_lay_block_F_R2.v (at head lib/A/Prog/ctrl_lay_block_F_R2.v:586-625; written on a working branch 63a02bb46d7)) in
   the route (C) form of record (a Theorem Labs lane's ASSIGN.md (a working note, not in this delivery; its form frozen by a Theorem Labs lane 09:38Z) + the 10:34Z amendment):
   - PRE: the Section's universal `SR0 : shadow_rw m` (ctrl_lay_block_F_R2.v:150) becomes
     `SR0 : shadow_rw_on (lay_F_R2_shadow_R FS p) m` (R2 below); the callee contract asan_memset_contract_F becomes
     a Theorem Labs lane's asan_memset_contract_F_on (lib/A/Prog/asan_memset_cF_on.v, 83ab88c3325), by name.
   - POST: FI's `shadow_rw mc` conjunct (ctrl_lay_block.v:1100) leaves the post (FI_on below) and the post gains the
     transport `forall P, shadow_rw_on P mc0 -> shadow_rw_on P mc` from the region's START memory mc0 (the run's pre
     memory) to its END memory mc (a Theorem Labs lane's request, 12:58Z).
   - lay_F_R2_shadow_R_sub proves R2 a subset of a Theorem Labs lane's ctrl_lay_block_shadow_R (lib/A/Prog/ctrl_lay_block_c.v:392,
     a working branch 0bf62760c4a, blob c36731db371), binders in its order (S FS p f md g fr mb nb a).

   R2 = lay_F_R2_shadow_R FS p = asan_stack_malloc_shadow_R FS 1 (the shadow of the class-1 fake-stack block) \/
        sh_word_on (p + 18) 32 (the aligned shadow words of the output block).
   DERIVATION (for the auditor a Theorem Labs lane; every use of SR0 in the original, verified against the source; a Theorem Labs lane's table
   shadow-rw-consumers-A.md row 418 (a working note, not in this delivery)):
   (1) STORES, 12 shadow bytes of the class-1 frame [frb / 8 + ASAN_K, + 12): fk_facts's conjunct ctrl_lay_block.v:520
       (proved from SR0 at :550) gives `wview m` of them; ctrl_lay_block_F_R2.v:265 destructs it as SW12 and the Ltac
       lay_wv (F_R2.v:223) takes it for the 12 frame-shadow stores F_R2.v:292-300 (0xf1 x4 at +0..3, 0xf3 x4 at
       +8..11) and :314-336 (0x00 x4 at +4..7).
   (2) READS, the first 8 of those bytes [frb / 8 + ASAN_K, + 8): F_R2.v:308 `proj2 (SR0 ...)` (mrd present at the
       store-time memory through RM), which tracks the 4 middle zeros for the box output's addressability.
   (3) READS by the callee: F_R2.v:344 `shadow_rw_mono m _ SR0 WM RM` -> F_R2.v:377, asan_memset_contract_F's shadow
       premise at the memset of [p + 18, p + 50); in the _on contract that premise is
       `shadow_rw_on (asan_memset_shadow_R a0 a2)` (asan_memset_c_on.v:23) with a0 = p + 18, a2 = 32, i.e.
       sh_word_on (p + 18) 32 (lay_F_R2_memset_R below).
   (4) the post: ME's / FI's `shadow_rw mp` (F_R2.v:418, :504) from the memset post: in route (C) the transport.
   Through fk_facts only (its non-shadow conjuncts, no shadow access): lay_Wf_sub (F_R2.v:341), lay_row_out_Wf
   (F_R2.v:347), lay_fw_rt (F_R2.v:408).  The stretch k = 3 (ctrl_lay_block_F_3.v, F_R2.v:604) takes no SR0: its one
   shadow load, the kind-byte check at shadow_addr f (F_3.v:271), is justified by addressable mc f 24 (LC_addr_f), not
   by shadow_rw; the jal (F_R2.v:609) has no data access.
   The run lemma takes the SIDE frame only (sfr <> 0, F_R2.v:576): frb = fs_frame FS 1 j, 0 <= j < fs_M 1, chosen by
   __asan_stack_malloc_1, so its 12 bytes lie in the shadow of the class-1 block (lay_on_frame_sh_block below); the
   frame index is a binder of the run lemma, not of the Section, so the Section's region names the block, as
   asan_stack_malloc_c_on.v and ctrl_lay_block_shadow_R do.  The real-frame arm (sfr = 0, frame in the window) is not
   taken by the run, so the window's shadow is NOT in R2: lay_F_R2_fwords_on takes `sfr <> 0` (DIFF below).

   RE-PROVED HELPERS (re-based copy allowance, a Theorem Labs lane 23:53Z: instruction proofs verbatim; each named here):
   - FI_on      = Section L's FI (ctrl_lay_block.v:1047-1053) minus its `shadow_rw mc` conjunct (:1050).
   - ME_on      = Section L's ME (ctrl_lay_block.v:581-590) minus its `shadow_rw mc` conjunct (:583).
   - fk_facts_on = fk_facts (ctrl_lay_block.v:515-552) minus its conjunct :520 and the proof lines that give it
                  (:546-547 B8, :549-550); it takes no shadow premise.
   - fk_facts_sw_on = the conjunct :520 for the side frame (sfr <> 0), from SR0 at R2 (the proof lines :546-547, :550).
   - lay_Wf_sub_on (ctrl_lay_block.v:698-744), lay_row_out_Wf_on (:747-786), lay_fw_rt_on (:2421-2487): verbatim, with
     fk_facts -> fk_facts_on (one destruct component fewer) and lay_Wf_sub -> lay_Wf_sub_on.
   - lay_F_pre_box_on, lay_F_boxarm_on, ctrl_lay_block_F_3_on = ctrl_lay_block_F_3.v:207-283 verbatim with FI -> FI_on
     (the stretch passes FI through untouched; the acc_hint override of F_3.v:76 is repeated Local).
   NEW: lay_on_frame_sh_block (class-1 frame shadow inside the class-1 block), lay_F_R2_frame_R, lay_F_R2_memset_R.

   DIFF AGAINST ctrl_lay_block_F_R2.v (instruction proofs VERBATIM):
   - Section F2R -> F2R_on; SR0's type (above); MEMSF : asan_memset_contract_F -> asan_memset_contract_F_on.
   - lay_F_R2_disp_post -> lay_F_R2_disp_post_on and lay_F_R2_box_pre -> lay_F_R2_box_pre_on: FIx -> FI_on, plus the
     last conjunct `forall P, shadow_rw_on P mc0 -> shadow_rw_on P mc`.
   - lay_F_R2_fwords_on: premise `sfr <> 0` added after FKx (intro Hs); fk_factsx's destruct -> fk_facts_on's (SW12 from
     fk_facts_sw_on); F_R2.v:308 SR0 -> SR0 at R2 (membership lay_F_R2_frame_R); F_R2.v:344 shadow_rw_mono ->
     A.ShadowRwOnT.shadow_rw_on_mem_mono; the memset premise (F_R2.v:377) -> shadow_rw_on_mono by lay_F_R2_memset_R;
     after the memset post, SRT (the transport mc -> mp: shadow_rw_on_mem_mono over the fwords stores, then the memset
     post's transport conjunct); MEx -> ME_on (one split / one destruct component fewer: SRp / SRm); FIc without SRm;
     the final split adds SRT; lay_Wf_subx / lay_row_out_Wfx / lay_fw_rtx -> the _on copies.
   - lay_F_R2_on: passes Hs to lay_F_R2_fwords_on.
   - lay_F_R2_run_on: stretch k = 3 -> ctrl_lay_block_F_3_on; the jal is ctrl_lay_block_F_R2.lay_F_R2_jal (no shadow,
     not copied); the final split adds the transport of lay_F_R2_on (the stretch and the jal keep the memory).

   PROVENANCE: as ctrl_lay_block_F_R2.v (image root (internal path), ELF
   sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd, FACTS of record ed6b6b7b0ab). *)
(* FIRST, before ctrl_lay_block_F_common loads ctrl_lay_block: A.ShadowRwOnT Requires A.Prog.MemMono, whose
   `Ltac footprint_after_store ::=` (MemMono.v:207) is non-local and is applied when MemMono is loaded; loaded after
   ctrl_lay_block it would replace ctrl_lay_block's own redefinition (ctrl_lay_block.v:215), which carries
   ctrl_lay_block.rd_mono hypotheses across stores (measured: with ShadowRwOnT Required below ctrl_lay_block,
   `rd_mono m mc` was not carried and F_R2.v:306's `apply RM` failed).  Loaded here, MemMono's comes first and
   ctrl_lay_block's wins, as in ctrl_lay_block_F_R2.v. *)
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
  asan_memset_c_on asan_memset_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* the jal (no shadow access, not copied) and stretch k = 3's Ltacs, Required qualified *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ctrl_lay_block_F_R2 ctrl_lay_block_F_3.
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

(* ---- R2, and its subset proof against a Theorem Labs lane's ctrl_lay_block_shadow_R ---- *)
Definition lay_F_R2_shadow_R (FS p : Z) (a : Z) : Prop :=
  asan_stack_malloc_shadow_R FS 1%nat a \/ sh_word_on (p + 18) 32 a.

Lemma lay_F_R2_shadow_R_sub : forall (S FS p f md g : Z) (fr mb nb : list byte) (a : Z),
  lay_F_R2_shadow_R FS p a -> ctrl_lay_block_shadow_R S FS p f md g fr mb nb a.
Proof.
  intros S FS p f md g fr mb nb a [H|H]; unfold ctrl_lay_block_shadow_R.
  - right; right; left; exact H.
  - right; right; right; left; exact H.
Qed.

(* The 16 shadow bytes of a class-1 frame fs_frame FS 1 j (j < fs_M 1 = 8192, fs_B 1 = 128) lie in the shadow of the
   class-1 block [fs_frame FS 1 0, + 2^20), whose shadow is asan_stack_malloc_shadow_R FS 1 (131072 bytes). *)
Lemma lay_on_frame_sh_block : forall (FS j i : Z), 0 <= j < fs_M 1 -> 0 <= i < 16 ->
  asan_stack_malloc_shadow_R FS 1%nat (shadow_addr (fs_frame FS 1 j + 8 * i)).
Proof.
  intros FS j i Hj Hi. replace (fs_M 1) with 8192 in Hj by reflexivity.
  unfold asan_stack_malloc_shadow_R, fs_frame, fs_B, shadow_addr. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 20) with 1048576. change (2 ^ 1) with 2.
  Z.div_mod_to_equations. lia.
Qed.

Section F2R_on.
  (* Section L's variables and hypotheses of ctrl_lay_block.v, verbatim (as ctrl_lay_block_F_R2.v:95-163), except SR0
     (route (C): the region R2) and the ONE callee contract this run applies, asan_memset_contract_F_on, of exactly
     a Theorem Labs lane's type (lib/A/Prog/asan_memset_cF_on.v), by name, never restated. *)
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
  (* route (C): the shadow bytes R2 names, present at the Section's memory m (header, "R2 = ..."). *)
  Hypothesis SR0 : shadow_rw_on (lay_F_R2_shadow_R FS p) m.
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

  (* The ONE callee contract this run applies, route (C) form, as a Section hypothesis of exactly its type. *)
  Hypothesis MEMSF : asan_memset_contract_F_on.

  Local Notation SP2 := ((S - 128) / 32 * 32).

  (* ---- Section L's predicates and helpers, at this section's variables (as ctrl_lay_block_F_R2.v:171-200; the
     SR0-taking ones are re-proved below) ---- *)
  Local Notation FKx := (FK sp FS).
  Local Notation WfX := (Wf sp FS).
  Local Notation SAVESx := (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).
  Local Notation lay_Xx := (lay_X sp FS).
  Local Notation BIx := (BI ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS).
  Local Notation LCx := (LC ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS fr).
  Local Notation SP2_factsx :=
    (SP2_facts sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg SP16 FL K9 TM P0 MDP).
  Local Notation STW0x := (STW0 sp m ST0).
  Local Notation lay_addr_keepx :=
    (lay_addr_keep sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg SP16 FL K9 TM P0 MDP HHM AR FP0).
  Local Notation lay_acx :=
    (lay_ac sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg FL K9 TM P0 MDP AC0 HHM ARDJ FP0).
  Local Notation lay_f_outx :=
    (lay_f_out sp tp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg DJ2 FL K9 TM P0 DB1 MDP HHM HAE AF FP0).
  Local Notation lay_out_fpw_dx := (lay_out_fpw_d sp tp m p f FS FP0).
  Local Notation LC_introx :=
    (LC_intro ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f md g FS fr mb nb Rp Rf Rmd Rg DJ3m DB3 DBN MDP ARDJ AMD FPM).
  Local Notation lay_rw_consx :=
    (lay_rw_cons sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg FL TM MDP).
  (* the Section L constants the re-proved helpers name, under their own names (the copies' text is verbatim) *)
  Local Notation SP2_facts :=
    (ctrl_lay_block.SP2_facts sp m p f md g fr tb mb nb gb Rp Rf Rmd Rg SP16 FL K9 TM P0 MDP).
  Local Notation lay_out_fpw_d := (ctrl_lay_block.lay_out_fpw_d sp tp m p f FS FP0).
  Local Notation lay_num := (ctrl_lay_block.lay_num sp m p f md g FS fr tb mb nb gb Rp Rf Rmd Rg FL TM MDP).
  Local Notation lay_fp_tls := (ctrl_lay_block.lay_fp_tls sp tp p f FS).
  Local Notation lay_cls := (ctrl_lay_block.lay_cls FS).
  Local Notation LC_addr_fl :=
    (ctrl_lay_block.LC_addr_f ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f md g FS fr tb mb nb gb
       Rp Rf Rmd Rg SP16 DJ2 FL K9 TM P0 MDP HHM AF AR FP0).

  (* ---- re-proved helpers (header, RE-PROVED HELPERS) ---- *)

  (* Section L's FI (ctrl_lay_block.v:1047-1053) without its `shadow_rw mc` conjunct (:1050). *)
  Definition FI_on (mc : word -> option byte) (frb sfr spc j : Z) (w120 : word) : Prop :=
    FKx frb sfr spc j w120 /\
    (sfr <> 0 -> bytes_at rsegs mc (frb + 120) (le8 w120)) /\
    asan_cells mc /\
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
    ctrl_lay_block_tls mc (bv_unsigned tp) FS (S - K) S /\
    (forall x, S - K <= x < S -> (x < frb \/ frb + 96 <= x) -> addressable mc x 1).

  (* Section L's ME (ctrl_lay_block.v:581-590) without its `shadow_rw mc` conjunct (:583). *)
  Definition ME_on (frb sfr : Z) (w120 : word) (mc : word -> option byte) : Prop :=
    munch (ctrl_lay_block_W p S ++ lay_Xx) m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    asan_cells mc /\ stk rsegs mc (S - K) S /\
    rw_cells rsegs mc (S - 96) SAVESx /\
    rw_cells rsegs mc (p + 18) [CB 32 ly_zero] /\
    bytes_at rsegs mc f fr /\ (sfr <> 0 -> bytes_at rsegs mc (frb + 120) (le8 w120)) /\
    addressable mc (p + 18) 32 /\ addressable mc f 24 /\ addressable mc (frb + 32) 32 /\
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
    ctrl_lay_block_tls mc (bv_unsigned tp) FS (S - K) S /\
    (forall x, S - K <= x < S -> (x < frb \/ frb + 96 <= x) -> addressable mc x 1).

  (* fk_facts (ctrl_lay_block.v:515-552) without its frame-shadow conjunct (:520): no shadow premise. *)
  Lemma fk_facts_on : forall frb sfr spc j w120, FKx frb sfr spc j w120 ->
    frb mod 8 = 0 /\ FS + 36864 <= frb /\ frb + 96 <= SP2 /\ (spc = SP2 \/ spc = frb) /\
    (forall i, 0 <= i < 96 -> wview rsegs m (wa (frb + i)) <> None) /\
    (forall i, 0 <= i < 96 -> app_mem (frb + i)) /\
    (frb + 96 <= LOWMEM_END \/ HIGHMEM_BEG <= frb) /\
    LOWMEM_END <= frb / 8 + ASAN_K /\ frb / 8 + ASAN_K + 12 <= HIGHMEM_BEG.
  Proof.
    intros frb sfr spc j w120 HK.
    pose proof SP2_facts as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & _).
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5. unfold ASAN_GT in P3.
    unfold CTRL_LAY_BLOCK_K in *.
    assert (B : frb mod 8 = 0 /\ FS + 36864 <= frb /\ frb + 96 <= SP2 /\ (spc = SP2 \/ spc = frb) /\
                (forall i, 0 <= i < 96 -> wview rsegs m (wa (frb + i)) <> None) /\
                (forall i, 0 <= i < 96 -> app_mem (frb + i))).
    { destruct HK as [(Ef & Efr & Esp) | (Hj & Efr & Ef & Esp & Ew)]; subst frb.
      - split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia|].
        intros i Hi. replace (SP2 - 96 + i) with (S - 4512 + (SP2 - 96 + i - (S - 4512))) by lia.
        apply (acl_app_in m (S - 4512) 4512); [exact AW0 | lia].
      - replace (fs_M 1) with 8192 in Hj by reflexivity.
        unfold fs_frame, fs_B in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 1) with 2 in *.
        split; [Z.div_mod_to_equations; lia|]. split; [lia|].
        split; [lia|]. split; [left; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ P5); lia|].
        intros i Hi. apply P4. lia. }
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (app_range frb 96 ltac:(lia) B6) as B7.
    do 7 (split; [assumption|]).
    unfold ASAN_K, LOWMEM_END, HIGHMEM_BEG. split; Z.div_mod_to_equations; lia.
  Qed.

  (* R2's frame part (header (1), (2)): the side frame's shadow bytes are in R2. *)
  Lemma lay_F_R2_frame_R : forall frb sfr spc j w120, FKx frb sfr spc j w120 -> sfr <> 0 ->
    forall i, 0 <= i < 16 -> lay_F_R2_shadow_R FS p (shadow_addr (frb + 8 * i)).
  Proof.
    intros frb sfr spc j w120 HK Hs i Hi.
    destruct HK as [(E0 & _) | (Hj & Efr & _)]; [exfalso; exact (Hs E0)|].
    left. subst frb. exact (lay_on_frame_sh_block FS j i Hj Hi).
  Qed.

  (* fk_facts's conjunct :520 for the side frame, from SR0 at R2 (ctrl_lay_block.v:546-547, :550). *)
  Lemma fk_facts_sw_on : forall frb sfr spc j w120, FKx frb sfr spc j w120 -> sfr <> 0 ->
    (forall i, 0 <= i < 12 -> wview rsegs m (wa (frb / 8 + ASAN_K + i)) <> None).
  Proof.
    intros frb sfr spc j w120 HK Hs.
    destruct (fk_facts_on frb sfr spc j w120 HK) as (B1 & _ & _ & _ & _ & B6 & _).
    assert (B8 : forall i, 0 <= i < 12 -> frb / 8 + ASAN_K + i = shadow_addr (frb + 8 * i)).
    { intros i Hi. rewrite sh_add8 by exact B1. unfold shadow_addr. lia. }
    intros i Hi. rewrite B8 by exact Hi.
    apply (proj1 (SR0 _ (lay_F_R2_frame_R frb sfr spc j w120 HK Hs i ltac:(lia))
                    (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
  Qed.

  (* The memset's region at its call (header (3)): asan_memset_shadow_R (asan_memset_c_on.v:23) at a0 = p + 18,
     a2 = 32 is sh_word_on (p + 18) 32, inside R2. *)
  Lemma lay_F_R2_memset_R : forall a,
    asan_memset_shadow_R (Z_to_bv 64 (p + 18)) (Z_to_bv 64 32) a -> lay_F_R2_shadow_R FS p a.
  Proof.
    intros a H. unfold asan_memset_shadow_R in H.
    rewrite (unsigned_lit (p + 18)) in H by lia. rewrite (unsigned_lit 32) in H by lia.
    right. exact H.
  Qed.

  (* lay_Wf_sub (ctrl_lay_block.v:698-744), fk_facts -> fk_facts_on. *)
  Lemma lay_Wf_sub_on : forall frb sfr spc j n w120, FKx frb sfr spc j w120 -> 0 <= n <= 1 ->
    (n = 0 \/ 0 <= j < fs_M 1) -> sub_fp (WfX frb j n) (ctrl_lay_block_W p S ++ lay_Xx).
  Proof.
    intros frb sfr spc j n w120 HK Hn Hnj.
    destruct (fk_facts_on frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & _).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & _) & _).
    pose proof SP2_facts as (HA32 & HAlo & HAhi).
    assert (S8 : S mod 8 = 0) by (pose proof SP16 as H16; clear -H16; Z.div_mod_to_equations; lia).
    assert (Esh : shadow_addr frb + 16 = shadow_addr (frb + 128))
      by (replace (frb + 128) with (frb + 8 * 16) by lia; symmetry; apply sh_add8; exact FR8).
    intros x Hf. unfold ctrl_lay_block_W, lay_X in Hf.
    apply acl_out_app_inv in Hf. destruct Hf as (HfW & Hf). apply acl_out_app_inv in Hf. destruct Hf as (Hfpw & Hfsh).
    cbn [outside] in HfW, Hfsh. destruct HfW as (HWwin & _). destruct Hfsh as (HWsh & _).
    cbn [fp_w flat_map fp_w1 app outside] in Hfpw.
    destruct Hfpw as (Oh0 & Ofl0 & Ofr0 & Osh0 & Oh1 & Ofl1 & Ofr1 & Osh1 & _).
    unfold Wf. cbn [outside].
    unfold fs_hint, fs_flag, fs_M in Oh1, Ofl1 |- *.
    cbn [Z.of_nat Pos.of_succ_nat] in Oh1, Ofl1 |- *.
    change (2 ^ (14 - 1)) with 8192 in Ofl1 |- *.
    change (2 ^ 15) with 32768 in Ofl1 |- *. change (2 ^ (15 - 1)) with 16384 in Ofl1 |- *.
    split; [exact HWwin|].
    split; [clear -Oh1; lia|].
    assert (Oflag : ~ (FS + 4096 + 32768 - 16384 + j <= x < FS + 4096 + 32768 - 16384 + j + n)).
    { destruct Hnj as [Hn0 | Hjb]; [subst n; lia |
        replace (fs_M 1) with 8192 in Hjb by reflexivity; clear -Ofl1 Hjb Hn; lia]. }
    split; [exact Oflag|].
    destruct HK as [(Ef & Efr & Esp) | (Hj & Efr & Ef & Esp & Ew)].
    - (* real: frame and its shadow are in the window and its shadow *)
      subst frb. unfold CTRL_LAY_BLOCK_K in HWwin, HWsh.
      split; [clear -HWwin HAlo HAhi; lia|].
      split; [| exact I]. rewrite Esh.
      pose proof (acl_sh_ge (SP2 - 96) (S - 4512) ltac:(clear -HAlo; lia)) as G1.
      pose proof (acl_sh_lt (SP2 - 96 + 128) S S8 ltac:(clear -HAhi; lia)) as G2.
      clear -HWsh G1 G2. lia.
    - (* side: frame and its shadow are in the class-1 side-stack ranges (fs_frame kept folded) *)
      subst frb. replace (fs_M 1) with 8192 in Hj by reflexivity.
      assert (B1 : fs_frame FS 1 0 <= fs_frame FS 1 j)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 1) with 2; clear -Hj; lia).
      assert (B2 : fs_frame FS 1 j + 128 <= fs_frame FS 1 (fs_M 1))
        by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 1) with 2; change (2 ^ (14 - 1)) with 8192; clear -Hj; lia).
      split; [clear -Ofr1 B1 B2; lia|].
      split; [| exact I]. rewrite Esh.
      pose proof (acl_sh_ge (fs_frame FS 1 j) (fs_frame FS 1 0) B1) as G1.
      pose proof (acl_sh_ge (fs_frame FS 1 (fs_M 1)) (fs_frame FS 1 j + 128) B2) as G2.
      clear -Osh1 G1 G2. lia.
  Qed.

  (* lay_row_out_Wf (ctrl_lay_block.v:747-786), fk_facts -> fk_facts_on. *)
  Lemma lay_row_out_Wf_on : forall frb sfr spc j n w120 x, FKx frb sfr spc j w120 -> 0 <= n <= 1 ->
    (n = 0 \/ 0 <= j < fs_M 1) -> p + 18 <= x < p + 50 -> outside (WfX frb j n) x.
  Proof.
    intros frb sfr spc j n w120 x HK Hn Hnj Hx.
    destruct (fk_facts_on frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & _).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & _) & _).
    pose proof SP2_facts as (HA32 & HAlo & HAhi).
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    pose proof (acl_app_in m (p + 18) 32 (x - (p + 18)) AR ltac:(clear -Hx; lia)) as Hap.
    replace (p + 18 + (x - (p + 18))) with x in Hap by (clear -Hx; lia).
    pose proof (lay_out_fpw_d (p + 18) (p + 50) x ltac:(right; left; reflexivity) Hx) as Hfpw.
    cbn [fp_w flat_map fp_w1 app outside] in Hfpw.
    destruct Hfpw as (Oh0 & Ofl0 & Ofr0 & Osh0 & Oh1 & Ofl1 & Ofr1 & Osh1 & _).
    assert (Esh : shadow_addr frb + 16 = shadow_addr (frb + 128))
      by (replace (frb + 128) with (frb + 8 * 16) by (clear; lia); symmetry; apply sh_add8; exact FR8).
    assert (Hfrb0 : 0 <= frb) by (clear -FRlo P1; lia).
    assert (HfrbA : frb + 128 <= APPMEM_END) by (clear -FRhi HAhi HAE'; unfold APPMEM_END; lia).
    assert (Osf : ~ (shadow_addr frb <= x < shadow_addr frb + 16)).
    { rewrite Esh. apply acl_sh_out; [exact Hap | exact Hfrb0 | exact HfrbA]. }
    unfold Wf. cbn [outside].
    split; [unfold ly_dj in DJ1; clear -DJ1 Hx; lia|].
    split; [exact Oh1|].
    split.
    { unfold fs_flag, fs_M in Ofl1 |- *. cbn [Z.of_nat Pos.of_succ_nat] in Ofl1 |- *.
      change (2 ^ (14 - 1)) with 8192 in Ofl1. change (2 ^ 15) with 32768 in Ofl1 |- *.
      change (2 ^ (15 - 1)) with 16384 in Ofl1 |- *.
      destruct Hnj as [Hn0 | Hjb]; [subst n; lia |
        replace (fs_M 1) with 8192 in Hjb by reflexivity; clear -Ofl1 Hjb Hn; lia]. }
    destruct HK as [(Ef & Efr & Esp) | (Hj & Efr & Ef & Esp & Ew)].
    - subst frb. split; [| split; [exact Osf | exact I]].
      unfold ly_dj in DJ1. unfold CTRL_LAY_BLOCK_K in DJ1. clear -DJ1 HAlo HAhi Hx. lia.
    - subst frb. split; [| split; [exact Osf | exact I]].
      replace (fs_M 1) with 8192 in Hj by reflexivity.
      assert (B1 : fs_frame FS 1 0 <= fs_frame FS 1 j)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 1) with 2; clear -Hj; lia).
      assert (B2 : fs_frame FS 1 j + 128 <= fs_frame FS 1 (fs_M 1))
        by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 1) with 2; change (2 ^ (14 - 1)) with 8192; clear -Hj; lia).
      clear -Ofr1 B1 B2. lia.
  Qed.

  (* lay_fw_rt (ctrl_lay_block.v:2421-2487), fk_facts -> fk_facts_on, lay_Wf_sub -> lay_Wf_sub_on. *)
  Lemma lay_fw_rt_on : forall frb sfr spc j w120 (mc mp : word -> option byte),
    FKx frb sfr spc j w120 ->
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) ->
    ctrl_lay_block_tls mc (bv_unsigned tp) FS (S - K) S -> addressable mc (S - K) K ->
    munch [(S - K, S); (frb, frb + 24); (shadow_addr frb, shadow_addr frb + 12); (p + 18, p + 50)] mc mp ->
    wmono rsegs mc mp -> rd_mono mc mp ->
    fp [0%nat; 1%nat] mp (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
    ctrl_lay_block_tls mp (bv_unsigned tp) FS (S - K) S /\
    (forall x, S - K <= x < S -> (x < frb \/ frb + 96 <= x) -> addressable mp x 1).
  Proof.
    intros frb sfr spc j w120 mc mp HK FPc TLc AWc MU WM RM.
    destruct (fk_facts_on frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & _ & _ & _).
    pose proof SP2_facts as (_ & _ & SP2hi).
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    pose proof lay_num as (NH0 & NH1 & NM0 & NM1 & NB1 & NF0 & NF1 & NR0 & NR1).
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFS & _ & HWd & _).
    unfold FS_SIZE in HFS, P4.
    assert (E96 : shadow_addr frb + 12 = shadow_addr (frb + 96))
      by (replace (frb + 96) with (frb + 8 * 12) by lia; symmetry; apply sh_add8; exact FR8).
    (* the row is apart from the side stack's header (fp's W-disjointness) *)
    assert (X0 : ly_dj (p + 18) (p + 50) FS (FS + 36864)).
    { assert (IPW : In (p + 18, p + 50) (ctrl_lay_block_W p S))
        by (unfold ctrl_lay_block_W; cbn [In]; right; left; reflexivity).
      assert (IFS : In (FS, fs_frame FS 0 0) (fp_tls (bv_unsigned tp) DT TS C T DB k0 ++ [(FS, fs_frame FS 0 0)]))
        by (apply in_or_app; right; left; reflexivity).
      unfold fp_dj in HWd. rewrite Forall_forall in HWd. pose proof (HWd _ IPW) as H1.
      rewrite Forall_forall in H1. pose proof (H1 _ IFS) as H2. cbn [fst snd] in H2.
      rewrite (NR0 0) in H2. replace (FS + 36864 + 64 * 0) with (FS + 36864) in H2 by lia. exact H2. }
    assert (SUBd : sub_fp [(S - K, S); (frb, frb + 24); (shadow_addr frb, shadow_addr frb + 12); (p + 18, p + 50)]
                     (ctrl_lay_block_W p S ++ lay_Xx)).
    { intros x Hx. pose proof (lay_Wf_sub_on frb sfr spc j 0 w120 HK ltac:(lia) (or_introl eq_refl) x Hx) as Hf.
      unfold Wf in Hf. cbn [outside] in Hf. destruct Hf as (Hw & _ & _ & Hfr & Hsh & _).
      unfold ctrl_lay_block_W, lay_X in Hx. apply acl_out_app_inv in Hx. destruct Hx as (HW & _).
      cbn [outside] in HW. destruct HW as (_ & Hrow & _).
      cbn [outside]. split; [exact Hw|]. split; [lia|]. split; [lia|]. split; [exact Hrow | exact I]. }
    assert (OH : forall x, FS <= x < FS + 36864 ->
      outside [(S - K, S); (frb, frb + 24); (shadow_addr frb, shadow_addr frb + 12); (p + 18, p + 50)] x).
    { intros x Hx. assert (Hap : app_mem x) by (apply P4; lia).
      cbn [outside]. split; [lia|]. split; [lia|].
      split; [rewrite E96; apply acl_sh_out; [exact Hap | lia | unfold APPMEM_END; lia]|].
      split; [unfold ly_dj in X0; lia | exact I]. }
    assert (HCLS : forall c, In c [0%nat; 1%nat] -> lay_cls mp c).
    { intros c Hc. pose proof FPc as (DT' & TS' & C' & T' & DB' & k' & _ & _ & _ & _ & _ & HCL' & _).
      rewrite Forall_forall in HCL'.
      destruct (fl_cls_h _ mc mp FS c OH MU (HCL' c Hc)) as (_ & h & flags & Hh & Hf & Hl & Hb).
      split; [exists h; exact Hh | exists flags; split; [exact Hf | split; assumption]]. }
    destruct (lay_fp_tls mc mp _ FPc TLc MU WM RM SUBd ltac:(intros x Hx; apply OH; lia) HCLS) as [FPp TLp].
    split; [exact FPp|]. split; [exact TLp|].
    intros x Hx Hfx.
    assert (Hap : app_mem x).
    { replace x with (S - K + (x - (S - K))) by lia. apply (acl_app_in m (S - K) K); [exact AW0 | lia]. }
    pose proof (rt_app_shadow x Hap) as Hsx.
    apply (addr_munch _ mc mp x 1 (acl_addr_sub mc (S - K) K x 1 AWc ltac:(lia) ltac:(lia) ltac:(lia)) MU).
    intros i Hi. replace (x + i) with x by lia.
    cbn [outside].
    split.
    { apply (lay_sh_app_out _ (S - K) S Hsx). intros z Hz. replace z with (S - K + (z - (S - K))) by lia.
      apply (acl_app_in m (S - K) K); [exact AW0 | lia]. }
    split.
    { apply (lay_sh_app_out _ frb (frb + 24) Hsx). intros z Hz. replace z with (frb + (z - frb)) by lia.
      apply FAP. lia. }
    split; [rewrite E96; exact (acl_win_sh x frb (frb + 96) FR8 ltac:(lia))|].
    split; [| exact I].
    apply (lay_sh_app_out _ (p + 18) (p + 50) Hsx). intros z Hz. replace z with (p + 18 + (z - (p + 18))) by lia.
    apply (acl_app_in m (p + 18) 32); [exact AR | lia].
  Qed.

  (* ---- the copy's post: lay_F_R2_disp_post (ctrl_lay_block_F_R2.v:204-215) with FI_on, plus the transport from the
     pre memory mc0 ---- *)
  Definition lay_F_R2_disp_post_on (mc0 : word -> option byte) (frb sfr spc j : Z) (w120 : word)
      : machine_state -> Prop :=
    fun ms' => exists (mc : word -> option byte) (gj : list byte)
                      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      ms' = MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
                    x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f)
                    (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md) (Z_to_bv 64 p)
                    (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
                    x28 x29 x30 x31)
               F (Z_to_bv 64 0x85718) fc None mc (seg_rom rsegs) /\
      FI_on mc frb sfr spc j w120 /\ LCx mc gj ly_zero /\ addressable mc (frb + 32) 32 /\
      munch [(S - K, S); (frb, frb + 24); (frb / 8 + ASAN_K, frb / 8 + ASAN_K + 12); (p + 18, p + 50)] mc0 mc /\
      (forall P : Z -> Prop, shadow_rw_on P mc0 -> shadow_rw_on P mc).


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
  Lemma lay_F_R2_fwords_on : forall (RNG : ExecF.footprint) (frb sfr spc j n : Z) (w120 : word)
      (mc : word -> option byte)
      (xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    FKx frb sfr spc j w120 -> sfr <> 0 -> 0 <= n <= 1 -> (n = 0 \/ 0 <= j < fs_M 1) ->
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
    ExecF.evtF rsegs RNG (lay_F_R2_disp_post_on mc frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) s5 (Z_to_bv 64 md) (Z_to_bv 64 p)
                 s8 (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x8569c) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG frb sfr spc j n w120 mc xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      HK Hs Hn Hnj HB RBY RIMG RSTK RFRB RFSH RMSK RROW RROWS RMSKS.
    pose proof SP2_factsx as (SP2m & SP2lo & SP2hi).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts_on frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & Hspc & FW & FAP & FRlh & SHlo & SHhi).
    pose proof (fk_facts_sw_on frb sfr spc j w120 HK Hs) as SW12.
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
      pose proof (proj2 (SR0 (shadow_addr (frb + 8 * jj)) (lay_F_R2_frame_R frb sfr spc j w120 HK Hs jj ltac:(lia))
                         (rt_app_shadow (frb + 8 * jj) Hap))) as [bb Hbb].
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
    (* now at ASAN_MEMSET (0x524c4): the checked memset of the row [p+18, p+50), through the _F_on contract. *)
    pose proof (lay_Wf_sub_on frb sfr spc j n w120 HK Hn Hnj) as SUBf. unfold Wf, shadow_addr in SUBf.
    pose proof (munch_weaken _ _ _ _ SUBf MU) as MUe.
    pose proof (lay_acx _ _ MU SUBf) as AC1.
    pose proof (A.ShadowRwOnT.shadow_rw_on_mem_mono _ m _ SR0 WM RM) as SR1.
    pose proof (acl_rw _ m _ (p + 18) [CB 32 ob] BLK MU WM
                  ltac:(intros x Hx; cbn [cells_size csize Nat.add] in Hx; change (Z.of_nat 32) with 32 in Hx;
                        apply (lay_row_out_Wf_on frb sfr spc j n w120 x HK Hn Hnj); lia)) as RW1.
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
    pose proof MEMSF as HM. unfold asan_memset_contract_F_on, ASAN_MEMSET_K in HM. cbv zeta in HM.
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
      - exact (shadow_rw_on_mono _ _ _ lay_F_R2_memset_R SR1).
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
    (* the transport from the run's pre memory mc: the fwords stores keep wview and mrd (WMc, RMc at the call's
       memory), then the memset post's own transport conjunct (asan_memset_c_on.v:35). *)
    assert (SRT : forall P : Z -> Prop, shadow_rw_on P mc -> shadow_rw_on P mp)
      by (intros P HP; apply SRp; exact (A.ShadowRwOnT.shadow_rw_on_mem_mono P mc _ HP WMc RMc)).
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
    destruct (lay_fw_rt_on frb sfr spc j w120 mc mp HK FPc TLc AWc MUd (wmono_trans rsegs _ _ _ WMc WMp)
                (rd_mono_trans _ _ _ RMc RMp)) as (FPp & TLp & AWp).
    (* ME_on at 0x85718, exactly as fwords hands it to KB (less the shadow conjunct) *)
    assert (MEp : ME_on frb sfr w120 mp).
    { unfold ME_on.
      split; [ eapply munch_trans; [exact MUe | eapply munch_weaken; [exact SUBms | exact MUp]] | ].
      split; [ eapply wmono_trans; [exact WM | exact WMp] | ].
      split; [ eapply rd_mono_trans; [exact RM | exact RMp] | ].
      split; [ exact MIp | ].
      split; [ exact ACp | ].
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
      { intros Hs0. specialize (F120 Hs0).
        destruct HK as [(E0 & _) | (Hj & Efr & _ & Esp & _)]; [exfalso; exact (Hs0 E0)|].
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
    (* ly_kb (:2723-2755): ME_on and FK give the DISP_T bundle *)
    clear MUe MUp MUc SUBms.
    destruct MEp as (MUm & WMm & RMm & MIm & ACm & STKm & SVm & RWm & FBm & F120m & ADrm & ADfm & AMm
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
    assert (FIc : FI_on mp frb sfr spc j w120).
    { split; [exact HK|]. split; [exact F120m|]. split; [exact ACm|].
      split; [exact FPm|]. split; [exact TLm | exact AWom]. }
    apply ExecF.evtF_done. unfold lay_F_R2_disp_post_on.
    do 18 eexists.
    split; [reflexivity | ]. split; [exact FIc | ]. split; [exact LCc | split; [exact AMm | split; [exact MUd | exact SRT]]].
  Qed.


  (* ---- 0x8566c -> 0x85718: ly_pro_go's side-frame arm (:2967-2968) and the stretch above ---- *)
  Lemma lay_F_R2_on : forall (RNG : ExecF.footprint) (frb sfr spc j : Z) (w120 : word) (mc : word -> option byte)
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
    ExecF.evtF rsegs RNG (lay_F_R2_disp_post_on mc frb sfr spc j w120)
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
    destruct (fk_facts_on frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & Hspc & FW & FAP & FRlh & SHlo & SHhi).
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
    apply (lay_F_R2_fwords_on RNG frb frb SP2 j 1 w120 mc xra t0' t1' t2' (Z_to_bv 64 frb) a1' a2' a3' a4' a5' a6' a7'
             t3' t4' t5' t6');
      [ exact HK | exact Hs | lia | right; exact Hj | exact HB | exact RBY | exact RIMG | exact RSTK | exact RFRB
      | exact RFSH | exact RMSK | exact RROW | exact RROWS | exact RMSKS ].
  Qed.

  (* ---- stretch k = 3 (ctrl_lay_block_F_3.v:203-283), verbatim with FI -> FI_on: the stretch passes FI through
     untouched.  F_3.v:76's acc_hint override, Local, from here on (lay_F_R2_fwords_on above is proved without it). *)
  Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= ctrl_lay_block_F_3.lay3_accF.

  Definition lay_F_pre_box_on (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z) (w120 : word)
    : machine_state -> Prop :=
    fun ms' => exists (xra x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      ms' = MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
                    (Z_to_bv 64 md) (Z_to_bv 64 (ly_bb (ly_k fr))) (Z_to_bv 64 (frb + 32))
                    x13 x14 x15 x16 x17
                    (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md)
                    (Z_to_bv 64 (frb + 32)) (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb)
                    (Z_to_bv 64 ASAN_K) s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x85824) fc None mc (seg_rom rsegs) /\
      FI_on mc frb sfr spc j w120 /\ LCx mc gj ly_zero /\ addressable mc (frb + 32) 32 /\
      3 <= ly_k fr <= 9.

  Lemma lay_F_boxarm_on : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte)
      (b frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    b = ly_bb (ly_k fr) -> 3 <= ly_k fr <= 9 ->
    FI_on mc frb sfr spc j w120 -> LCx mc gj ly_zero -> addressable mc (frb + 32) 32 ->
    evtF rsegs RNG (lay_F_pre_box_on mc gj frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md)
               (Z_to_bv 64 p) (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85818) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj b frb sfr spc j w120 xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      -> KB9 FIH LCH AO.
    step. step. step.
    apply evtF_done. hnf.
    do 13 eexists.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FIH|]. split; [exact LCH|]. split; [exact AO | exact KB9].
  Qed.

  Lemma ctrl_lay_block_F_3_on : forall (RNG : footprint) (mc : word -> option byte) (gj : list byte)
      (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rng RNG (S - K) K -> rng RNG f 24 -> rng RNG (shadow_addr f) 3 -> rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    3 <= ly_k fr <= 9 ->
    FI_on mc frb sfr spc j w120 -> LCx mc gj ly_zero -> addressable mc (frb + 32) 32 ->
    evtF rsegs RNG (lay_F_pre_box_on mc gj frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md)
               (Z_to_bv 64 p) (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85718) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      RSTK RFB RFSH RIMG KB FIH LCH AFR.
    unfold IMG_LO, IMG_HI in RIMG. unfold shadow_addr in RFSH.
    pose proof (LC_addr_fl mc gj ly_zero LCH) as AFc.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FBc).
    pose proof (rd_byte rsegs mc f fr 2 FBc ltac:(lia)) as R2.
    step.
    pose proof (acl_shadow mc f 24 2 1 (f + 2) AFc ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite Z.add_mod by lia; rewrite F8; cbn; lia) eq_refl) as SH2.
    assert (RX2 : 0 <= f + 2 < 2^64) by lia.
    ctrl_lay_block_F_3.chk_coreF (f + 2) RX2 (Z_to_bv 5 12) SH2 ctrl_lay_block_F_3.pre_srF
      ctrl_lay_block_F_3.no_extraF.
    step. clear R2. step. step. rewrite (rc_u8_gtu fr 2 9) by lia.
    replace (9 <? rc_u8 fr 2) with false by (symmetry; apply Z.ltb_ge; unfold ly_k in K9; lia). cbv iota.
    assert (KC : ly_k fr = 3 \/ ly_k fr = 4 \/ ly_k fr = 5 \/ ly_k fr = 6 \/ ly_k fr = 7 \/ ly_k fr = 8 \/
                 ly_k fr = 9) by lia.
    destruct KC as [KE|[KE|[KE|[KE|[KE|[KE|KE]]]]]]; rewrite (rc_zxb_lit fr 2 _ KE); do 8 step;
      repeat lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x85818) _ _ _ _) => fail | _ => step end;
      (eapply lay_F_boxarm_on; [unfold ly_bb; rewrite KE; reflexivity | exact KB | exact FIH | exact LCH
                               | exact AFR]).
  Qed.

  (* ---- the region's whole run (0x8566c -> the callee's entry 0x85b44, ra = 0x85828): lay_F_R2_on, then stretch
     k = 3 (ctrl_lay_block_F_3_on), then ctrl_lay_block_F_R2.lay_F_R2_jal.  k = 3 and the jal keep the memory, so
     the write set and the transport are lay_F_R2_on's. ---- *)
  Definition lay_F_R2_box_pre_on (mc0 : word -> option byte) (frb sfr spc j : Z) (w120 : word)
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
      FI_on mc frb sfr spc j w120 /\ LCx mc gj ly_zero /\ addressable mc (frb + 32) 32 /\
      munch [(S - K, S); (frb, frb + 24); (frb / 8 + ASAN_K, frb / 8 + ASAN_K + 12); (p + 18, p + 50)] mc0 mc /\
      (forall P : Z -> Prop, shadow_rw_on P mc0 -> shadow_rw_on P mc).

  Lemma lay_F_R2_run_on : forall (RNG : ExecF.footprint) (frb sfr spc j : Z) (w120 : word)
      (mc : word -> option byte)
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
    ExecF.evtF rsegs RNG (lay_F_R2_box_pre_on mc frb sfr spc j w120)
      (MS (mkR xra (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
                 (Z_to_bv 64 frb) a1' a2' a3' a4' a5' a6' a7'
                 s2 (Z_to_bv 64 g) (Z_to_bv 64 f) s5 (Z_to_bv 64 md) (Z_to_bv 64 p)
                 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x8566c) fc None mc (seg_rom rsegs)).
  Proof.
    intros RNG frb sfr spc j w120 mc xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      HK Hs Hj HB RBY RIMG RSTK RFRB RFSH RMSK RROW RROWS RMSKS RF RSHF KB.
    eapply ExecF.evtF_cut.
    { exact (lay_F_R2_on RNG frb sfr spc j w120 mc xra t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
               HK Hs Hj HB RBY RIMG RSTK RFRB RFSH RMSK RROW RROWS RMSKS). }
    intros ms1 (mc1 & gj & y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31
                & -> & FI1 & LC1 & AO1 & MU1 & SRT1).
    eapply ExecF.evtF_cut.
    { exact (ctrl_lay_block_F_3_on RNG mc1 gj frb sfr spc j w120 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17
               y28 y29 y30 y31 RSTK RF RSHF RIMG KB FI1 LC1 AO1). }
    intros ms2 (z1 & z5 & z6 & z7 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & -> & FI2 & LC2 & AO2 & _).
    eapply ExecF.evtF_cut; [apply ctrl_lay_block_F_R2.lay_F_R2_jal |].
    intros ms3 ->. apply ExecF.evtF_done. unfold lay_F_R2_box_pre_on.
    exists mc1, gj, z5, z6, z7, z13, z14, z15, z16, z17, z28, z29, z30, z31.
    split; [reflexivity|]. split; [exact FI2|]. split; [exact LC2|].
    split; [exact AO2 | split; [exact MU1 | exact SRT1]].
  Qed.

End F2R_on.

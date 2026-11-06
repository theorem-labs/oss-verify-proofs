(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 409 of its 423 lines of code are new or changed and 234 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_model_block_epi.v; 182 of its 261 lines of code are new or changed and 344 lines of the source are left out. *)
(* Footprint (_F) re-run of reac_box_model_block.v at a working branch d69f7c708f6 (proved v1.9 run of
   record) over lib/Lib/StepF, in three stretches cut at its two allocator events (main_pre_F, main_mid_F, main_post_F, below); reac_box_model_block_holds_of_F has a new proof.
   Image: fuzz_ctrl.asan (libreac v1.9.0), ELF sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd. FACTS ed6b6b7b0ab.
   Const cells checked against the v1.9.0 image bytes (file offsets from the LOAD headers of fuzz_ctrl.debug:
   vaddr 0x10000 at offset 0x0, vaddr 0x9e348 at offset 0x8c348, vaddr 0xa17c8 at offset 0x8e7c8):
     GOT_CELL_K 0x9fad0 (offset 0x8dad0): 78 88 0a 00 00 00 00 00  = 0xa8878 = CELL_K
     GOT_UAR    0x9fb28 (offset 0x8db28): 80 88 0a 00 00 00 00 00  = 0xa8880 = UAR
     jump table 0x219f4 (offset 0x119f4): 94 42 06 00 | f8 44 06 00 | b8 44 06 00 | c4 44 06 00 | 2c 44 06 00 |
       10 45 06 00 | a4 45 06 00, i.e. the seven offsets 0x64294 0x644f8 0x644b8 0x644c4 0x6442c 0x64510 0x645a4,
       which added to the table address 0x219f4 give the case entries 0x85c88 0x85eec 0x85eac 0x85eb8 0x85e20
       0x85f04 0x85f98 (cs0 .. cs6).
   CELL_K 0xa8878 and UAR 0xa8880 lie past the file image of their LOAD segment (vaddr 0xa17c8, filesz 0x39f8):
   they are .bss runtime cells with no image bytes, and the run reads them through asan_cells, not as image
   constants.

   Route (a) conditions (lead 22:15-22:18Z, a Theorem Labs lane 22:20Z), obeyed here except condition 1:
   1. Each _F is a MECHANICAL re-derivation of an already-PROVED v1.9 run: the same proof script over StepF, and no
      new proof obligation.
   2. The _F output feeds ONLY the ported cgif-form walk.  No W_cutfree_ok, no cut-free twin, no LSCPS join, no
      top-level claim.
   3. The source runs are on ctrl's v1.9 record (FACTS ed6b6b7b0ab), with no stale AsanRT / off_img literal /
      wrong-image cell.  The re-run's const cells are checked against fuzz_ctrl's v1.9.0 image bytes.
   4. Every _F carries provenance in its header (image root, ELF sha256, tool version, which compare) and goes to
      the auditor a Theorem Labs lane, who signs it against its proved run before it counts.
   5. A StepF "uncovered access" error means STOP: report it.  Do not widen the footprint to make it pass.

   This is the file the cgif glue consumes.  The function run contains two allocator EVENTS, so it is NOT lifted
   whole (segF-rerun-recipe.md, "Function runs that contain a fake-stack call"): the call
   `jal __asan_stack_malloc_0` at 0x85bb8 and the fake-frame flag release `sb zero,0(a0)` at 0x864f8.  The three
   silent stretches between them are:
     main_pre_F   S1  [0x85b44 .. 0x85bb8)   = reac_box_model_block_baseF.entry_pre_F
     main_mid_F   S2  [0x85bbc .. 0x864f8)   = entry_post_F + body_F, under the epi obligation HKR (bmb_KR Q)
     main_post_F  S3  [0x864fc .. ret]       = reac_box_model_block_epiF.epi_post_F
   The glue supplies the call through cgif's astack_malloc_realizes (fake-frame arm) and the release through
   astack_free_law / frame_flag_lawP.

   reac_box_model_block.v and its theorem reac_box_model_block_holds, as the run of record named on :1 has them, are not in this delivery, and this file edits neither.  The whole-function footprint
   contract reac_box_model_block_contract_F (reac_box_model_block_cF.v) is NOT proved here and must not be: its run
   crosses the two events, so no mechanical re-derivation of the proved v1.9 script can close it (rule 24: no
   function is proved in this file).  reac_box_model_block_holds_of_F is the recipe's step-4 corollary in its
   place: it re-derives the OLD statement reac_box_model_block_contract - the conclusion of
   reac_box_model_block_holds - from the footprint one at ExecF.RNG_all, which is the check that the _F statement
   is the old statement plus footprint premises and nothing weaker. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c
  reac_box_model_block_base reac_box_model_block_epi reac_box_model_block_binv reac_box_model_block_binv2 reac_box_model_block_cases reac_box_model_block_cases0a reac_box_model_block_cases0b reac_box_model_block_cases0c reac_box_model_block_cases0 reac_box_model_block_cases2 reac_box_model_block_body reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF asan_memcpy_cF
  reac_box_model_block_cF reac_box_model_block_baseF reac_box_model_block_epiF
  reac_box_model_block_binvF
  reac_box_model_block_binv2F reac_box_model_block_casesF reac_box_model_block_cases0aF
  reac_box_model_block_cases0bF reac_box_model_block_cases0cF reac_box_model_block_cases0F
  reac_box_model_block_cases2aF reac_box_model_block_cases2bF reac_box_model_block_bodyF.
(* Route (C): the narrowed shadow premise, the region it names, and the callees' `_on` contracts (a Theorem Labs lane's
   text, carried by a Theorem Labs lane from a working branch f4423e55886 and a working branch). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import rng_asan sh_word_on asan_memset_c_on
  asan_memset_cF_on asan_memcpy_c_on asan_memcpy_cF_on reac_box_model_block_c_on.
(* Last: StepF's step / store_done / if_false (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module B := reac_box_model_block_base.
Module BEPI := reac_box_model_block_epi.
Module BINV := reac_box_model_block_binv.
Module BBODY := reac_box_model_block_body.
Module SRON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module C_ON := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c_on.

Module BaseF := reac_box_model_block_baseF.
Module EpiF := reac_box_model_block_epiF.
Module BodyF := reac_box_model_block_bodyF.
Module BinvF := reac_box_model_block_binvF.

From Ltac2 Require Import Ltac2.

(* The section-closing generalization abstracts each lemma of Section Main over the section variables and hypotheses
   it uses, in declaration order, under their own names. inst c applies c to the hypotheses of the current context
   that carry the names of c's leading binders, and stops at the first binder whose name is not a hypothesis. *)
Ltac2 rec inst_go (c : constr) (t : constr) (acc : constr list) :=
  let fin () := match acc with
                | [] => c
                | _ => Constr.Unsafe.make (Constr.Unsafe.App c (Array.of_list (List.rev acc)))
                end in
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod bnd body =>
      match Constr.Binder.name bnd with
      | Some id =>
          match Control.case (fun () => Control.hyp id) with
          | Val hv => let (h, _) := hv in inst_go c (Constr.Unsafe.substnl [h] 0 body) (h :: acc)
          | Err _ => fin ()
          end
      | None => fin ()
      end
  | _ => fin ()
  end.

Ltac2 inst (c : constr) := inst_go c (Constr.type c) [].

Ltac2 Notation "inst_exact" c(constr) := let r := inst c in exact $r.

Set Default Proof Mode "Classic".

Section MainF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  (* The callee contracts in footprint form (a Theorem Labs lane's shared text).  No lemma of this file takes the stack
     malloc contract: S1 ends before the 0x85bb8 call and S2 starts after it has returned. *)
  Hypothesis HMSF : asan_memset_cF_on.asan_memset_contract_F_on.
  Hypothesis HMCF : asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis HBDF : build_dt1_single_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  (* Route (C) narrowing (a Theorem Labs lane batch 75): not the universal A.AsanRT.shadow_rw, which is false at the allocator
     state, but the shadow region this function and its callees read or write (a Theorem Labs lane's audited region,
     reac_box_model_block_c_on.v:38). *)
  Hypothesis SR0 : SRON.shadow_rw_on (C_ON.reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rb : 0 <= b < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
  Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ bytes_at rsegs m (rname row) nb /\
    (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
    (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o).
  Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
  Hypothesis AP : p <> 0 -> addressable m p 296.
  Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    addressable m (rname row) (Z.of_nat (length nb)).
  Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).

  (* The footprint and the regions the runs of this function read or write (reac_box_model_block_cF.v). *)
  Variable RNG : footprint.
  Hypothesis Rimg : rng RNG 0x10000 0x5ee000.
  Hypothesis Rrt : rng RNG RT_LO (RT_HI - RT_LO).
  Hypothesis Rwin : rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis Rwsh : sh_cover RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis Rtp88 : rng RNG (bv_unsigned tp - 88) 8.
  Hypothesis Rtp8 : rng RNG (bv_unsigned tp - 8) 24.
  Hypothesis Rtls : reac_box_model_block_tls_rng RNG m (bv_unsigned tp).
  Hypothesis RFSh : rng RNG FS (fs_frame FS 0%nat 0 - FS).
  Hypothesis RFSw : rng_ivls RNG (tl (fp_w [0%nat] FS)).
  Hypothesis RFSsh : rng RNG (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8).
  Hypothesis Rby : rng_bytes RNG.
  Hypothesis Rwsw : rng_asan.sh_word_rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K.
  Hypothesis RP : p <> 0 -> rng RNG p 296.
  Hypothesis RPs : p <> 0 -> sh_cover RNG p 296.
  Hypothesis RO : o <> 0 -> rng RNG o 32.
  Hypothesis ROs : o <> 0 -> sh_cover RNG o 32.
  Hypothesis RN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    rng RNG (rname row) (Z.of_nat (length nb)).
  Hypothesis RNs : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    sh_cover RNG (rname row) (Z.of_nat (length nb)).
  Hypothesis RJ13s : b = 2 -> sh_cover RNG JOIN_0013 32.
  Hypothesis RJ14s : b = 1 -> sh_cover RNG JOIN_0014 32.

  (* The post of the S2 stretch and the epi obligation it stops at. *)
  Let bmb_KR := ltac2:(inst_exact @EpiF.bmb_KR).
  Variable Q : Z -> Z -> Z -> Z -> Z -> word -> machine_state -> Prop.
  Hypothesis HKR : bmb_KR Q.

  (* The definitions of the proved files at this section's variables. *)
  Notation FK := (B.FK FS A).
  Notation Wf := (B.Wf sp FS).
  Notation EBW := (B.EBW sp p o FS).
  Notation SAVES := (B.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation BI := (B.BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m FS).
  Notation EB := (B.EB ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m p b o FS row nb).
  (* Route (C): the ret post is a Theorem Labs lane's _on form (reac_box_model_block_c_on.v:47), whose shadow conjunct is
     the region transport `forall P, shadow_rw_on P m -> shadow_rw_on P m'` (a Theorem Labs lane, epiF's Q0). *)
  Notation Q0 := (C_ON.reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb).
  Let RB := ltac2:(inst_exact @BinvF.RB_F).

  (* The cut points of the two allocator events, and the three stretches between them. *)
  Let bmb_at_call := ltac2:(inst_exact @BaseF.bmb_at_call).
  Let bmb_after_rel := ltac2:(inst_exact @EpiF.bmb_after_rel).
  Let bmb_at_call_refl := ltac2:(inst_exact @BaseF.bmb_at_call_refl).
  Let bmb_at_ret_of := ltac2:(inst_exact @BaseF.bmb_at_ret_of).
  Let entry_pre_F := ltac2:(inst_exact @BaseF.entry_pre_F).
  Let entry_post_F := ltac2:(inst_exact @BaseF.entry_post_F).
  Let epi_post_F := ltac2:(inst_exact @EpiF.epi_post_F).
  Let body_F := ltac2:(inst_exact @BodyF.body_F).

  (* S1: [0x85b44 .. 0x85bb8), the prologue, the GOT / UAR reads, the A computation and the argument set-up, up to
     the state of the jal __asan_stack_malloc_0.  The event itself is cgif's astack_malloc_realizes. *)
  Lemma main_pre_F : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (K : machine_state -> Prop)
      (m0 : word -> option byte), m0 = m ->
    (forall (a1' a2' : word) (m1 : word -> option byte), bmb_at_call m1 ->
       evtF rsegs RNG K (MS (mkR ra (Z_to_bv 64 A) gp tp t0 t1 t2 sp (Z_to_bv 64 A)
                          (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                          (Z_to_bv 64 b) s7 s8 (wa off) s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x85bb8) fc None m1 (seg_rom rsegs))) ->
    evtF rsegs RNG K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m0 (seg_rom rsegs)).
  Proof. exact entry_pre_F. Qed.

  (* S2: [0x85bbc .. 0x864f8), from the fake-frame return state of __asan_stack_malloc_0 to the epi obligation
     HKR : bmb_KR Q, which the glue instantiates with the continuation at the flag release (epi_pre_F).  It is the
     frame words and the frame shadow (entry_post_F, fwords_F) followed by the whole body (body_F). *)
  Lemma main_mid_F : forall jj (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    0 <= jj < fs_M 0%nat ->
    bytes_at rsegs m (fs_flag FS 0 jj) [Z_to_bv 8 1] ->
    bytes_at rsegs m (fs_frame FS 0 jj + 56) (le8 (Z_to_bv 64 (fs_flag FS 0 jj))) ->
    bytes_at rsegs m (shadow_addr (fs_frame FS 0 jj)) (repeat (Z_to_bv 8 0) 8) ->
    addressable m (fs_frame FS 0 jj) 64 ->
    stk rsegs m (fs_frame FS 0 jj) (fs_frame FS 0 jj + 64) ->
    rw_cells rsegs m (bv_unsigned sp + -104) SAVES ->
    evtF rsegs RNG (Q (fs_frame FS 0 jj) (fs_frame FS 0 jj) A jj 1 (Z_to_bv 64 (fs_flag FS 0 jj)))
      (MS (mkR x1' (Z_to_bv 64 A) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
               (Z_to_bv 64 (fs_frame FS 0 jj)) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5
               (Z_to_bv 64 b) s7 s8 (wa off) s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x85bbc) fc None m
          (seg_rom rsegs)).
  Proof.
    intros jj x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hjj Hflag Hw56 Hsh Hadd Hstk Hsaves.
    exact (entry_post_F jj m m x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Q
             (bmb_at_call_refl Hsaves) (bmb_at_ret_of jj Hjj Hflag Hw56 Hsh Hadd Hstk) body_F).
  Qed.

  (* S3: [0x864fc .. ret 0x86560], from the state after the flag release (cgif's astack_free_law gives
     bmb_after_rel) to the function's post Q0: the post-release steps, epi_close_F and td_tail_F.  S3 stores
     nothing, so the post also hands the final memory back as mfin, which the glue needs for the caller's
     journal. *)
  Lemma main_post_F : forall (r : Z) (mc mfin : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word)
      (spc fr f j n : Z) (w56 : word),
    FK fr f spc j n w56 -> EB fr f j n w56 mc -> n = 1 ->
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    bmb_after_rel fr j mc mfin ->
    evtF rsegs RNG (fun s => Q0 s /\ ms_mem s = mfin)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x864fc) fc None mfin (seg_rom rsegs)).
  Proof. exact epi_post_F. Qed.

End MainF.

(* RECIPE step 4: the old statement from the footprint one at RNG_all, every rng premise by rng_all.  This is the
   check that reac_box_model_block_contract_F is reac_box_model_block_contract - the conclusion of
   reac_box_model_block_holds - plus footprint premises, and nothing weaker.  The bounds of the thread cells and of
   the side stack come from the bytes_at facts of asan_tls_cells and from fs_place, as bytes_at_bound reads them. *)
Theorem reac_box_model_block_holds_of_F :
  reac_box_model_block_contract_F -> reac_box_model_block_contract.
Proof.
  unfold reac_box_model_block_contract_F, reac_box_model_block_contract, REAC_BOX_MODEL_BLOCK_K. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p b o FS row nb ob Ea0 Ea1 Ea2 Rp Rb Ro HS16 ST0 HP HN HO MI0 AC0 SR0 HHM HAE AW0 AP ANB AO AJ1 AJ2 FP0 NDJ
    TLS0.
  (* the side stack and the thread cells of m, with their bounds *)
  pose proof FP0 as FPc.
  destruct FPc as (DT & TS & C & T & DB & kk & HTLS & HTP & HPl & _ & _ & _ & HFSb & _).
  pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSb, P4, P5.
  assert (FSlo : 0 < FS) by exact P1.
  assert (FShi : FS + 11571200 <= 2 ^ 64).
  { pose proof (P4 (FS + 11571200 - 1) ltac:(lia)) as A1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1. lia. }
  pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  assert (EFR0 : fs_frame FS 0%nat 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (ESH0 : fs_M 0%nat * fs_B 0%nat / 8 = 131072) by reflexivity.
  (* the thread-pointer words, from the bytes asan_tls_cells pins *)
  pose proof HTLS as (_ & _ & HDTb & HDT8 & _ & _ & _ & HTS88 & HTSk & HC152 & (tb & te & HT48) & _ & _ & _ & _ &
                      _ & HDB8 & _ & HDB24).
  pose proof (bytes_at_bound _ _ _ _ HDTb) as BDT. rewrite length_le8 in BDT. cbn [Z.of_nat] in BDT.
  pose proof (bytes_at_bound _ _ _ _ HDB8) as BDB. rewrite length_le8 in BDB. cbn [Z.of_nat] in BDB.
  pose proof (bytes_at_bound _ _ _ _ HTS88) as BTS88. rewrite length_le8 in BTS88. cbn [Z.of_nat] in BTS88.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply HF with (ob := ob); try assumption.
  - (* the image *) apply ExecF.rng_all; lia.
  - (* the memory-checking runtime words *) apply ExecF.rng_all; unfold RT_LO, RT_HI; lia.
  - (* the window *) apply ExecF.rng_all; lia.
  - (* the window's shadow cover *)
    unfold sh_cover. apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* tp - 88 *) apply ExecF.rng_all; lia.
  - (* tp - 8 *) apply ExecF.rng_all; lia.
  - (* the thread cells *)
    unfold reac_box_model_block_tls_rng. intros DT' TS' C' T' DB' k' HC'.
    pose proof HC' as (_ & _ & _ & HDT8' & _ & _ & _ & _ & HTSk' & HC152' & (tb' & te' & HT48') & _ & _ & _ & _ &
                       _ & _ & _ & HDB24').
    pose proof (bytes_at_bound _ _ _ _ HDT8') as B1. rewrite length_le8 in B1. cbn [Z.of_nat] in B1.
    pose proof (bytes_at_bound _ _ _ _ HTSk') as B2. rewrite length_le8 in B2. cbn [Z.of_nat] in B2.
    pose proof (bytes_at_bound _ _ _ _ HC152') as B3. rewrite length_le8 in B3. cbn [Z.of_nat] in B3.
    pose proof (bytes_at_bound _ _ _ _ HT48') as B4. rewrite length_app, !length_le8 in B4. cbn [Z.of_nat] in B4.
    pose proof (bytes_at_bound _ _ _ _ HDB24') as B5. rewrite length_le8 in B5. cbn [Z.of_nat] in B5.
    split; [apply ExecF.rng_all; lia|]. split; [apply ExecF.rng_all; lia|].
    split; [apply ExecF.rng_all; lia|]. split; [apply ExecF.rng_all; lia|].
    apply ExecF.rng_all; lia.
  - (* the side-stack header *) rewrite EFR0. apply ExecF.rng_all; lia.
  - (* the class-0 area: rng_ivls carries no bound, and RNG_all admits every access *)
    unfold rng_ivls. repeat constructor; intros; exact I.
  - (* the shadow of the class-0 frames *)
    rewrite EFR0, ESH0. apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* RNG_all is byte-wise *) unfold rng_bytes; intros; exact I.
  - (* the window's aligned shadow words *)
    unfold rng_asan.sh_word_rng. right.
    apply ExecF.rng_all; unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr, ASAN_K;
      Z.div_mod_to_equations; lia.
  - (* the row *)
    intros Hp0. destruct (HP Hp0) as (_ & Lrow & HRB & _).
    pose proof (bytes_at_bound _ _ _ _ HRB) as BR. rewrite Lrow in BR. cbn [Z.of_nat] in BR.
    apply ExecF.rng_all; lia.
  - (* the row's shadow cover *)
    intros Hp0. destruct (HP Hp0) as (_ & Lrow & HRB & _).
    pose proof (bytes_at_bound _ _ _ _ HRB) as BR. rewrite Lrow in BR. cbn [Z.of_nat] in BR.
    unfold sh_cover. apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* the box cell *)
    intros Ho0. destruct (AO Ho0) as (_ & HAPo & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HAPo.
    apply ExecF.rng_all; lia.
  - (* the box cell's shadow cover *)
    intros Ho0. destruct (AO Ho0) as (_ & HAPo & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HAPo.
    unfold sh_cover. apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* the name bytes *)
    intros Hp0 Hb56 Hhas Hrn. destruct (HN Hp0 Hb56 Hhas Hrn) as (_ & HNB & _).
    pose proof (bytes_at_bound _ _ _ _ HNB) as BN.
    apply ExecF.rng_all; lia.
  - (* the name bytes' shadow cover *)
    intros Hp0 Hb56 Hhas Hrn. destruct (HN Hp0 Hb56 Hhas Hrn) as (_ & HNB & _).
    pose proof (bytes_at_bound _ _ _ _ HNB) as BN.
    unfold sh_cover. apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* JOIN_0013's shadow cover *)
    intros _. unfold sh_cover, JOIN_0013.
    apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* JOIN_0014's shadow cover *)
    intros _. unfold sh_cover, JOIN_0014.
    apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

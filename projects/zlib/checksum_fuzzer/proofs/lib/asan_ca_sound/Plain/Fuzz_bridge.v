(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Exec.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.CkP Require Import RegsFull BridgeKit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Plain Require Import PImg StdioFiles.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Spec Require Import Prelim Malloc Monad Stdio Harness Prog.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Plain Require Import RunDraw.
Require OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.S0FuzzStmt OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.S0Fuzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Module FS := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.S0FuzzStmt.
Module FZ := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.S0Fuzz.

Section CANSEC1. Context {rc : runConstT}.
Theorem fuzz_one_bridge : fuzz_one_stmt.
Proof.
  unfold fuzz_one_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB D payload AB lo errv
         HEAP BY FP RC D16 D0 DT PL HC SE AUX SPAB ST CEIL LO ERR MI FRM TP SP16 A0 A1 RAE.
  unfold Prog.fuzz_one, Harness.fuzz_one. apply implM_ret.
  pose proof (getr_mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as GR.
  set (R0 := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) in *.
  destruct GR as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20
                  & G21 & G22 & G23 & G24 & G25 & G26 & G27 & G28 & G29 & G30 & G31).
  pose proof ST as (LO0 & SPHI & STK).
  atop_facts. unfold HARNESS_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  assert (PL0 : 0 <= zlength payload) by (unfold zlength; lia).
  assert (UD : bv_unsigned (wz D) = D) by (unfold wz; apply unsigned_lit; lia).
  destruct (@FZ.s0_fuzz (OP.mkFP F fc) R0 m (seg_rom psegs) ra sp (wz D) (zlength payload)) as (R' & m' & RUN & KCS & R10 & FM).
  - exact G1.
  - apply OH.ret_ok_even. exact RAE.
  - exact G2.
  - rewrite G10. exact A0.
  - rewrite G11. exact A1.
  - exact PL0.
  - rewrite UD. lia.
  - rewrite UD. lia.
  - lia.
  - intros _ i Hi. rewrite UD. rewrite rdn_conv.
    pose proof (bytes_at_rdn psegs m D (map (Z_to_bv 8) payload) (Z.to_nat i) 1 BY) as RD.
    rewrite Z2Nat.id in RD by lia. unfold wa in RD. change M.loaded_segments with psegs. rewrite RD by (rewrite length_map; unfold zlength in Hi; lia).
    destruct (skipn (Z.to_nat i) (map (Z_to_bv 8) payload)) as [|b rest] eqn:E.
    + exfalso. apply (f_equal (@length _)) in E. rewrite length_skipn, length_map in E. unfold zlength in Hi. cbn in E. lia.
    + exists b. reflexivity.
  - change M.loaded_segments with psegs.
    assert (WR : wr_at psegs m (bv_unsigned sp - 192) 192).
    { split; [lia|]. split; [lia|]. intros i Hi. apply (STK (bv_unsigned sp - 192 + i)). lia. }
    pose proof (wr_at_store_ok psegs m (bv_unsigned sp - 192) 192 0 192%nat WR ltac:(lia) ltac:(lia)) as SO.
    rewrite Z.add_0_r in SO. exact SO.
  - intros _. rewrite UD. lia.
  - intros j Hj. destruct (m (Z_to_bv 64 (66900 + j))) as [b|] eqn:E; [|reflexivity]. exfalso.
    pose proof (MI _ _ E) as RO. rewrite p_ro_addr in RO. rewrite unsigned_lit in RO by lia.
    revert RO. clear -Hj. intros RO. apply andb_false_iff in RO. destruct RO as [RO|RO]; [apply Z.leb_gt in RO| apply Z.ltb_ge in RO]; lia.
  - assert (EPC : wz PFUZZ_ENTRY = ((0x141f0)%bv : word)) by (apply bv_eq; reflexivity).
    rewrite EPC.
    apply (evt_of_msteps_mkR psegs _ R0 F _ ra fc m m' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ER'.
    pose proof (getr_mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as GR'.
    rewrite <- ER' in GR'.
    destruct GR' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20
                     & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31).
    assert (CS : forall r, In r OR.callee_saved -> OP.getr R' r = OP.getr R0 r) by exact KCS.
    assert (E1 : x1 = ra) by (rewrite <- H1, <- G1; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E2 : x2 = sp) by (rewrite <- H2, <- G2; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E3 : x3 = gp) by (rewrite <- H3, <- G3; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E4 : x4 = tp) by (rewrite <- H4, <- G4; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E8 : x8 = s0) by (rewrite <- H8, <- G8; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E9 : x9 = s1) by (rewrite <- H9, <- G9; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E18 : x18 = s2) by (rewrite <- H18, <- G18; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E19 : x19 = s3) by (rewrite <- H19, <- G19; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E20 : x20 = s4) by (rewrite <- H20, <- G20; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E21 : x21 = s5) by (rewrite <- H21, <- G21; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E22 : x22 = s6) by (rewrite <- H22, <- G22; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E23 : x23 = s7) by (rewrite <- H23, <- G23; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E24 : x24 = s8) by (rewrite <- H24, <- G24; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E25 : x25 = s9) by (rewrite <- H25, <- G25; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E26 : x26 = s10) by (rewrite <- H26, <- G26; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E27 : x27 = s11) by (rewrite <- H27, <- G27; apply CS; unfold OR.callee_saved; cbn; tauto).
    assert (E10 : x10 = Z_to_bv 64 0) by (rewrite <- H10; exact R10).
    clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 CS.
    subst x1 x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x10.
    pose proof (frame_mod_munch m m' (bv_unsigned sp - 192) 192 ltac:(lia) ltac:(lia) FM) as MU.
    replace (bv_unsigned sp - 192 + 192) with (bv_unsigned sp) in MU by lia.
    pose proof (mem_grows_wmono psegs m m' (proj2 FM)) as WM.
    assert (WIN : forall x : Z, bv_unsigned sp - 192 <= x < bv_unsigned sp -> exists b, m' (wa x) = Some b).
    { intros x Hx. destruct (STK x ltac:(lia)) as [_ [b Hb]].
      rewrite ref_mrd_overlay in Hb by (unfold wa; rewrite unsigned_lit by lia; lia).
      pose proof (proj2 FM (wa x) ltac:(rewrite Hb; discriminate)) as G. destruct (m' (wa x)) as [b'|]; [exists b'; reflexivity| contradiction]. }
    assert (ST' : stk psegs m' lo (bv_unsigned sp)).
    { eapply stk_transport; [exact ST| exact MU| exact WM|]. intros x Hx. cbn [outside].
      destruct (Z_lt_dec x (bv_unsigned sp - 192)) as [L|L]; [left; split; [lia| exact I]| right; apply WIN; lia]. }
    assert (MI' : mem_inv psegs m').
    { eapply mem_inv_window; [exact MI| exact MU|]. intros x Hx.
      assert (IN : bv_unsigned sp - 192 <= bv_unsigned x < bv_unsigned sp).
      { cbn [outside] in Hx. lia. }
      pose proof (proj1 (STK (bv_unsigned x) ltac:(lia))) as W2. unfold wa in W2. rewrite Z_to_bv_bv_unsigned in W2. exact W2. }
    unfold fuzz_one_post.
    exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F, fc, m', errv.
    rewrite (ret_pc_of_even ra RAE).
    split; [reflexivity|]. split; [lia|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split.
    { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. split; [| exact I].
      subst tp. unfold wz, RATP. rewrite unsigned_lit by lia. left. lia. }
    split.
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn [fst snd]. unfold RAUXV_CELL. split; [exact SPAB| right; lia]. }
    split.
    { intros a Ha Hc.
      assert (OUT : outside [(bv_unsigned sp - 192, bv_unsigned sp)] a).
      { cbn [outside]. split; [| exact I]. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|].
        pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HEAP Hb) as (_ & _ & _ & B4 & _). lia. }
      split; [apply MU; rewrite wa_unsigned by exact Ha; exact OUT| apply WM]. }
    split.
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HEAP| exact MU| exact WM|]. constructor; [| constructor]. left. cbn [fst]. lia. }
    reflexivity.
Qed.
End CANSEC1.

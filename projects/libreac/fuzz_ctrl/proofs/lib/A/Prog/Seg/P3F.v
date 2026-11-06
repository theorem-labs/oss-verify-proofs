(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its addresses changed; 1324 of its 1487 lines of code are new or changed and 1039 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P3.v; 462 of its 820 lines of code are new or changed and 1129 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/P3.v blob d3039cfecf9b at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives P3.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of P3.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint twins of Seg/P3.v's two run lemmas (p3_evt :153 (at head lib/A/Prog/Seg/P3.v:166), p3_evt_ro :463 (at head lib/A/Prog/Seg/P3.v:678), the lines of
   S_P3 (segment-runs-A.tsv (a working note, not in this delivery)); P3.p3_run :346 (at head lib/A/Prog/Seg/P3.v:537) concludes SR, not evt,
   so it is out of the spec's scope and stays plain).
   The segment (0x81b14 -> 0x81b7c) has two kinds of data access of its own: the 19 one-byte frame-shadow stores
   into [S + 336, S + 365), which the lemma's own 29-cell `rw_cells rsegs m (S + 336) [C1 b0; ...]` premise names,
   and the spill load [A + 32, A + 40) (`ld a0,32(s1)`), which its `rw_cells rsegs m (A + 32) [C8 ...]` premise
   names: two rng premises.
   Its two callees enter through their footprint contracts, each in the place where P3.p3_evt takes the plain one:
   asan_memset_contract_F (lib/A/Prog/asan_memset_cF.v, proved by a Theorem Labs lane as asan_memset_holds_F in
   lib/A/Prog/asan_memsetF.v) and reac_identity_init_contract_F (lib/A/Prog/reac_identity_init_c.v:62).  Their own
   footprint premises are passed through unchanged, instantiated at these call sites (fb, 35, spv for the memset;
   id and spv for the init).  rng_bytes RNG is a forall-memory form and is passed through unchanged.
   P3.v's code is unchanged since release c5e779efe8c (comments edited); it differs from the source blob above: 40 of its code lines changed or removed, 353 added. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c asan_memset_cF reac_identity_init_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require P3.
(* Last: StepF's step / finish (evtF goals) shadow Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* P3.p3_sb with the evtF goal shape (the one helper the template shows must change: StepF's step and
   mem_after_store close an evtF goal where Step's close an evt one). *)
Ltac p3F_sb :=
  step;
  try (lazymatch goal with
       | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
           first [ change bs with [Z_to_bv 8 0] | change bs with [Z_to_bv 8 6] | change bs with [Z_to_bv 8 3] ];
           mem_after_store
       end).

(* ---- p3_evt (P3.v:153) under a footprint RNG. ---- *)
Lemma p3_evt_F : asan_memset_contract_F -> reac_identity_init_contract_F ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv S id lo A fb : Z)
         (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27
          b28 : byte) (idb fbj : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 S -> s11 = Z_to_bv 64 id -> s1 = Z_to_bv 64 A ->
    0 <= spv < 2 ^ 64 -> 0 <= S -> RT_HI <= S -> S + 365 <= 2 ^ 64 -> S + 365 <= HIGHMEM_BEG ->
    0 < id -> id + 38 <= 2 ^ 64 -> id mod 2 = 0 ->
    (id + 38 <= S + 336 \/ S + 365 <= id) ->
    0 <= A -> A + 40 <= 2 ^ 64 -> (A + 40 <= S + 336 \/ S + 365 <= A + 32) ->
    0 < fb -> fb + 35 <= 2 ^ 64 -> (fb + 35 <= S + 336 \/ S + 365 <= fb) -> (fb + 35 <= id \/ id + 38 <= fb) ->
    rw_cells rsegs m (S + 336) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
                                C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18; C1 b19;
                                C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28] ->
    rw_cells rsegs m id [CB 38 idb] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 fb)] ->
    rw_cells rsegs m fb [CB 35 fbj] ->
    (forall m', bytes_at rsegs m' (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
       addressable m' id 38) ->
    (forall m', bytes_at rsegs m' (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
       addressable m' fb 35) ->
    end_in_app id 38 -> (id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id + 38 <= spv - REAC_IDENTITY_INIT_K \/ spv <= id) ->
    end_in_app fb 35 -> app_mem (fb + 7) -> (fb + 35 <= RT_LO \/ RT_HI <= fb) ->
    (fb + 35 <= spv - REAC_IDENTITY_INIT_K \/ spv <= fb) ->
    stk rsegs m lo spv -> lo + REAC_IDENTITY_INIT_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    (* the segment's own accesses: the 19 frame-shadow stores and the spill load *)
    ExecF.rng RNG (S + 336) 29 ->
    ExecF.rng RNG (A + 32) 8 ->
    (* __asan_memset's regions (asan_memset_contract_F's rng premises at this call site), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG fb 35 ->
    sh_word_rng RNG fb 35 ->
    sh_word_rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    (* reac_identity_init's regions (reac_identity_init_contract_F's rng premises), unchanged *)
    ExecF.rng RNG (spv - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    sh_word_rng RNG (spv - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    ExecF.rng RNG ((spv - REAC_IDENTITY_INIT_K) / 8 + ASAN_K)
                  ((spv - 1) / 8 - (spv - REAC_IDENTITY_INIT_K) / 8 + 1) ->
    ExecF.rng RNG RT_LO (RT_HI - RT_LO) ->
    (id <> 0 -> ExecF.rng RNG id 38 /\
                ExecF.rng RNG ((id / 8 + ASAN_K) / 8 * 8)
                              (((id + 37) / 8 + ASAN_K) / 8 * 8 + 8 - (id / 8 + ASAN_K) / 8 * 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (msh m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 336, S + 365)] m msh /\ wmono rsegs m msh /\
         rw_cells rsegs msh (S + 336) (P3.p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) /\
         munch [(fb, fb + 35); (spv - REAC_IDENTITY_INIT_K, spv); (id, id + 38)] msh m' /\ wmono rsegs msh m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)] /\
         rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RII RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23
    b24 b25 b26 b27 b28 idb fbj
    -> -> -> -> Hspv HS0 HSRT HS64 HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
    RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HMI
    Gsh Ga32 Gby Gimg Gstk Gfb Gshfb Gshs Gik Gikw Giks Girt Gid.
  unfold asan_memset_contract_F, ASAN_MEMSET in MSET. cbv zeta in MSET.
  unfold reac_identity_init_contract_F, reac_identity_init_post, reac_identity_init_W, REAC_IDENTITY_INIT in RII.
  unfold REAC_IDENTITY_INIT_K in *.
  assert (EKm : ASAN_MEMSET_K = 2208) by reflexivity.
  pose proof (munch_refl [(S + 336, S + 365)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  (* 0x81b14 .. 0x81b64: the 19 shadow stores and the two li (the stored byte 3 at 81b64 is p3F_sb's third case). *)
  p3F_sb. p3F_sb. p3F_sb. p3F_sb.                  (* 81b14 .. 81b20: S(fr) + 336 .. 339 *)
  step.                                            (* 81b24 li a0,6 *)
  p3F_sb. p3F_sb. p3F_sb. p3F_sb. p3F_sb. p3F_sb.  (* 81b28 .. 81b3c: 349 .. 354 *)
  p3F_sb. p3F_sb.                                  (* 81b40 / 81b44: 360 / 361 *)
  step.                                            (* 81b48 li a1,3 *)
  p3F_sb. p3F_sb. p3F_sb. p3F_sb.                  (* 81b4c .. 81b58: 340 (= 6), 346 .. 348 *)
  p3F_sb. p3F_sb. p3F_sb.                          (* 81b5c / 81b60: 362 / 363; 81b64: 364 (= 3) *)
  (* 0x81b68 li a2,35 ; 0x81b6c ld a0,32(s1) ; 0x81b70 li a1,0 ; 0x81b74 jal checked_memset *)
  step. step. step. step.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into msh end.
  assert (HB29 : bytes_at rsegs msh (S + 336) (cells_bytes (P3.p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23))).
  { destruct RWS as [[_ HB] _]. exact HB. }
  assert (HACs : asan_cells msh).
  { apply (asan_cells_kept [(S + 336, S + 365)] m msh HAC MU0). cbn [disjoint_from].
    unfold RT_LO, RT_HI in *. split; [lia | exact I]. }
  assert (HSWs : shadow_rw msh).
  { eapply (P3.p3_shadow_rw_keep m msh (S + 336) 29 _ HSW); [| exact WM0 | exact HB29 | reflexivity].
    replace (S + 336 + 29) with (S + 365) by lia. exact MU0. }
  assert (HB5 : bytes_at rsegs msh (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6]).
  { assert (HB' : bytes_at rsegs msh (S + 336)
                    ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ++
                     [b5; b6; b7; b8; b9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; b19; b20; b21; b22; b23;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3])) by exact HB29.
    apply bytes_at_app in HB'. exact (proj1 HB'). }
  assert (HB360 : bytes_at rsegs msh (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3]).
  { assert (HB' : bytes_at rsegs msh (S + 336)
                    ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6;
                      b5; b6; b7; b8; b9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; b19; b20; b21; b22; b23] ++
                     [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3])) by exact HB29.
    apply bytes_at_app in HB'. destruct HB' as [_ HB'].
    match type of HB' with bytes_at _ _ ?a _ => replace a with (S + 360) in HB' by (cbn; lia) end.
    exact HB'. }
  (* the memset of first.sroa.7: D = [s1 + 32] = fb, N = 35, a1 = 0; ld a0,32(s1) reads RWA. *)
  eapply ExecF.evtF_cut.
  { eapply MSET with (RNG := RNG) (junk := fbj) (lo := lo).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RWF.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      exact (HADDRf msh HB360).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HEF.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. right. exact HF7.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HRTF.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact ST.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - exact HHM.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HAE.
    - exact HACs.
    - exact HSWs.
    - exact HMI.
    - exact Gby.
    - exact Gimg.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gstk.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gfb.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gshfb.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gshs. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mm &
              E & MUm & WMm & MIm & STm & RWm & HACm & HSWm).
  subst ms'.
  assert (Efb : bv_unsigned (Z_to_bv 64 fb) = fb) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (E35 : bv_unsigned (Z_to_bv 64 35) = 35) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  rewrite Efb in MUm, RWm. rewrite E35 in MUm, RWm. rewrite Esp in MUm, STm.
  fold_lit_ux_in RWm.
  replace (ret_pc (Z_to_bv 64 0x81b78)) with (Z_to_bv 64 0x81b78)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the identity record's cell and its 5 shadow bytes, past the memset ([fb, fb + 35) and its window) *)
  assert (RWI' : rw_cells rsegs mm id [CB 38 idb]).
  { apply (rw_cells_transport rsegs [(fb, fb + 35); (spv - ASAN_MEMSET_K, spv)] msh mm id _ RWI MUm WMm).
    cbn [disjoint_from cells_size csize]. repeat split; try exact I; lia. }
  assert (HB5m : bytes_at rsegs mm (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6]).
  { apply (bytes_at_transport rsegs [(fb, fb + 35); (spv - ASAN_MEMSET_K, spv)] msh mm (S + 336) _ HB5 MUm).
    cbn [disjoint_from length]. change (Z.of_nat 5) with 5. repeat split; try exact I; lia. }
  (* 0x81b78 mv a0,s11 ; 0x81b7c jal reac_identity_init *)
  step. step.
  eapply ExecF.evtF_cut.
  { eapply RII with (RNG := RNG) (lo := lo) (id := id) (idb := idb).
    - first [reflexivity | f_equal; lia].
    - lia.
    - intros _. split; [exact Hidm | exact RWI'].
    - exact MIm.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact STm.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - exact HHM.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HAE.
    - exact HACm.
    - exact HSWm.
    - intros _. split; [exact (HADDR mm HB5m) | exact HEI].
    - intros _. exact HRTI.
    - intros _. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HSTI.
    - exact Gby.
    - exact Gimg.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gik.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gikw.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Giks.
    - exact Girt.
    - exact Gid. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
              m' & E & MUc & WMc & MIc & STc & HACc & HSWc & _ & RWc).
  subst ms'.
  rewrite Esp in MUc, STc.
  specialize (RWc ltac:(lia)).
  replace (ret_pc (Z_to_bv 64 0x81b80)) with (Z_to_bv 64 0x81b80)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the two calls' write sets, joined: [spv - 2208, spv) is inside [spv - 2224, spv) *)
  assert (MUcall : munch [(fb, fb + 35); (spv - 2224, spv); (id, id + 38)] msh m').
  { apply (munch_trans _ msh mm m').
    - eapply munch_weaken; [| exact MUm]. intros x Hx. cbn [outside] in *.
      destruct Hx as (H1 & H2 & H3 & _). split; [exact H1|]. split; [|exact I]. intros Hc. apply H2. lia.
    - eapply munch_weaken; [| exact MUc]. intros x Hx. cbn [outside] in *.
      destruct Hx as (H1 & H2 & H3 & _). split; [exact H2|]. split; [exact H3 | exact I]. }
  assert (WMcall : wmono rsegs msh m') by (eapply wmono_trans; [exact WMm | exact WMc]).
  assert (RWF' : rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)]).
  { apply (rw_cells_transport rsegs [(spv - 2224, spv); (id, id + 38)] mm m' fb _ RWm MUc WMc).
    cbn [disjoint_from cells_size csize]. repeat split; try exact I; lia. }
  apply ExecF.evtF_done. do 3 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU0|]. split; [exact WM0|]. split; [exact RWS|].
  split; [exact MUcall|]. split; [exact WMcall|]. split; [exact MIc|].
  split; [exact STc|]. split; [exact HACc|]. split; [exact HSWc|].
  split; [exact RWF' | exact RWc].
Qed.

(* ---- Route (C) (a Theorem Labs lane's frozen form; p3_evt_F stays as it is): p3_evt_F with the two callees' _F_on contracts,
   asan_memset_contract_F_on (lib/A/Prog/asan_memset_cF_on.v, a Theorem Labs lane 83ab88c3325) and
   reac_identity_init_contract_F_on (lib/A/Prog/reac_identity_init_c.v, a Theorem Labs lane 09bc1c86820).  The run reads no
   shadow byte and stores none through `shadow_rw m`: its 19 frame-shadow stores (0x81b14 .. 0x81b64) go through the
   rw_cells premise of S + 336 .. S + 364.  The shadow it needs present is its two callees': the memset at 0x81b74
   (asan_memset_shadow_R at a0 = fb, a2 = 35) and reac_identity_init at 0x81b7c (reac_identity_init_shadow_R id).  That
   union is P3.p3_evt_shadow_R id fb (Seg/P3.v, the plain p3_evt_on's region), cited by name.  The post's `shadow_rw m'`
   becomes the transport `forall P, shadow_rw_on P m -> shadow_rw_on P m'`.  It is the run p3_evt_ro_F_on needs. ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memset_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.

Lemma p3_evt_F_on : asan_memset_cF_on.asan_memset_contract_F_on -> reac_identity_init_contract_F_on ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv S id lo A fb : Z)
         (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27
          b28 : byte) (idb fbj : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 S -> s11 = Z_to_bv 64 id -> s1 = Z_to_bv 64 A ->
    0 <= spv < 2 ^ 64 -> 0 <= S -> RT_HI <= S -> S + 365 <= 2 ^ 64 -> S + 365 <= HIGHMEM_BEG ->
    0 < id -> id + 38 <= 2 ^ 64 -> id mod 2 = 0 ->
    (id + 38 <= S + 336 \/ S + 365 <= id) ->
    0 <= A -> A + 40 <= 2 ^ 64 -> (A + 40 <= S + 336 \/ S + 365 <= A + 32) ->
    0 < fb -> fb + 35 <= 2 ^ 64 -> (fb + 35 <= S + 336 \/ S + 365 <= fb) -> (fb + 35 <= id \/ id + 38 <= fb) ->
    rw_cells rsegs m (S + 336) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
                                C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18; C1 b19;
                                C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28] ->
    rw_cells rsegs m id [CB 38 idb] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 fb)] ->
    rw_cells rsegs m fb [CB 35 fbj] ->
    (forall m', bytes_at rsegs m' (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
       addressable m' id 38) ->
    (forall m', bytes_at rsegs m' (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
       addressable m' fb 35) ->
    end_in_app id 38 -> (id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id + 38 <= spv - REAC_IDENTITY_INIT_K \/ spv <= id) ->
    end_in_app fb 35 -> app_mem (fb + 7) -> (fb + 35 <= RT_LO \/ RT_HI <= fb) ->
    (fb + 35 <= spv - REAC_IDENTITY_INIT_K \/ spv <= fb) ->
    stk rsegs m lo spv -> lo + REAC_IDENTITY_INIT_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (P3.p3_evt_shadow_R id fb) m -> mem_inv rsegs m ->
    (* the segment's own accesses: the 19 frame-shadow stores and the spill load *)
    ExecF.rng RNG (S + 336) 29 ->
    ExecF.rng RNG (A + 32) 8 ->
    (* __asan_memset's regions (asan_memset_contract_F_on's rng premises at this call site), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG fb 35 ->
    sh_word_rng RNG fb 35 ->
    sh_word_rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    (* reac_identity_init's regions (reac_identity_init_contract_F_on's rng premises), unchanged *)
    ExecF.rng RNG (spv - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    sh_word_rng RNG (spv - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    ExecF.rng RNG ((spv - REAC_IDENTITY_INIT_K) / 8 + ASAN_K)
                  ((spv - 1) / 8 - (spv - REAC_IDENTITY_INIT_K) / 8 + 1) ->
    ExecF.rng RNG RT_LO (RT_HI - RT_LO) ->
    (id <> 0 -> ExecF.rng RNG id 38 /\
                ExecF.rng RNG ((id / 8 + ASAN_K) / 8 * 8)
                              (((id + 37) / 8 + ASAN_K) / 8 * 8 + 8 - (id / 8 + ASAN_K) / 8 * 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (msh m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 336, S + 365)] m msh /\ wmono rsegs m msh /\
         rw_cells rsegs msh (S + 336) (P3.p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) /\
         munch [(fb, fb + 35); (spv - REAC_IDENTITY_INIT_K, spv); (id, id + 38)] msh m' /\ wmono rsegs msh m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\
         (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)] /\
         rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RII RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23
    b24 b25 b26 b27 b28 idb fbj
    -> -> -> -> Hspv HS0 HSRT HS64 HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
    RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HMI
    Gsh Ga32 Gby Gimg Gstk Gfb Gshfb Gshs Gik Gikw Giks Girt Gid.
  unfold asan_memset_cF_on.asan_memset_contract_F_on, ASAN_MEMSET in MSET. cbv zeta in MSET.
  unfold reac_identity_init_contract_F_on, reac_identity_init_post_on, reac_identity_init_W, REAC_IDENTITY_INIT in RII.
  unfold REAC_IDENTITY_INIT_K in *.
  assert (EKm : ASAN_MEMSET_K = 2208) by reflexivity.
  pose proof (munch_refl [(S + 336, S + 365)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  (* 0x81b14 .. 0x81b64: the 19 shadow stores and the two li (the stored byte 3 at 81b64 is p3F_sb's third case). *)
  p3F_sb. p3F_sb. p3F_sb. p3F_sb.                  (* 81b14 .. 81b20: S(fr) + 336 .. 339 *)
  step.                                            (* 81b24 li a0,6 *)
  p3F_sb. p3F_sb. p3F_sb. p3F_sb. p3F_sb. p3F_sb.  (* 81b28 .. 81b3c: 349 .. 354 *)
  p3F_sb. p3F_sb.                                  (* 81b40 / 81b44: 360 / 361 *)
  step.                                            (* 81b48 li a1,3 *)
  p3F_sb. p3F_sb. p3F_sb. p3F_sb.                  (* 81b4c .. 81b58: 340 (= 6), 346 .. 348 *)
  p3F_sb. p3F_sb. p3F_sb.                          (* 81b5c / 81b60: 362 / 363; 81b64: 364 (= 3) *)
  (* 0x81b68 li a2,35 ; 0x81b6c ld a0,32(s1) ; 0x81b70 li a1,0 ; 0x81b74 jal checked_memset *)
  step. step. step. step.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into msh end.
  assert (HB29 : bytes_at rsegs msh (S + 336) (cells_bytes (P3.p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23))).
  { destruct RWS as [[_ HB] _]. exact HB. }
  assert (HACs : asan_cells msh).
  { apply (asan_cells_kept [(S + 336, S + 365)] m msh HAC MU0). cbn [disjoint_from].
    unfold RT_LO, RT_HI in *. split; [lia | exact I]. }
  (* every region present and writable at m still is at msh (P3.p3_shadow_rw_keep_on: the stores write
     [S + 336, S + 365) and leave it readable) *)
  assert (KPs : forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P msh).
  { intros P HP.
    eapply (P3.p3_shadow_rw_keep_on m msh (S + 336) 29 _); [| exact WM0 | exact HB29 | reflexivity | exact HP].
    replace (S + 336 + 29) with (S + 365) by lia. exact MU0. }
  assert (HB5 : bytes_at rsegs msh (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6]).
  { assert (HB' : bytes_at rsegs msh (S + 336)
                    ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ++
                     [b5; b6; b7; b8; b9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; b19; b20; b21; b22; b23;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3])) by exact HB29.
    apply bytes_at_app in HB'. exact (proj1 HB'). }
  assert (HB360 : bytes_at rsegs msh (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3]).
  { assert (HB' : bytes_at rsegs msh (S + 336)
                    ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6;
                      b5; b6; b7; b8; b9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
                      Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; b19; b20; b21; b22; b23] ++
                     [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3])) by exact HB29.
    apply bytes_at_app in HB'. destruct HB' as [_ HB'].
    match type of HB' with bytes_at _ _ ?a _ => replace a with (S + 360) in HB' by (cbn; lia) end.
    exact HB'. }
  (* the memset of first.sroa.7: D = [s1 + 32] = fb, N = 35, a1 = 0; ld a0,32(s1) reads RWA. *)
  eapply ExecF.evtF_cut.
  { eapply MSET with (RNG := RNG) (junk := fbj) (lo := lo).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RWF.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      exact (HADDRf msh HB360).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HEF.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. right. exact HF7.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HRTF.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact ST.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - exact HHM.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HAE.
    - exact HACs.
    - apply (A.ShadowRwOn.shadow_rw_on_mono (P3.p3_evt_shadow_R id fb)); [|exact (KPs _ HSW)].
      intros x Hx. unfold P3.p3_evt_shadow_R. left. exact Hx.
    - exact HMI.
    - exact Gby.
    - exact Gimg.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gstk.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gfb.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gshfb.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gshs. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mm &
              E & MUm & WMm & MIm & STm & RWm & HACm & HSWm).
  subst ms'.
  assert (Efb : bv_unsigned (Z_to_bv 64 fb) = fb) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (E35 : bv_unsigned (Z_to_bv 64 35) = 35) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  rewrite Efb in MUm, RWm. rewrite E35 in MUm, RWm. rewrite Esp in MUm, STm.
  fold_lit_ux_in RWm.
  replace (ret_pc (Z_to_bv 64 0x81b78)) with (Z_to_bv 64 0x81b78)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the identity record's cell and its 5 shadow bytes, past the memset ([fb, fb + 35) and its window) *)
  assert (RWI' : rw_cells rsegs mm id [CB 38 idb]).
  { apply (rw_cells_transport rsegs [(fb, fb + 35); (spv - ASAN_MEMSET_K, spv)] msh mm id _ RWI MUm WMm).
    cbn [disjoint_from cells_size csize]. repeat split; try exact I; lia. }
  assert (HB5m : bytes_at rsegs mm (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6]).
  { apply (bytes_at_transport rsegs [(fb, fb + 35); (spv - ASAN_MEMSET_K, spv)] msh mm (S + 336) _ HB5 MUm).
    cbn [disjoint_from length]. change (Z.of_nat 5) with 5. repeat split; try exact I; lia. }
  (* 0x81b78 mv a0,s11 ; 0x81b7c jal reac_identity_init *)
  step. step.
  eapply ExecF.evtF_cut.
  { eapply RII with (RNG := RNG) (lo := lo) (id := id) (idb := idb).
    - first [reflexivity | f_equal; lia].
    - lia.
    - intros _. split; [exact Hidm | exact RWI'].
    - exact MIm.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact STm.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - exact HHM.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HAE.
    - exact HACm.
    - apply (A.ShadowRwOn.shadow_rw_on_mono (P3.p3_evt_shadow_R id fb)); [|exact (HSWm _ (KPs _ HSW))].
      intros x Hx. unfold P3.p3_evt_shadow_R. right. exact Hx.
    - intros _. split; [exact (HADDR mm HB5m) | exact HEI].
    - intros _. exact HRTI.
    - intros _. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HSTI.
    - exact Gby.
    - exact Gimg.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gik.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gikw.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Giks.
    - exact Girt.
    - exact Gid. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
              m' & E & MUc & WMc & MIc & STc & HACc & HSWc & _ & RWc).
  subst ms'.
  rewrite Esp in MUc, STc.
  specialize (RWc ltac:(lia)).
  replace (ret_pc (Z_to_bv 64 0x81b80)) with (Z_to_bv 64 0x81b80)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the two calls' write sets, joined: [spv - 2208, spv) is inside [spv - 2224, spv) *)
  assert (MUcall : munch [(fb, fb + 35); (spv - 2224, spv); (id, id + 38)] msh m').
  { apply (munch_trans _ msh mm m').
    - eapply munch_weaken; [| exact MUm]. intros x Hx. cbn [outside] in *.
      destruct Hx as (H1 & H2 & H3 & _). split; [exact H1|]. split; [|exact I]. intros Hc. apply H2. lia.
    - eapply munch_weaken; [| exact MUc]. intros x Hx. cbn [outside] in *.
      destruct Hx as (H1 & H2 & H3 & _). split; [exact H2|]. split; [exact H3 | exact I]. }
  assert (WMcall : wmono rsegs msh m') by (eapply wmono_trans; [exact WMm | exact WMc]).
  assert (RWF' : rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)]).
  { apply (rw_cells_transport rsegs [(spv - 2224, spv); (id, id + 38)] mm m' fb _ RWm MUc WMc).
    cbn [disjoint_from cells_size csize]. repeat split; try exact I; lia. }
  apply ExecF.evtF_done. do 3 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU0|]. split; [exact WM0|]. split; [exact RWS|].
  split; [exact MUcall|]. split; [exact WMcall|]. split; [exact MIc|].
  split; [exact STc|]. split; [exact HACc|].
  split; [intros P HP; exact (HSWc P (HSWm P (KPs P HP)))|].
  split; [exact RWF' | exact RWc].
Qed.

(* P3.p3_evt's conclusion under the two footprint contracts: p3_evt_F at ExecF.RNG_all. *)
Lemma p3_evt_of_F : asan_memset_contract_F -> reac_identity_init_contract_F ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv S id lo A fb : Z)
         (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27
          b28 : byte) (idb fbj : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 S -> s11 = Z_to_bv 64 id -> s1 = Z_to_bv 64 A ->
    0 <= spv < 2 ^ 64 -> 0 <= S -> RT_HI <= S -> S + 365 <= 2 ^ 64 -> S + 365 <= HIGHMEM_BEG ->
    0 < id -> id + 38 <= 2 ^ 64 -> id mod 2 = 0 ->
    (id + 38 <= S + 336 \/ S + 365 <= id) ->
    0 <= A -> A + 40 <= 2 ^ 64 -> (A + 40 <= S + 336 \/ S + 365 <= A + 32) ->
    0 < fb -> fb + 35 <= 2 ^ 64 -> (fb + 35 <= S + 336 \/ S + 365 <= fb) -> (fb + 35 <= id \/ id + 38 <= fb) ->
    rw_cells rsegs m (S + 336) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
                                C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18; C1 b19;
                                C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28] ->
    rw_cells rsegs m id [CB 38 idb] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 fb)] ->
    rw_cells rsegs m fb [CB 35 fbj] ->
    (forall m', bytes_at rsegs m' (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
       addressable m' id 38) ->
    (forall m', bytes_at rsegs m' (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
       addressable m' fb 35) ->
    end_in_app id 38 -> (id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id + 38 <= spv - REAC_IDENTITY_INIT_K \/ spv <= id) ->
    end_in_app fb 35 -> app_mem (fb + 7) -> (fb + 35 <= RT_LO \/ RT_HI <= fb) ->
    (fb + 35 <= spv - REAC_IDENTITY_INIT_K \/ spv <= fb) ->
    stk rsegs m lo spv -> lo + REAC_IDENTITY_INIT_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (msh m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 336, S + 365)] m msh /\ wmono rsegs m msh /\
         rw_cells rsegs msh (S + 336) (P3.p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) /\
         munch [(fb, fb + 35); (spv - REAC_IDENTITY_INIT_K, spv); (id, id + 38)] msh m' /\ wmono rsegs msh m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)] /\
         rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RII ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23
    b24 b25 b26 b27 b28 idb fbj
    E2 E19 E27 E9 Hspv HS0 HSRT HS64 HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
    RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HMI.
  assert (HFBa : fb + 35 <= APPMEM_END).
  { destruct HEF as [HEF0 | HEF1]; [lia|].
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HEF1 |- *. lia. }
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (p3_evt_F MSET RII ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
           s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
           b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 idb fbj
           E2 E19 E27 E9 Hspv HS0 HSRT HS64 HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
           RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HMI).
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; unfold ASAN_MEMSET_K, REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply ExecF.rng_all; lia.
  - apply sh_word_rng_all; lia.
  - apply sh_word_rng_all;
      unfold ASAN_MEMSET_K, REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply ExecF.rng_all; unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply sh_word_rng_all; unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply ExecF.rng_all;
      unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END, ASAN_K in *; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; unfold RT_LO, RT_HI; lia.
  - intros _. split.
    + apply ExecF.rng_all; lia.
    + apply ExecF.rng_all; unfold ASAN_K in *; Z.div_mod_to_equations; lia.
Qed.

Example p3_evt_of_F_verbatim : True.
Proof.
  lazymatch type of P3.p3_evt with ?P -> ?P2 -> ?A =>
    constr_eq P asan_memset_contract; constr_eq P2 reac_identity_init_contract;
    lazymatch type of p3_evt_of_F with ?Q -> ?Q2 -> ?B =>
      constr_eq Q asan_memset_contract_F; constr_eq Q2 reac_identity_init_contract_F; constr_eq A B
    end
  end.
  exact I.
Qed.

(* ---- p3_evt_ro (P3.v:463) under a footprint RNG: p3_evt_F on the normalized memory, moved back by
   MemNormF.evtF_normalize_ro.  The import block below is P3.v's own second block, in its order, so that the
   names of p3_evt_ro_of_F's statement are the names of P3.p3_evt_ro's (`getr` is YK11's from here on). ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift BzBridge KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs P1.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_b5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.

(* p3_evt_ro_F states lib.A.MemNorm's ro_agree (the copy the image-A walk states; MemNormF's evtF_normalize_ro
   takes that copy too), and its script uses that copy throughout (MN). *)

Lemma p3_evt_ro_F : asan_memset_contract_F -> reac_identity_init_contract_F ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv S id lo A fb : Z)
         (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27
          b28 : byte) (idb fbj : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 S -> s11 = Z_to_bv 64 id -> s1 = Z_to_bv 64 A ->
    0 <= spv < 2 ^ 64 -> LOWMEM_END <= S -> S + 365 <= HIGHMEM_BEG ->
    0x5fe000 <= id -> id + 38 <= 2 ^ 64 -> id mod 2 = 0 ->
    (id + 38 <= S + 336 \/ S + 365 <= id) ->
    0x5fe000 <= A -> A + 40 <= 2 ^ 64 -> (A + 40 <= S + 336 \/ S + 365 <= A + 32) ->
    0x5fe000 <= fb -> fb + 35 <= 2 ^ 64 -> (fb + 35 <= S + 336 \/ S + 365 <= fb) ->
    (fb + 35 <= id \/ id + 38 <= fb) ->
    rw_cells rsegs m (S + 336) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
                                C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18; C1 b19;
                                C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28] ->
    rw_cells rsegs m id [CB 38 idb] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 fb)] ->
    rw_cells rsegs m fb [CB 35 fbj] ->
    (forall m', bytes_at rsegs m' (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
       addressable m' id 38) ->
    (forall m', bytes_at rsegs m' (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
       addressable m' fb 35) ->
    end_in_app id 38 -> (id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id + 38 <= spv - REAC_IDENTITY_INIT_K \/ spv <= id) ->
    end_in_app fb 35 -> app_mem (fb + 7) -> (fb + 35 <= RT_LO \/ RT_HI <= fb) ->
    (fb + 35 <= spv - REAC_IDENTITY_INIT_K \/ spv <= fb) ->
    stk rsegs m lo spv -> lo + REAC_IDENTITY_INIT_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m ->
    ExecF.rng RNG (S + 336) 29 ->
    ExecF.rng RNG (A + 32) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG fb 35 ->
    sh_word_rng RNG fb 35 ->
    sh_word_rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG (spv - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    sh_word_rng RNG (spv - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    ExecF.rng RNG ((spv - REAC_IDENTITY_INIT_K) / 8 + ASAN_K)
                  ((spv - 1) / 8 - (spv - REAC_IDENTITY_INIT_K) / 8 + 1) ->
    ExecF.rng RNG RT_LO (RT_HI - RT_LO) ->
    (id <> 0 -> ExecF.rng RNG id 38 /\
                ExecF.rng RNG ((id / 8 + ASAN_K) / 8 * 8)
                              (((id + 37) / 8 + ASAN_K) / 8 * 8 + 8 - (id / 8 + ASAN_K) / 8 * 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (msh m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 336, S + 365)] m msh /\ wmono rsegs m msh /\
         rw_cells rsegs msh (S + 336) (P3.p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) /\
         munch [(fb, fb + 35); (spv - REAC_IDENTITY_INIT_K, spv); (id, id + 38)] msh m' /\ wmono rsegs msh m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\
         rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)] /\
         rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RII RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23
    b24 b25 b26 b27 b28 idb fbj
    E2 E19 E27 E9 Hspv HSlo HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
    RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HRO
    Gsh Ga32 Gby Gimg Gstk Gfb Gshfb Gshs Gik Gikw Giks Girt Gid.
  assert (EL : LOWMEM_END = 2147450880) by reflexivity.
  assert (EH : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (ERT : RT_HI = 0xa9578) by reflexivity.
  pose proof (MN.mem_rel_normalize rsegs m HRO) as REL.
  eapply ExecF.evtF_mono.
  - eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (seg_rom rsegs) HRO).
    apply (p3_evt_F MSET RII RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc (MN.normalize rsegs m) spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
             b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 idb fbj E2 E19 E27 E9 Hspv
             ltac:(lia) ltac:(lia) ltac:(lia) HSHI ltac:(lia) Hid38 Hidm HSEPs ltac:(lia) HA40 HSEPa ltac:(lia)
             Hfb35 HSEPb HSEPfi
             (P3.p3_rw_rel m _ (S + 336) _ REL ltac:(lia) RWS) (P3.p3_rw_rel m _ id _ REL ltac:(lia) RWI)
             (P3.p3_rw_rel m _ (A + 32) _ REL ltac:(lia) RWA) (P3.p3_rw_rel m _ fb _ REL ltac:(lia) RWF)
             HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF
             (P3.p3_stk_rel m _ lo spv REL ltac:(lia) ltac:(lia) ST) HLO HHM HAE (P3.p3_cells_rel m _ REL HAC)
             (P3.p3_shadow_rw_rel m _ REL HSW) (MN.mem_inv_normalize rsegs m)
             Gsh Ga32 Gby Gimg Gstk Gfb Gshfb Gshs Gik Gikw Giks Girt Gid).
  - intros s (s0' & (R & msh0 & m0' & -> & P2 & P3' & P4 & P8 & P9 & P19 & P26 & P22 & P25 & MU1 & WM1 & RWS1 &
               MU2 & WM2 & _ & ST2 & _ & _ & RWF2 & RW2) & MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    assert (RELsh : MN.mem_rel rsegs (P3.p3_lift m msh0) msh0).
    { split.
      - intros a. unfold MN.normalize, P3.p3_lift.
        destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr rsegs a) eqn:E; [|reflexivity].
        rewrite (MU1 a).
        + unfold MN.normalize. rewrite E. reflexivity.
        + pose proof (Tac_b5.sl_ro_lo a E) as Ha. cbn [outside]. split; [lia | exact I].
      - intros a b E Hb. unfold P3.p3_lift in Hb. rewrite E in Hb. exact (proj2 REL a b E Hb). }
    assert (ROsh : MN.ro_same rsegs m (P3.p3_lift m msh0)).
    { intros a E. unfold P3.p3_lift. rewrite E. reflexivity. }
    assert (RO2 : MN.ro_same rsegs (P3.p3_lift m msh0) ms).
    { intros a E. rewrite (RS a E). unfold P3.p3_lift. rewrite E. reflexivity. }
    exists R, (P3.p3_lift m msh0), ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3'|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P22|]. split; [exact P25|].
    split; [exact (MN.munch_rel rsegs _ m _ _ msh0 REL RELsh ROsh MU1)|].
    split; [exact (MN.wmono_rel rsegs m _ _ msh0 REL RELsh ROsh WM1)|].
    split; [exact (P3.p3_rw_back _ msh0 (S + 336) _ RELsh ltac:(lia) RWS1)|].
    split; [exact (MN.munch_rel rsegs _ _ msh0 ms m0' RELsh Hmem RO2 MU2)|].
    split; [exact (MN.wmono_rel rsegs _ msh0 ms m0' RELsh Hmem RO2 WM2)|].
    split; [exact (MN.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (P3.p3_stk_back ms m0' lo spv Hmem ltac:(lia) ltac:(lia) ST2)|].
    split; [exact (P3.p3_rw_back ms m0' fb _ Hmem ltac:(lia) RWF2) |].
    exact (P3.p3_rw_back ms m0' id _ Hmem ltac:(lia) RW2).
Qed.

(* ---- Route (C) (a Theorem Labs lane's frozen form; p3_evt_ro_F stays as it is): p3_evt_ro_F with the two callees' _F_on
   contracts.  Its one shadow premise `shadow_rw m` becomes shadow_rw_on of P3.p3_evt_ro_shadow_R id fb (Seg/P3.v, the
   plain p3_evt_ro_on's region, = P3.p3_evt_shadow_R id fb): the run (p3_evt_F_on on MN.normalize rsegs m, moved back
   by MNF.evtF_normalize_ro as in p3_evt_ro_F) reads and stores no shadow byte through it; only its two callees' regions
   (the memset at a0 = fb, a2 = 35; reac_identity_init at id) must be present, and normalize keeps them
   (A.ShadowRwOnT.shadow_rw_on_rel).  p3_evt_ro_F's post states no shadow fact, so this post is p3_evt_ro_F's. ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOnT.

Lemma p3_evt_ro_F_on : asan_memset_cF_on.asan_memset_contract_F_on -> reac_identity_init_contract_F_on ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv S id lo A fb : Z)
         (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27
          b28 : byte) (idb fbj : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 S -> s11 = Z_to_bv 64 id -> s1 = Z_to_bv 64 A ->
    0 <= spv < 2 ^ 64 -> LOWMEM_END <= S -> S + 365 <= HIGHMEM_BEG ->
    0x5fe000 <= id -> id + 38 <= 2 ^ 64 -> id mod 2 = 0 ->
    (id + 38 <= S + 336 \/ S + 365 <= id) ->
    0x5fe000 <= A -> A + 40 <= 2 ^ 64 -> (A + 40 <= S + 336 \/ S + 365 <= A + 32) ->
    0x5fe000 <= fb -> fb + 35 <= 2 ^ 64 -> (fb + 35 <= S + 336 \/ S + 365 <= fb) ->
    (fb + 35 <= id \/ id + 38 <= fb) ->
    rw_cells rsegs m (S + 336) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
                                C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18; C1 b19;
                                C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28] ->
    rw_cells rsegs m id [CB 38 idb] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 fb)] ->
    rw_cells rsegs m fb [CB 35 fbj] ->
    (forall m', bytes_at rsegs m' (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
       addressable m' id 38) ->
    (forall m', bytes_at rsegs m' (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
       addressable m' fb 35) ->
    end_in_app id 38 -> (id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id + 38 <= spv - REAC_IDENTITY_INIT_K \/ spv <= id) ->
    end_in_app fb 35 -> app_mem (fb + 7) -> (fb + 35 <= RT_LO \/ RT_HI <= fb) ->
    (fb + 35 <= spv - REAC_IDENTITY_INIT_K \/ spv <= fb) ->
    stk rsegs m lo spv -> lo + REAC_IDENTITY_INIT_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (P3.p3_evt_ro_shadow_R id fb) m ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m ->
    ExecF.rng RNG (S + 336) 29 ->
    ExecF.rng RNG (A + 32) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG fb 35 ->
    sh_word_rng RNG fb 35 ->
    sh_word_rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG (spv - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    sh_word_rng RNG (spv - REAC_IDENTITY_INIT_K) REAC_IDENTITY_INIT_K ->
    ExecF.rng RNG ((spv - REAC_IDENTITY_INIT_K) / 8 + ASAN_K)
                  ((spv - 1) / 8 - (spv - REAC_IDENTITY_INIT_K) / 8 + 1) ->
    ExecF.rng RNG RT_LO (RT_HI - RT_LO) ->
    (id <> 0 -> ExecF.rng RNG id 38 /\
                ExecF.rng RNG ((id / 8 + ASAN_K) / 8 * 8)
                              (((id + 37) / 8 + ASAN_K) / 8 * 8 + 8 - (id / 8 + ASAN_K) / 8 * 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (msh m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 336, S + 365)] m msh /\ wmono rsegs m msh /\
         rw_cells rsegs msh (S + 336) (P3.p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) /\
         munch [(fb, fb + 35); (spv - REAC_IDENTITY_INIT_K, spv); (id, id + 38)] msh m' /\ wmono rsegs msh m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\
         rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)] /\
         rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RII RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23
    b24 b25 b26 b27 b28 idb fbj
    E2 E19 E27 E9 Hspv HSlo HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
    RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HRO
    Gsh Ga32 Gby Gimg Gstk Gfb Gshfb Gshs Gik Gikw Giks Girt Gid.
  assert (EL : LOWMEM_END = 2147450880) by reflexivity.
  assert (EH : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (ERT : RT_HI = 0xa9578) by reflexivity.
  pose proof (MN.mem_rel_normalize rsegs m HRO) as REL.
  eapply ExecF.evtF_mono.
  - eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (seg_rom rsegs) HRO).
    apply (p3_evt_F_on MSET RII RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             s11 t3 t4 t5 t6 F fc (MN.normalize rsegs m) spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
             b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 idb fbj E2 E19 E27 E9 Hspv
             ltac:(lia) ltac:(lia) ltac:(lia) HSHI ltac:(lia) Hid38 Hidm HSEPs ltac:(lia) HA40 HSEPa ltac:(lia)
             Hfb35 HSEPb HSEPfi
             (P3.p3_rw_rel m _ (S + 336) _ REL ltac:(lia) RWS) (P3.p3_rw_rel m _ id _ REL ltac:(lia) RWI)
             (P3.p3_rw_rel m _ (A + 32) _ REL ltac:(lia) RWA) (P3.p3_rw_rel m _ fb _ REL ltac:(lia) RWF)
             HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF
             (P3.p3_stk_rel m _ lo spv REL ltac:(lia) ltac:(lia) ST) HLO HHM HAE (P3.p3_cells_rel m _ REL HAC)
             (A.ShadowRwOnT.shadow_rw_on_rel _ m _ REL HSW) (MN.mem_inv_normalize rsegs m)
             Gsh Ga32 Gby Gimg Gstk Gfb Gshfb Gshs Gik Gikw Giks Girt Gid).
  - intros s (s0' & (R & msh0 & m0' & -> & P2 & P3' & P4 & P8 & P9 & P19 & P26 & P22 & P25 & MU1 & WM1 & RWS1 &
               MU2 & WM2 & _ & ST2 & _ & _ & RWF2 & RW2) & MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    assert (RELsh : MN.mem_rel rsegs (P3.p3_lift m msh0) msh0).
    { split.
      - intros a. unfold MN.normalize, P3.p3_lift.
        destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr rsegs a) eqn:E; [|reflexivity].
        rewrite (MU1 a).
        + unfold MN.normalize. rewrite E. reflexivity.
        + pose proof (Tac_b5.sl_ro_lo a E) as Ha. cbn [outside]. split; [lia | exact I].
      - intros a b E Hb. unfold P3.p3_lift in Hb. rewrite E in Hb. exact (proj2 REL a b E Hb). }
    assert (ROsh : MN.ro_same rsegs m (P3.p3_lift m msh0)).
    { intros a E. unfold P3.p3_lift. rewrite E. reflexivity. }
    assert (RO2 : MN.ro_same rsegs (P3.p3_lift m msh0) ms).
    { intros a E. rewrite (RS a E). unfold P3.p3_lift. rewrite E. reflexivity. }
    exists R, (P3.p3_lift m msh0), ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3'|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P22|]. split; [exact P25|].
    split; [exact (MN.munch_rel rsegs _ m _ _ msh0 REL RELsh ROsh MU1)|].
    split; [exact (MN.wmono_rel rsegs m _ _ msh0 REL RELsh ROsh WM1)|].
    split; [exact (P3.p3_rw_back _ msh0 (S + 336) _ RELsh ltac:(lia) RWS1)|].
    split; [exact (MN.munch_rel rsegs _ _ msh0 ms m0' RELsh Hmem RO2 MU2)|].
    split; [exact (MN.wmono_rel rsegs _ msh0 ms m0' RELsh Hmem RO2 WM2)|].
    split; [exact (MN.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (P3.p3_stk_back ms m0' lo spv Hmem ltac:(lia) ltac:(lia) ST2)|].
    split; [exact (P3.p3_rw_back ms m0' fb _ Hmem ltac:(lia) RWF2) |].
    exact (P3.p3_rw_back ms m0' id _ Hmem ltac:(lia) RW2).
Qed.

(* P3.p3_evt_ro's conclusion under the two footprint contracts, by p3_evt_ro_F at ExecF.RNG_all. Its two ro_agree
   are lib.A.MemNorm's by full path, as P3.p3_evt_ro's statement writes them, so the constr_eq pin
   p3_evt_ro_of_F_verbatim compares the same constant whether or not BzBridge also loads the root lib.MemNorm. *)
Lemma p3_evt_ro_of_F : asan_memset_contract_F -> reac_identity_init_contract_F ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv S id lo A fb : Z)
         (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27
          b28 : byte) (idb fbj : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 S -> s11 = Z_to_bv 64 id -> s1 = Z_to_bv 64 A ->
    0 <= spv < 2 ^ 64 -> LOWMEM_END <= S -> S + 365 <= HIGHMEM_BEG ->
    0x5fe000 <= id -> id + 38 <= 2 ^ 64 -> id mod 2 = 0 ->
    (id + 38 <= S + 336 \/ S + 365 <= id) ->
    0x5fe000 <= A -> A + 40 <= 2 ^ 64 -> (A + 40 <= S + 336 \/ S + 365 <= A + 32) ->
    0x5fe000 <= fb -> fb + 35 <= 2 ^ 64 -> (fb + 35 <= S + 336 \/ S + 365 <= fb) ->
    (fb + 35 <= id \/ id + 38 <= fb) ->
    rw_cells rsegs m (S + 336) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9;
                                C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15; C1 b16; C1 b17; C1 b18; C1 b19;
                                C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28] ->
    rw_cells rsegs m id [CB 38 idb] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 fb)] ->
    rw_cells rsegs m fb [CB 35 fbj] ->
    (forall m', bytes_at rsegs m' (S + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
       addressable m' id 38) ->
    (forall m', bytes_at rsegs m' (S + 360) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 3] ->
       addressable m' fb 35) ->
    end_in_app id 38 -> (id + 38 <= RT_LO \/ RT_HI <= id) ->
    (id + 38 <= spv - REAC_IDENTITY_INIT_K \/ spv <= id) ->
    end_in_app fb 35 -> app_mem (fb + 7) -> (fb + 35 <= RT_LO \/ RT_HI <= fb) ->
    (fb + 35 <= spv - REAC_IDENTITY_INIT_K \/ spv <= fb) ->
    stk rsegs m lo spv -> lo + REAC_IDENTITY_INIT_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (msh m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b80) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 336, S + 365)] m msh /\ wmono rsegs m msh /\
         rw_cells rsegs msh (S + 336) (P3.p3_shc b5 b6 b7 b8 b9 b19 b20 b21 b22 b23) /\
         munch [(fb, fb + 35); (spv - REAC_IDENTITY_INIT_K, spv); (id, id + 38)] msh m' /\ wmono rsegs msh m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\
         rw_cells rsegs m' fb [CB 35 (repeat (Z_to_bv 8 0) 35)] /\
         rw_cells rsegs m' id [CB 38 (repeat (Z_to_bv 8 0) 38)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RII ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23
    b24 b25 b26 b27 b28 idb fbj
    E2 E19 E27 E9 Hspv HSlo HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
    RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HRO.
  assert (HFBa : fb + 35 <= APPMEM_END).
  { destruct HEF as [HEF0 | HEF1]; [lia|].
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HEF1 |- *. lia. }
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (p3_evt_ro_F MSET RII ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
           s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m spv S id lo A fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
           b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 idb fbj
           E2 E19 E27 E9 Hspv HSlo HSHI Hid0 Hid38 Hidm HSEPs HA0 HA40 HSEPa Hfb0 Hfb35 HSEPb HSEPfi
           RWS RWI RWA RWF HADDR HADDRf HEI HRTI HSTI HEF HF7 HRTF HSTF ST HLO HHM HAE HAC HSW HRO).
  - apply ExecF.rng_all; unfold LOWMEM_END, HIGHMEM_BEG in *; lia.
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; unfold ASAN_MEMSET_K, REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply ExecF.rng_all; lia.
  - apply sh_word_rng_all; lia.
  - apply sh_word_rng_all;
      unfold ASAN_MEMSET_K, REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply ExecF.rng_all; unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply sh_word_rng_all; unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply ExecF.rng_all;
      unfold REAC_IDENTITY_INIT_K, HIGHMEM_BEG, APPMEM_END, ASAN_K in *; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; unfold RT_LO, RT_HI; lia.
  - intros _. split.
    + apply ExecF.rng_all; lia.
    + apply ExecF.rng_all; unfold ASAN_K in *; Z.div_mod_to_equations; lia.
Qed.

Example p3_evt_ro_of_F_verbatim : True.
Proof.
  lazymatch type of P3.p3_evt_ro with ?P -> ?P2 -> ?A =>
    constr_eq P asan_memset_contract; constr_eq P2 reac_identity_init_contract;
    lazymatch type of p3_evt_ro_of_F with ?Q -> ?Q2 -> ?B =>
      constr_eq Q asan_memset_contract_F; constr_eq Q2 reac_identity_init_contract_F; constr_eq A B
    end
  end.
  exact I.
Qed.

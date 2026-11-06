(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 1068 of its 1186 lines of code are new or changed and 1084 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F23.v; 463 of its 632 lines of code are new or changed and 1017 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F23.v 39b3fcab64e4 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f23_evt_of_F re-derives F23.f23_evt at ExecF.RNG_all; f23_evt_of_F_verbatim checks by constr_eq that
   its type is the type of F23.f23_evt. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint twin of Seg/F23.v's one evt run lemma (segment F23 = 0x825a0-0x825c8, the call of
   checked_memcpy at 0x825c4):
   - f23_evt_F: F23.f23_evt (:607) as an ExecF.evtF under a footprint RNG. The segment's own data accesses are
     the two shadow stores `sb zero,16(s3)` / `sb a0,17(s3)` at S(fr) + 16 and S(fr) + 17, which the lemma's
     own s3 = Z_to_bv 64 Sf premise names as [Sf + 16, Sf + 18), and the 8-byte load `ld s4,136(s1)` of the
     ports pointer, which its own premise `q64 m (A + 136) (fr + 128)` names as [A + 136, A + 144): two rng
     premises. The callee enters through its footprint contract asan_memcpy_contract_F
     (lib/A/Prog/asan_memcpy_cF.v, proved by asan_memcpyF.v asan_memcpy_holds_F) in the place of F23's
     Section Hypothesis MCPY (:394, plain asan_memcpy_contract); the callee's own footprint premises are that
     contract's, passed through unchanged (rng_bytes, the image range [IMG_LO, IMG_HI), the callee window
     [sp - ASAN_MEMCPY_K, sp), the destination [fr + 128, fr + 140) and the image source [PORTSC, PORTSC + 12),
     and the 8-aligned shadow word spans of those two buffers and of the callee window).
     The call runs on the normalized memory, as F23.f23_evt does (MemNorm.evt_normalize there,
     MemNormF.evtF_normalize_ro here); the footprint RNG is the same on both sides.
   F23.f23_run_lib (:356) is NOT re-run: it concludes SR, not evt, so it is out of the spec's scope
   (a Theorem Labs lane, 2026-10-28); it stays plain and the ported walk reaches it through the twin above.
   F23.v itself is unchanged apart from comments; its seg_F23 still goes through F23.f23_evt.
   rule 24: no function proved (a mechanical re-run of an already-proved segment run). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_cF asan_memcpyF.
(* route (C) (f23_evt_F_on / f23_evt_of_F_on): the copy's region-restricted contracts and proof (a Theorem Labs lane
   83ab88c3325, taken by path), the form (lib/A/ShadowRwOn.v, ShadowRwOnT.v; a Theorem Labs lane 9ec78006def) and MemMono's
   rd_mono for the two shadow stores *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_c_on asan_memcpy_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.Prog.MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_memcpyF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs B7Cuts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F23.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* Last: StepF's step / if_true_by (evtF goals) shadow Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
(* The core copy an _F statement names (a Theorem Labs lane 08:56Z rule): LMS (lib.Lib's MState). *)
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

(* The segment's addresses reach solve_accs as bv_unsigned (Z_to_bv 64 Sf) + 16 / + 17 and
   bv_unsigned (Z_to_bv 64 A) + 136, which its syntactic matching does not relate to the premises
   [ExecF.rng RNG (Sf + 16) 2] / [ExecF.rng RNG (A + 136) 8]; close such a goal from any rng hypothesis after
   normalizing bv_unsigned (Z_to_bv 64 _). (The v1.8 Seg/R8F.v's r8_accF, unchanged.) *)
Ltac f23_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | H : rng RNG ?lo ?len |- _ =>
          apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz));
          cbv [wa]; rewrite ?LMS.unsigned_lit_wrap; Z.div_mod_to_equations; lia
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= f23_accF.

(* ---- the ten instructions 0x825a0-0x825c4 under a footprint RNG, the copy on its footprint contract ---- *)
Lemma f23_evt_F : forall (RNG : ExecF.footprint),
  asan_memcpy_contract_F ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (spv A fr Sf : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sf -> a0 = s4 -> Sf = Sfr fr ->
    0 <= fr -> fr mod 8 = 0 -> AC.GT <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spv - 2224 \/ spv <= fr) ->
    fr + FRAME_BYTES <= A -> spv <= A -> A + 312 <= 2 ^ 64 ->
    HIGHMEM_BEG + FN_STACK <= spv -> spv <= APPMEM_END ->
    0 <= Sf -> Sf + FRAME_SHADOW <= HIGHMEM_BEG -> (fr + FRAME_BYTES <= Sf \/ Sf + FRAME_SHADOW <= fr) ->
    q64 m (A + 136) (fr + 128) ->
    rw_cells rsegs m (fr + 128) [CB 12 junk] ->
    addressable m F23.PORTSC 12 ->
    asan_cells m -> shadow_rw m -> ro_agree rsegs m -> stk rsegs m (spv - FN_STACK) spv ->
    (* the segment's own accesses: the two shadow stores and the ports-pointer load *)
    ExecF.rng RNG (Sf + 16) 2 ->
    ExecF.rng RNG (A + 136) 8 ->
    (* the callee's regions (asan_memcpy_contract_F's footprint premises), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    ExecF.rng RNG (fr + 128) 12 -> ExecF.rng RNG F23.PORTSC 12 ->
    sh_word_rng RNG (fr + 128) 12 -> sh_word_rng RNG F23.PORTSC 12 ->
    sh_word_rng RNG (spv - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x825c8) fcs None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 20 = Z_to_bv 64 (fr + 128) /\
         munch [(spv - 2224, spv); (fr + 128, fr + 140); (Sf + 16, Sf + 18)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m' /\
         stk rsegs m' (spv - FN_STACK) spv /\
         bytes_at rsegs m' (fr + 128) F23.ports_c_bytes /\ addressable m' (fr + 128) 12)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x825a0) fcs None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros RNG MCPY ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcs m spv A fr Sf junk Esp Es1 Es3 Ea0 ESf Hfr0 Hfr8 HGT Hfrend Happ Hfrw HfrA HspA HAhi Hsplo Hspend
    HSf0 HSfhi HSfap Hq136 RWq HADimg HAC HSW HRO HST
    RSh R136 Rby Rimg Rstk RngD RngS RngDs RngSs RngKs.
  subst sp s1 s3 a0.
  unfold asan_memcpy_contract_F in MCPY.
  unfold AC.GT in HGT.
  assert (KAPP : APPMEM_END = 0x800000000000) by reflexivity.
  assert (KHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (KLM : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (KSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (KFN : FN_STACK = 1044480) by reflexivity.
  assert (KMC : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (Hspb : 0 <= spv < 2 ^ 64) by (unfold HIGHMEM_BEG, AF.SLOT_STACK, APPMEM_END in *; lia).
  assert (HAb : 0 <= A < 2 ^ 64) by (unfold HIGHMEM_BEG, AF.SLOT_STACK in *; lia).
  assert (HSfb : 0 <= Sf /\ Sf + 18 <= 2 ^ 64) by (unfold HIGHMEM_BEG in *; lia).
  assert (HSfK : 2147450880 <= Sf).
  { rewrite ESf. unfold Sfr, shadow_addr, ASAN_K.
    assert (0 <= fr / 8) by (apply Z.div_pos; lia). lia. }
  assert (HSH16 : in_shadow (Sf + 16)) by (rewrite ESf; exact (F23.f23_fr_shadow fr 16 ltac:(lia) Happ)).
  assert (HSH17 : in_shadow (Sf + 17)) by (rewrite ESf; exact (F23.f23_fr_shadow fr 17 ltac:(lia) Happ)).
  assert (HS16 : store_ok rsegs m (wa (Sf + 16)) 1 = true)
    by (eapply F23.f23_store_ok1; [exact (proj1 (HSW _ HSH16)) | apply wmono_refl | lia | lia]).
  (* 0x825a0 bne a0,s4: the call's result and s4 are the same word, the branch is not taken *)
  step.
  rewrite F23.f23_bne_same. cbv iota.
  (* 0x825a4 sb zero,16(s3) *)
  step.
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HS17 : store_ok rsegs mm (wa (Sf + 17)) 1 = true)
        by (eapply (F23.f23_store_ok1 m); [exact (proj1 (HSW _ HSH17)) | apply wmono_write; apply wmono_refl
                                          | lia | lia])
  end.
  (* 0x825a8 li a0,4 ; 0x825ac sb a0,17(s3) *)
  step. step.
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem (write_to_mem _ _ ?bA) _ ?bB) _) =>
      assert (EA : bA = [Z_to_bv 8 0]) by (vm_compute; reflexivity);
      assert (EB : bB = [Z_to_bv 8 4]) by (vm_compute; reflexivity);
      try rewrite EA; try rewrite EB
  end.
  set (m2 := write_to_mem (write_to_mem m (Z_to_bv 64 (Sf + 16)) [Z_to_bv 8 0])
               (Z_to_bv 64 (Sf + 17)) [Z_to_bv 8 4]).
  (* the two shadow bytes of m2 *)
  assert (HB16 : bytes_at rsegs m2 (Sf + 16) [Z_to_bv 8 0]).
  { unfold m2. apply bytes_at_write_other; [apply bytes_at_write_same; cbn; lia | lia | cbn; lia | cbn; lia]. }
  assert (HB17 : bytes_at rsegs m2 (Sf + 17) [Z_to_bv 8 4]).
  { unfold m2. apply bytes_at_write_same; cbn; lia. }
  assert (HM16 : mrd rsegs m2 (wa (Sf + 16)) = Some (Z_to_bv 8 0)).
  { destruct HB16 as (_ & _ & HH). pose proof (HH 0%nat ltac:(cbn; lia)) as HE.
    cbn [Z.of_nat nth_error] in HE. rewrite Z.add_0_r in HE. exact HE. }
  assert (HM17 : mrd rsegs m2 (wa (Sf + 17)) = Some (Z_to_bv 8 4)).
  { destruct HB17 as (_ & _ & HH). pose proof (HH 0%nat ltac:(cbn; lia)) as HE.
    cbn [Z.of_nat nth_error] in HE. rewrite Z.add_0_r in HE. exact HE. }
  (* the memory facts of m2 *)
  assert (MU2 : munch [(Sf + 16, Sf + 18)] m m2).
  { unfold m2. apply munch_write; [|lia|cbn; lia|cbn; lia].
    apply munch_write; [apply munch_refl | lia | cbn; lia | cbn; lia]. }
  assert (WM2 : wmono rsegs m m2)
    by (unfold m2; apply wmono_write; apply wmono_write; apply wmono_refl).
  assert (RO2 : ro_agree rsegs m2).
  { unfold m2. apply F23.f23_ro_agree_write1; [apply F23.f23_ro_agree_write1; [exact HRO | lia] | lia]. }
  assert (SW2 : shadow_rw m2).
  { unfold m2. apply F23.f23_shadow_rw_write;
      [apply F23.f23_shadow_rw_write; [exact HSW | lia | cbn; lia] | lia | cbn; lia]. }
  assert (AC2 : asan_cells m2).
  { apply (asan_cells_kept [(Sf + 16, Sf + 18)] m m2 HAC MU2).
    cbn [disjoint_from]. split; [|exact I]. unfold RT_LO, RT_HI. lia. }
  assert (ST2 : stk rsegs m2 (spv - FN_STACK) spv).
  { apply (stk_transport_disjoint rsegs [(Sf + 16, Sf + 18)] m m2 _ _ HST MU2 WM2).
    cbn [disjoint_from]. split; [|exact I]. unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
  assert (AD2 : addressable m2 (fr + 128) 12).
  { apply (F23.f23_addr12 m2 fr Hfr8 Hfr0 Hfrend Happ); rewrite <- ESf; assumption. }
  assert (ADS2 : addressable m2 F23.PORTSC 12).
  { apply (F23.f23_addr_keep m m2 [(Sf + 16, Sf + 18)] F23.PORTSC 12 HADimg MU2).
    intros i Hi. cbn [outside]. split; [|exact I].
    assert (Hd : (F23.PORTSC + i) / 8 <= 16946)
      by (apply Z.div_le_upper_bound; unfold F23.PORTSC; lia).
    assert (Hfd : 785408 <= fr / 8)
      by (replace 785408 with (6283264 / 8) by reflexivity; apply Z.div_le_mono; lia).
    rewrite ESf. unfold Sfr, shadow_addr. lia. }
  assert (RW2 : rw_cells rsegs m2 (fr + 128) [CB 12 junk]).
  { unfold m2.
    apply rw_cells_frame;
      [ apply rw_cells_frame;
          [ exact RWq | lia | cbn; lia | cbn; lia ]
      | lia | cbn; lia | cbn; lia ]. }
  assert (RO136 : ro_cells rsegs m2 (A + 136) [C8 (Z_to_bv 64 (fr + 128))]).
  { apply ro_c8. unfold q64 in Hq136. unfold m2.
    apply bytes_at_write_other;
      [ apply bytes_at_write_other;
          [ exact Hq136 | lia | cbn; lia | rewrite length_le8; cbn; unfold HIGHMEM_BEG in *; lia ]
      | lia | cbn; lia | rewrite length_le8; cbn; unfold HIGHMEM_BEG in *; lia ]. }
  (* 0x825b0 auipc ; 0x825b4 addi a1 ; 0x825b8 li a2,12 ; 0x825bc ld s4,136(s1) ; 0x825c0 mv a0,s4 ; 0x825c4 jal *)
  step. step. step. step.
  step. step.
  (* the copy, on its footprint contract, run on the normalized memory: the contract asks for mem_inv, which the
     frame does not carry; every premise and every conclusion crosses mem_rel (MemNorm) *)
  pose proof (mem_rel_normalize rsegs m2 RO2) as REL2.
  eapply ExecF.evtF_cut.
  { eapply MNF.evtF_normalize_ro; [exact RO2|].
    eapply MCPY with (RNG := RNG) (src := F23.ports_c_bytes) (junk := junk) (lo := spv - FN_STACK).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      exact (F23.f23_src_bytes _ (mem_inv_normalize rsegs m2)).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      rewrite F23.f23_ports_len. reflexivity.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      exact (F23.f23_rw_cells_rel m2 _ (fr + 128) _ REL2 ltac:(lia) RW2).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      unfold F23.PORTSC. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      exact (F23.f23_addressable_rel m2 _ F23.PORTSC 12 REL2 ADS2).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      exact (F23.f23_addressable_rel m2 _ (fr + 128) 12 REL2 AD2).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      unfold end_in_app, app_mem, F23.PORTSC, LOWMEM_END. right. left. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. unfold end_in_app.
      right. apply Happ. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      right. split.
      + unfold app_mem, F23.PORTSC, LOWMEM_END. left. lia.
      + apply Happ. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. unfold RT_LO, RT_HI.
      lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      unfold F23.PORTSC, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      exact (F23.f23_stk_rel_hi m2 _ (spv - FN_STACK) spv REL2 ltac:(lia) ltac:(lia) ST2).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - exact (F23.f23_asan_cells_rel m2 _ REL2 AC2).
    - exact (F23.f23_shadow_rw_rel m2 _ REL2 SW2).
    - exact (mem_inv_normalize rsegs m2).
    - exact Rby.
    - exact Rimg.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Rstk.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngD.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      exact RngS.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngDs.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      exact RngSs.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngKs. }
  intros ms' PO. destruct PO as (st0 & PO & REL & SAME).
  unfold asan_memcpy_post in PO.
  destruct PO as (u0 & u1 & u2 & b1' & b2' & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m3n &
                  E3 & MU3 & WM3 & MI3 & ST3 & RW3 & HBS3 & AC3 & SW3).
  subst st0.
  destruct REL as (ER & EF & EPC & ESV & ERV & EFC & EROM & R8).
  destruct ms' as [R' F' pc' svc' rv' fc' m3 ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in ER, EF, EPC, ESV, ERV, EFC, EROM, R8, SAME |- *.
  subst R' F' pc' svc' rv' fc' ro'.
  rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in ST3, RW3, HBS3 by lia.
  assert (MU3nn : munch [(fr + 128, fr + 140); (spv - 2224, spv)] (normalize rsegs m2) m3n).
  { intros x Hx. apply MU3. cbn [outside] in Hx |- *. destruct Hx as (HO1 & HO2 & _).
    rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
    split; [intros [Q1 Q2]; apply HO1; lia|]. split; [intros [Q1 Q2]; apply HO2; lia | exact I]. }
  assert (MU3n : munch [(fr + 128, fr + 140); (spv - 2224, spv)] m2 m3)
    by (eapply munch_rel; [exact REL2 | exact R8 | exact SAME | exact MU3nn]).
  assert (WM3r : wmono rsegs m2 m3)
    by (eapply wmono_rel; [exact REL2 | exact R8 | exact SAME | exact WM3]).
  replace (ret_pc (Z_to_bv 64 0x825c8)) with (Z_to_bv 64 0x825c8)
    by (symmetry; apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  (* munch, wmono *)
  assert (MUa : munch [(spv - 2224, spv); (fr + 128, fr + 140); (Sf + 16, Sf + 18)] m m2).
  { eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & _).
    split; [exact H3 | exact I]. }
  assert (MUb : munch [(spv - 2224, spv); (fr + 128, fr + 140); (Sf + 16, Sf + 18)] m2 m3).
  { eapply munch_weaken; [|exact MU3n]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & _).
    split; [intros [Q1 Q2]; apply H2; lia|]. split; [intros [Q1 Q2]; apply H1; lia | exact I]. }
  split; [exact (munch_trans _ _ _ _ MUa MUb)|].
  split; [exact (wmono_trans rsegs _ _ _ WM2 WM3r)|].
  split; [exact (ro_agree_same rsegs m2 m3 RO2 SAME)|].
  split; [exact (F23.f23_shadow_rw_rel_back m3 m3n R8 SW3)|].
  split; [exact (F23.f23_stk_rel_hi_back m3 m3n (spv - FN_STACK) spv R8 ltac:(lia) ltac:(lia) ST3)|].
  split.
  { destruct RW3 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    exact (proj2 (bytes_at_rel rsegs m3 m3n (fr + 128) F23.ports_c_bytes R8) HB). }
  { apply (F23.f23_addr_keep m2 m3 _ (fr + 128) 12 AD2 MU3n).
    intros i Hi. cbn [outside].
    assert (Hap : app_mem (fr + 128 + i)) by (apply Happ; lia).
    pose proof (shadow_of_app _ Hap) as Hsh.
    pose proof (Happ (fr + 128) ltac:(lia)) as Hap0.
    pose proof (Happ (fr + 139) ltac:(lia)) as Hap1.
    unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END,
      AF.SLOT_STACK in *.
    split; [lia|]. split; [lia | exact I]. }
Qed.

(* F23.f23_evt's statement, term for term: f23_evt_F at ExecF.RNG_all, with the footprint contract discharged by
   a Theorem Labs lane's proof asan_memcpy_holds_F (lib/A/Prog/asan_memcpyF.v), so that the plain asan_memcpy_contract
   premise F23's Section Hypothesis MCPY left on f23_evt is kept in its place and used by nothing. *)
Lemma f23_evt_of_F : asan_memcpy_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (spv A fr Sf : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sf -> a0 = s4 -> Sf = Sfr fr ->
    0 <= fr -> fr mod 8 = 0 -> AC.GT <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spv - 2224 \/ spv <= fr) ->
    fr + FRAME_BYTES <= A -> spv <= A -> A + 312 <= 2 ^ 64 ->
    HIGHMEM_BEG + FN_STACK <= spv -> spv <= APPMEM_END ->
    0 <= Sf -> Sf + FRAME_SHADOW <= HIGHMEM_BEG -> (fr + FRAME_BYTES <= Sf \/ Sf + FRAME_SHADOW <= fr) ->
    q64 m (A + 136) (fr + 128) ->
    rw_cells rsegs m (fr + 128) [CB 12 junk] ->
    addressable m F23.PORTSC 12 ->
    asan_cells m -> shadow_rw m -> ro_agree rsegs m -> stk rsegs m (spv - FN_STACK) spv ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x825c8) fcs None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 20 = Z_to_bv 64 (fr + 128) /\
         munch [(spv - 2224, spv); (fr + 128, fr + 140); (Sf + 16, Sf + 18)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m' /\
         stk rsegs m' (spv - FN_STACK) spv /\
         bytes_at rsegs m' (fr + 128) F23.ports_c_bytes /\ addressable m' (fr + 128) 12)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x825a0) fcs None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros _ ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcs m spv A fr Sf junk Esp Es1 Es3 Ea0 ESf Hfr0 Hfr8 HGT Hfrend Happ Hfrw HfrA HspA HAhi Hsplo Hspend
    HSf0 HSfhi HSfap Hq136 RWq HADimg HAC HSW HRO HST.
  pose proof two64 as H64.
  assert (KAPP : APPMEM_END = 0x800000000000) by reflexivity.
  assert (KHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (KFN : FN_STACK = 1044480) by reflexivity.
  assert (KMC : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (KIL : IMG_LO = 65536) by reflexivity.
  assert (KIH : IMG_HI = 6283264) by reflexivity.
  assert (KPO : F23.PORTSC = 135552) by reflexivity.
  assert (KGT : AC.GT = 6283264) by reflexivity.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f23_evt_F ExecF.RNG_all asan_memcpy_holds_F
           ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           Fr fcs m spv A fr Sf junk Esp Es1 Es3 Ea0 ESf Hfr0 Hfr8 HGT Hfrend Happ Hfrw
           HfrA HspA HAhi Hsplo Hspend HSf0 HSfhi HSfap Hq136 RWq HADimg HAC HSW HRO HST).
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply sh_word_rng_all; lia.
  - apply sh_word_rng_all; lia.
  - apply sh_word_rng_all; lia.
Qed.

(* The pin: f23_evt_of_F states F23's v1.9 text, term for term (constr_eq: syntactic, not up to conversion),
   the plain asan_memcpy_contract premise of the Section Hypothesis included. *)
Lemma f23_evt_of_F_verbatim : True.
Proof.
  let A := type of F23.f23_evt in let B := type of f23_evt_of_F in constr_eq A B; exact I.
Qed.

(* ---- Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery), 10:34Z amendment): ADDITIVE twins
   of f23_evt_F and f23_evt_of_F.  Both old lemmas stay byte-identical with their own proofs (a Theorem Labs lane 09:58Z: a run that
   takes a callee contract keeps X); the twins take the copy's region-restricted contracts. ----
   R (the shadow bytes the run reads or stores through its shadow_rw premise HSW), from HSW's uses in f23_evt_F:
     - Sf + 16 <= a < Sf + 18: the two shadow stores 0x825a4 sb zero,16(s3) and 0x825ac sb a0,17(s3) need the bytes
       writable (HS16 / HS17: `proj1 (HSW _ HSH16)` / `proj1 (HSW _ HSH17)`); the run reads no shadow byte;
     - asan_memcpy_shadow_R at the call's arguments a0 = fr + 128 (0x825bc ld s4,136(s1), q64 premise), a1 = PORTSC
       (0x825b0 auipc / addi), a2 = 12 (li a2,12): the copy's shadow premise (`F23.f23_shadow_rw_rel m2 _ REL2 SW2`,
       SW2 from HSW across the two stores by F23.f23_shadow_rw_write).
   The third use (`F23.f23_shadow_rw_rel_back m3 m3n R8 SW3`, the post's shadow_rw m') becomes the forall-P post and
   needs no byte. The copy's own stack shadow is a footprint premise (sh_word_rng), not read through shadow_rw by
   asan_memcpy_contract_F_on, so it is not in R. The same region as F23.v's plain twin f23_evt_on (a Theorem Labs lane,
   F23.v (a version not in this delivery; from a working branch f556cbc34ed) f23_evt_shadow_R), stated here for the footprint twin. Transports: the stores by
   ShadowRwOnT.shadow_rw_on_mem_mono (MemMono.rd_mono_write), normalize by ShadowRwOnT.shadow_rw_on_rel, back by
   ShadowRwOnT.shadow_rw_on_of_rel. *)
Definition f23_evt_F_shadow_R (fr Sf a : Z) : Prop :=
  (Sf + 16 <= a < Sf + 18) \/
  asan_memcpy_shadow_R (Z_to_bv 64 (fr + 128)) (Z_to_bv 64 F23.PORTSC) (Z_to_bv 64 12) a.

Lemma f23_evt_F_on : forall (RNG : ExecF.footprint),
  asan_memcpy_contract_F_on ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (spv A fr Sf : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sf -> a0 = s4 -> Sf = Sfr fr ->
    0 <= fr -> fr mod 8 = 0 -> AC.GT <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spv - 2224 \/ spv <= fr) ->
    fr + FRAME_BYTES <= A -> spv <= A -> A + 312 <= 2 ^ 64 ->
    HIGHMEM_BEG + FN_STACK <= spv -> spv <= APPMEM_END ->
    0 <= Sf -> Sf + FRAME_SHADOW <= HIGHMEM_BEG -> (fr + FRAME_BYTES <= Sf \/ Sf + FRAME_SHADOW <= fr) ->
    q64 m (A + 136) (fr + 128) ->
    rw_cells rsegs m (fr + 128) [CB 12 junk] ->
    addressable m F23.PORTSC 12 ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (f23_evt_F_shadow_R fr Sf) m -> ro_agree rsegs m ->
    stk rsegs m (spv - FN_STACK) spv ->
    (* the segment's own accesses: the two shadow stores and the ports-pointer load *)
    ExecF.rng RNG (Sf + 16) 2 ->
    ExecF.rng RNG (A + 136) 8 ->
    (* the callee's regions (asan_memcpy_contract_F_on's footprint premises), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    ExecF.rng RNG (fr + 128) 12 -> ExecF.rng RNG F23.PORTSC 12 ->
    sh_word_rng RNG (fr + 128) 12 -> sh_word_rng RNG F23.PORTSC 12 ->
    sh_word_rng RNG (spv - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x825c8) fcs None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 20 = Z_to_bv 64 (fr + 128) /\
         munch [(spv - 2224, spv); (fr + 128, fr + 140); (Sf + 16, Sf + 18)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         stk rsegs m' (spv - FN_STACK) spv /\
         bytes_at rsegs m' (fr + 128) F23.ports_c_bytes /\ addressable m' (fr + 128) 12)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x825a0) fcs None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros RNG MCPY ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcs m spv A fr Sf junk Esp Es1 Es3 Ea0 ESf Hfr0 Hfr8 HGT Hfrend Happ Hfrw HfrA HspA HAhi Hsplo Hspend
    HSf0 HSfhi HSfap Hq136 RWq HADimg HAC HSW HRO HST
    RSh R136 Rby Rimg Rstk RngD RngS RngDs RngSs RngKs.
  subst sp s1 s3 a0.
  unfold asan_memcpy_contract_F_on in MCPY.
  unfold AC.GT in HGT.
  assert (KAPP : APPMEM_END = 0x800000000000) by reflexivity.
  assert (KHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (KLM : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (KSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (KFN : FN_STACK = 1044480) by reflexivity.
  assert (KMC : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (Hspb : 0 <= spv < 2 ^ 64) by (unfold HIGHMEM_BEG, AF.SLOT_STACK, APPMEM_END in *; lia).
  assert (HAb : 0 <= A < 2 ^ 64) by (unfold HIGHMEM_BEG, AF.SLOT_STACK in *; lia).
  assert (HSfb : 0 <= Sf /\ Sf + 18 <= 2 ^ 64) by (unfold HIGHMEM_BEG in *; lia).
  assert (HSfK : 2147450880 <= Sf).
  { rewrite ESf. unfold Sfr, shadow_addr, ASAN_K.
    assert (0 <= fr / 8) by (apply Z.div_pos; lia). lia. }
  assert (HSH16 : in_shadow (Sf + 16)) by (rewrite ESf; exact (F23.f23_fr_shadow fr 16 ltac:(lia) Happ)).
  assert (HSH17 : in_shadow (Sf + 17)) by (rewrite ESf; exact (F23.f23_fr_shadow fr 17 ltac:(lia) Happ)).
  assert (HR16 : f23_evt_F_shadow_R fr Sf (Sf + 16)) by (left; lia).
  assert (HR17 : f23_evt_F_shadow_R fr Sf (Sf + 17)) by (left; lia).
  assert (HS16 : store_ok rsegs m (wa (Sf + 16)) 1 = true)
    by (eapply F23.f23_store_ok1; [exact (proj1 (HSW _ HR16 HSH16)) | apply wmono_refl | lia | lia]).
  (* 0x825a0 bne a0,s4: the call's result and s4 are the same word, the branch is not taken *)
  step.
  rewrite F23.f23_bne_same. cbv iota.
  (* 0x825a4 sb zero,16(s3) *)
  step.
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HS17 : store_ok rsegs mm (wa (Sf + 17)) 1 = true)
        by (eapply (F23.f23_store_ok1 m); [exact (proj1 (HSW _ HR17 HSH17)) | apply wmono_write; apply wmono_refl
                                          | lia | lia])
  end.
  (* 0x825a8 li a0,4 ; 0x825ac sb a0,17(s3) *)
  step. step.
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem (write_to_mem _ _ ?bA) _ ?bB) _) =>
      assert (EA : bA = [Z_to_bv 8 0]) by (vm_compute; reflexivity);
      assert (EB : bB = [Z_to_bv 8 4]) by (vm_compute; reflexivity);
      try rewrite EA; try rewrite EB
  end.
  set (m2 := write_to_mem (write_to_mem m (Z_to_bv 64 (Sf + 16)) [Z_to_bv 8 0])
               (Z_to_bv 64 (Sf + 17)) [Z_to_bv 8 4]).
  (* the two shadow bytes of m2 *)
  assert (HB16 : bytes_at rsegs m2 (Sf + 16) [Z_to_bv 8 0]).
  { unfold m2. apply bytes_at_write_other; [apply bytes_at_write_same; cbn; lia | lia | cbn; lia | cbn; lia]. }
  assert (HB17 : bytes_at rsegs m2 (Sf + 17) [Z_to_bv 8 4]).
  { unfold m2. apply bytes_at_write_same; cbn; lia. }
  assert (HM16 : mrd rsegs m2 (wa (Sf + 16)) = Some (Z_to_bv 8 0)).
  { destruct HB16 as (_ & _ & HH). pose proof (HH 0%nat ltac:(cbn; lia)) as HE.
    cbn [Z.of_nat nth_error] in HE. rewrite Z.add_0_r in HE. exact HE. }
  assert (HM17 : mrd rsegs m2 (wa (Sf + 17)) = Some (Z_to_bv 8 4)).
  { destruct HB17 as (_ & _ & HH). pose proof (HH 0%nat ltac:(cbn; lia)) as HE.
    cbn [Z.of_nat nth_error] in HE. rewrite Z.add_0_r in HE. exact HE. }
  (* the memory facts of m2 *)
  assert (MU2 : munch [(Sf + 16, Sf + 18)] m m2).
  { unfold m2. apply munch_write; [|lia|cbn; lia|cbn; lia].
    apply munch_write; [apply munch_refl | lia | cbn; lia | cbn; lia]. }
  assert (WM2 : wmono rsegs m m2)
    by (unfold m2; apply wmono_write; apply wmono_write; apply wmono_refl).
  assert (RO2 : ro_agree rsegs m2).
  { unfold m2. apply F23.f23_ro_agree_write1; [apply F23.f23_ro_agree_write1; [exact HRO | lia] | lia]. }
  (* the two stores keep every shadow region present and writable (MemMono.rd_mono_write) *)
  assert (SW2 : forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m2).
  { intros P HP. apply (A.ShadowRwOnT.shadow_rw_on_mem_mono P m m2 HP WM2).
    unfold m2. apply A.Prog.MemMono.rd_mono_write, A.Prog.MemMono.rd_mono_write, A.Prog.MemMono.rd_mono_refl. }
  assert (AC2 : asan_cells m2).
  { apply (asan_cells_kept [(Sf + 16, Sf + 18)] m m2 HAC MU2).
    cbn [disjoint_from]. split; [|exact I]. unfold RT_LO, RT_HI. lia. }
  assert (ST2 : stk rsegs m2 (spv - FN_STACK) spv).
  { apply (stk_transport_disjoint rsegs [(Sf + 16, Sf + 18)] m m2 _ _ HST MU2 WM2).
    cbn [disjoint_from]. split; [|exact I]. unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
  assert (AD2 : addressable m2 (fr + 128) 12).
  { apply (F23.f23_addr12 m2 fr Hfr8 Hfr0 Hfrend Happ); rewrite <- ESf; assumption. }
  assert (ADS2 : addressable m2 F23.PORTSC 12).
  { apply (F23.f23_addr_keep m m2 [(Sf + 16, Sf + 18)] F23.PORTSC 12 HADimg MU2).
    intros i Hi. cbn [outside]. split; [|exact I].
    assert (Hd : (F23.PORTSC + i) / 8 <= 16946)
      by (apply Z.div_le_upper_bound; unfold F23.PORTSC; lia).
    assert (Hfd : 785408 <= fr / 8)
      by (replace 785408 with (6283264 / 8) by reflexivity; apply Z.div_le_mono; lia).
    rewrite ESf. unfold Sfr, shadow_addr. lia. }
  assert (RW2 : rw_cells rsegs m2 (fr + 128) [CB 12 junk]).
  { unfold m2.
    apply rw_cells_frame;
      [ apply rw_cells_frame;
          [ exact RWq | lia | cbn; lia | cbn; lia ]
      | lia | cbn; lia | cbn; lia ]. }
  assert (RO136 : ro_cells rsegs m2 (A + 136) [C8 (Z_to_bv 64 (fr + 128))]).
  { apply ro_c8. unfold q64 in Hq136. unfold m2.
    apply bytes_at_write_other;
      [ apply bytes_at_write_other;
          [ exact Hq136 | lia | cbn; lia | rewrite length_le8; cbn; unfold HIGHMEM_BEG in *; lia ]
      | lia | cbn; lia | rewrite length_le8; cbn; unfold HIGHMEM_BEG in *; lia ]. }
  (* 0x825b0 auipc ; 0x825b4 addi a1 ; 0x825b8 li a2,12 ; 0x825bc ld s4,136(s1) ; 0x825c0 mv a0,s4 ; 0x825c4 jal *)
  step. step. step. step.
  step. step.
  (* the copy, on its region-restricted footprint contract, run on the normalized memory (as f23_evt_F) *)
  pose proof (mem_rel_normalize rsegs m2 RO2) as REL2.
  eapply ExecF.evtF_cut.
  { eapply MNF.evtF_normalize_ro; [exact RO2|].
    eapply MCPY with (RNG := RNG) (src := F23.ports_c_bytes) (junk := junk) (lo := spv - FN_STACK).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      exact (F23.f23_src_bytes _ (mem_inv_normalize rsegs m2)).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      rewrite F23.f23_ports_len. reflexivity.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      exact (F23.f23_rw_cells_rel m2 _ (fr + 128) _ REL2 ltac:(lia) RW2).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      unfold F23.PORTSC. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      exact (F23.f23_addressable_rel m2 _ F23.PORTSC 12 REL2 ADS2).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      exact (F23.f23_addressable_rel m2 _ (fr + 128) 12 REL2 AD2).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      unfold end_in_app, app_mem, F23.PORTSC, LOWMEM_END. right. left. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. unfold end_in_app.
      right. apply Happ. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      right. split.
      + unfold app_mem, F23.PORTSC, LOWMEM_END. left. lia.
      + apply Happ. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. unfold RT_LO, RT_HI.
      lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      unfold F23.PORTSC, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      exact (F23.f23_stk_rel_hi m2 _ (spv - FN_STACK) spv REL2 ltac:(lia) ltac:(lia) ST2).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - exact (F23.f23_asan_cells_rel m2 _ REL2 AC2).
    - (* the copy's region is the second disjunct of f23_evt_F_shadow_R *)
      apply (A.ShadowRwOnT.shadow_rw_on_rel _ m2 _ REL2). apply SW2.
      apply (A.ShadowRwOn.shadow_rw_on_mono (f23_evt_F_shadow_R fr Sf) _ m); [|exact HSW].
      intros x Hx. right. unfold asan_memcpy_shadow_R in Hx |- *.
      rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in Hx
        by (try unfold F23.PORTSC; lia).
      rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit
        by (try unfold F23.PORTSC; lia).
      exact Hx.
    - exact (mem_inv_normalize rsegs m2).
    - exact Rby.
    - exact Rimg.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Rstk.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngD.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      exact RngS.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngDs.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      exact RngSs.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngKs. }
  intros ms' PO. destruct PO as (st0 & PO & REL & SAME).
  unfold asan_memcpy_post_on in PO.
  destruct PO as (u0 & u1 & u2 & b1' & b2' & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m3n &
                  E3 & MU3 & WM3 & MI3 & ST3 & RW3 & HBS3 & AC3 & SW3).
  subst st0.
  destruct REL as (ER & EF & EPC & ESV & ERV & EFC & EROM & R8).
  destruct ms' as [R' F' pc' svc' rv' fc' m3 ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in ER, EF, EPC, ESV, ERV, EFC, EROM, R8, SAME |- *.
  subst R' F' pc' svc' rv' fc' ro'.
  rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in ST3, RW3, HBS3 by lia.
  assert (MU3nn : munch [(fr + 128, fr + 140); (spv - 2224, spv)] (normalize rsegs m2) m3n).
  { intros x Hx. apply MU3. cbn [outside] in Hx |- *. destruct Hx as (HO1 & HO2 & _).
    rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
    split; [intros [Q1 Q2]; apply HO1; lia|]. split; [intros [Q1 Q2]; apply HO2; lia | exact I]. }
  assert (MU3n : munch [(fr + 128, fr + 140); (spv - 2224, spv)] m2 m3)
    by (eapply munch_rel; [exact REL2 | exact R8 | exact SAME | exact MU3nn]).
  assert (WM3r : wmono rsegs m2 m3)
    by (eapply wmono_rel; [exact REL2 | exact R8 | exact SAME | exact WM3]).
  replace (ret_pc (Z_to_bv 64 0x825c8)) with (Z_to_bv 64 0x825c8)
    by (symmetry; apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  (* munch, wmono *)
  assert (MUa : munch [(spv - 2224, spv); (fr + 128, fr + 140); (Sf + 16, Sf + 18)] m m2).
  { eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & _).
    split; [exact H3 | exact I]. }
  assert (MUb : munch [(spv - 2224, spv); (fr + 128, fr + 140); (Sf + 16, Sf + 18)] m2 m3).
  { eapply munch_weaken; [|exact MU3n]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & _).
    split; [intros [Q1 Q2]; apply H2; lia|]. split; [intros [Q1 Q2]; apply H1; lia | exact I]. }
  split; [exact (munch_trans _ _ _ _ MUa MUb)|].
  split; [exact (wmono_trans rsegs _ _ _ WM2 WM3r)|].
  split; [exact (ro_agree_same rsegs m2 m3 RO2 SAME)|].
  (* every region: the stores (SW2), normalize (mem_rel), the copy's post (SW3), back across mem_rel *)
  split.
  { intros P HP. apply (A.ShadowRwOnT.shadow_rw_on_of_rel P m3 m3n R8). apply SW3.
    exact (A.ShadowRwOnT.shadow_rw_on_rel P m2 _ REL2 (SW2 P HP)). }
  split; [exact (F23.f23_stk_rel_hi_back m3 m3n (spv - FN_STACK) spv R8 ltac:(lia) ltac:(lia) ST3)|].
  split.
  { destruct RW3 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    exact (proj2 (bytes_at_rel rsegs m3 m3n (fr + 128) F23.ports_c_bytes R8) HB). }
  { apply (F23.f23_addr_keep m2 m3 _ (fr + 128) 12 AD2 MU3n).
    intros i Hi. cbn [outside].
    assert (Hap : app_mem (fr + 128 + i)) by (apply Happ; lia).
    pose proof (shadow_of_app _ Hap) as Hsh.
    pose proof (Happ (fr + 128) ltac:(lia)) as Hap0.
    pose proof (Happ (fr + 139) ltac:(lia)) as Hap1.
    unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END,
      AF.SLOT_STACK in *.
    split; [lia|]. split; [lia | exact I]. }
Qed.

(* The plain twin of f23_evt_of_F: f23_evt_F_on at ExecF.RNG_all, the footprint contract discharged by a Theorem Labs lane's
   asan_memcpy_holds_F_on (lib/A/Prog/asan_memcpyF_on.v). As f23_evt_of_F keeps the plain asan_memcpy_contract in
   its place, this keeps the plain region contract asan_memcpy_contract_on in its place, used by nothing. R: the
   same region as f23_evt_F_on's. No pin (no new constr_eq pin against a plain X_on). *)
Lemma f23_evt_of_F_on : asan_memcpy_contract_on ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (spv A fr Sf : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sf -> a0 = s4 -> Sf = Sfr fr ->
    0 <= fr -> fr mod 8 = 0 -> AC.GT <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spv - 2224 \/ spv <= fr) ->
    fr + FRAME_BYTES <= A -> spv <= A -> A + 312 <= 2 ^ 64 ->
    HIGHMEM_BEG + FN_STACK <= spv -> spv <= APPMEM_END ->
    0 <= Sf -> Sf + FRAME_SHADOW <= HIGHMEM_BEG -> (fr + FRAME_BYTES <= Sf \/ Sf + FRAME_SHADOW <= fr) ->
    q64 m (A + 136) (fr + 128) ->
    rw_cells rsegs m (fr + 128) [CB 12 junk] ->
    addressable m F23.PORTSC 12 ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (f23_evt_F_shadow_R fr Sf) m -> ro_agree rsegs m ->
    stk rsegs m (spv - FN_STACK) spv ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x825c8) fcs None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 20 = Z_to_bv 64 (fr + 128) /\
         munch [(spv - 2224, spv); (fr + 128, fr + 140); (Sf + 16, Sf + 18)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         stk rsegs m' (spv - FN_STACK) spv /\
         bytes_at rsegs m' (fr + 128) F23.ports_c_bytes /\ addressable m' (fr + 128) 12)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x825a0) fcs None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros _ ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcs m spv A fr Sf junk Esp Es1 Es3 Ea0 ESf Hfr0 Hfr8 HGT Hfrend Happ Hfrw HfrA HspA HAhi Hsplo Hspend
    HSf0 HSfhi HSfap Hq136 RWq HADimg HAC HSW HRO HST.
  pose proof two64 as H64.
  assert (KAPP : APPMEM_END = 0x800000000000) by reflexivity.
  assert (KHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (KFN : FN_STACK = 1044480) by reflexivity.
  assert (KMC : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (KIL : IMG_LO = 65536) by reflexivity.
  assert (KIH : IMG_HI = 6283264) by reflexivity.
  assert (KPO : F23.PORTSC = 135552) by reflexivity.
  assert (KGT : AC.GT = 6283264) by reflexivity.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f23_evt_F_on ExecF.RNG_all A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on
           ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           Fr fcs m spv A fr Sf junk Esp Es1 Es3 Ea0 ESf Hfr0 Hfr8 HGT Hfrend Happ Hfrw
           HfrA HspA HAhi Hsplo Hspend HSf0 HSfhi HSfap Hq136 RWq HADimg HAC HSW HRO HST).
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply sh_word_rng_all; lia.
  - apply sh_word_rng_all; lia.
  - apply sh_word_rng_all; lia.
Qed.

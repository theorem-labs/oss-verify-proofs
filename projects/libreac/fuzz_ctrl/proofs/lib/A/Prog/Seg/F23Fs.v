(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 1068 of its 1186 lines of code are new or changed and 1084 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F23.v; 148 of its 304 lines of code are new or changed and 1030 lines of the source are left out. *)
(* PROVENANCE. Image A = fuzz_ctrl.asan, libreac v1.9.0 (pinned as lib/A/Prog/Seg/F23F.v's header states:
   (internal path) sha256
   aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d). FACTS ed6b6b7b0ab, PAU pau-libreac-v190.
   Source: lib/A/Prog/Seg/F23F.v (a Theorem Labs lane's mechanical re-run of Seg/F23.v's f23_evt), unchanged apart from comment text, and Required.
   Written by a Theorem Labs lane (the glue lane of stage seg_F23), under a Theorem Labs lane's narrowing rule (the
   stage's glue owner may add a minimal narrowed `_Fs` in its own new file, with a proved pin re-deriving a Theorem Labs lane's
   lemma); approved by the lane lead a Theorem Labs lane 2026-10-29. rule 24: no function proved (a narrowing of an
   already-proved segment run).

   WHAT CHANGES, AND WHY. F23F.f23_evt_F (Seg/F23F.v:72-109) hands the copy's contract asan_memcpy_contract_F the
   stack window `stk rsegs m lo sp` with lo FIXED to `spv - FN_STACK` (FN_STACK = 1044480; F23F.v:86 premise, :214
   instantiation, :106 post). The walk's cut (lib/A/ACtlCutP.v C_A825a0_at, under ACtlCut.v's ctl_from) gives
   presence of the journal's stack window [c_sp - 32768, c_sp) only (Reusable/YCbq.v:368; AR_stack_law,
   Reusable/YG0d.v:468, gives no presence), so that 1 MB premise is not provable at the cut. The contract itself
   takes a free lo (lib/A/Prog/asan_memcpy_cF.v:49, :58-59: `stk rsegs m lo sp`, `lo + ASAN_MEMCPY_K <= sp`,
   `HIGHMEM_BEG <= lo`), as F18F / F19F state the same callee premise. So f23_evt_Fs below is f23_evt_F with lo a
   binder:
     premises  `HIGHMEM_BEG + FN_STACK <= spv` and `stk rsegs m (spv - FN_STACK) spv` become
               `HIGHMEM_BEG <= lo`, `lo + ASAN_MEMCPY_K <= spv` and `stk rsegs m lo spv`;
     post      `stk rsegs m' (spv - FN_STACK) spv` becomes `stk rsegs m' lo spv`;
   everything else (binders, premises, footprint premises, post) is f23_evt_F's, in its order. The proof is
   f23_evt_F's script with `spv - FN_STACK` replaced by lo; no new reasoning.

   THE PIN. f23_evt_F_of_Fs states f23_evt_F's type (copied) and is proved from f23_evt_Fs at
   lo := spv - FN_STACK; f23_evt_F_of_Fs_verbatim checks by constr_eq (syntactic) that its type IS the type of
   F23F.f23_evt_F, so the narrowing re-derives a Theorem Labs lane's lemma and weakens nothing.

   Shape of segF-v19-spec.md (a working note, not in this delivery) (RNG first, footprint premises appended, evtF
   conclusion, a verbatim pin). Footprint rows: lib/A/Prog/Seg/F23Fs.rng.tsv.

   QUALIFIED NAMES (a Theorem Labs lane 15:45Z, a Theorem Labs lane). ctrlgate 4468e8a23a4a-49a5f33bf5c7 flagged 27 uses written
   `MState.unsigned_lit_wrap` (:65, in f23s_accF), `MState.unsigned_lit` (25 uses in f23_evt_Fs) and
   `MState.ret_pc_even` (in f23_evt_Fs) as ambiguous: this file's closure reaches three MState copies (lib/Lib,
   lib/A/Bz/Lib, lib/A/Tk/UL). Each such use is now written with the full path of the copy it bound before the change:
   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState, as both this file's own .glob and Locate in its
   context (locate_table v5) show. So each use binds the same constant as before; `Set Printing All. Print` of the
   touched declarations gives the same bytes before and after the change. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs B7Cuts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F23 F23F.
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

(* F23F.v's f23_accF (Seg/F23F.v:59-69), unchanged: F23F.v sets it Local, so it is restated here. *)
Ltac f23s_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | H : rng RNG ?lo ?len |- _ =>
          apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz));
          cbv [wa]; rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit_wrap; Z.div_mod_to_equations; lia
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= f23s_accF.

(* ---- f23_evt_F with the copy's stack-window base lo a binder ---- *)
Lemma f23_evt_Fs : forall (RNG : ExecF.footprint),
  asan_memcpy_contract_F ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (spv A fr Sf lo : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sf -> a0 = s4 -> Sf = Sfr fr ->
    0 <= fr -> fr mod 8 = 0 -> AC.GT <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spv - 2224 \/ spv <= fr) ->
    fr + FRAME_BYTES <= A -> spv <= A -> A + 312 <= 2 ^ 64 ->
    HIGHMEM_BEG <= lo -> lo + ASAN_MEMCPY_K <= spv -> spv <= APPMEM_END ->
    0 <= Sf -> Sf + FRAME_SHADOW <= HIGHMEM_BEG -> (fr + FRAME_BYTES <= Sf \/ Sf + FRAME_SHADOW <= fr) ->
    q64 m (A + 136) (fr + 128) ->
    rw_cells rsegs m (fr + 128) [CB 12 junk] ->
    addressable m F23.PORTSC 12 ->
    asan_cells m -> shadow_rw m -> ro_agree rsegs m -> stk rsegs m lo spv ->
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
         stk rsegs m' lo spv /\
         bytes_at rsegs m' (fr + 128) F23.ports_c_bytes /\ addressable m' (fr + 128) 12)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x825a0) fcs None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros RNG MCPY ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcs m spv A fr Sf lo junk Esp Es1 Es3 Ea0 ESf Hfr0 Hfr8 HGT Hfrend Happ Hfrw HfrA HspA HAhi Hlo HloK
    Hspend HSf0 HSfhi HSfap Hq136 RWq HADimg HAC HSW HRO HST
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
  assert (ST2 : stk rsegs m2 lo spv).
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
  (* the copy, on its footprint contract, run on the normalized memory, at the window base lo *)
  pose proof (mem_rel_normalize rsegs m2 RO2) as REL2.
  eapply ExecF.evtF_cut.
  { eapply MNF.evtF_normalize_ro; [exact RO2|].
    eapply MCPY with (RNG := RNG) (src := F23.ports_c_bytes) (junk := junk) (lo := lo).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      exact (F23.f23_src_bytes _ (mem_inv_normalize rsegs m2)).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. rewrite F23.f23_ports_len. reflexivity.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      exact (F23.f23_rw_cells_rel m2 _ (fr + 128) _ REL2 ltac:(lia) RW2).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia). unfold F23.PORTSC. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      exact (F23.f23_addressable_rel m2 _ F23.PORTSC 12 REL2 ADS2).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact (F23.f23_addressable_rel m2 _ (fr + 128) 12 REL2 AD2).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia).
      unfold end_in_app, app_mem, F23.PORTSC, LOWMEM_END. right. left. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. unfold end_in_app. right. apply Happ. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia). right. split.
      + unfold app_mem, F23.PORTSC, LOWMEM_END. left. lia.
      + apply Happ. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. unfold RT_LO, RT_HI. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia). unfold F23.PORTSC, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      exact (F23.f23_stk_rel_hi m2 _ lo spv REL2 ltac:(lia) ltac:(lia) ST2).
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
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia). exact RngS.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RngDs.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by (unfold F23.PORTSC; lia). exact RngSs.
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
  split; [exact (F23.f23_stk_rel_hi_back m3 m3n lo spv R8 ltac:(lia) ltac:(lia) ST3)|].
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

(* ---- the pin: f23_evt_F's type (Seg/F23F.v:72-109, copied), re-derived from f23_evt_Fs at lo := spv - FN_STACK ---- *)
Lemma f23_evt_F_of_Fs : forall (RNG : ExecF.footprint),
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
  intros RNG MCPY ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcs m spv A fr Sf junk Esp Es1 Es3 Ea0 ESf Hfr0 Hfr8 HGT Hfrend Happ Hfrw HfrA HspA HAhi Hsplo Hspend
    HSf0 HSfhi HSfap Hq136 RWq HADimg HAC HSW HRO HST.
  assert (KFN : FN_STACK = 1044480) by reflexivity.
  assert (KMC : ASAN_MEMCPY_K = 2224) by reflexivity.
  exact (f23_evt_Fs RNG MCPY ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fcs m spv A fr Sf (spv - FN_STACK) junk Esp Es1 Es3 Ea0 ESf Hfr0 Hfr8 HGT Hfrend Happ Hfrw
           HfrA HspA HAhi ltac:(lia) ltac:(lia) Hspend HSf0 HSfhi HSfap Hq136 RWq HADimg HAC HSW HRO HST).
Qed.

(* The pin: f23_evt_F_of_Fs states F23F.f23_evt_F's type, term for term (constr_eq: syntactic, not up to
   conversion), so the narrowing re-derives a Theorem Labs lane's lemma. *)
Lemma f23_evt_F_of_Fs_verbatim : True.
Proof.
  let A := type of F23F.f23_evt_F in let B := type of f23_evt_F_of_Fs in constr_eq A B; exact I.
Qed.

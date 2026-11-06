(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 1068 of its 1186 lines of code are new or changed and 1084 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F23.v; 113 of its 263 lines of code are new or changed and 1036 lines of the source are left out. *)
(* lib/A/Prog/Seg/F23Fs_on.v -- route (C) twin of lib/A/Prog/Seg/F23Fs.v's f23_evt_Fs (Seg/F23Fs.v:71-299), for the
   glue stage F23 of a Theorem Labs lane (owner a Theorem Labs lane). ADDITIVE: Seg/F23Fs.v (and Seg/F23.v, Seg/F23F.v) are Required and
   unchanged in this delivery apart from comment text; since this twin was written, F23Fs.v names MState by its full path and F23F.v gained its own f23_evt_F_on; this file adds one Definition and one Lemma. Proves no function (kind: segment run).
   rule 24: no function proved.

   WHAT CHANGES. f23_evt_Fs_on is f23_evt_Fs with ONLY:
     - the callee premise `asan_memcpy_contract_F ->` becomes `asan_memcpy_contract_F_on ->`
       (lib/A/Prog/asan_memcpy_cF_on.v; its binders and footprint premises are asan_memcpy_contract_F's, unchanged:
       asan_memcpy_cF_on.v:36-41 = asan_memcpy_cF.v:62-67; the glue closes it with
       A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on);
     - the shadow premise `shadow_rw m` becomes `shadow_rw_on (f23_evt_Fs_shadow_R fr Sf) m`;
     - the post conjunct `shadow_rw m'` becomes `(forall P, shadow_rw_on P m -> shadow_rw_on P m')`.
   Every other binder, premise (the rng / sh_word_rng footprint premises included) and post conjunct is
   f23_evt_Fs's, in its order.

   THE REGION R = f23_evt_Fs_shadow_R fr Sf (the text of a Theorem Labs lane's F23.f23_evt_shadow_R (from a working branch f556cbc34ed),
   Seg/F23.v (a version not in this delivery), with PORTSC qualified as F23Fs.v names it, F23.PORTSC). Its disjuncts are the uses of the shadow
   premise HSW in f23_evt_Fs's proof (lines of Seg/F23Fs.v):
     - Sf + 16 <= a < Sf + 18: the two shadow stores 0x825a4 sb zero,16(s3) and 0x825ac sb a0,17(s3) need the bytes
       writable: HS16, F23Fs.v:133 `proj1 (HSW _ HSH16)`, and HS17, F23Fs.v:142 `proj1 (HSW _ HSH17)`;
     - asan_memcpy_shadow_R at the call's arguments a0 = fr + 128, a1 = F23.PORTSC, a2 = 12: the copy's own shadow
       premise, F23Fs.v:238 `F23.f23_shadow_rw_rel m2 _ REL2 SW2`, with SW2 from HSW across the two stores
       (F23Fs.v:174-176, F23.f23_shadow_rw_write).
   The remaining use, F23Fs.v:285 `F23.f23_shadow_rw_rel_back m3 m3n R8 SW3` for the post's shadow_rw m', becomes the
   forall-P post and reads no byte of the premise. The copy's own stack shadow is not in asan_memcpy_contract_F_on's
   shadow premise (only in its sh_word_rng footprint premise, kept), so it is not in R.

   PROOF. f23_evt_Fs's script, with a Theorem Labs lane's narrowing steps from the plain twin F23.f23_evt_on (from a working branch f556cbc34ed,
   Seg/F23.v (a version not in this delivery)): HS16 / HS17 from `proj1 (HSW _ HR16 HSH16)` / `proj1 (HSW _ HR17 HSH17)`; SW2 for every
   region across the two stores by A.ShadowRwOnT.shadow_rw_on_mem_mono + A.Prog.MemMono.rd_mono_write; the copy's
   shadow premise by A.ShadowRwOnT.shadow_rw_on_rel + A.ShadowRwOn.shadow_rw_on_mono from R's second disjunct; the
   post by A.ShadowRwOnT.shadow_rw_on_of_rel + the copy's forall-P post + A.ShadowRwOnT.shadow_rw_on_rel. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_c_on asan_memcpy_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs B7Cuts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F23 F23Fs.
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
(* lib/A/Tk/UL's MState (the copy the .glob of the first build records for unsigned_lit / ret_pc_even), by an alias,
   so ctrlgate's DUP check (lib/Lib/MState.v and lib/A/Bz/Lib/MState.v are also in the closure) sees one copy. *)
Module ULMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.

(* F23Fs.v's footprint hint for `step` (Seg/F23Fs.v:58-68), cited: F23Fs.v sets the hint Local. *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::=
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F23Fs.f23s_accF.

(* The shadow bytes f23_evt_Fs reads or writes through its shadow premise (header: where each disjunct comes from). *)
Definition f23_evt_Fs_shadow_R (fr Sf a : Z) : Prop :=
  (Sf + 16 <= a < Sf + 18) \/
  asan_memcpy_shadow_R (Z_to_bv 64 (fr + 128)) (Z_to_bv 64 F23.PORTSC) (Z_to_bv 64 12) a.

(* ---- f23_evt_Fs with the copy on asan_memcpy_contract_F_on and the shadow premise narrowed to R ---- *)
Lemma f23_evt_Fs_on : forall (RNG : ExecF.footprint),
  asan_memcpy_contract_F_on ->
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
    asan_cells m -> shadow_rw_on (f23_evt_Fs_shadow_R fr Sf) m -> ro_agree rsegs m -> stk rsegs m lo spv ->
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
         wmono rsegs m m' /\ ro_agree rsegs m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\
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
  assert (HR16 : f23_evt_Fs_shadow_R fr Sf (Sf + 16)) by (left; lia).
  assert (HR17 : f23_evt_Fs_shadow_R fr Sf (Sf + 17)) by (left; lia).
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
  (* the two stores keep every shadow byte present and writable, for any region (MemMono.rd_mono_write) *)
  assert (SW2 : forall P, shadow_rw_on P m -> shadow_rw_on P m2).
  { intros P HP. apply (ShadowRwOnT.shadow_rw_on_mem_mono P m m2 HP WM2).
    unfold m2. apply MemMono.rd_mono_write, MemMono.rd_mono_write, MemMono.rd_mono_refl. }
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
  (* the copy, on its route (C) footprint contract, run on the normalized memory, at the window base lo *)
  pose proof (mem_rel_normalize rsegs m2 RO2) as REL2.
  eapply ExecF.evtF_cut.
  { eapply MNF.evtF_normalize_ro; [exact RO2|].
    eapply MCPY with (RNG := RNG) (src := F23.ports_c_bytes) (junk := junk) (lo := lo).
    - rewrite !ULMS.unsigned_lit by (unfold F23.PORTSC; lia).
      exact (F23.f23_src_bytes _ (mem_inv_normalize rsegs m2)).
    - rewrite !ULMS.unsigned_lit by lia. rewrite F23.f23_ports_len. reflexivity.
    - rewrite !ULMS.unsigned_lit by lia.
      exact (F23.f23_rw_cells_rel m2 _ (fr + 128) _ REL2 ltac:(lia) RW2).
    - rewrite !ULMS.unsigned_lit by (unfold F23.PORTSC; lia). unfold F23.PORTSC. lia.
    - rewrite !ULMS.unsigned_lit by lia. lia.
    - rewrite !ULMS.unsigned_lit by (unfold F23.PORTSC; lia).
      exact (F23.f23_addressable_rel m2 _ F23.PORTSC 12 REL2 ADS2).
    - rewrite !ULMS.unsigned_lit by lia. exact (F23.f23_addressable_rel m2 _ (fr + 128) 12 REL2 AD2).
    - rewrite !ULMS.unsigned_lit by (unfold F23.PORTSC; lia).
      unfold end_in_app, app_mem, F23.PORTSC, LOWMEM_END. right. left. lia.
    - rewrite !ULMS.unsigned_lit by lia. unfold end_in_app. right. apply Happ. lia.
    - rewrite !ULMS.unsigned_lit by (unfold F23.PORTSC; lia). right. split.
      + unfold app_mem, F23.PORTSC, LOWMEM_END. left. lia.
      + apply Happ. lia.
    - rewrite !ULMS.unsigned_lit by lia. unfold RT_LO, RT_HI. lia.
    - rewrite !ULMS.unsigned_lit by lia. lia.
    - rewrite !ULMS.unsigned_lit by (unfold F23.PORTSC; lia). unfold F23.PORTSC, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - rewrite !ULMS.unsigned_lit by lia.
      exact (F23.f23_stk_rel_hi m2 _ lo spv REL2 ltac:(lia) ltac:(lia) ST2).
    - rewrite !ULMS.unsigned_lit by lia. lia.
    - unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - rewrite !ULMS.unsigned_lit by lia. lia.
    - exact (F23.f23_asan_cells_rel m2 _ REL2 AC2).
    - (* the copy's region is the second disjunct of f23_evt_Fs_shadow_R *)
      apply (ShadowRwOnT.shadow_rw_on_rel _ m2 _ REL2). apply SW2.
      apply (shadow_rw_on_mono (f23_evt_Fs_shadow_R fr Sf) _ m); [|exact HSW].
      intros x Hx. right. unfold asan_memcpy_shadow_R in Hx |- *.
      rewrite !ULMS.unsigned_lit in Hx by (try unfold F23.PORTSC; lia).
      rewrite !ULMS.unsigned_lit by (try unfold F23.PORTSC; lia). exact Hx.
    - exact (mem_inv_normalize rsegs m2).
    - exact Rby.
    - exact Rimg.
    - rewrite !ULMS.unsigned_lit by lia. exact Rstk.
    - rewrite !ULMS.unsigned_lit by lia. exact RngD.
    - rewrite !ULMS.unsigned_lit by (unfold F23.PORTSC; lia). exact RngS.
    - rewrite !ULMS.unsigned_lit by lia. exact RngDs.
    - rewrite !ULMS.unsigned_lit by (unfold F23.PORTSC; lia). exact RngSs.
    - rewrite !ULMS.unsigned_lit by lia. exact RngKs. }
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
  rewrite !ULMS.unsigned_lit in ST3, RW3, HBS3 by lia.
  assert (MU3nn : munch [(fr + 128, fr + 140); (spv - 2224, spv)] (normalize rsegs m2) m3n).
  { intros x Hx. apply MU3. cbn [outside] in Hx |- *. destruct Hx as (HO1 & HO2 & _).
    rewrite !ULMS.unsigned_lit by lia.
    split; [intros [Q1 Q2]; apply HO1; lia|]. split; [intros [Q1 Q2]; apply HO2; lia | exact I]. }
  assert (MU3n : munch [(fr + 128, fr + 140); (spv - 2224, spv)] m2 m3)
    by (eapply munch_rel; [exact REL2 | exact R8 | exact SAME | exact MU3nn]).
  assert (WM3r : wmono rsegs m2 m3)
    by (eapply wmono_rel; [exact REL2 | exact R8 | exact SAME | exact WM3]).
  replace (ret_pc (Z_to_bv 64 0x825c8)) with (Z_to_bv 64 0x825c8)
    by (symmetry; apply ULMS.ret_pc_even; [lia | reflexivity]).
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
  { intros P HP. apply (ShadowRwOnT.shadow_rw_on_of_rel P m3 m3n R8). apply SW3.
    exact (ShadowRwOnT.shadow_rw_on_rel P m2 _ REL2 (SW2 P HP)). }
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

Print Assumptions f23_evt_Fs_on.

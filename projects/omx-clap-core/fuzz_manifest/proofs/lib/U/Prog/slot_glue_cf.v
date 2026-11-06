From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import AgCf.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestModel ManifestMem ManifestB names_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import check_no_overread_c check_no_overread_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import slot_steps_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import slot_glue.
Import ListNotations.
Open Scope Z_scope.

(* The cut-free twins of slot_glue.v's allocator calls (sl_malloc_call, sl_free_call): SRcf in place of SR, the
   allocator through malloc_contract_cf / free_contract_cf, and the malloc room in its agreement form (AgCf.room_ag,
   turned into room_cf by room_cf_of_limit under LIMLAW). kinv and the pure lemmas of slot_glue.v are reused. *)
Section SGcf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.
Hypothesis SF : statics_facts B.
Hypothesis SFR : statics_free B MR.
Hypothesis ERR : errno_low B.
Hypothesis SNE : statics_noerrno B.
Hypothesis MSO : malloc_syms_omx B.
Hypothesis MCF : forall fx' : FPState, @malloc_contract_cf fx' rc B API.
Hypothesis FCF : forall fx' : FPState, @free_contract_cf fx' rc B API.
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).


Ltac kq := unfold SLK, ALLOC_STACK in *; lia.

Lemma sl_malloc_call_cf : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md n bnd (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 n -> 0 < n -> res_ok_slots A bnd -> room_ag bnd n ->
  (forall L' A' R' m' md' res,
     regs_preserved R R' -> getr R' 10 = Z_to_bv 64 res ->
     kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> st_init_done A' = true ->
     res_ok_slots A' (sb_malloc bnd n) -> 4096 <= res -> res + n <= alloc_ceiling ->
     (exists junk, rw_cells rsegs (normalize rsegs m') res [CB (Z.to_nat n) junk]) ->
     In (res, n) (blocks L' A') -> ~ In (res, n) (blocks L A) -> rmb (res, n) (blocks L' A') = blocks L A ->
     (forall x, In x (blocks L A) -> In x (blocks L' A')) ->
     (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, (spZ R <= a < 2 ^ 64 \/ alloc_statics a) ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     SRcf B (mkCfg (@mkst f R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x14f8c) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md n bnd P J INIT HAC H16 H63 SPR RA TP N10 Hn RES ROOM K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  replace (Z_to_bv 64 0x14f8c) with (Z_to_bv 64 (ms_malloc B)) by (rewrite (proj1 MSO); reflexivity).
  eapply SRcf_bind; [apply (MCF f L A R m md n bnd); [| rewrite HS; exact HMI | exact N10 | exact RES
    | exact (room_cf_of B API LIMLAW L A m md bnd n HM ROOM)] |].
  { apply (proj2 (call_pre_k_alloc B MR L A R m md)).
    apply (sl_pre_k B API HS ALLOC_STACK L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR RA TP); kq. }
  intros c' (L' & A' & R' & m' & md' & res & -> & CP & R10 & Hnz & H16' & (H4096 & HRC & HNI) & (b1 & b2 & E1 & E2) &
             BK0 & MI & GK & UB & INIT' & LEN & RES').
  apply (proj2 (call_post_k_alloc B MR _ _ _ _ _ _ _ _ _ _ _)) in CP.
  pose proof CP as (HM' & HWF' & HBD' & HLE & HST & RP & HMD' & HFR' & HKP & HSC').
  assert (BK : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)).
  { intros a k i Hin Hi. rewrite <- HS. exact (BK0 a k i Hin (fun x => x) Hi). }
  rewrite HS in HFR', HSC', MI.
  assert (NIN' : ~ In (res, n) (b1 ++ b2)) by exact (fresh_notin B API L' A' m' md' b1 b2 res n HM' E1 Hn).
  assert (INC : forall x, In x (blocks L A) -> In x (blocks L' A')).
  { intros x Hx. rewrite E2 in Hx. rewrite E1. apply in_app_iff in Hx. apply in_app_iff.
    destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx]. }
  assert (INR : In (res, n) (blocks L' A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
  destruct (sl_block_range B API L' A' m' md' res n HM' INR) as [_ RNG].
  apply (K L' A' R' m' md' res RP R10).
  - apply (kinv_step B API AX SLK L0 A0 regs0 mem0 md0 L A m md L' A' m' md' ALLOC_STACK (spZ R) (fun _ => False)
             J HM' HWF' HBD' HMD').
    + kq.
    + kq.
    + kq.
    + intros a [].
    + intros a Hr H1 H2 H3 H4. apply HFR'; assumption.
    + intros a Ha. apply HSC'. exact Ha.
    + intros a k i Hin Hi. exact (BK a k i (HP0 _ Hin) Hi).
    + intros x Hx. apply INC. exact (HP0 x Hx).
    + exact MI.
  - exact INIT'.
  - exact RES'.
  - exact H4096.
  - exact RNG.
  - destruct (rw_cells_of_present m' res n ltac:(lia) ltac:(lia) ltac:(lia)) as (junk & RW).
    { intros i Hi. destruct (in_blocks L' A' res n INR) as (p & Hp & Ep).
      destruct (mr_blocks _ _ (aa_laws API) L' A' m' md' p n i HM' Hp Hi) as (Pr & _). rewrite <- Ep in Pr. exact Pr. }
    exists junk. apply (rw_cells_norm m' res _ MI RW). intros i Hi. cbn [cells_size csize] in Hi.
    apply (ro_false_not_img B HS); [apply HNI; lia | lia].
  - exact INR.
  - rewrite E2. exact NIN'.
  - rewrite E1, E2. apply rmb_ins. exact NIN'.
  - exact INC.
  - exact BK.
  - intros a Ha. apply (sl_cp_keep B API HS SF SFR ERR SNE L A R m md (fun _ => False) L' A' R' m' md' HM CP); [kq | exact Ha | intros []].
Qed.

Lemma sl_free_call_cf : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md r n bnd (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 r -> In (r, n) (blocks L A) -> ~ In (r, n) (blocks L0 A0) -> 0 < n ->
  res_ok_slots A bnd ->
  (forall L' A' R' m' md',
     regs_preserved R R' -> kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> st_init_done A' = true ->
     res_ok_slots A' (sb_free bnd n) -> blocks L' A' = rmb (r, n) (blocks L A) ->
     (forall a k i, In (a, k) (blocks L A) -> a <> r -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, (spZ R <= a < 2 ^ 64 \/ alloc_statics a) ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     SRcf B (mkCfg (@mkst f R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x14e4c) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md r n bnd P J INIT HAC H16 H63 SPR RA TP R10 Hin NIN0 Hn RES K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  destruct (in_blocks L A r n Hin) as (p & Hp & Er).
  destruct (sl_block_range B API L A m md r n HM Hin) as [RL RH].
  replace (Z_to_bv 64 0x14e4c) with (Z_to_bv 64 (ms_free B)) by (rewrite (proj2 MSO); reflexivity).
  eapply SRcf_bind; [apply (FCF f L A R m md p n bnd); [| rewrite HS; exact HMI | exact Hp | rewrite <- Er; exact R10 | exact RES] |].
  { apply (proj2 (call_pre_k_alloc B MR L A R m md)).
    apply (sl_pre_k B API HS ALLOC_STACK L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR RA TP); kq. }
  intros c' (L' & A' & R' & m' & md' & -> & CP & (b1 & b2 & E1 & E2) & BK0 & MI & GK & UB & INIT' & LEN & RES').
  rewrite <- Er in CP, E1, BK0.
  pose proof CP as (HM' & HWF' & HBD' & HLE & HST & RP & HMD' & HFR' & HKP & HSC').
  assert (BK : forall a k i, In (a, k) (blocks L A) -> a <> r -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)).
  { intros a k i Ha Hne Hi. rewrite <- HS. exact (BK0 a k i Ha Hne Hi). }
  rewrite HS in HFR', HSC', MI.
  assert (NIN' : ~ In (r, n) (b1 ++ b2)) by exact (fresh_notin B API L A m md b1 b2 r n HM E1 Hn).
  assert (EB : blocks L' A' = rmb (r, n) (blocks L A)) by (rewrite E2, E1; symmetry; apply rmb_ins; exact NIN').
  assert (NE0 : forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k -> a <> r).
  { intros a k i Ha Hi Ear. subst a.
    assert (Hne : (r, k) <> (r, n)) by (intros E; rewrite E in Ha; exact (NIN0 Ha)).
    destruct (blocks_sep B API L A m md (r, k) (r, n) HM (HP0 _ Ha) Hin Hne) as [D|D]; cbn in D; lia. }
  apply (K L' A' R' m' md' RP).
  - apply (kinv_step B API AX SLK L0 A0 regs0 mem0 md0 L A m md L' A' m' md' ALLOC_STACK (spZ R)
             (fun a => r <= a < r + n) J HM' HWF' HBD' HMD').
    + kq.
    + kq.
    + kq.
    + intros a Ha. left. split; [lia|].
      pose proof (block_not_img B API AX L A m md r n (a - r) HM Hin ltac:(lia)) as Hni.
      replace (r + (a - r)) with a in Hni by lia. exact Hni.
    + intros a Hr H1 H2 H3 H4. apply HFR'; assumption.
    + intros a Ha. apply HSC'. exact Ha.
    + intros a k i Ha Hi. exact (BK a k i (HP0 _ Ha) (NE0 a k i Ha Hi) Hi).
    + intros x Hx. rewrite EB. destruct x as [a k]. apply rmb_in; [exact (HP0 _ Hx)|].
      intros E. rewrite E in Hx. exact (NIN0 Hx).
    + exact MI.
  - exact (INIT' INIT).
  - exact RES'.
  - exact EB.
  - exact BK.
  - intros a Ha. apply (sl_cp_keep B API HS SF SFR ERR SNE L A R m md _ L' A' R' m' md' HM CP); [kq | exact Ha |].
    intros He. cbv beta in He. destruct Ha as [Ha|Ha]; [kq|]. pose proof (sl_statics_low a Ha).
    pose proof (block_not_img B API AX L A m md r n (a - r) HM Hin ltac:(lia)) as Hni.
    replace (r + (a - r)) with a in Hni by lia. exact (Hni (proj1 (SF a Ha))).
Qed.

End SGcf.

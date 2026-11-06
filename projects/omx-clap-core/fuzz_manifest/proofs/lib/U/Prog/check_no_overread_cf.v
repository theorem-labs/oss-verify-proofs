From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem memcpy_c memset_c check_no_overread_steps.
Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestB names_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import check_no_overread_c check_no_overread_glue.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import AllocRoom SlotAgree AgreeLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import AgCf names_c_cf check_no_overread_c_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import check_no_overread.
Local Open Scope Z_scope.

(* The cut-free (agreement) twin of check_no_overread.cno_core / check_no_overread_holds: the same proof in SRcf
   form. The allocator is taken through malloc_contract_cf / free_contract_cf (room_cf at each malloc site from the
   agreement room AgCf.room_ag and the source limit LIMLAW (2^34 <= vm_limit)), names through names_contract_cf. The four malloc sites
   get room_ag from AgCf.room_ag_of: cap <= CAP_AG and 3 * len ub + 2 * len tb + 91 <= 2^29 live bytes at entry. *)

Ltac cfeed H :=
  repeat match type of H with
  | ?P -> _ => match type of P with Prop => match goal with Hp : _ |- _ => specialize (H Hp) end end
  end.

Section P.
Context {fx : YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTX : ctx_owned B MR.
Hypothesis SF : statics_facts B.
Hypothesis SFR : statics_free B MR.
Hypothesis ERR : errno_low B.
Hypothesis SNE : statics_noerrno B.
Hypothesis MSO : malloc_syms_omx B.
Hypothesis MCF : forall fx' : FPState, @malloc_contract_cf fx' rc B API.
Hypothesis FCF : forall fx' : FPState, @free_contract_cf fx' rc B API.
Hypothesis NAMES : forall fx' : FPState, @names_contract_cf fx' rc B API.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis MEMSET : memset_contract.
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).

Section H.
Hypothesis HS : ms_segs B = rsegs.

Lemma malloc_call_cf : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md n bnd (P : config -> Prop),
  jinv B API L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true ->
  alloc_ceiling + CNO_K <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 ->
  spZ R = spZ regs0 - 96 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 n -> 0 < n -> res_ok_slots A bnd -> room_ag bnd n ->
  (forall L' A' R' m' md' res,
     regs_preserved R R' -> getr R' 10 = Z_to_bv 64 res ->
     jinv B API L0 A0 regs0 mem0 md0 L' A' m' md' -> st_init_done A' = true ->
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
  first [pose proof (check_no_overread.cp_keep B API) as cp_keep | pose proof (check_no_overread.cp_keep B) as cp_keep]. cfeed cp_keep.
  first [pose proof (check_no_overread.block_range B API) as block_range | pose proof (check_no_overread.block_range B) as block_range]. cfeed block_range.
  intros f L0 A0 regs0 mem0 md0 L A R m md n bnd P J INIT HAC H16 H63 SPR RA TP N10 Hn RES ROOM K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  replace (Z_to_bv 64 0x14f8c) with (Z_to_bv 64 (ms_malloc B)) by (rewrite (proj1 MSO); reflexivity).
  eapply SRcf_bind; [apply (MCF f L A R m md n bnd); [| rewrite HS; exact HMI | exact N10 | exact RES | exact (room_cf_of B API LIMLAW L A m md bnd n HM ROOM)] |].
  { unfold call_pre. split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact RA|].
    split; [rewrite SPR; Z.div_mod_to_equations; lia|]. split; [rewrite SPR; kc|]. split; [lia|].
    split; [intros a Ha; rewrite HS; apply HSC; left; kc|].
    split; [exact TP|]. split; [intros a Ha; rewrite HS; apply HSC; right; exact Ha|].
    intros H. rewrite INIT in H. discriminate. }
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
  destruct (block_range L' A' m' md' res n HM' INR) as [_ RNG].
  apply (K L' A' R' m' md' res RP R10).
  - apply (jinv_step B API AX L0 A0 regs0 mem0 md0 L A m md L' A' m' md' ALLOC_STACK (spZ R) (fun _ => False)
             J HM' HWF' HBD' HMD').
    + kc.
    + kc.
    + kc.
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
  - intros a Ha. apply (cp_keep L A R m md (fun _ => False) L' A' R' m' md' HM CP); [kc | exact Ha | intros []].
Qed.

Lemma free_call_cf : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md r n bnd (P : config -> Prop),
  jinv B API L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true ->
  alloc_ceiling + CNO_K <= spZ regs0 -> spZ regs0 < 2 ^ 63 ->
  spZ R mod 16 = 0 -> spZ regs0 - CNO_K <= spZ R - ALLOC_STACK -> spZ R <= spZ regs0 ->
  YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 r -> In (r, n) (blocks L A) -> ~ In (r, n) (blocks L0 A0) -> 0 < n ->
  res_ok_slots A bnd ->
  (forall L' A' R' m' md',
     regs_preserved R R' -> jinv B API L0 A0 regs0 mem0 md0 L' A' m' md' -> st_init_done A' = true ->
     res_ok_slots A' (sb_free bnd n) -> blocks L' A' = rmb (r, n) (blocks L A) ->
     (forall a k i, In (a, k) (blocks L A) -> a <> r -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, (spZ R <= a < 2 ^ 64 \/ alloc_statics a) ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     SRcf B (mkCfg (@mkst f R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x14e4c) m (seg_rom (ms_segs B))) md) P.
Proof.
  first [pose proof (check_no_overread.cp_keep B API) as cp_keep | pose proof (check_no_overread.cp_keep B) as cp_keep]. cfeed cp_keep.
  first [pose proof (check_no_overread.block_range B API) as block_range | pose proof (check_no_overread.block_range B) as block_range]. cfeed block_range.
  intros f L0 A0 regs0 mem0 md0 L A R m md r n bnd P J INIT HAC H63 H16 SPL SPH RA TP R10 Hin NIN0 Hn RES K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  destruct (in_blocks L A r n Hin) as (p & Hp & Er).
  destruct (block_range L A m md r n HM Hin) as [RL RH].
  replace (Z_to_bv 64 0x14e4c) with (Z_to_bv 64 (ms_free B)) by (rewrite (proj2 MSO); reflexivity).
  eapply SRcf_bind; [apply (FCF f L A R m md p n bnd); [| rewrite HS; exact HMI | exact Hp | rewrite <- Er; exact R10 | exact RES] |].
  { unfold call_pre. split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact RA|].
    split; [exact H16|]. split; [kc|]. split; [lia|].
    split; [intros a Ha; rewrite HS; apply HSC; left; kc|].
    split; [exact TP|]. split; [intros a Ha; rewrite HS; apply HSC; right; exact Ha|].
    intros H. rewrite INIT in H. discriminate. }
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
  - apply (jinv_step B API AX L0 A0 regs0 mem0 md0 L A m md L' A' m' md' ALLOC_STACK (spZ R)
             (fun a => r <= a < r + n) J HM' HWF' HBD' HMD').
    + kc.
    + kc.
    + kc.
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
  - intros a Ha. apply (cp_keep L A R m md _ L' A' R' m' md' HM CP); [kc | exact Ha |].
    intros He. cbv beta in He. destruct Ha as [Ha|Ha]; [kc|]. pose proof (statics_low a Ha).
    pose proof (block_not_img B API AX L A m md r n (a - r) HM Hin ltac:(lia)) as Hni.
    replace (r + (a - r)) with a in Hni by lia. exact (Hni (proj1 (SF a Ha))).
Qed.

Lemma names_call_cf : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md bnd (ub tb : list byte) Lam pk0 ct0 fl
    pk ct (ta ua fa fb : Z) (P : config -> Prop),
  jinv B API L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true -> frm_zero (@fp_csr f) ->
  ledger B L0 A0 mem0 Lam pk0 ct0 fl -> img_strings mem0 -> ro_agree rsegs mem0 ->
  alloc_ceiling + CNO_K <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 -> spZ regs0 <= TASK_SIZE ->
  spZ R = spZ regs0 - 96 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 ta -> getr R 11 = Z_to_bv 64 ua ->
  bytes_at rsegs m ta (cpy tb fa) -> bytes_at rsegs m ua (cpy ub fb) ->
  In (ta, Z.of_nat (length tb) + 18) (blocks L A) -> In (ua, Z.of_nat (length ub) + 18) (blocks L A) ->
  Forall (fun x => bv_unsigned x <> 0) tb -> Forall (fun x => bv_unsigned x <> 0) ub ->
  (length ub <= 255)%nat -> Z.of_nat (length tb) <= 2 ^ 22 ->
  alloc_words B m (lsum Lam) pk ct fl -> lsum Lam <= pk < 2 ^ 64 -> 0 <= ct -> ct + 1 < 2 ^ 63 ->
  fl = 2 ^ 64 - 1 ->
  res_ok_slots A bnd -> sb_live bnd + 1 <= sb_cap bnd <= CAP_AG -> 0 <= sb_bytes bnd ->
  sb_bytes bnd + (Z.of_nat (length ub) + 19) <= 2 ^ 29 ->
  (forall (f' : FPState) L' A' R' m' md',
     frm_zero (@fp_csr f') -> st_init_done A' = true -> regs_preserved R R' ->
     getr R' 10 = Z_to_bv 64 (ub_case ub 0 (names (ManifestMem.zbytes tb) (ManifestMem.zbytes ub))) ->
     jinv B API L0 A0 regs0 mem0 md0 L' A' m' md' -> blocks L' A' = blocks L A ->
     (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, spZ R <= a < 2 ^ 64 ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     alloc_words B m' (lsum Lam) (ub_case ub pk (Z.max pk (lsum Lam + Z.of_nat (length ub) + 3)))
       (ub_case ub ct (ct + 1)) fl ->
     lsum Lam <= ub_case ub pk (Z.max pk (lsum Lam + Z.of_nat (length ub) + 3)) < 2 ^ 64 ->
     res_ok_slots A' bnd ->
     SRcf B (mkCfg (@mkst f' R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x13e10) m (seg_rom (ms_segs B))) md) P.
Proof.
  first [pose proof (check_no_overread.block_range B API) as block_range | pose proof (check_no_overread.block_range B) as block_range]. cfeed block_range.
  first [pose proof (check_no_overread.off_statics_block B API) as off_statics_block | pose proof (check_no_overread.off_statics_block B) as off_statics_block]. cfeed off_statics_block.
  first [pose proof (check_no_overread.ledger_jinv B API) as ledger_jinv | pose proof (check_no_overread.ledger_jinv B) as ledger_jinv]. cfeed ledger_jinv.
  first [pose proof (check_no_overread.aw_of_ledger B API) as aw_of_ledger | pose proof (check_no_overread.aw_of_ledger B) as aw_of_ledger]. cfeed aw_of_ledger.
  intros f L0 A0 regs0 mem0 md0 L A R m md bnd ub tb Lam pk0 ct0 fl pk ct ta ua fa fb P
    J INIT FRM LED0 IMG0 MI0 HAC H16 H63 TSZ SPR RA TP R10 R11 CT CU INT INU NZT NZU LU LT AW PK C0 C1 FL RES CAP BY0 BYQ K.
  pose proof alloc_ceiling_val as Hacv. unfold errno_low in ERR.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  destruct (block_range L A m md ta _ HM INT) as [TL TH].
  destruct (block_range L A m md ua _ HM INU) as [UL UH].
  assert (LG : ledger B L A m Lam pk ct fl) by (eapply ledger_jinv; [exact LED0 | exact J | exact AW | exact PK | lia]).
  assert (SLK : forall (bs : list byte) (fl0 : Z), (- (ta + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length (repeat (Z_to_bv 8 fl0) 16 ++ [Z_to_bv 8 0]))).
  { intros. rewrite length_app, repeat_length. cbn [length]. pose proof (Z.mod_pos_bound (- (ta + Z.of_nat (length bs) + 1)) 8). lia. }
  assert (SLU : forall (bs : list byte) (fl0 : Z), (- (ua + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length (repeat (Z_to_bv 8 fl0) 16 ++ [Z_to_bv 8 0]))).
  { intros. rewrite length_app, repeat_length. cbn [length]. pose proof (Z.mod_pos_bound (- (ua + Z.of_nat (length bs) + 1)) 8). lia. }
  assert (SL : length (repeat (Z_to_bv 8 fa) 16 ++ [Z_to_bv 8 0]) = 17%nat) by (rewrite length_app, repeat_length; reflexivity).
  assert (SLb : length (repeat (Z_to_bv 8 fb) 16 ++ [Z_to_bv 8 0]) = 17%nat) by (rewrite length_app, repeat_length; reflexivity).
  assert (UT : bv_unsigned (getr R 10) = ta) by (rewrite R10; apply unsigned_lit; lia).
  assert (UU : bv_unsigned (getr R 11) = ua) by (rewrite R11; apply unsigned_lit; lia).
  assert (US : bv_unsigned (getr R 2) = spZ regs0 - 96) by exact SPR.
  eapply SRcf_bind.
  { apply (NAMES f L A R m md bnd tb (repeat (Z_to_bv 8 fa) 16 ++ [Z_to_bv 8 0]) ub
             (repeat (Z_to_bv 8 fb) 16 ++ [Z_to_bv 8 0]) Lam pk ct fl).
    - exact HS.
    - unfold call_pre_k. split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact RA|].
      split; [rewrite SPR; Z.div_mod_to_equations; lia|]. split; [rewrite SPR; kc|]. split; [lia|].
      split; [intros a Ha; rewrite HS; apply HSC; left; kc|].
      split; [exact TP|]. split; [intros a Ha; rewrite HS; apply HSC; right; exact Ha|].
      intros H. rewrite INIT in H. discriminate.
    - exact INIT.
    - rewrite US. lia.
    - exact FRM.
    - exact HMI.
    - destruct (ax_statics AX L A m md HM) as (G0 & (g & _ & Wg) & _). split; [exact G0 | exists g; exact Wg].
    - rewrite UT. split; [exact CT|]. split; [exact NZT | apply SLK].
    - rewrite UU. split; [exact CU|]. split; [exact NZU | apply SLU].
    - rewrite UT. left. exists ta, (Z.of_nat (length tb) + 18). split; [exact INT | lia].
    - rewrite UU. left. exists ua, (Z.of_nat (length ub) + 18). split; [exact INU | lia].
    - rewrite UT. exact TL.
    - rewrite UU. exact UL.
    - lia.
    - exact LU.
    - exact (img_strings_agree mem0 m MI0 HMI IMG0).
    - unfold off_stack. rewrite US, UT, SL. left. kc.
    - unfold off_stack. rewrite US, UU, SLb. left. kc.
    - unfold off_stack. rewrite US. unfold PREFIX_LC_STR. left. kc.
    - unfold off_stack. rewrite US. unfold PREFIX_UC_STR. left. kc.
    - unfold off_stack. rewrite US. unfold FMT_WHOLE_STR. left. kc.
    - rewrite UT, SL. apply (off_statics_block L A m md ta _ _ HM INT); lia.
    - rewrite UU, SLb. apply (off_statics_block L A m md ua _ _ HM INU); lia.
    - exact LG.
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' (f' & L' & A' & R' & m' & md' & res & -> & FRM' & INIT' & BP & R10' & _ & _ & ARMS & RES').
  pose proof BP as (HM' & HWF' & HBD' & RP & HMD' & HBL & HBB & HFR' & HSC' & MI' & _).
  rewrite HS in HBB, HFR', HSC', MI'.
  assert (JV : jinv B API L0 A0 regs0 mem0 md0 L' A' m' md').
  { apply (jinv_step B API AX L0 A0 regs0 mem0 md0 L A m md L' A' m' md' NAMES_K (spZ R) stat_writes
             J HM' HWF' HBD' HMD').
    + kc.
    + kc.
    + kc.
    + intros a Ha. right. exact Ha.
    + intros a Hr H1 H2 H3 H4. apply HFR'; assumption.
    + intros a Ha. apply HSC'. exact Ha.
    + intros a k i Ha Hi. exact (HBB a k i (HP0 _ Ha) Hi).
    + intros x Hx. rewrite HBL. exact (HP0 x Hx).
    + exact MI'. }
  assert (KP : forall a, spZ R <= a < 2 ^ 64 ->
             mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)).
  { intros a Ha. apply HFR'.
    - left. kc.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). kc.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). kc.
    - unfold scratch_k. intros [Hs|Hs]; kc.
    - unfold stat_writes, G_LIVE, G_COUNT, G_FAIL. kc. }
  destruct ARMS as [(Eub & Er & LG') | [(_ & Ecf & _) | (Nub & Ncf & Er & LG')]].
  - subst ub res. destruct (aw_of_ledger _ _ _ _ _ _ _ LG') as (AW' & PK' & _).
    apply (K f' L' A' R' m' md' FRM' INIT' RP R10' JV HBL HBB KP AW' PK' RES').
  - lia.
  - destruct ub as [|u ub']; [exfalso; exact (Nub eq_refl)|]. subst res.
    rewrite (Z.mod_small (ct + 1) (2 ^ 64)) in LG' by lia.
    destruct (aw_of_ledger _ _ _ _ _ _ _ LG') as (AW' & PK' & _).
    apply (K f' L' A' R' m' md' FRM' INIT' RP R10' JV HBL HBB KP AW' PK' RES').
Qed.

Ltac sbl := unfold cno_b4, sb_malloc, sb_free; cbn [sb_live sb_bytes sb_cap]; lia.

Ltac fixrom := try replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite HS; reflexivity).
Ltac rok H := rewrite H; apply ret_ok_even; vm_compute; reflexivity.
Ltac sblc := pose proof CAP_AG_le_CAPMAX; unfold cno_b4, sb_malloc, sb_free, CAPMAX in *; cbn [sb_live sb_bytes sb_cap]; lia.

Lemma cno_core_cf : check_no_overread_contract_cf B API.
Proof.
  first [pose proof (check_no_overread.sep_new B API) as sep_new | pose proof (check_no_overread.sep_new B) as sep_new]. cfeed sep_new.
  first [pose proof (check_no_overread.aw_keep B API) as aw_keep | pose proof (check_no_overread.aw_keep B) as aw_keep]. cfeed aw_keep.
  first [pose proof (check_no_overread.aw_block B API) as aw_block | pose proof (check_no_overread.aw_block B) as aw_block]. cfeed aw_block.
  first [pose proof (check_no_overread.ledger_jinv B API) as ledger_jinv | pose proof (check_no_overread.ledger_jinv B) as ledger_jinv]. cfeed ledger_jinv.
  first [pose proof (check_no_overread.payload_now B API) as payload_now | pose proof (check_no_overread.payload_now B) as payload_now]. cfeed payload_now.
  first [pose proof (check_no_overread.payload_disj B API) as payload_disj | pose proof (check_no_overread.payload_disj B) as payload_disj]. cfeed payload_disj.
  first [pose proof (check_no_overread.jinv_MR B API) as jinv_MR | pose proof (check_no_overread.jinv_MR B) as jinv_MR]. cfeed jinv_MR.
  first [pose proof (check_no_overread.jinv_md B API) as jinv_md | pose proof (check_no_overread.jinv_md B) as jinv_md]. cfeed jinv_md.
  first [pose proof (check_no_overread.jinv_mi B API) as jinv_mi | pose proof (check_no_overread.jinv_mi B) as jinv_mi]. cfeed jinv_mi.
  first [pose proof (check_no_overread.jinv_inc B API) as jinv_inc | pose proof (check_no_overread.jinv_inc B) as jinv_inc]. cfeed jinv_inc.
  first [pose proof (check_no_overread.jinv_copy B API) as jinv_copy | pose proof (check_no_overread.jinv_copy B) as jinv_copy]. cfeed jinv_copy.
  unfold check_no_overread_contract_cf.
  intros L A regs mem md b ub tb Lam peak cnt fail SEG PRE INIT TSZ FRM MI R11 R13 PU PT NZU NZT LU LT IBU IBT IMG LED
    QT RES CAP BY0 BYQ.
  clear SEG.
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hac47.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  destruct QT as (QF & QC0 & QC1).
  pose proof RES as (_ & _ & _ & _ & _ & _ & _ & _ & RL0 & _).
  pose proof CAP as CAPu.
  assert (RM1 : room_ag b (Z.of_nat (length ub) + 18)) by (apply room_ag_of; [apply room_slots_big | |]; sblc).
  assert (RM2 : room_ag (sb_malloc b (Z.of_nat (length ub) + 18)) (Z.of_nat (length tb) + 18))
    by (apply room_ag_of; [apply room_slots_big | |]; sblc).
  assert (RM3 : room_ag (sb_malloc (sb_malloc b (Z.of_nat (length ub) + 18)) (Z.of_nat (length tb) + 18))
    (Z.of_nat (length ub) + 18)) by (apply room_ag_of; [apply room_slots_big | |]; sblc).
  assert (RM4 : room_ag (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length ub) + 18))
    (Z.of_nat (length tb) + 18)) (Z.of_nat (length ub) + 18)) (Z.of_nat (length tb) + 18))
    by (apply room_ag_of; [apply room_slots_big | |]; sblc).
  clear CAPu RL0.
  pose proof LED as (AW0 & PK0 & CT0 & FL0 & _).
  pose proof (zr_word (getr regs 2)) as Rsp. unfold inr64 in Rsp. change (bv_unsigned (getr regs 2)) with (spZ regs) in Rsp.
  pose proof (jinv_init B API HS L A regs mem md PRE MI) as J0.
  destruct (jinv_md _ _ _ _ _ _ _ _ _ J0) as [Hh0 Hl0].
  assert (STK : stk rsegs mem (spZ regs - CNO_K) (spZ regs)).
  { apply stk_of_writable; [kc | lia |]. intros a Ha. rewrite <- HS. apply HWS. exact Ha. }
  eapply evt_SRcf_canon; [ | exact Hh0 | exact Hl0 | ].
  { rewrite canon_mkst. rewrite HS. unfold mkR_of.
    apply evt_normalize; [exact rsegs_wx | exact MI |].
    eapply (cno_s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normalize rsegs mem) (spZ regs - CNO_K)
              (Z.of_nat (length ub))).
    - exact R11.
    - lia.
    - exact (mem_inv_normalize rsegs mem).
    - apply (stk_norm mem _ _ MI); [kc | exact STK].
    - change (bv_unsigned (reg_get regs 2)) with (spZ regs). kc. }
  intros ms1 (can & (s0 & (m1n & Es0 & FRn & MU1n & WM1n & _ & _) & REL & ROS) & EQV). subst s0.
  destruct (rel_eqv _ _ _ _ _ _ _ _ REL EQV) as [EQV' HREL]. clear REL EQV.
  set (m1 := ms_mem can) in *.
  destruct (norm_back mem m1n m1 _ MI HREL ROS MU1n WM1n) as (MU1 & WM1 & MI1).
  pose proof (rw_cells_rel m1 m1n _ _ HREL FRn) as FR.
  clear HREL ROS MU1n WM1n FRn.
  apply eqv_shape in EQV' as [Ems XR]. rewrite Ems. clear Ems.
  destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV1 & RA1 & A01 & _).
  clear XR. set (R1 := ms_regs ms1) in *.
  change (bv_unsigned (reg_get regs 2)) with (spZ regs) in *.
  assert (J1 : jinv B API L A regs mem md L A m1 md).
  { apply (jinv_kindA B API HS AX L A regs mem md L A mem md m1 _ J0 MU1 WM1 MI1 HAC).
    intros x Hx. destruct (Z.lt_ge_cases x (spZ regs - 96)) as [H1|H1]; [left; apply outside_one; lia|].
    destruct (Z.lt_ge_cases x (spZ regs)) as [H2|H2]; [right; left; kc | left; apply outside_one; lia]. }
  assert (AW1 : alloc_words B m1 (lsum Lam) peak cnt fail).
  { apply (alloc_words_munch B mem m1 _ _ _ _ _ AW0 MU1). intros x Hx. apply outside_one. kc. }
  clear MU1 WM1 J0 STK.
  destruct (stage_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV1 HTP ltac:(kc)) as [SP1 TP1].
  assert (RO1 : YK0s.ret_ok (getr R1 1)) by (rok RA1).
  fixrom.
  apply (malloc_call_cf fx L A regs mem md L A R1 m1 md (Z.of_nat (length ub) + 18) b _ J1 INIT HAC H16 H63 SP1 RO1 TP1
           A01 ltac:(lia) RES RM1).
  intros L1 A1 R1' m1' md1 ua RP1 U10 J2 INIT1 RES1 U4096 URNG (ju & RWU) INU NINU RMBU INC1 BK1 KP1.
  pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV1 RP1) as SV1'.
  pose proof (frame_keep m1 m1' _ _ (spZ R1) FR ltac:(kc) (fun a Ha => KP1 a (or_introl Ha))) as FR1.
  pose proof (aw_keep m1 m1' _ _ _ _ (fun a Ha => proj1 (KP1 a (or_intror Ha))) AW1) as AW1'.
  clear FR AW1 KP1 BK1 SV1 RP1 J1 MI1.
  destruct (jinv_md _ _ _ _ _ _ _ _ _ J2) as [Hh2 Hl2].
  rewrite RA1.
  eapply evt_SRcf_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite (canon_saved fx R1' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV1'). rewrite HS.
    apply evt_normalize; [exact rsegs_wx | exact (jinv_mi _ _ _ _ _ _ _ _ _ J2) |].
    eapply (cno_s1 MEMCPY MEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normalize rsegs m1') ua
              (Z.of_nat (length ub)) (Z.of_nat (length tb)) ub ju).
    - exact U10.
    - exact R11.
    - reflexivity.
    - exact R13.
    - exact U4096.
    - lia.
    - lia.
    - lia.
    - reflexivity.
    - exact (bytes_at_normalize rsegs m1' _ _ (jinv_mi _ _ _ _ _ _ _ _ _ J2) (payload_now _ _ _ _ _ _ _ _ _ _ _ J2 PU IBU)).
    - eapply payload_disj; [exact (jinv_MR _ _ _ _ _ _ _ _ _ J2) | exact IBU | exact (jinv_inc _ _ _ _ _ _ _ _ _ J2) |
        exact INU | exact NINU].
    - exact RWU.
    - exact (mem_inv_normalize rsegs m1'). }
  intros ms2 (can2 & (s0 & (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2n & Es0 & CPUn & MU2n & WM2n & _) &
    REL & ROS) & EQV). subst s0.
  destruct (rel_eqv _ _ _ _ _ _ _ _ REL EQV) as [EQV' HREL]. clear REL EQV.
  set (m2 := ms_mem can2) in *.
  destruct (norm_back m1' m2n m2 _ (jinv_mi _ _ _ _ _ _ _ _ _ J2) HREL ROS MU2n WM2n) as (MU2 & WM2 & MI2).
  pose proof (proj2 (bytes_at_rel rsegs m2 m2n _ _ HREL) CPUn) as CPU.
  clear HREL ROS MU2n WM2n CPUn.
  apply eqv_shape in EQV' as [Ems XR]. rewrite Ems. clear Ems.
  destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV2 & RA2 & A02 & _).
  clear XR. set (R2 := ms_regs ms2) in *.
  pose proof (jinv_copy L A regs mem md L1 A1 m1' md1 m2 ua _ (cpy ub 97) J2 MU2 WM2 MI2 HAC INU NINU CPU
                (cpy_length _ _)) as J3.
  pose proof (frame_copy m1' m2 _ _ ua _ FR1 MU2 WM2 ltac:(kc)) as FR2.
  pose proof (aw_block L1 A1 m1' md1 m1' m2 ua _ _ _ _ _ (jinv_MR _ _ _ _ _ _ _ _ _ J2) INU MU2 AW1') as AW2.
  clear FR1 AW1' MU2 WM2 J2 RWU SV1'.
  destruct (stage_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV2 HTP ltac:(kc)) as [SP2 TP2].
  assert (RO2 : YK0s.ret_ok (getr R2 1)) by (rok RA2).
  fixrom.
  apply (malloc_call_cf fx L A regs mem md L1 A1 R2 m2 md1 (Z.of_nat (length tb) + 18)
           (sb_malloc b (Z.of_nat (length ub) + 18)) _ J3 INIT1 HAC H16 H63 SP2 RO2 TP2 A02 ltac:(lia) RES1 RM2).
  intros L2 A2 R2' m2' md2 ta RP2 T10 J4 INIT2 RES2 T4096 TRNG (jt & RWT) INT NINT RMBT INC2 BK2 KP2.
  pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV2 RP2) as SV2'.
  pose proof (frame_keep m2 m2' _ _ (spZ R2) FR2 ltac:(kc) (fun a Ha => KP2 a (or_introl Ha))) as FR2'.
  pose proof (aw_keep m2 m2' _ _ _ _ (fun a Ha => proj1 (KP2 a (or_intror Ha))) AW2) as AW2'.
  pose proof (bytes_blk m2 m2' ua (cpy ub 97) (blocks L1 A1) _ CPU INU ltac:(rewrite cpy_length; lia) BK2) as CPU2.
  assert (NINT0 : ~ In (ta, Z.of_nat (length tb) + 18) (blocks L A)) by (intros H; exact (NINT (INC1 _ H))).
  clear FR2 AW2 KP2 BK2 SV2 RP2 J3 CPU MI2.
  destruct (jinv_md _ _ _ _ _ _ _ _ _ J4) as [Hh4 Hl4].
  rewrite RA2.
  eapply evt_SRcf_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite (canon_saved fx R2' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV2'). rewrite HS.
    apply evt_normalize; [exact rsegs_wx | exact (jinv_mi _ _ _ _ _ _ _ _ _ J4) |].
    eapply (cno_s2 MEMCPY MEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normalize rsegs m2') ta
              (Z.of_nat (length ub)) (Z.of_nat (length tb)) tb jt).
    - exact T10.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact T4096.
    - lia.
    - lia.
    - lia.
    - reflexivity.
    - exact (bytes_at_normalize rsegs m2' _ _ (jinv_mi _ _ _ _ _ _ _ _ _ J4) (payload_now _ _ _ _ _ _ _ _ _ _ _ J4 PT IBT)).
    - eapply payload_disj; [exact (jinv_MR _ _ _ _ _ _ _ _ _ J4) | exact IBT | exact (jinv_inc _ _ _ _ _ _ _ _ _ J4) |
        exact INT | exact NINT0].
    - exact RWT.
    - exact (mem_inv_normalize rsegs m2'). }
  intros ms3 (can3 & (s0 & (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3n & Es0 & CPTn & MU3n & WM3n & _) &
    REL & ROS) & EQV). subst s0.
  destruct (rel_eqv _ _ _ _ _ _ _ _ REL EQV) as [EQV' HREL]. clear REL EQV.
  set (m3 := ms_mem can3) in *.
  destruct (norm_back m2' m3n m3 _ (jinv_mi _ _ _ _ _ _ _ _ _ J4) HREL ROS MU3n WM3n) as (MU3 & WM3 & MI3).
  pose proof (proj2 (bytes_at_rel rsegs m3 m3n _ _ HREL) CPTn) as CPT.
  clear HREL ROS MU3n WM3n CPTn.
  apply eqv_shape in EQV' as [Ems XR]. rewrite Ems. clear Ems.
  destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV3 & RA3 & A03 & _).
  clear XR. set (R3 := ms_regs ms3) in *.
  pose proof (jinv_copy L A regs mem md L2 A2 m2' md2 m3 ta _ (cpy tb 97) J4 MU3 WM3 MI3 HAC INT NINT0 CPT
                (cpy_length _ _)) as J5.
  pose proof (frame_copy m2' m3 _ _ ta _ FR2' MU3 WM3 ltac:(kc)) as FR3.
  pose proof (aw_block L2 A2 m2' md2 m2' m3 ta _ _ _ _ _ (jinv_MR _ _ _ _ _ _ _ _ _ J4) INT MU3 AW2') as AW3.
  pose proof (sep_new L2 A2 m2' md2 (blocks L1 A1) _ _ (jinv_MR _ _ _ _ _ _ _ _ _ J4) (INC2 _ INU) INT INU NINT) as D12.
  cbn [fst snd] in D12.
  pose proof (bytes_copy m2' m3 ua (cpy ub 97) ta _ CPU2 MU3 ltac:(rewrite cpy_length; lia)) as CPU3.
  clear FR2' AW2' MU3 WM3 J4 RWT SV2' CPU2.
  destruct (stage_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV3 HTP ltac:(kc)) as [SP3 TP3].
  assert (RO3 : YK0s.ret_ok (getr R3 1)) by (rok RA3).
  fixrom.
  apply (malloc_call_cf fx L A regs mem md L2 A2 R3 m3 md2 (Z.of_nat (length ub) + 18)
           (sb_malloc (sb_malloc b (Z.of_nat (length ub) + 18)) (Z.of_nat (length tb) + 18)) _ J5 INIT2 HAC H16 H63
           SP3 RO3 TP3 A03 ltac:(lia) RES2 RM3).
  intros L3 A3 R3' m3' md3 ub0 RP3 V10 J6 INIT3 RES3 V4096 VRNG (jv & RWV) INV NINV RMBV INC3 BK3 KP3.
  pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV3 RP3) as SV3'.
  pose proof (frame_keep m3 m3' _ _ (spZ R3) FR3 ltac:(kc) (fun a Ha => KP3 a (or_introl Ha))) as FR3'.
  pose proof (aw_keep m3 m3' _ _ _ _ (fun a Ha => proj1 (KP3 a (or_intror Ha))) AW3) as AW3'.
  pose proof (bytes_blk m3 m3' ua (cpy ub 97) (blocks L2 A2) _ CPU3 (INC2 _ INU) ltac:(rewrite cpy_length; lia) BK3) as CPU3'.
  pose proof (bytes_blk m3 m3' ta (cpy tb 97) (blocks L2 A2) _ CPT INT ltac:(rewrite cpy_length; lia) BK3) as CPT3.
  assert (NINV0 : ~ In (ub0, Z.of_nat (length ub) + 18) (blocks L A)) by (intros H; exact (NINV (INC2 _ (INC1 _ H)))).
  clear FR3 AW3 KP3 BK3 SV3 RP3 J5 CPU3 CPT MI3.
  destruct (jinv_md _ _ _ _ _ _ _ _ _ J6) as [Hh6 Hl6].
  rewrite RA3.
  eapply evt_SRcf_canon; [ | exact Hh6 | exact Hl6 | ].
  { rewrite (canon_saved fx R3' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV3'). rewrite HS.
    apply evt_normalize; [exact rsegs_wx | exact (jinv_mi _ _ _ _ _ _ _ _ _ J6) |].
    eapply (cno_s3 MEMCPY MEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normalize rsegs m3') ub0
              (Z.of_nat (length ub)) (Z.of_nat (length tb)) ub jv).
    - exact V10.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact V4096.
    - lia.
    - lia.
    - lia.
    - reflexivity.
    - exact (bytes_at_normalize rsegs m3' _ _ (jinv_mi _ _ _ _ _ _ _ _ _ J6) (payload_now _ _ _ _ _ _ _ _ _ _ _ J6 PU IBU)).
    - eapply payload_disj; [exact (jinv_MR _ _ _ _ _ _ _ _ _ J6) | exact IBU | exact (jinv_inc _ _ _ _ _ _ _ _ _ J6) |
        exact INV | exact NINV0].
    - exact RWV.
    - exact (mem_inv_normalize rsegs m3'). }
  intros ms4 (can4 & (s0 & (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4n & Es0 & CPVn & MU4n & WM4n & _) &
    REL & ROS) & EQV). subst s0.
  destruct (rel_eqv _ _ _ _ _ _ _ _ REL EQV) as [EQV' HREL]. clear REL EQV.
  set (m4 := ms_mem can4) in *.
  destruct (norm_back m3' m4n m4 _ (jinv_mi _ _ _ _ _ _ _ _ _ J6) HREL ROS MU4n WM4n) as (MU4 & WM4 & MI4).
  pose proof (proj2 (bytes_at_rel rsegs m4 m4n _ _ HREL) CPVn) as CPV.
  clear HREL ROS MU4n WM4n CPVn.
  apply eqv_shape in EQV' as [Ems XR]. rewrite Ems. clear Ems.
  destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV4 & RA4 & A04 & _).
  clear XR. set (R4 := ms_regs ms4) in *.
  pose proof (jinv_copy L A regs mem md L3 A3 m3' md3 m4 ub0 _ (cpy ub 0) J6 MU4 WM4 MI4 HAC INV NINV0 CPV
                (cpy_length _ _)) as J7.
  pose proof (frame_copy m3' m4 _ _ ub0 _ FR3' MU4 WM4 ltac:(kc)) as FR4.
  pose proof (aw_block L3 A3 m3' md3 m3' m4 ub0 _ _ _ _ _ (jinv_MR _ _ _ _ _ _ _ _ _ J6) INV MU4 AW3') as AW4.
  pose proof (sep_new L3 A3 m3' md3 (blocks L2 A2) _ _ (jinv_MR _ _ _ _ _ _ _ _ _ J6) (INC3 _ (INC2 _ INU)) INV
                (INC2 _ INU) NINV) as D13.
  pose proof (sep_new L3 A3 m3' md3 (blocks L2 A2) _ _ (jinv_MR _ _ _ _ _ _ _ _ _ J6) (INC3 _ INT) INV INT NINV) as D23.
  cbn [fst snd] in D13, D23.
  pose proof (bytes_copy m3' m4 ua (cpy ub 97) ub0 _ CPU3' MU4 ltac:(rewrite cpy_length; lia)) as CPU4.
  pose proof (bytes_copy m3' m4 ta (cpy tb 97) ub0 _ CPT3 MU4 ltac:(rewrite cpy_length; lia)) as CPT4.
  clear FR3' AW3' MU4 WM4 J6 RWV SV3' CPU3' CPT3.
  destruct (stage_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV4 HTP ltac:(kc)) as [SP4 TP4].
  assert (RO4 : YK0s.ret_ok (getr R4 1)) by (rok RA4).
  fixrom.
  apply (malloc_call_cf fx L A regs mem md L3 A3 R4 m4 md3 (Z.of_nat (length tb) + 18)
           (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length ub) + 18)) (Z.of_nat (length tb) + 18))
              (Z.of_nat (length ub) + 18)) _ J7 INIT3 HAC H16 H63 SP4 RO4 TP4 A04 ltac:(lia) RES3 RM4).
  intros L4 A4 R4' m4' md4 tb0 RP4 W10 J8 INIT4 RES4 W4096 WRNG (jw & RWW) INW NINW RMBW INC4 BK4 KP4.
  pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV4 RP4) as SV4'.
  pose proof (frame_keep m4 m4' _ _ (spZ R4) FR4 ltac:(kc) (fun a Ha => KP4 a (or_introl Ha))) as FR4'.
  pose proof (aw_keep m4 m4' _ _ _ _ (fun a Ha => proj1 (KP4 a (or_intror Ha))) AW4) as AW4'.
  pose proof (bytes_blk m4 m4' ua (cpy ub 97) (blocks L3 A3) _ CPU4 (INC3 _ (INC2 _ INU))
                ltac:(rewrite cpy_length; lia) BK4) as CPU4'.
  pose proof (bytes_blk m4 m4' ta (cpy tb 97) (blocks L3 A3) _ CPT4 (INC3 _ INT) ltac:(rewrite cpy_length; lia) BK4) as CPT4'.
  pose proof (bytes_blk m4 m4' ub0 (cpy ub 0) (blocks L3 A3) _ CPV INV ltac:(rewrite cpy_length; lia) BK4) as CPV4.
  assert (NINW0 : ~ In (tb0, Z.of_nat (length tb) + 18) (blocks L A))
    by (intros H; exact (NINW (INC3 _ (INC2 _ (INC1 _ H))))).
  clear FR4 AW4 KP4 BK4 SV4 RP4 J7 CPU4 CPT4 CPV MI4.
  destruct (jinv_md _ _ _ _ _ _ _ _ _ J8) as [Hh8 Hl8].
  rewrite RA4.
  eapply evt_SRcf_canon; [ | exact Hh8 | exact Hl8 | ].
  { rewrite (canon_saved fx R4' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV4'). rewrite HS.
    apply evt_normalize; [exact rsegs_wx | exact (jinv_mi _ _ _ _ _ _ _ _ _ J8) |].
    eapply (cno_s4 MEMCPY MEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normalize rsegs m4') tb0
              (Z.of_nat (length tb)) tb jw).
    - exact W10.
    - reflexivity.
    - reflexivity.
    - exact W4096.
    - lia.
    - lia.
    - reflexivity.
    - exact (bytes_at_normalize rsegs m4' _ _ (jinv_mi _ _ _ _ _ _ _ _ _ J8) (payload_now _ _ _ _ _ _ _ _ _ _ _ J8 PT IBT)).
    - eapply payload_disj; [exact (jinv_MR _ _ _ _ _ _ _ _ _ J8) | exact IBT | exact (jinv_inc _ _ _ _ _ _ _ _ _ J8) |
        exact INW | exact NINW0].
    - exact RWW.
    - exact (mem_inv_normalize rsegs m4'). }
  intros ms5 (can5 & (s0 & (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5n & Es0 & CPWn & MU5n & WM5n & _) &
    REL & ROS) & EQV). subst s0.
  destruct (rel_eqv _ _ _ _ _ _ _ _ REL EQV) as [EQV' HREL]. clear REL EQV.
  set (m5 := ms_mem can5) in *.
  destruct (norm_back m4' m5n m5 _ (jinv_mi _ _ _ _ _ _ _ _ _ J8) HREL ROS MU5n WM5n) as (MU5 & WM5 & MI5).
  pose proof (proj2 (bytes_at_rel rsegs m5 m5n _ _ HREL) CPWn) as CPW.
  clear HREL ROS MU5n WM5n CPWn.
  apply eqv_shape in EQV' as [Ems XR]. rewrite Ems. clear Ems.
  destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV5 & RA5 & A05 & A15).
  clear XR. set (R5 := ms_regs ms5) in *.
  pose proof (jinv_copy L A regs mem md L4 A4 m4' md4 m5 tb0 _ (cpy tb 0) J8 MU5 WM5 MI5 HAC INW NINW0 CPW
                (cpy_length _ _)) as J9.
  pose proof (frame_copy m4' m5 _ _ tb0 _ FR4' MU5 WM5 ltac:(kc)) as FR5.
  pose proof (aw_block L4 A4 m4' md4 m4' m5 tb0 _ _ _ _ _ (jinv_MR _ _ _ _ _ _ _ _ _ J8) INW MU5 AW4') as AW5.
  assert (INU4 : In (ua, Z.of_nat (length ub) + 18) (blocks L4 A4)) by exact (INC4 _ (INC3 _ (INC2 _ INU))).
  assert (INT4 : In (ta, Z.of_nat (length tb) + 18) (blocks L4 A4)) by exact (INC4 _ (INC3 _ INT)).
  assert (INV4 : In (ub0, Z.of_nat (length ub) + 18) (blocks L4 A4)) by exact (INC4 _ INV).
  pose proof (sep_new L4 A4 m4' md4 (blocks L3 A3) _ _ (jinv_MR _ _ _ _ _ _ _ _ _ J8) INU4 INW
                (INC3 _ (INC2 _ INU)) NINW) as D14.
  pose proof (sep_new L4 A4 m4' md4 (blocks L3 A3) _ _ (jinv_MR _ _ _ _ _ _ _ _ _ J8) INT4 INW (INC3 _ INT) NINW) as D24.
  pose proof (sep_new L4 A4 m4' md4 (blocks L3 A3) _ _ (jinv_MR _ _ _ _ _ _ _ _ _ J8) INV4 INW INV NINW) as D34.
  cbn [fst snd] in D14, D24, D34.
  pose proof (bytes_copy m4' m5 ua (cpy ub 97) tb0 _ CPU4' MU5 ltac:(rewrite cpy_length; lia)) as CPU5.
  pose proof (bytes_copy m4' m5 ta (cpy tb 97) tb0 _ CPT4' MU5 ltac:(rewrite cpy_length; lia)) as CPT5.
  pose proof (bytes_copy m4' m5 ub0 (cpy ub 0) tb0 _ CPV4 MU5 ltac:(rewrite cpy_length; lia)) as CPV5.
  clear FR4' AW4' MU5 WM5 J8 RWW SV4' CPU4' CPT4' CPV4.
  destruct (stage_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV5 HTP ltac:(kc)) as [SP5 TP5].
  assert (RO5 : YK0s.ret_ok (getr R5 1)) by (rok RA5).
  fixrom.
  apply (names_call_cf fx L A regs mem md L4 A4 R5 m5 md4 (cno_b4 b (Z.of_nat (length ub)) (Z.of_nat (length tb))) ub tb
           Lam peak cnt fail peak cnt ta ua 97 97 _ J9 INIT4 FRM LED IMG MI HAC H16 H63 TSZ SP5 RO5 TP5 A05 A15 CPT5 CPU5
           INT4 INU4 NZT NZU LU LT AW5 PK0 QC0 ltac:(lia) QF RES4 ltac:(sbl) ltac:(sbl) ltac:(sbl)).
  intros f5 L5 A5 R5' m5' md5 FRM5 INIT5 RP5 N10 J10 BL5 BK5 KP5 AW5' PK5 RES5.
  pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV5 RP5) as SV5'.
  pose proof (frame_keep m5 m5' _ _ (spZ R5) FR5 ltac:(kc) KP5) as FR5'.
  pose proof (bytes_blk m5 m5' ub0 (cpy ub 0) (blocks L4 A4) _ CPV5 INV4 ltac:(rewrite cpy_length; lia) BK5) as CPV5'.
  pose proof (bytes_blk m5 m5' tb0 (cpy tb 0) (blocks L4 A4) _ CPW INW ltac:(rewrite cpy_length; lia) BK5) as CPW5.
  clear FR5 AW5 KP5 BK5 SV5 RP5 J9 CPU5 CPT5 CPV5 CPW MI5.
  destruct (jinv_md _ _ _ _ _ _ _ _ _ J10) as [Hh10 Hl10].
  rewrite RA5.
  eapply evt_SRcf_canon; [ | exact Hh10 | exact Hl10 | ].
  { rewrite (canon_saved f5 R5' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV5'). rewrite HS. apply cno_s5. }
  intros ms6 (can6 & Ecan & EQV). subst can6. apply eqv_shape in EQV as [Ems XR]. rewrite Ems. clear Ems.
  destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV6 & RA6 & A06 & A16).
  clear XR. set (R6 := ms_regs ms6) in *.
  destruct (stage_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV6 HTP ltac:(kc)) as [SP6 TP6].
  assert (RO6 : YK0s.ret_ok (getr R6 1)) by (rok RA6).
  assert (INW5 : In (tb0, Z.of_nat (length tb) + 18) (blocks L5 A5)) by (rewrite BL5; exact INW).
  assert (INV5 : In (ub0, Z.of_nat (length ub) + 18) (blocks L5 A5)) by (rewrite BL5; exact INV4).
  assert (C0' : 0 <= ub_case ub cnt (cnt + 1)) by (destruct (ub_case_split ub cnt (cnt + 1)) as [[_ E]|[_ E]]; rewrite E; lia).
  assert (C1' : ub_case ub cnt (cnt + 1) + 1 < 2 ^ 63)
    by (destruct (ub_case_split ub cnt (cnt + 1)) as [[_ E]|[_ E]]; rewrite E; lia).
  fixrom.
  apply (names_call_cf f5 L A regs mem md L5 A5 R6 m5' md5
           (cno_b4 b (Z.of_nat (length ub)) (Z.of_nat (length tb))) ub tb
           Lam peak cnt fail (ub_case ub peak (Z.max peak (lsum Lam + Z.of_nat (length ub) + 3)))
           (ub_case ub cnt (cnt + 1)) tb0 ub0 0 0 _ J10 INIT5 FRM5 LED IMG MI HAC H16 H63 TSZ SP6 RO6 TP6 A06 A16 CPW5
           CPV5' INW5 INV5 NZT NZU LU LT AW5' PK5 C0' C1' QF RES5 ltac:(sbl) ltac:(sbl) ltac:(sbl)).
  intros f6 L6 A6 R6' m6 md6 FRM6 INIT6 RP6 N10' J11 BL6 BK6 KP6 AW6 PK6 RES6.
  pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV6 RP6) as SV6'.
  pose proof (frame_keep m5' m6 _ _ (spZ R6) FR5' ltac:(kc) KP6) as FR6.
  clear FR5' AW5' KP6 BK6 SV6 RP6 J10 CPV5' CPW5.
  destruct (jinv_md _ _ _ _ _ _ _ _ _ J11) as [Hh11 Hl11].
  rewrite RA6.
  eapply evt_SRcf_canon; [ | exact Hh11 | exact Hl11 | ].
  { rewrite (canon_saved f6 R6' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV6'). rewrite HS. apply cno_s6.
    transitivity (Z_to_bv 64 (ub_case ub 0 (names (ManifestMem.zbytes tb) (ManifestMem.zbytes ub))));
      [exact N10 | symmetry; exact N10']. }
  intros ms7 (can7 & Ecan & EQV). subst can7. apply eqv_shape in EQV as [Ems XR]. rewrite Ems. clear Ems.
  destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV7 & RA7 & A07 & _).
  clear XR. set (R7 := ms_regs ms7) in *.
  destruct (stage_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV7 HTP ltac:(kc)) as [SP7 TP7].
  assert (RO7 : YK0s.ret_ok (getr R7 1)) by (rok RA7).
  assert (INU6 : In (ua, Z.of_nat (length ub) + 18) (blocks L6 A6)) by (rewrite BL6, BL5; exact INU4).
  fixrom.
  apply (free_call_cf f6 L A regs mem md L6 A6 R7 m6 md6 ua (Z.of_nat (length ub) + 18)
           (cno_b4 b (Z.of_nat (length ub)) (Z.of_nat (length tb)))
              _ J11 INIT6 HAC H63 ltac:(rewrite SP7; Z.div_mod_to_equations; lia)
           ltac:(rewrite SP7; kc) ltac:(lia) RO7 TP7 A07 INU6 NINU ltac:(lia) RES6).
  intros L7 A7 R7' m7 md7 RP7 J12 INIT7 RES7 BL7 BK7 KP7.
  pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV7 RP7) as SV7'.
  pose proof (frame_keep m6 m7 _ _ (spZ R7) FR6 ltac:(kc) (fun a Ha => KP7 a (or_introl Ha))) as FR7.
  pose proof (aw_keep m6 m7 _ _ _ _ (fun a Ha => proj1 (KP7 a (or_intror Ha))) AW6) as AW7.
  clear FR6 AW6 KP7 BK7 SV7 RP7 J11.
  destruct (jinv_md _ _ _ _ _ _ _ _ _ J12) as [Hh12 Hl12].
  rewrite RA7.
  eapply evt_SRcf_canon; [ | exact Hh12 | exact Hl12 | ].
  { rewrite (canon_saved f6 R7' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV7'). rewrite HS. apply cno_s7. }
  intros ms8 (can8 & Ecan & EQV). subst can8. apply eqv_shape in EQV as [Ems XR]. rewrite Ems. clear Ems.
  destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV8 & RA8 & A08 & _).
  clear XR. set (R8 := ms_regs ms8) in *.
  destruct (stage_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV8 HTP ltac:(kc)) as [SP8 TP8].
  assert (RO8 : YK0s.ret_ok (getr R8 1)) by (rok RA8).
  assert (NEta : (ta, Z.of_nat (length tb) + 18) <> (ua, Z.of_nat (length ub) + 18))
    by (intros E; rewrite E in NINT; exact (NINT INU)).
  assert (INT7 : In (ta, Z.of_nat (length tb) + 18) (blocks L7 A7))
    by (rewrite BL7, BL6, BL5; apply rmb_in; [exact INT4 | exact NEta]).
  fixrom.
  apply (free_call_cf f6 L A regs mem md L7 A7 R8 m7 md7 ta (Z.of_nat (length tb) + 18)
           (sb_free (cno_b4 b (Z.of_nat (length ub)) (Z.of_nat (length tb))) (Z.of_nat (length ub) + 18)) _
           J12 INIT7 HAC H63 ltac:(rewrite SP8; Z.div_mod_to_equations; lia)
           ltac:(rewrite SP8; kc) ltac:(lia) RO8 TP8 A08 INT7 NINT0 ltac:(lia) RES7).
  intros L8 A8 R8' m8 md8 RP8 J13 INIT8 RES8 BL8 BK8 KP8.
  pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV8 RP8) as SV8'.
  pose proof (frame_keep m7 m8 _ _ (spZ R8) FR7 ltac:(kc) (fun a Ha => KP8 a (or_introl Ha))) as FR8.
  pose proof (aw_keep m7 m8 _ _ _ _ (fun a Ha => proj1 (KP8 a (or_intror Ha))) AW7) as AW8.
  clear FR7 AW7 KP8 BK8 SV8 RP8 J12.
  destruct (jinv_md _ _ _ _ _ _ _ _ _ J13) as [Hh13 Hl13].
  rewrite RA8.
  eapply evt_SRcf_canon; [ | exact Hh13 | exact Hl13 | ].
  { rewrite (canon_saved f6 R8' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV8'). rewrite HS. apply cno_s8. }
  intros ms9 (can9 & Ecan & EQV). subst can9. apply eqv_shape in EQV as [Ems XR]. rewrite Ems. clear Ems.
  destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV9 & RA9 & A09 & _).
  clear XR. set (R9 := ms_regs ms9) in *.
  destruct (stage_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV9 HTP ltac:(kc)) as [SP9 TP9].
  assert (RO9 : YK0s.ret_ok (getr R9 1)) by (rok RA9).
  assert (NEva : (ub0, Z.of_nat (length ub) + 18) <> (ua, Z.of_nat (length ub) + 18))
    by (intros E; rewrite E in NINV; exact (NINV (INC2 _ INU))).
  assert (NEvt : (ub0, Z.of_nat (length ub) + 18) <> (ta, Z.of_nat (length tb) + 18))
    by (intros E; rewrite E in NINV; exact (NINV INT)).
  assert (INV8 : In (ub0, Z.of_nat (length ub) + 18) (blocks L8 A8))
    by (rewrite BL8, BL7, BL6, BL5; apply rmb_in; [apply rmb_in; [exact INV4 | exact NEva] | exact NEvt]).
  fixrom.
  apply (free_call_cf f6 L A regs mem md L8 A8 R9 m8 md8 ub0 (Z.of_nat (length ub) + 18)
           (sb_free (sb_free (cno_b4 b (Z.of_nat (length ub)) (Z.of_nat (length tb))) (Z.of_nat (length ub) + 18))
              (Z.of_nat (length tb) + 18)) _
           J13 INIT8 HAC H63 ltac:(rewrite SP9; Z.div_mod_to_equations; lia)
           ltac:(rewrite SP9; kc) ltac:(lia) RO9 TP9 A09 INV8 NINV0 ltac:(lia) RES8).
  intros L9 A9 R9' m9 md9 RP9 J14 INIT9 RES9 BL9 BK9 KP9.
  pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV9 RP9) as SV9'.
  pose proof (frame_keep m8 m9 _ _ (spZ R9) FR8 ltac:(kc) (fun a Ha => KP9 a (or_introl Ha))) as FR9.
  pose proof (aw_keep m8 m9 _ _ _ _ (fun a Ha => proj1 (KP9 a (or_intror Ha))) AW8) as AW9.
  clear FR8 AW8 KP9 BK9 SV9 RP9 J13.
  destruct (jinv_md _ _ _ _ _ _ _ _ _ J14) as [Hh14 Hl14].
  rewrite RA9.
  eapply evt_SRcf_canon; [ | exact Hh14 | exact Hl14 | ].
  { rewrite (canon_saved f6 R9' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV9'). rewrite HS. apply cno_s9.
    rewrite unsigned_lit by kc. exact FR9. }
  intros ms10 (can10 & Ecan & EQV). subst can10. apply eqv_shape in EQV as [Ems XR]. rewrite Ems. clear Ems.
  destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV10 & RA10 & A010 & _).
  clear XR. set (R10 := ms_regs ms10) in *.
  assert (ESP : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (spZ regs + -96)) + 96) = getr regs 2).
  { rewrite unsigned_lit by kc. replace (spZ regs + -96 + 96) with (spZ regs) by lia. unfold spZ.
    apply Z_to_bv_bv_unsigned. }
  rewrite ESP in SV10.
  assert (SP10 : spZ R10 = spZ regs) by (unfold spZ at 1; rewrite (proj1 SV10); reflexivity).
  assert (TP10 : getr R10 4 = Z_to_bv 64 (ms_tp B)) by (rewrite (proj1 (proj2 (proj2 SV10))); exact HTP).
  assert (RO10 : YK0s.ret_ok (getr R10 1)) by (rewrite RA10; exact HRA).
  assert (NEwa : (tb0, Z.of_nat (length tb) + 18) <> (ua, Z.of_nat (length ub) + 18))
    by (intros E; rewrite E in NINW; exact (NINW (INC3 _ (INC2 _ INU)))).
  assert (NEwt : (tb0, Z.of_nat (length tb) + 18) <> (ta, Z.of_nat (length tb) + 18))
    by (intros E; rewrite E in NINW; exact (NINW (INC3 _ INT))).
  assert (NEwv : (tb0, Z.of_nat (length tb) + 18) <> (ub0, Z.of_nat (length ub) + 18))
    by (intros E; rewrite E in NINW; exact (NINW INV)).
  assert (INW9 : In (tb0, Z.of_nat (length tb) + 18) (blocks L9 A9)).
  { rewrite BL9, BL8, BL7, BL6, BL5. apply rmb_in; [apply rmb_in; [apply rmb_in; [exact INW | exact NEwa] |
      exact NEwt] | exact NEwv]. }
  fixrom.
  apply (free_call_cf f6 L A regs mem md L9 A9 R10 m9 md9 tb0 (Z.of_nat (length tb) + 18)
           (sb_free (sb_free (sb_free (cno_b4 b (Z.of_nat (length ub)) (Z.of_nat (length tb)))
              (Z.of_nat (length ub) + 18)) (Z.of_nat (length tb) + 18)) (Z.of_nat (length ub) + 18)) _
           J14 INIT9 HAC H63 ltac:(rewrite SP10; exact H16) ltac:(rewrite SP10; kc) ltac:(lia) RO10 TP10 A010 INW9
           NINW0 ltac:(lia) RES9).
  intros L10 A10 R10' m10 md10 RP10 J15 INIT10 RES10 BL10 BK10 KP10.
  pose proof (aw_keep m9 m10 _ _ _ _ (fun a Ha => proj1 (KP10 a (or_intror Ha))) AW9) as AW10.
  rewrite RA10. apply SRcf_ret. unfold cno_post.
  exists f6, L10, A10, R10', m10, md10.
  split; [reflexivity|]. split; [exact FRM6|]. split; [exact INIT10|].
  split.
  { apply (jinv_bpost B API HS AX L A regs mem md L10 A10 m10 md10 R10' CTX HM J15).
    - apply preserved_of_saved. exact (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV10 RP10).
    - rewrite BL10, BL9, BL8, BL7, BL6, BL5.
      exact (rmb4 _ _ _ _ (blocks L A) (blocks L1 A1) (blocks L2 A2) (blocks L3 A3) (blocks L4 A4) RMBW RMBV RMBT RMBU). }
  split; [exact (payload_now _ _ _ _ _ _ _ _ _ _ _ J15 PU IBU)|].
  split; [exact (payload_now _ _ _ _ _ _ _ _ _ _ _ J15 PT IBT)|].
  assert (EB : sb_free (sb_free (sb_free (sb_free (cno_b4 b (Z.of_nat (length ub)) (Z.of_nat (length tb)))
    (Z.of_nat (length ub) + 18)) (Z.of_nat (length tb) + 18)) (Z.of_nat (length ub) + 18))
    (Z.of_nat (length tb) + 18) = b) by (destruct b; unfold cno_b4, sb_free, sb_malloc; cbn; f_equal; lia).
  rewrite EB in RES10.
  split; [|exact RES10].
  destruct ub as [|u ub'].
  - left. split; [reflexivity|]. cbn [ub_case] in AW10, PK6.
    apply (ledger_jinv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LED J15 AW10 PK6). lia.
  - right. split; [discriminate|]. cbn [ub_case] in AW10, PK6.
    set (X := lsum Lam + Z.of_nat (length (u :: ub')) + 3) in *.
    replace (Z.max (Z.max peak X) X) with (Z.max peak X) in AW10, PK6 by lia.
    replace (cnt + 1 + 1) with (cnt + 2) in AW10 by lia.
    apply (ledger_jinv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LED J15 AW10 PK6). lia.
Qed.


End H.

Lemma cno_holds_cf : check_no_overread_contract_cf B API.
Proof.
  intros L A regs mem md b ub tb Lam peak cnt fail SEG.
  exact (cno_core_cf SEG L A regs mem md b ub tb Lam peak cnt fail SEG).
Qed.

End P.

Theorem check_no_overread_cf_holds {fx : YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) :
  AllocExtra B (aa_MR API) -> ctx_owned B (aa_MR API) -> statics_facts B -> statics_free B (aa_MR API) ->
  errno_low B -> statics_noerrno B -> malloc_syms_omx B ->
  (forall fx' : FPState, @malloc_contract_cf fx' rc B API) -> (forall fx' : FPState, @free_contract_cf fx' rc B API) ->
  memcpy_contract -> memset_contract -> (forall fx' : FPState, @names_contract_cf fx' rc B API) ->
  (forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md)) ->
  check_no_overread_contract_cf B API.
Proof.
  intros AX CTX SF SFR ERR SNE MSO MCF FCF MEMCPY MEMSET NAMES LIMLAW.
  pose proof (cno_holds_cf B API) as H. cfeed H. exact H.
Qed.

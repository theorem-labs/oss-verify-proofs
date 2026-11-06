From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import AgCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import names_c_cf check_no_overread_c_cf check_reject_clean_starved_c_cf check_round_trip_c_cf.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestModel ManifestMem ManifestB names_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import check_no_overread_c check_no_overread_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import check_reject_clean_starved_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import slot_steps_c slot_glue slot_img.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require KindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import slot_kb.
Import ListNotations.
Open Scope Z_scope.

(* The cut-free twins of slot_kb.v's Kind B call wrappers: SRcf in place of SR, the callees through their cut-free
   contracts (<f>_c_cf.v), whose bounds are the agreement ones (sb_cap <= CAP_AG, bytes <= 2^29). *)
Section KBcf.
Context {fx : YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.
Hypothesis SF : statics_facts B.
Hypothesis SFR : statics_free B MR.
Hypothesis ERR : errno_low B.
Hypothesis CNO : forall fx' : FPState, @check_no_overread_contract_cf fx' rc B API.
Hypothesis NAMES : forall fx' : FPState, @names_contract_cf fx' rc B API.
Hypothesis STARVED : forall fx' : FPState, @check_reject_clean_starved_contract_cf fx' rc B API.
Hypothesis CRT : forall fx' : FPState, @check_round_trip_contract_cf fx' rc B API.

Ltac kq := unfold SLK, CNO_K, CHECK_REJECT_CLEAN_STARVED_K, CRT_K, NAMES_K, READINGS_KB, ALLOC_STACK in *; lia.

Lemma sl_cno_call_cf : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md bnd (ub tb : list byte) pk ct
    (uri text : Z) (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true -> frm_zero (@fp_csr f) ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 -> spZ regs0 <= TASK_SIZE ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 uri -> getr R 12 = Z_to_bv 64 text -> 0 <= uri < 2 ^ 64 -> 0 <= text < 2 ^ 64 ->
  getr R 11 = Z_to_bv 64 (Z.of_nat (length ub)) -> getr R 13 = Z_to_bv 64 (Z.of_nat (length tb)) ->
  bytes_at rsegs m uri ub -> bytes_at rsegs m text tb ->
  Forall (fun x => bv_unsigned x <> 0) ub -> Forall (fun x => bv_unsigned x <> 0) tb ->
  (length ub <= 255)%nat -> Z.of_nat (length tb) <= 2 ^ 22 ->
  in_blk (blocks L A) uri (Z.of_nat (length ub)) -> in_blk (blocks L A) text (Z.of_nat (length tb)) ->
  alloc_words B m 0 pk ct (2 ^ 64 - 1) -> 0 <= pk < 2 ^ 64 -> 0 <= ct -> ct + 2 < 2 ^ 63 ->
  res_ok_slots A bnd -> sb_live bnd + 5 <= sb_cap bnd <= CAP_AG -> 0 <= sb_bytes bnd ->
  sb_bytes bnd + (3 * Z.of_nat (length ub) + 2 * Z.of_nat (length tb) + 91) <= 2 ^ 29 ->
  (forall (f' : FPState) L' A' R' m' md' pk' ct',
     frm_zero (@fp_csr f') -> st_init_done A' = true -> regs_preserved R R' ->
     kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> blocks L' A' = blocks L A ->
     (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, spZ R <= a < 2 ^ 64 ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     alloc_words B m' 0 pk' ct' (2 ^ 64 - 1) -> 0 <= pk' < 2 ^ 64 -> ct <= ct' <= ct + 2 ->
     res_ok_slots A' bnd ->
     SRcf B (mkCfg (@mkst f' R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x130d0) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md bnd ub tb pk ct uri text P
    J INIT FRM HAC H16 H63 TSZ SPR RA TP R10 R12 RU RT R11 R13 BU BT NZU NZT LU LT IBU IBT AW PK C0 C1
    RES CAP BY0 BYQ K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  assert (UU : bv_unsigned (getr R 10) = uri) by (rewrite R10; apply unsigned_lit; lia).
  assert (UT : bv_unsigned (getr R 12) = text) by (rewrite R12; apply unsigned_lit; lia).
  assert (US : bv_unsigned (getr R 2) = spZ regs0 - 64) by exact SPR.
  eapply SRcf_bind.
  { apply (CNO f L A R m md bnd ub tb [] pk ct (2 ^ 64 - 1)).
    - exact HS.
    - apply (sl_pre_k B API HS CNO_K L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR RA TP); kq.
    - exact INIT.
    - rewrite US. lia.
    - exact FRM.
    - exact HMI.
    - exact R11.
    - exact R13.
    - rewrite UU. exact BU.
    - rewrite UT. exact BT.
    - exact NZU.
    - exact NZT.
    - exact LU.
    - exact LT.
    - rewrite UU. exact IBU.
    - rewrite UT. exact IBT.
    - exact (img_strings_ro m HMI).
    - unfold ledger. cbn [lsum map]. split; [exact AW|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; constructor.
    - unfold quiet. split; [reflexivity | lia].
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' (f' & L' & A' & R' & m' & md' & -> & FRM' & INIT' & BP & _ & _ & ARMS & RES').
  destruct (sl_bpost B API HS AX ERR L0 A0 regs0 mem0 md0 L A R m md CNO_K L' A' R' m' md' J BP HAC H63 SPR
              ltac:(kq) ltac:(kq)) as (J' & RP & BL & BB & KP & MI').
  destruct ARMS as [(_ & LG) | (_ & LG)]; destruct LG as (AW' & PK' & CT' & _); cbn [lsum] in AW', PK'.
  - exact (K f' L' A' R' m' md' pk ct FRM' INIT' RP J' BL BB KP AW' ltac:(lia) ltac:(lia) RES').
  - exact (K f' L' A' R' m' md' _ (ct + 2) FRM' INIT' RP J' BL BB KP AW' ltac:(lia) ltac:(lia) RES').
Qed.

Lemma sl_names_call_cf : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md bnd (tb ts ub us : list byte) pk ct
    (ta ua : Z) (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true -> frm_zero (@fp_csr f) ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 -> spZ regs0 <= TASK_SIZE ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 ta -> getr R 11 = Z_to_bv 64 ua ->
  cstr_at m ta tb ts -> Z.of_nat (length ts) = (- (ta + Z.of_nat (length tb) + 1)) mod 8 ->
  cstr_at m ua ub us -> Z.of_nat (length us) = (- (ua + Z.of_nat (length ub) + 1)) mod 8 ->
  In (ta, Z.of_nat (length tb) + 1) (blocks L A) -> In (ua, Z.of_nat (length ub) + 1) (blocks L A) ->
  (length ub <= 255)%nat ->
  alloc_words B m 0 pk ct (2 ^ 64 - 1) -> 0 <= pk < 2 ^ 64 -> 0 <= ct -> ct + 1 < 2 ^ 63 ->
  res_ok_slots A bnd -> sb_live bnd + 1 <= sb_cap bnd <= CAP_AG -> 0 <= sb_bytes bnd ->
  sb_bytes bnd + (Z.of_nat (length ub) + 19) <= 2 ^ 29 ->
  (forall (f' : FPState) L' A' R' m' md' pk' ct',
     frm_zero (@fp_csr f') -> st_init_done A' = true -> regs_preserved R R' ->
     getr R' 10 = Z_to_bv 64 (names (zbytes tb) (zbytes ub)) ->
     kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> blocks L' A' = blocks L A ->
     (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, spZ R <= a < 2 ^ 64 ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     (exists ts', cstr_at m' ta tb ts') -> (exists us', cstr_at m' ua ub us') ->
     alloc_words B m' 0 pk' ct' (2 ^ 64 - 1) ->
     ((ub = [] /\ pk' = pk) \/ (ub <> [] /\ pk' = Z.max pk (Z.of_nat (length ub) + 3))) -> ct <= ct' <= ct + 1 ->
     res_ok_slots A' bnd ->
     SRcf B (mkCfg (@mkst f' R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x13e10) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md bnd tb ts ub us pk ct ta ua P
    J INIT FRM HAC H16 H63 TSZ SPR RA TP R10 R11 CT LTS CU LUS INT INU LU AW PK C0 C1 RES CAP BY0 BYQ K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  destruct (sl_block_range B API L A m md ta _ HM INT) as [TL TH].
  destruct (sl_block_range B API L A m md ua _ HM INU) as [UL UH].
  assert (UT : bv_unsigned (getr R 10) = ta) by (rewrite R10; apply unsigned_lit; lia).
  assert (UU : bv_unsigned (getr R 11) = ua) by (rewrite R11; apply unsigned_lit; lia).
  assert (US : bv_unsigned (getr R 2) = spZ regs0 - 64) by exact SPR.
  pose proof (slack_eq ta tb ts LTS) as ST. pose proof (slack_eq ua ub us LUS) as SU.
  eapply SRcf_bind.
  { apply (NAMES f L A R m md bnd tb ts ub us [] pk ct (2 ^ 64 - 1)).
    - exact HS.
    - apply (sl_pre_k B API HS NAMES_K L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR RA TP); kq.
    - exact INIT.
    - rewrite US. lia.
    - exact FRM.
    - exact HMI.
    - destruct (ax_statics AX L A m md HM) as (G0 & (g & _ & Wg) & _). split; [exact G0 | exists g; exact Wg].
    - rewrite UT. exact CT.
    - rewrite UU. exact CU.
    - rewrite UT. left. exists ta, (Z.of_nat (length tb) + 1). split; [exact INT | lia].
    - rewrite UU. left. exists ua, (Z.of_nat (length ub) + 1). split; [exact INU | lia].
    - rewrite UT. exact TL.
    - rewrite UU. exact UL.
    - lia.
    - exact LU.
    - exact (img_strings_ro m HMI).
    - unfold off_stack. rewrite US, UT. left. rewrite ST. Z.div_mod_to_equations. kq.
    - unfold off_stack. rewrite US, UU. left. rewrite SU. Z.div_mod_to_equations. kq.
    - unfold off_stack, PREFIX_LC_STR. rewrite US. left. kq.
    - unfold off_stack, PREFIX_UC_STR. rewrite US. left. kq.
    - unfold off_stack, FMT_WHOLE_STR. rewrite US. left. kq.
    - rewrite UT. apply (sl_off_statics B API AX SF L A m md ta (Z.of_nat (length tb) + 1) _ HM INT); [lia | lia |].
      rewrite ST. lia.
    - rewrite UU. apply (sl_off_statics B API AX SF L A m md ua (Z.of_nat (length ub) + 1) _ HM INU); [lia | lia |].
      rewrite SU. lia.
    - unfold ledger. cbn [lsum map]. split; [exact AW|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; constructor.
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' (f' & L' & A' & R' & m' & md' & res & -> & FRM' & INIT' & BP & R10' & CT' & CU' & ARMS & RES').
  rewrite UT in CT'. rewrite UU in CU'.
  destruct (sl_bpost B API HS AX ERR L0 A0 regs0 mem0 md0 L A R m md NAMES_K L' A' R' m' md' J BP HAC H63 SPR
              ltac:(kq) ltac:(kq)) as (J' & RP & BL & BB & KP & MI').
  destruct ARMS as [(Eub & Er & LG') | [(_ & Ecf & _) | (Nub & Ncf & Er & LG')]].
  - subst ub res. destruct LG' as (AW' & PK' & CT0 & _). cbn [lsum] in AW'.
    exact (K f' L' A' R' m' md' pk ct FRM' INIT' RP ltac:(rewrite R10'; reflexivity) J' BL BB KP CT' CU' AW'
             (or_introl (conj eq_refl eq_refl)) ltac:(lia) RES').
  - lia.
  - subst res. rewrite (Z.mod_small (ct + 1) (2 ^ 64)) in LG' by lia.
    destruct LG' as (AW' & PK' & CT0 & _). cbn [lsum] in AW'.
    exact (K f' L' A' R' m' md' _ (ct + 1) FRM' INIT' RP R10' J' BL BB KP CT' CU' AW'
             (or_intror (conj Nub eq_refl)) ltac:(lia) RES').
Qed.

Lemma sl_starved_call_cf : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md bnd (tb ts ub us : list byte) pk ct
    (ta ua : Z) (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true -> frm_zero (@fp_csr f) ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 -> spZ regs0 <= TASK_SIZE ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 ta -> getr R 11 = Z_to_bv 64 ua ->
  cstr_at m ta tb ts -> Z.of_nat (length ts) = (- (ta + Z.of_nat (length tb) + 1)) mod 8 ->
  cstr_at m ua ub us -> Z.of_nat (length us) = (- (ua + Z.of_nat (length ub) + 1)) mod 8 ->
  In (ta, Z.of_nat (length tb) + 1) (blocks L A) -> In (ua, Z.of_nat (length ub) + 1) (blocks L A) ->
  (length ub <= 255)%nat ->
  alloc_words B m 0 pk ct (2 ^ 64 - 1) -> 0 <= pk < 2 ^ 64 -> 0 <= ct -> ct + 1 < 2 ^ 63 ->
  res_ok_slots A bnd -> sb_live bnd + 1 <= sb_cap bnd <= CAP_AG -> 0 <= sb_bytes bnd ->
  sb_bytes bnd + (Z.of_nat (length ub) + 19) <= 2 ^ 29 ->
  (forall (f' : FPState) L' A' R' m' md' ct',
     frm_zero (@fp_csr f') -> st_init_done A' = true -> regs_preserved R R' ->
     kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> blocks L' A' = blocks L A ->
     (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, spZ R <= a < 2 ^ 64 ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     (exists ts', cstr_at m' ta tb ts') -> (exists us', cstr_at m' ua ub us') ->
     alloc_words B m' 0 pk ct' (2 ^ 64 - 1) -> ct <= ct' <= ct + 1 ->
     res_ok_slots A' bnd ->
     SRcf B (mkCfg (@mkst f' R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x13390) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md bnd tb ts ub us pk ct ta ua P
    J INIT FRM HAC H16 H63 TSZ SPR RA TP R10 R11 CT LTS CU LUS INT INU LU AW PK C0 C1 RES CAP BY0 BYQ K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  destruct (sl_block_range B API L A m md ta _ HM INT) as [TL TH].
  destruct (sl_block_range B API L A m md ua _ HM INU) as [UL UH].
  assert (UT : bv_unsigned (getr R 10) = ta) by (rewrite R10; apply unsigned_lit; lia).
  assert (UU : bv_unsigned (getr R 11) = ua) by (rewrite R11; apply unsigned_lit; lia).
  assert (US : bv_unsigned (getr R 2) = spZ regs0 - 64) by exact SPR.
  pose proof (slack_eq ta tb ts LTS) as ST. pose proof (slack_eq ua ub us LUS) as SU.
  eapply SRcf_bind.
  { apply (STARVED f L A R m md bnd tb ts ub us [] pk ct (2 ^ 64 - 1)).
    - exact HS.
    - apply (sl_pre_k B API HS CHECK_REJECT_CLEAN_STARVED_K L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR
               RA TP); kq.
    - exact INIT.
    - rewrite US. lia.
    - exact FRM.
    - exact HMI.
    - destruct (ax_statics AX L A m md HM) as (G0 & (g & _ & Wg) & _). split; [exact G0 | exists g; exact Wg].
    - rewrite UT. exact CT.
    - rewrite UU. exact CU.
    - rewrite UT. left. exists ta, (Z.of_nat (length tb) + 1). split; [exact INT | lia].
    - rewrite UU. left. exists ua, (Z.of_nat (length ub) + 1). split; [exact INU | lia].
    - rewrite UT. exact TL.
    - rewrite UU. exact UL.
    - lia.
    - exact LU.
    - exact (img_strings_ro m HMI).
    - unfold off_stack. rewrite US, UT. left. rewrite ST. Z.div_mod_to_equations. kq.
    - unfold off_stack. rewrite US, UU. left. rewrite SU. Z.div_mod_to_equations. kq.
    - rewrite UT. apply (sl_off_statics B API AX SF L A m md ta (Z.of_nat (length tb) + 1) _ HM INT); [lia | lia |].
      rewrite ST. lia.
    - rewrite UU. apply (sl_off_statics B API AX SF L A m md ua (Z.of_nat (length ub) + 1) _ HM INU); [lia | lia |].
      rewrite SU. lia.
    - unfold ledger. cbn [lsum map]. split; [exact AW|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; constructor.
    - unfold quiet. split; [reflexivity | lia].
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' (f' & L' & A' & R' & m' & md' & -> & FRM' & INIT' & BP & CT' & CU' & ARMS & RES').
  rewrite UT in CT'. rewrite UU in CU'.
  destruct (sl_bpost B API HS AX ERR L0 A0 regs0 mem0 md0 L A R m md CHECK_REJECT_CLEAN_STARVED_K L' A' R' m' md'
              J BP HAC H63 SPR ltac:(kq) ltac:(kq)) as (J' & RP & BL & BB & KP & MI').
  destruct ARMS as [(_ & LG) | (_ & LG)]; destruct LG as (AW' & PK' & CT0 & _); cbn [lsum] in AW'.
  - exact (K f' L' A' R' m' md' ct FRM' INIT' RP J' BL BB KP CT' CU' AW' ltac:(lia) RES').
  - exact (K f' L' A' R' m' md' (ct + 1) FRM' INIT' RP J' BL BB KP CT' CU' AW' ltac:(lia) RES').
Qed.

Lemma sl_crt_call_cf : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md bnd (ub us : list byte) pk ct
    (ua : Z) (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true -> frm_zero (@fp_csr f) ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 -> spZ regs0 <= TASK_SIZE ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 ua ->
  cstr_at m ua ub us -> In (ua, Z.of_nat (length ub) + 1) (blocks L A) -> (length ub <= 255)%nat ->
  alloc_words B m 0 pk ct (2 ^ 64 - 1) -> 0 <= pk < 2 ^ 64 -> 0 <= ct -> ct + 1019 < 2 ^ 63 ->
  res_ok_slots A bnd -> sb_live bnd + 2 <= sb_cap bnd <= CAP_AG -> 0 <= sb_bytes bnd ->
  sb_bytes bnd + (4 * Z.of_nat (length ub) + 83) <= 2 ^ 29 ->
  (forall (f' : FPState) L' A' R' m' md' pk' ct',
     frm_zero (@fp_csr f') -> st_init_done A' = true -> regs_preserved R R' ->
     kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> blocks L' A' = blocks L A ->
     (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, spZ R <= a < 2 ^ 64 ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     alloc_words B m' 0 pk' ct' (2 ^ 64 - 1) -> 0 <= pk' < 2 ^ 64 -> ct <= ct' <= ct + 1023 ->
     res_ok_slots A' bnd ->
     SRcf B (mkCfg (@mkst f' R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@mkst f R (Z_to_bv 64 0x133ec) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md bnd ub us pk ct ua P
    J INIT FRM HAC H16 H63 TSZ SPR RA TP R10 CU INU LU AW PK C0 C1 RES CAP BY0 BYQ K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  destruct (sl_block_range B API L A m md ua _ HM INU) as [UL UH].
  assert (UU : bv_unsigned (getr R 10) = ua) by (rewrite R10; apply unsigned_lit; lia).
  assert (US : bv_unsigned (getr R 2) = spZ regs0 - 64) by exact SPR.
  eapply SRcf_bind.
  { apply (CRT f L A R m md bnd ub us [] pk ct (2 ^ 64 - 1)).
    - exact HS.
    - apply (sl_pre_k B API HS CRT_K L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR RA TP); kq.
    - exact INIT.
    - rewrite US. lia.
    - exact FRM.
    - exact HMI.
    - destruct (ax_statics AX L A m md HM) as (G0 & (g & _ & Wg) & _). split; [exact G0 | exists g; exact Wg].
    - rewrite UU. exact CU.
    - rewrite UU. exists ua, (Z.of_nat (length ub) + 1). split; [exact INU | lia].
    - exact LU.
    - exact (img_strings_ro m HMI).
    - exact (crt_strings_ro m HMI).
    - unfold ledger. cbn [lsum map]. split; [exact AW|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; constructor.
    - unfold quiet. split; [reflexivity | lia].
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' (f' & L' & A' & R' & m' & md' & -> & FRM' & INIT' & BP & _ & LG & RES').
  destruct (sl_bpost B API HS AX ERR L0 A0 regs0 mem0 md0 L A R m md CRT_K L' A' R' m' md' J BP HAC H63 SPR
              ltac:(kq) ltac:(kq)) as (J' & RP & BL & BB & KP & MI').
  destruct LG as (AW' & PK' & CT0 & _). cbn [lsum] in AW', PK'.
  pose proof (rt_calls_bound ub) as RB.
  exact (K f' L' A' R' m' md' _ _ FRM' INIT' RP J' BL BB KP AW' ltac:(lia) ltac:(lia) RES').
Qed.

End KBcf.

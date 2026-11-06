From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ex_value_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes EntC1_Defs EntC1_Glue LLVMFuzzerTestOneInput_c EntSegA EntSP_Seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_as_written_c check_no_overread_c EntryDefs EntrySR EntBase EntGlue EntStg EntSP_Base EntStgD.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require
  read_members_c check_reject_clean_c fuzz_alloc_live_c strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The check_as_written stage of the #102 ubsan entry (check_as_written 0x13ad4 called at 0x137d4, ra 0x137d8) through
   CF/check_as_written_c.v's caller form check_as_written_contract_z (both flag bytes 0 in: a0 = 0 and both still 0),
   then took = count2 - count (0x1380c) and the rc test (0x13810): rc = 0 goes on to the read_members call (0x1383c,
   EntStgD); rc != 0 calls check_reject_clean (0x13bec) and reaches check_reject_clean_starved (0x13c3c, ra 0x13838). *)

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis CAW : forall fx' : YK11.FPState, @check_as_written_contract fx' rc B API F.
Hypothesis HCRC : check_reject_clean_c.check_reject_clean_contract.
Hypothesis HRM : read_members_c.read_members_contract.

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.

Theorem stg_caw_holds : stg_crs0_st (fx := fx) B API F -> stg_crt_st (fx := fx) B API F ->
  stg_caw_st (fx := fx) B API F.
Proof.
  intros NEXT0 NEXT1. unfold stg_caw_st.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md Lam peak E1 E2 E3 D Dp
    ENT INV R1 RK R8 R9 R10 R11 R13 R18 R19 R21 FL HEMP HE0 ROOMS NLE CNOW DL MATCH.
  pose proof RK as (G2 & G3 & G4 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof FL as (FLR & FLO).
  pose proof (esp_frame B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT)
    as (SPC & SP47 & SP16 & SLK & HN & HC0).
  pose proof alloc_ceiling_val as HCV.
  pose proof ENT as (_ & SYMS & _).
  pose proof (ent_errno B SYMS) as ERRB.
  assert (HKC : CAW_K = 13760) by reflexivity.
  assert (HSP : spZ regs = spZ regs0 - 112) by (apply (esp_sp regs0 regs G2); lia).
  assert (RET : YK0s.ret_ok (getr regs 1)) by (rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  destruct (esp_pay B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak
    (ent_c3 cnt0 pl) (ent_b2 F b0 pl E1 E2 E3 Dp) ENT INV HE0) as (Hp0 & Hpn & BY & HBL & _).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & LED & RES & _).
  pose proof RS as (MRc & _).
  assert (HNL : n = Z.of_nat (length pl)) by (rewrite HN; reflexivity).
  assert (HNE : pl <> [] -> 0 < n) by (intros Hne; rewrite HNL; destruct pl; [contradiction | cbn [length]; lia]).
  assert (NC : (ncalls jr_strtod (zb pl) <= 2 * length (zb pl) + 2)%nat) by apply G7_4.
  assert (EL : length (zb pl) = length pl) by (unfold zb; apply length_map).
  assert (HT : 0 <= ent_took pl <= 2 * n + 2) by (unfold ent_took; rewrite HNL; lia).
  pose proof CNOW as (C1 & C2 & C3).
  pose proof (ROOMS NLE) as (_ & HRM0).
  destruct (HRM0 E1 E2 E3 C1 C2 C3) as (_ & HM).
  set (S := spZ regs0) in *.
  pose proof (ent_env_mid B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    fx1 L A mem md Lam peak (ent_c3 cnt0 pl) (ent_b2 F b0 pl E1 E2 E3 Dp) regs CAW_K ENT INV HSP G4 RET
    ltac:(lia) ltac:(lia)) as REN.
  assert (CALL : forall (rcv : Z) (t' : jv) (D' : list (Z * Z)) (P : config -> Prop),
    getr regs 12 = Z_to_bv 64 rcv -> 0 <= rcv < 2 ^ 64 ->
    (rcv = 0 -> pj_node (ms_segs B) mem (lin Lam) (S - 112) t' D' /\
       Forall (fun ak => caw_inside L A (fst ak) (snd ak) /\ fst ak mod 8 = 0) D') ->
    caw_agree rcv pl t' ->
    rf_room F (ent_b2 F b0 pl E1 E2 E3 Dp) (ent_n pl + 1) ->
    (forall (fx' : YK11.FPState) L' A' regs' mem' md',
       ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx' L' A' mem' md' Lam peak (ent_c3 cnt0 pl)
         (ent_b3 F b0 pl E1 E2 E3 Dp) ->
       rstep B API CAW_K (S - 112) (fun _ : Z => False) (fun a : Z => exists n0 : Z, (fun _ _ : Z => False) a n0)
         L A mem md L' A' mem' md' ->
       regs_preserved regs regs' -> getr regs' 10 = Z_to_bv 64 0 -> ent_flags (ms_segs B) mem' ->
       SR segs (mkCfg (@mkst fx' regs' (Z_to_bv 64 0x137d8) mem' (seg_rom segs)) md') P) ->
    SR segs (mkCfg (@mkst fx1 regs (Z_to_bv 64 CHECK_AS_WRITTEN) mem (seg_rom segs)) md) P).
  { intros rcv t' D' P R12 Hrcv HDOC HAG HROOM K.
    eapply SR_bind.
    { apply (@check_as_written_z fx1 rc B API F (CAW fx1) L A regs mem md p rcv (S - 112) pl (lin Lam) t' D'
        (ent_b2 F b0 pl E1 E2 E3 Dp) REN R10).
      - rewrite <- HNL. exact R11.
      - exact R12.
      - exact R13.
      - exact Hrcv.
      - lia.
      - lia.
      - exact Hp0.
      - lia.
      - exact BY.
      - intros Hne. unfold caw_inside. exists p, n. split; [exact (HBL (HNE Hne)) | lia].
      - intros H0. destruct (HDOC H0) as (HN1 & HF). split; [exact HN1|]. split; [lia|]. split; [lia | exact HF].
      - exact HAG.
      - exact RES.
      - exact HROOM.
      - exact FLR.
      - exact FLO. }
    intros c' (fx' & L' & A' & regs' & mem' & md' & -> & FZ' & _ & RP & RD' & INIT' & BLK' & BY' & RES' & A0' & GR'
      & GO').
    rewrite R1.
    pose proof (rstep_of_rpost B API HSEG AX FG CAW_K L A regs mem md (fun _ => False) (fun _ _ => False)
      L' A' regs' mem' md' RP) as ST.
    rewrite HSP in ST.
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RR' & _).
    assert (LED' : ledger B L' A' mem' Lam peak (ent_c3 cnt0 pl) (2 ^ 64 - 1)).
    { apply (ledger_rstep B API HSEG AX FG CAW_K (S - 112) _ _ L A mem md L' A' mem' md' Lam peak (ent_c3 cnt0 pl)
        (2 ^ 64 - 1) MRc LED ST).
      - intros a Ha. pose proof (ent_statics_lo a Ha) as Hl.
        unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha.
        split; [unfold rwin; rewrite ERRB; unfold strtod_c.STRTOD_ERRNO; lia | intros []].
      - intros a k _. split; [intros (n0 & []) | intros i _ []]. }
    apply (K fx' L' A' regs' mem' md'); [| exact ST | exact RR' | exact A0' | exact (conj GR' GO')].
    apply (ent_after B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak
      (ent_c3 cnt0 pl) (ent_b2 F b0 pl E1 E2 E3 Dp) CAW_K _ _ fx' L' A' mem' md' Lam peak (ent_c3 cnt0 pl)
      (ent_b3 F b0 pl E1 E2 E3 Dp) ENT INV ST ltac:(lia) ltac:(lia)).
    - intros a [].
    - intros a _ [].
    - intros a k _ _ (n0 & []).
    - intros a k Hin _. rewrite BLK'. exact Hin.
    - exact (proj1 RD').
    - exact FZ'.
    - exact LED'.
    - exact RES'. }
  assert (KEEP : forall (regs' : bvmap 5 word), regs_preserved regs regs' ->
    getr regs' 2 = Z_to_bv 64 (S - 112) /\ getr regs' 8 = Z_to_bv 64 n /\ getr regs' 9 = Z_to_bv 64 p /\
    getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 (cnt0 + 3 * ent_took pl) /\
    getr regs' 21 = Z_to_bv 64 (ent_c3 cnt0 pl) /\ ent_rk regs0 regs').
  { intros regs' RR'.
    assert (P2 : getr regs' 2 = getr regs 2) by (apply (RR' 2); unfold callee_saved; lia).
    assert (P3 : getr regs' 3 = getr regs 3) by (apply (RR' 3); unfold callee_saved; lia).
    assert (P4 : getr regs' 4 = getr regs 4) by (apply (RR' 4); unfold callee_saved; lia).
    assert (P8 : getr regs' 8 = getr regs 8) by (apply (RR' 8); unfold callee_saved; lia).
    assert (P9 : getr regs' 9 = getr regs 9) by (apply (RR' 9); unfold callee_saved; lia).
    assert (P18 : getr regs' 18 = getr regs 18) by (apply (RR' 18); unfold callee_saved; lia).
    assert (P19 : getr regs' 19 = getr regs 19) by (apply (RR' 19); unfold callee_saved; lia).
    assert (P21 : getr regs' 21 = getr regs 21) by (apply (RR' 21); unfold callee_saved; lia).
    assert (P22 : getr regs' 22 = getr regs 22) by (apply (RR' 22); unfold callee_saved; lia).
    assert (P23 : getr regs' 23 = getr regs 23) by (apply (RR' 23); unfold callee_saved; lia).
    assert (P24 : getr regs' 24 = getr regs 24) by (apply (RR' 24); unfold callee_saved; lia).
    assert (P25 : getr regs' 25 = getr regs 25) by (apply (RR' 25); unfold callee_saved; lia).
    assert (P26 : getr regs' 26 = getr regs 26) by (apply (RR' 26); unfold callee_saved; lia).
    assert (P27 : getr regs' 27 = getr regs 27) by (apply (RR' 27); unfold callee_saved; lia).
    split; [rewrite P2; exact G2|]. split; [rewrite P8; exact R8|]. split; [rewrite P9; exact R9|].
    split; [rewrite P18; exact R18|]. split; [rewrite P19; exact R19|]. split; [rewrite P21; exact R21|].
    split; [rewrite P2; exact G2|]. split; [rewrite P3; exact G3|]. split; [rewrite P4; exact G4|].
    split; [rewrite P22; exact G22|]. split; [rewrite P23; exact G23|]. split; [rewrite P24; exact G24|].
    split; [rewrite P25; exact G25|]. split; [rewrite P26; exact G26 | rewrite P27; exact G27]. }
  assert (HTK : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (ent_c3 cnt0 pl)) - bv_unsigned (Z_to_bv 64 (cnt0 + 3 * ent_took pl)))
              = Z_to_bv 64 (ent_took pl)).
  { unfold ent_c3. rewrite !esp_uns by lia. f_equal. lia. }
  destruct (json_read jr_strtod (zb pl)) as [t|] eqn:EJ.
  - destruct MATCH as (M12 & M20 & EDp & TREE). subst Dp.
    pose proof TREE as (PERM & NODE & TDL & NEW).
    assert (DLam : forall bk, In bk D -> In bk Lam) by (intros bk Hin; exact (Permutation_in _ (Permutation_sym PERM) Hin)).
    apply (CALL 0 t D).
    + exact M12.
    + lia.
    + intros _. split; [exact NODE|]. rewrite Forall_forall. intros [a k] Hin. cbn [fst snd].
      pose proof LED as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
      destruct (FB (a, k) (DLam _ Hin)) as (Hk & Hblk & _). cbn [fst snd] in *.
      pose proof (ledger_block_aligned B API L A mem md Lam peak (ent_c3 cnt0 pl) (2 ^ 64 - 1) a k MRc LED (DLam _ Hin))
        as HAL.
      split; [unfold caw_inside; exists (a - 16), (k + 16); split; [exact Hblk | lia] | Z.div_mod_to_equations; lia].
    + left. split; [reflexivity | exact EJ].
    + exact (proj1 HM).
    + intros fx' L' A' regs' mem' md' INV' ST RR' A0' FL'.
      pose proof INV' as (RS' & _).
      pose proof RS' as (MR' & _).
      assert (NODE' : pj_node (ms_segs B) mem' (lin Lam) (S - 112) t D).
      { apply (pj_node_rstep B API HSEG AX FG CAW_K (S - 112) _ _ L A mem md L' A' mem' md' Lam Lam peak
          (ent_c3 cnt0 pl) (2 ^ 64 - 1) (S - 112) t D MRc LED NODE DLam ST); [lia | lia | | | intros bk Hb; exact Hb].
        - intros i Hi. split; [unfold rwin; rewrite ERRB; unfold strtod_c.STRTOD_ERRNO; lia | intros []].
        - intros a k _. split; [intros (n0 & []) | intros i _ []]. }
      destruct (KEEP regs' RR') as (G2' & G8' & G9' & G18' & G19' & G21' & RK').
      assert (G20' : getr regs' 20 = Z_to_bv 64 0)
        by (etransitivity; [apply (RR' 20); unfold callee_saved; lia | exact M20]).
      destruct (kb_md B API L' A' mem' md' MR') as (Hh & Hz).
      eapply (ent_kA B HSEG fx' regs' _ mem' md' _ _ Hh Hz).
      { unfold rmk. rewrite G2', A0', G20'.
        exact (esp_segC0 (getr regs' 1) (getr regs' 3) (getr regs' 4) (getr regs' 5) (getr regs' 6) (getr regs' 7)
          (getr regs' 8) (getr regs' 9) (getr regs' 11) (getr regs' 12) (getr regs' 13)
          (getr regs' 14) (getr regs' 15) (getr regs' 16) (getr regs' 17) (getr regs' 18) (getr regs' 19)
          (getr regs' 21) (getr regs' 22) (getr regs' 23) (getr regs' 24) (getr regs' 25) (getr regs' 26)
          (getr regs' 27) (getr regs' 28) (getr regs' 29) (getr regs' 30) (getr regs' 31) (@fp_regs fx')
          (@fp_csr fx') mem' (S - 112)). }
      { intros ms' E. eexists _, _, _. exact E. }
      intros R pc' mem1 regs1 HQ HGr.
      ent_inj HQ R pc' mem1.
      pose proof RK' as (_ & G3' & G4' & G22' & G23' & G24' & G25' & G26' & G27').
      apply (stg_d_to_crt B API F HSEG FA HRM NEXT1 stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
        fx' L' A' regs1 mem' md' Lam peak E1 E2 E3 t D ENT INV').
      * split; [rewrite HGr; reflexivity|].
        split; [rewrite HGr; exact G3'|]. split; [rewrite HGr; exact G4'|].
        split; [rewrite HGr; exact G22'|]. split; [rewrite HGr; exact G23'|]. split; [rewrite HGr; exact G24'|].
        split; [rewrite HGr; exact G25'|]. split; [rewrite HGr; exact G26' | rewrite HGr; exact G27'].
      * rewrite HGr. exact G8'.
      * rewrite HGr. exact G9'.
      * rewrite HGr. cbn. rewrite G21', G19'. exact HTK.
      * exact FL'.
      * exact HEMP.
      * exact HE0.
      * exact ROOMS.
      * exact NLE.
      * exact CNOW.
      * exact EJ.
      * unfold ent_tree. split; [exact PERM|]. split; [exact NODE'|]. split; [exact TDL | exact NEW].
  - destruct MATCH as (M12 & M20 & ELam & PERM & ZERO). subst Lam.
    apply (CALL (2 ^ 64 - 1) JNull []).
    + rewrite M12. apply bv_eq. vm_compute. reflexivity.
    + lia.
    + intros H0. lia.
    + right. split; [lia | exact EJ].
    + exact (proj1 (HM D Dp PERM DL)).
    + intros fx' L' A' regs' mem' md' INV' ST RR' A0' FL'.
      pose proof INV' as (RS' & _ & _ & RD'' & _ & LED' & _).
      pose proof RS' as (MR' & _).
      pose proof ST as (_ & _ & _ & _ & _ & _ & STF & _).
      pose proof LED' as (_ & HPk & _). cbn [lsum] in HPk.
      assert (ZERO' : pj_zero (ms_segs B) mem' (S - 112)).
      { apply (esp_zero_keep (ms_segs B) mem mem' (S - 112) ZERO). intros a Ha.
        destruct (STF a ltac:(lia) ltac:(unfold rwin; rewrite ERRB; unfold strtod_c.STRTOD_ERRNO; lia) (fun h => h))
          as (E1' & E2').
        split; [exact E1' | exact (proj1 E2')]. }
      assert (RAn : MemNorm.ro_agree rsegs mem') by (rewrite <- HSEG; exact (proj1 RD'')).
      destruct (KEEP regs' RR') as (G2' & G8' & G9' & G18' & G19' & G21' & RK').
      pose proof RK' as (_ & G3' & G4' & G22' & G23' & G24' & G25' & G26' & G27').
      assert (G20' : getr regs' 20 = Z_to_bv 64 (-1))
        by (etransitivity; [apply (RR' 20); unfold callee_saved; lia | exact M20]).
      destruct (esp_led B API F HSEG FA L' A' mem' [] peak (ent_c3 cnt0 pl) (2 ^ 64 - 1) LED' ltac:(lia))
        as (_ & _ & BL).
      assert (STKn : EFrame.stk rsegs (MemNorm.normalize rsegs mem') (S - stk) (S - 112)).
      { apply esp_stk_norm.
        - pose proof (esp_stk_rng B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A'
            mem' md' [] peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 Dp) (S - stk) (S - 112) ENT INV'
            ltac:(lia) ltac:(lia)) as X.
          rewrite HSEG in X. exact X.
        - intros a Ha.
          destruct (esp_stk B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A' mem' md'
            [] peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 Dp) a ENT INV' ltac:(lia))
            as (_ & _ & _ & _ & _ & _ & Hr).
          exact Hr. }
      destruct (kb_md B API L' A' mem' md' MR') as (Hh & Hz).
      eapply (esp_kAn B API F HSEG FA fx' regs' _ mem' md' _ _ Hh Hz RAn).
      { unfold rmk. rewrite G2', A0'.
        apply (ent_segC HCRC (getr regs' 1) (getr regs' 3) (getr regs' 4) (getr regs' 5) (getr regs' 6)
          (getr regs' 7) (getr regs' 8) (getr regs' 9) (getr regs' 11) (getr regs' 12)
          (getr regs' 13) (getr regs' 14) (getr regs' 15) (getr regs' 16) (getr regs' 17) (getr regs' 18)
          (getr regs' 19) (getr regs' 20) (getr regs' 21) (getr regs' 22) (getr regs' 23) (getr regs' 24)
          (getr regs' 25) (getr regs' 26) (getr regs' 27) (getr regs' 28) (getr regs' 29) (getr regs' 30)
          (getr regs' 31) (@fp_regs fx') (@fp_csr fx') (MemNorm.normalize rsegs mem') (S - 112) (S - stk) (-1)).
        - exact G20'.
        - lia.
        - lia.
        - lia.
        - intros _. apply MemNorm.bytes_at_normalize; [exact RAn|]. rewrite <- HSEG. exact (proj2 ZERO').
        - intros _. rewrite G18'. apply MemNorm.bytes_at_normalize; [exact RAn | exact (BL eq_refl)].
        - apply MemNorm.mem_inv_normalize.
        - exact STKn.
        - lia.
        - left. unfold fuzz_alloc_live_c.G_LIVE, GL_LIVE. lia. }
      { intros ms' [(C & _)|(_ & t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & _ & _ & _ & _ & E)];
          [lia | eexists _, _, _; exact E]. }
      intros R pc' mem1 m0 regs1 HQ HREL HSAME HGr.
      destruct HQ as [(C & _)|(_ & t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & MU & WM & _ &
        _ & E)]; [lia|].
      ent_inj E R pc' m0.
      pose proof (MemNorm.mem_rel_normalize rsegs mem' RAn) as HR0.
      pose proof (MemNorm.munch_rel rsegs [(S - 112 - 16, S - 112)] mem' (MemNorm.normalize rsegs mem') mem1 m'
        HR0 HREL HSAME MU) as MU'.
      pose proof (MemNorm.wmono_rel rsegs mem' (MemNorm.normalize rsegs mem') mem1 m' HR0 HREL HSAME WM) as WM'.
      rewrite <- HSEG in WM'.
      pose proof (esp_munch_inv B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A'
        mem' md' [] peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 Dp) mem1 [(S - 112 - 16, S - 112)] 16 ENT INV'
        ltac:(lia) ltac:(lia) MU' WM' ltac:(intros x Hx Hn; cbn [EFrame.outside] in Hn; lia)) as INV''.
      assert (FL1 : ent_flags (ms_segs B) mem1).
      { destruct FL' as (FR & FO). unfold ent_flags. rewrite HSEG in FR, FO |- *.
        split; [apply (EFrame.bytes_at_transport rsegs [(S - 112 - 16, S - 112)] mem' mem1 _ _ FR MU') |
                apply (EFrame.bytes_at_transport rsegs [(S - 112 - 16, S - 112)] mem' mem1 _ _ FO MU')];
          cbn [EFrame.disjoint_from]; rewrite EMem.length_le1;
          unfold fuzz_alloc_ran_out_c.G_RAN_OUT, GL_OWN_RAN_OUT in *; (split; [lia | exact I]). }
      apply (NEXT0 stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A' regs1 mem1 md' peak E1 E2 E3 D Dp
        ENT INV'').
      * rewrite HGr. reflexivity.
      * split; [rewrite HGr; reflexivity|].
        split; [rewrite HGr; exact G3'|]. split; [rewrite HGr; exact G4'|].
        split; [rewrite HGr; exact G22'|]. split; [rewrite HGr; exact G23'|]. split; [rewrite HGr; exact G24'|].
        split; [rewrite HGr; exact G25'|]. split; [rewrite HGr; exact G26' | rewrite HGr; exact G27'].
      * rewrite HGr. exact G8'.
      * rewrite HGr. exact G9'.
      * rewrite HGr. exact G9'.
      * rewrite HGr. exact G8'.
      * rewrite HGr. cbn. rewrite G21', G19'. exact HTK.
      * rewrite HGr. reflexivity.
      * exact FL1.
      * exact HEMP.
      * exact HE0.
      * exact ROOMS.
      * exact NLE.
      * exact CNOW.
      * exact EJ.
      * exact PERM.
      * exact DL.
Qed.

End C.

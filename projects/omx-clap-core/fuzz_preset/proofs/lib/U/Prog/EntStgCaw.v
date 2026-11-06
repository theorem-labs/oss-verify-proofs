From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes EntC1_Defs EntC1_Glue LLVMFuzzerTestOneInput_c check_as_written_c check_no_overread_c EntSegA EntryDefs EntrySR EntBase EntGlue EntStg EntSP_Base EntSP_Seg EntStgD.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require read_members_c check_reject_clean_c fuzz_alloc_live_c fuzz_alloc_ran_out_c strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

(* The check_as_written stage of LLVMFuzzerTestOneInput on the #102 ubsan pin (fuzz_preset.c:821-826 of #102,
   `if (out_of_memory() || check_as_written(data, size, rc, &doc)) { pj_free(&doc); return 0; }`, plain 0x13ad4 called
   at 0x137d4).  out_of_memory() was read as 0 before the call (EntSegA.ent_segB2); with both flag bytes 0 the call
   returns a0 = 0 and keeps them 0 (check_as_written_c.check_as_written_z), so the branch at 0x137d8 falls through and
   the pj_free / return 0 exit is not reached.  Then EntSegA.ent_segC: took = count2 - count (0x1380c); rc = 0 goes on at
   0x1383c (EntStgD, the read_members stage, then check_round_trip); rc != 0 runs check_reject_clean and reaches
   check_reject_clean_starved(data, size, took, NULL) (stg_crs0_st). *)

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

(* check_as_written (0x13ad4) called at 0x137d4 (stg_caw_st), on to check_round_trip (rc = 0) or to
   check_reject_clean_starved with doc = NULL (rc != 0) *)
Theorem stg_caw_holds : stg_crs0_st (fx := fx) B API F -> stg_crt_st (fx := fx) B API F ->
  stg_caw_st (fx := fx) B API F.
Proof.
  intros NEXT0 NEXT1. unfold stg_caw_st.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md Lam peak E1 E2 E3 D Dp
    ENT INV R1 RK R8 R9 R10 R11 R13 R18 R19 R21 FLG HEMP HE0 ROOMS NLE CNOW DL MATCH.
  pose proof RK as (G2 & G3 & G4 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof FLG as (FR & FO).
  pose proof (esp_frame B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT)
    as (SPC & SP47 & SP16 & SLK & HN & HC0).
  pose proof alloc_ceiling_val as HCV.
  pose proof ENT as (_ & SYMS & _).
  pose proof (ent_errno B SYMS) as ERRB.
  pose proof (fun fx' : YK11.FPState => check_as_written_z (fx := fx') B API F (CAW fx')) as CAWZ.
  assert (HKC : CAW_K = ltac:(let v := eval vm_compute in CAW_K in exact v)) by reflexivity.
  assert (HSP : spZ regs = spZ regs0 - 112) by (apply (esp_sp regs0 regs G2); lia).
  assert (RET : YK0s.ret_ok (getr regs 1)) by (rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  destruct (esp_pay B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak
    (ent_c3 cnt0 pl) (ent_b2 F b0 pl E1 E2 E3 Dp) ENT INV HE0) as (Hp0 & Hpn & BY & HBL & _).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & LED & RES & _).
  pose proof RS as (MRc & _).
  pose proof LED as (_ & _ & HC & _).
  assert (HT : 0 <= ent_took pl) by (unfold ent_took; lia).
  assert (HNL : n = Z.of_nat (length pl)) by (rewrite HN; reflexivity).
  assert (HNE : pl <> [] -> 0 < n) by (intros Hne; rewrite HNL; destruct pl; [contradiction | cbn [length]; lia]).
  pose proof CNOW as (C1 & C2 & C3).
  pose proof (ROOMS NLE) as (_ & HRM0).
  destruct (HRM0 E1 E2 E3 C1 C2 C3) as (_ & HM).
  set (S := spZ regs0) in *.
  (* took = count2 - count, the s3 that 0x1380c computes *)
  assert (TOOK : forall r21 r19 : word, r21 = Z_to_bv 64 (ent_c3 cnt0 pl) ->
     r19 = Z_to_bv 64 (cnt0 + 3 * ent_took pl) ->
     Z_to_bv 64 (bv_unsigned r21 - bv_unsigned r19) = Z_to_bv 64 (ent_took pl)).
  { intros r21 r19 -> ->. unfold ent_c3 in *. rewrite !esp_uns by lia. f_equal. lia. }
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
       regs_preserved regs regs' -> getr regs' 10 = Z_to_bv 64 0 -> ent_flags segs mem' ->
       SR segs (mkCfg (@mkst fx' regs' (Z_to_bv 64 0x137d8) mem' (seg_rom segs)) md') P) ->
    SR segs (mkCfg (@mkst fx1 regs (Z_to_bv 64 CHECK_AS_WRITTEN) mem (seg_rom segs)) md) P).
  { intros rcv t' D' P R12 Hrcv HDOC HAG HROOM K.
    eapply SR_bind.
    { apply (CAWZ fx1 L A regs mem md p rcv (S - 112) pl (lin Lam) t' D' (ent_b2 F b0 pl E1 E2 E3 Dp) REN R10).
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
      - exact FR.
      - exact FO. }
    intros c' (fx' & L' & A' & regs' & mem' & md' & -> & FZ' & _ & RP & RD' & INIT' & BLK' & BY' & RES' & A0' &
               FR' & FO').
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
        split; [unfold rwin; rewrite ERRB; unfold U.Prog.strtod_c.STRTOD_ERRNO; lia | intros []].
      - intros a k _. split; [intros (n0 & []) | intros i _ []]. }
    apply (K fx' L' A' regs' mem' md'); [| exact ST | exact RR' | exact A0' | exact (conj FR' FO')].
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
  destruct (json_read jr_strtod (zb pl)) as [t|] eqn:EJ.
  - (* rc = 0: the doc holds the tree; on to read_members and check_round_trip *)
    destruct MATCH as (M12 & M20 & EDp & TREE). subst Dp.
    pose proof TREE as (PERM & NODE & TDL & NEW).
    assert (DLam : forall bk, In bk D -> In bk Lam) by (intros bk Hin; exact (Permutation_in _ (Permutation_sym PERM) Hin)).
    apply (CALL 0 t D).
    + exact M12.
    + lia.
    + intros _. split; [exact NODE|]. rewrite Forall_forall. intros [a k] Hin. cbn [fst snd].
      pose proof LED as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
      destruct (FB (a, k) (DLam _ Hin)) as (Hk & Hblk & _). cbn [fst snd] in *.
      (* the U check_as_written contract also asks the doc blocks 8-aligned (ubsan's alignment checks): from the ledger,
         RwLedger's ledger_block_aligned (lib/U/Prog/Ledger.v), as h-walk-grant's CF twin does *)
      pose proof (ledger_block_aligned B API L A mem md Lam peak (ent_c3 cnt0 pl) (2 ^ 64 - 1) a k MRc LED (DLam _ Hin))
        as HAL.
      split; [unfold caw_inside; exists (a - 16), (k + 16); split; [exact Hblk | lia] | Z.div_mod_to_equations; lia].
    + left. split; [reflexivity | exact EJ].
    + exact (proj1 HM).
    + intros fx' L' A' regs' mem' md' INV' ST RR' A0' FLG'.
      pose proof INV' as (RS' & _ & _ & RD'' & _).
      pose proof RS' as (MR' & _).
      assert (NODE' : pj_node (ms_segs B) mem' (lin Lam) (S - 112) t D).
      { apply (pj_node_rstep B API HSEG AX FG CAW_K (S - 112) _ _ L A mem md L' A' mem' md' Lam Lam peak
          (ent_c3 cnt0 pl) (2 ^ 64 - 1) (S - 112) t D MRc LED NODE DLam ST); [lia | lia | | | intros bk Hb; exact Hb].
        - intros i Hi. split; [unfold rwin; rewrite ERRB; unfold U.Prog.strtod_c.STRTOD_ERRNO; lia | intros []].
        - intros a k _. split; [intros (n0 & []) | intros i _ []]. }
      pose proof (ents_node_norm B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A'
        mem' md' Lam peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 []) t D ENT INV' DLam NODE') as NODEn.
      assert (RAn : MemNorm.ro_agree rsegs mem') by (rewrite <- HSEG; exact (proj1 RD'')).
      assert (G2' : getr regs' 2 = Z_to_bv 64 (S - 112))
        by (etransitivity; [apply (RR' 2); unfold callee_saved; lia | exact G2]).
      assert (G3' : getr regs' 3 = getr regs0 3)
        by (etransitivity; [apply (RR' 3); unfold callee_saved; lia | exact G3]).
      assert (G4' : getr regs' 4 = getr regs0 4)
        by (etransitivity; [apply (RR' 4); unfold callee_saved; lia | exact G4]).
      assert (G22' : getr regs' 22 = getr regs0 22)
        by (etransitivity; [apply (RR' 22); unfold callee_saved; lia | exact G22]).
      assert (G23' : getr regs' 23 = getr regs0 23)
        by (etransitivity; [apply (RR' 23); unfold callee_saved; lia | exact G23]).
      assert (G24' : getr regs' 24 = getr regs0 24)
        by (etransitivity; [apply (RR' 24); unfold callee_saved; lia | exact G24]).
      assert (G25' : getr regs' 25 = getr regs0 25)
        by (etransitivity; [apply (RR' 25); unfold callee_saved; lia | exact G25]).
      assert (G26' : getr regs' 26 = getr regs0 26)
        by (etransitivity; [apply (RR' 26); unfold callee_saved; lia | exact G26]).
      assert (G27' : getr regs' 27 = getr regs0 27)
        by (etransitivity; [apply (RR' 27); unfold callee_saved; lia | exact G27]).
      assert (G8' : getr regs' 8 = Z_to_bv 64 n)
        by (etransitivity; [apply (RR' 8); unfold callee_saved; lia | exact R8]).
      assert (G9' : getr regs' 9 = Z_to_bv 64 p)
        by (etransitivity; [apply (RR' 9); unfold callee_saved; lia | exact R9]).
      assert (G19' : getr regs' 19 = Z_to_bv 64 (cnt0 + 3 * ent_took pl))
        by (etransitivity; [apply (RR' 19); unfold callee_saved; lia | exact R19]).
      assert (G20' : getr regs' 20 = Z_to_bv 64 0)
        by (etransitivity; [apply (RR' 20); unfold callee_saved; lia | exact M20]).
      assert (G21' : getr regs' 21 = Z_to_bv 64 (ent_c3 cnt0 pl))
        by (etransitivity; [apply (RR' 21); unfold callee_saved; lia | exact R21]).
      assert (HGL : fuzz_alloc_live_c.G_LIVE + 8 <= S - 112 - 16 \/ S - 112 <= fuzz_alloc_live_c.G_LIVE)
        by (left; unfold fuzz_alloc_live_c.G_LIVE; lia).
      destruct (kb_md B API L' A' mem' md' MR') as (Hh & Hz).
      eapply (esp_kAn B API F HSEG FA fx' regs' _ mem' md' _ _ Hh Hz RAn).
      { unfold rmk. rewrite G2', A0'.
        apply (ent_segC HCRC (getr regs' 1) (getr regs' 3) (getr regs' 4) (getr regs' 5) (getr regs' 6)
          (getr regs' 7) (getr regs' 8) (getr regs' 9) (getr regs' 11) (getr regs' 12)
          (getr regs' 13) (getr regs' 14) (getr regs' 15) (getr regs' 16) (getr regs' 17) (getr regs' 18)
          (getr regs' 19) (getr regs' 20) (getr regs' 21) (getr regs' 22) (getr regs' 23) (getr regs' 24)
          (getr regs' 25) (getr regs' 26) (getr regs' 27) (getr regs' 28) (getr regs' 29) (getr regs' 30)
          (getr regs' 31) (@fp_regs fx') (@fp_csr fx') (MemNorm.normalize rsegs mem') (S - 112) (S - stk) 0).
        - exact G20'.
        - lia.
        - lia.
        - lia.
        - intros H0. exfalso. exact (H0 eq_refl).
        - intros H0. exfalso. exact (H0 eq_refl).
        - apply MemNorm.mem_inv_normalize.
        - apply (ents_stk_norm B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A'
            mem' md' Lam peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 []) (S - stk) (S - 112) ENT INV');
            lia.
        - lia.
        - exact HGL. }
      { intros ms' [(_ & E)|(C & _)]; [eexists _, _, _; exact E | exfalso; exact (C eq_refl)]. }
      intros R pc' mem1 m0 regs1 HQ HREL HSAME HGr.
      destruct HQ as [(_ & E)|(C & _)]; [|exfalso; exact (C eq_refl)].
      ent_inj E R pc' m0.
      pose proof (MemNorm.mem_rel_normalize rsegs mem' RAn) as HR0.
      assert (MU0 : EFrame.munch [] (MemNorm.normalize rsegs mem') (MemNorm.normalize rsegs mem'))
        by apply EFrame.munch_refl.
      assert (WM0 : EFrame.wmono rsegs (MemNorm.normalize rsegs mem') (MemNorm.normalize rsegs mem'))
        by apply EFrame.wmono_refl.
      pose proof (MemNorm.munch_rel rsegs [] mem' (MemNorm.normalize rsegs mem') mem1 (MemNorm.normalize rsegs mem')
        HR0 HREL HSAME MU0) as MU'.
      pose proof (MemNorm.wmono_rel rsegs mem' (MemNorm.normalize rsegs mem') mem1 (MemNorm.normalize rsegs mem')
        HR0 HREL HSAME WM0) as WM'.
      rewrite <- HSEG in WM'.
      pose proof (esp_munch_inv B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A'
        mem' md' Lam peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 []) mem1 [] 0 ENT INV'
        ltac:(lia) ltac:(lia) MU' WM' ltac:(intros x _ Hn; exfalso; apply Hn; exact I)) as INV1.
      assert (FLG1 : ent_flags (ms_segs B) mem1) by exact (ents_flags_munch (ms_segs B) [] mem' mem1 FLG' MU' I I).
      assert (N1 : pj_node (ms_segs B) mem1 (lin Lam) (S - 112) t D).
      { rewrite <- HSEG in HREL, NODEn.
        exact (pj_node_unnormalize B API HSEG AX FG mem1 _ (lin Lam) (S - 112) t D HREL NODEn). }
      assert (Q3 : getr regs1 3 = getr regs' 3) by (rewrite HGr; reflexivity).
      assert (Q4 : getr regs1 4 = getr regs' 4) by (rewrite HGr; reflexivity).
      assert (Q8 : getr regs1 8 = getr regs' 8) by (rewrite HGr; reflexivity).
      assert (Q9 : getr regs1 9 = getr regs' 9) by (rewrite HGr; reflexivity).
      assert (Q22 : getr regs1 22 = getr regs' 22) by (rewrite HGr; reflexivity).
      assert (Q23 : getr regs1 23 = getr regs' 23) by (rewrite HGr; reflexivity).
      assert (Q24 : getr regs1 24 = getr regs' 24) by (rewrite HGr; reflexivity).
      assert (Q25 : getr regs1 25 = getr regs' 25) by (rewrite HGr; reflexivity).
      assert (Q26 : getr regs1 26 = getr regs' 26) by (rewrite HGr; reflexivity).
      assert (Q27 : getr regs1 27 = getr regs' 27) by (rewrite HGr; reflexivity).
      assert (Q19 : getr regs1 19 = Z_to_bv 64 (bv_unsigned (getr regs' 21) - bv_unsigned (getr regs' 19)))
        by (rewrite HGr; reflexivity).
      apply (stg_d_to_crt B API F HSEG FA HRM NEXT1 stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
        fx' L' A' regs1 mem1 md' Lam peak E1 E2 E3 t D ENT INV1).
      * split; [rewrite HGr; reflexivity|].
        split; [rewrite Q3; exact G3'|]. split; [rewrite Q4; exact G4'|].
        split; [rewrite Q22; exact G22'|]. split; [rewrite Q23; exact G23'|].
        split; [rewrite Q24; exact G24'|]. split; [rewrite Q25; exact G25'|].
        split; [rewrite Q26; exact G26' | rewrite Q27; exact G27'].
      * rewrite Q8. exact G8'.
      * rewrite Q9. exact G9'.
      * rewrite Q19. exact (TOOK _ _ G21' G19').
      * exact FLG1.
      * exact HEMP.
      * exact HE0.
      * exact ROOMS.
      * exact NLE.
      * exact CNOW.
      * exact EJ.
      * unfold ent_tree. split; [exact PERM|]. split; [exact N1|]. split; [exact TDL | exact NEW].
  - (* rc != 0: no tree, the doc is zero; check_reject_clean, then check_reject_clean_starved with doc = NULL *)
    destruct MATCH as (M12 & M20 & ELam & PERM & ZERO). subst Lam.
    apply (CALL (2 ^ 64 - 1) JNull []).
    + rewrite M12. apply bv_eq. vm_compute. reflexivity.
    + lia.
    + intros H0. lia.
    + right. split; [lia | exact EJ].
    + exact (proj1 (HM D Dp PERM DL)).
    + intros fx' L' A' regs' mem' md' INV' ST RR' A0' FLG'.
      pose proof INV' as (RS' & _ & _ & RD'' & _ & LED' & _).
      pose proof RS' as (MR' & _).
      pose proof ST as (_ & _ & _ & _ & _ & _ & STF & _).
      pose proof LED' as (_ & HPk & _). cbn [lsum] in HPk.
      assert (ZERO' : pj_zero (ms_segs B) mem' (S - 112)).
      { apply (esp_zero_keep (ms_segs B) mem mem' (S - 112) ZERO). intros a Ha.
        destruct (STF a ltac:(lia) ltac:(unfold rwin; rewrite ERRB; unfold U.Prog.strtod_c.STRTOD_ERRNO; lia) (fun h => h))
          as (E1' & E2').
        split; [exact E1' | exact (proj1 E2')]. }
      assert (RAn : MemNorm.ro_agree rsegs mem') by (rewrite <- HSEG; exact (proj1 RD'')).
      assert (G2' : getr regs' 2 = Z_to_bv 64 (S - 112))
        by (etransitivity; [apply (RR' 2); unfold callee_saved; lia | exact G2]).
      assert (G3' : getr regs' 3 = getr regs0 3)
        by (etransitivity; [apply (RR' 3); unfold callee_saved; lia | exact G3]).
      assert (G4' : getr regs' 4 = getr regs0 4)
        by (etransitivity; [apply (RR' 4); unfold callee_saved; lia | exact G4]).
      assert (G22' : getr regs' 22 = getr regs0 22)
        by (etransitivity; [apply (RR' 22); unfold callee_saved; lia | exact G22]).
      assert (G23' : getr regs' 23 = getr regs0 23)
        by (etransitivity; [apply (RR' 23); unfold callee_saved; lia | exact G23]).
      assert (G24' : getr regs' 24 = getr regs0 24)
        by (etransitivity; [apply (RR' 24); unfold callee_saved; lia | exact G24]).
      assert (G25' : getr regs' 25 = getr regs0 25)
        by (etransitivity; [apply (RR' 25); unfold callee_saved; lia | exact G25]).
      assert (G26' : getr regs' 26 = getr regs0 26)
        by (etransitivity; [apply (RR' 26); unfold callee_saved; lia | exact G26]).
      assert (G27' : getr regs' 27 = getr regs0 27)
        by (etransitivity; [apply (RR' 27); unfold callee_saved; lia | exact G27]).
      assert (G8' : getr regs' 8 = Z_to_bv 64 n)
        by (etransitivity; [apply (RR' 8); unfold callee_saved; lia | exact R8]).
      assert (G9' : getr regs' 9 = Z_to_bv 64 p)
        by (etransitivity; [apply (RR' 9); unfold callee_saved; lia | exact R9]).
      assert (G18' : getr regs' 18 = Z_to_bv 64 0)
        by (etransitivity; [apply (RR' 18); unfold callee_saved; lia | exact R18]).
      assert (G19' : getr regs' 19 = Z_to_bv 64 (cnt0 + 3 * ent_took pl))
        by (etransitivity; [apply (RR' 19); unfold callee_saved; lia | exact R19]).
      assert (G20' : getr regs' 20 = Z_to_bv 64 (-1))
        by (etransitivity; [apply (RR' 20); unfold callee_saved; lia | exact M20]).
      assert (G21' : getr regs' 21 = Z_to_bv 64 (ent_c3 cnt0 pl))
        by (etransitivity; [apply (RR' 21); unfold callee_saved; lia | exact R21]).
      destruct (esp_led B API F HSEG FA L' A' mem' [] peak (ent_c3 cnt0 pl) (2 ^ 64 - 1) LED' ltac:(lia))
        as (_ & _ & BL).
      assert (HGL : fuzz_alloc_live_c.G_LIVE + 8 <= S - 112 - 16 \/ S - 112 <= fuzz_alloc_live_c.G_LIVE)
        by (left; unfold fuzz_alloc_live_c.G_LIVE; lia).
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
        - apply (ents_stk_norm B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A'
            mem' md' [] peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 Dp) (S - stk) (S - 112) ENT INV');
            lia.
        - lia.
        - exact HGL. }
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
      assert (FLG1 : ent_flags (ms_segs B) mem1).
      { apply (ents_flags_munch (ms_segs B) _ mem' mem1 FLG' MU');
          cbn [EFrame.disjoint_from]; unfold fuzz_alloc_ran_out_c.G_RAN_OUT, GL_OWN_RAN_OUT;
          (split; [left; lia | exact I]). }
      assert (Q3 : getr regs1 3 = getr regs' 3) by (rewrite HGr; reflexivity).
      assert (Q4 : getr regs1 4 = getr regs' 4) by (rewrite HGr; reflexivity).
      assert (Q8 : getr regs1 8 = getr regs' 8) by (rewrite HGr; reflexivity).
      assert (Q9 : getr regs1 9 = getr regs' 9) by (rewrite HGr; reflexivity).
      assert (Q10 : getr regs1 10 = getr regs' 9) by (rewrite HGr; reflexivity).
      assert (Q11 : getr regs1 11 = getr regs' 8) by (rewrite HGr; reflexivity).
      assert (Q12 : getr regs1 12 = Z_to_bv 64 (bv_unsigned (getr regs' 21) - bv_unsigned (getr regs' 19)))
        by (rewrite HGr; reflexivity).
      assert (Q22 : getr regs1 22 = getr regs' 22) by (rewrite HGr; reflexivity).
      assert (Q23 : getr regs1 23 = getr regs' 23) by (rewrite HGr; reflexivity).
      assert (Q24 : getr regs1 24 = getr regs' 24) by (rewrite HGr; reflexivity).
      assert (Q25 : getr regs1 25 = getr regs' 25) by (rewrite HGr; reflexivity).
      assert (Q26 : getr regs1 26 = getr regs' 26) by (rewrite HGr; reflexivity).
      assert (Q27 : getr regs1 27 = getr regs' 27) by (rewrite HGr; reflexivity).
      apply (NEXT0 stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A' regs1 mem1 md' peak E1 E2 E3 D Dp
        ENT INV'').
      * rewrite HGr. reflexivity.
      * split; [rewrite HGr; reflexivity|].
        split; [rewrite Q3; exact G3'|]. split; [rewrite Q4; exact G4'|].
        split; [rewrite Q22; exact G22'|]. split; [rewrite Q23; exact G23'|].
        split; [rewrite Q24; exact G24'|]. split; [rewrite Q25; exact G25'|].
        split; [rewrite Q26; exact G26' | rewrite Q27; exact G27'].
      * rewrite Q8. exact G8'.
      * rewrite Q9. exact G9'.
      * rewrite Q10. exact G9'.
      * rewrite Q11. exact G8'.
      * rewrite Q12. exact (TOOK _ _ G21' G19').
      * rewrite HGr. reflexivity.
      * exact FLG1.
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

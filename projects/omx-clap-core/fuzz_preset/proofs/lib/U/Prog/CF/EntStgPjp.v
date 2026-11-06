From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes EntC1_Defs EntC1_Glue LLVMFuzzerTestOneInput_c EntSegA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import pj_parse_c parse_noting_c check_no_overread_c EntryDefs EntrySR EntBase EntGlue EntStg EntSP_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require
  fuzz_alloc_peak_c fuzz_alloc_count_c check_bounded_alloc_c fuzz_alloc_ran_out_c strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The parse_noting stage of the #102 ubsan entry (parse_noting 0x13a38 called at 0x13794, ra 0x13798; it replaces the
   old direct pj_parse call) and the walk on to check_as_written (0x13ad4, ra 0x137d8: ent_segB2, which reads
   out_of_memory() = 0). parse_noting's contract (CF/parse_noting_c.v) takes g_ran_out = 0 and keeps it; g_own_ran_out
   is outside its writes (esp_flag_keep). *)

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis PN : forall fx' : YK11.FPState, @parse_noting_contract fx' rc B API F.
Hypothesis HCOUNT : fuzz_alloc_count_c.fuzz_alloc_count_contract.
Hypothesis HPEAK : fuzz_alloc_peak_c.fuzz_alloc_peak_contract.
Hypothesis HCBA : check_bounded_alloc_c.check_bounded_alloc_contract.
Hypothesis HRO : fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract.

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.

Lemma esp_pjp_seg : stg_caw_st (fx := fx) B API F ->
  forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 (fx1 : YK11.FPState) L A regs mem md Lam peak
    E1 E2 E3 D Dp,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak (ent_c3 cnt0 pl)
    (ent_b2 F b0 pl E1 E2 E3 Dp) ->
  ent_rk regs0 regs ->
  getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 p ->
  getr regs 18 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 (cnt0 + 3 * ent_took pl) ->
  getr regs 21 = Z_to_bv 64 (GL_OWN_RAN_OUT + 0x4f8) -> ent_flags segs mem ->
  0 <= peak <= 256 * n + 20480 ->
  0 < empty < 2 ^ 62 -> empty = 0x35230 ->
  entry_rooms F b0 cnt0 pl -> ent_n pl <= 0x300000 -> ent_cnow pl E1 E2 E3 -> ent_tree_dl pl D ->
  match json_read jr_strtod (zb pl) with
  | Some t => getr regs 10 = Z_to_bv 64 0 /\ Dp = [] /\ ent_tree B L0 A0 regs0 mem Lam pl t D
  | None => getr regs 10 = Z_to_bv 64 (-1) /\ Lam = [] /\ Permutation D Dp /\ pj_zero segs mem (spZ regs0 - 112)
  end ->
  SR segs (mkCfg (@mkst fx1 regs (Z_to_bv 64 0x13798) mem (seg_rom segs)) md)
    (ent_sr_post B API F stk j L0 A0 regs0 mem0 md0 ra p n pl cnt0 b0).
Proof.
  intros NEXT stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md Lam peak E1 E2 E3 D Dp
    ENT INV RK G8 G9 G18 G19 G21 FL HPK HEMP HE0 ROOMS NLE CNOW DL MATCH.
  pose proof RK as (G2 & G3 & G4 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof FL as (FLR & FLO).
  pose proof (esp_frame B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT)
    as (SPC & SP47 & SP16 & SLK & HN & HC0).
  pose proof INV as (RS & _ & _ & _ & _ & LED & _).
  pose proof RS as (MRc & _).
  pose proof LED as (_ & _ & HC & _).
  pose proof alloc_ceiling_val as HCV.
  assert (HT : 0 <= ent_took pl) by (unfold ent_took; lia).
  set (S := spZ regs0) in *.
  assert (HN0 : 0 <= n <= 0x300000) by (rewrite HN; unfold ent_n in *; lia).
  destruct (esp_led B API F HSEG FA L A mem Lam peak (ent_c3 cnt0 pl) (2 ^ 64 - 1) LED ltac:(lia)) as (BP & BC & _).
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  eapply (ent_kA B HSEG fx1 regs _ mem md _ _ Hh Hz).
  { unfold rmk. rewrite G2, G21. unfold segs in FLR, FLO. rewrite HSEG in FLR, FLO.
    apply (ent_segB2 HCOUNT HPEAK HCBA HRO (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
      (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
      (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
      (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) (@fp_regs fx1) (@fp_csr fx1) mem
      (S - 112) (Z_to_bv 64 peak) (Z_to_bv 64 (ent_c3 cnt0 pl)) BP BC FLO FLR).
    - rewrite G8, esp_uns by lia. lia.
    - rewrite G8, G18, !esp_uns by lia. rewrite Z.sub_0_r, Z.mod_small by lia. lia. }
  { intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E). eexists _, _, _. exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  destruct HQ as (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E).
  ent_inj E R pc' mem1.
  assert (Q3 : getr regs1 3 = getr regs 3) by (rewrite HGr; reflexivity).
  assert (Q4 : getr regs1 4 = getr regs 4) by (rewrite HGr; reflexivity).
  assert (Q8 : getr regs1 8 = getr regs 8) by (rewrite HGr; reflexivity).
  assert (Q9 : getr regs1 9 = getr regs 9) by (rewrite HGr; reflexivity).
  assert (Q10 : getr regs1 10 = getr regs 9) by (rewrite HGr; reflexivity).
  assert (Q11 : getr regs1 11 = getr regs 8) by (rewrite HGr; reflexivity).
  assert (Q12 : getr regs1 12 = getr regs 10) by (rewrite HGr; reflexivity).
  assert (Q18 : getr regs1 18 = getr regs 18) by (rewrite HGr; reflexivity).
  assert (Q19 : getr regs1 19 = getr regs 19) by (rewrite HGr; reflexivity).
  assert (Q20 : getr regs1 20 = getr regs 10) by (rewrite HGr; reflexivity).
  assert (Q22 : getr regs1 22 = getr regs 22) by (rewrite HGr; reflexivity).
  assert (Q23 : getr regs1 23 = getr regs 23) by (rewrite HGr; reflexivity).
  assert (Q24 : getr regs1 24 = getr regs 24) by (rewrite HGr; reflexivity).
  assert (Q25 : getr regs1 25 = getr regs 25) by (rewrite HGr; reflexivity).
  assert (Q26 : getr regs1 26 = getr regs 26) by (rewrite HGr; reflexivity).
  assert (Q27 : getr regs1 27 = getr regs 27) by (rewrite HGr; reflexivity).
  apply (NEXT stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs1 mem md Lam peak E1 E2 E3 D Dp
    ENT INV).
  - rewrite HGr. reflexivity.
  - split; [rewrite HGr; reflexivity|].
    split; [rewrite Q3; exact G3|]. split; [rewrite Q4; exact G4|].
    split; [rewrite Q22; exact G22|]. split; [rewrite Q23; exact G23|]. split; [rewrite Q24; exact G24|].
    split; [rewrite Q25; exact G25|]. split; [rewrite Q26; exact G26 | rewrite Q27; exact G27].
  - rewrite Q8. exact G8.
  - rewrite Q9. exact G9.
  - rewrite Q10. exact G9.
  - rewrite Q11. exact G8.
  - rewrite HGr. reflexivity.
  - rewrite Q18. exact G18.
  - rewrite Q19. exact G19.
  - rewrite HGr. reflexivity.
  - exact FL.
  - exact HEMP.
  - exact HE0.
  - exact ROOMS.
  - exact NLE.
  - exact CNOW.
  - exact DL.
  - rewrite Q12, Q20. destruct (json_read jr_strtod (zb pl)) as [t|].
    + destruct MATCH as (M10 & M2 & M3). exact (conj M10 (conj M10 (conj M2 M3))).
    + destruct MATCH as (M10 & M2 & M3 & M4). exact (conj M10 (conj M10 (conj M2 (conj M3 M4)))).
Qed.

Theorem stg_pjp_holds : stg_caw_st (fx := fx) B API F -> stg_pjp_st (fx := fx) B API F.
Proof.
  intros NEXT. unfold stg_pjp_st.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md E1 E2 E3
    ENT INV R1 RK R8 R9 R10 R11 R12 R18 R19 R21 FL HEMP HE0 ROOMS NLE CNOW.
  pose proof RK as (G2 & G3 & G4 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof FL as (FLR & FLO).
  pose proof ENT as (_ & SYMS & _).
  pose proof (ent_errno B SYMS) as ERRB.
  pose proof (esp_frame B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT)
    as (SPC & SP47 & SP16 & SLK & HN & HC0).
  pose proof alloc_ceiling_val as HCV.
  assert (HKP : PJ_PARSE_K = 14160) by reflexivity.
  assert (HKN : PN_K = 14208) by reflexivity.
  assert (HSP : spZ regs = spZ regs0 - 112) by (apply (esp_sp regs0 regs G2); lia).
  assert (RET : YK0s.ret_ok (getr regs 1)) by (rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  destruct (esp_pay B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md [] 0
    (cnt0 + 3 * ent_took pl) (ent_b1 F b0 pl E1 E2 E3) ENT INV HE0) as (Hp0 & Hpn & BY & HBL & HNO).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & LED & RES & _).
  pose proof RS as (MRc & _ & _ & _ & KBc & _).
  assert (NC : (ncalls jr_strtod (zb pl) <= 2 * length (zb pl) + 2)%nat) by apply G7_4.
  assert (EL : length (zb pl) = length pl) by (unfold zb; apply length_map).
  assert (HNL : n = Z.of_nat (length pl)) by (rewrite HN; reflexivity).
  assert (ET : ent_took pl = Z.of_nat (ncalls jr_strtod (zb pl))) by reflexivity.
  set (S := spZ regs0) in *.
  set (c1 := cnt0 + 3 * ent_took pl) in *.
  pose proof (ent_env_mid B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    fx1 L A mem md [] 0 c1 (ent_b1 F b0 pl E1 E2 E3) regs PN_K ENT INV HSP G4 RET ltac:(lia) ltac:(lia)) as REN.
  eapply SR_bind.
  { apply (PN fx1 L A regs mem md [] 0 c1 (2 ^ 64 - 1) (ent_b1 F b0 pl E1 E2 E3) p n (S - 112) pl REN LED RES
      R10 R11 R12).
    - lia.
    - exact Hp0.
    - lia.
    - lia.
    - exact BY.
    - pose proof (PjRoundTrip.G12_1 (zb pl)) as G. lia.
    - split.
      + destruct (Z_lt_le_dec 0 n) as [Hn|Hn].
        * right. right. left. exists p, n. split; [exact (HBL Hn)|]. split; [unfold lin; cbn; tauto | lia].
        * right. left. intros i Hi. lia.
      + intros i Hi. destruct (HNO i Hi) as (H1 & H2 & H3 & _). tauto.
    - lia.
    - exact (esp_out_rw B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md [] 0 c1
        (ent_b1 F b0 pl E1 E2 E3) ENT INV).
    - exact (esp_rplace B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md [] 0 c1
        (ent_b1 F b0 pl E1 E2 E3) regs ENT INV HSP).
    - intros a k [].
    - cbn [EFrame.disjoint_from]. split; [right; lia | exact I].
    - exact FLR.
    - pose proof (ent_W_img B API HSEG FA fuzz_alloc_ran_out_c.G_RAN_OUT ltac:(right; left; lia)) as HRI.
      pose proof (ent_W_lo fuzz_alloc_ran_out_c.G_RAN_OUT ltac:(right; left; lia)) as HRL.
      cbn [EFrame.disjoint_from]. split; [|split; [left; lia | exact I]].
      destruct (Z_lt_le_dec fuzz_alloc_ran_out_c.G_RAN_OUT p) as [H1|H1]; [left; lia|].
      destruct (Z_lt_le_dec fuzz_alloc_ran_out_c.G_RAN_OUT (p + n)) as [H2|H2]; [exfalso|right; lia].
      destruct (HNO (fuzz_alloc_ran_out_c.G_RAN_OUT - p) ltac:(lia)) as (_ & _ & _ & HNI).
      replace (p + (fuzz_alloc_ran_out_c.G_RAN_OUT - p)) with fuzz_alloc_ran_out_c.G_RAN_OUT in HNI by lia.
      exact (HNI HRI).
    - cbn [EFrame.disjoint_from]. rewrite HSP. split; [right; lia|]. split; [left; lia | exact I].
    - unfold c1. lia.
    - destruct (ROOMS NLE) as (_ & HR). destruct CNOW as (C1 & C2 & C3).
      exact (proj1 (HR E1 E2 E3 C1 C2 C3)). }
  intros c' (fx' & L' & A' & regs' & mem' & md' & Lam' & peak' & cnt' & fail' & ok & res & tr & -> & FZ' & _ & RP & RD' &
             GR' & LED' & JR & OKS & CT' & FL' & PK' & HPK' & _ & SUC & MATCH).
  destruct SUC as [ERES ECALLS]; [right; unfold c1; lia|].
  rewrite ECALLS in OKS, CT', FL'.
  assert (ETR : tr = ent_T pl).
  { assert (HU : forall i, (i < ncalls jr_strtod (zb pl))%nat -> nth i ok true = true).
    { intros i Hi. rewrite (OKS i Hi). apply negb_true_iff. apply Z.eqb_neq. unfold c1. lia. }
    rewrite (G7_1 jr_strtod (zb pl) ok HU) in JR. injection JR as _ E. symmetry. exact E. }
  assert (EFL : fail' = 2 ^ 64 - 1) by (apply (proj2 FL'); unfold c1; lia).
  assert (ECT : cnt' = ent_c3 cnt0 pl) by (rewrite CT'; unfold c1, ent_c3; lia).
  subst tr fail' cnt'.
  pose proof (rstep_of_rpost B API HSEG AX FG PN_K L A regs mem md (parse_noting_writes (S - 112)) (fun _ _ => False)
    L' A' regs' mem' md' RP) as ST.
  rewrite HSP in ST.
  pose proof RP as (MR' & _ & _ & _ & _ & _ & _ & UB' & PA' & RR' & _).
  assert (HZ : forall a k, In (a, k) (blocks L A) -> k <= 0 -> In (a, k) (blocks L' A')).
  { intros a k Hin _. destruct (rg_blk_in B API HSEG AX FG L A a k Hin) as (q0 & Hq0 & <-).
    assert (Hq1 : In (q0, k) (user_blocks A')) by (apply UB'; [exact Hq0 | intros []]).
    rewrite <- (PA' q0 k Hq0 Hq1). exact (rg_blk_of B API HSEG AX FG L' A' q0 k Hq1). }
  assert (HB0 : forall a k, In (a, k) (blocks L0 A0) -> In (a, k) (blocks L A)).
  { intros a k Hin. destruct (Z_le_gt_dec k 0) as [Hk|Hk];
      [exact (Z0 a k Hin Hk) | exact (KBc a k Hin ltac:(lia) (fun h => h))]. }
  assert (INV' : forall bnd', rf_ok F A' bnd' -> pj_rw segs mem' (S - 112) ->
     ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx' L' A' mem' md' Lam' peak' (ent_c3 cnt0 pl) bnd').
  { intros bnd' RES' RW'.
    apply (ent_after B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md [] 0
      c1 (ent_b1 F b0 pl E1 E2 E3) PN_K _ _ fx' L' A' mem' md' Lam' peak' (ent_c3 cnt0 pl) bnd' ENT INV ST
      ltac:(lia) ltac:(lia)); [| | | exact HZ | exact (proj1 RD') | exact FZ' | exact LED' | exact RES'].
    - intros a [Ha|Ha]; [right; left; lia | left; left; exact Ha].
    - intros a Ha [Hw|Hw]; [exact (esp_rw_wr segs mem' (S - 112) a RW' Hw) | pose proof (ent_statics_lo a Hw); lia].
    - intros a k _ _ (n' & []). }
  assert (G2' : getr regs' 2 = Z_to_bv 64 (S - 112))
    by (etransitivity; [apply (RR' 2); unfold callee_saved; lia | exact G2]).
  assert (G3' : getr regs' 3 = getr regs0 3)
    by (etransitivity; [apply (RR' 3); unfold callee_saved; lia | exact G3]).
  assert (G4' : getr regs' 4 = getr regs0 4)
    by (etransitivity; [apply (RR' 4); unfold callee_saved; lia | exact G4]).
  assert (G8' : getr regs' 8 = Z_to_bv 64 n)
    by (etransitivity; [apply (RR' 8); unfold callee_saved; lia | exact R8]).
  assert (G9' : getr regs' 9 = Z_to_bv 64 p)
    by (etransitivity; [apply (RR' 9); unfold callee_saved; lia | exact R9]).
  assert (G18' : getr regs' 18 = Z_to_bv 64 0)
    by (etransitivity; [apply (RR' 18); unfold callee_saved; lia | exact R18]).
  assert (G19' : getr regs' 19 = Z_to_bv 64 (cnt0 + 3 * ent_took pl))
    by (etransitivity; [apply (RR' 19); unfold callee_saved; lia | exact R19]).
  assert (G21' : getr regs' 21 = Z_to_bv 64 (GL_OWN_RAN_OUT + 0x4f8))
    by (etransitivity; [apply (RR' 21); unfold callee_saved; lia | exact R21]).
  assert (RK' : ent_rk regs0 regs').
  { split; [exact G2'|]. split; [exact G3'|]. split; [exact G4'|].
    split; [etransitivity; [apply (RR' 22); unfold callee_saved; lia | exact G22]|].
    split; [etransitivity; [apply (RR' 23); unfold callee_saved; lia | exact G23]|].
    split; [etransitivity; [apply (RR' 24); unfold callee_saved; lia | exact G24]|].
    split; [etransitivity; [apply (RR' 25); unfold callee_saved; lia | exact G25]|].
    split; [etransitivity; [apply (RR' 26); unfold callee_saved; lia | exact G26]|].
    etransitivity; [apply (RR' 27); unfold callee_saved; lia | exact G27]. }
  assert (FLG' : ent_flags segs mem').
  { split; [exact GR'|].
    apply (esp_flag_keep B API F HSEG FA PN_K (S - 112) (parse_noting_writes (S - 112)) _ L A mem md L' A' mem' md'
      GL_OWN_RAN_OUT _ ST (or_introl eq_refl) ltac:(lia)); [| exact ERRB | exact FLO].
    unfold parse_noting_writes, pj_parse_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL, GL_OWN_RAN_OUT.
    pose proof alloc_ceiling_val. lia. }
  assert (PKB : 0 <= peak' <= 256 * n + 20480) by (rewrite PK'; cbn [lsum]; lia).
  rewrite ERES in MATCH. rewrite R1.
  destruct (json_read jr_strtod (zb pl)) as [t|] eqn:EJ.
  - destruct MATCH as (R10' & RF & D & PERM & LS & LN & NEW & NODE).
    rewrite app_nil_r in PERM.
    assert (Eb : ent_b2 F b0 pl E1 E2 E3 [] = rf_run F (ent_b1 F b0 pl E1 E2 E3) (ent_T pl))
      by (unfold ent_b2, cno_ok; rewrite EJ; reflexivity).
    apply (esp_pjp_seg NEXT stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A' regs' mem' md' Lam'
      peak' E1 E2 E3 D [] ENT (INV' (ent_b2 F b0 pl E1 E2 E3 []) ltac:(rewrite Eb; exact RF) (esp_node_rw _ _ _ _ _ _ NODE))
      RK' G8' G9' G18' G19' G21' FLG' PKB HEMP HE0 ROOMS NLE CNOW (conj LS LN)).
    rewrite EJ. split; [exact R10'|]. split; [reflexivity|].
    unfold ent_tree. split; [exact PERM|]. split; [exact NODE|]. split; [exact (conj LS LN)|].
    intros a k Hin Hb. exact (NEW a k Hin (HB0 _ _ Hb)).
  - destruct MATCH as (R10' & (D0 & D' & HP & LS & LN & RF) & PERM & ZERO).
    pose proof (Permutation_nil (Permutation_sym PERM)) as ELam. subst Lam'.
    assert (Eb : ent_b2 F b0 pl E1 E2 E3 D' = rf_frees F (rf_run F (ent_b1 F b0 pl E1 E2 E3) (ent_T pl)) D')
      by (unfold ent_b2, cno_ok; rewrite EJ; reflexivity).
    apply (esp_pjp_seg NEXT stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L' A' regs' mem' md' []
      peak' E1 E2 E3 D0 D' ENT (INV' (ent_b2 F b0 pl E1 E2 E3 D') ltac:(rewrite Eb; exact RF) (proj1 ZERO))
      RK' G8' G9' G18' G19' G21' FLG' PKB HEMP HE0 ROOMS NLE CNOW (conj LS LN)).
    rewrite EJ. split; [exact R10'|]. split; [reflexivity|]. split; [exact HP | exact ZERO].
Qed.

End P.

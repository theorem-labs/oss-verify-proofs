From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes EntC1_Defs EntC1_Glue LLVMFuzzerTestOneInput_c EntSP_Seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import EntryDefs EntrySR EntBase EntGlue EntStg EntSP_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require read_members_c fuzz_alloc_ran_out_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The D stage of the #102 ubsan entry: at 0x1383c (rc = 0) the entry calls read_members(&doc), out of line since #102
   (0x13e94; lib/U/Prog/read_members_c.v, RM_K = 192), then passes &doc to check_round_trip (0x1408c, ra 0x1384c):
   EntSP_Seg.esp_segD. The old inline read_members walk (pj_get / pj_get_str, EntSegD1 / EntSegD2) is gone from the
   code, so from this file too. *)

Section D.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis HRM : read_members_c.read_members_contract.

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.
#[local] Set Default Proof Using "All".

Lemma stg_d_to_crt : stg_crt_st (fx := fx) B API F ->
  forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 (fx1 : YK11.FPState) L A regs mem md Lam peak
    E1 E2 E3 t D,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak (ent_c3 cnt0 pl)
    (ent_b3 F b0 pl E1 E2 E3 []) ->
  ent_rk regs0 regs ->
  getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 (ent_took pl) ->
  ent_flags (ms_segs B) mem ->
  0 < empty < 2 ^ 62 -> empty = 0x35230 ->
  entry_rooms F b0 cnt0 pl -> ent_n pl <= 0x300000 -> ent_cnow pl E1 E2 E3 ->
  json_read jr_strtod (zb pl) = Some t -> ent_tree B L0 A0 regs0 mem Lam pl t D ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs (Z_to_bv 64 0x1383c) mem (seg_rom (ms_segs B))) md)
    (ent_sr_post B API F stk j L0 A0 regs0 mem0 md0 ra p n pl cnt0 b0).
Proof.
  intros NEXT stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md Lam peak E1 E2 E3 t D
    ENT INV RK G8 G9 G19 FL HEMP HE0 ROOMS NLE CNOW EJ TREE.
  pose proof RK as (G2 & G3 & G4 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof (esp_frame B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT)
    as (SPC & SP47 & SP16 & SLK & HN & HC0).
  pose proof INV as (RS & _ & _ & RD & _ & LED & _).
  pose proof RS as (MRc & _).
  pose proof alloc_ceiling_val as HCV.
  pose proof TREE as (PERM & NODE & TDL & NEW).
  assert (HRK : read_members_c.RM_K = 192) by reflexivity.
  assert (RA : MemNorm.ro_agree rsegs mem) by (rewrite <- HSEG; exact (proj1 RD)).
  set (S := spZ regs0) in *.
  assert (DL : forall bk, In bk D -> In bk Lam) by (intros bk Hin; exact (Permutation_in _ (Permutation_sym PERM) Hin)).
  assert (LB : forall a k, lin Lam a k ->
    0 < a /\ a mod 8 = 0 /\ a + k <= 2 ^ 47 /\
    EFrame.disjoint_from [(a, a + k)] (S - 112 - read_members_c.RM_K) read_members_c.RM_K).
  { intros a k Hin. unfold lin in Hin.
    destruct (ledger_block_range B API L A mem md Lam peak (ent_c3 cnt0 pl) (2 ^ 64 - 1) a k MRc LED Hin)
      as (H1 & H2 & H3).
    pose proof (ledger_block_aligned B API L A mem md Lam peak (ent_c3 cnt0 pl) (2 ^ 64 - 1) a k MRc LED Hin) as H4.
    split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|].
    cbn [EFrame.disjoint_from]. split; [right; lia | exact I]. }
  assert (NODEn : pj_node rsegs (MemNorm.normalize rsegs mem) (lin Lam) (S - 112) t D).
  { pose proof (pj_node_normalize B API HSEG AX FG mem (lin Lam) (S - 112) t D (proj1 RD) NODE) as X.
    rewrite HSEG in X. apply X. intros x [Hx|([a k] & Hb & Hx)].
    - destruct (esp_stk B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam
        peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 []) x ENT INV ltac:(lia)) as (_ & _ & _ & _ & _ & _ & Hr).
      exact Hr.
    - unfold pj_holds in Hx. cbn [fst snd] in Hx.
      pose proof LED as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
      destruct (FB (a, k) (DL _ Hb)) as (Hk & Hblk & _ & HNI). cbn [fst snd] in *.
      destruct (ledger_block_range B API L A mem md Lam peak (ent_c3 cnt0 pl) (2 ^ 64 - 1) a k MRc LED (DL _ Hb))
        as (H1 & H2 & _).
      apply (esp_ro_false B API F HSEG FA x ltac:(lia)).
      replace x with (a - 16 + (x - a + 16)) by lia. apply HNI. lia. }
  assert (STKn : forall lo hi, S - stk <= lo -> hi <= S -> EFrame.stk rsegs (MemNorm.normalize rsegs mem) lo hi).
  { intros lo hi H1 H2. apply esp_stk_norm.
    - pose proof (esp_stk_rng B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md
        Lam peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 []) lo hi ENT INV H1 H2) as X.
      rewrite HSEG in X. exact X.
    - intros a Ha.
      destruct (esp_stk B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam
        peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 []) a ENT INV ltac:(lia)) as (_ & _ & _ & _ & _ & _ & Hr).
      exact Hr. }
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  eapply (esp_kAn B API F HSEG FA fx1 regs _ mem md _ _ Hh Hz RA).
  { unfold rmk. rewrite G2.
    apply (esp_segD HRM (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
      (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
      (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
      (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
      (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) (@fp_regs fx1) (@fp_csr fx1)
      (MemNorm.normalize rsegs mem) (lin Lam) (S - 112) (S - stk) t D).
    - lia.
    - Z.div_mod_to_equations. lia.
    - exact LB.
    - apply STKn; lia.
    - lia.
    - apply MemNorm.mem_inv_normalize.
    - exact NODEn. }
  { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & _).
    eexists _, _, _. exact E. }
  intros R pc' mem1 m0 regs1 HQ HREL HSAME HGr.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM &
    _ & _ & N2).
  ent_inj E R pc' m0.
  pose proof (MemNorm.mem_rel_normalize rsegs mem RA) as HR0.
  pose proof (MemNorm.munch_rel rsegs [(S - 112 - read_members_c.RM_K, S - 112)] mem
    (MemNorm.normalize rsegs mem) mem1 m' HR0 HREL HSAME MU) as MU'.
  pose proof (MemNorm.wmono_rel rsegs mem (MemNorm.normalize rsegs mem) mem1 m' HR0 HREL HSAME WM) as WM'.
  rewrite <- HSEG in WM'.
  pose proof (esp_munch_inv B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md
    Lam peak (ent_c3 cnt0 pl) (ent_b3 F b0 pl E1 E2 E3 []) mem1
    [(S - 112 - read_members_c.RM_K, S - 112)] read_members_c.RM_K ENT INV ltac:(lia) ltac:(lia) MU' WM'
    ltac:(intros x Hx Hn; cbn [EFrame.outside] in Hn; lia)) as INV'.
  assert (N2' : pj_node (ms_segs B) mem1 (lin Lam) (S - 112) t D).
  { rewrite <- HSEG in HREL, N2.
    exact (pj_node_unnormalize B API HSEG AX FG mem1 m' (lin Lam) (S - 112) t D HREL N2). }
  assert (FL1 : ent_flags (ms_segs B) mem1).
  { destruct FL as (FR & FO). unfold ent_flags. rewrite HSEG in FR, FO |- *.
    split; [apply (EFrame.bytes_at_transport rsegs [(S - 112 - read_members_c.RM_K, S - 112)] mem mem1 _ _ FR MU') |
            apply (EFrame.bytes_at_transport rsegs [(S - 112 - read_members_c.RM_K, S - 112)] mem mem1 _ _ FO MU')];
      cbn [EFrame.disjoint_from]; rewrite EMem.length_le1;
      unfold fuzz_alloc_ran_out_c.G_RAN_OUT, GL_OWN_RAN_OUT in *; (split; [lia | exact I]). }
  apply (NEXT stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs1 mem1 md Lam peak E1 E2 E3 t D
    ENT INV').
  - rewrite HGr. reflexivity.
  - split; [rewrite HGr; reflexivity|].
    split; [rewrite HGr; exact G3|]. split; [rewrite HGr; exact G4|].
    split; [rewrite HGr; exact G22|]. split; [rewrite HGr; exact G23|]. split; [rewrite HGr; exact G24|].
    split; [rewrite HGr; exact G25|]. split; [rewrite HGr; exact G26 | rewrite HGr; exact G27].
  - rewrite HGr. exact G8.
  - rewrite HGr. exact G9.
  - rewrite HGr. reflexivity.
  - rewrite HGr. exact G19.
  - exact FL1.
  - exact HEMP.
  - exact HE0.
  - exact ROOMS.
  - exact NLE.
  - exact CNOW.
  - exact EJ.
  - unfold ent_tree. split; [exact PERM|]. split; [exact N2'|]. split; [exact TDL | exact NEW].
Qed.

End D.

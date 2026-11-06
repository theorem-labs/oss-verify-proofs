From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YL0b YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI AllocPack SlotPack.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes EntC1_Defs EntC1_Glue LLVMFuzzerTestOneInput_c EntSegA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import EntrySR EntBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.

Lemma ent_env0 : forall stk empty j L A regs mem md ra p n pl peak cnt b0,
  ent_pre (fx := fx) B API F stk empty j L A regs mem md ra p n pl peak cnt b0 ->
  reader_env B API stk L A regs mem md.
Proof.
  intros stk empty j L A regs mem md ra p n pl peak cnt b0 ENT.
  pose proof (ent_ret_ok B API F stk empty j L A regs mem md ra p n pl peak cnt b0 ENT) as RET.
  pose proof ENT as ((PRE & _ & _ & _ & _ & _ & _ & SP47) & SYMS & _ & _ & SLK & RO & _ & FRM & _).
  pose proof PRE as (MR0 & WF0 & BD0 & INIT0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & _).
  pose proof SYMS as (_ & _ & _ & _ & GD & GG & TPB & EOF).
  pose proof alloc_ceiling_val as HCV.
  split; [exact HSEG|]. split; [rewrite TPB; reflexivity|]. split; [exact (ent_errno B SYMS)|].
  split; [rewrite GG; reflexivity|]. split; [rewrite GD; reflexivity|].
  split.
  { split; [exact MR0|]. split; [exact WF0|]. split; [exact BD0|]. split; [exact RET|]. split; [exact SP16|].
    split; [exact SPC|]. split; [exact SP63|]. split; [exact WIN0|]. split; [exact TP0|]. split; [exact ERRW0|].
    intros Hf. rewrite INIT0 in Hf. discriminate. }
  split; [exact SP47|]. split; [unfold strtod_c.STRTOD_GLOBALS_TOP; lia|]. split; [exact FRM|].
  exact (rd_cells_of_MR B API HSEG AX FG L A mem md MR0 RO).
Qed.

Lemma ent_env_mid : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A mem md Lam peak cnt bnd regs K,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak cnt bnd ->
  spZ regs = spZ regs0 - 112 -> getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs 1) ->
  0 <= K -> 112 + K <= stk ->
  @reader_env fx1 rc B API K L A regs mem md.
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd regs K
    ENT INV HSP HTP HRA HK0 HK1.
  pose proof (ent_env0 stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT)
    as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _ & H10).
  pose proof INV as (RS & _ & INIT & RD & FRM & _).
  pose proof ENT as (((_ & _ & _ & _ & _ & SP16 & _) & _) & _).
  apply (reader_env_mid (fx := fx1) B API HSEG AX FG stk L0 A0 regs0 mem0 md0 ent_W L A mem md regs K 112
    (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj FRM H10))))))))) RS INIT RD FRM);
    [exact HSP | rewrite HSP; Z.div_mod_to_equations; lia | exact HTP | exact HRA | lia | lia | lia].
Qed.

Lemma ent_post_intro : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx' : YK11.FPState) L A regs mem md peak cnt bnd,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  rstep B API stk (spZ regs0) ent_W (fun _ => False) L0 A0 mem0 md0 L A mem md ->
  (forall a k, In (a, k) (blocks L0 A0) -> k <= 0 -> In (a, k) (blocks L A)) ->
  st_init_done A = true -> ro_agree segs mem -> frm_zero (@fp_csr fx') ->
  ledger B L A mem [] peak cnt (2 ^ 64 - 1) -> cnt <= Z.of_nat (S j) * 2 ^ 60 ->
  rf_ok F A bnd ->
  regs_preserved regs0 regs -> getr regs 10 = Z_to_bv 64 0 ->
  ent_cpost B API F stk j L0 A0 regs0 mem0 md0 ra p n bnd (mkCfg (@mkst fx' regs (Z_to_bv 64 ra) mem (seg_rom segs)) md).
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx' L A regs mem md peak cnt bnd
    ENT RS Z0 INIT RO FRM LED CNT RES RP R10.
  pose proof ENT as (PREW & SYMS & SINKS & _ & SLK & _ & _ & _ & _ & _ & HJ & _).
  pose proof PREW as (PRE & _ & _ & SINK & _ & FSS & _ & _).
  pose proof PRE as (MR0 & WF0 & BD0 & INIT0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & _).
  pose proof RS as (MRc & WFc & BDc & INc & KBc & MDc & ACc & IMc & BKc & WRc).
  pose proof (ent_img_low B HSEG) as (HIL & _).
  pose proof alloc_ceiling_val as HCV.
  pose proof (ent_errno B SYMS) as ERRB.
  pose proof MDc as (vm' & Emd).
  assert (HSTG : forall a, ent_W a -> in_globals slot_G a).
  { intros a Ha. unfold in_globals, slot_G, GL_runs. unfold ent_W in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
    - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha.
      destruct Ha as [H|[H|[H|H]]].
      + exists GL_OWN_RAN_OUT, 40. split; [right; left; reflexivity | unfold GL_OWN_RAN_OUT; lia].
      + exists GL_OWN_RAN_OUT, 40. split; [right; left; reflexivity | unfold GL_OWN_RAN_OUT; lia].
      + exists GL_OWN_RAN_OUT, 40. split; [right; left; reflexivity | unfold GL_OWN_RAN_OUT; lia].
      + exists GL_FAIL, 16. split; [left; reflexivity | unfold GL_FAIL; lia].
    - unfold fuzz_alloc_ran_out_c.G_RAN_OUT in Ha.
      exists GL_OWN_RAN_OUT, 40. split; [right; left; reflexivity | unfold GL_OWN_RAN_OUT; lia].
    - exists GL_OWN_RAN_OUT, 40. split; [right; left; reflexivity | lia].
    - exists GL_FAIL, 16. split; [left; reflexivity | unfold GL_FAIL, GL_MOST in *; lia]. }
  assert (IMG : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals slot_G a ->
     mbyte segs mem a = mbyte segs mem0 a /\ (writable_at segs mem0 a <-> writable_at segs mem a)).
  { intros a Hi Hso Hctx Herr Hg. apply IMc; [exact Hi | | |].
    - intros L1 A1 m1 d1 HM [Ho|Ho]; [exact (Hctx (ax_img AX L1 A1 m1 d1 a HM Hi Ho)) | exact (Hso Ho)].
    - intros [Hr|Hr]; [pose proof (HIL a Hi); lia | exact (Herr Hr)].
    - intros Hst. exact (Hg (HSTG a Hst)). }
  assert (GW : forall a m, in_globals slot_G a -> writable_at segs m a).
  { intros a m (lo & len & Hin & Ha). unfold slot_G, GL_runs in Hin.
    assert (Hc : seg_win_check (ms_segs B) lo (Z.to_nat len) = true /\ 0 <= len).
    { rewrite HSEG. destruct Hin as [E|[E|[]]]; injection E as E1 E2; subst lo len;
        (split; [vm_compute; reflexivity | lia]). }
    destruct Hc as [Hc Hl]. exact (seg_win_wview (ms_segs B) lo len m a Hc Hl Ha). }
  assert (BLK : forall q k i, In (q, k) (user_blocks A0) -> 0 <= i < k ->
     mbyte segs mem (ptr_addr L0 q + i) = mbyte segs mem0 (ptr_addr L0 q + i)).
  { intros q k i Hq Hi. exact (ent_blk_W B API HSEG FA stk (spZ regs0) ent_W L0 A0 mem0 md0 L A mem md q k i
      MR0 RS (fun x h => h) Hq Hi). }
  assert (SKC : forall a, slot_sink_cell a -> mbyte segs mem a = mbyte segs mem0 a).
  { intros a Hc. destruct (SINKS a Hc) as ((Hi & Hso & Hctx & Herr) & Hng).
    exact (proj1 (IMG a Hi Hso Hctx Herr Hng)). }
  exists fx', L, A, regs, mem, md.
  split; [reflexivity|]. split; [exact FRM|].
  split.
  2: { split.
       - pose proof LED as (W & HP & HC & _). cbn [lsum] in HP.
         exists peak, cnt. split; [exact W|]. split; [lia|]. split; [lia|]. lia.
       - exact RES. }
  split; [exact MRc|]. split; [exact WFc|]. split; [exact BDc|]. split; [exact INIT|]. split; [exact R10|].
  split; [exact RP|].
  split.
  { exists vm', (m_fds md0), (m_statpins md0). split; [rewrite Emd; apply with_vmmaps_os_upd | intros k; reflexivity]. }
  split.
  { intros q k Hq.
    pose proof (rg_blk_of B API HSEG AX FG L0 A0 q k Hq) as Hb.
    assert (Hb' : In (ptr_addr L0 q, k) (blocks L A)).
    { destruct (Z_le_gt_dec k 0) as [Hk|Hk]; [exact (Z0 _ _ Hb Hk) | exact (KBc _ _ Hb ltac:(lia) (fun h => h))]. }
    destruct (rg_blk_in B API HSEG AX FG L A _ _ Hb') as (q' & Hq' & E). exists q'. split; [exact Hq' | exact E]. }
  split.
  { intros a Ha Hs. apply ACc; [exact Ha | exact Hs |]. intros Hst. pose proof (ent_W_lo a Hst). lia. }
  split; [exact IMG|].
  split; [intros a Hg; split; intros _; apply GW; exact Hg|].
  split; [intros q k i Hq _ Hi; exact (BLK q k i Hq Hi)|].
  split; [intros a Ha; exact (WRc a Ha)|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact FSS|].
  split.
  { destruct SINK as ((Ht & Hl) & Hh & Hn). split; [split|split].
    - apply (val_mem_frame B mem0 mem); [|exact Ht]. intros x Hx. apply SKC. unfold slot_sink_cell.
      right. left. cbn in Hx. lia.
    - apply (val_mem_frame B mem0 mem); [|exact Hl]. intros x Hx. apply SKC. unfold slot_sink_cell.
      right. right. cbn in Hx. lia.
    - apply (word_mem_frame (ms_segs B) mem0 mem); [exact Hh|]. intros k Hk. apply SKC. unfold slot_sink_cell.
      left. lia.
    - rewrite Emd, with_vmmaps_os_upd. exact Hn. }
  split; [exact RO|].
  exact (ent_pay_W B API HSEG FA stk empty L0 A0 regs0 mem0 md0 ra p n pl stk (spZ regs0) ent_W L A mem md
    PREW RS (fun x h => h)).
Qed.

Lemma ent_fin : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A regs mem md peak cnt bnd,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md [] peak cnt bnd ->
  cnt <= Z.of_nat (S j) * 2 ^ 60 ->
  getr regs 2 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  getr regs 22 = getr regs0 22 -> getr regs 23 = getr regs0 23 -> getr regs 24 = getr regs0 24 ->
  getr regs 25 = getr regs0 25 -> getr regs 26 = getr regs0 26 -> getr regs 27 = getr regs0 27 ->
  SR segs (mkCfg (@mkst fx1 regs (Z_to_bv 64 0x137e4) mem (seg_rom segs)) md)
    (ent_cpost B API F stk j L0 A0 regs0 mem0 md0 ra p n bnd).
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs mem md peak cnt bnd
    ENT INV CNT G2 G3 G4 G22 G23 G24 G25 G26 G27.
  pose proof (ent_ret_ok B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT) as RET.
  pose proof ENT as ((PRE & _) & _ & _ & _ & SLK & _).
  pose proof PRE as (MR0 & _ & _ & _ & RA0 & SP16 & SPC & SP63 & _).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & LED & RES & _ & SL8 & SL16 & SL24 & SL32 & SL40 & SL48 & SL56 & _).
  pose proof RS as (MRc & _).
  pose proof alloc_ceiling_val as HCV.
  assert (HK : SLOT_K = 14704) by reflexivity.
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  eapply (ent_kA B HSEG fx1 regs _ mem md _ _ Hh Hz).
  { unfold rmk. rewrite G2.
    apply (ent_epi (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8)
      (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15)
      (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
      (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
      (getr regs 30) (getr regs 31) (@fp_regs fx1) (@fp_csr fx1) mem (spZ regs0 - 112)
      (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20)
      (getr regs0 21)); [lia | lia | | | | | | |].
    - apply (ent_slot _ _ (spZ regs0 - 8)); [lia | rewrite <- HSEG; exact SL8].
    - apply (ent_slot _ _ (spZ regs0 - 16)); [lia | rewrite <- HSEG; exact SL16].
    - apply (ent_slot _ _ (spZ regs0 - 24)); [lia | rewrite <- HSEG; exact SL24].
    - apply (ent_slot _ _ (spZ regs0 - 32)); [lia | rewrite <- HSEG; exact SL32].
    - apply (ent_slot _ _ (spZ regs0 - 40)); [lia | rewrite <- HSEG; exact SL40].
    - apply (ent_slot _ _ (spZ regs0 - 48)); [lia | rewrite <- HSEG; exact SL48].
    - apply (ent_slot _ _ (spZ regs0 - 56)); [lia | rewrite <- HSEG; exact SL56]. }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  ent_inj HQ R pc' mem1.
  apply SR_ret. rewrite (kb_ret_pc _ RET), RA0.
  apply (ent_post_intro stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A regs1 mem md peak cnt bnd
    ENT RS Z0 INIT (proj1 RD) FRM LED CNT RES).
  - intros r Hr. unfold callee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    rewrite HGr.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
    + transitivity (Z_to_bv 64 (spZ regs0 - 112 + 112)); [reflexivity|].
      replace (spZ regs0 - 112 + 112) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
    + transitivity (getr regs 3); [reflexivity | exact G3].
    + transitivity (getr regs 4); [reflexivity | exact G4].
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + transitivity (getr regs 22); [reflexivity | exact G22].
    + transitivity (getr regs 23); [reflexivity | exact G23].
    + transitivity (getr regs 24); [reflexivity | exact G24].
    + transitivity (getr regs 25); [reflexivity | exact G25].
    + transitivity (getr regs 26); [reflexivity | exact G26].
    + transitivity (getr regs 27); [reflexivity | exact G27].
  - rewrite HGr. reflexivity.
Qed.

Lemma ent_post_pg : forall stk L A regs mem md p n l L' A' regs' mem' md' cs b,
  CF.EntrySR.ent_post B API stk L A regs mem md p n l L' A' regs' mem' md' ->
  res_ok_pack A' (PB (pb_live b) (pb_bytes b) cs) ->
  lib_post_pg B API cs slot_G stk L A regs mem md p n b l L' A' regs' mem' md'.
Proof.
  intros stk L A regs mem md p n l L' A' regs' mem' md' cs b
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19) HR.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
    (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj HR H19))))))))))))))))))).
Qed.

End G.

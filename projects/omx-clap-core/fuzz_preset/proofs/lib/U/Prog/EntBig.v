From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YL0b YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes EntC1_Defs EntC1_Glue LLVMFuzzerTestOneInput_c EntSegA EntryDefs EntrySR EntBase EntGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c fuzz_alloc_ran_out_c fuzz_alloc_ran_out_reset_c fuzz_alloc_most_c.
Import ListNotations.
Local Open Scope Z_scope.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.

Hypothesis HRST : fuzz_alloc_ran_out_reset_c.fuzz_alloc_ran_out_reset_contract.
Hypothesis HMOST : fuzz_alloc_most_c.fuzz_alloc_most_contract.

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.

Lemma ent_munch : forall stk empty j L A regs mem md ra p n pl peak cnt b0 m1,
  ent_pre (fx := fx) B API F stk empty j L A regs mem md ra p n pl peak cnt b0 ->
  EFrame.munch [(spZ regs - 56, spZ regs)] mem m1 -> EFrame.wmono rsegs mem m1 ->
  rstep B API stk (spZ regs) alloc_statics (fun _ => False) L A mem md L A m1 md /\
  ledger B L A m1 [] peak cnt (2 ^ 64 - 1) /\ ro_agree segs m1.
Proof.
  intros stk empty j L A regs mem md ra p n pl peak cnt b0 m1 ENT MU WM.
  pose proof ENT as ((PRE & _) & SYMS & _ & _ & SLK & RO & _ & _ & LED & _).
  pose proof PRE as (MR0 & WF0 & BD0 & _ & _ & _ & SPC & SP63 & WIN0 & _ & ERRW0 & _).
  pose proof alloc_ceiling_val as HCV.
  pose proof (ent_errno B SYMS) as ERRB.
  assert (HK : SLOT_K = 14704) by reflexivity.
  assert (ST0e : rstep B API stk (spZ regs) (fun _ => False) (fun _ => False) L A mem md L A m1 md).
  { apply (rstep_of_munch B API HSEG AX FG stk (spZ regs) (fun _ => False) (fun _ => False) L A mem m1 md
      [(spZ regs - 56, spZ regs)] MR0 WF0 BD0).
    - intros a [Ha|Ha]; [apply WIN0; exact Ha | apply ERRW0; exact Ha].
    - exact MU.
    - rewrite HSEG. exact WM.
    - intros x Hx Hn. left. unfold rwin. left.
      destruct (Z_lt_le_dec x (spZ regs - 88)) as [H1|H1]; [exfalso; apply Hn; apply outside_one; lia|].
      destruct (Z_lt_le_dec x (spZ regs)) as [H2|H2]; [lia | exfalso; apply Hn; apply outside_one; lia].
    - intros x Hx _. apply outside_one. lia. }
  split.
  { apply (rstep_E B API HSEG AX FG stk (spZ regs) (fun _ => False) alloc_statics (fun _ => False) (fun _ => False)
      L A mem md L A m1 md ST0e); intros a []. }
  split.
  { apply (ledger_rstep B API HSEG AX FG stk (spZ regs) (fun _ => False) (fun _ => False) L A mem md L A m1 md [] peak
      cnt (2 ^ 64 - 1) MR0 LED ST0e).
    - intros a Ha. split; [|intros []]. unfold rwin. rewrite ERRB. unfold strtod_c.STRTOD_ERRNO.
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. lia.
    - intros a k []. }
  assert (HLO : alloc_ceiling <= spZ regs - 56) by lia.
  exact (ent_ro_munch B HSEG mem m1 (spZ regs - 56) (spZ regs) RO MU HLO).
Qed.

Lemma ent_a1 : forall stk empty j L A regs mem md ra p n pl peak cnt b0,
  ent_pre (fx := fx) B API F stk empty j L A regs mem md ra p n pl peak cnt b0 ->
  bv_unsigned (getr regs 11) = ent_n pl.
Proof.
  intros stk empty j L A regs mem md ra p n pl peak cnt b0 ENT.
  pose proof ENT as ((PRE & HN & _) & _).
  pose proof PRE as (MR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R11 & PAY & _).
  pose proof alloc_ceiling_val as HCV.
  assert (Hn : 0 <= n < 2 ^ 64).
  { destruct PAY as [(Hn & _)|(Hn & q & Hq & _)]; [lia|].
    destruct (rg_blk B API HSEG AX FG L A mem md (ptr_addr L q) n 0 MR0 (rg_blk_of B API HSEG AX FG L A q n Hq)
      ltac:(lia)) as (_ & H1 & H2 & _).
    lia. }
  rewrite R11, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
  unfold ent_n. exact HN.
Qed.

Lemma entry_big_pre : forall stk empty j L A regs mem md ra p n pl peak cnt b0,
  ent_pre (fx := fx) B API F stk empty j L A regs mem md ra p n pl peak cnt b0 ->
  0x300000 < ent_n pl ->
  SR segs (mkCfg (mkst regs (Z_to_bv 64 LLVMFUZZERTESTONEINPUT) mem (seg_rom segs)) md)
    (ent_sr_post B API F stk j L A regs mem md ra p n pl cnt b0).
Proof.
  intros stk empty j L A regs mem md ra p n pl peak cnt b0 ENT HBIG.
  pose proof (ent_ret_ok B API F stk empty j L A regs mem md ra p n pl peak cnt b0 ENT) as RET.
  pose proof (ent_a1 stk empty j L A regs mem md ra p n pl peak cnt b0 ENT) as HA1.
  pose proof (ent_env0 B API F HSEG FA stk empty j L A regs mem md ra p n pl peak cnt b0 ENT) as REN.
  pose proof REN as (_ & _ & _ & _ & _ & CPK & _).
  pose proof ENT as ((PRE & _) & _ & _ & _ & SLK & _ & _ & FRM & LED & CNT & HJ & RES).
  pose proof PRE as (MR0 & WF0 & BD0 & INIT0 & RA0 & _ & SPC & SP63 & _).
  pose proof alloc_ceiling_val as HCV.
  assert (HK : SLOT_K = 14704) by reflexivity.
  destruct (kb_md B API L A mem md MR0) as (Hh & Hz).
  assert (HSP : Z_to_bv 64 (spZ regs) = getr regs 2) by (unfold spZ; apply Z_to_bv_bv_unsigned).
  pose proof (kb_stk B API (ent_img_low B HSEG) stk L A regs mem md CPK ltac:(lia)) as Hstk.
  pose proof (ent_stk_sub _ mem _ _ (spZ regs - 56) (spZ regs) Hstk ltac:(lia) ltac:(lia) ltac:(lia)) as Hstk1.
  rewrite HSEG in Hstk1.
  unfold LLVMFUZZERTESTONEINPUT.
  eapply (ent_kA B HSEG fx regs _ mem md _ _ Hh Hz).
  { unfold rmk. rewrite <- HSP.
    apply (ent_segA (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8)
      (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15)
      (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
      (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
      (getr regs 30) (getr regs 31) (@fp_regs fx) (@fp_csr fx) mem (spZ regs)); [lia | exact Hstk1]. }
  { intros ms' (m' & _ & _ & [(_ & E) | (_ & _ & _ & _ & _ & _ & _ & _ & _ & E)]);
      eexists _, _, _; exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  destruct HQ as (m1 & MU & WM & [(_ & E) | (HLE & _)]); [|exfalso; lia].
  ent_inj E R pc' mem1.
  destruct (ent_munch stk empty j L A regs mem md ra p n pl peak cnt b0 m1 ENT MU WM) as (ST & LED1 & RA1).
  pose proof (rstep_E B API HSEG AX FG _ _ _ ent_W _ _ _ _ _ _ _ _ _ _ ST (fun a h => or_introl h) (fun a h => h)) as STW.
  apply SR_ret. rewrite (kb_ret_pc _ RET), RA0.
  apply (ent_sr_of_cpost B API F stk j L A regs mem md ra p n pl cnt b0 [] [] [] [] 0 b0 [] [] []);
    [exact (entry_wit_big F b0 cnt pl [] [] [] [] 0 b0 [] [] [] HBIG)|].
  rewrite (entry_fold_big F b0 cnt pl [] [] [] [] 0 b0 [] [] [] HBIG).
  apply (ent_post_intro B API F HSEG FA stk empty j L A regs mem md ra p n pl peak cnt b0 fx L A regs1 m1 md peak cnt b0
    ENT STW (fun a k h _ => h) INIT0 RA1 FRM LED1 ltac:(lia) RES).
  - intros r Hr. unfold callee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    rewrite HGr.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      [transitivity (Z_to_bv 64 (spZ regs)); [reflexivity | exact HSP] | reflexivity ..].
  - rewrite HGr. reflexivity.
Qed.

Lemma entry_big : forall ra empty stk,
  slot_syms B -> slot_globals B -> slot_sinks B -> ra mod 2 = 0 -> 0 < empty < 2 ^ 62 -> SLOT_K <= stk ->
  forall (j : nat) L A regs mem md p n pl (peak cnt : Z) (b0 : rf_R F),
    (j < 4)%nat ->
    lib_pre_w B API stk empty L A regs mem md ra p n pl ->
    G_img_c B frame_RELRO mem -> ro_agree segs mem -> spZ regs <= TASK_SIZE -> frm_zero fp_csr ->
    ledger B L A mem [] peak cnt (2 ^ 64 - 1) -> cnt <= Z.of_nat j * 2 ^ 60 ->
    rf_ok F A b0 ->
    0x300000 < ent_n pl ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 LLVMFUZZERTESTONEINPUT) mem (seg_rom segs)) md)
      (ent_sr_post B API F stk j L A regs mem md ra p n pl cnt b0).
Proof.
  intros ra empty stk SYMS _ SINKS RAE _ SLK j L A regs mem md p n pl peak cnt b0 HJ PREW _ RO TS FRM LED CNT RES HBIG.
  exact (entry_big_pre stk empty j L A regs mem md ra p n pl peak cnt b0
    (conj PREW (conj SYMS (conj SINKS (conj RAE (conj SLK (conj RO (conj TS (conj FRM (conj LED (conj CNT
      (conj HJ RES))))))))))) HBIG).
Qed.

Lemma ent_cells_rw : forall a : word,
  (GL_OWN_RAN_OUT <= bv_unsigned a < GL_OWN_RAN_OUT + 1 \/
   fuzz_alloc_ran_out_reset_c.G_RAN_OUT <= bv_unsigned a < fuzz_alloc_ran_out_reset_c.G_RAN_OUT + 1 \/
   fuzz_alloc_most_c.G_MOST <= bv_unsigned a < fuzz_alloc_most_c.G_MOST + 8) ->
  EMem.ro_addr rsegs a = false.
Proof.
  intros a Ha. unfold EMem.ro_addr.
  unfold GL_OWN_RAN_OUT, fuzz_alloc_ran_out_reset_c.G_RAN_OUT, fuzz_alloc_most_c.G_MOST in Ha.
  assert (E : bv_unsigned a = 0x35250 \/ bv_unsigned a = 0x35258 \/ bv_unsigned a = 0x24fe0 \/
              bv_unsigned a = 0x24fe1 \/ bv_unsigned a = 0x24fe2 \/ bv_unsigned a = 0x24fe3 \/
              bv_unsigned a = 0x24fe4 \/ bv_unsigned a = 0x24fe5 \/ bv_unsigned a = 0x24fe6 \/
              bv_unsigned a = 0x24fe7) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]; rewrite E; vm_compute; reflexivity.
Qed.

Lemma ent_cells_wr : forall lo n0 m, seg_win_check rsegs lo (Z.to_nat n0) = true -> 0 <= lo -> 0 <= n0 ->
  lo + n0 <= 2 ^ 64 -> EMem.wr_at rsegs m lo n0.
Proof.
  intros lo n0 m Hc Hl Hn Hh. split; [exact Hl|]. split; [exact Hh|].
  intros i Hi. apply (seg_win_wview rsegs lo n0 m (lo + i) Hc Hn). lia.
Qed.

(* 0x13718 .. 0x1376c: the prologue, the size test (small arm), g_own_ran_out = 0, fuzz_alloc_ran_out_reset(),
   fuzz_alloc_most(PJ_ALLOC_BOUND(size)), and the call of check_no_overread(data, size) *)
Lemma ent_start : forall stk empty j L A regs mem md ra p n pl peak cnt b0 (P : config -> Prop),
  ent_pre (fx := fx) B API F stk empty j L A regs mem md ra p n pl peak cnt b0 ->
  ent_n pl <= 0x300000 ->
  (forall regs1 mem1,
     ent_inv B API F stk L A regs mem md p n fx L A mem1 md [] peak cnt b0 ->
     ent_flags segs mem1 ->
     getr regs1 1 = Z_to_bv 64 0x13770 -> getr regs1 2 = Z_to_bv 64 (spZ regs - 112) ->
     getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
     getr regs1 22 = getr regs 22 -> getr regs1 23 = getr regs 23 -> getr regs1 24 = getr regs 24 ->
     getr regs1 25 = getr regs 25 -> getr regs1 26 = getr regs 26 -> getr regs1 27 = getr regs 27 ->
     getr regs1 8 = getr regs 11 -> getr regs1 9 = getr regs 10 ->
     getr regs1 10 = getr regs 10 -> getr regs1 11 = getr regs 11 ->
     getr regs1 21 = Z_to_bv 64 (GL_OWN_RAN_OUT + 0x4f8) ->
     SR segs (mkCfg (mkst regs1 (Z_to_bv 64 0x13868) mem1 (seg_rom segs)) md) P) ->
  SR segs (mkCfg (mkst regs (Z_to_bv 64 LLVMFUZZERTESTONEINPUT) mem (seg_rom segs)) md) P.
Proof.
  intros stk empty j L A regs mem md ra p n pl peak cnt b0 P ENT HSMALL KONT.
  pose proof (ent_a1 stk empty j L A regs mem md ra p n pl peak cnt b0 ENT) as HA1.
  pose proof (ent_env0 B API F HSEG FA stk empty j L A regs mem md ra p n pl peak cnt b0 ENT) as REN.
  pose proof REN as (_ & _ & _ & _ & _ & CPK & _).
  pose proof ENT as (PREW & SYMS & _ & _ & SLK & _ & _ & FRM & LED & CNT & HJ & RES).
  pose proof PREW as (PRE & _).
  pose proof PRE as (MR0 & WF0 & BD0 & INIT0 & _ & _ & SPC & SP63 & _).
  pose proof alloc_ceiling_val as HCV.
  pose proof (ent_errno B SYMS) as ERRB.
  assert (HK : SLOT_K = 14704) by reflexivity.
  destruct (kb_md B API L A mem md MR0) as (Hh & Hz).
  assert (HSP : Z_to_bv 64 (spZ regs) = getr regs 2) by (unfold spZ; apply Z_to_bv_bv_unsigned).
  pose proof (kb_stk B API (ent_img_low B HSEG) stk L A regs mem md CPK ltac:(lia)) as Hstk.
  pose proof (ent_stk_sub _ mem _ _ (spZ regs - 56) (spZ regs) Hstk ltac:(lia) ltac:(lia) ltac:(lia)) as Hstk1.
  rewrite HSEG in Hstk1.
  unfold LLVMFUZZERTESTONEINPUT.
  eapply (ent_kA B HSEG fx regs _ mem md _ _ Hh Hz).
  { unfold rmk. rewrite <- HSP.
    apply (ent_segA (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8)
      (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15)
      (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
      (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
      (getr regs 30) (getr regs 31) (@fp_regs fx) (@fp_csr fx) mem (spZ regs)); [lia | exact Hstk1]. }
  { intros ms' (m' & _ & _ & [(_ & E) | (_ & _ & _ & _ & _ & _ & _ & _ & _ & E)]);
      eexists _, _, _; exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  destruct HQ as (m1 & MU & WM & [(HGT & _) |
    (_ & B8 & B16 & B24 & B32 & B40 & B48 & B56 & WR & E)]); [exfalso; lia|].
  ent_inj E R pc' mem1.
  destruct (ent_munch stk empty j L A regs mem md ra p n pl peak cnt b0 m1 ENT MU WM) as (ST & LED1 & RA1).
  pose proof ST as (MR1 & _ & _ & _ & _ & _ & _ & _ & _ & WR1).
  assert (G2 : getr regs1 2 = Z_to_bv 64 (spZ regs - 112)) by (rewrite HGr; reflexivity).
  pose proof (ent_cells_wr GL_OWN_RAN_OUT 1 m1 ltac:(vm_compute; reflexivity) ltac:(unfold GL_OWN_RAN_OUT; lia)
    ltac:(lia) ltac:(unfold GL_OWN_RAN_OUT; lia)) as W1.
  pose proof (ent_cells_wr fuzz_alloc_ran_out_reset_c.G_RAN_OUT 1 m1 ltac:(vm_compute; reflexivity)
    ltac:(unfold fuzz_alloc_ran_out_reset_c.G_RAN_OUT; lia) ltac:(lia)
    ltac:(unfold fuzz_alloc_ran_out_reset_c.G_RAN_OUT; lia)) as W2.
  pose proof (ent_cells_wr fuzz_alloc_most_c.G_MOST 8 m1 ltac:(vm_compute; reflexivity)
    ltac:(unfold fuzz_alloc_most_c.G_MOST; lia) ltac:(lia) ltac:(unfold fuzz_alloc_most_c.G_MOST; lia)) as W3.
  eapply (ent_kA B HSEG fx regs1 _ m1 md _ _ Hh Hz).
  { unfold rmk. rewrite G2.
    exact (ent_segA2 HRST HMOST (getr regs1 1) (getr regs1 3) (getr regs1 4) (getr regs1 5) (getr regs1 6)
      (getr regs1 7) (getr regs1 8) (getr regs1 9) (getr regs1 10) (getr regs1 11) (getr regs1 12) (getr regs1 13)
      (getr regs1 14) (getr regs1 15) (getr regs1 16) (getr regs1 17) (getr regs1 18) (getr regs1 19) (getr regs1 20)
      (getr regs1 21) (getr regs1 22) (getr regs1 23) (getr regs1 24) (getr regs1 25) (getr regs1 26) (getr regs1 27)
      (getr regs1 28) (getr regs1 29) (getr regs1 30) (getr regs1 31) (@fp_regs fx) (@fp_csr fx) m1
      (spZ regs - 112) W1 W2 W3). }
  { intros ms' (m' & _ & _ & _ & _ & E). eexists _, _, _. exact E. }
  intros R2 pc2 mem2 regs2 HQ2 HGr2.
  destruct HQ2 as (m2 & MU2 & WM2 & BO & BR & E2).
  ent_inj E2 R2 pc2 mem2.
  set (EC := fun a : Z => fuzz_alloc_ran_out_c.G_RAN_OUT <= a < fuzz_alloc_ran_out_c.G_RAN_OUT + 1 \/
                          GL_OWN_RAN_OUT <= a < GL_OWN_RAN_OUT + 1 \/
                          fuzz_alloc_most_c.G_MOST <= a < fuzz_alloc_most_c.G_MOST + 8).
  assert (ECW : forall a, EC a -> ent_W a).
  { intros a Ha. unfold ent_W. right. unfold EC in Ha.
    destruct Ha as [H|[H|H]]; [left; exact H | right; left; exact H |].
    right; right. unfold GL_MOST, fuzz_alloc_most_c.G_MOST in *. lia. }
  assert (ECimg : forall a, EC a -> in_img B a /\ forall L1 A1 m d, aa_MR API L1 A1 m d -> ~ owned B L1 A1 a).
  { intros a Ha. split; [exact (ent_W_img B API HSEG FA a (ECW a Ha))|].
    intros L1 A1 m d HM. apply (ent_FG B API FA L1 A1 m d a HM).
    unfold in_globals, frame_G, GL_runs. unfold EC in Ha.
    destruct Ha as [H|[H|H]].
    + exists GL_OWN_RAN_OUT, 40. split; [right; left; reflexivity|].
      unfold fuzz_alloc_ran_out_c.G_RAN_OUT, GL_OWN_RAN_OUT in *. lia.
    + exists GL_OWN_RAN_OUT, 40. split; [right; left; reflexivity | lia].
    + exists GL_FAIL, 16. split; [left; reflexivity|]. unfold fuzz_alloc_most_c.G_MOST, GL_FAIL in *. lia. }
  assert (INW : forall x, ~ EFrame.outside [(GL_OWN_RAN_OUT, GL_OWN_RAN_OUT + 1);
      (fuzz_alloc_ran_out_reset_c.G_RAN_OUT, fuzz_alloc_ran_out_reset_c.G_RAN_OUT + 1);
      (fuzz_alloc_most_c.G_MOST, fuzz_alloc_most_c.G_MOST + 8)] x -> EC x).
  { intros x Hn. unfold EC. cbn [EFrame.outside] in Hn.
    unfold GL_OWN_RAN_OUT, fuzz_alloc_ran_out_reset_c.G_RAN_OUT, fuzz_alloc_most_c.G_MOST,
      fuzz_alloc_ran_out_c.G_RAN_OUT in *.
    destruct (Z_lt_le_dec x 0x35250) as [H1|H1]; [|destruct (Z_lt_le_dec x 0x35251) as [H2|H2]].
    - destruct (Z_lt_le_dec x 0x24fe0) as [H3|H3]; [exfalso; apply Hn; repeat split; lia|].
      destruct (Z_lt_le_dec x 0x24fe8) as [H4|H4]; [right; right; lia | exfalso; apply Hn; repeat split; lia].
    - right; left; lia.
    - destruct (Z_lt_le_dec x 0x35258) as [H3|H3]; [exfalso; apply Hn; repeat split; lia|].
      destruct (Z_lt_le_dec x 0x35259) as [H4|H4]; [left; lia | exfalso; apply Hn; repeat split; lia]. }
  assert (ST2 : rstep B API stk (spZ regs) EC (fun _ => False) L A m1 md L A m2 md).
  { apply (rstep_of_munch B API HSEG AX FG stk (spZ regs) EC (fun _ => False) L A m1 m2 md _ MR1 WF0 BD0 WR1 MU2).
    - rewrite HSEG. exact WM2.
    - intros x Hx Hn. right. exact (INW x Hn).
    - intros x Hx Hob. destruct (kb_outside_dec [(GL_OWN_RAN_OUT, GL_OWN_RAN_OUT + 1);
        (fuzz_alloc_ran_out_reset_c.G_RAN_OUT, fuzz_alloc_ran_out_reset_c.G_RAN_OUT + 1);
        (fuzz_alloc_most_c.G_MOST, fuzz_alloc_most_c.G_MOST + 8)] x) as [Ho|Hn]; [exact Ho|exfalso].
      destruct (ECimg x (INW x Hn)) as (Himg & Hno).
      destruct Hob as [Ho | (q & k & Hb & Hq)].
      + exact (Hno L A m1 md MR1 Ho).
      + destruct (rg_blk_in B API HSEG AX FG L A q k Hb) as (q' & Hq' & Eq).
        apply (ax_blocks_img AX L A m1 md q' k (x - q) MR1 Hq'); [lia|].
        rewrite Eq. replace (q + (x - q)) with x by lia. exact Himg. }
  assert (LED2 : ledger B L A m2 [] peak cnt (2 ^ 64 - 1)).
  { apply (ledger_rstep B API HSEG AX FG stk (spZ regs) EC (fun _ => False) L A m1 md L A m2 md [] peak cnt
      (2 ^ 64 - 1) MR1 LED1 ST2).
    - intros a Ha. pose proof (ent_statics_lo a Ha) as Hl.
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha.
      split; [unfold rwin; rewrite ERRB; unfold strtod_c.STRTOD_ERRNO; lia|].
      unfold EC, fuzz_alloc_ran_out_c.G_RAN_OUT, GL_OWN_RAN_OUT, fuzz_alloc_most_c.G_MOST. lia.
    - intros a k []. }
  assert (RA2 : ro_agree (ms_segs B) m2).
  { intros a Ha. pose proof (RA1 a Ha) as H0.
    destruct (kb_outside_dec [(GL_OWN_RAN_OUT, GL_OWN_RAN_OUT + 1);
        (fuzz_alloc_ran_out_reset_c.G_RAN_OUT, fuzz_alloc_ran_out_reset_c.G_RAN_OUT + 1);
        (fuzz_alloc_most_c.G_MOST, fuzz_alloc_most_c.G_MOST + 8)] (bv_unsigned a)) as [Ho|Hn].
    - unfold EMem.mrd in *. rewrite (MU2 a Ho). exact H0.
    - exfalso. rewrite HSEG in Ha. rewrite (ent_cells_rw a) in Ha; [discriminate|].
      pose proof (INW _ Hn) as He. unfold EC in He.
      destruct He as [H|[H|H]]; [right; left; exact H | left; exact H | right; right; exact H]. }
  assert (STc : rstep B API stk (spZ regs) ent_W (fun _ => False) L A mem md L A m2 md).
  { apply (rstep_E B API HSEG AX FG stk (spZ regs) (fun x => alloc_statics x \/ EC x) ent_W (fun _ => False)
      (fun _ => False) L A mem md L A m2 md).
    - apply (rstep_seq B API HSEG AX FG stk (spZ regs) alloc_statics EC (fun _ => False) (fun _ => False)
        L A mem md L A m1 md L A m2 md ST ST2). intros a k _ _ _ [].
    - intros a [Ha|Ha]; [left; exact Ha | exact (ECW a Ha)].
    - intros a Ha; exact Ha. }
  assert (HBt : forall x bs, alloc_ceiling <= x -> EMem.bytes_at rsegs m1 x bs -> EMem.bytes_at rsegs m2 x bs).
  { intros x bs Hx Hb. apply (EFrame.bytes_at_transport rsegs _ m1 m2 x bs Hb MU2).
    cbn [EFrame.disjoint_from].
    unfold GL_OWN_RAN_OUT, fuzz_alloc_ran_out_reset_c.G_RAN_OUT, fuzz_alloc_most_c.G_MOST.
    repeat (split; [right; lia|]). exact I. }
  apply (KONT regs2 m2).
  - split; [exact STc|].
    split; [intros a k h _; exact h|].
    split; [exact INIT0|].
    split; [exact (rd_cells_of_MR B API HSEG AX FG L A m2 md (proj1 STc) RA2)|].
    split; [exact FRM|].
    split; [exact LED2|].
    split; [exact RES|].
    split; [exact (ent_pay_W B API HSEG FA stk empty L A regs mem md ra p n pl stk (spZ regs) ent_W L A m2 md
                     PREW STc (fun x h => h))|].
    rewrite HSEG.
    split; [exact (HBt (spZ regs - 8) _ ltac:(lia) B8)|]. split; [exact (HBt (spZ regs - 16) _ ltac:(lia) B16)|].
    split; [exact (HBt (spZ regs - 24) _ ltac:(lia) B24)|]. split; [exact (HBt (spZ regs - 32) _ ltac:(lia) B32)|].
    split; [exact (HBt (spZ regs - 40) _ ltac:(lia) B40)|]. split; [exact (HBt (spZ regs - 48) _ ltac:(lia) B48)|].
    split; [exact (HBt (spZ regs - 56) _ ltac:(lia) B56)|].
    exact (EFrame.wr_at_transport rsegs m1 m2 _ _ WR WM2).
  - unfold ent_flags, segs. rewrite HSEG. split; [exact BR | exact BO].
  - rewrite HGr2. reflexivity.
  - rewrite HGr2. reflexivity.
  - transitivity (getr regs1 3); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - transitivity (getr regs1 4); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - transitivity (getr regs1 22); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - transitivity (getr regs1 23); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - transitivity (getr regs1 24); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - transitivity (getr regs1 25); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - transitivity (getr regs1 26); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - transitivity (getr regs1 27); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - transitivity (getr regs1 8); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - transitivity (getr regs1 9); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - transitivity (getr regs1 9); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - transitivity (getr regs1 8); [rewrite HGr2; reflexivity | rewrite HGr; reflexivity].
  - rewrite HGr2. reflexivity.
Qed.

End E.

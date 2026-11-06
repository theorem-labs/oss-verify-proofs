(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ PEnv F_poison F_mm_D F_prim_L0 APrimSpec APrimLem AFrame F_prim_efa APrimPop F_prim_pop F_prim_popf ATacFix APrimPopR F_prim_popt.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section POPF.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Hypothesis AO : alayout_ok AL.
  Notation THR := (at_thr (al_thread AL)).
  Notation STAT := (at_thr (al_thread AL) + CSTATS_OFF).
  Variables (ra gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo c r : Z) (k : pclass) (inited : bool) (m m1 : mem) (H H1 : word -> bool).
  Variables (mu1 cnt mfa2 calloc cmapped cm1 : Z).
  Notation RI := (ri_addr AL c).
  Notation FA := (fa_base AL c).
  Notation SZ := (class_size c).
  Notation REG := (al_space AL + c * 4294967296).
  Notation tot := (p_nf k + cnt).
  Notation k1 := (mkPCL (p_nf k) (p_mfa k) (p_au k) mu1 (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k)).

  Definition pop_W0 : list (Z * Z) :=
    [(lo, q); (al_space AL + 137438953472 + 128 * c, al_space AL + 137438953472 + 128 * c + 128);
     (REG + 3758096384 + 4 * p_nf k, REG + 3758096384 + mfa2); (REG + p_mu k, REG + mu1);
     (REG + 3758096384 + p_mfa k, REG + 3758096384 + mfa2);
     (sh (REG + p_mu k), sh (REG + mu1)); (sh (REG + 3758096384 + p_mfa k), sh (REG + 3758096384 + mfa2));
     (THR + 2768 + 16, THR + 2768 + 32); (THR + 2800, THR + 2800 + 368)].

  #[using="AO"] Lemma pop_finish : forall (x1 t0 t1 t2 s1v s3v s6v a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 : word)
      (j8 j64 j88 j96 j104 j112 : word) (jpad jt : list byte) (nb nsh : nat) (ts : list byte),
    mem_inv asegs m1 -> mclean H1 m1 -> shvis H1 m1 -> poison_env E m1 -> thread_env (al_thread AL) m1 -> prim_env AL m1 ->
    stk asegs m1 lo (q - 64) -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - 64 - 48 - 400 -> q <= 2^47 -> q mod 16 = 0 ->
    1 <= c <= 31 -> 1 <= r <= 8 -> pclass_wf c k ->
    p_mu k + r * class_size c + K_MAP <= FA_OFF -> BUD2P c r k ->
    mu1 = pop_mu k c r -> cnt = pop_new k c r -> mfa2 = efa_new k1 tot ->
    rw_cells asegs m1 RI (ri_cells KWL k1 j8 j64 j88 j96 j104 j112 jpad) ->
    pcl_rep AL m1 inited c k -> fa_rep AL m1 c k ->
    rw_cells asegs m1 (REG + p_au k) [CB nb jt] -> Z.of_nat nb = mu1 - p_au k ->
    rw_cells asegs m1 (sh (REG + p_au k)) [CB nsh (repeat (Z_to_bv 8 250) nsh)] -> 8 * Z.of_nat nsh = mu1 - p_au k ->
    (forall v, In v (p_fa k ++ p_chunks k) -> free_chunk AL m c v) ->
    rw_cells asegs m1 (q - 64) [C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
    rw_cells asegs m1 (STAT + 16) [C8 (wz calloc); C8 (wz cm1)] ->
    rw_cells asegs m1 (THR + TSTATS_OFF) [CB 368 ts] ->
    munch pop_W0 m m1 -> wmono asegs m m1 ->
    H1 = H_opt (negb (mu1 =? p_mu k)) (region AL c + p_mu k) (mu1 - p_mu k) H ->
    cm1 = cmapped + (mu1 - p_mu k) ->
    implA H1 (t_efa AL c k1 tot)
      (populate_post AL E ra gp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F_ fc q lo c r k inited calloc cmapped H m)
      (MS (mkR x1 (wz (q - 64)) gp (wz A0_TP) t0 t1 t2 (wz RI) s1v (wz INSTANCE) a1 a2 (wz (p_au k)) a4 a5 a6 a7
               (wz REG) s3v (wz mu1) (wz SZ) s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x389c4) fc None m1 (seg_rom asegs)).
  Proof.
    intros until ts. intros MI MC SV PE TE PRE ST LOH CLO LO QH Q16 Hc Hr WF BUD1 B2 Hmu1 Hcnt Hmfa2 RIC PCL FAR TL Hnb TSH Hnsh FCH FR STC TS MU WM EH1 Ecm.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. layout_facts AO 3%nat THF.
    destruct SPF as (SP1 & SP2 & SP3 & _ & SP5 & _ & _). destruct THF as (TH1 & TH2 & TH3 & _ & TH5 & _ & _).
    pose proof AO as AO'. destruct AO' as (_ & _ & SPAL & TLO & _ & _).
    pose proof (region_range AL c Hc) as RR. unfold region in RR.
    layout_apart_fact AO 0%nat 3%nat AP03.
    pose proof (SZ_facts c r k Hc Hr) as (CS & CS16 & RS & RS8).
    pose proof (pop_mu_facts c r k Hc Hr WF BUD1) as (M1 & M2 & M3 & M4 & M5 & _). rewrite <- ?Hmu1 in M1, M2, M3, M4, M5.
    pose proof (pop_new_facts c r k Hc Hr WF BUD1) as (N0 & N1 & N2 & N3). rewrite <- ?Hmu1, <- ?Hcnt in N0, N1, N2, N3.
    pose proof WF as WF0. unfold pclass_wf in WF0.
    destruct WF0 as (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & MUM & AUS & GAP & ND & FB & NA & NFR).
    assert (TB : 4 * tot + K_MAP <= K_FA_SIZE) by (unfold BUD2P in B2; lia).
    pose proof (efa_new_facts c r k k1 tot ltac:(cbn; lia) ltac:(cbn; exact MFAM) ltac:(lia) TB) as (F1 & F2 & F3 & F4).
    cbn [p_mfa] in F1, F2, F3, F4. rewrite <- Hmfa2 in F1, F2, F3, F4.
    clear N3 AUS GAP ND FB CNT Lcnt.

    assert (FAM : (REG + 3758096384 + p_mfa k) mod 32768 = 0) by (clear - SPAL MFAM; Z.div_mod_to_equations; lia).
    assert (DM : (mfa2 - p_mfa k) mod 32768 = 0) by (clear - F3 MFAM; Z.div_mod_to_equations; lia).
    pose proof (sw_exact _ _ FAM DM) as (SWE1 & SWE2 & SWE3). clear FAM DM.
    replace (REG + 3758096384 + p_mfa k + (mfa2 - p_mfa k)) with (REG + 3758096384 + mfa2) in SWE2, SWE3 by lia.

    assert (SHA1 : sh (REG + p_au k) <= sh (REG + p_mu k)) by (apply sh_le; lia).
    assert (SHF1 : sh (REG + p_au k) <= sh (REG + 3758096384 + p_mfa k)) by (apply sh_le; lia).
    assert (SHU1 : sh (REG + mu1) <= 17594333495296) by (pose proof (sh_le (REG + mu1) (2^47) ltac:(lia)) as X; exact X).
    assert (SHU2 : sh (REG + 3758096384 + mfa2) <= 17594333495296) by (pose proof (sh_le (REG + 3758096384 + mfa2) (2^47) ltac:(lia)) as X; exact X).
    assert (SHM1 : sh (REG + p_mu k) <= sh (REG + mu1)) by (apply sh_le; lia).
    assert (SHM2 : sh (REG + 3758096384 + p_mfa k) <= sh (REG + 3758096384 + mfa2)) by (apply sh_le; lia).
    assert (SHL0 : 2147450880 <= sh (REG)) by (pose proof (sh_le 0 REG ltac:(lia)) as X; exact X).
    assert (SHR : sh REG <= sh (REG + p_au k)) by (apply sh_le; lia).

    assert (FCH1 : forall v, In v (p_fa k ++ p_chunks k) -> free_chunk AL m1 c v).
    { eapply (free_chunks_frame AL AO c k Hc WF pop_W0 m m1 MU WM); [| exact FCH].
      unfold carved_clear, pop_W0, region. clear - SPAL SP1 SP2 RR AP03 TH1 TH2 AU MUF M1 M5 MFA F2 F4 Lnf CLO LO SHA1 SHF1 SHU1 SHU2 SHM1 SHM2 SHL0 SHR ACR Hc.
      repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd]; repeat split; lia. }
    eapply implA_mono.
    { eapply (pop_tail AL E AO ra gp F_ fc q lo c r k inited m1 H1 mu1 cnt mfa2); try eassumption. }
    intros a H' ms' PO. unfold popT_post in PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & EH & MU' & WM' & MI' & ST' & PE' & TE' & PRE' & SV' & CO' & SR').
    pose proof (populate_shape c r k) as (S_nf & S_au & S_mu & S_fa & S_cnt & S_ch & _ & _ & S_mfa).
    unfold populate_post. exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m'. cbv zeta.
    split; [reflexivity|]. split.
    { rewrite EH, EH1. unfold H_populate. cbv zeta. rewrite <- Hmu1, <- Hcnt. reflexivity. }
    split.
    { rewrite S_mu, S_mfa, <- Hmu1, <- Hcnt, <- Hmfa2.
      eapply munch_trans; [| eapply munch_weaken; [| exact MU']].
      - eapply munch_weaken; [| exact MU]. unfold sub_fp, pop_W0, fa_base, region, ri_addr, RIB; cbn [outside]; intros; lia.
      - unfold sub_fp, popT_W, fa_base, region, ri_addr, RIB; cbn [outside]. rewrite SWE1, SWE2. rewrite <- SWE3.
        clear - LO F1 F2 NF4 N0 SHM2. intros; lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact PE'|]. split; [exact TE'|]. split; [exact PRE'|].
    split; [exact SV'|].
    split; [exact CO'|].
    rewrite S_mu, <- Hmu1, <- Ecm. exact SR'.
  Qed.
End POPF.

Section POP2.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation THR := (at_thr (al_thread AL)).
  Notation STAT := (at_thr (al_thread AL) + CSTATS_OFF).

  #[using="Type"] Theorem populate_spec : populate_stmt AL E.
  Proof.
    unfold populate_stmt.
    intros ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo c r k inited calloc cmapped
           AO MI MC SV PE TE PRE ST LOH CLO LO QH Q16 Hc Hr CO SR BUD1 BUD2 C0 CM0 CMB.
    destruct CO as (WF & (j8 & j64 & j88 & j96 & j104 & j112 & jpad & RIC) & PCL & FAR & TLR & FCH).
    destruct SR as [STC (ts & TS)]. destruct TLR as [(jt & TL) TSH].
    unfold POP_STACK, MF_STACK in LO.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. layout_facts AO 3%nat THF.
    destruct SPF as (SP1 & SP2 & SP3 & _ & SP5 & _ & _). destruct THF as (TH1 & TH2 & TH3 & _ & TH5 & _ & _).
    pose proof AO as AO'. destruct AO' as (_ & _ & SPAL & TLO & _ & _).
    pose proof (region_range AL c Hc) as RR.
    layout_apart_fact AO 0%nat 3%nat AP03.
    pose proof (SZ_facts c r k Hc Hr) as (CS & CS16 & RS & RS8).
    pose proof (pop_mu_facts c r k Hc Hr WF BUD1) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    pose proof (pop_new_facts c r k Hc Hr WF BUD1) as (N0 & N1 & N2 & N3).
    pose proof WF as WF0. unfold pclass_wf in WF0.
    destruct WF0 as (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & MUM & AUS & GAP & ND & FB & NA & NFR).
    pose proof (au_mod16 c r k Hc Hr WF) as AU16.
    assert (SZr : r * class_size c = class_size c * r) by apply Z.mul_comm.
    remember (pop_mu k c r) as mu1 eqn:Hmu1. remember (pop_new k c r) as cnt eqn:Hcnt.
    remember (efa_new (mkPCL (p_nf k) (p_mfa k) (p_au k) mu1 (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k)) (p_nf k + cnt)) as mfa2 eqn:Hmfa2.
    assert (TB : 4 * (p_nf k + cnt) + K_MAP <= K_FA_SIZE) by lia.
    pose proof (efa_new_facts c r k (mkPCL (p_nf k) (p_mfa k) (p_au k) mu1 (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k)) (p_nf k + cnt)
                  ltac:(cbn; lia) ltac:(cbn; exact MFAM) ltac:(lia) TB) as (F1 & F2 & F3 & F4).
    cbn [p_mfa] in F1, F2, F3, F4. rewrite <- Hmfa2 in F1, F2, F3, F4.
    assert (B2 : BUD2P c r k) by exact BUD2. clear BUD2 N3.
    demod SP3. demod TH3. demod SPAL. demod CS16. demod M4. demod MFAM. demod MUM. demod AU16. demod F3. demod Q16. clear AUS.
    destruct PCL as [PC1 (wsc & PA & PL & PX)]. destruct FAR as (ws & FAA & LEN & FX).
    unfold ri_addr, RIB in *. unfold prim_env in PRE. unfold ri_cells in RIC. unfold pcl_addr in PC1, PA. unfold fa_base, region in FAA. unfold region in TL, TSH.
    assert (SHT : sh (al_space AL + c * 4294967296 + p_au k) + (p_mu k - p_au k) / 8 <= 17594333495296).
    { pose proof (sh_le (al_space AL + c * 4294967296 + p_mu k) (2^47) ltac:(unfold region in RR; lia)) as X. change (sh (2^47)) with 17594333495296 in X.
      revert X. unfold sh. rewrite AU0, MUM0, SP0. clear. intros X. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(lo, q); (al_space AL + 137438953472 + 128 * c, al_space AL + 137438953472 + 128 * c + 128);
              (fa_base AL c + 4 * p_nf k, fa_base AL c + mfa2); (region AL c + p_mu k, region AL c + mu1);
              (fa_base AL c + p_mfa k, fa_base AL c + mfa2);
              (sh (region AL c + p_mu k), sh (region AL c + mu1)); (sh (fa_base AL c + p_mfa k), sh (fa_base AL c + mfa2));
              (at_thr (al_thread AL) + CSTATS_OFF + 16, at_thr (al_thread AL) + CSTATS_OFF + 32);
              (at_thr (al_thread AL) + TSTATS_OFF, at_thr (al_thread AL) + TSTATS_OFF + 368)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    lz_go.
    call (pop_A AL AO ra gp F_ fc q lo c r k KWL m t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 j8 j64 j88 j96 j104 j112 jpad).
    1: exact MI.
    1: exact PRE.
    1: exact ST.
    1-8: lia.
    1: exact RIC.
    clear SHT.
    assert (SHL1 : 2147450880 <= sh (region AL c + p_mu k)) by (pose proof (sh_le 0 (region AL c + p_mu k) ltac:(lia)) as X; exact X).
    assert (SHL2 : 2147450880 <= sh (fa_base AL c + p_mfa k)) by (pose proof (sh_le 0 (fa_base AL c + p_mfa k) ltac:(unfold fa_base; lia)) as X; exact X).
    assert (SHU1 : sh (region AL c + mu1) <= 17594333495296) by (pose proof (sh_le (region AL c + mu1) (2^47) ltac:(lia)) as X; exact X).
    assert (SHU2 : sh (fa_base AL c + mfa2) <= 17594333495296) by (pose proof (sh_le (fa_base AL c + mfa2) (2^47) ltac:(unfold fa_base; lia)) as X; exact X).
    lazymatch type of MU with munch ?W0 _ _ => assert (AIW : above_img W0) by (unfold fa_base, region in *; env_clear) end.
    lazymatch type of MU with munch ?W0 _ _ => assert (TCW : thread_clear (al_thread AL) W0) end.
    { pose proof TLO as TL'. unfold thread_layout_ok in TL'. layout_apart_fact AO 0%nat 2%nat AP02.
      destruct TL' as (CX1 & CX2 & _ & _ & CXT & _).
      repeat match goal with
          | H : rw_cells _ _ _ _ |- _ => clear H | H : u32arr _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
          | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
          | H : shvis _ _ |- _ => clear H | H : poison_env _ _ |- _ => clear H | H : thread_env _ _ |- _ => clear H
          | H : above_img _ |- _ => clear H end.
      clear FCH FX PX. unfold fa_base, region in *. env_clear. }
    destruct (Z.ltb_spec (p_mu k) (p_au k + class_size c * r)) as [LT|GE].
    - pose proof (M7 ltac:(lia)) as EMU. clear M6 M7.
      unfold t_populate. cbv zeta. rewrite <- Hmu1, <- Hcnt.
      replace (negb (mu1 =? p_mu k)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; pose proof (rup_ge (p_au k + r * class_size c - p_mu k) K_MAP ltac:(lia)); lia).
      unfold t_opt.
      remember (rup (p_au k + r * class_size c - p_mu k) K_MAP) as msz eqn:Hmsz.
      replace (mu1 - p_mu k) with msz by lia.
      assert (MSZM : msz mod K_MAP = 0) by (rewrite Hmsz; apply rup_mod; lia). demod MSZM.
      assert (MSZP : 0 < msz) by (pose proof (rup_ge (p_au k + r * class_size c - p_mu k) K_MAP ltac:(lia)); lia).
      assert (BEGM : (region AL c + p_mu k) mod 32768 = 0) by (unfold region; rewrite SPAL0, MUM0; clear; Z.div_mod_to_equations; lia).
      assert (MSZ8 : msz mod 32768 = 0) by (rewrite MSZM0; clear; Z.div_mod_to_equations; lia).
      pose proof (sw_exact (region AL c + p_mu k) msz BEGM MSZ8) as (SWE1 & SWE2 & SWE3). clear BEGM MSZ8.
      replace (region AL c + p_mu k + msz) with (region AL c + mu1) in SWE2, SWE3 by lia.
      assert (ERI : ri_addr AL c = al_space AL + 137438953472 + 128 * c) by reflexivity.
      unfold fa_base, region in *.
      lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?xa5 ?xa6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mx _) =>
        callA (pop_B AL E AO gp F_ fc q lo c r k KWL mx H ra t0 t1 t2 xa5 xa6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 j8 j64 j88 j96 j104 j112 jpad jt calloc cmapped msz ts) end.
      1: assumption.
      1: assumption.
      1: eapply shvis_wmono; [exact SV| exact WM].
      1: eapply poison_env_frame; [exact PE| exact MU| exact WM| exact AIW].
      1: eapply thread_env_frame; [exact TE| exact MU| exact WM| exact TCW].
      1: unfold prim_env; assumption.
      1: assumption.
      1-4: lia.
      1: rewrite Q0; apply Z_mod_mult.
      1-3: lia.
      1: rewrite AU0; apply Z_mod_mult.
      1: rewrite MUM0; apply Z_mod_mult.
      1-2: lia.
      1: rewrite <- SZr; exact Hmsz.
      1-3: lia.
      1: assumption.
      1: assumption.
      1: assumption.
      1: assumption.
      1: assumption.
      clear SWR SWB.
      assert (EMS : msz = mu1 - p_mu k) by lia.
      replace (p_mu k + msz) with mu1 in * by lia.
      destruct PC8 as (ts1 & TS1).
      lz_here.
      eapply (pop_finish AL E AO ra gp F_ fc q lo c r k inited m _ H _ mu1 cnt mfa2 calloc cmapped (cmapped + msz)).
      1-7: assumption.
      1-4: lia.
      1: rewrite Q0; apply Z_mod_mult.
      1-5: first [assumption | lia].
      1-3: assumption.
      1: exact PC6.
      1: split; [exact PC1| exists wsc; split; [exact PA| split; [exact PL| exact PX]]].
      1: exists ws; split; [exact FAA| split; [exact LEN| exact FX]].
      1: exact PC9.
      1: rewrite Z2Nat.id by lia; reflexivity.
      1: exact PC10.
      1: rewrite Z2Nat.id by (apply Z.div_pos; lia); rewrite AU0, M0; clear; Z.div_mod_to_equations; lia.
      1: exact FCH.
      1: exact PC.
      1: exact PC7.
      1: exact TS1.
      1: exact MU.
      1: exact WM.
      1: unfold H_opt; replace (negb (mu1 =? p_mu k)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia); rewrite <- EMS; reflexivity.
      1: lia.
    - pose proof (M6 ltac:(lia)) as EMU. clear M6 M7.
      unfold t_populate. cbv zeta. rewrite <- Hmu1, <- Hcnt.
      replace (negb (mu1 =? p_mu k)) with false by (symmetry; apply negb_false_iff, Z.eqb_eq; lia).
      unfold t_opt, t_none.
      lazymatch goal with |- context [ebind (Ret (Ok tt)) ?f] => change (ebind (Ret (Ok tt)) f) with (f tt); cbv beta end.
      rewrite EMU in *. clear EMU.
      lz_here.
      eapply (pop_finish AL E AO ra gp F_ fc q lo c r k inited m _ H _ (p_mu k) cnt mfa2 calloc cmapped cmapped).
      1-2: assumption.
      1: eapply shvis_wmono; [exact SV| exact WM].
      1: eapply poison_env_frame; [exact PE| exact MU| exact WM| exact AIW].
      1: eapply thread_env_frame; [exact TE| exact MU| exact WM| exact TCW].
      1: unfold prim_env; exact PRE.
      1: assumption.
      1-4: lia.
      1: rewrite Q0; apply Z_mod_mult.
      1-5: first [assumption | lia].
      1-3: assumption.
      1: unfold ri_addr, RIB; exact RIC.
      1: split; [exact PC1| exists wsc; split; [exact PA| split; [exact PL| exact PX]]].
      1: exists ws; split; [exact FAA| split; [exact LEN| exact FX]].
      1: exact TL.
      1: rewrite Z2Nat.id by lia; reflexivity.
      1: exact TSH.
      1: rewrite Z2Nat.id by (apply Z.div_pos; lia); rewrite AU0, MUM0; clear; Z.div_mod_to_equations; lia.
      1: exact FCH.
      1: exact PC.
      1: exact STC.
      1: exact TS.
      1: exact MU.
      1: exact WM.
      1: unfold H_opt; replace (negb (p_mu k =? p_mu k)) with false by (symmetry; apply negb_false_iff, Z.eqb_eq; reflexivity); reflexivity.
      1: lia.
  Qed.
End POP2.

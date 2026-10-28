From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_SR LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_StateStmt LbB_Own LbB_HKit LbB_HStKit LbB_ContStmt LbB_ResvB.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoKit3 LbB_WoSt LbB_WoCut LbB_WoE0 LbB_WoVec LbB_WoT2 LbB_WoR6 LbB_WoG LbB_WoRv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_PmBase LbB_PiStmt LbB_PiInit LbB_WoBP LbB_PmExit LbB_DiagStmt LbB_WoDiagP LbB_WoS4 LbB_WoShK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_WoDiagC2 LbB_WoDiagH LbB_PmMagW LbB_PmCall.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac uhinst X Hv HHv :=
  lazymatch type of X with
  | forall _ : asr, _ => specialize (X Hv); uhinst X Hv HHv
  | asan_rt_hyps _ -> _ => specialize (X HHv)
  | _ => idtac
  end.

Section WUW.
  #[local] Set Default Proof Using "All".
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB : asan_rt_hyps H := rt_bp_base H HHb.

  Lemma wu_len : forall L, length (wo_sh L) = 476%nat.
  Proof.
    intros L. unfold wo_sh. rewrite length_app, repeat_length.
    assert (G : forall L L' k os, length (wo_sh_go L k os) = length (wo_sh_go L' k os)).
    { intros L1 L2 k os. revert k. induction os as [|[n r] os IH]; intros k; [reflexivity|].
      cbn [wo_sh_go]. rewrite !length_app, !repeat_length, IH. reflexivity. }
    rewrite (G L [] 0%nat WO_OBJS). vm_compute. reflexivity.
  Qed.

  Lemma wu_wtl : forall (e : went H) ff fp XS s LB LBs (m m' : mem) (c : parserC) (w : piw H),
    wpre H e -> bp_wl H e ff w -> winv H e ff fp XS s LB m -> pi_err H LINV_P5 w s LB LBs m c ->
    bp_slots H e ff m -> bp_shad ff [20; 21]%nat m ->
    munch [(sh ff + 382, sh ff + 412); (wS1 e - AINTRIN_STACK, wS1 e); (ff + 3056, ff + 3296)] m m' -> wmono asegs m m' ->
    winv H e ff fp XS s LB m' -> bp_slots H e ff m' -> bp_shad ff [19; 20; 21]%nat m' ->
    wtl H e ff fp XS s LB LBs [] m' (pc_state c)
    /\ lb_small LB + 700 <= RT_SMALL_MAX /\ Z.of_nat (length LB) + 3 <= RT_CNT_MAX /\ nlarge LB <= RT_LARGE_MAX
    /\ as_AL H s >= as_AL H (LbB_WoDefs.w_s e) - po_cost (LbB_WoDefs.w_n e) /\ 0 <= as_AL H s.
  Proof.
    intros e ff fp XS s LB LBs m m' c w HP WL HI PE SL SH MU WM HI' SL' SH'.
    pose proof PE as (RH & (SO1 & SO2) & OWN & PR & PSH & HC & HU & HW & HN & M1 & M2 & M3 & VS & BK & MI & ER & RA & AC & ST0 & LV & AL & MD).
    pose proof WL as (Wp & Wc & Ww & Wn & WLB & Ws0 & _).
    pose proof HP as (_ & _ & (Hn0 & Hn1) & _ & _ & B1 & B2 & B3 & _).
    assert (PC : po_cost (LbB_WoDefs.w_n e) <= as_AL H (LbB_WoDefs.w_s e)) by (unfold wpre in HP; tauto).
    pose proof LbB_PmMagW.hdr_geo as G. uhinst G H HB. specialize (G e ff fp XS s LB m HP HI).
    destruct G as (G64 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
    pose proof HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WF' & _).
    rewrite WLB in SO1. rewrite Wn in M1, M2, M3. rewrite Wp in PR, PSH. rewrite Ws0, Wn in AL.
    assert (LW := wu_len [19; 20; 21]%nat).
    assert (F8 : ff mod 8 = 0).
    { pose proof (Z.div_mod ff 64 ltac:(lia)) as D. rewrite G64, Z.add_0_r in D. rewrite D.
      replace (64 * (ff / 64)) with ((8 * (ff / 64)) * 8) by ring. apply Z.mod_mul. lia. }
    assert (B0 : 0 <= ff) by lia.
    unfold AINTRIN_STACK in MU.
    assert (INB : forall p n, In (p, n) (state_blocks (pc_state c)) -> In (p, n) (lbl LB)).
    { intros p0 n0 Hin. apply (Permutation_in _ (Permutation_sym SO2)) in Hin.
      apply (Permutation_in _ (Permutation_map (fun b => (snd (fst b), snd b)) (Permutation_sym SO1))).
      unfold lbl in Hin |- *. rewrite map_app. apply in_or_app. right. exact Hin. }
    assert (STm : state_repA LB m (ff + 3504) (pc_state c)).
    { destruct PR as [_ _ _ _ _ PRs _ _ _ _ _ _].
      split; [replace (ff + 3504) with (ff + 3456 + ST_OFF) by (unfold ST_OFF; lia); exact PRs |].
      exact (vstride_of_vsteps _ VS). }
    assert (SSm : state_sh m (pc_state c)) by (destruct PSH as (_ & _ & SSH); exact SSH).
    pose proof LbB_WoT2.wstate_mu_ff as WS. uhinst WS H HB.
    destruct (WS e ff fp XS s LB m m' _ (pc_state c) HP HI MU WM) as (STm' & SSm'); [| exact INB | exact STm | exact SSm |].
    { repeat (apply Forall_cons; [|]); [| | | apply Forall_nil].
      - right. unfold LbB_WoT2.wfw. cbn [fst snd]. right. right. lia.
      - left. unfold LbB_WoT2.wsw. cbn [fst snd]. left. lia.
      - right. unfold LbB_WoT2.wfw. cbn [fst snd]. left. lia. }
    split; [|split; [|split; [|split; [|split]]]].
    - unfold wtl. split; [exact HI'|]. split.
      + unfold wtc. pose proof SL' as (S1c & S2c & S3c).
        replace [C8 (wz (LbB_WoDefs.w_words e)); C8 (wz (LbB_WoDefs.w_n e)); C8 (wz ASHADOW_BASE); C8 (wz (ff + 2224)); C8 (wz (ff + 3376))]
          with ([C8 (wz (LbB_WoDefs.w_words e)); C8 (wz (LbB_WoDefs.w_n e))] ++ [C8 (wz ASHADOW_BASE)] ++ [C8 (wz (ff + 2224))] ++ [C8 (wz (ff + 3376))]) in S2c
          by reflexivity.
        apply rw_cells_app in S2c as [_ S2c]. apply rw_cells_app in S2c as [SA S2c]. apply rw_cells_app in S2c as [_ SB].
        cbn [cells_size csize Nat.add Z.of_nat] in SA, SB.
        split; [exact S1c|]. split.
        { replace (wS1 e + 40) with (wS1 e + 24 + 16) by lia. exact SA. }
        split.
        { replace (wS1 e + 56) with (wS1 e + 24 + 16 + 8 + 8) by lia. exact SB. }
        split.
        { destruct PR as [_ _ _ _ _ _ _ _ _ PRcf _ _]. rewrite HC, Wc in PRcf.
          assert (F0 : fldA m' (ff + 3408) 8 0).
          { eapply LbB_PmCall.fld_munch; [replace (ff + 3408) with (ff + 3376 + 32) by lia; exact PRcf | exact MU | | lia | lia].
            cbn [disjoint_from Z.of_nat]. unfold sh in *. lia. }
          apply LbB_WoDiagH.w_cells8_of_fld; [exact F0 |].
          eapply LbB_PmCall.wr_at_sub; [exact WF' | lia | unfold WO_FLAGP; lia | lia]. }
        { unfold bp_shad, u8arr in SH'. destruct SH' as (_ & WR). rewrite length_map, LW in WR. exact WR. }
      + split; [exact STm'|]. split; [exact SSm'|].
        split; [exact SO2|]. split; [exact BK|].
        split; [rewrite app_nil_r; exact SO1|].
        split; [exact (lb_own_wmono _ _ _ OWN WM)|].
        split.
        { pose proof (ah_nodup H HB _ _ _ RH) as ND. apply (Permutation_map blk_id) in SO1.
          apply (Permutation_NoDup SO1) in ND. rewrite map_app in ND. exact (NoDup_app_remove_l _ _ ND). }
        split.
        { apply (bp_shad_addr ff [19; 20; 21]%nat m' 3056 240 SH' B0 F8); try lia; try reflexivity.
          rewrite LW. apply Z.leb_le. reflexivity. }
        { apply (bp_shad_addr ff [19; 20; 21]%nat m' 3456 288 SH' B0 F8); try lia; try reflexivity.
          rewrite LW. apply Z.leb_le. reflexivity. }
    - rewrite (LbB_WoDiagC2.wlb_small_perm _ _ SO1), LbB_WoDiagC2.wlb_small_app. lia.
    - rewrite (Permutation_length SO1), length_app. lia.
    - rewrite (LbB_WoDiagC2.wnlarge_perm _ _ SO1), LbB_WoDiagC2.wnlarge_app. lia.
    - exact AL.
    - lia.
  Qed.
End WUW.

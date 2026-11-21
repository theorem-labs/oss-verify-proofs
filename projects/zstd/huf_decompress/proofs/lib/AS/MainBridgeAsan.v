(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (made from MainEntry.v's start-up chain, bridge and asan_side_ok, moved here so that amain_at's readers build without them, in the form of simple_decompress's AS/MainBridgeAsan.v: the main-entry states computed per CONFIG_RSEQ value by the start-up certificates (StartupRegenAsan), the recorded registers, visible ranges and ledger renumbered by the probe-read map FM, and the remade facts and the start state's argv cells justified against those states (JUST, main_justified); the bridge proves argv_cells, the stack window, the remade facts' bounds (the image-range fact, the stack-window fact, the shadow bands' clearance) and amodel's new fields (the ledger's byte bound, the computed total, the mappings' clearance from the ledger); the bridge and the start-up chain at any allocation limit LIM (asan_main_bootL, used at LIMIT here and at LIMITH by MainEntryH.v) over the launch's ProcInput, kernel build, exec file name and SIGPIPE disposition, with AsanInit.argH0's ranges read at an address (argH_of_range); asan_side_ok over the 20-field ProcInput, reading the recorded kernel, the channel reader and the SIGPIPE declaration from valid_input_either, the walk lifted to the run's segments; ported by content from zstd_frame_info's file of the same role, with this binary's addresses and names; FM is mapf bpM (MainEntry.bpM)). *)
(* The main entry's bridge and the ASan build's side_ok (LPS 727298f3). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupHS2Asan AsanBoot
  AsanCertDefs PlanRegen StartupRegenAsan AsanStartupCert AsanStartupCertB AsanStartupCertC AsanStartupCertD AsanStartupCert2
  MainRenum RegsEqv0 SrzEqv MainExport MainFactsAsan MainEntry RomBase RomStable.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore TopLevelGen.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* LPS 727298f3: the start-up run numbers its fresh variables differently (the launch variable
   [V_GID], the longer auxv), so the hand-off states at main ([stS1 r], [stS2 r], computed in the
   build by StartupRegenAsan) name the main entry's variables at other numbers than the recorded
   facts of MainFactsAsan.  [FM] is that renumbering, the startup2 map read from a probe run
   (StartupRegenAsan.bp2) with the breakpoint for the variables only the facts name (MainEntry.bpM);
   the facts keep their recorded numbering and are stated about
   [fun n => V' (FM n)], [V'] the run's own variables (MainRenum; the method of
   msgpack-c/unpack_pack_fuzzer's AS/MainEntry.v). *)
Definition FM : nat -> nat := mapf bpM.
Lemma FM_low : forall n, (n < 13)%nat -> FM n = n.
Proof.
  intros n Hn. unfold FM, mapf, bpM, bp2. cbn [fold_left fst snd].
  repeat (rewrite (proj2 (Nat.leb_gt _ _)) by lia). reflexivity.
Qed.

(* the recorded main-entry registers, renumbered by [FM] (the computed states hold exactly these:
   [main_justified] checks it) *)
Definition AREGS : list expr := Eval vm_compute in map (esh FM) (s_regs (a_ss HS_asan2_1)).

(* what the bridge reads off a computed main-entry state [hs] (hand-off 1 when [w], 2 otherwise) at
   CONFIG_RSEQ value [r]: its registers, pc, descriptor table and break are the recorded ones
   renumbered; the facts remade by MainRegen's rule ([amf r w], [apf r w]), the argv pointer cells as the
   start state states them ([aargv r]), the visible ranges and the ledger, renumbered, are justified by it;
   the bounds the bridge reads off the remade facts hold of them *)
Definition JUST (r : Z) (w : bool) (hs : acs) : Prop :=
  s_regs (a_ss hs) = AREGS /\ pc hs = AMAIN /\ a_fd hs = FdStd /\ a_brk hs = EVar (FM V_VMBRK)
  /\ forallb (mjustify (kn hs) (var_ranges (kn hs)) AIMG_LO AIMG_HI) (map (msh FM) (amf r w ++ aargv r)) = true
  /\ forallb (pjustify (kn hs) (var_ranges (kn hs))) (map (pfsh FM) (apf r w)) = true
  /\ (vis_match (var_ranges (kn hs)) (a_vis hs) (map (bnsh FM) asan_vis_app) = true
      /\ vis_match (var_ranges (kn hs)) (a_ghost hs) (map (bnsh FM) asan_ghost) = true)
  /\ ledger_xmatch (var_ranges (kn hs)) (a_maps hs) (map (lsh FM) asan_ledger) = true
  /\ ((a_totsz hs <=? ATOTSZ) && (a_eager hs <=? asan_eager) && (a_abytes hs <=? asan_abytes))%bool = true
  /\ existsb (fun f => match f with MImg lo' hi' => (lo' <=? 0x10000) && (0xaf000 <=? hi') | _ => false end) (amf r w) = true
  /\ existsb (fun f => match f with MWr a' n' => zexp_eqb a' STKA && (n' =? 6144513) | _ => false end) (amf r w) = true
  /\ forallb (shad_clear (pvranges (apf r w)) (apf r w)) asan_vis_app = true
  /\ forallb (shad_clear (pvranges (apf r w)) (apf r w)) asan_ghost = true.

(* the bridge's totals in amodel's terms: the same sums under MainExport's names *)
Lemma ivs_sum_sizes : forall l, ivs_sum l = sum_sizes l.
Proof. induction l as [|iv l IH]; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma ivz_A_bytes : forall A, ivz_bytes A = A_bytes A.
Proof. induction A as [|iv A IH]; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.

Section Bridge.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable hw : word.
  Variable abt : bool.
  Variable urnd : InputStream.   (* [comment removed for export] *)
  (* the kernel build, the exec file name and the SIGPIPE disposition: the launch's own (LPS 727298f3) *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdef : bool.
  #[local] Notation INP := (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb execfn sdef).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  Definition en0 : ExecEntry := mkEntry sp brk0 mbase rdraw.
  Definition inp0 : ProcInput := INP.

  #[local] Notation APC := Asan.M.init_pc.
  #[local] Notation SINV := (SINV0 APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb execfn sdef).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).
  Let RZr : 0 <= RZ <= 1 := rseq_z_range (kb_rseq kb).

  (* AsanInit's lemmas take the launch through the section's hypotheses ([eassumption], which also
     fixes their variables); the atable, segments, headers, entry point and image facts their
     proofs carry, the goal does not fix: [CL] gives this build's *)
  Local Ltac CL := first [eassumption | exact ASAN | exact APH | exact ASEGS | exact asan_img_facts | exact APC | reflexivity].
  Local Ltac USE c := unshelve (eapply c; try eassumption); CL.

  (* transparent, so that no theorem below is generalized over them *)
  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a Ha. USE argH0_high. Defined.
  (* the start-up chain's own second bound, should its theorems take it *)
  Let AH2 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a HS Ha. USE argH0_high2. Defined.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).

  (* [comment removed for export] *)
  Lemma sinv_usp : forall E M, SINV E M -> uE E e_sp0 = usp.
  Proof.
    intros E M [HE _].
    transitivity (uE E0a e_sp0); [| USE AsanInit.u_e_sp0].
    unfold e_sp0, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot].
    rewrite !HE by (unfold NX0, V_S1, V_S2, V_SP; lia). reflexivity.
  Qed.

  Lemma u_launch :
    uE E0a (EVar V_S1) = usp / 32768 /\ uE E0a (EVar V_S2) = (usp mod 4096) / 16
    /\ uE E0a (EVar V_ARGC) = argc /\ uE E0a (EVar V_ENVC) = envc
    /\ uE E0a (EVar V_L0) = Z.of_nat (length (nth 0 argv []))
    /\ uE E0a (EVar V_W) = Wpad en0 inp0 /\ uE E0a (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0a (EVar V_SP) = (usp mod 32768) / 4096
    /\ uE E0a (EVar V_L1) = Z.of_nat (length (nth 1 argv []))
    /\ uE E0a (EVar V_UID) = bv_unsigned uid /\ uE E0a (EVar V_HW) = bv_unsigned hw
    /\ uE E0a (EVar V_G) = Z.of_nat (block_items argv envp mod 2).
  Proof.
    assert (U : uE E0a (EVar V_S1) = usp / 32768 /\ uE E0a (EVar V_S2) = (usp mod 4096) / 16
    /\ uE E0a (EVar V_ARGC) = argc /\ uE E0a (EVar V_ENVC) = envc
    /\ uE E0a (EVar V_L0) = Z.of_nat (length (nth 0 argv []))
    /\ uE E0a (EVar V_W) = Wpad en0 inp0 /\ uE E0a (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0a (EVar V_G) = Z.of_nat (block_items argv envp mod 2)) by (USE AsanInit.uE0).
    destruct U as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8).
    assert (U9 : uE E0a (EVar V_SP) = (usp mod 32768) / 4096) by (USE AsanInit.uE0_sp).
    assert (U10 : uE E0a (EVar V_L1) = Z.of_nat (length (nth 1 argv []))) by (USE AsanInit.uE0_L1).
    repeat split; try assumption; reflexivity.
  Qed.

  (* [hidden_arg]'s two ranges are [AsanInit.argH0]'s, read at an address (simple_decompress's and
     msgpack-c's AsanInit.v state this as [argH0_of_range]; this unit's AsanInit.v does not) *)
  Lemma argH_of_range : forall E (a : Z), hidden_arg en0 inp0 a -> argH E (wa a) = true.
  Proof.
    intros E a Ha.
    unfold hidden_arg, STR0_of, Wpad, en0, inp0, AsanInit.inp in Ha.
    cbn [en_sp en_draw in_argv in_envp in_kernel in_execfn recorded_kernel kb_rseq] in Ha.
    pose proof Hva as (LA & _). pose proof Hve as (LE & _).
    pose proof Hsp as (S1 & S2 & _). unfold sp_window_lo, sp_window_hi in S1, S2.
    pose proof (u64_range (ed_top rdraw)) as RT.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; lia).
    unfold argH0. cbv beta zeta. rewrite wa_unsigned by exact Ha64.
    apply orb_true_intro. destruct Ha as [Ha|Ha]; [left|right]; apply andb_true_intro; split;
      first [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  (* the two computed main-entry states, at the run's own CONFIG_RSEQ value; [main_justified] below
     proves the hypothesis by computation at both values *)
  Hypothesis HJ : forall w : bool, JUST RZ w (if w then stS1 RZ else stS2 RZ).

  (* [comment removed for export] *)
  Section Lim.
  Variable LIM : Z.

  (* [comment removed for export] *)
  Theorem amain_bridge_w : forall (w : bool) (hs : acs), JUST RZ w hs ->
    forall E R FULL mo,
    cs_ok ASEGS ASAN LIM SINV argH fs E hs R FULL mo ->
    exists ms, cfg_eqv (cfg_of ASEGS R (pc hs) FULL mo) (mkCfg ms mo) /\ amain_atL LIM en0 inp0 ms mo.
  Proof.
    intros w hs (Hregs & Hpc & Hfd & Hbrk0 & MJ & PJ & VJ & LJ & CONSTS & IMGc & STKc & CLRv & CLRg) E R FULL mo HC. rewrite Hpc.
    set (V := Vf FM (uev E)).
    assert (HVl : forall n, (n < 13)%nat -> V n = uev E n).
    { intros n Hn. unfold V, Vf. rewrite (FM_low n Hn). reflexivity. }
    (* [comment removed for export] *)
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HSINV. pose proof HSINV as [Hev Hhid].
    pose proof (sinv_usp E FULL HSINV) as USP.
    pose proof u_launch as (U0 & U6 & U1 & U2 & U3 & U4 & U5 & U10 & U7 & U8 & U9 & U11).
    unfold APS.uE in U0, U6, U1, U2, U3, U4, U5, U7, U8, U9, U10, U11. cbn [edenot] in U0, U6, U1, U2, U3, U4, U5, U7, U8, U9, U10, U11.
    assert (PIN : forall n z, (n < 13)%nat -> bv_unsigned (ev E0a n) = z -> V n = z).
    { intros n z Hn Hz. rewrite (HVl n Hn). unfold uev. rewrite (Hev n) by (unfold NX0; lia). exact Hz. }
    pose proof (PIN 0%nat _ ltac:(lia) U0) as P0. pose proof (PIN 6%nat _ ltac:(lia) U6) as P6.
    pose proof (PIN 1%nat _ ltac:(lia) U1) as P1. pose proof (PIN 2%nat _ ltac:(lia) U2) as P2.
    pose proof (PIN 3%nat _ ltac:(lia) U3) as P3. pose proof (PIN 4%nat _ ltac:(lia) U4) as P4.
    pose proof (PIN 5%nat _ ltac:(lia) U5) as P5. pose proof (PIN 7%nat _ ltac:(lia) U7) as P7.
    pose proof (PIN 8%nat _ ltac:(lia) U8) as P8. pose proof (PIN 9%nat _ ltac:(lia) U9) as P9.
    pose proof (PIN 10%nat _ ltac:(lia) U10) as P10. pose proof (PIN 11%nat _ ltac:(lia) U11) as P11.
    clear U0 U6 U1 U2 U3 U4 U5 U7 U8 U9 U10 U11.
    assert (Hal : bv_unsigned sp mod 16 = 0) by (pose proof Hsp as (_ & _ & H); exact H).
    assert (LO : 0x7fff80000000 <= usp) by (pose proof Hsp as (H & _); exact H).
    assert (HI : usp + 192 <= 2 ^ 47) by (USE AsanInit.usp_hi).
    assert (PSP : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned sp).
    { rewrite P0, P6, P10. fold usp. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (VR : forall n, 0 <= V n < 2 ^ 64) by (intros n; unfold V, Vf; apply uev_range).
    (* [comment removed for export] *)
    pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as TOP. rewrite USP in TOP.
    assert (ATOP : atop mo = bv_unsigned sp - 8388608) by (unfold atop; rewrite TOP; reflexivity).
    eexists. split; cycle 1.
    { (* [comment removed for export] *)
      exists w, V, FULL. split; [reflexivity|].
      split; [exact VR|].
      split; [repeat split; assumption|].
      (* [comment removed for export] *)
      assert (HIDrom : forall a, APS.hid ASAN argH E hs mo a = true -> seg_rom asegs a = None).
      { intros a Ha. apply (APS.seg_rom_off_hull ASEGS ASAN asan_in_hull).
        unfold APS.hid in Ha. apply orb_prop in Ha as [Ha|Ha].
        - pose proof (AH E a Ha) as Hc. unfold APS.in_hull. cbn [img_lo img_hi ASAN]. unfold CEIL in Hc.
          apply andb_false_iff. right. apply Z.ltb_ge. lia.
        - apply negb_true_iff in Ha. unfold APS.vis in Ha. apply orb_false_iff in Ha as [Ha _]. apply orb_false_iff in Ha as [Ha _]. exact Ha. }
      assert (HULLvis : forall a, AIMG_LO <= bv_unsigned a < AIMG_HI -> APS.hid ASAN argH E hs mo a = false).
      { intros a Ha. apply (APS.hid_hull ASAN asan_hull_ok argH AH). unfold APS.in_hull. cbn [img_lo img_hi ASAN]. unfold AIMG_LO, AIMG_HI in Ha.
        apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
      pose proof (export_sound asegs E (APS.hid ASAN argH E hs mo) FULL (kn hs) AIMG_LO AIMG_HI
                    (co_know _ _ _ _ _ _ _ _ _ _ _ HC) HIDrom HULLvis _ _ MJ PJ) as [HMFs HPFs].
      pose proof (Forall_mfact_ok_msh FM asegs (uev E) FULL _ HMFs) as HMF0. fold V in HMF0.
      apply Forall_app in HMF0 as [HMF HAV].
      pose proof (Forall_pfact_ok_pfsh FM (uev E) _ HPFs) as HPF. fold V in HPF.
      split; [exact HMF|]. split; [exact HPF|].
      (* [comment removed for export] *)
      split.
      { intros a b Hab. rewrite a_ro_addr.
        destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); [|reflexivity].
        destruct (Z.ltb_spec0 (bv_unsigned a) 0xaf000); [|reflexivity].
        exfalso. pose proof (mimg_cover asegs V FULL (amf RZ w) 0x10000 0xaf000 HMF IMGc (bv_unsigned a) ltac:(lia)) as X.
        unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. congruence. }
      (* the zero-mapped stack window: the start-up's [KWr (SA e_sp0 (-6144513)) (ELit 6144513)] *)
      split.
      { pose proof (mwr_find asegs V FULL (amf RZ w) STKA 6144513 HMF STKc) as W.
        cbn [zv STKA] in W.
        replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) + -6144513) with (bv_unsigned sp - 6144513) in W by lia.
        cbn [en0 en_sp].
        apply wr_at_stk; [replace (bv_unsigned sp - (bv_unsigned sp - 6144513)) with 6144513 by lia; exact W|].
        intros a Ha. apply ref_find_segment_none; [lia|]. lia. }
      (* [comment removed for export] *)
      split.
      { intros a Ha. apply Hhid. exact (argH_of_range E a Ha). }
      (* the argv pointer cells: the start state's own claims ([aargv]), justified against the computed
         state above, read in the launch's terms (AsanInit: the block head, the pad and the strings fill
         the stack block up to the stack VMA's end) *)
      split.
      { assert (CH : Z.of_nat (block_head_size (kb_rseq kb) argv envp)
                     = 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 472 + 32 * RZ
                       + 8 * Z.of_nat (block_items argv envp mod 2))
          by (USE AsanInit.chead_eq).
        assert (S0 : bv_unsigned sp + Z.of_nat (block_head_size (kb_rseq kb) argv envp)
                     + Z.of_nat (block_pad_len (kb_rseq kb) sp (ed_top rdraw) argv envp execfn)
                     + Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned (ed_top rdraw))
          by (USE AsanInit.str0_hi).
        assert (P4' : V 4%nat = Z.of_nat (block_pad_len (kb_rseq kb) sp (ed_top rdraw) argv envp execfn))
          by (rewrite P4; reflexivity).
        assert (P1' : V 1%nat = Z.of_nat (length argv)) by (rewrite P1; reflexivity).
        assert (P2' : V 2%nat = Z.of_nat (length envp)) by (rewrite P2; reflexivity).
        rewrite Forall_forall in HAV.
        assert (A0 : mfact_ok asegs V FULL (MRo (mkaddr (zof0 e_sp0) 8) 8 (zof0 (e_str0 RZ))))
          by (apply HAV; unfold aargv; cbn [In]; left; reflexivity).
        assert (A1 : mfact_ok asegs V FULL (MRo (mkaddr (zof0 e_sp0) 16) 8 (zof0 (e_argv1w RZ))))
          by (apply HAV; unfold aargv; cbn [In]; right; left; reflexivity).
        cbn [mfact_ok] in A0, A1. rewrite !zv_mkaddr, zv_sp0 in A0, A1. rewrite (zv_str0 V RZ RZr) in A0.
        unfold argv_cells, STR0_of, Wpad. cbv zeta.
        change (en_sp en0) with sp. change (en_draw en0) with rdraw.
        change (in_argv inp0) with argv. change (in_envp inp0) with envp. change (in_execfn inp0) with execfn.
        change (kb_rseq (in_kernel inp0)) with (kb_rseq kb).
        split; [lia|]. split.
        - replace (32768 * V 0%nat + 16 * V 6%nat + 4096 * V 10%nat + 8) with (bv_unsigned sp + 8) in A0 by lia.
          replace (32768 * V 0%nat + 16 * V 6%nat + 4096 * V 10%nat + 8 * V 1%nat + 8 * V 2%nat + 8 * V 11%nat + V 4%nat + 472 + 32 * RZ)
            with (bv_unsigned (ed_top rdraw) - 8 - Z.of_nat (launch_string_bytes argv envp execfn)) in A0 by lia.
          exact A0.
        - intros H2. pose proof (VR 1%nat) as VR1. rewrite (zv_argv1 V RZ RZr ltac:(lia)) in A1.
          replace (32768 * V 0%nat + 16 * V 6%nat + 4096 * V 10%nat + 16) with (bv_unsigned sp + 16) in A1 by lia.
          replace (32768 * V 0%nat + 16 * V 6%nat + 4096 * V 10%nat + 8 * V 1%nat + 8 * V 2%nat + 8 * V 11%nat + V 4%nat + 472 + 32 * RZ + V 3%nat + 1)
            with (bv_unsigned (ed_top rdraw) - 8 - Z.of_nat (launch_string_bytes argv envp execfn) + Z.of_nat (length (nth 0 argv [])) + 1) in A1
            by (rewrite P3; lia).
          exact A1. }
      (* [comment removed for export] *)
      pose proof (var_ranges_sound ASEGS E _ (kn hs) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as HVR.
      destruct VJ as [VJa VJg].
      pose proof (vis_match_sound E _ _ _ HVR VJa) as HVISa0. pose proof (vis_match_sound E _ _ _ HVR VJg) as HVISg0.
      pose proof (Forall2_map_bnsh FM (uev E)
                    (fun p x y => bv_unsigned (edenot E (fst p)) = x /\ bv_unsigned (edenot E (snd p)) = y /\ 0 <= y) _ _ HVISa0) as HVISa.
      pose proof (Forall2_map_bnsh FM (uev E)
                    (fun p x y => bv_unsigned (edenot E (fst p)) = x /\ bv_unsigned (edenot E (snd p)) = y /\ 0 <= y) _ _ HVISg0) as HVISg.
      cbv beta in HVISa, HVISg. fold V in HVISa, HVISg.
      pose proof (ledger_den_lsh FM (uev E) _ _ (ledger_den_sound E _ HVR _ _ _ LJ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC))) as HLD.
      pose proof (ledger_kinds_sound E _ HVR _ _ mo LJ (co_none _ _ _ _ _ _ _ _ _ _ _ HC) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC)) as HKD0.
      assert (HKD : Forall (lentry_kind_ok V mo) asan_ledger).
      { rewrite Forall_map in HKD0. eapply Forall_impl; [|exact HKD0]. intros e He. exact (lentry_kind_ok_lsh FM (uev E) mo e He). }
      fold V in HLD.
      (* [comment removed for export] *)
      split.
      { pose proof (pvranges_sound V (apf RZ w) VR HPF) as HVRp.
        assert (Elow : In (LMap (ZLit 0x7fff7000) 0x10000000 KRWLAZY) asan_ledger) by (cbn; tauto).
        assert (Ehigh : In (LMap (ZLit 0x2008fff7000) 0xdfff0001000 KRWLAZY) asan_ledger) by (cbn; tauto).
        intros a Hsh Hnv.
        assert (Ha : 0 <= a < 2 ^ 64) by (unfold ashadow in Hsh; lia).
        assert (Ua : bv_unsigned (wa a) = a) by (apply wa_unsigned; exact Ha).
        (* [comment removed for export] *)
        assert (KL : ~ MainExport.in_ivs a (vm_noaccess (m_vmmaps mo)) /\ page_in_ranges (page_base (wa a)) (m_vm_lazy mo) = true
                     /\ APS.in_ivs a (vm_maps (m_vmmaps mo)) = true).
        { destruct Hsh as [Hsh|Hsh].
          - pose proof (proj1 (Forall_forall _ _) HKD _ Elow) as K. cbn [lentry_kind_ok zv] in K.
            destruct (K (wa a) ltac:(rewrite Ua; lia)) as [K1 K2]. rewrite Ua in K1. split; [exact K1|]. split; [exact K2|].
            apply (proj2 (in_ivs_APS _ _)). exists (wa 0x7fff7000, wa 0x10000000). split; [exact (ledger_den_In V _ _ _ _ _ HLD Elow)|].
            cbn [fst snd]. rewrite !wa_unsigned by lia. lia.
          - pose proof (proj1 (Forall_forall _ _) HKD _ Ehigh) as K. cbn [lentry_kind_ok zv] in K.
            destruct (K (wa a) ltac:(rewrite Ua; lia)) as [K1 K2]. rewrite Ua in K1. split; [exact K1|]. split; [exact K2|].
            apply (proj2 (in_ivs_APS _ _)). exists (wa 0x2008fff7000, wa 0xdfff0001000). split; [exact (ledger_den_In V _ _ _ _ _ HLD Ehigh)|].
            cbn [fst snd]. rewrite !wa_unsigned by lia. lia. }
        destruct KL as (Kna & Klz & Kmap).
        assert (HSS : exists s, In s ASHADOWS /\ fst s <= a < snd s).
        { destruct Hsh as [Hsh|Hsh]; [exists (0x7fff7000, 0x8fff7000) | exists (0x2008fff7000, 0x10007fff8000)]; cbn; split; auto; lia. }
        apply (co_zero _ _ _ _ _ _ _ _ _ _ _ HC (wa a)); rewrite ?Ua.
        - (* [comment removed for export] *)
          unfold APS.hid. apply orb_true_intro. right. apply negb_true_iff. unfold APS.vis. rewrite Ua.
          rewrite Klz. cbn [negb].
          replace (APS.in_hull ASAN a) with false.
          2:{ symmetry. unfold APS.in_hull. cbn [img_lo img_hi ASAN]. apply andb_false_iff. right. apply Z.ltb_ge. unfold ashadow in Hsh. lia. }
          replace (atop mo <=? a) with false by (symmetry; apply Z.leb_gt; rewrite ATOP; unfold ashadow in Hsh; lia).
          cbn [orb]. replace (APS.in_allow ASAN E hs a) with false; [destruct (APS.in_ivs _ _ && _)%bool; reflexivity|].
          symmetry. unfold APS.in_allow. apply orb_false_intro.
          + (* [comment removed for export] *)
            unfold APS.in_vis. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3). unfold APS.uE in X1, X2. rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
            apply (shad_clear_sound V _ (apf RZ w) bn a HVRp HPF (proj1 (forallb_forall _ _) CLRv bn Hbn) HSS). lia.
          + (* [comment removed for export] *)
            unfold APS.in_sh. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.sh_lo, APS.sh_hi, APS.uE in X1, X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
            apply Hnv. exists bn. split; [exact Hbn|]. change (shadow_off ASAN) with ASHOFF in X1, X2. lia.
        - exact Kmap.
        - apply Bool.not_true_iff_false. intros X. apply Kna. apply (proj1 (in_ivs_APS _ _)). exact X.
        - exact Klz.
        - (* [comment removed for export] *)
          unfold APS.in_ghost. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
          apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.uE in X1, X2.
          destruct (Forall2_In_l _ _ _ _ HVISg Hp) as (bn & Hbn & E1 & E2 & E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
          apply (shad_clear_sound V _ (apf RZ w) bn a HVRp HPF (proj1 (forallb_forall _ _) CLRg bn Hbn) HSS). lia. }
      (* [comment removed for export] *)
      pose proof (allowA_allow_of ASAN E _ _ (Forall2_app HVISa0 HVISg0)) as HAL. change (shadow_off ASAN) with ASHOFF in HAL.
      change (flat_map (allow1 ASAN E) (a_vis hs ++ a_ghost hs)) with (allowA ASAN E hs) in HAL.
      rewrite <- map_app, (allow_of_bnsh FM) in HAL. fold V in HAL. change (asan_vis_app ++ asan_ghost) with asan_vis in HAL.
      apply andb_prop in CONSTS as [CONSTS Ca]. apply andb_prop in CONSTS as [Ct Ce]. apply Z.leb_le in Ct, Ce, Ca.
      assert (USPW : vm_init_sp (m_vmmaps mo) = sp) by (apply bv_eq; exact TOP).
      destruct HC. cbn [inp0 AsanInit.inp in_fs in_image_fs in_tmp en0 en_sp]. rewrite Hfd in co_fds0. rewrite Hbrk0 in co_brk0.
      constructor.
      + exact co_halt0.
      + exact co_reader0.
      + exact co_fds0.
      + exact co_fs0.
      + exact co_res0.
      + exact co_limit0.
      + rewrite co_brk0. cbn [edenot]. symmetry. apply Z_to_bv_bv_unsigned.
      + rewrite co_brk0 in co_sbrk0. cbn [edenot] in co_sbrk0. exact co_sbrk0.
      + exact USPW.
      + split; [exact LO|]. split; [lia| exact Hal].
      + exact HLD.
      + exact HKD.
      + apply seps_ivs_sep. exact co_seps0.
      + eapply Forall_impl; [|exact co_bounds0]. cbv beta. intros iv (B1 & B2 & B3 & B4 & B5 & B6).
        unfold hull_clear in B5. cbn [img_lo img_hi ASAN] in B5. rewrite ATOP in B6. unfold AIMG_LO, AIMG_HI. repeat split; assumption.
      + eapply Forall_impl; [|exact co_lazyb0]. cbv beta. intros iv (B5 & B6).
        unfold hull_clear in B5. cbn [img_lo img_hi ASAN] in B5. rewrite ATOP in B6. unfold AIMG_LO, AIMG_HI. split; assumption.
      + destruct co_wf0 as (_ & Wn & _). apply Forall_forall. intros iv Hiv. exact (Wn iv Hiv).
      + intros z Hz. apply (proj1 (in_ivs_APS _ _)). apply co_nasub0. apply (proj2 (in_ivs_APS _ _)). exact Hz.
      + exact co_napos0.
      + rewrite ivs_sum_sizes. lia.
      + change (nonlazy_bytes mo) with (eager_used mo). lia.
      + rewrite <- HAL, ivz_A_bytes. lia.
      + rewrite <- HAL. pose proof (minv_budget _ _ co_minv0) as B. rewrite co_limit0 in B. exact B.
      + rewrite <- HAL. exact (APS.A_wf_allowA ASAN HS_asan2 XN0 XE0 XB0 NX0 E hs).
      + exact (minv_nodup _ _ co_minv0).
      + intros p Hp. split; [exact (minv_aligned _ _ co_minv0 p Hp)|]. split; [exact (minv_lazy _ _ co_minv0 p Hp)|].
        rewrite <- HAL. apply page_allowedb_aallowed. exact (minv_allowed _ _ co_minv0 p Hp).
      + exact co_mres0. }
    - (* [comment removed for export] *)
      unfold cfg_of. split; [|reflexivity]. cbn [cfg_ms].
      split; [| split; [apply regs_eqv_refl| repeat split; reflexivity]].
      cbn [ms_regs AS.PropExec.mkst MS].
      intros r Hr. destruct (OSSVerify.Proofs.zstd.huf_decompress.lib.Lib.RegsEquiv.reg_of_nat r) as (n & -> & Hn).
      pose proof (is_x0_of_nat n Hn Hr) as Hn1.
      rewrite (regs_ok_nth E _ R (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) n Hn1). rewrite reg_get_mkR by exact Hn1. rewrite Hregs.
      destruct n as [|n]; [cbv in Hr; discriminate|].
      cbn [en0 inp0 AsanInit.inp en_sp in_argv in_envp].
      do 31 (destruct n as [|n];
        [ cbn [nth AREGS];
          first [ reflexivity
                | apply Z_to_bv_bv_unsigned
                | symmetry; apply Z_to_bv_bv_unsigned
                | erewrite <- (zexp_of_sound E) by reflexivity; cbn [zv];
                  rewrite <- ?(HVl 0%nat ltac:(lia)), <- ?(HVl 1%nat ltac:(lia)), <- ?(HVl 6%nat ltac:(lia)), <- ?(HVl 10%nat ltac:(lia));
                  unfold AMAIN, ARA, AGP, ATP, usp, argc in *; f_equal; lia ]
        |]). lia.
  Qed.

  Theorem amain_bridge_HM : forall (w : bool) E R FULL mo,
    cs_ok ASEGS ASAN LIM SINV argH fs E (if w then stS1 RZ else stS2 RZ) R FULL mo ->
    exists ms, cfg_eqv (cfg_of ASEGS R (pc (if w then stS1 RZ else stS2 RZ)) FULL mo) (mkCfg ms mo) /\ amain_atL LIM en0 inp0 ms mo.
  Proof.
    intros w E R FULL mo HC.
    exact (amain_bridge_w w _ (HJ w) E R FULL mo HC).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HLIM : source_alloc_limit <= LIM.
  (* LPS 727298f3: the five start-up certificates at the run's CONFIG_RSEQ flag, against
     StartupRegenAsan's renumbered plans and computed hand-off tables, counters and shapes
     (AsanBoot's own premises) *)
  #[local] Notation CERT_A_T := (check ASEGS IT0 ASAN NX0 LIM RZ (XNS ASEGS ASAN NX0 LIM) XE0 XB0 (hsA RZ) KC0 BFUEL FUEL None (asan_init RZ) (planA RZ) = COk (shapeA RZ)).
  #[local] Notation CERT_B_T := (check ASEGS ITB ASAN (nxB RZ) LIM RZ (XNS ASEGS ASAN (nxB RZ) LIM) XE0 XB0 (hsB RZ) KC0 BFUEL FUEL None (stA RZ) (planB RZ) = COk (shapeB RZ)).
  #[local] Notation CERT_C_T := (check ASEGS ITC ASAN (nxC RZ) LIM RZ (XNS ASEGS ASAN (nxC RZ) LIM) XE0 XB0 (hsC RZ) KC0 BFUEL FUEL None (stB RZ) (planC RZ) = COk (shapeC RZ)).
  #[local] Notation CERT_D_T := (check ASEGS ITD ASAN (nxD RZ) LIM RZ (XNS ASEGS ASAN (nxD RZ) LIM) XE0 XB0 (hsD RZ) KC0 BFUEL FUEL None (stC RZ) (planD RZ) = COk (shapeD RZ)).
  #[local] Notation CERT_2_T := (check ASEGS IT2 ASAN (nx2 RZ) LIM RZ (XNS ASEGS ASAN (nx2 RZ) LIM) XE0 XB0 (hs2 RZ) KC0 BFUEL FUEL None (stD RZ) (plan2 RZ) = COk (shape2 RZ)).
  (* [comment removed for export] *)
  Variable TL : TSet.
  Hypothesis TL_nil : TL [].
  Hypothesis MAINL : forall ms mo, amain_atL LIM en0 inp0 ms mo -> srealizes asegs (mkCfg ms mo) TL.

  (* the start-up chain's last hole: the two computed main-entry states *)
  Lemma asan_main_holes : holes_stmt ASEGS ASAN LIM (hs2 RZ) SINV argH (fun _ _ _ => TL) fs.
  Proof.
    intros h ch Hh E R FULL mo HC.
    destruct (hs2_two RZ h ch Hh) as [[-> ->]|[-> ->]].
    - destruct (amain_bridge_HM true E R FULL mo HC) as (ms & Heqv & Hat).
      apply (srealizes_eqv ASEGS (mkCfg ms mo) TL (MAINL ms mo Hat)). apply cfg_eqv_sym. exact Heqv.
    - destruct (amain_bridge_HM false E R FULL mo HC) as (ms & Heqv & Hat).
      apply (srealizes_eqv ASEGS (mkCfg ms mo) TL (MAINL ms mo Hat)). apply cfg_eqv_sym. exact Heqv.
  Qed.

  (* AsanBoot's premises are dispatched by their form, so that their order (and whether the chain's
     local bounds AH, AH2 are among them) does not matter; a certificate is matched by its itab and
     never tried against another *)
  Theorem asan_main_bootL : CERT_A_T -> CERT_B_T -> CERT_C_T -> CERT_D_T -> CERT_2_T ->
    srealizes asegs (init_config asegs Asan.M.init_pc a_phdrs sp brk0 mbase rdraw LIM inp0) TL.
  Proof.
    intros CERT_A CERT_B CERT_C CERT_D CERT_2.
    change asegs with ASEGS. change a_phdrs with APH.
    eapply asan_boot with (sp := sp) (rdraw := rdraw) (brk0 := brk0) (mbase := mbase) (argv := argv) (envp := envp)
      (fs := fs) (stdin := stdin) (uid := uid) (gid := gid) (hw := hw) (groups := groups) (net := net) (nof := nof)
      (sigm := sigm) (abt := abt) (urnd := urnd) (kb := kb) (execfn := execfn) (sdef := sdef) (LIM := LIM)
      (H := fun _ _ => TL).
    all: lazymatch goal with
         | |- check _ IT0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => exact CERT_A
         | |- check _ ITB _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => exact CERT_B
         | |- check _ ITC _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => exact CERT_C
         | |- check _ ITD _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => exact CERT_D
         | |- check _ IT2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => exact CERT_2
         | |- holes_stmt _ _ _ _ _ _ _ _ => exact asan_main_holes
         | |- _ => first [ intros; exact TL_nil | exact AH | exact AH2 | eassumption | intros; reflexivity ]
         end.
  Qed.
  End Lim.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAINA : forall ms mo, amain_at en0 inp0 ms mo -> srealizes asegs (mkCfg ms mo) T.

  Theorem asan_main_boot :
    srealizes asegs (init_config asegs Asan.M.init_pc a_phdrs sp brk0 mbase rdraw target_alloc_limit inp0) T.
  Proof.   (* [comment removed for export] *)
    exact (asan_main_bootL AsanInit.LIMIT AsanInit.LIMIT_ge T T_nil (fun ms mo H => MAINA ms mo (amain_atL_amain_at _ _ _ _ H))
             (startup_cert RZ RZr) (startup_certB RZ RZr) (startup_certC RZ RZr) (startup_certD RZ RZr) (startup2_cert RZ RZr)).
  Qed.
End Bridge.

(* the main entry's facts hold in the computed states at both CONFIG_RSEQ values *)
Lemma main_justified : forall r, 0 <= r <= 1 -> forall w : bool, JUST r w (if w then stS1 r else stS2 r).
Proof.
  intros r Hr w. assert (r = 0 \/ r = 1) as [-> | ->] by lia; destruct w; unfold JUST; vm_compute; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem asan_side_ok : forall T : tfam,
  (forall en inp, valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      T inp en [] /\ forall ms mo, amain_at en inp ms mo -> srealizes asegs (mkCfg ms mo) (T inp en)) ->
  side_ok asegs a_init_pc a_phdrs target_alloc_limit T.
Proof.
  intros T HT. apply side_ok_of_srealizes. intros [sp brk0 mbase rdraw] inp Hv Hi.
  destruct (HT _ _ Hv Hi) as [Tnil MAINA].
  (* valid_input_either's conjuncts by shape (LPS 727298f3: 15 of them); the channel reader is its
     reader clause, which AsanInit's start state needs (co_reader) *)
  pose proof Hi as (Hva & Hve & Hfs & _ & _ & [Huid Hgid] & Hnof & Hsigm & Hhw & Hvasz & _ & Hlaunch & Hrdr & Hspt & Hkern).
  apply (proj1 (valid_entry_sv48 _ _ _ Hvasz)) in Hv.
  destruct Hv as (Hsp & Hbrk & Hmb & Hfit & Hlau).
  (* the run reads the image's segments and the vDSO pair; the walk is over the image's own *)
  unfold vsegs. cbn [en_sp en_brk en_mmap_base en_draw].
  apply RomStable.srun_init; [reflexivity|].
  destruct inp as [argv envp ifs stdin uid gid groups net nof sigm hw abt vasz urnd tmp kb execfn chrd sdef spt].
  cbn in Hfit, Hva, Hve, Hfs, Huid, Hgid, Hhw, Hvasz, Hrdr, Hspt. cbn [in_kernel] in Hkern. subst vasz chrd spt.
  (* the input is AsanInit's launch input at the recorded kernel build: AsanInit's input seeds the
     run's /tmp into its file system and declares none, which is the same run (by conversion, as
     at main) *)
  rewrite Hkern in Tnil, MAINA, Hlaunch, Hlau |- *.
  eapply asan_main_boot with (sp := sp) (brk0 := brk0) (mbase := mbase) (rdraw := rdraw) (argv := argv) (envp := envp)
    (fs := fs_seed_tmp ifs tmp) (stdin := stdin) (uid := uid) (gid := gid) (groups := groups) (net := net) (nof := nof)
    (sigm := sigm) (hw := hw) (abt := abt) (urnd := urnd) (kb := kb) (execfn := execfn) (sdef := sdef);
    first [ exact (main_justified _ (rseq_z_range (kb_rseq kb))) | exact Tnil | exact MAINA | eassumption ].
Qed.

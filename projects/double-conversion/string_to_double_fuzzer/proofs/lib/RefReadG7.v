(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SpecConsts.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib MemSplit Frame StreamSim SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib RefMemcpyBase RefMemcpy MallocDefs RefEnframeBase RefEnframe RefGetMeta RefNodes LibKnowFrame LibKnowXfer RefReadLib RefReadBase RefReadStage RefReadChunk RefReadG0.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.

(* [comment removed for export] *)
Module RefReadG8.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AllocSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.FileSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AgentLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MemSplit OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Frame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpy OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MallocDefs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefEnframeBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefEnframe OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefGetMeta OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowFrame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowXfer OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadStage OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadChunk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG0.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.
Section FPW_1. Context {fx : PropExec.FPState}.


Section G.
  Variables (sp0 p1 mb gm can sec : word) (path content : list byte).   (* [comment removed for export] *)
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadStage.modelG path stdin0 fs0 tid) (only parsing).
  #[local] Notation oom_branch := (RefReadStage.oom_branch sp0 path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e can sec content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV40 Pf off :=
    lazymatch type of EV40 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 40) _ off _ EV40); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV40 Pf off w z :=
    lazymatch type of EV40 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 40) _ off w (ELit z) (Z_to_bv 64 z) EV40 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  #[using="Type"] Theorem grow8 : forall R M V B e M0 K TOOM,
    full 8 sp0 p1 mb gm L B e can sec content M0 R M V ->
    (16777216 <= L)%Z ->
    (0x1000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    oom_branch M0 TOOM -> half_branch 9 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32608) M (seg_rom RSEGS)) (modelG 16777216 V)) (t_alt2 TOOM K).
  Proof.
    intros R M V B e M0 K TOOM ST HL64 Hmb0 Hmb1 Hmba HspR HOOM HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Visp & Vlim & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 8) with 16781312%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e can sec extra) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals_RD; rewrite length_app; destruct extra; [discriminate|]; cbn [length tl] in HLx |- *; lia).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.   (* [comment removed for export] *)
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBsp.   (* [comment removed for export] *)
    cbn [kentry_ok] in KBsp. unfold estart, BELOW in KBsp. cbn [a_base a_off BA LA MBA edenot ev] in KBsp. rewrite P5, P0 in KBsp.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 8388608 (dropz 8388608 content)) = Z.to_nat 8388608)
      by (pose proof (pref_length 8388608 (dropz 8388608 content) ltac:(lia)); pose proof (dropz_length 8388608 content ltac:(lia)); lia).
    assert (EBc : gblobs content 15%nat = pref 8388608 (dropz 8388608 content))
      by (rewrite <- (gblobs_cb 8) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 40%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x9a1ec) Mc MD ECALLW 33554452 TOOM K fetch_9a034 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 33554452) with 33558528%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | unfold init_sp_ok, sp_window_lo; cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps]; cbn [vm_init_sp]; rewrite ?Visp; lia ];
          cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
      + (* [comment removed for export] *)
        intros err Herr. cbn [mmap_errnos In] in Herr. destruct Herr as [<-|[]]. subst E.
        rewrite v_addi_pc4 by lia. change (631276 + 4)%Z with 0x9a1f0%Z.
        lazymatch type of HR with regs_ok ?E _ _ =>
          pose proof (regs_set_a0 E _ _ (errno_ret ENOMEM) (ELit (- 12)) HR eq_refl) as HR2 end.
        clear HR. rename HR2 into HR.
        save_know HK. run_block_keep scr0 40%nat. note_pres HKb EQM PRES.
        apply HOOM. split; [|split; [|split; [|split]]].
        * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. rewrite P0. f_equal; lia.
        * regv HR (3 : reg). reflexivity.
        * regv HR (4 : reg). reflexivity.
        * exact PRES.
        * intros d m Hd Hm.
          lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
            let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in
            pose proof (kwr_store_ok RSEGS E Mc kn i (EVar 0) (-8388608)%Z 8388608%Z (-8388608 + d)%Z m HK eq_refl ltac:(lia) ltac:(lia)) as ST end.
          unfold adenot, v_addi in ST. cbn [a_base a_off BA LA MBA edenot ev] in ST. rewrite P0 in ST.
          replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia. exact ST.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 33554452) with 33558528%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (631276 + 4)%Z with 0x9a1f0%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        unfold alloc_top, stack_max_size in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps] in GC. rewrite ?Vmaps in GC. cbn [vm_init_sp] in GC. rewrite Visp in GC.   (* [comment removed for export] *)
        cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps] in GF, GLv. rewrite Vres, Vmaps, rsegs_reserved in GF.
        assert (GB1 : (0xe6000 <= bv_unsigned B')%Z).
        { (* [comment removed for export] *)
          pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 139264) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X1.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 204800) (Z_to_bv 64 499712) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X2.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 704512) (Z_to_bv 64 24576) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X3.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 729088) (Z_to_bv 64 212992) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X1 by lia. rewrite !u_small in X2 by lia. rewrite !u_small in X3 by lia.
          rewrite !u_small in X by lia. pose proof (u64_range B'). lia. }
        assert (GB2 : (bv_unsigned B' + 33558528 <= bv_unsigned B \/ bv_unsigned B + 16781312 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 16781312) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 33558528 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P40 : vals_ev (vals ++ [B']) 40 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 41%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD40 : adenot E (SA (EVar 40) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 40) HR2 ltac:(cbn [edenot ev]; subst E; exact P40)) as HR. clear HR2.
        assert (KA40 : kentry_ok RSEGS E M1 (KAlign (EVar 40) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. exact GA. }
        assert (KR40 : kentry_ok RSEGS E M1 (KRange (EVar 40) 0xe6000 (CEIL - 33558528))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. unfold CEIL. lia. }
        assert (KD40a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 40) 0) 33558528 (SA (EVar 5) 0) 16781312)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, P5. lia. }
        assert (KD40b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 40) 0) 33558528 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, P2. lia. }
        assert (KD40c : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BELOW (SA (EVar 40) 0) 33558528)).   (* [comment removed for export] *)
        { cbn [kentry_ok]. unfold estart, BELOW. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA40 (know_ok_cons _ _ _ _ _ KR40
                     (know_ok_cons _ _ _ _ _ KD40a (know_ok_cons _ _ _ _ _ KD40b (know_ok_cons _ _ _ _ _ KD40c HK2))))) as HK2'.
        clear KA40 KR40 KD40a KD40b KD40c HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 40) 0 33558528 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD40 in HK3. clear HK2'.
        assert (KW40 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 33558528) M1) (KWr (SA (EVar 40) 0) 33558528)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW40 HK3) as HK. clear KW40 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 33558528) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 33558528); [lia | lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 41%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4176%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P40 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 40) 12%Z Z12. kzero_at HK (EVar 40) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P40 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 10) (bv_unsigned mb + 4160) (bv_unsigned B') 33562592 0 33554432 0 0 33558512 (bv_unsigned B' + 16) 10) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 40) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P40; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x1abc8 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x3261c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x3261c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4160))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 33554432) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 10) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x3261c) (Z_to_bv 64 10) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 628988) with (0x998fc : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD40. subst E.
        grow_vals HL (junk_vals R3) 73%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 40) (ELit 176))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P40. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 40) 13) \/ estart E (SA (EVar 40) 13) + 33558511 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P40 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 40) 13 33558511 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (33558512 - 4 - 33554432 - 16 * 10))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (33558512 * 0 / 16 + 10)%Z with 10%Z in Pm2 by (vm_compute; reflexivity).
        replace (33558512 - 4 - 33554432 - 16 * 10)%Z with 3916%Z in Pe4 by reflexivity.
        assert (EV40 : edenot E (EVar 40) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P40).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 172) 1 (ELit 0))) by (hdr_byte EV40 Pm4 172%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 173) 1 (ELit 160))) by (hdr_byte EV40 Pm3 173%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 174) 2 (ELit 10))) by (hdr_word EV40 Pm2 174%Z 2%nat 10%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 33554608) 1 (ELit 0))) by (hdr_byte EV40 Pzr 33554608%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 33558519) 1 (ELit 0))) by (hdr_byte EV40 Pe5 33558519%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 33558520) 4 (ELit 3916))) by (hdr_word EV40 Pe4 33558520%Z 4%nat 3916%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 13) 1 (ELit 224))) by (hdr_byte EV40 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 14) 2 (ELit 10))) by (hdr_word EV40 Ps2 14%Z 2%nat 10%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 33558511); [lia | lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 73%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 16781312)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 160 (ELit 8388608) 14%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 8388768 (ELit 8388608) 15%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 14%nat) with (gblobs content 14%nat) in SRC1. rewrite (gblobs_hb 8) in SRC1 by lia. change (held_of 8) with 8388608%Z in SRC1.
        change (eb E 15%nat) with (gblobs content 15%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 8388608 content) = Z.to_nat 8388608) by (pose proof (pref_length 8388608 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 160)) (length (pref 16777216 content)) = Some (pref 16777216 content)).
        { replace (pref 16777216 content) with (pref 8388608 content ++ pref 8388608 (dropz 8388608 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 160) + nat_to_word (Z.to_nat 8388608)) with (adenot E (SA (EVar 5) 8388768)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 16777216 content) = Z.to_nat 16777216) by (pose proof (pref_length 16777216 content ltac:(lia)); lia).
        assert (EBf : gblobs content 16%nat = pref 16777216 content) by (rewrite <- (gblobs_fb 8) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 40) 176)). set (src := adenot E (SA (EVar 5) 160)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 176)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 160)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 16777216 (pref 16777216 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x32638)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x32638) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 16777216) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 16777216 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x32638) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 681768) with (0xa6728 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 40) 176 16%nat (pref 16777216 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 176)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 176)) (pref 16777216 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 176) 16777216); [lia | lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV40 Hflat5.
        grow_vals HL (junk_vals R5) 105%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 105%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 16781312)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 156%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 157%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 158%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4136%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4144%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4148%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0xe4d28%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        cbn [ev] in Gsec. rewrite P8 in Garea, Gsec.   (* [comment removed for export] *)
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 160) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 9 16785376 0 0 sec) end.   (* [comment removed for export] *)
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 160 - 4)%Z with (bv_unsigned B + 156)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 160 - 3)%Z with (bv_unsigned B + 157)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 160 - 2)%Z with (bv_unsigned B + 158)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4120)) with 4120%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4120 + 24)%Z with (bv_unsigned mb + 4144)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4120 + 28)%Z with (bv_unsigned mb + 4148)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4120) mod 4096 = 24)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4120 - 24)%Z with (bv_unsigned mb + 4096)%Z by lia. exact Garea.
          - exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x1abc8 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 160) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 9 16785376 0 0).
        { constructor.
          all: try (change (w_lastidx 16785376) with 0%Z); try (change (w_sizeclass 16785376) with 63%Z);
               try (change (w_maplen 16785376) with 4097%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x98380)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 160))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x98380) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x98380) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 623912) with (0x98528 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 137%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4120)) (ridx 11) (ELit 9)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 137%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x9a358) Mc MD ECALLW B 16781312 K fetch_9a1a0 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 16781312) with 16781312%Z. rewrite task_size_val. lia.   (* [comment removed for export] *)
        * change (page_round_up_Z 16781312) with 16781312%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 16781312) with 16781312%Z.
          rewrite v_addi_pc4 by lia. change (0x9a358 + 4)%Z with 0x9a35c%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 16781312 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 16781312); [lia | lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 137%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadStage.modelG mkModelA]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x32640) Mc (seg_rom RSEGS)) (modelG (held_of 9) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 40; EExt true 0 4 (EVar 6); EVar 7] ++ (EVar 8 :: tl srf));
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) can sec (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 9) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 9) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app tl].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P40, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_init_sp vm_limit vm_maps]. split; [exact Vres|]. split; [exact Visp|]. split; [exact Vlim|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 9) with 33558528%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 9) with 33558528%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.
End FPW_1.

End RefReadG8.

(* [comment removed for export] *)
Module RefReadG9.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AllocSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.FileSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AgentLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MemSplit OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Frame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpy OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MallocDefs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefEnframeBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefEnframe OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefGetMeta OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowFrame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowXfer OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadStage OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadChunk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG0.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.
Section FPW_2. Context {fx : PropExec.FPState}.


Section G.
  Variables (sp0 p1 mb gm can sec : word) (path content : list byte).   (* [comment removed for export] *)
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadStage.modelG path stdin0 fs0 tid) (only parsing).
  #[local] Notation oom_branch := (RefReadStage.oom_branch sp0 path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e can sec content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV40 Pf off :=
    lazymatch type of EV40 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 40) _ off _ EV40); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV40 Pf off w z :=
    lazymatch type of EV40 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 40) _ off w (ELit z) (Z_to_bv 64 z) EV40 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  #[using="Type"] Theorem grow9 : forall R M V B e M0 K TOOM,
    full 9 sp0 p1 mb gm L B e can sec content M0 R M V ->
    (33554432 <= L)%Z ->
    (0x1000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    oom_branch M0 TOOM -> half_branch 10 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32608) M (seg_rom RSEGS)) (modelG 33554432 V)) (t_alt2 TOOM K).
  Proof.
    intros R M V B e M0 K TOOM ST HL64 Hmb0 Hmb1 Hmba HspR HOOM HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Visp & Vlim & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 9) with 33558528%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e can sec extra) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals_RD; rewrite length_app; destruct extra; [discriminate|]; cbn [length tl] in HLx |- *; lia).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.   (* [comment removed for export] *)
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBsp.   (* [comment removed for export] *)
    cbn [kentry_ok] in KBsp. unfold estart, BELOW in KBsp. cbn [a_base a_off BA LA MBA edenot ev] in KBsp. rewrite P5, P0 in KBsp.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 16777216 (dropz 16777216 content)) = Z.to_nat 16777216)
      by (pose proof (pref_length 16777216 (dropz 16777216 content) ltac:(lia)); pose proof (dropz_length 16777216 content ltac:(lia)); lia).
    assert (EBc : gblobs content 17%nat = pref 16777216 (dropz 16777216 content))
      by (rewrite <- (gblobs_cb 9) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 40%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x9a1ec) Mc MD ECALLW 67108884 TOOM K fetch_9a034 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 67108884) with 67112960%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | unfold init_sp_ok, sp_window_lo; cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps]; cbn [vm_init_sp]; rewrite ?Visp; lia ];
          cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
      + (* [comment removed for export] *)
        intros err Herr. cbn [mmap_errnos In] in Herr. destruct Herr as [<-|[]]. subst E.
        rewrite v_addi_pc4 by lia. change (631276 + 4)%Z with 0x9a1f0%Z.
        lazymatch type of HR with regs_ok ?E _ _ =>
          pose proof (regs_set_a0 E _ _ (errno_ret ENOMEM) (ELit (- 12)) HR eq_refl) as HR2 end.
        clear HR. rename HR2 into HR.
        save_know HK. run_block_keep scr0 40%nat. note_pres HKb EQM PRES.
        apply HOOM. split; [|split; [|split; [|split]]].
        * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. rewrite P0. f_equal; lia.
        * regv HR (3 : reg). reflexivity.
        * regv HR (4 : reg). reflexivity.
        * exact PRES.
        * intros d m Hd Hm.
          lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
            let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in
            pose proof (kwr_store_ok RSEGS E Mc kn i (EVar 0) (-8388608)%Z 8388608%Z (-8388608 + d)%Z m HK eq_refl ltac:(lia) ltac:(lia)) as ST end.
          unfold adenot, v_addi in ST. cbn [a_base a_off BA LA MBA edenot ev] in ST. rewrite P0 in ST.
          replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia. exact ST.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 67108884) with 67112960%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (631276 + 4)%Z with 0x9a1f0%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        unfold alloc_top, stack_max_size in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps] in GC. rewrite ?Vmaps in GC. cbn [vm_init_sp] in GC. rewrite Visp in GC.   (* [comment removed for export] *)
        cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps] in GF, GLv. rewrite Vres, Vmaps, rsegs_reserved in GF.
        assert (GB1 : (0xe6000 <= bv_unsigned B')%Z).
        { (* [comment removed for export] *)
          pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 139264) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X1.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 204800) (Z_to_bv 64 499712) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X2.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 704512) (Z_to_bv 64 24576) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X3.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 729088) (Z_to_bv 64 212992) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X1 by lia. rewrite !u_small in X2 by lia. rewrite !u_small in X3 by lia.
          rewrite !u_small in X by lia. pose proof (u64_range B'). lia. }
        assert (GB2 : (bv_unsigned B' + 67112960 <= bv_unsigned B \/ bv_unsigned B + 33558528 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 33558528) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 67112960 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P40 : vals_ev (vals ++ [B']) 40 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 41%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD40 : adenot E (SA (EVar 40) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 40) HR2 ltac:(cbn [edenot ev]; subst E; exact P40)) as HR. clear HR2.
        assert (KA40 : kentry_ok RSEGS E M1 (KAlign (EVar 40) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. exact GA. }
        assert (KR40 : kentry_ok RSEGS E M1 (KRange (EVar 40) 0xe6000 (CEIL - 67112960))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. unfold CEIL. lia. }
        assert (KD40a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 40) 0) 67112960 (SA (EVar 5) 0) 33558528)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, P5. lia. }
        assert (KD40b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 40) 0) 67112960 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, P2. lia. }
        assert (KD40c : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BELOW (SA (EVar 40) 0) 67112960)).   (* [comment removed for export] *)
        { cbn [kentry_ok]. unfold estart, BELOW. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA40 (know_ok_cons _ _ _ _ _ KR40
                     (know_ok_cons _ _ _ _ _ KD40a (know_ok_cons _ _ _ _ _ KD40b (know_ok_cons _ _ _ _ _ KD40c HK2))))) as HK2'.
        clear KA40 KR40 KD40a KD40b KD40c HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 40) 0 67112960 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD40 in HK3. clear HK2'.
        assert (KW40 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 67112960) M1) (KWr (SA (EVar 40) 0) 67112960)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW40 HK3) as HK. clear KW40 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 67112960) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 67112960); [lia | lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 41%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4136%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P40 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 40) 12%Z Z12. kzero_at HK (EVar 40) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P40 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 11) (bv_unsigned mb + 4120) (bv_unsigned B') 67117024 0 67108864 0 0 67112944 (bv_unsigned B' + 16) 11) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 40) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P40; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x1abc8 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x3261c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x3261c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4120))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 67108864) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 11) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x3261c) (Z_to_bv 64 11) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 628988) with (0x998fc : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD40. subst E.
        grow_vals HL (junk_vals R3) 73%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 40) (ELit 192))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P40. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 40) 13) \/ estart E (SA (EVar 40) 13) + 67112943 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P40 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 40) 13 67112943 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (67112944 - 4 - 67108864 - 16 * 11))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (67112944 * 0 / 16 + 11)%Z with 11%Z in Pm2 by (vm_compute; reflexivity).
        replace (67112944 - 4 - 67108864 - 16 * 11)%Z with 3900%Z in Pe4 by reflexivity.
        assert (EV40 : edenot E (EVar 40) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P40).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 188) 1 (ELit 0))) by (hdr_byte EV40 Pm4 188%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 189) 1 (ELit 160))) by (hdr_byte EV40 Pm3 189%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 190) 2 (ELit 11))) by (hdr_word EV40 Pm2 190%Z 2%nat 11%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 67109056) 1 (ELit 0))) by (hdr_byte EV40 Pzr 67109056%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 67112951) 1 (ELit 0))) by (hdr_byte EV40 Pe5 67112951%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 67112952) 4 (ELit 3900))) by (hdr_word EV40 Pe4 67112952%Z 4%nat 3900%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 13) 1 (ELit 224))) by (hdr_byte EV40 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 14) 2 (ELit 11))) by (hdr_word EV40 Ps2 14%Z 2%nat 11%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 67112943); [lia | lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 73%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 33558528)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 176 (ELit 16777216) 16%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 16777392 (ELit 16777216) 17%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 16%nat) with (gblobs content 16%nat) in SRC1. rewrite (gblobs_hb 9) in SRC1 by lia. change (held_of 9) with 16777216%Z in SRC1.
        change (eb E 17%nat) with (gblobs content 17%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 16777216 content) = Z.to_nat 16777216) by (pose proof (pref_length 16777216 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 176)) (length (pref 33554432 content)) = Some (pref 33554432 content)).
        { replace (pref 33554432 content) with (pref 16777216 content ++ pref 16777216 (dropz 16777216 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 176) + nat_to_word (Z.to_nat 16777216)) with (adenot E (SA (EVar 5) 16777392)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 33554432 content) = Z.to_nat 33554432) by (pose proof (pref_length 33554432 content ltac:(lia)); lia).
        assert (EBf : gblobs content 18%nat = pref 33554432 content) by (rewrite <- (gblobs_fb 9) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 40) 192)). set (src := adenot E (SA (EVar 5) 176)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 192)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 176)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 33554432 (pref 33554432 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x32638)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x32638) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 33554432) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 33554432 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x32638) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 681768) with (0xa6728 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 40) 192 18%nat (pref 33554432 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 192)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 192)) (pref 33554432 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 192) 33554432); [lia | lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV40 Hflat5.
        grow_vals HL (junk_vals R5) 105%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 105%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 33558528)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 172%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 173%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 174%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4176%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4184%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4188%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0xe4d28%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        cbn [ev] in Gsec. rewrite P8 in Garea, Gsec.   (* [comment removed for export] *)
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 176) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 10 33562592 0 0 sec) end.   (* [comment removed for export] *)
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 176 - 4)%Z with (bv_unsigned B + 172)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 176 - 3)%Z with (bv_unsigned B + 173)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 176 - 2)%Z with (bv_unsigned B + 174)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4160)) with 4160%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4160 + 24)%Z with (bv_unsigned mb + 4184)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4160 + 28)%Z with (bv_unsigned mb + 4188)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4160) mod 4096 = 64)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4160 - 64)%Z with (bv_unsigned mb + 4096)%Z by lia. exact Garea.
          - exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x1abc8 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 176) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 10 33562592 0 0).
        { constructor.
          all: try (change (w_lastidx 33562592) with 0%Z); try (change (w_sizeclass 33562592) with 63%Z);
               try (change (w_maplen 33562592) with 8193%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x98380)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 176))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x98380) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x98380) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 623912) with (0x98528 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 137%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4160)) (ridx 11) (ELit 10)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 137%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x9a358) Mc MD ECALLW B 33558528 K fetch_9a1a0 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 33558528) with 33558528%Z. rewrite task_size_val. lia.   (* [comment removed for export] *)
        * change (page_round_up_Z 33558528) with 33558528%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 33558528) with 33558528%Z.
          rewrite v_addi_pc4 by lia. change (0x9a358 + 4)%Z with 0x9a35c%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 33558528 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 33558528); [lia | lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 137%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadStage.modelG mkModelA]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x32640) Mc (seg_rom RSEGS)) (modelG (held_of 10) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 40; EExt true 0 4 (EVar 6); EVar 7] ++ (EVar 8 :: tl srf));
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) can sec (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 10) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 10) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app tl].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P40, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_init_sp vm_limit vm_maps]. split; [exact Vres|]. split; [exact Visp|]. split; [exact Vlim|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 10) with 67112960%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 10) with 67112960%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.
End FPW_2.

End RefReadG9.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AllocSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.FileSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.AgentLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MemSplit OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Frame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpy OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MallocDefs OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefEnframeBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefEnframe OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefGetMeta OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowFrame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowXfer OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadStage OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadChunk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadG0.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.
Section FPW_3. Context {fx : PropExec.FPState}.


Section G.
  Variables (sp0 p1 mb gm can sec : word) (path content : list byte).   (* [comment removed for export] *)
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadStage.modelG path stdin0 fs0 tid) (only parsing).
  #[local] Notation oom_branch := (RefReadStage.oom_branch sp0 path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e can sec content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32640) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV40 Pf off :=
    lazymatch type of EV40 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 40) _ off _ EV40); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV40 Pf off w z :=
    lazymatch type of EV40 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 40) _ off w (ELit z) (Z_to_bv 64 z) EV40 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  #[using="Type"] Theorem grow7 : forall R M V B e M0 K TOOM,
    full 7 sp0 p1 mb gm L B e can sec content M0 R M V ->
    (8388608 <= L)%Z ->
    (0x1000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    oom_branch M0 TOOM -> half_branch 8 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32608) M (seg_rom RSEGS)) (modelG 8388608 V)) (t_alt2 TOOM K).
  Proof.
    intros R M V B e M0 K TOOM ST HL64 Hmb0 Hmb1 Hmba HspR HOOM HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Visp & Vlim & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 7) with 8392704%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e can sec extra) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals_RD; rewrite length_app; destruct extra; [discriminate|]; cbn [length tl] in HLx |- *; lia).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.   (* [comment removed for export] *)
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBsp.   (* [comment removed for export] *)
    cbn [kentry_ok] in KBsp. unfold estart, BELOW in KBsp. cbn [a_base a_off BA LA MBA edenot ev] in KBsp. rewrite P5, P0 in KBsp.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 4194304 (dropz 4194304 content)) = Z.to_nat 4194304)
      by (pose proof (pref_length 4194304 (dropz 4194304 content) ltac:(lia)); pose proof (dropz_length 4194304 content ltac:(lia)); lia).
    assert (EBc : gblobs content 13%nat = pref 4194304 (dropz 4194304 content))
      by (rewrite <- (gblobs_cb 7) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 40%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x9a1ec) Mc MD ECALLW 16777236 TOOM K fetch_9a034 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 16777236) with 16781312%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | unfold init_sp_ok, sp_window_lo; cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps]; cbn [vm_init_sp]; rewrite ?Visp; lia ];
          cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
      + (* [comment removed for export] *)
        intros err Herr. cbn [mmap_errnos In] in Herr. destruct Herr as [<-|[]]. subst E.
        rewrite v_addi_pc4 by lia. change (631276 + 4)%Z with 0x9a1f0%Z.
        lazymatch type of HR with regs_ok ?E _ _ =>
          pose proof (regs_set_a0 E _ _ (errno_ret ENOMEM) (ELit (- 12)) HR eq_refl) as HR2 end.
        clear HR. rename HR2 into HR.
        save_know HK. run_block_keep scr0 40%nat. note_pres HKb EQM PRES.
        apply HOOM. split; [|split; [|split; [|split]]].
        * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. rewrite P0. f_equal; lia.
        * regv HR (3 : reg). reflexivity.
        * regv HR (4 : reg). reflexivity.
        * exact PRES.
        * intros d m Hd Hm.
          lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
            let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in
            pose proof (kwr_store_ok RSEGS E Mc kn i (EVar 0) (-8388608)%Z 8388608%Z (-8388608 + d)%Z m HK eq_refl ltac:(lia) ltac:(lia)) as ST end.
          unfold adenot, v_addi in ST. cbn [a_base a_off BA LA MBA edenot ev] in ST. rewrite P0 in ST.
          replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia. exact ST.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 16777236) with 16781312%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (631276 + 4)%Z with 0x9a1f0%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        unfold alloc_top, stack_max_size in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps] in GC. rewrite ?Vmaps in GC. cbn [vm_init_sp] in GC. rewrite Visp in GC.   (* [comment removed for export] *)
        cbv [m_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps] in GF, GLv. rewrite Vres, Vmaps, rsegs_reserved in GF.
        assert (GB1 : (0xe6000 <= bv_unsigned B')%Z).
        { (* [comment removed for export] *)
          pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 139264) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X1.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 204800) (Z_to_bv 64 499712) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X2.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 704512) (Z_to_bv 64 24576) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X3.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 729088) (Z_to_bv 64 212992) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X1 by lia. rewrite !u_small in X2 by lia. rewrite !u_small in X3 by lia.
          rewrite !u_small in X by lia. pose proof (u64_range B'). lia. }
        assert (GB2 : (bv_unsigned B' + 16781312 <= bv_unsigned B \/ bv_unsigned B + 8392704 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 8392704) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 16781312 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P40 : vals_ev (vals ++ [B']) 40 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 41%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD40 : adenot E (SA (EVar 40) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 40) HR2 ltac:(cbn [edenot ev]; subst E; exact P40)) as HR. clear HR2.
        assert (KA40 : kentry_ok RSEGS E M1 (KAlign (EVar 40) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. exact GA. }
        assert (KR40 : kentry_ok RSEGS E M1 (KRange (EVar 40) 0xe6000 (CEIL - 16781312))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. unfold CEIL. lia. }
        assert (KD40a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 40) 0) 16781312 (SA (EVar 5) 0) 8392704)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, P5. lia. }
        assert (KD40b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 40) 0) 16781312 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, P2. lia. }
        assert (KD40c : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BELOW (SA (EVar 40) 0) 16781312)).   (* [comment removed for export] *)
        { cbn [kentry_ok]. unfold estart, BELOW. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA40 (know_ok_cons _ _ _ _ _ KR40
                     (know_ok_cons _ _ _ _ _ KD40a (know_ok_cons _ _ _ _ _ KD40b (know_ok_cons _ _ _ _ _ KD40c HK2))))) as HK2'.
        clear KA40 KR40 KD40a KD40b KD40c HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 40) 0 16781312 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD40 in HK3. clear HK2'.
        assert (KW40 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 16781312) M1) (KWr (SA (EVar 40) 0) 16781312)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW40 HK3) as HK. clear KW40 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 16781312) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 16781312); [lia | lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 41%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4136%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P40 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 40) 12%Z Z12. kzero_at HK (EVar 40) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P40 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 9) (bv_unsigned mb + 4120) (bv_unsigned B') 16785376 0 16777216 0 0 16781296 (bv_unsigned B' + 16) 9) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 40) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P40; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x1abc8 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x3261c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x3261c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4120))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 16777216) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 9) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x3261c) (Z_to_bv 64 9) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 628988) with (0x998fc : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD40. subst E.
        grow_vals HL (junk_vals R3) 73%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 40) (ELit 160))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P40. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 40) 13) \/ estart E (SA (EVar 40) 13) + 16781295 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P40 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 40) 13 16781295 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (16781296 - 4 - 16777216 - 16 * 9))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (16781296 * 0 / 16 + 9)%Z with 9%Z in Pm2 by (vm_compute; reflexivity).
        replace (16781296 - 4 - 16777216 - 16 * 9)%Z with 3932%Z in Pe4 by reflexivity.
        assert (EV40 : edenot E (EVar 40) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P40).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 156) 1 (ELit 0))) by (hdr_byte EV40 Pm4 156%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 157) 1 (ELit 160))) by (hdr_byte EV40 Pm3 157%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 158) 2 (ELit 9))) by (hdr_word EV40 Pm2 158%Z 2%nat 9%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 16777376) 1 (ELit 0))) by (hdr_byte EV40 Pzr 16777376%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 16781303) 1 (ELit 0))) by (hdr_byte EV40 Pe5 16781303%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 16781304) 4 (ELit 3932))) by (hdr_word EV40 Pe4 16781304%Z 4%nat 3932%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 13) 1 (ELit 224))) by (hdr_byte EV40 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 14) 2 (ELit 9))) by (hdr_word EV40 Ps2 14%Z 2%nat 9%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 16781295); [lia | lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 73%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8392704)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 144 (ELit 4194304) 12%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 4194448 (ELit 4194304) 13%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 12%nat) with (gblobs content 12%nat) in SRC1. rewrite (gblobs_hb 7) in SRC1 by lia. change (held_of 7) with 4194304%Z in SRC1.
        change (eb E 13%nat) with (gblobs content 13%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 4194304 content) = Z.to_nat 4194304) by (pose proof (pref_length 4194304 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 144)) (length (pref 8388608 content)) = Some (pref 8388608 content)).
        { replace (pref 8388608 content) with (pref 4194304 content ++ pref 4194304 (dropz 4194304 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 144) + nat_to_word (Z.to_nat 4194304)) with (adenot E (SA (EVar 5) 4194448)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 8388608 content) = Z.to_nat 8388608) by (pose proof (pref_length 8388608 content ltac:(lia)); lia).
        assert (EBf : gblobs content 14%nat = pref 8388608 content) by (rewrite <- (gblobs_fb 7) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 40) 160)). set (src := adenot E (SA (EVar 5) 144)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 160)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P40, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 144)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 8388608 (pref 8388608 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x32638)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x32638) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 8388608) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 8388608 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x32638) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 681768) with (0xa6728 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 40) 160 14%nat (pref 8388608 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 160)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 160)) (pref 8388608 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 160) 8388608); [lia | lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV40 Hflat5.
        grow_vals HL (junk_vals R5) 105%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 105%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8392704)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 140%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 141%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 142%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4176%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4184%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4188%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0xe4d28%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        cbn [ev] in Gsec. rewrite P8 in Garea, Gsec.   (* [comment removed for export] *)
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 144) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 8 8396768 0 0 sec) end.   (* [comment removed for export] *)
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 144 - 4)%Z with (bv_unsigned B + 140)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 144 - 3)%Z with (bv_unsigned B + 141)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 144 - 2)%Z with (bv_unsigned B + 142)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4160)) with 4160%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4160 + 24)%Z with (bv_unsigned mb + 4184)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4160 + 28)%Z with (bv_unsigned mb + 4188)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4160) mod 4096 = 64)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4160 - 64)%Z with (bv_unsigned mb + 4096)%Z by lia. exact Garea.
          - exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x1abc8 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 144) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 8 8396768 0 0).
        { constructor.
          all: try (change (w_lastidx 8396768) with 0%Z); try (change (w_sizeclass 8396768) with 63%Z);
               try (change (w_maplen 8396768) with 2049%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x98380)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 144))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x98380) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x98380) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 623912) with (0x98528 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 137%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4160)) (ridx 11) (ELit 8)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 137%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x9a358) Mc MD ECALLW B 8392704 K fetch_9a1a0 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 8392704) with 8392704%Z. rewrite task_size_val. lia.   (* [comment removed for export] *)
        * change (page_round_up_Z 8392704) with 8392704%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadStage.modelG mkModelA m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 8392704) with 8392704%Z.
          rewrite v_addi_pc4 by lia. change (0x9a358 + 4)%Z with 0x9a35c%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 8392704 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 8392704); [lia | lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 137%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadStage.modelG mkModelA]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x32640) Mc (seg_rom RSEGS)) (modelG (held_of 8) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 40; EExt true 0 4 (EVar 6); EVar 7] ++ (EVar 8 :: tl srf));
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) can sec (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 8) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 8) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app tl].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P40, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_init_sp vm_limit vm_maps]. split; [exact Vres|]. split; [exact Visp|]. split; [exact Vlim|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 8) with 16781312%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 8) with 16781312%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.

End FPW_3.

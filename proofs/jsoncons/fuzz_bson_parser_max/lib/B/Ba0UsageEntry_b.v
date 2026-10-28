(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec ShapeAlg SpinAlg CatExec CatSim StoreOk AgentLib AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b Ba0StartupK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HandoffBridgeK HandoffBInvK HandoffRolesK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0HandoffK_b Ba0HSK_0_b Ba0HSK_1_b Ba0MainTableK_b Ba0HandoffInstK_b Ba0DrvEntryK_b Ba0UsageEntryK_b Ba0StartupFinalK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB
  ArtRuns ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatFsInv_b Ba0ArtHandoffK_b Ba0ArtHandoffInstK_b Ba0StkShK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0DrvEntryInst_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvStdio_b Ba0DrvA_b
  Ba0DrvE_b Ba0MainPhaseA_b Ba0DrvMain_b Ba0DiagArmRefuse_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ShapeLaws Spec BigintSpec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import HeapIfaceABxI_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import StrictOfB. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import StrictOfBI_b.      (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import SX2. Import SX2S.

Definition sr_mainU : list expr :=
  [ELit 0; ELit 0x1180b0; spx (-48); ELit 0x10800; ELit 0x673d00; EVar 11; EVar 12; EVar 13;
   spx 8; EVar 2; EVar 2; spx 8; EVar 18; EVar 19; EVar 20; EVar 21;
   EVar 22; EVar 23; ELit 0xa7b04; EVar 25; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

Definition kn_mainU : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KWord (SA (EVar 0) 8) 8 (EVar 1);
   KImg 0x10000 0x139000; KImg 0x672290 0x673c30;
   KImg 0x13bcc8 0x13bdb8; KImg 0x13bdb8 0x13bea0; KImg 0x13bea0 0x13c580;
   KWord (SA (ELit 0) 0x693d40) 8 (EVar 3);
   KWord (SA (ELit 0) 0x673c58) 4 (EVar 4); KRange (EVar 4) 1 4194303;
   KImg 0x13bbf8 0x13bca0;
   KWord (SA (ELit 0) 6897520) 4 (ELit 0); KWord (SA (ELit 0) 6897555) 1 (ELit 0); KWord (SA (ELit 0) 6896992) 8 (ELit 6897000); KWord (SA (ELit 0) 6896984) 4 (ELit 1);
   KWord (SA (ELit 0) 6897008) 8 (ELit 1148964); KWord (SA (ELit 0) 6897264) 8 (ELit 619876); KWord (SA (ELit 0) 6896980) 4 (ELit 0); KWord (SA (ELit 0) 6897000) 8 (ELit 0);
   KWord (SA (ELit 0) 6898952) 8 (ELit 0); KWord (SA (ELit 0) 6896976) 1 (ELit 0); KWord (SA (ELit 0) 6897776) 4 (ELit 0)].      (* [comment removed for export] *)

Definition vals_mainU (sp p0 argcw can tid : word) (R : bvmap 5 word) : list word := [sp; p0; argcw; can; tid; Z_to_bv 64 0] ++ junk_vals R.

Section FPX_1. Context {fx : PropExec.FPState}.
Section PackU.
  Variables (sp : word) (argc envc : Z).
  Variable R : bvmap 5 word.
  Variable MV : word -> option byte.
  Variable ebs : nat -> list byte.
  #[local] Abbreviation usp := (bv_unsigned sp).
  Hypothesis Hsp : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
  Hypothesis Hb : 1 <= argc <= 1024 /\ 0 <= envc <= 256.
  Hypothesis REGS : forall r v, In (r, v)
    [(1, 0x1180b0); (2, usp - 48); (3, 0x10800); (4, 0x673d00); (8, usp + 8); (9, argc); (10, argc); (11, usp + 8);
     (12, usp + 16 + 8 * argc); (18, 0xa7b04); (19, usp + 16 + 8 * argc); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)] ->
    getr R (Z_to_bv 5 r) = Z_to_bv 64 v.
  Hypothesis WORD8 : rdn ASEGS MV (Z_to_bv 64 (usp + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * argc + 8 * envc + 184))).
  Hypothesis WINDOW : forall d (m : nat), 0 <= d -> d + Z.of_nat m <= 8388608 -> store_ok ASEGS MV (Z_to_bv 64 (usp - 8388608 + d)) m = true.
  Variable can : word.
  Hypothesis GUARD : rdn ASEGS MV (Z_to_bv 64 0x693d40) 8 = Some (word_to_le_bytes 8 can).
  Hypothesis IMG : forall lo hi i, In (lo, hi) [(0x10000, 0x139510); (0x13952c, 0x13c580); (0x66228a, 0x673c30); (0x693fc8, 0x693ff8)] -> lo <= i < hi -> MV (Z_to_bv 64 i) = None.
  Variable tid : word.
  Hypothesis TIDR : 1 <= bv_unsigned tid <= 4194303.
  Hypothesis TIDW : rdn ASEGS MV (Z_to_bv 64 0x673c58) 4 = Some (word_to_le_bytes 4 tid).
  Hypothesis XCW : Forall (fun c : Z * nat * Z => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c)))) XC9_CELLS.

  Let p0 : word := Z_to_bv 64 (usp + 8 * argc + 8 * envc + 184).
  Let ES : env := Env (vals_ev (vals_mainU sp p0 (Z_to_bv 64 argc) can tid R)) ebs.

  #[using="Type"] Lemma ev_junkU : forall i, (i < 32)%nat -> ev ES (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold ES, vals_mainU. cbn [ev]. unfold vals_ev.
    change (6 + i)%nat with (length [sp; p0; Z_to_bv 64 argc; can; tid; Z_to_bv 64 0] + i)%nat. rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  #[using="Type"] Lemma spx_valU : forall k, edenot ES (spx k) = Z_to_bv 64 (usp + k).
  Proof.
    intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev ES 0) with sp.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  #[using="REGS"] Theorem main_regs_okU : regs_ok ES sr_mainU R.
  Proof.
    apply regs_ok_by_indexA. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; cbn [nth sr_mainU Z.of_nat Pos.of_succ_nat Pos.succ].
    all: try solve [rewrite ?spx_valU; cbn [edenot]; apply REGS; cbn [In]; repeat (first [left; reflexivity | right])].
    all: try (match goal with |- getr R (Z_to_bv 5 ?z) = edenot ES (EVar _) =>
                let k := eval cbv in (Z.to_nat z) in exact (eq_sym (ev_junkU k ltac:(lia))) end).
    (* [comment removed for export] *) cbn [edenot]. reflexivity.
  Qed.

  #[using="Type"] Lemma estart_spU : forall off, estart ES (SA (EVar 0) off) = usp + off.
  Proof. intros off. unfold estart. cbn [a_base a_off edenot]. reflexivity. Qed.

  #[using="Hsp Hb WORD8 WINDOW GUARD IMG TIDR TIDW XCW"] Theorem main_know_okU : know_ok ASEGS ES MV kn_mainU.
  Proof.
    destruct Hsp as (S1 & S2). destruct Hb as (B1 & B2).
    assert (FLIT : forall a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 63 -> flat ES (SA (ELit 0) a) n).
    { intros a n H1 H2 H3. unfold flat, estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia. lia. }
    assert (ALIT : forall a, 0 <= a < 2 ^ 63 -> adenot ES (SA (ELit 0) a) = Z_to_bv 64 a).
    { intros a Ha. rewrite (adenot_flat ES (SA (ELit 0) a) 0 ltac:(apply FLIT; lia)). unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia. reflexivity. }
    assert (FL : forall off n, -8388608 <= off -> 0 <= n -> off + n <= 4096 -> flat ES (SA (EVar 0) off) n).
    { intros off n H1 H2 H3. unfold flat. rewrite estart_spU. lia. }
    assert (XC : forall (i : nat) c, nth_error XC9_CELLS i = Some c ->
                   rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c))))
      by (intros i c Hn; exact (proj1 (Forall_forall _ _) XCW c (nth_error_In _ _ Hn))).
    unfold kn_mainU, know_ok. repeat (apply Forall_cons); [ .. | apply Forall_nil]; cbn [kentry_ok].
    - split; [lia | exact S2].
    - cbn [edenot]. change (ev ES 0) with sp. lia.
    - split; [apply FL; lia|]. intros d m Hd Hm. rewrite estart_spU. replace (usp + -8388608 + d) with (usp - 8388608 + d) by ring. apply WINDOW; assumption.
    - split; [lia|]. split; [apply FL; lia|]. rewrite (adenot_flat ES (SA (EVar 0) 8) 8 ltac:(apply FL; lia)), estart_spU. exact WORD8.
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x10000 0x139510); [left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x66228a 0x673c30); [right; right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x13952c 0x13c580); [right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x13952c 0x13c580); [right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x13952c 0x13c580); [right; left; reflexivity | lia].
    - split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia; lia|].
      rewrite adenot_lit0. exact GUARD.
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact TIDW.
    - cbn [edenot]. change (ev ES 4) with tid. lia.
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x13952c 0x13c580); [right; left; reflexivity | lia].
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 0%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 1%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 2%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 3%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 4%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 5%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 6%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 7%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 8%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 9%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 10%nat _ eq_refl).
  Qed.
End PackU.
End FPX_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tid_chk_0 : tid_chk HS_0 = true.   Proof. vm_compute. reflexivity. Qed.
Lemma tid_chk_1 : tid_chk HS_1 = true.   Proof. vm_compute. reflexivity. Qed.
Lemma tid_chk_HSA : forall h, (h < 2)%nat -> tid_chk (HSA h) = true.
Proof. intros h Hh. destruct h as [|[|h]]; [exact tid_chk_0 | exact tid_chk_1 | lia]. Qed.

Section FPX_2. Context {fx : PropExec.FPState}.
Section InstU.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Abbreviation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Abbreviation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Abbreviation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.
  Hypothesis BUD_le : 16515072 + 2461330432 + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (17729665200128 + BUDGET) + (21 + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  #[local] Abbreviation usp := (bv_unsigned sp).
  #[local] Abbreviation argc := (Z.of_nat (length argv)).
  #[local] Abbreviation envc := (Z.of_nat (length envp)).
  #[local] Abbreviation a0s := (nth 0 argv []).

  #[using="Hsp Hva Hve Hfit BUDGET LENMAX KMAX BUD EXTRA_wf BUD_le GAP"] Theorem as0_main_entryU : forall ebs h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    let A0 := as0_A0 EXTRA (HSA h) E in
    let MV := mrestrict (ahid A0 model) FULL in
    let p0 := Z_to_bv 64 (usp + 8 * argc + 8 * envc + 184) in
    exists can tid : word,
      let ES := Env (vals_ev (vals_mainU sp p0 (Z_to_bv 64 argc) can tid R)) ebs in
      SX2S.regs_ok ES sr_mainU R
      /\ SX2S.know_ok ASEGS ES MV kn_mainU
      /\ lzinv ASEGS (ahid A0 model) A0 model
      /\ m_fds model = APSK.fds_std /\ m_fs model = fs
      /\ rdn ASEGS MV p0 (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])
      /\ bv_unsigned p0 = usp + 8 * argc + 8 * envc + 184
      /\ bv_unsigned p0 + Z.of_nat (length a0s) + 1 + 16 <= 2 ^ 47
      /\ (forall i, 0 <= i < Z.of_nat (length a0s) + 1 + 16 -> FULL (Z_to_bv 64 (bv_unsigned p0 + i)) <> None).
  Proof.
    intros ebs h Hh E R FULL model HC A0 MV p0.
    pose proof (as0_chk_HSA h Hh) as C0. pose proof (drv_chk_HSA h Hh) as CD. pose proof (stk_chk_HSA h Hh) as CS.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP h Hh) as GP.
    assert (G : exists can : word, rdn ASEGS MV (Z_to_bv 64 0x693d40) 8 = Some (word_to_le_bytes 8 can)).
    { edestruct (ent_guard sp brk0 rdraw argv envp uid hw fs) as (can & G1 & G2); [ .. | exists can; exact G1]; eassumption. }
    destruct G as (can & G1). exists can.
    assert (T : exists tid : word, 1 <= bv_unsigned tid <= 4194303 /\ rdn ASEGS MV (Z_to_bv 64 0x673c58) 4 = Some (word_to_le_bytes 4 tid)).
    { eapply (entg_tid sp brk0 rdraw argv envp uid hw fs); try eassumption. exact (tid_chk_HSA h Hh). }
    destruct T as (tid & TR & T2). exists tid. cbv zeta.
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0).
    { destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in H1, H2. lia. }
    assert (HB : 1 <= argc <= 1024 /\ 0 <= envc <= 256).
    { pose proof Hve as [Hle _]. pose proof Hva as (Hac & _). lia. }
    assert (STR : rdn ASEGS MV (cat_argv_ptr sp argv envp 0) (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])
                  /\ bv_unsigned (cat_argv_ptr sp argv envp 0) = usp + 8 * argc + 8 * envc + 184).
    { eapply (entg_str0 sp brk0 rdraw argv envp uid hw fs); try eassumption. }
    destruct STR as (STR1 & PV0).
    assert (PE : p0 = cat_argv_ptr sp argv envp 0).
    { unfold p0. apply bv_eq. rewrite PV0, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity. }
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    - apply (main_regs_okU sp argc envc R ebs).
      eapply (entg_regs sp brk0 rdraw argv envp uid hw fs); try eassumption.
    - apply (main_know_okU sp argc envc R MV ebs SR HB).
      + eapply (entg_stack_words sp brk0 rdraw argv envp uid hw fs); try eassumption.
      + eapply (ent_window sp brk0 rdraw argv envp uid hw fs); eassumption.
      + exact G1.
      + eapply (ent_img sp brk0 rdraw argv envp uid hw fs); eassumption.
      + exact TR.
      + exact T2.
      + change XC9_CELLS with XC9K. eapply (ent_xcells sp brk0 rdraw argv envp uid hw fs); try eassumption; first [reflexivity | exact (xc_chk_HSA h Hh)].
    - unfold lzinv. eapply (ent_lz sp brk0 rdraw argv envp uid hw fs); eassumption.
    - eapply (ent_model sp brk0 rdraw argv envp uid hw fs); eassumption.
    - eapply (ent_model sp brk0 rdraw argv envp uid hw fs); eassumption.
    - rewrite PE. exact STR1.
    - rewrite PE. exact PV0.
    - rewrite PE. eapply (entg_str0_hi sp brk0 rdraw argv envp uid hw fs); try eassumption.
    - rewrite PE. eapply (entg_str0_defined sp brk0 rdraw argv envp uid hw fs); try eassumption.
  Qed.

  #[using="Hsp Hva Hve Hfit BUDGET LENMAX KMAX BUD EXTRA BUD_le GAP"] Theorem as0_main_stack_definedU : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    forall top, top mod 4096 = 0 -> top <= usp + 4096 -> defined FULL usp (top - usp).
  Proof.
    intros h Hh E R FULL model HC top Hm Hle i Hi.
    pose proof (as0_chk_HSA h Hh) as C0. pose proof (drv_chk_HSA h Hh) as CD. pose proof (stk_chk_HSA h Hh) as CS.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP h Hh) as GP.
    eapply (entg_stack_defined_top sp brk0 rdraw argv envp uid hw fs); try eassumption.
  Qed.
End InstU.
End FPX_2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX_3. Context {fx : PropExec.FPState}.
Definition rU := Eval vm_compute in runA (SCR [true] [] []) (SS 0xa7b04 sr_mainU [] kn_mainU 38).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
Definition knU : list kentry := Eval vm_compute in kn_after rU kn_mainU.
End FPX_3.

(* [comment removed for export] *)
Lemma usage_itinerary_okA :
  (s_pc (fst (fst rU)), snd (fst rU)) = (0x633bc, [SCBr true BC_NE (EVar 2) (ELit 2)])
  /\ (nth 1 srU (ELit 0), nth 2 srU (ELit 0), nth 4 srU (ELit 0), nth 8 srU (ELit 0), nth 10 srU (ELit 0), nth 11 srU (ELit 0), nth 12 srU (ELit 0))
     = (ELit 687288, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 6765824, ELit 2, ELit 1293512, ELit 90394, EVar 1)
  /\ forallb (fun K => existsb (kentry_eqb K) knU)
       [KWord (SA (EVar 0) (-56)) 8 (ELit 1147056); KWord (SA (EVar 0) (-64)) 8 (EAlu ALU_ADD (EVar 0) (ELit 8)); KWord (SA (EVar 0) (-72)) 8 (EVar 2);
        KWord (SA (EVar 0) (-80)) 8 (ELit 686852); KWord (SA (EVar 0) (-88)) 8 (EVar 25); KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
        KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-120)) 8 (ELit 0); KWord (SA (EVar 0) 8) 8 (EVar 1)] = true
  /\ dg_kn_ok knU = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section FPX_4. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Usage.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable fs0 : Fs.Fs.
  Variables p0 can : word.
  Variable M0 : word -> option byte.
  Variable LK0 : list fframe.
  Variable cr0 : credit.
  Variable A0 : list (Z * Z).

  #[local] Abbreviation dinvA := (dinv ar HI sp0 M0).
  #[local] Abbreviation ENV0 := (ENVA []).

  (* [comment removed for export] *)
  Definition usage_kA (KU : TSet) : Prop :=
    forall vals R M (model : Model),
      length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = p0 -> vals_ev vals 3 = can ->
      regs_ok (ENV0 vals) srU R -> know_ok ASEGS (ENV0 vals) (mrestrict (ahid A0 model) M) knU ->
      dinvA [] LK0 cr0 A0 M model -> m_fds model = fds0 -> m_fs model = fs0 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x633bc) M (seg_rom ASEGS)) model) KU.

  #[using="L C IL HIok Hsp DL"] Theorem drv_usageA : forall KU R (model : Model) (argcw tid : word),
    let vals := vals_mainU sp0 p0 argcw can tid R in
    bv_unsigned argcw <> 2 ->
    regs_ok (ENV0 vals) sr_mainU R -> know_ok ASEGS (ENV0 vals) (mrestrict (ahid A0 model) M0) kn_mainU ->
    dinvA [] LK0 cr0 A0 M0 model -> m_fds model = fds0 -> m_fs model = fs0 ->
    usage_kA KU ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7b04) M0 (seg_rom ASEGS)) model) KU.
  Proof.
    intros KU R model argcw tid vals Hargc HR HK DI Hfds Hfs0 HKU.
    pose proof Hsp as Hsp'.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals_mainU; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0) by reflexivity.
    assert (P2 : vals_ev vals 2 = argcw) by reflexivity.
    assert (P3 : vals_ev vals 3 = can) by reflexivity.
    clearbody vals.
    drv_block0 HIok Hsp DL HR HK DI P0 (SCR [true] [] []) 38%nat.
    { unfold sc_denot, LinuxProcessSemantics.Riscv.Sem.branch_taken. cbn [edenot ev ENVA]. rewrite P2. unfold bv_eqb.
      apply negb_true_iff, Z.eqb_neq. change (bv_unsigned (Z_to_bv 64 2)) with 2. exact Hargc. }
    destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite Hfds in F1. rewrite Hfs0 in F2.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?mc) _ => apply (HKU vals Rc Mc mc) end; try assumption.
  Qed.
End Usage.
End FPX_4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Definition dg_usage_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  forall ar HI sp0 M0, drv_ctxA scfg L C IL ar HI sp0 M0 -> forall a0s fs0 p0 can cr0 A0, drv_pathA sp0 M0 p0 a0s ->
    shadow_allowed A0 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    usage_kA scfg ar HI sp0 fs0 p0 can M0 [] cr0 A0 (t_die (msg_usage a0s) fs0).

Lemma spec_usageA : forall argv fs, length argv <> 2%nat -> spec argv fs = t_die (msg_usage (nth 0 argv [])) fs.
Proof. intros argv fs H. destruct argv as [|a [|b [|c l]]]; try reflexivity. exfalso. apply H. reflexivity. Qed.

Section UsagePhase.
  Variable scfg : SpuriousCfg.
  Variable L : asan_layout.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable BUDGET : Z.
  Hypothesis BUD_ge : 2 ^ 34 <= BUDGET.
  Hypothesis BUD_hi : BUDGET <= 2 ^ 39 - 2 ^ 35.
  Hypothesis INST_OK : inst_ok_stmt scfg L C BUDGET.
  Hypothesis FREE_NULL : free_null_stmt scfg L BUDGET.
  Hypothesis H4E : h4e_stmt BUDGET.
  Hypothesis ICPT_OK : icpt_ok_stmt scfg L IL BUDGET.
  Hypothesis DLA_OK : dla_ok_stmt scfg L C IL.
  Hypothesis DRV_CONSTS : drv_consts_stmt L C IL.
  Hypothesis DG_USAGE : dg_usage_stmt scfg L C IL.

  #[using="L C IL BUDGET BUD_ge BUD_hi INST_OK FREE_NULL H4E ICPT_OK DLA_OK DRV_CONSTS DG_USAGE"] Theorem as0_usage : usage_stmt scfg.
  Proof.
    unfold usage_stmt. intros sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit Hvfs h Hh2 E R FULL model HC Hargc.
    assert (EFS : m_fs model = fs).
    { exact (proj2 (ent_model sp brk0 rdraw argv envp uid hw fs (HSA h) (drv_chk_HSA h Hh2) E R FULL model HC)). }
    rewrite (spec_usageA argv fs Hargc).
    pose proof (mp_bud BUDGET BUD_ge) as MPB. pose proof (mp_gap BUDGET BUD_hi) as MPG.
    (* [comment removed for export] *)
    set (cs := HSA h). set (rn := as0_rn E cs). set (ar := as0_ar E cs).
    set (MAPS0 := vm_maps (m_vmmaps model)). set (RESV0 := segments_reserved ASEGS0). set (NOACC0 := vm_noaccess (m_vmmaps model)).
    pose proof (as0_art_handoff_h sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit BUDGET BUD_ge BUD_hi h Hh2 E R FULL model HC) as HT.
    pose proof (as0_handoff_static sp brk0 rdraw argv envp uid hw fs BUDGET BatInv_b.LENMAX BatInv_b.KMAX MPB MPG h Hh2 E R FULL model HC) as BS.
    rewrite (as0_RES_art h Hh2 E) in BS. fold cs rn in BS.
    pose proof (sp0_val sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit BUDGET BatInv_b.LENMAX BatInv_b.KMAX (HSA h) (drv_chk_HSA h Hh2) (mp_gap_h BUDGET BUD_hi h Hh2)
                  E R FULL model HC) as SPV.
    pose proof HT as (REP & _ & _ & _ & CLI & _). destruct REP as (ROK & _).
    (* [comment removed for export] *)
    set (HR0 := HIR BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn).
    assert (INSTR : hl_img_hi L <= BIGSHADOW_LO /\ HAJ.asan_iface_okR L ar C scfg HR0 /\ rt_flag_in_fs L ar HR0).
    { apply (INST_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    destruct INSTR as (IMGL & HIRok & FLG).
    assert (HIok : asan_iface_okB L ar C scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)) by exact (strict_ok L ar C scfg HR0 IMGL FLG HIRok).
    assert (FNok : afree_null_spec L ar scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)).
    { apply (strict_free_null_of L ar C scfg HR0 HIRok). apply (FREE_NULL MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    assert (ICR : aicpt_ok L ar IL scfg HR0).
    { apply (ICPT_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    pose proof (strict_of_nil HR0 _ _ _ _ (H4E _ _ _ _ _ _ _ _ _ _ _ _ HT)) as RI.
    set (HI := HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn) in *.
    change (HAJ.strict_of HR0) with HI in RI.
    assert (SPT : ar_sptop ar = bv_unsigned sp) by exact SPV.
    assert (ICok : aicpt_ok L ar IL scfg HI) by exact (strict_icpt L ar C IL scfg HR0 IMGL HIRok ICR).
    pose proof (DLA_OK ar HI sp HIok SPT) as DL.
    (* [comment removed for export] *)
    pose proof (as0_EXTRA_wf cs E) as XWF.
    assert (XBL : 16515072 + 2461330432 + A_bytes (as0_EXTRA cs E) + BUDGET <= AsanInitK.LIMIT).
    { unfold as0_EXTRA. cbn [A_bytes fst snd]. unfold AsanInitK.LIMIT, target_alloc_limit. lia. }
    destruct (as0_main_entryU sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit BUDGET BatInv_b.LENMAX BatInv_b.KMAX MPB (as0_EXTRA cs E) XWF XBL MPG
                (blobs_ev [[]; []; []; []; []]) h Hh2 E R FULL model HC) as (can & tid & HR & HK & LZ & FDS & _ & STR & PV & PH & PDEF).
    pose proof LZ as (HOFF & _ & _ & MI & HALT).
    destruct CLI as (_ & _ & SAH & _ & S1 & S2 & S3 & S4 & S5 & _).
    cbn [as0_rn rn_ar as0_ar ar_stack_top ar_stack_bottom ar_sptop] in S1, S2, S3, S4, S5.
    assert (SDEF : defined FULL (bv_unsigned sp) (ar_stack_top ar - bv_unsigned sp)).
    { apply (as0_main_stack_definedU sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit BUDGET BatInv_b.LENMAX BatInv_b.KMAX MPB (as0_EXTRA cs E) XBL MPG
               h Hh2 E R FULL model HC); unfold ar, cs; cbn [as0_ar ar_stack_top]; rewrite SPV in *.
      - rewrite S5. rewrite <- Z.add_mod_idemp_l by lia. rewrite S3. reflexivity.
      - lia. }
    assert (DI : dinv ar HI sp FULL [] [] (8192, 2 ^ 34) (as0_A0x cs E) FULL model).
    { apply DINV; [exact RI | exact MI | exact HALT | reflexivity | |].
      intros x Hx. apply (as0_stksh_main sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit h Hh2 E R FULL model HC). unfold STKTOP, ar, cs in Hx. cbn [as0_ar ar_sptop ar_stack_top] in Hx. rewrite SPV in Hx. exact Hx.
      intros x Hx. apply (as0_stksh_main_hi sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit h Hh2 E R FULL model HC). unfold ahl_ceil, ar, cs in Hx. cbn [as0_ar ar_sptop] in Hx. rewrite SPV in Hx. exact Hx. }
    assert (SR : 0x7fff80000000 <= bv_unsigned sp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
    assert (SA16 : bv_unsigned sp mod 16 = 0) by (destruct Hsp as (_ & _ & H3); exact H3).
    assert (HAC : 1 <= Z.of_nat (length argv) <= 1024) by (destruct Hva as (Hac & _); exact Hac).
    set (p0 := Z_to_bv 64 (bv_unsigned sp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)) in *.
    set (a0s := nth 0 argv []) in *.
    assert (CTX : drv_ctxA scfg L C IL ar HI sp FULL) by (constructor; assumption).
    assert (PTH : drv_pathA sp FULL p0 a0s).
    { constructor.
      - rewrite PV. pose proof (Zle_0_nat (length envp)). lia.
      - exact (rdn_of_mrestrict ASEGS _ FULL HOFF _ _ _ STR).
      - destruct Hva as (_ & _ & _ & Hnn & _). unfold a0s. destruct argv as [|a l]; [cbn in HAC; lia|]. inversion Hnn as [|x l' Hx _]; subst. exact Hx.
      - destruct Hva as (_ & _ & Hfa & _). unfold a0s. destruct argv as [|a l]; [cbn in HAC; lia|]. inversion Hfa as [|x l' Hx _]; subst. exact Hx.
      - intros i Hi. exact (PDEF i Hi). }
    unfold APSK.cfg_of, cs. rewrite (HSA_pc h Hh2). fold cs.
    apply (@drv_usageA PropExec.fx0 scfg L ar C IL HI HIok sp SR DL fs p0 can FULL [] (8192, 2 ^ 34) (as0_A0x cs E)
             (t_die (msg_usage a0s) fs) R model (Z_to_bv 64 (Z.of_nat (length argv))) tid).
    - rewrite u_small by lia. intros Hc. apply Hargc. lia.
    - exact HR.
    - exact HK.
    - exact DI.
    - exact FDS.
    - exact EFS.
    - exact (DG_USAGE ar HI sp FULL CTX a0s fs p0 can (8192, 2 ^ 34) (as0_A0x cs E) PTH SAH).
  Qed.
End UsagePhase.

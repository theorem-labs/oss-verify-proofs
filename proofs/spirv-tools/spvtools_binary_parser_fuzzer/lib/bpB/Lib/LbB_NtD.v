(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_NtStmt LbB_NtK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_HEmpD LbB_HEmpI.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_VAL : Z := 0xf5cd4.
Definition E_END : Z := 0xf5cb4.
Definition E_VCHK : Z := 0xf5cd4.
Definition E_FOUND : Z := 0xf58c4.

Definition shEe (e : expr) : expr := EAlu ALU_ADD (EAlu ALU_SRL e (ELit 3)) (ELit 2147450880).
Definition rShe (w : word) : word := alu64 ALU_ADD (alu64 ALU_SRL w (Z_to_bv 64 3)) (Z_to_bv 64 2147450880).

Lemma sh_word : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 2147450880) = Z_to_bv 64 (x / 8 + SHBASE).
Proof.
  intros x Hx. rewrite HWord.w_srl by lia. change (2 ^ 3) with 8.
  assert (0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold SHBASE. rewrite w_add by lia. reflexivity.
Qed.

Lemma C4_lo32 : forall w : word, cbytes (C4 w) = cbytes (C4 (Z_to_bv 64 (lo32 w))).
Proof.
  intros w. cbn [cbytes]. unfold le4, lo32.
  pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
  pose proof (Z.mod_pos_bound (bv_unsigned w) (2 ^ 32) ltac:(lia)) as Hm.
  rewrite u64_of_Z by lia. symmetry. apply BMem.Z_to_le_bytes_mod. cbn. lia.
Qed.

Lemma rw_cells_C4_lo32 : forall m a w, rw_cells asegs m a [C4 w] -> rw_cells asegs m a [C4 (Z_to_bv 64 (lo32 w))].
Proof.
  intros m a w RW. unfold rw_cells in *. destruct RW as ((W0 & W1) & W2 & W3). split; [| split; [exact W2 | exact W3]].
  split; [exact W0|]. cbn [cells_bytes app] in *. rewrite <- C4_lo32. exact W1.
Qed.

Lemma lo32_range : forall w, 0 <= lo32 w < 2 ^ 32.
Proof. intros w. unfold lo32. apply Z.mod_pos_bound. lia. Qed.

Lemma umap_blocks_val : forall NS bl bc (l1 l2 : list (Z * (Z * (Z * Z * Z)))) p k (v v' : Z * Z * Z),
  umap_blocks NS bl bc (l1 ++ (p, (k, v)) :: l2) = umap_blocks NS bl bc (l1 ++ (p, (k, v')) :: l2).
Proof. intros. unfold umap_blocks. rewrite !map_app. reflexivity. Qed.

Ltac rwc_newT Hlf WR fin :=
  lazymatch goal with |- rw_cells _ (mem_denot ?E ?m ?lg) ?A [?c] =>
    let rec go pre post :=
      lazymatch post with
      | SE ?a ?w ?v :: ?post' =>
          first [ eapply (rw_cells_mem_denot_w E m pre a w v post' A c);
                  [ exact Hlf
                  | repeat (apply Forall_cons; [cbn [e_addr e_width]; rwc_norm|]); apply Forall_nil
                  | rwc_norm
                  | exact WR | reflexivity | exact I | fin ]
                | let pre' := eval cbn [app] in (pre ++ [SE a w v]) in go pre' post' ]
      end in
    go (@nil sentry) lg
  end.

Section NtC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

  Variables (gp tp s0 s4 ty wd enc : word) (S1 : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj key v408 v576 v624 : Z) (ents : list ent).
  Variables (bl bc lo B shi : Z) (m0 : mem) (mo0 : Model).

  Definition nval : Z * Z * Z := (lo32 ty, lo32 wd, lo32 enc).
  Definition QF : config -> Prop :=
    nt_post H gp tp s0 s4 sk0 LB0 LF S1 obj key v408 v576 v624 nval ents bl bc lo B shi m0 mo0.

  Definition WSLOTS (m : mem) (j584 j592 : word) : Prop :=
    rw_cells asegs m (S1 + 584) [C8 j584; C8 j592] /\ nt_wslots m S1 obj ty enc.

  Lemma blk_win : forall s LBx m q A N a1 a2, as_RHEAP H s LBx m -> In (q, A, N) LBx -> A <= a1 -> a2 <= A + N ->
    aclient_write_ok H LBx (a1, a2) /\ afs_write_ok H LF (a1, a2) /\ aconst_ok (a1, a2) /\ stack0_ok (a1, a2)
    /\ (a2 <= ALOWSH_LO \/ AHI_LO <= a1).
  Proof.
    intros s LBx m q A N a1 a2 RH IN H1 H2.
    pose proof (ah_blocks H HH _ _ _ _ RH IN) as (B0 & B16 & Bn & BI & BC & BF & BA).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, B16, Bn, BI, BC, BF, BA.
    split; [right; right; left; exists (q, A, N); split; [exact IN | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; lia]|].
    split; [left; cbn [Datatypes.fst Datatypes.snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; split; lia|].
    split; [eapply (aconst_ok_app A N); [exact BA | cbn; lia | cbn; lia]|].
    split; [eapply (stack0_ok_aapp A N); [exact BA | cbn; lia | cbn; lia]|].
    unfold aapp, aapp_lo, aapp_hi in BA. lia.
  Qed.

  Lemma stage_val : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y21 y22 y25 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl' bc' : Z) (l1 l2 : list ent) (v0 : Z * Z * Z) (inserted rehashed : bool)
      (j584 j592 : word),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 (Z_to_bv 64 SHBASE) y16 y17
                             y18 (Z_to_bv 64 v624) s4 y21 y22 (Z_to_bv 64 p) wd y25 (Z_to_bv 64 v408) (Z_to_bv 64 v576) y28 y29 y30 y31)
                        F (Z_to_bv 64 E_VAL) fc None m (seg_rom asegs) ->
    frm_zero fc ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    WSLOTS m j584 j592 -> nt_slots m S1 obj v408 v576 v624 ->
    2 ^ 45 <= S1 -> S1 + 672 <= 2 ^ 47 -> 0 <= v408 < 2 ^ 64 -> 0 <= v576 < 2 ^ 64 -> 0 <= v624 < 2 ^ 64 ->
    mem_inv asegs m -> stk asegs m lo (S1 + 672) -> rw_cells asegs m (errno_addr tp) [C4 errv'] -> as_rauxv_ok H m B ->
    tp = Z_to_bv 64 ATP ->
    umapx MI_A 32 (nval32 ASEGS) (lbl LB') m obj bl' bc' (l1 ++ (p, (key, v0)) :: l2) ->
    umap_sh m 32 (bl', bc', l1 ++ (p, (key, v0)) :: l2) ->
    addressable m obj 40 -> wr_at asegs m obj 40 ->
    (inserted = false -> ents = l1 ++ (p, (key, v0)) :: l2 /\ rehashed = false) ->
    (inserted = true -> Permutation (l1 ++ (p, (key, v0)) :: l2) ((p, (key, v0)) :: ents)) ->
    (rehashed = false -> bl' = bl /\ bc' = bc) ->
    (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc) ->
    as_RHEAP H s LB' m -> Permutation LB' (LB0 ++ LBm') ->
    Permutation (lbl LBm') (umap_blocks 32 bl' bc' (l1 ++ (p, (key, v0)) :: l2)) ->
    lb_own LBm' m ->
    xpres H LB0 S1 (nt_X S1 obj) m0 m ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi -> aceil <= lo -> lo <= S1 ->
    as_AL H s >= as_AL H sk0 - (if rehashed then ICM (8 * bc') else 0) ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y21 y22 y25 y28 y29 y30 y31
      errv' LB' LBm' p bl' bc' l1 l2 v0 inserted rehashed j584 j592
      VIS FRZ KR MP WS NS SPL SPH V408 V576 V624 MI ST ERR RA TPV U SH AD WR CI1 CI2 CR3 CR4 RH PE PM OWN XP RF AC S0 ACL LOS AL.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof WS as (W584 & W600 & W632 & W656).
    pose proof NS as (N408 & N576 & N616 & N624 & N648).
    assert (INp : In (p, (key, v0)) (l1 ++ (p, (key, v0)) :: l2)) by (apply in_app_iff; right; left; reflexivity).
    destruct (u_node U p key v0 INp) as (Hlive & Hp0 & Hp47 & Hpal & _ & _ & Hkr & _ & Hpo & Hpb).
    assert (GZp : gz m p 32).
    { destruct SH as [_ SHn]. eapply LbB_HEmpI.gzA; [exact (SHn p key v0 INp) | reflexivity]. }

    assert (INm : In (p, 32) (lbl LBm')).
    { apply (Permutation_in _ (Permutation_sym PM)). unfold umap_blocks. apply in_app_iff. right. apply in_map_iff.
      exists (p, (key, v0)). split; [reflexivity | exact INp]. }
    destruct (lbl_in_inv _ _ _ INm) as (pid & INm').
    assert (INL : In (pid, p, 32) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact INm').
    pose proof (lb_own_In _ _ _ OWN INm') as OW. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in OW.
    pose proof (ah_blocks H HH _ _ _ _ RH INL) as (B0 & B16 & Bn & BI & BC & BF & BA).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in B0, B16, Bn, BI, BC, BF, BA. unfold AIMG_TOP in BI.
    pose proof BA as PAPP. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in PAPP.
    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 (Z_to_bv 64 SHBASE) y16 y17
                  y18 (Z_to_bv 64 v624) s4 y21 y22 (Z_to_bv 64 p) wd y25 (Z_to_bv 64 v408) (Z_to_bv 64 v576) y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 p; ty; enc; Z_to_bv 64 (obj - 136); wd]).
    assert (HR : regs_ok E (srs sr_id [(9%bv, EVar 32); (23%bv, EVar 33); (15%bv, ELit SHBASE); (24%bv, EVar 37)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]).
      apply Forall_nil. }
    assert (HK : know_ok asegs E m
       (kn_fix 20 [NT_EXIT] (SCR [] [] []) E_VAL (srs sr_id [(9%bv, EVar 32); (23%bv, EVar 33); (15%bv, ELit SHBASE); (24%bv, EVar 37)])
         [ KWord (SA (EVar 32) 608) 8 (EVar 34); KWord (SA (EVar 32) 600) 8 (EVar 35); KWord (SA (EVar 32) 648) 8 (EVar 36);
           KWr (SA (EVar 33) 20) (ELit 12);
           KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KRange (EVar 33) 0x6e8000 (2 ^ 47 - 32); KAlign (EVar 33) 16 ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell W600 8%nat (C8 ty). }
      apply Forall_cons. { kword_cell W600 0%nat (C8 enc). }
      apply Forall_cons. { kword_cell N648 0%nat (C8 (Z_to_bv 64 (obj - 136))). }
      apply Forall_cons.
      { eapply kwr_of_wr_at;
          [ exact (LbB_HEmpD.wr_at_subE m p 32 (p + 20) 12 OW ltac:(lia) ltac:(lia) ltac:(lia))
          | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
          | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
      do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; split; [lia | exact Hpal]|].
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_VAL m (seg_rom asegs) HR HK 40%nat [NT_EXIT] (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1; try sc_shdj; try sc_dj. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (MU1 : munch [(p + 20, p + 32)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (GR1 : forall x, m x <> None -> M1 x <> None).
    { intros x Hx. subst M1. lazymatch goal with |- mem_denot ?EE ?mm ?lg x <> None =>
        destruct (mem_denot_cases EE mm lg x) as [-> | (b & ->)]; [exact Hx | discriminate] end. }
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo (S1 + 672)) by (subst M1; apply stk_mem_denot; exact ST).
    assert (WRA : forall o k, 0 <= o -> o + k <= 32 -> 0 <= k -> wr_at asegs m (p + o) k)
      by (intros o k Ho Hk Hk0; eapply LbB_HEmpD.wr_at_subE; [exact OW | lia | lia | lia]).
    assert (NV1 : rw_cells asegs M1 (p + 20) [C4 ty] /\ rw_cells asegs M1 (p + 24) [C4 wd] /\ rw_cells asegs M1 (p + 28) [C4 enc]).
    { subst M1. split; [|split].
      - rwc_newT Hlf (WRA 20 4 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(evs; reflexivity).
      - rwc_newT Hlf (WRA 24 4 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(evs; reflexivity).
      - rwc_newT Hlf (WRA 28 4 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(evs; reflexivity). }
    destruct NV1 as (NVa & NVb & NVc).
    apply rw_cells_C4_lo32 in NVa. apply rw_cells_C4_lo32 in NVb. apply rw_cells_C4_lo32 in NVc.
    assert (U1 : umapx MI_A 32 (nval32 ASEGS) (lbl LB') M1 obj bl' bc' (l1 ++ (p, (key, nval)) :: l2)).
    { eapply (umapx_set_val32A (lbl LB') m M1); [exact U | | | | exact MU1 | exact GR1 | exact NVa | exact NVb | exact NVc];
        apply lo32_range. }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 9%bv G9. rreg HR' 23%bv G23.
    rewrite G9, G23 in HRe.

    destruct (blk_win s LB' m pid p 32 (p + 20) (p + 32) RH INL ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4 & W5).
    destruct (client_frame H HH s LB' LF B [(p + 20, p + 32)] m M1 RH RF AC RA MU1 WM1
               (Forall_cons _ _ _ W1 (Forall_nil _)) (Forall_cons _ _ _ W2 (Forall_nil _)) (Forall_cons _ _ _ W3 (Forall_nil _)))
      as (RH1 & RF1 & AC1 & RA1).
    assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact (Forall_cons _ _ _ W4 (Forall_nil _))]).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv']).
    { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
      eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; lia]. }
    assert (DSH : forall A n, 0 <= A -> 0 <= n -> A + n <= 2 ^ 47 -> disjoint_from [(p + 20, p + 32)] (sh A) (nsh n)).
    { intros A n HA Hn Han. apply LbB_HEmpI.dsh_app; [| exact HA | exact Hn | exact Han].
      apply Forall_cons; [cbn [Datatypes.fst Datatypes.snd]; exact W5 | apply Forall_nil]. }
    assert (SH1 : umap_sh M1 32 (bl', bc', l1 ++ (p, (key, nval)) :: l2)).
    { destruct SH as [SHb SHn]. unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c in *. cbn [Datatypes.fst Datatypes.snd] in *.
      split.
      - intros Hbc. pose proof (u_bl_lo U Hbc) as B0'. pose proof (u_bl_hi U) as B1'.
        pose proof (LbB_HFind.BSEQ_boundA bc' (u_bseq U)) as BCR.
        eapply addressable_transport; [exact (SHb Hbc) | exact MU1 | exact WM1 | apply DSH; lia].
      - intros q k v Hin.
        assert (Hin0 : exists v', In (q, (k, v')) (l1 ++ (p, (key, v0)) :: l2)).
        { apply in_app_iff in Hin. destruct Hin as [Hin|[Hin|Hin]]; [exists v; apply in_app_iff; left; exact Hin | | exists v; apply in_app_iff; right; right; exact Hin].
          injection Hin as <- <- <-. exists v0. exact INp. }
        destruct Hin0 as (v' & Hin0). destruct (u_node U q k v' Hin0) as (_ & P0 & P1 & _).
        eapply addressable_transport; [exact (SHn q k v' Hin0) | exact MU1 | exact WM1 | apply DSH; lia]. }
    assert (AD1 : addressable M1 obj 40) by (pose proof (u_obj_lo U); pose proof (u_obj_hi U); eapply addressable_transport; [exact AD | exact MU1 | exact WM1 | apply DSH; lia]).
    assert (XP1 : xpres H LB0 S1 (nt_X S1 obj) m0 M1).
    { eapply (xpres_munch_mixed H HH s LB' LB0 LBm' S1 (nt_X S1 obj) [(p + 20, p + 32)] m0 m M1);
        [exact XP | exact RH | exact PE | lia | exact MU1 | exact WM1 |].
      apply Forall_cons; [| apply Forall_nil]. right; right. exists pid, p, 32. split; [exact INm' | cbn; lia]. }
    assert (V584 : rw_cells asegs M1 (S1 + 584) [C8 j584; C8 j592])
      by (eapply rw_cells_transport; [exact W584 | exact MU1 | exact WM1 | cbn; lia]).
    assert (V600 : rw_cells asegs M1 (S1 + 600) [C8 enc; C8 ty])
      by (eapply rw_cells_transport; [exact W600 | exact MU1 | exact WM1 | cbn; lia]).
    assert (V632 : rw_cells asegs M1 (S1 + 632) [C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 (obj / 8))])
      by (eapply rw_cells_transport; [exact W632 | exact MU1 | exact WM1 | cbn; lia]).
    assert (V656 : rw_cells asegs M1 (S1 + 656) [C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 (sh (obj + 8)))])
      by (eapply rw_cells_transport; [exact W656 | exact MU1 | exact WM1 | cbn; lia]).
    assert (V584' : rw_cells asegs M1 (S1 + 584) [C8 j584; C8 j592; C8 enc; C8 ty]).
    { change [C8 j584; C8 j592; C8 enc; C8 ty] with ([C8 j584; C8 j592] ++ [C8 enc; C8 ty]).
      apply rw_cells_app. split; [exact V584|].
      replace (S1 + 584 + Z.of_nat (cells_size [C8 j584; C8 j592])) with (S1 + 600) by (cbn; lia). exact V600. }
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1. apply (ah_done H HH). unfold QF, nt_post. cbn [cfg_ms cfg_model].
    do 21 eexists.
    exists M1, errv', s, LB', LBm', F, fc, p, bl', bc', (l1 ++ (p, (key, nval)) :: l2), inserted, rehashed,
           j584, j592, enc, ty, (Z_to_bv 64 (obj + 8)), (Z_to_bv 64 (obj / 8)), (Z_to_bv 64 obj), (Z_to_bv 64 (sh (obj + 8))).
    split; [rewrite VIS1; reflexivity|].
    split; [exact FRZ|]. split; [exact KR1|]. split; [eapply (ah_mpres_trans H HH); [exact MP | exact MP1]|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact RA1|].
    split; [exact U1|]. split; [exact SH1|]. split; [exact AD1|]. split; [exact (wr_at_wmono _ _ _ _ WR WM1)|].
    split; [apply in_app_iff; right; left; reflexivity|].
    split.
    { intros Hf. destruct (CI1 Hf) as [E1 E2]. exists v0, l1, l2. split; [exact E1|]. split; [reflexivity | exact E2]. }
    split.
    { intros Ht. pose proof (CI2 Ht) as P2.
      apply (Permutation_trans (l' := (p, (key, nval)) :: (l1 ++ l2))).
      - apply Permutation_sym. apply Permutation_middle.
      - apply perm_skip. apply (Permutation_cons_inv (a := (p, (key, v0)))).
        apply (Permutation_trans (l' := l1 ++ (p, (key, v0)) :: l2)); [apply Permutation_middle | exact P2]. }
    split; [exact CR3|]. split; [exact CR4|].
    split; [exact RH1|]. split; [exact PE|]. split; [rewrite (umap_blocks_val 32 bl' bc' l1 l2 p key nval v0); exact PM|].
    split; [exact (lb_own_wmono _ _ _ OWN WM1)|]. split; [exact XP1|].
    split; [exact V584'|]. split; [exact V632|]. split; [exact V656|].
    split; [exact RF1|]. split; [exact AC1|]. split; [exact S01|]. exact AL.
  Qed.

  Lemma stage_found : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y25 y27 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p : Z) (l1 l2 : list ent) (v0 : Z * Z * Z) (j584 j592 : word),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                             y18 (Z_to_bv 64 v624) s4 y21 y22 (Z_to_bv 64 p) wd y25 (Z_to_bv 64 v408) y27 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_FOUND) fc None m (seg_rom asegs) ->
    frm_zero fc ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    WSLOTS m j584 j592 -> nt_slots m S1 obj v408 v576 v624 ->
    2 ^ 45 <= S1 -> S1 + 672 <= 2 ^ 47 -> 0 <= v408 < 2 ^ 64 -> 0 <= v576 < 2 ^ 64 -> 0 <= v624 < 2 ^ 64 ->
    mem_inv asegs m -> stk asegs m lo (S1 + 672) -> rw_cells asegs m (errno_addr tp) [C4 errv'] -> as_rauxv_ok H m B ->
    tp = Z_to_bv 64 ATP ->
    ents = l1 ++ (p, (key, v0)) :: l2 ->
    umapx MI_A 32 (nval32 ASEGS) (lbl LB') m obj bl bc ents -> umap_sh m 32 (bl, bc, ents) ->
    addressable m obj 40 -> wr_at asegs m obj 40 ->
    as_RHEAP H s LB' m -> Permutation LB' (LB0 ++ LBm') -> Permutation (lbl LBm') (umap_blocks 32 bl bc ents) ->
    lb_own LBm' m ->
    xpres H LB0 S1 (nt_X S1 obj) m0 m ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi -> aceil <= lo -> lo <= S1 ->
    as_AL H s >= as_AL H sk0 ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y25 y27 y28 y29 y30 y31
      errv' LB' LBm' p l1 l2 v0 j584 j592
      VIS FRZ KR MP WS NS SPL SPH V408 V576 V624 MI ST ERR RA TPV Eents U SH AD WR RH PE PM OWN XP RF AC S0 ACL LOS AL.
    rewrite Eents in U, SH, PM. pose proof NS as (N408 & N576 & N616 & N624 & N648).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                  y18 (Z_to_bv 64 v624) s4 y21 y22 (Z_to_bv 64 p) wd y25 (Z_to_bv 64 v408) y27 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 p; Z_to_bv 64 v576]).
    assert (HR : regs_ok E (srs sr_id [(9%bv, EVar 32); (23%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]).
      apply Forall_nil. }
    assert (HK : know_ok asegs E m
       (kn_fix 20 [E_VAL] (SCR [] [] []) E_FOUND (srs sr_id [(9%bv, EVar 32); (23%bv, EVar 33)])
         [ KWord (SA (EVar 32) 576) 8 (EVar 34); KWord (SA (EVar 32) 616) 8 (ELit SHBASE);
           KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell N576 0%nat (C8 (Z_to_bv 64 v576)). }
      apply Forall_cons. { kword_cell N616 0%nat (C8 (Z_to_bv 64 SHBASE)). }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_FOUND m (seg_rom asegs) HR HK 40%nat [E_VAL] (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1; try sc_shdj; try sc_dj. }
    clear HK.
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with m in Hms end.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 9%bv G9. rreg HR' 23%bv G23. rreg HR' 15%bv G15. rreg HR' 27%bv G27.
    change (Z_to_bv 64 2147450880) with (Z_to_bv 64 SHBASE) in G15.
    rewrite G9, G23, G15, G27 in HRe.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (stage_val s msF1 mo1 m F fc) with (inserted := false) (rehashed := false) (l1 := l1) (l2 := l2) (v0 := v0) (bl' := bl) (bc' := bc)
      (LB' := LB') (LBm' := LBm') (p := p);
      [ exact VIS1 | exact FRZ | exact KR1 | eapply (ah_mpres_trans H HH); [exact MP | exact MP1] | exact WS | exact NS
      | exact SPL | exact SPH | exact V408 | exact V576 | exact V624 | exact MI | exact ST | exact ERR | exact RA | exact TPV
      | exact U | exact SH | exact AD | exact WR
      | intros _; split; [exact Eents | reflexivity] | intros X; discriminate X | intros _; split; reflexivity | intros X; discriminate X
      | exact RH | exact PE | exact PM | exact OWN | exact XP | exact RF | exact AC | exact S0 | exact ACL | exact LOS | cbn; lia ].
  Qed.

  Lemma stage_end : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y22 y25 y27 y28 y29 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl' bc' : Z) (l1 l2 : list ent) (rehashed : bool) (j584 j592 : word),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 (Z_to_bv 64 SHBASE) y16 y17
                             y18 y19 s4 y21 y22 (Z_to_bv 64 p) wd y25 (Z_to_bv 64 (obj + 24)) y27 y28 y29
                             (rShe (Z_to_bv 64 (obj + 24))) y31)
                        F (Z_to_bv 64 E_END) fc None m (seg_rom asegs) ->
    frm_zero fc ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    WSLOTS m j584 j592 -> nt_slots m S1 obj v408 v576 v624 ->
    2 ^ 45 <= S1 -> S1 + 672 <= 2 ^ 47 -> 0 <= v408 < 2 ^ 64 -> 0 <= v576 < 2 ^ 64 -> 0 <= v624 < 2 ^ 64 ->
    mem_inv asegs m -> stk asegs m lo (S1 + 672) -> rw_cells asegs m (errno_addr tp) [C4 errv'] -> as_rauxv_ok H m B ->
    tp = Z_to_bv 64 ATP ->
    map_live_frame LF obj -> obj mod 8 = 0 ->
    rw_cells asegs m (obj + 24) [C8 (Z_to_bv 64 (Zlength ents))] -> 0 <= Zlength ents < 2 ^ 60 ->
    (forall M', munch [(obj + 24, obj + 32)] m M' -> wmono asegs m M' -> rw_cells asegs M' (obj + 24) [C8 (Z_to_bv 64 (Zlength ents + 1))] ->
        umapx MI_A 32 (nval32 ASEGS) (lbl LB') M' obj bl' bc' (l1 ++ (p, (key, (0, 0, 0))) :: l2)) ->
    umap_sh m 32 (bl', bc', l1 ++ (p, (key, (0, 0, 0))) :: l2) ->
    (bc' <> 0 -> 0 <= bl' /\ bl' + 8 * bc' <= 2 ^ 47) ->
    (forall q k v, In (q, (k, v)) (l1 ++ (p, (key, (0, 0, 0))) :: l2) -> 0 <= q /\ q + 32 <= 2 ^ 47) ->
    0x6e8000 <= p -> p mod 16 = 0 ->
    addressable m obj 40 -> wr_at asegs m obj 40 ->
    Permutation (l1 ++ (p, (key, (0, 0, 0))) :: l2) ((p, (key, (0, 0, 0))) :: ents) ->
    (rehashed = false -> bl' = bl /\ bc' = bc) ->
    (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc) ->
    as_RHEAP H s LB' m -> Permutation LB' (LB0 ++ LBm') ->
    Permutation (lbl LBm') (umap_blocks 32 bl' bc' (l1 ++ (p, (key, (0, 0, 0))) :: l2)) ->
    lb_own LBm' m ->
    xpres H LB0 S1 (nt_X S1 obj) m0 m ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi -> aceil <= lo -> lo <= S1 ->
    as_AL H s >= as_AL H sk0 - (if rehashed then ICM (8 * bc') else 0) ->
    as_SR H QF (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y17 y18 y19 y21 y22 y25 y27 y28 y29 y31
      errv' LB' LBm' p bl' bc' l1 l2 rehashed j584 j592
      VIS FRZ KR MP WS NS SPL SPH V408 V576 V624 MI ST ERR RA TPV LFO OAL CSZ SZR HU SH BLR NDR BI PAL AD WR PERM CR3 CR4 RH PE PM OWN XP RF AC S0 ACL LOS AL.
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK _]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4).
    assert (GZO : gz m obj 40) by (intros i Hi; eapply sh0_of_addressable; [exact AD | change (8 * (40 / 8)) with 40; lia]).
    assert (OAPP : obj + 40 <= 0x7fff7000 \/ 0x10007fff8000 <= obj).
    { unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA. lia. }
    pose proof NS as (N408 & N576 & N616 & N624 & N648).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 (Z_to_bv 64 SHBASE) y16 y17
                  y18 y19 s4 y21 y22 (Z_to_bv 64 p) wd y25 (Z_to_bv 64 (obj + 24)) y27 y28 y29
                  (rShe (Z_to_bv 64 (obj + 24))) y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 (Zlength ents); wd;
                        Z_to_bv 64 v576; Z_to_bv 64 v624; Z_to_bv 64 v408]).
    assert (HR : regs_ok E (srs sr_id [(9%bv, EVar 32); (23%bv, EVar 33); (15%bv, ELit SHBASE); (24%bv, EVar 36);
                                        (26%bv, EAlu ALU_ADD (EVar 34) (ELit 24));
                                        (30%bv, shEe (EAlu ALU_ADD (EVar 34) (ELit 24)))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; unfold shEe, rShe; evs; rewrite ?w_add by lia; reflexivity] |]).
      apply Forall_nil. }
    assert (HK : know_ok asegs E m
       (kn_fix 20 [E_VAL] (SCR [] [] []) E_END (srs sr_id [(9%bv, EVar 32); (23%bv, EVar 33); (15%bv, ELit SHBASE); (24%bv, EVar 36);
                                                 (26%bv, EAlu ALU_ADD (EVar 34) (ELit 24));
                                                 (30%bv, shEe (EAlu ALU_ADD (EVar 34) (ELit 24)))])
         [ KWord (SA (EVar 34) 24) 8 (EVar 35); KWr (SA (EVar 34) 24) (ELit 8);
           KWord (SA (EVar 32) 576) 8 (EVar 37); KWord (SA (EVar 32) 624) 8 (EVar 38); KWord (SA (EVar 32) 408) 8 (EVar 39);
           KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KRange (EVar 34) 0x6e8000 (2 ^ 47 - 40); KRange (EVar 35) 0 (2 ^ 60) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { kword_cell CSZ 0%nat (C8 (Z_to_bv 64 (Zlength ents))). }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact (LbB_HEmpD.wr_at_subE m obj 40 (obj + 24) 8 WR ltac:(lia) ltac:(lia) ltac:(lia)) | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
      apply Forall_cons. { kword_cell N576 0%nat (C8 (Z_to_bv 64 v576)). }
      apply Forall_cons. { kword_cell N624 0%nat (C8 (Z_to_bv 64 v624)). }
      apply Forall_cons. { kword_cell N408 0%nat (C8 (Z_to_bv 64 v408)). }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_END m (seg_rom asegs) HR HK 40%nat [E_VAL] (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1; try sc_shdj; try sc_dj. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (MU1 : munch [(obj + 24, obj + 32)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo (S1 + 672)) by (subst M1; apply stk_mem_denot; exact ST).
    assert (CSZ1 : rw_cells asegs M1 (obj + 24) [C8 (Z_to_bv 64 (Zlength ents + 1))]).
    { assert (EQv : map (fun v => C8 (edenot E v)) [EAlu ALU_ADD (EVar 35) (ELit 1)] = [C8 (Z_to_bv 64 (Zlength ents + 1))])
        by (cbn [map]; f_equal; f_equal; evs; rewrite w_add by lia; reflexivity).
      rewrite <- EQv. subst M1.
      change [{| e_addr := {| a_base := EVar 34; a_off := 24 |}; e_width := 8; e_val := EAlu ALU_ADD (EVar 35) (ELit 1) |}]
        with (c8log (EVar 34) 24 [EAlu ALU_ADD (EVar 35) (ELit 1)]) in Hlf |- *.
      apply rw_cells_c8log; [exact Hlf | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia |].
      cbn [length Z.of_nat]. exact (LbB_HEmpD.wr_at_subE m obj 40 (obj + 24) 8 WR ltac:(lia) ltac:(lia) ltac:(lia)). }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 9%bv G9. rreg HR' 23%bv G23. rreg HR' 15%bv G15. rreg HR' 24%bv G24.
    rreg HR' 19%bv G19. rreg HR' 26%bv G26. rreg HR' 27%bv G27.
    change (Z_to_bv 64 2147450880) with (Z_to_bv 64 SHBASE) in G15.
    rewrite G9, G23, G15, G24, G19, G26, G27 in HRe.

    destruct (LbB_HEmpD.obj_window_ok H HH LF obj LB' m (obj + 24) (obj + 32) RF LFO ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4).
    destruct (client_frame H HH s LB' LF B [(obj + 24, obj + 32)] m M1 RH RF AC RA MU1 WM1
               (Forall_cons _ _ _ W1 (Forall_nil _)) (Forall_cons _ _ _ W2 (Forall_nil _)) (Forall_cons _ _ _ W3 (Forall_nil _)))
      as (RH1 & RF1 & AC1 & RA1).
    assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact (Forall_cons _ _ _ W4 (Forall_nil _))]).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv']).
    { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
      eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; unfold AFS_SIZE in *; lia]. }
    assert (DSH : forall A n, 0 <= A -> 0 <= n -> A + n <= 2 ^ 47 -> disjoint_from [(obj + 24, obj + 32)] (sh A) (nsh n)).
    { intros A n HA Hn Han. cbn [disjoint_from]. split; [|exact I].
      pose proof (sh_nsh_high A n HA Hn ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN.
      assert (ASHADOW_BASE <= sh A) by (unfold sh; pose proof (Z.div_pos A 8 ltac:(lia) ltac:(lia)); lia). unfold ASHADOW_BASE in *. lia. }
    assert (WS1 : WSLOTS M1 j584 j592).
    { pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4). destruct WS as (W584 & W600 & W632 & W656).
      unfold WSLOTS, nt_wslots. split; [|split; [|split]];
        (eapply rw_cells_transport; [eassumption | exact MU1 | exact WM1 | cbn; unfold AFS_SIZE in *; lia]). }
    assert (NS1 : nt_slots M1 S1 obj v408 v576 v624).
    { pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4). unfold nt_slots.
      repeat match goal with |- _ /\ _ => split end;
        (eapply rw_cells_transport; [eassumption | exact MU1 | exact WM1 | cbn; unfold AFS_SIZE in *; lia]). }
    assert (SH1 : umap_sh M1 32 (bl', bc', l1 ++ (p, (key, (0, 0, 0))) :: l2)).
    { destruct SH as [SHb SHn]. unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c in *. cbn [Datatypes.fst Datatypes.snd] in *.
      split.
      - intros Hbc. destruct (BLR Hbc) as [B0 B1]. pose proof (u_bseq (HU M1 MU1 WM1 CSZ1)) as BSQ.
        pose proof (LbB_HFind.BSEQ_boundA bc' BSQ) as BCR.
        eapply addressable_transport; [exact (SHb Hbc) | exact MU1 | exact WM1 | apply DSH; lia].
      - intros q k v Hin. destruct (NDR q k v Hin) as [Q0 Q1].
        eapply addressable_transport; [exact (SHn q k v Hin) | exact MU1 | exact WM1 | apply DSH; lia]. }
    assert (AD1 : addressable M1 obj 40) by (eapply addressable_transport; [exact AD | exact MU1 | exact WM1 | apply DSH; lia]).
    assert (XP1 : xpres H LB0 S1 (nt_X S1 obj) m0 M1).
    { eapply (xpres_trans H); [exact XP|].
      eapply (xpres_weaken H); [eapply (xpres_of_munch H s LB' S1 (nt_X S1 obj) [(obj + 24, obj + 32)] m m M1 HH RH MU1 WM1) | lia | |].
      - apply Forall_cons; [right; intros a Ha; cbn in Ha |- *; left; lia | apply Forall_nil].
      - intros b Hb. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. left. exact Hb.
      - intros a Ha. exact Ha. }
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (stage_val s msF1 mo1 M1 F fc) with (inserted := true) (rehashed := rehashed) (l1 := l1) (l2 := l2) (v0 := (0, 0, 0)) (bl' := bl') (bc' := bc')
      (LB' := LB') (LBm' := LBm') (p := p);
      [ exact VIS1 | exact FRZ | exact KR1 | eapply (ah_mpres_trans H HH); [exact MP | exact MP1] | exact WS1 | exact NS1
      | exact SPL | exact SPH | exact V408 | exact V576 | exact V624 | exact MI1 | exact ST1 | exact ERR1 | exact RA1 | exact TPV
      | exact (HU M1 MU1 WM1 CSZ1) | exact SH1 | exact AD1
      | exact (wr_at_wmono _ _ _ _ WR WM1)
      | intros X; discriminate X | intros _; exact PERM | exact CR3 | exact CR4
      | exact RH1 | exact PE | exact PM | exact (lb_own_wmono _ _ _ OWN WM1) | exact XP1 | exact RF1 | exact AC1 | exact S01 | exact ACL | exact LOS | exact AL ].
  Qed.
End NtC.

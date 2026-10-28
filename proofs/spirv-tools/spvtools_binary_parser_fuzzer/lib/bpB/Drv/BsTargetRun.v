(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BHoare BFrame BShapeLaws BpecConsts BAgentLib BSymExec2 BSymExec2Sound BSymRun BSymDriveX BMemSplit BSpec BLibTail BRefPrintfLib BRefMemcpyLib BReach BegsEquivM BainEqv BeapCeil BazyRestrict BazySR BainWalk_defs BainSegs BainMem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BArr BStep BLFrame BMState BSysStep BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BInitMem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsDriverLaws BsStack0 BXXRep DvB_FuzzStmt RtB_Iface DvB_CXXAs BRefExitBase BsPrintfFirst BsPrintfBuf BsDrvHeap BsDrvRun BsDrvIO BsDrvFuzz BsDrvMem BsDrvDefs BsTRWalk_defs BsTRSegs.
Import ListNotations.
Import BSymExec2.SX2. Import BSymExec2Sound.SX2S.
Import BPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac in_solve := cbn [In]; repeat (first [ left; reflexivity | right ]).
Ltac in_from H := cbn [In] in H; decompose [or] H; clear H; try contradiction; subst; in_solve.

Lemma ardn_S : forall m (a : word) n bs,
  rdn RSEGS m a (S n) = Some bs ->
  exists b r, bs = b :: r /\ mrd asegs m a = Some b /\ rdn RSEGS m (a + 1)%bv n = Some r.
Proof.
  intros m a n bs HR. change (rdn RSEGS) with (OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.HF.Lib.BLPropExec.rdn asegs) in HR |- *.
  rewrite rdn_unfold in HR. destruct (mrd asegs m a) as [b|]; [|discriminate].
  destruct (OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.HF.Lib.BLPropExec.rdn asegs m (a + 1)%bv n) as [r|]; [|discriminate].
  injection HR as <-. exists b, r. auto.
Qed.

Lemma ardn_bytes_at : forall bs m (a : Z),
  rdn RSEGS m (Z_to_bv 64 a) (length bs) = Some bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at asegs m a bs.
Proof.
  induction bs as [|b bs IH]; intros m a HR Ha Hn.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [length] in HR, Hn. destruct (ardn_S m _ _ _ HR) as (b' & r & E & Hm & Hr). injection E as <- <-.
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn. rewrite Z.add_0_r. rewrite wa_eq. exact Hm.
    + cbn [nth_error]. destruct (Z.eq_dec (a + 1) (2 ^ 64)) as [Heq|Hne].
      { cbn [length] in Hi. lia. }
      assert (IHr := IH m (a + 1)).
      assert (Ea : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)).
      { apply bv_eq. rewrite u_add1 by (rewrite u_small by lia; lia). rewrite !u_small by lia. reflexivity. }
      rewrite Ea in Hr. specialize (IHr Hr ltac:(lia) ltac:(cbn [length] in Hi |- *; lia)).
      destruct IHr as (_ & _ & IH3). rewrite <- (IH3 i) by (cbn [length] in Hi; lia). f_equal. f_equal. lia.
Qed.

Section TR.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.
  Variable FZP : fuzz_params.
  Hypothesis PO : fz_params_ok FZP.

  Hypothesis FZINV : forall m, mem_inv asegs m -> arelro_none m -> ACONST m -> LbB_DStat.dstat m -> fz_inv FZP m.

  Hypothesis FZINV' : forall m, fz_inv FZP m -> LbB_DStat.dstat m.
  Hypothesis FZ : fuzz_stmt H FZP.

  Let rom := seg_rom asegs.

  Section Call.
    Variables (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s0 : as_St H) (LB : list block)
              (msF0 : machine_state) (mo0 : Model) (regs0 : bvmap 5 word) (mem0 : word -> option byte).
    Hypothesis PRE : ATRpre H FZP sp A cap data p s0 LB msF0 mo0 regs0 mem0.

    Let cfg : Z := hdr_cfg data.
    Let N : Z := hdr_payload_len data.
    Let CP : Z := A + 2.
    Let PL : Z := A + 2 + hdr_cfg data + 4.

    Let ds : list byte := firstn (Z.to_nat N) (skipn (Z.to_nat (6 + cfg)) data).
    Let calls : nat := hdr_calls data.

    Let HCLO : aceil + ATR_STACK + 4096 <= bv_unsigned sp.
    Proof. exact (atr_splo _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
    Let SPlo : 0x7fff7f811000 <= bv_unsigned sp.
    Proof. pose proof HCLO as X. acb. unfold ATR_STACK in X. lia. Qed.
    Let SPhi : bv_unsigned sp <= 0x7fffffffff80.
    Proof. pose proof (atr_sphi _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). lia. Qed.
    Let SP16 : bv_unsigned sp mod 16 = 0.
    Proof. exact (atr_sp16 _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
    Let Hcfg : 0 <= cfg < 32768. Proof. exact (hdr_cfg_range data). Qed.
    Let HN : 0 <= N < 2 ^ 26.
    Proof. pose proof (atr_len6 _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). pose proof (atr_lenhi _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). unfold MAX_INPUT in *. subst N. unfold hdr_payload_len. subst cfg. lia. Qed.
    Let Hds : length ds = Z.to_nat N.
    Proof.
      pose proof (atr_len6 _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). subst ds N cfg. unfold hdr_payload_len in *.
      rewrite length_firstn, length_skipn. lia.
    Qed.
    Let Hcalls : (1 <= calls <= 4)%nat. Proof. exact (hdr_calls_range data). Qed.

    Definition atr_region (r : word * Z) : Prop :=
      (bv_unsigned sp - ATR_STACK <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= bv_unsigned sp /\ 0 <= snd r)
      \/ (0x189b00 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x189be8 /\ 0 <= snd r)
      \/ (0x6e6480 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x6e6488 /\ 0 <= snd r)
      \/ (0x6c3690 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x6c3698 /\ 0 <= snd r)
      \/ (0x6e58a8 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x6e59e8 /\ 0 <= snd r).

    Definition still_region (r : word * Z) : Prop :=
      (bv_unsigned sp - ATR_STACK <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= bv_unsigned sp /\ 0 <= snd r)
      \/ (0x189b00 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x189be8 /\ 0 <= snd r)
      \/ (0x6e6480 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x6e6488 /\ 0 <= snd r).

    Definition quiet_region (r : word * Z) : Prop :=
      (bv_unsigned sp - ATR_STACK <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= bv_unsigned sp /\ 0 <= snd r)
      \/ (0x6c3690 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x6c3698 /\ 0 <= snd r)
      \/ (0x6e58a8 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x6e59e8 /\ 0 <= snd r).
    Lemma still_atr : forall r, still_region r -> atr_region r.
    Proof. intros r [X|[X|X]]; [left; exact X | right; left; exact X | right; right; left; exact X]. Qed.
    Lemma quiet_atr : forall r, quiet_region r -> atr_region r.
    Proof. intros r [X|[X|X]]; [left; exact X | right; right; right; left; exact X | right; right; right; right; exact X]. Qed.

    Record atinv (cs : list (Z * nat * Z)) (m : word -> option byte) : Prop := ATI {
      ti_inv   : mem_inv asegs m;
      ti_stk   : stk asegs m (bv_unsigned sp - ATR_STACK) (bv_unsigned sp);
      ti_ac    : ACONST m;
      ti_relro : arelro_none m;
      ti_glb   : aglb_none m;
      ti_cells : cells_ok m cs;
      ti_tid   : exists t, atid_cell m t;
      ti_errno : exists e, rw_cells asegs m AERRNO [C4 e];
      ti_can   : exists can, acanary m can;
      ti_rfs   : as_RFS H [] m;
      ti_sh0   : exists shi, stack0 m (bv_unsigned sp - ATR_STACK) shi /\ 0x800000000000 <= shi;
      ti_above : forall a : word, bv_unsigned sp <= bv_unsigned a -> m a = mem0 a;
      ti_aux   : exists B', as_rauxv_ok H m B' /\ bv_unsigned sp + 128 <= B' < 2 ^ 64;
      ti_addr  : addressable m A cap;
      ti_data  : rdn RSEGS m (Z_to_bv 64 A) (length data) = Some data;
      ti_cb    : exists junk, rw_cells asegs m A [CB (Z.to_nat cap) junk];
      ti_dstat : LbB_DStat.dstat m }.

    Definition TB (b : Z) : Prop := b = 0 \/ b = 1.
    Definition cell_rng (c : Z * nat * Z) : Prop :=
      match c with (a, w, _) =>
        (0x186f40 <= a /\ a + Z.of_nat w <= 0x1899b4) \/ (a = 0x18d9d0 /\ w = 1%nat) \/ (0x6e58a8 <= a /\ a + Z.of_nat w <= 0x6e5aec) \/ (a = 0x6e6060 /\ w = 8%nat)
        \/ (a = 0x6c5828 /\ w = 8%nat) \/ (0x6c3938 <= a /\ a + Z.of_nat w <= 0x6c4558) \/ (0x6c3690 <= a /\ a + Z.of_nat w <= 0x6c3698) end.
    Definition cell_client (c : Z * nat * Z) : Prop :=
      match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x end.
    Lemma adrv_cells_wf : forallb cell_wf_b adrv_cells = true. Proof. vm_compute. reflexivity. Qed.
    Lemma cellsT_wf : forall b, TB b -> forallb cell_wf_b (adrv_cellsT_of b) = true.
    Proof. intros b [-> | ->]; vm_compute; reflexivity. Qed.
    Lemma adrv_cells_range : Forall cell_rng adrv_cells.
    Proof. unfold adrv_cells, aios_cells, cell_rng. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.
    Lemma cellsT_range : forall b, TB b -> Forall cell_rng (adrv_cellsT_of b).
    Proof.
      intros b Hb. unfold adrv_cellsT_of. apply Forall_app. split.
      - unfold adrv_cells_base, cell_rng. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
      - unfold atr_new_cells, cell_rng. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
    Qed.
    Lemma adrv_cells_client : Forall cell_client adrv_cells.
    Proof. unfold adrv_cells, aios_cells, cell_client, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil. Qed.
    Lemma cellsT_client : forall b, TB b -> Forall cell_client (adrv_cellsT_of b).
    Proof.
      intros b Hb. unfold adrv_cellsT_of. apply Forall_app. split.
      - unfold adrv_cells_base, cell_client, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil.
      - unfold atr_new_cells, cell_client, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil.
    Qed.
    Lemma astdout0_wf : forallb cell_wf_b astdout0 = true. Proof. vm_compute. reflexivity. Qed.
    Lemma TB0 : TB 0. Proof. left. reflexivity. Qed.
    Lemma TB1 : TB 1. Proof. right. reflexivity. Qed.

    Lemma blkA : ablock_range H A cap.
    Proof. exact (ah_blocks H HH _ _ _ _ (atr_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) (atr_blk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE)). Qed.

    Lemma atinv_frame : forall cs cs' m m' rs,
      atinv cs m -> frame_mod m m' rs -> (forall r, In r rs -> atr_region r) -> cells_ok m' cs' -> atinv cs' m'.
    Proof.
      intros cs cs' m m' rs [INV STK AC RELRO GLB CELLS [t TID] [e ERR] [can [CAN CAN64]] RFS [shi [SH0 Hshi]] ABOVE [B' [AUX HB']] ADDR DATA [junk JCB] DST] FM RS CELLS'.
      pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. acb. unfold ATR_STACK in HCL.
      pose proof FM as [Hout Hg]. unfold atr_region, ATR_STACK in RS.
      pose proof (frame_mod_munch _ _ _ FM) as MU. pose proof (aframe_mod_wmono _ _ _ FM) as WM.
      pose proof blkA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
      assert (IVS : forall iv, In iv (ivls rs) -> exists r, In r rs /\ iv = (bv_unsigned (fst r), bv_unsigned (fst r) + snd r)).
      { intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr). eauto. }
      split.
      - eapply amem_inv_frame; [exact INV | exact FM |]. apply Forall_forall. intros r Hr. pose proof (u64_range (fst r)). destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - apply (astk_grows m m'); [exact STK | unfold AIMG_TOP in *; lia | lia | exact Hg].
      - eapply ACONST_frame; [exact AC | exact MU | exact WM |].
        apply Forall_forall. intros iv Hiv. destruct (IVS iv Hiv) as (r & Hr & ->).
        destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; [apply aconst_ok_hi; unfold AHI_LO; lia | | | |];
          apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
            AF_DCO_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP in *;
            rewrite ?ASHADOW_BASE_val; cbn [fst snd]; lia.
      - refine (arange_none_frame m m' rs _ _ RELRO FM _ _ _); [| lia | lia]. intros r Hr. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - destruct GLB as [G1 G2]. split.
        + refine (arange_none_frame m m' rs _ _ G1 FM _ _ _); [| lia | lia]. intros r Hr. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
        + refine (arange_none_frame m m' rs _ _ G2 FM _ _ _); [| lia | lia]. intros r Hr. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - exact CELLS'.
      - exists t. destruct TID as [TID Ht]. split; [|exact Ht]. eapply ardn_frame; [exact FM | exact TID | lia | cbn; lia |].
        intros r Hr. cbn. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - exists e. eapply arw_cells_frame; [exact ERR | exact FM |]. intros r Hr. cbn. unfold AERRNO, ATP. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - exists can. split; [|exact CAN64]. eapply ardn_frame; [exact FM | exact CAN | lia | cbn; lia |].
        intros r Hr. cbn. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - pose proof (ah_RFS_range H HH _ _ RFS) as [(F1 & F2 & F3 & F4) _].
        eapply (ah_RFS_frame H HH); [exact RFS | exact MU | exact WM |].
        apply Forall_forall. intros iv Hiv. destruct (IVS iv Hiv) as (r & Hr & ->). unfold afs_write_ok. left. cbn [fst snd].
        unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - exists shi. split; [|exact Hshi]. eapply stack0_transport; [exact SH0 | exact MU | exact WM |].
        apply Forall_forall. intros iv Hiv. destruct (IVS iv Hiv) as (r & Hr & ->). unfold stack0_ok. cbn [fst snd].
        assert (SHT : 0x800d5000 <= sh aceil).
        { unfold sh. rewrite ASHADOW_BASE_val. assert (A8 : 0 < 8) by lia. assert (ACL : 0x7fff7f800000 <= aceil) by lia.
          pose proof (Z.div_le_mono _ _ _ A8 ACL) as DM.
          change (0x7fff7f800000 / 8) with 0xfffeff00000 in DM. lia. }
        unfold AHI_LO. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - intros a Ha. rewrite <- (ABOVE a Ha). apply Hout. apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - exists B'. split; [|exact HB']. eapply (ah_rauxv_frame H HH LB); [exact AUX | exact MU | exact WM |].
        apply Forall_forall. intros iv Hiv. destruct (IVS iv Hiv) as (r & Hr & ->). unfold aclient_write_ok, aimg_client_w. cbn [fst snd].
        unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ALIBC_PGSZ, ATP in *. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - eapply addressable_transport; [exact ADDR | exact MU | exact WM |].
        assert (SHR : (0x800d5000 <= sh A /\ sh A + nsh cap <= 0x8fff6e00) \/ (0x2008fff7000 <= sh A /\ sh A + nsh cap <= sh aceil /\ sh aceil < AHI_LO)).
        { destruct BA7 as [P|P]; [left; exact (sh_aapp_lo_range A cap P BA3) | right; exact (sh_aapp_hi_range A cap P BA3)]. }
        assert (SHT : sh aceil <= 0x10007fff7000).
        { unfold sh. rewrite ASHADOW_BASE_val. assert (A8 : 0 < 8) by lia. assert (ACL : aceil <= 0x7fffff800000) by lia.
          pose proof (Z.div_le_mono _ _ _ A8 ACL) as DM. change (0x7fffff800000 / 8) with 0xffffff00000 in DM. lia. }
        clear - RS SHR SHT SPlo. induction rs as [|[r k] rs IH]; [exact I|]. cbn. split.
        + pose proof (RS (r, k) (or_introl eq_refl)) as X. cbn [fst snd] in X. unfold AHI_LO in SHR. destruct X as [X|[X|[X|[X|X]]]]; lia.
        + apply IH. intros r' Hr'. apply RS. right. exact Hr'.
      - eapply ardn_frame; [exact FM | exact DATA | lia | pose proof (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE); acb; lia |].
        intros r Hr. pose proof (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). unfold AIMG_TOP in *. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - exists junk. eapply arw_cells_frame; [exact JCB | exact FM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        intros r Hr. unfold AIMG_TOP in *. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
      - eapply adstat_eq; [exact DST|]. intros x Hx. unfold adstat_win in Hx. apply Hout. apply outside_of_disjoint.
        intros r Hr. rewrite wa_eq, u_small by lia. destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; lia.
    Qed.

    Lemma atinv_frame_still : forall b m m' rs,
      TB b -> atinv (adrv_cellsT_of b) m -> frame_mod m m' rs -> (forall r, In r rs -> still_region r) -> atinv (adrv_cellsT_of b) m'.
    Proof.
      intros b m m' rs Hb TI FM RS. pose proof SPlo. pose proof HCLO as HCL. acb. unfold ATR_STACK in HCL.
      eapply atinv_frame; [exact TI | exact FM | intros r Hr; apply still_atr; apply RS; exact Hr |].
      eapply acells_ok_frame; [apply cellsT_wf; exact Hb | exact (ti_cells _ _ TI) | exact FM |].
      eapply Forall_impl; [| apply cellsT_range; exact Hb]. intros [[a w] v] Ra r Hr. cbn [fst snd]. unfold cell_rng in Ra.
      unfold still_region, ATR_STACK in RS. destruct (RS r Hr) as [X|[X|X]]; first [clear - X HCL Ra; lia | lia].
    Qed.

    Lemma cells_ok_In : forall m cs c, cells_ok m cs -> In c cs -> cell_ok m c.
    Proof. intros m cs c Hc HIn. unfold cells_ok in Hc. rewrite Forall_forall in Hc. apply Hc. exact HIn. Qed.
    Definition cell_eqb (c d : Z * nat * Z) : bool :=
      match c, d with (a, w, v), (a', w', v') => ((a =? a') && Nat.eqb w w' && (v =? v'))%bool end.
    Lemma cell_eqb_eq : forall c d, cell_eqb c d = true -> c = d.
    Proof.
      intros [[a w] v] [[a' w'] v'] E. cbn in E. apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
      apply Z.eqb_eq in E1. apply Nat.eqb_eq in E2. apply Z.eqb_eq in E3. subst. reflexivity.
    Qed.
    Lemma cells_ok_sub : forall m cs cs2, cells_ok m cs -> forallb (fun d => existsb (cell_eqb d) cs) cs2 = true -> cells_ok m cs2.
    Proof.
      intros m cs cs2 Hc Hs. unfold cells_ok in *. rewrite Forall_forall in Hc. apply Forall_forall. intros d Hd.
      rewrite forallb_forall in Hs. pose proof (Hs d Hd) as X. apply existsb_exists in X as (c & Hcin & E).
      apply cell_eqb_eq in E. subst d. apply Hc. exact Hcin.
    Qed.
    Ltac in_cells := unfold adrv_cells, adrv_cellsT_of, adrv_cells_base, atr_new_cells, aios_cells; cbn [In app]; repeat (first [left; reflexivity | right]).

    Lemma cells_T0 : forall m m',
      cells_ok m adrv_cells -> frame_mod m m' (regT0_w sp) -> tcells m' atx_cells1 -> cells_ok m' (adrv_cellsT_of 0).
    Proof.
      intros m m' CELLS FM TC. pose proof SPlo. pose proof SPhi.
      assert (BASE : cells_ok m' adrv_cells_base).
      { assert (CB0 : cells_ok m adrv_cells_base).
        { apply (cells_ok_sub m adrv_cells); [exact CELLS | vm_compute; reflexivity]. }
        eapply acells_ok_frame; [vm_compute; reflexivity | exact CB0 | exact FM |].
        unfold adrv_cells_base. repeat (apply Forall_cons; [intros r Hr; unfold regT0_w, AINIT, AX_SLOT, AX_F3, AX_A3 in Hr; cbn [In] in Hr;
          destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by lia; lia |]).
        apply Forall_nil. }
      assert (AEF : cell_ok m' (0x6c3694, 1%nat, 0)).
      { pose proof (cells_ok_In m adrv_cells (0x6c3694, 1%nat, 0) CELLS ltac:(in_cells)) as C. unfold cell_ok in *.
        eapply ardn_frame; [exact FM | exact C | lia | cbn; lia |].
        intros r Hr. unfold regT0_w, AINIT, AX_SLOT, AX_F3, AX_A3 in Hr. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by lia; lia. }
      unfold adrv_cellsT_of. unfold cells_ok. apply Forall_app. split; [exact BASE|].
      unfold tcells, atx_cells1, AX_SLOT, AX_F3, AX_A3, AINIT, ATEXIT_CALL_A, AEF_GUARD_A in TC.
      repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
      unfold atr_new_cells. repeat apply Forall_cons; try apply Forall_nil; unfold cell_ok; try assumption.
    Qed.

    Lemma cells_flag : forall b b' m m',
      TB b -> cells_ok m (adrv_cellsT_of b) -> frame_mod m m' regTf_w -> tcell m' (AAEF, 1%nat, b') -> cells_ok m' (adrv_cellsT_of b').
    Proof.
      intros b b' m m' Hb CELLS FM TC. unfold adrv_cellsT_of, cells_ok in *. apply Forall_app in CELLS as [CB CN]. apply Forall_app. split.
      - eapply acells_ok_frame; [vm_compute; reflexivity | exact CB | exact FM |].
        unfold adrv_cells_base. repeat (apply Forall_cons; [intros r Hr; unfold regTf_w, AAEF in Hr; cbn [In] in Hr;
          destruct Hr as [<-|[]]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by lia; lia |]).
        apply Forall_nil.
      - unfold atr_new_cells in *.
        repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
        repeat apply Forall_cons; try apply Forall_nil;
          first [ exact TC
                | eapply ardn_frame; [exact FM | eassumption | lia | cbn; lia |];
                  intros r Hr; unfold regTf_w, AAEF in Hr; cbn [In] in Hr; destruct Hr as [<-|[]]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by lia; lia ].
    Qed.

    Lemma rdn_apres : forall LB1 SP m m' (a : Z) n bs,
      apres H LB1 SP m m' -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
      (forall x, a <= x < a + Z.of_nat n -> aclient_addr H LB1 SP x) ->
      rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
    Proof.
      intros LB1 SP m m' a n bs HP HD Ha Hn HC.
      destruct n as [|n']; [cbn in *; exact HD|].
      rewrite (rdn_ext RSEGS (S n') m' m); [exact HD | rewrite u_small by lia; lia |]. intros x Hx. rewrite u_small in Hx by lia.
      rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP _ (u64_range x) (HC _ Hx))).
    Qed.

    Lemma cells_ok_apres : forall LB1 SP m m' cs,
      forallb cell_wf_b cs = true -> cells_ok m cs -> apres H LB1 SP m m' -> Forall cell_client cs -> cells_ok m' cs.
    Proof.
      intros LB1 SP m m' cs Hwf Hc HP Hd. unfold cells_ok in *.
      induction cs as [|[[a w] v] cs IH]; [constructor|].
      cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
      inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
      unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
      repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
      unfold cell_ok, cell_client in *. eapply rdn_apres; [exact HP | exact Hok | lia | lia |]. intros y Hy. right; left. apply Hx. exact Hy.
    Qed.

    Lemma astdout0_client : Forall cell_client astdout0.
    Proof. unfold astdout0, cell_client, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil. Qed.

    Definition cell_td (c : Z * nat * Z) : Prop :=
      match c with (a, w, v) => (a + Z.of_nat w <= RtB_Td.ATDLOC \/ RtB_Td.ATDLOC + 8 <= a) \/ (a, w, v) = (0x6c5828, 8%nat, 0x6e5b20) end.
    Ltac cell_td_list := repeat (apply Forall_cons; [first [left; unfold RtB_Td.ATDLOC; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | right; reflexivity]|]); apply Forall_nil.
    Lemma cellsT_td : forall b, TB b -> Forall cell_td (adrv_cellsT_of b).
    Proof.
      intros b Hb. unfold adrv_cellsT_of. apply Forall_app. split.
      - unfold adrv_cells_base, cell_td. cell_td_list.
      - unfold atr_new_cells, cell_td. cell_td_list.
    Qed.
    Lemma astdout0_td : Forall cell_td astdout0.
    Proof. unfold astdout0, cell_td. cell_td_list. Qed.
    Lemma cell_td_of_dstat : forall m, LbB_DStat.dstat m -> cell_ok m (0x6c5828, 8%nat, 0x6e5b20).
    Proof.
      intros m D. unfold cell_ok.
      assert (BA : bytes_at asegs m 0x6c5828 (map (Z_to_bv 8) [0x20; 0x5b; 0x6e; 0; 0; 0; 0; 0])).
      { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn [length map] in Hi.
        do 8 (destruct i as [|i]; [cbn [nth_error map];
               match goal with |- mrd _ _ (wa ?e) = Some (Z_to_bv 8 ?bb) => let v := eval vm_compute in e in change e with v; apply (D v bb); [lia | vm_compute; reflexivity] end|]).
        lia. }
      pose proof (bytes_at_rdn asegs m 0x6c5828 _ 0 8 BA ltac:(cbn; lia)) as R.
      change (0x6c5828 + Z.of_nat 0) with 0x6c5828 in R. refine (eq_trans R _). f_equal. apply LbB_DStat.byte_list_eqZ. vm_compute. reflexivity.
    Qed.

    Lemma atinv_apres : forall b m m' LB1 B2 e',
      TB b -> atinv (adrv_cellsT_of b) m -> apres H LB1 (bv_unsigned sp - 80) m m' -> In (p, A, cap) LB1 ->
      mem_inv asegs m' -> stk asegs m' (bv_unsigned sp - ATR_STACK) (bv_unsigned sp - 80) -> ACONST m' ->
      as_rauxv_ok H m' B2 -> bv_unsigned sp + 128 <= B2 < 2 ^ 64 ->
      rw_cells asegs m' AERRNO [C4 e'] -> as_RFS H [] m' ->
      (forall shi, stack0 m (bv_unsigned sp - ATR_STACK) shi -> stack0 m' (bv_unsigned sp - ATR_STACK) shi) ->
      atinv (adrv_cellsT_of b) m'.
    Proof.
      intros b m m' LB1 B2 e' Hb [INV STK AC RELRO GLB CELLS [t [TID Ht]] ERR [can [CAN CAN64]] RFS [shi [SH0 Hshi]] ABOVE AUX ADDR DATA [junk JCB] DST]
             HP HIn INV' STK' AC' AUX' HB2 ERR' RFS' SH'.
      pose proof SPlo. pose proof SPhi.
      assert (AG : forall x : word, bv_unsigned sp - 80 <= bv_unsigned x -> m' x = m x).
      { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP _ (u64_range x) ltac:(left; lia))). }
      split; try assumption.
      - destruct STK as (S1 & S2 & S3). destruct STK' as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
        intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp - 80)) as [L|L]; [apply S3'; lia|].
        assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by lia; lia).
        unfold wview, mrd. rewrite E. apply S3. lia.
      - intros i Hi. rewrite <- (RELRO i Hi). rewrite <- wa_eq.
        assert (Hi64 : 0 <= i < 2 ^ 64) by lia.
        exact (proj1 (HP i Hi64 ltac:(right; left; unfold aimg_client; lia))).
      - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq;
          (assert (Hi64 : 0 <= i < 2 ^ 64) by lia); exact (proj1 (HP i Hi64 ltac:(right; left; unfold aimg_client; lia))).
      - eapply cells_ok_apres; [apply cellsT_wf; exact Hb | exact CELLS | exact HP | apply cellsT_client; exact Hb].
      - exists t. split; [|exact Ht]. eapply rdn_apres; [exact HP | exact TID | lia | cbn; lia |]. intros x Hx. right; left. unfold aimg_client. cbn in Hx. lia.
      - exists e'. exact ERR'.
      - exists can. split; [|exact CAN64]. eapply rdn_apres; [exact HP | exact CAN | lia | cbn; lia |]. intros x Hx. right; left. unfold aimg_client. cbn in Hx. lia.
      - exists shi. split; [apply SH'; exact SH0 | exact Hshi].
      - intros a Ha. rewrite <- (ABOVE a Ha). apply AG. lia.
      - exists B2. split; assumption.
      - eapply apres_addressable; [exact HP | exact ADDR | exact HIn].
      - pose proof (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as HC. pose proof blkA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
        eapply rdn_apres; [exact HP | exact DATA | lia | acb; lia |].
        intros x Hx. right; right; left. exists (p, A, cap). split; [exact HIn | cbn; lia].
      - exists junk. eapply apres_rw_cells; [exact HP | exact JCB |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (pose proof blkA as (_ & _ & B3 & _); exact B3).
        eapply aclient_range_block; [exact HIn | lia | lia].
      - eapply adstat_eq; [exact DST|]. intros x Hx. unfold adstat_win in Hx.
        assert (Hx64 : 0 <= x < 2 ^ 64) by lia. exact (proj1 (HP x Hx64 ltac:(right; left; unfold aimg_client; lia))).
    Qed.

    Lemma atframe_agree : forall m m' x0 x1 x2 x3 x4 x5 x6 x7,
      tframe sp m x0 x1 x2 x3 x4 x5 x6 x7 -> (forall x : word, bv_unsigned sp - 80 <= bv_unsigned x < bv_unsigned sp -> m' x = m x) ->
      tframe sp m' x0 x1 x2 x3 x4 x5 x6 x7.
    Proof.
      intros m m' x0 x1 x2 x3 x4 x5 x6 x7 TF AG. pose proof SPlo. pose proof SPhi. unfold tframe in *.
      repeat match goal with |- _ /\ _ => split end;
        lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
          rewrite (rdn_ext RSEGS 8 m' m); [tauto | unorm; lia | intros x Hx; apply AG; revert Hx; unorm; intros Hx; lia] end.
    Qed.

    Definition sto (j : nat) (m : word -> option byte) : Prop :=
      match j with O => cells_ok m astdout0 | S k => astdout_after m k end.

    Lemma astdout0_range : Forall (fun c : Z * nat * Z => match c with (a, w, _) => 0x189b00 <= a /\ a + Z.of_nat w <= 0x189b94 end) astdout0.
    Proof. unfold astdout0. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.

    Lemma sto_frame : forall j m m' rs, (j <= 4)%nat -> sto j m -> frame_mod m m' rs -> (forall r, In r rs -> quiet_region r) -> sto j m'.
    Proof.
      intros j m m' rs Hj ST FM RS. pose proof SPlo. unfold quiet_region, ATR_STACK in RS. destruct j as [|k]; cbn [sto] in *.
      - eapply acells_ok_frame; [apply astdout0_wf | exact ST | exact FM |].
        eapply Forall_impl; [| apply astdout0_range]. intros [[a w] v] RR r Hr. cbn [fst snd]. destruct (RS r Hr) as [X|[X|X]]; lia.
      - destruct ST as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 LBF].
        assert (T : forall (a : Z) (n : nat) bs, 0x189b00 <= a -> a + Z.of_nat n <= 0x6e6880 -> (a + Z.of_nat n <= 0x189bd0 \/ 0x6e6480 <= a) ->
                  rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Ha Hn Hor HD. eapply ardn_frame; [exact FM | exact HD | lia | lia |]. intros r Hr. destruct (RS r Hr) as [X|[X|X]]; lia. }
        split; (eapply T; [ | | | eassumption]); cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]; lia.
    Qed.

    Lemma sto_apres : forall j m m' LB1, (j <= 4)%nat -> sto j m -> apres H LB1 (bv_unsigned sp - 80) m m' -> sto j m'.
    Proof.
      intros j m m' LB1 Hj ST HP. pose proof SPlo. destruct j as [|k]; cbn [sto] in *.
      - eapply cells_ok_apres; [apply astdout0_wf | exact ST | exact HP | apply astdout0_client].
      - destruct ST as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 LBF].
        split; (eapply rdn_apres; [exact HP | eassumption | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]; lia |]);
          intros x Hx; right; left; unfold aimg_client, ATLS_PRIV_LO, ATP; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul] in Hx; lia.
    Qed.

    Lemma atinv_stk128 : forall cs m, atinv cs m -> stk_ok RSEGS m sp 128.
    Proof. intros cs m TI. pose proof SPlo. pose proof SPhi. eapply astk_stk_ok; [exact (ti_stk _ _ TI) | unfold ATR_STACK; lia | lia | lia | lia]. Qed.
    Lemma atinv_stklo : forall cs m, atinv cs m -> stk asegs m (bv_unsigned sp - ATR_STACK) (bv_unsigned sp - 80).
    Proof. intros cs m TI. destruct (ti_stk _ _ TI) as (S1 & S2 & S3). split; [exact S1|]. split; [lia|]. intros a Ha. apply S3. lia. Qed.
    Lemma atinv_ro : forall cs m, atinv cs m -> aro_none m.
    Proof. intros cs m TI. exact (amem_inv_ro_none m (ti_inv _ _ TI)). Qed.
    Lemma atinv_latch : forall cs m, atinv cs m -> latch_ok m.
    Proof.

      intros cs m TI a n Ha Hn. apply store_ok_data. unfold AINIT in *. rewrite !u_small in * by lia. lia.
    Qed.
    Lemma atinv_atx : forall cs m, atinv cs m -> atx_ok m.
    Proof.
      intros cs m TI a n Ha Hn. apply store_ok_data. unfold AX_FIN in *. rewrite !u_small in * by lia. lia.
    Qed.

    Lemma fuzz_cost_nonneg : forall n, 0 <= n -> 0 <= fz_cost FZP n.
    Proof.
      intros n Hn. exact (proj1 PO n Hn).
    Qed.

    Definition xfar (XS : list (Z * Z)) : Prop := Forall (fun iv : Z * Z => AIMG_TOP <= fst iv /\ snd iv <= aceil) XS.

    Lemma scratch_iv : forall m iv, as_RFS H [] m -> fs_scratch H [] iv -> AIMG_TOP <= fst iv /\ snd iv <= aceil.
    Proof.
      intros m iv RFS SC. pose proof (ah_RFS_range H HH _ _ RFS) as [(F1 & F2 & F3 & F4) _]. acb.
      destruct SC as [-> | (k & ff & fp & FF & E)]; [cbn; unfold AFS_FLAGS, AFS_SIZE in *; lia|].
      pose proof (fresh_frame_facts H _ _ _ _ FF) as (Kk & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)) as FSZP. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
      destruct E as [-> | [-> | ->]]; cbn [fst snd]; [lia | lia |].
      rewrite (fshn_nsh k) by lia.
      pose proof (sh_nsh_high ff (fsz k) ltac:(unfold AIMG_TOP in *; lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SH.
      pose proof (sh_mono AIMG_TOP ff ltac:(lia)) as SM.
      unfold sh, AIMG_TOP, AHI_LO in *. rewrite ASHADOW_BASE_val in *. lia.
    Qed.
    Lemma scratch_far : forall m XS, as_RFS H [] m -> Forall (fs_scratch H []) XS -> xfar XS.
    Proof. intros m XS RFS F. eapply Forall_impl; [| exact F]. intros iv Hiv. eapply scratch_iv; [exact RFS | exact Hiv]. Qed.

    Lemma not_rin_far : forall XS a, xfar XS -> (a < AIMG_TOP \/ aceil <= a) -> ~ rin_ivs XS a.
    Proof.
      intros XS a F Ha. induction XS as [|iv XS IH]; cbn; [tauto|].
      pose proof (Forall_inv F) as F1. cbn in F1. pose proof (Forall_inv_tail F) as F2. intros [R|R]; [lia | exact (IH F2 R)].
    Qed.

    Lemma not_rin_far_td : forall XS a, xfar XS -> (a < AIMG_TOP \/ aceil <= a) -> ~ (RtB_Td.ATDLOC <= a < RtB_Td.ATDLOC + 8) ->
      ~ rin_ivs ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) a.
    Proof. intros XS a F Ha Htd. cbn [rin_ivs fst snd]. intros [R|R]; [exact (Htd R) | exact (not_rin_far XS a F Ha R)]. Qed.
    Lemma not_rin_of_Forall : forall XS a, Forall (fun iv : Z * Z => a < fst iv \/ snd iv <= a) XS -> ~ rin_ivs XS a.
    Proof.
      intros XS a F. induction XS as [|iv XS IH]; cbn; [tauto|].
      pose proof (Forall_inv F) as F1. cbn in F1. pose proof (Forall_inv_tail F) as F2. intros [R|R]; [lia | exact (IH F2 R)].
    Qed.

    Lemma rdn_xpres : forall LB1 SP XS m m' (a : Z) n bs,
      xpres H LB1 SP XS m m' -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
      (forall x, a <= x < a + Z.of_nat n -> xclient H LB1 SP XS x) ->
      rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
    Proof.
      intros LB1 SP XS m m' a n bs HP HD Ha Hn HC.
      destruct n as [|n']; [cbn in *; exact HD|].
      rewrite (rdn_ext RSEGS (S n') m' m); [exact HD | rewrite u_small by lia; lia |]. intros x Hx. rewrite u_small in Hx by lia.
      rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP _ (u64_range x) (HC _ Hx))).
    Qed.

    Lemma cells_ok_xpres_td : forall LB1 SP XS m m' cs,
      forallb cell_wf_b cs = true -> cells_ok m cs -> xpres H LB1 SP ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) m m' -> xfar XS ->
      Forall cell_client cs -> Forall cell_td cs -> LbB_DStat.dstat m' -> cells_ok m' cs.
    Proof.
      intros LB1 SP XS m m' cs Hwf Hc HP HF Hd Ht DS'. unfold cells_ok in *.
      induction cs as [|[[a w] v] cs IH]; [constructor|].
      cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
      inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. inversion Ht as [|x' l' Hx' Hl']; subst.
      constructor; [|apply IH; assumption].
      destruct Hx' as [TDF|E]; [| injection E as -> -> ->; exact (cell_td_of_dstat m' DS')].
      unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
      repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
      unfold cell_ok, cell_client in *. eapply rdn_xpres; [exact HP | exact Hok | lia | lia |]. intros y Hy.
      pose proof (Hx y Hy) as CY. split; [right; left; exact CY|]. apply not_rin_far_td; [exact HF | left; unfold aimg_client, AIMG_TOP in *; lia | lia].
    Qed.

    Lemma blk_scratch : forall sx LB1 m0 m1 XS q Bk n,
      as_RHEAP H sx LB1 m0 -> In (q, Bk, n) LB1 -> as_RFS H [] m1 -> Forall (fs_scratch H []) XS ->
      Forall (fun iv : Z * Z => Bk + n <= fst iv \/ snd iv <= Bk) XS
      /\ Forall (fun iv : Z * Z => sh Bk + nsh n <= fst iv \/ snd iv <= sh Bk) XS.
    Proof.
      intros sx LB1 m0 m1 XS q Bk n RH HIn RFS F.
      pose proof (ah_blocks H HH _ _ _ _ RH HIn) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *. acb.
      pose proof (fsobj_block H HH sx LB1 m0 [] q Bk n RH HIn) as OB.
      split; (eapply Forall_impl; [| exact F]); intros iv Hiv.
      - eapply (fsobj_scratch H HH); [exact RFS | exact OB | lia | lia | unfold AAPP_HI; lia | exact B7 | exact Hiv].
      - eapply (fsobj_scratch_sh H HH); [exact RFS | exact OB | lia | lia | unfold AAPP_HI; lia | exact Hiv].
    Qed.

    Lemma atinv_xpres : forall b m m' LB1 XS sx m1 B2 e',
      TB b -> atinv (adrv_cellsT_of b) m -> xpres H LB1 (bv_unsigned sp - 80) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) m m' -> Forall (fs_scratch H []) XS -> as_RFS H [] m1 ->
      as_RHEAP H sx LB1 m -> In (p, A, cap) LB1 ->
      mem_inv asegs m' -> stk asegs m' (bv_unsigned sp - ATR_STACK) (bv_unsigned sp - 80) -> ACONST m' ->
      as_rauxv_ok H m' B2 -> bv_unsigned sp + 128 <= B2 < 2 ^ 64 ->
      rw_cells asegs m' AERRNO [C4 e'] -> as_RFS H [] m' ->
      (exists shi, stack0 m' (bv_unsigned sp - ATR_STACK) shi /\ 0x800000000000 <= shi) ->
      LbB_DStat.dstat m' ->
      atinv (adrv_cellsT_of b) m'.
    Proof.
      intros b m m' LB1 XS sx m1 B2 e' Hb [INV STK AC RELRO GLB CELLS [t [TID Ht]] ERR [can [CAN CAN64]] RFS SH0 ABOVE AUX ADDR DATA [junk JCB] DST]
             HP HSC RFS1 RH HIn INV' STK' AC' AUX' HB2 ERR' RFS' SH' DS'.
      pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb.
      pose proof (scratch_far m1 XS RFS1 HSC) as FAR.
      pose proof (blk_scratch sx LB1 m m1 XS p A cap RH HIn RFS1 HSC) as [BF BS].
      assert (AG : forall x : word, bv_unsigned sp - 80 <= bv_unsigned x -> m' x = m x).
      { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq.
        refine (proj1 (HP _ (u64_range x) _)). split; [left; lia|]. apply not_rin_far_td; [exact FAR | right; lia | unfold RtB_Td.ATDLOC; lia]. }
      assert (IMG : forall x, aimg_client x -> 0 <= x < 2 ^ 64 -> ~ (RtB_Td.ATDLOC <= x < RtB_Td.ATDLOC + 8) -> m' (wa x) = m (wa x)).
      { intros x Hx Hx64 Htd. refine (proj1 (HP x Hx64 _)). split; [right; left; exact Hx|]. apply not_rin_far_td; [exact FAR | left | exact Htd].
        unfold aimg_client, AIMG_TOP in *. lia. }
      split; try assumption.
      - destruct STK as (S1 & S2 & S3). destruct STK' as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
        intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp - 80)) as [L|L]; [apply S3'; lia|].
        assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by lia; lia).
        unfold wview, mrd. rewrite E. apply S3. lia.
      - intros i Hi. rewrite <- (RELRO i Hi). rewrite <- wa_eq. apply IMG; [unfold aimg_client; lia | lia | unfold RtB_Td.ATDLOC; lia].
      - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq;
          apply IMG; first [lia | unfold aimg_client; lia | unfold RtB_Td.ATDLOC; lia].
      - eapply cells_ok_xpres_td; [apply cellsT_wf; exact Hb | exact CELLS | exact HP | exact FAR | apply cellsT_client; exact Hb | apply cellsT_td; exact Hb | exact DS'].
      - exists t. split; [|exact Ht]. eapply rdn_xpres; [exact HP | exact TID | lia | cbn; lia |]. intros x Hx. cbn in Hx.
        split; [right; left; unfold aimg_client; lia|]. apply not_rin_far_td; [exact FAR | left; unfold AIMG_TOP; lia | unfold RtB_Td.ATDLOC; lia].
      - exists e'. exact ERR'.
      - exists can. split; [|exact CAN64]. eapply rdn_xpres; [exact HP | exact CAN | lia | cbn; lia |]. intros x Hx. cbn in Hx.
        split; [right; left; unfold aimg_client; lia|]. apply not_rin_far_td; [exact FAR | left; unfold AIMG_TOP; lia | unfold RtB_Td.ATDLOC; lia].
      - intros a Ha. rewrite <- (ABOVE a Ha). apply AG. lia.
      - exists B2. split; assumption.
      - eapply (xpres_addressable H); [exact HP | exact ADDR |]. split; [eapply aclient_range_block_sh; exact HIn |].
        apply Forall_cons; [| exact BS]. cbn [fst snd]. right. pose proof blkA as (BA1' & _). unfold sh. rewrite ASHADOW_BASE_val. unfold RtB_Td.ATDLOC. clear - BA1'. Z.div_mod_to_equations. lia.
      - pose proof (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as HC. pose proof blkA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
        eapply rdn_xpres; [exact HP | exact DATA | lia | lia |].
        intros x Hx. split.
        + right; right; left. exists (p, A, cap). split; [exact HIn | cbn; lia].
        + apply not_rin_of_Forall. apply Forall_cons; [cbn [fst snd]; right; unfold RtB_Td.ATDLOC, AIMG_TOP in *; lia|]. eapply Forall_impl; [| exact BF]. cbn. intros iv Hiv. lia.
      - exists junk. eapply (xpres_rw_cells H); [exact HP | exact JCB |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (pose proof blkA as (_ & _ & B3 & _); exact B3).
        split; [eapply aclient_range_block; [exact HIn | lia | lia] |].
        apply Forall_cons; [| exact BF]. cbn [fst snd]. right. pose proof blkA as (_ & _ & _ & BA4' & _). unfold RtB_Td.ATDLOC, AIMG_TOP in *. lia.

    Qed.

    Lemma sto_xpres : forall j m m' LB1 XS m1, (j <= 4)%nat -> sto j m -> xpres H LB1 (bv_unsigned sp - 80) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) m m' ->
      Forall (fs_scratch H []) XS -> as_RFS H [] m1 -> LbB_DStat.dstat m' -> sto j m'.
    Proof.
      intros j m m' LB1 XS m1 Hj ST HP HSC RFS1 DS'. pose proof SPlo. pose proof (scratch_far m1 XS RFS1 HSC) as FAR.
      destruct j as [|k]; cbn [sto] in *.
      - eapply cells_ok_xpres_td; [apply astdout0_wf | exact ST | exact HP | exact FAR | apply astdout0_client | apply astdout0_td | exact DS'].
      - destruct ST as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 LBF].
        split; (eapply rdn_xpres; [exact HP | eassumption | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]; lia |]);
          intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul] in Hx;
          (split; [right; left; unfold aimg_client, ATLS_PRIV_LO, ATP; lia | apply not_rin_far_td; [exact FAR | left; unfold AIMG_TOP; lia | unfold RtB_Td.ATDLOC; lia]]).
    Qed.

    Lemma stack0_qsh0 : forall m lo hi (sp' : Z),
      stack0 m lo hi -> lo + 4104 <= sp' -> sp' <= hi ->
      forall a, ASHADOW_BASE + (sp' - 4096) / 8 <= a < ASHADOW_BASE + sp' / 8 -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
    Proof.
      intros m lo hi sp' ST Hlo Hhi a Ha. pose proof (stack0_bounds _ _ _ ST) as [B1 B2]. acb. rewrite ASHADOW_BASE_val in Ha.
      set (x := 8 * (a - 0x7fff8000)).
      assert (Hx : lo <= x /\ x + 1 <= hi) by (subst x; Z.div_mod_to_equations; lia).
      assert (Ex : wa (sh x) = Z_to_bv 64 a).
      { unfold wa, sh. rewrite ASHADOW_BASE_val. f_equal. subst x. Z.div_mod_to_equations. lia. }
      pose proof (stack0_read0 m lo hi x 1 (Z_to_bv 64 a) ST ltac:(lia) ltac:(lia) ltac:(lia) ltac:(symmetry; exact Ex)) as RD.
      rewrite ov_rdn in RD. cbn [rdn BLPropExec.rdn] in RD. unfold mrd in RD.
      destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
      - cbn in RD. unfold BacX.b8 in RD. congruence.
      - exfalso. change asegs with RSEGS in RD. rewrite (aseg_rom_high (Z_to_bv 64 a)) in RD; [discriminate|].
        rewrite u_small; [lia | unfold AAPP_HI in *; lia].
    Qed.

    Lemma rw_rdn : forall m a cs, rw_cells asegs m a cs -> rdn RSEGS m (Z_to_bv 64 a) (cells_size cs) = Some (cells_bytes cs).
    Proof.
      intros m a cs [[WF BA] _].
      assert (L : length (cells_bytes cs) = cells_size cs) by (apply cells_bytes_length; exact WF).
      pose proof (bytes_at_rdn asegs m a (cells_bytes cs) 0 (cells_size cs) BA ltac:(lia)) as R.
      rewrite drop_0, take_ge in R by lia. rewrite Nat2Z.inj_0, Z.add_0_r in R. exact R.
    Qed.

    Lemma cell_of_C8 : forall m a v, rw_cells asegs m a [C8 (BacX.wz v)] -> cell_ok m (a, 8%nat, v).
    Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. unfold cell_ok. cbn [cells_size csize Nat.add] in R. rewrite R. cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity. Qed.
    Lemma cell_of_C4 : forall m a v, rw_cells asegs m a [C4 (BacX.wz v)] -> cell_ok m (a, 4%nat, v).
    Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. unfold cell_ok. cbn [cells_size csize Nat.add] in R. rewrite R. cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity. Qed.

    Lemma cells_of_C8C8 : forall m a v1 v2, rw_cells asegs m a [C8 (BacX.wz v1); C8 (BacX.wz v2)] -> 0 <= a -> a + 16 < 2 ^ 64 ->
      cell_ok m (a, 8%nat, v1) /\ cell_ok m (a + 8, 8%nat, v2).
    Proof.
      intros m a v1 v2 RC Ha Ha2. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. unfold cell_ok. split.
      - pose proof (rdn_firstn RSEGS m 16 (Z_to_bv 64 a) _ 8 R ltac:(lia)) as R1. rewrite R1. cbn [cells_bytes cbytes app].
        rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by (rewrite length_le8; lia). reflexivity.
      - pose proof (rdn_skipn RSEGS m 16 (Z_to_bv 64 a) _ 8 R ltac:(lia)) as R2. unfold nat_to_word in R2.
        change (16 - 8)%nat with 8%nat in R2. replace (Z.of_nat 8) with 8 in R2 by reflexivity. rewrite lit_add_lit in R2.
        rewrite R2. cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (drop_app_length' _ _ 8) by (rewrite length_le8; reflexivity). reflexivity.
    Qed.
    Lemma cells_of_C1C1 : forall m a v1 v2, rw_cells asegs m a [C1 (BacX.b8 v1); C1 (BacX.b8 v2)] -> 0 <= a -> a + 2 < 2 ^ 64 ->
      rdn RSEGS m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v1] /\ rdn RSEGS m (Z_to_bv 64 (a + 1)) 1 = Some [Z_to_bv 8 v2].
    Proof.
      intros m a v1 v2 RC Ha Ha2. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. split.
      - pose proof (rdn_firstn RSEGS m 2 (Z_to_bv 64 a) _ 1 R ltac:(lia)) as R1. rewrite R1. reflexivity.
      - pose proof (rdn_skipn RSEGS m 2 (Z_to_bv 64 a) _ 1 R ltac:(lia)) as R2. unfold nat_to_word in R2.
        change (2 - 1)%nat with 1%nat in R2. replace (Z.of_nat 1) with 1 in R2 by reflexivity. rewrite lit_add_lit in R2.
        rewrite R2. reflexivity.
    Qed.
    Lemma cell_of_C1 : forall m a v, rw_cells asegs m a [C1 (BacX.b8 v)] -> rdn RSEGS m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v].
    Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. rewrite R. reflexivity. Qed.

    Lemma apf1_cells_of : forall m, ACONST m -> cells_ok m astdout0 -> cells_ok m apf1_cells.
    Proof.
      intros m AC ST.
      pose proof (ACONST_drv_reals m AC) as (R1 & R2 & R3 & R4 & R5 & R6).
      pose proof (ACONST_drv_flags m AC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
      pose proof (ACONST_drv_shwords m AC) as (W1 & W2 & W3 & W4 & W5 & W6).
      pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2].
      pose proof (cell_of_C1 m _ _ F1) as I3.
      unfold apf1_cells, cells_ok.
      repeat apply Forall_cons; try apply Forall_nil;
        first [ apply cell_of_C8; assumption
              | apply cell_of_C4; assumption
              | unfold cell_ok; first [exact I1 | exact I2 | exact I3]
              | eapply (cells_ok_In m astdout0); [exact ST | solve [in_solve]] ].
    Qed.

    Lemma apb_cells_of : forall m k, ACONST m -> astdout_after m k -> cells_ok m (apb_cells (ABUF + 2 * Z.of_nat k)).
    Proof.
      intros m k AC ST.
      pose proof (ACONST_drv_reals m AC) as (R1 & R2 & R3 & R4 & R5 & R6).
      pose proof (ACONST_drv_flags m AC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
      pose proof (ACONST_drv_shwords m AC) as (W1 & W2 & W3 & W4 & W5 & W6).
      pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2].
      pose proof (cell_of_C1 m _ _ F1) as I3.
      destruct ST as [S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14].
      unfold apb_cells, cells_ok, ABUF.
      repeat apply Forall_cons; try apply Forall_nil;
        first [ apply cell_of_C8; assumption
              | apply cell_of_C4; assumption
              | unfold cell_ok; first [exact I1 | exact I2 | exact I3 | assumption] ].
    Qed.

    Lemma aheap_frame_tr : forall m m' s1 LB1 rs,
      as_RHEAP H s1 LB1 m -> frame_mod m m' rs -> (forall r, In r rs -> atr_region r) -> as_RHEAP H s1 LB1 m'.
    Proof.
      intros m m' s1 LB1 rs RH FM RS. pose proof SPlo. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb. unfold atr_region, ATR_STACK in RS.
      eapply (ah_RHEAP_frame H HH); [exact RH | apply frame_mod_munch; exact FM | exact (aframe_mod_wmono _ _ _ FM) |].
      apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr).
      unfold aclient_write_ok, aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ALIBC_PGSZ, ATP. cbn [fst snd].
      destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; [left; lia | right; left; lia | right; left; lia | right; left; lia | right; left; lia].
    Qed.

    Ltac pf_region Hr :=
      cbn [In] in Hr;
      repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
      unfold atr_region, ATR_STACK; cbn [fst snd]; rewrite ?u_small by lia; lia.

    Lemma zero_lines_snoc : forall k, zero_lines k ++ [Z_to_bv 8 48; Z_to_bv 8 10] = zero_lines (S k).
    Proof. induction k as [|k IH]; [reflexivity|]. cbn [zero_lines app]. rewrite IH. reflexivity. Qed.

    Lemma amemcpy_call : forall (regs : bvmap 5 word) (mem : mem) (msF : machine_state) (mo : Model) (s : as_St H)
        (SP Dst Src Nn lo : Z) (src junk : list byte) (ra : Z) (Kx : TSet),
      as_VIS H s msF = mkst regs (Z_to_bv 64 AMEMCPY_STUB) mem rom -> as_AKREL H s (mkCfg msF mo) ->
      getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
      getr regs 2 = Z_to_bv 64 SP -> getr regs 10 = Z_to_bv 64 Dst -> getr regs 11 = Z_to_bv 64 Src -> getr regs 12 = Z_to_bv 64 Nn ->
      bytes_at asegs mem Src src -> length src = Z.to_nat Nn -> rw_cells asegs mem Dst [CB (Z.to_nat Nn) junk] ->
      (Src + Nn <= Dst \/ Dst + Nn <= Src) -> 0 <= Nn <= 2 ^ 40 -> 0 <= Src -> 0 <= Dst ->
      accessible mem Src Nn -> accessible mem Dst Nn -> shvis mem Src (Src + Nn) -> shvis mem Dst (Dst + Nn) ->
      in_app_mem Src (Src + Nn) -> in_app_mem Dst (Dst + Nn) -> aconst_ok (Dst, Dst + Nn) ->
      stk asegs mem lo SP -> aceil <= lo -> lo <= SP - 4096 -> SP < 2 ^ 64 ->
      (Dst + Nn <= lo \/ SP <= Dst) -> (Src + Nn <= lo \/ SP <= Src) ->
      mem_inv asegs mem -> ACONST mem ->
      (forall regs' mem' msF' mo',
         as_VIS H s msF' = mkst regs' (Z_to_bv 64 ra) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' ->
         (forall r, In r aheap_kept -> getr regs' r = getr regs r) -> getr regs' 10 = Z_to_bv 64 Dst ->
         munch [(Dst, Dst + Nn); (SP - 4096, SP)]%Z mem mem' -> wmono asegs mem mem' -> mem_inv asegs mem' -> stk asegs mem' lo SP ->
         rw_cells asegs mem' Dst [CB (Z.to_nat Nn) src] -> bytes_at asegs mem' Src src -> ACONST mem' ->
         realizes asegs (mkCfg msF' mo') Kx) ->
      realizes asegs (mkCfg msF mo) Kx.
    Proof.
      intros regs mem msF mo s SP Dst Src Nn lo src junk ra Kx HV HA Hra Hra64 Hra2 R2 R10 R11 R12
             SRC LEN DST SEP HNn HS HD ACS ACD SVS SVD IMS IMD AOK ST CE LO SPH FSD FSS MI AC HK.
      eapply (aevt_call H HH DL _ s msF mo regs _ mem Kx HV HA).
      - rewrite mkR_of_getr, Hra, R2, R10, R11, R12.
        eapply (amemcpy_specZ H HH) with (lo := lo) (junk := junk); eassumption.
      - intros msF' mo' HA' HMP HP. unfold amove_post in HP.
        destruct HP as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms & MU' & WM' & MI' & ST' & D' & S' & AC').
        rewrite (ret_pc_even ra Hra64 Hra2) in Hms.
        change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in Hms.
        eapply (HK _ m' msF' mo' Hms HA' HMP); try assumption.
        + intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
          destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
            rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; assumption].
        + rewrite (getr_mkR (Z_to_bv 64 ra)). reflexivity.
    Qed.

    Lemma rdn_munch : forall W m m' (a : Z) n bs,
      munch W m m' -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
      (forall x, a <= x < a + Z.of_nat n -> outside W x) ->
      rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
    Proof.
      intros W m m' a n bs MU HD Ha Hn HO.
      destruct n as [|n']; [cbn in *; exact HD|].
      rewrite (rdn_ext RSEGS (S n') m' m); [exact HD | rewrite u_small by lia; lia |]. intros x Hx. rewrite u_small in Hx by lia.
      apply MU. apply HO. exact Hx.
    Qed.

    Lemma cells_ok_munch : forall W m m' cs,
      forallb cell_wf_b cs = true -> cells_ok m cs -> munch W m m' ->
      Forall (fun c : Z * nat * Z => match c with (a, w, _) => disjoint_from W a (Z.of_nat w) end) cs ->
      cells_ok m' cs.
    Proof.
      intros W m m' cs Hwf Hc MU Hd. unfold cells_ok in *.
      induction cs as [|[[a w] v] cs IH]; [constructor|].
      cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
      inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
      unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
      repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
      unfold cell_ok in *. eapply rdn_munch; [exact MU | exact Hok | lia | lia |]. intros y Hy. eapply disjoint_outside; [exact Hx | lia].
    Qed.

    Lemma atinv_copy : forall b m m' (D Nn : Z) LB1 sx,
      TB b -> atinv (adrv_cellsT_of b) m -> munch [(D, D + Nn); (bv_unsigned sp - 80 - 4096, bv_unsigned sp - 80)]%Z m m' -> wmono asegs m m' ->
      mem_inv asegs m' -> stk asegs m' (bv_unsigned sp - ATR_STACK) (bv_unsigned sp - 80) -> ACONST m' ->
      ablock_range H D Nn -> (D + Nn <= A \/ A + cap <= D) -> as_RHEAP H sx LB1 m -> In (p, A, cap) LB1 -> (exists q, In (q, D, Nn) LB1) ->
      atinv (adrv_cellsT_of b) m'.
    Proof.
      intros b m m' D Nn LB1 sx Hb [INV STK AC RELRO GLB CELLS [t [TID Ht]] [e ERR] [can [CAN CAN64]] RFS [shi [SH0 Hshi]] ABOVE [B' [AUX HB']] ADDR DATA [junk JCB] DST]
             MU WM INV' STK' AC' HBR DISJ RH HIn [q HInD].
      pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb.
      pose proof HBR as (R1 & R2 & R3 & R4 & R5 & R6 & R7). unfold AIMG_TOP in R4.
      pose proof blkA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7). unfold AIMG_TOP in BA4. pose proof (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as HC.
      pose proof (ah_RFS_range H HH _ _ RFS) as [(F1 & F2 & F3 & F4) _].
      assert (AG : forall x : word, bv_unsigned sp - 80 <= bv_unsigned x -> m' x = m x).
      { intros x Hx. apply MU. cbn. lia. }
      assert (IMG : forall x n, x + n <= 0x6e8000 -> disjoint_from [(D, D + Nn); (bv_unsigned sp - 80 - 4096, bv_unsigned sp - 80)]%Z x n).
      { intros x n Hx. cbn. lia. }
      assert (CW : Forall (aclient_write_ok H LB1) [(D, D + Nn); (bv_unsigned sp - 80 - 4096, bv_unsigned sp - 80)]%Z).
      { constructor; [| constructor; [| constructor]].
        - right; right; left. exists (q, D, Nn). split; [exact HInD | cbn; lia].
        - left. cbn. lia. }
      split; try assumption.
      - destruct STK as (S1 & S2 & S3). destruct STK' as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
        intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp - 80)) as [L|L]; [apply S3'; lia|].
        assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by lia; lia).
        unfold wview, mrd. rewrite E. apply S3. lia.
      - intros i Hi. rewrite <- (RELRO i Hi). rewrite <- wa_eq. apply MU. rewrite wa_eq, u_small by lia. cbn. lia.
      - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq;
          apply MU; rewrite wa_eq, u_small by lia; cbn; lia.
      - eapply cells_ok_munch; [apply cellsT_wf; exact Hb | exact CELLS | exact MU |].
        eapply Forall_impl; [| apply cellsT_range; exact Hb]. intros [[a w] v] Ra. unfold cell_rng in Ra. apply IMG. lia.
      - exists t. split; [|exact Ht]. eapply rdn_munch; [exact MU | exact TID | lia | cbn; lia |]. intros x Hx. cbn in Hx |- *. lia.
      - exists e. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. apply IMG. unfold AERRNO, ATP. cbn. lia.
      - exists can. split; [|exact CAN64]. eapply rdn_munch; [exact MU | exact CAN | lia | cbn; lia |]. intros x Hx. cbn in Hx |- *. lia.
      - eapply (ah_RFS_frame H HH); [exact RFS | exact MU | exact WM |].
        constructor; [| constructor; [| constructor]]; left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP; lia.
      - exists shi. split; [|exact Hshi]. eapply stack0_transport; [exact SH0 | exact MU | exact WM |].
        constructor; [eapply stack0_ok_aapp; [exact R7 | lia | lia] | constructor; [apply stack0_ok_app; unfold AHI_LO; lia | constructor]].
      - intros a Ha. rewrite <- (ABOVE a Ha). apply AG. lia.
      - exists B'. split; [|exact HB']. eapply (ah_rauxv_frame H HH LB1); [exact AUX | exact MU | exact WM | exact CW].
      - eapply addressable_transport; [exact ADDR | exact MU | exact WM |].
        pose proof (aapp_disjoint_sh D Nn A cap R7 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as SD.
        pose proof (sh_below_aceil (A + cap) ltac:(unfold AAPP_HI; lia)).
        pose proof (sh_nsh_high A cap ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)).
        pose proof (sh_mono A (A + cap) ltac:(lia)).
        cbn. unfold AHI_LO in *. repeat split; lia.
      - eapply rdn_munch; [exact MU | exact DATA | lia | lia |]. intros x Hx. cbn. lia.
      - exists junk. eapply rw_cells_transport; [exact JCB | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. lia.
      - eapply adstat_eq; [exact DST|]. intros x Hx. unfold adstat_win in Hx. apply MU. rewrite wa_eq, u_small by lia. cbn. lia.
    Qed.

    Section Loop.

      Variables (Dz OWz : Z) (cb : list block).
      Hypothesis COPY : (N = 0 /\ Dz = AFUZZ_EMPTY /\ OWz = 0 /\ cb = [])
                        \/ (1 <= N /\ OWz = Dz /\ exists pD, cb = [(pD, Dz, N)] /\ ablock_range H Dz N).
      Let LB0 : list block := cb ++ LB.

      Variable K : TSet.
      Hypothesis HPOST : forall (fx' : DFP) regs' mem' msF' mo' s', ATRpost H FZP fx' sp A cap data p s0 LB mo0 regs0 mem0 regs' mem' msF' mo' s' ->
         realizes asegs (mkCfg msF' mo') K.

      Definition spent (k : nat) : Z := as_Cm H N + Z.of_nat k * fz_cost FZP N.

      Let HD16 : Dz mod 16 = 0.
      Proof. destruct COPY as [(_ & -> & _) | (_ & _ & pD & _ & (_ & R2 & _))]; [reflexivity | exact R2]. Qed.

      Record lstate (k kc : nat) (r : Z) (regs : bvmap 5 word) (m : word -> option byte) (mo : Model) (sC : as_St H) (LBc : list block) : Prop := LS {
        ls_regs  : loop_base sp regs (Z_to_bv 64 N) (Z_to_bv 64 Dz) (Z_to_bv 64 OWz);
        ls_r     : getr regs 21 = Z_to_bv 64 r;
        ls_k4    : forall rr : reg, In rr ([24; 25; 26; 27]%bv : list reg) -> getr regs rr = getr regs0 rr;
        ls_tinv  : atinv (adrv_cellsT_of 0) m;
        ls_frame : tframe sp m (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23);
        ls_heap  : as_RHEAP H sC LBc m;
        ls_perm  : Permutation LBc LB0;
        ls_mpres : as_MPRES H mo0 mo;
        ls_copy  : rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds;
        ls_cells : 1 <= N -> rw_cells asegs m Dz [CB (Z.to_nat N) ds];
        ls_caddr : 1 <= N -> addressable m Dz N;
        ls_sto   : sto k m;
        ls_al    : as_AL H sC >= as_AL H s0 - spent kc }.

      Let Hfd1 : forall mo, as_MPRES H mo0 mo -> fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
      Proof. intros mo MP. destruct (adl_mpres H DL _ _ MP) as (_ & E & _). rewrite E. exact (atr_fd1 _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
      Let Hfd2 : forall mo, as_MPRES H mo0 mo -> fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
      Proof. intros mo MP. destruct (adl_mpres H DL _ _ MP) as (_ & E & _). rewrite E. exact (atr_fd2 _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
      Let Hfs : forall mo, as_MPRES H mo0 mo -> m_fs mo = m_fs mo0.
      Proof. intros mo MP. exact (proj1 (adl_mpres H DL _ _ MP)). Qed.

      Section FPL1.
      Context {fx : DFP}.

      Lemma tr_ret : forall regs m msF mo sC LBf,
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0xe87bc) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        loop_base sp regs (Z_to_bv 64 N) (Z_to_bv 64 Dz) (Z_to_bv 64 OWz) ->
        (forall rr : reg, In rr ([24; 25; 26; 27]%bv : list reg) -> getr regs rr = getr regs0 rr) ->
        atinv (adrv_cellsT_of 0) m ->
        tframe sp m (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23) ->
        as_RHEAP H sC LBf m -> Permutation LBf LB -> as_MPRES H mo0 mo -> sto calls m ->
        as_AL H sC >= as_AL H s0 - atr_cost H FZP data ->
        realizes asegs (mkCfg msF mo) K.
      Proof.
        intros regs m msF mo sC LBf HV HA LR K4 TI TF RH PERM MP STO HAL. pose proof SPlo. pose proof SPhi.
        eapply (seg_T8 H DL sp SP16 SPlo SPhi sC msF mo regs m _ _ _ _ _ _ _ _ _ _ _ K LR (atinv_stk128 _ m TI) (atinv_ro _ m TI) (ti_relro _ _ TI) (atinv_latch _ m TI) TF);
          [| exact HV | exact HA].
        intros regs' msF' mo' HV' HA' SB' Q2 Q4 Q10 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 KP K4'.
        apply (HPOST fx regs' m msF' mo' sC). destruct TI as [INV STK AC RELRO GLB CELLS TID ERR CAN RFS SH0 ABOVE [B' [AUX HB']] ADDR DATA JCB DST].
        destruct calls as [|k'] eqn:EC; [lia|]. cbn [sto] in STO.
        split; try assumption.
        - eapply (ah_mpres_trans H HH); [exact MP| apply (adl_sb H DL); exact SB'].
        - intros rr Hrr. cbn [In] in Hrr.
          destruct Hrr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]];
            first [assumption | rewrite K4' by in_solve; apply K4; in_solve].
        - eapply astk_stk_ok; [exact STK | lia | lia | unfold ATR_STACK; lia | lia].
        - exists LBf. split; [exact RH | exact PERM].
        - exists B'. split; [exact AUX|]. lia.
        - rewrite adrv_cells_T_eq. split; try assumption.
        - change (hdr_calls data) with calls. rewrite EC. cbn [Nat.pred]. exact STO.
        - rewrite (same_but_materialized_fs _ _ SB'). apply Hfs. exact MP.
        - rewrite (same_but_materialized_fds _ _ SB'). apply Hfd1. exact MP.
        - rewrite (same_but_materialized_fds _ _ SB'). apply Hfd2. exact MP.
      Qed.
      End FPL1.

      Lemma lb_remove_perm : forall L q Ak n, List.NoDup (map blk_id L) -> In (q, Ak, n) L ->
        Permutation L ((q, Ak, n) :: as_lb_remove H q L).
      Proof.
        destruct (ah_lb_remove H HH) as (L1 & L2 & L3).
        induction L as [|b L IH]; intros q Ak n ND HIn; [destruct HIn|].
        cbn [map] in ND. apply NoDup_cons_iff in ND as [Hni Hnd].
        destruct HIn as [E | HIn].
        - subst b. cbn [blk_id fst] in Hni. pose proof (L1 q Ak n L Hni) as E1.
          change (@cons (prod (prod bptr Z) Z)) with (@cons block) in E1. rewrite E1. apply Permutation_refl.
        - assert (NE : blk_id b <> q).
          { intros E. apply Hni. rewrite E. replace q with (blk_id (q, Ak, n)) by reflexivity. apply in_map. exact HIn. }
          pose proof (L2 q b L NE) as E2. change (@cons (prod (prod bptr Z) Z)) with (@cons block) in E2. rewrite E2.
          eapply Permutation_trans; [apply perm_skip; apply (IH q Ak n Hnd HIn) | apply perm_swap].
      Qed.

      Let TRC : adrv_traces H FZP. Proof. exact (atr_tr _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
      Let HCAP : Z.of_nat (length data) <= cap. Proof. exact (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
      Let HAL0 : atr_cost H FZP data <= as_AL H s0. Proof. exact (atr_al _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
      Let COSTS : cost_laws H. Proof. exact (ah_costs H HH). Qed.

      Section FPL2.
      Context {fx : DFP}.

      Lemma tr_free : forall regs m msF mo sC LBc,
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0xe87a0) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate calls calls 1 regs m mo sC LBc -> getr regs 19 = Z_to_bv 64 0 ->
        realizes asegs (mkCfg msF mo) K.
      Proof.
        intros regs m msF mo sC LBc HV HA [LR R21 K4 TI TF RH PERM MP CPY CELLS CADDR STO HAL] R19. pose proof SPlo. pose proof SPhi.
        pose proof HCLO as HCL. unfold ATR_STACK in HCL. pose proof HN as HN'.
        assert (HCOST : atr_cost H FZP data = as_Cm H N + as_Cf H N + Z.of_nat calls * fz_cost FZP N) by reflexivity.
        pose proof HAL0 as AL0. rewrite HCOST in AL0. unfold spent in HAL.
        destruct COSTS as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (C1 N ltac:(lia)). pose proof (C3 N ltac:(lia)). pose proof (C3 0 ltac:(lia)).
        pose proof (C4 0 N ltac:(lia)).
        eapply (seg_T7free H DL sp SP16 SPlo SPhi sC msF mo regs m _ _ _ K LR R19 R21 (atinv_stk128 _ m TI) (atinv_ro _ m TI) (ti_relro _ _ TI) (atinv_latch _ m TI));
          [| exact HV | exact HA].
        intros regs1 msF1 mo1 HV1 HA1 SB1 (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23) Q1 Q10 K4'.
        destruct (ti_aux _ _ TI) as [B' [AUX1 HB']]. destruct (ti_errno _ _ TI) as [errv ERR].
        assert (MP1 : as_MPRES H mo0 mo1) by (eapply (ah_mpres_trans H HH); [exact MP | apply (adl_sb H DL); exact SB1]).
        destruct COPY as [(N0 & ED & EOW & Ecb) | (N1 & EOW & pD & Ecb & HBR)].
        -
          rewrite EOW in Q10.
          eapply (afree_null_call H HH DL regs1 m msF1 mo1 sC LBc (bv_unsigned sp - ATR_STACK) B' errv 0xe87bc [] K HV1 HA1 Q1);
            [ lia | reflexivity | exact Q4 | exact Q10 | exact RH | lia
            | exact AUX1 | rewrite Q2, u_small by lia; lia
            | rewrite Q2, u_small by lia; exact (atinv_stklo _ m TI)
            | acb; unfold ATR_STACK; lia | rewrite Q2, u_small by lia; unfold AFREE_STACK, ATR_STACK; lia
            | rewrite Q2, u_small by lia; unfold ATR_STACK; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
            | rewrite Q4; unfold AERRNO; rewrite u_small by (unfold ATP; lia); exact ERR | exact (ti_inv _ _ TI) | exact (ti_ac _ _ TI)
            | apply (ah_chain_nil H HH); rewrite Q8, u_small by lia; acb; lia |].
          intros regs2 mem2 msF2 mo2 s2 HV2 HA2 MP2 KEPT Hinv2 STK2 ERR2 AUX2 HP2 RH2 AC2 HAL2.
          rewrite Q2, u_small in STK2, HP2 by lia. rewrite Q4 in ERR2. unfold AERRNO in *.
          pose proof (KEPT 2%bv ltac:(in_solve)) as S2'. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
          pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 20%bv ltac:(in_solve)) as S20.
          pose proof (KEPT 22%bv ltac:(in_solve)) as S22. pose proof (KEPT 23%bv ltac:(in_solve)) as S23.
          eapply (tr_ret regs2 mem2 msF2 mo2 s2 LBc HV2 HA2).
          + unfold loop_base. rewrite S2', S4, S8, S9, S18, S20, S22, S23. repeat split; assumption.
          + intros rr Hrr. rewrite (KEPT rr) by (unfold aheap_kept; in_from Hrr). rewrite (K4' rr Hrr). apply K4. exact Hrr.
          + eapply (atinv_apres 0 m mem2 LBc B' _ TB0); try assumption.
            * eapply Permutation_in; [apply Permutation_sym; exact PERM|]. subst LB0. rewrite Ecb. cbn. apply (atr_blk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE).
            * rewrite u_small in ERR2 by (unfold ATP; lia). exact ERR2.
            * eapply (RFS_via_apres H HH); [exact (ti_rfs _ _ TI) | exact HP2].
            * intros shi SH. eapply stack0_xpres; [apply xpres_of_apres; exact HP2 | exact SH | constructor].
          + eapply atframe_agree; [exact TF|]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP2 _ (u64_range x) ltac:(left; lia))).
          + exact RH2.
          + eapply Permutation_trans; [exact PERM|]. subst LB0. rewrite Ecb. apply Permutation_refl.
          + eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
          + eapply sto_apres; [lia | exact STO | exact HP2].
          + rewrite HCOST. rewrite N0 in *. lia.
        -
          assert (HIn : In (pD, Dz, N) LBc) by (eapply Permutation_in; [apply Permutation_sym; exact PERM|]; subst LB0; rewrite Ecb; left; reflexivity).
          assert (HInA : In (p, A, cap) LBc) by (eapply Permutation_in; [apply Permutation_sym; exact PERM|]; subst LB0; rewrite Ecb; right; apply (atr_blk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE)).
          destruct (CADDR N1) as [_ SHD].
          rewrite EOW in Q10.
          eapply (afree_call H HH DL regs1 m msF1 mo1 sC LBc pD Dz N (bv_unsigned sp - ATR_STACK) B' errv 0xe87bc [] ds (shadow_of N) K HV1 HA1 Q1);
            [ lia | reflexivity | exact Q4 | exact Q10 | exact RH | exact HIn | lia
            | exact (CELLS N1) | exact SHD | apply shadow_of_length; lia
            | exact AUX1 | rewrite Q2, u_small by lia; lia
            | rewrite Q2, u_small by lia; exact (atinv_stklo _ m TI)
            | acb; unfold ATR_STACK; lia | rewrite Q2, u_small by lia; unfold AFREE_STACK, ATR_STACK; lia
            | rewrite Q2, u_small by lia; unfold ATR_STACK; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
            | rewrite Q4; unfold AERRNO; rewrite u_small by (unfold ATP; lia); exact ERR | exact (ti_inv _ _ TI) | exact (ti_ac _ _ TI)
            | apply (ah_chain_nil H HH); rewrite Q8, u_small by lia; acb; lia
            | cbn [map snd app]; destruct TRC as (_ & _ & _ & _ & _ & T6 & _); exact T6 |].
          intros regs2 mem2 msF2 mo2 s2 HV2 HA2 MP2 KEPT Hinv2 STK2 ERR2 AUX2 HP2 RH2 AC2 HAL2.
          rewrite Q2, u_small in STK2, HP2 by lia. rewrite Q4 in ERR2. unfold AERRNO in *.
          pose proof (KEPT 2%bv ltac:(in_solve)) as S2'. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
          pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 20%bv ltac:(in_solve)) as S20.
          pose proof (KEPT 22%bv ltac:(in_solve)) as S22. pose proof (KEPT 23%bv ltac:(in_solve)) as S23.
          pose proof (lb_remove_perm LBc pD Dz N (ah_nodup H HH _ _ _ RH) HIn) as P1.
          assert (PERM2 : Permutation (as_lb_remove H pD LBc) LB).
          { apply (Permutation_cons_inv (a:=(pD, Dz, N))). eapply Permutation_trans; [apply Permutation_sym; exact P1|].
            eapply Permutation_trans; [exact PERM|]. subst LB0. rewrite Ecb. apply Permutation_refl. }
          eapply (tr_ret regs2 mem2 msF2 mo2 s2 (as_lb_remove H pD LBc) HV2 HA2).
          + unfold loop_base. rewrite S2', S4, S8, S9, S18, S20, S22, S23. repeat split; assumption.
          + intros rr Hrr. rewrite (KEPT rr) by (unfold aheap_kept; in_from Hrr). rewrite (K4' rr Hrr). apply K4. exact Hrr.
          + eapply (atinv_apres 0 m mem2 (as_lb_remove H pD LBc) B' _ TB0); try assumption.
            * eapply Permutation_in; [apply Permutation_sym; exact PERM2 | apply (atr_blk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE)].
            * rewrite u_small in ERR2 by (unfold ATP; lia). exact ERR2.
            * eapply (RFS_via_apres H HH); [exact (ti_rfs _ _ TI) | exact HP2].
            * intros shi SH. eapply stack0_xpres; [apply xpres_of_apres; exact HP2 | exact SH | constructor].
          + eapply atframe_agree; [exact TF|]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP2 _ (u64_range x) ltac:(left; lia))).
          + exact RH2.
          + exact PERM2.
          + eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
          + eapply sto_apres; [lia | exact STO | exact HP2].
          + rewrite HCOST. lia.
      Qed.
      End FPL2.
      Lemma copy_in : forall LBc, Permutation LBc LB0 -> 1 <= N -> exists pD, In (pD, Dz, N) LBc.
      Proof.
        intros LBc HP HN1. destruct COPY as [(N0 & _) | (_ & _ & pD & Ecb & _)]; [lia|]. exists pD.
        eapply Permutation_in; [apply Permutation_sym; exact HP|]. subst LB0. rewrite Ecb. left. reflexivity.
      Qed.
      Lemma blkA_in : forall LBc, Permutation LBc LB0 -> In (p, A, cap) LBc.
      Proof.
        intros LBc HP. eapply Permutation_in; [apply Permutation_sym; exact HP|]. subst LB0. apply in_or_app. right.
        exact (atr_blk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE).
      Qed.
      Lemma LB0_bytes : lb_bytes LB0 <= 2 ^ 26 + 2 ^ 27 /\ Z.of_nat (length LB0) <= 3.
      Proof.
        pose proof (atr_lb1 _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as [H1 H2]. pose proof HN as HN'. subst LB0.
        destruct COPY as [(_ & _ & _ & ->) | (_ & _ & pD & -> & _)]; cbn [app lb_bytes fold_right length blk_size snd]; fold (lb_bytes LB); lia.
      Qed.

      Lemma copy_xpres : forall m m' LBc XS sx m1, Permutation LBc LB0 -> as_RHEAP H sx LBc m -> as_RFS H [] m1 ->
        Forall (fs_scratch H []) XS -> xpres H LBc (bv_unsigned sp - 80) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) m m' ->
        (rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds -> rdn RSEGS m' (Z_to_bv 64 Dz) (length ds) = Some ds)
        /\ (1 <= N -> rw_cells asegs m Dz [CB (Z.to_nat N) ds] -> rw_cells asegs m' Dz [CB (Z.to_nat N) ds])
        /\ (1 <= N -> addressable m Dz N -> addressable m' Dz N).
      Proof.
        intros m m' LBc XS sx m1 HPm RH RFS1 HSC HP. pose proof HN as HN'. pose proof Hds as Hds'.
        destruct COPY as [(N0 & _ & _ & _) | (N1 & _ & pD & Ecb & HBR)].
        - assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. split; [reflexivity|]. split; intros; lia.
        - assert (HIn : In (pD, Dz, N) LBc).
          { eapply Permutation_in; [apply Permutation_sym; exact HPm|]. subst LB0. rewrite Ecb. left. reflexivity. }
          pose proof (blk_scratch sx LBc m m1 XS pD Dz N RH HIn RFS1 HSC) as [BF BS].
          pose proof HBR as (R1 & R2 & R3 & R4 & R5 & R6 & R7). acb.
          split; [| split].
          + intros HC. eapply rdn_xpres; [exact HP | exact HC | lia | rewrite Hds; lia |]. rewrite Hds. intros x Hx. split.
            * right; right; left. exists (pD, Dz, N). split; [exact HIn | cbn; lia].
            * apply not_rin_of_Forall. apply Forall_cons; [cbn [fst snd]; right; unfold RtB_Td.ATDLOC, AIMG_TOP in *; lia|]. eapply Forall_impl; [| exact BF]. cbn. intros iv Hiv. lia.
          + intros _ RC. eapply (xpres_rw_cells H); [exact HP | exact RC |]. cbn [cells_size csize]. split.
            * eapply aclient_range_block; [exact HIn | lia | lia].
            * apply Forall_cons; [cbn [fst snd]; right; unfold RtB_Td.ATDLOC, AIMG_TOP in *; lia|]. eapply Forall_impl; [| exact BF]. cbn. intros iv Hiv. lia.
          + intros _ AD. eapply (xpres_addressable H); [exact HP | exact AD |]. split; [eapply aclient_range_block_sh; exact HIn |].
            apply Forall_cons; [| exact BS]. cbn [fst snd]. right. unfold sh. rewrite ASHADOW_BASE_val. unfold RtB_Td.ATDLOC, AIMG_TOP in *. Z.div_mod_to_equations. lia.
      Qed.

      Lemma copy_frame : forall m m' rs, frame_mod m m' rs -> (forall r, In r rs -> atr_region r) ->
        (rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds -> rdn RSEGS m' (Z_to_bv 64 Dz) (length ds) = Some ds)
        /\ (1 <= N -> rw_cells asegs m Dz [CB (Z.to_nat N) ds] -> rw_cells asegs m' Dz [CB (Z.to_nat N) ds])
        /\ (1 <= N -> addressable m Dz N -> addressable m' Dz N).
      Proof.
        intros m m' rs FM RS. pose proof HN as HN'. pose proof Hds as Hds'. pose proof SPlo. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb.
        unfold atr_region, ATR_STACK in RS.
        destruct COPY as [(N0 & _ & _ & _) | (N1 & _ & pD & Ecb & HBR)].
        - assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. split; [reflexivity|]. split; intros; lia.
        - pose proof HBR as (R1 & R2 & R3 & R4 & R5 & R6 & R7). unfold AIMG_TOP in R4.
          split; [| split].
          + intros HC. eapply ardn_frame; [exact FM | exact HC | lia | rewrite Hds; lia |]. rewrite Hds. intros r Hr.
            destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
          + intros _ RC. eapply arw_cells_frame; [exact RC | exact FM |]. cbn [cells_size csize]. intros r Hr.
            destruct (RS r Hr) as [X|[X|[X|[X|X]]]]; first [clear - X HCL; lia | lia].
          + intros _ AD. eapply addressable_transport; [exact AD | apply frame_mod_munch; exact FM | exact (aframe_mod_wmono _ _ _ FM) |].
            assert (SHR : (0x800d5000 <= sh Dz /\ sh Dz + nsh N <= 0x8fff6e00) \/ (0x2008fff7000 <= sh Dz /\ sh Dz + nsh N <= sh aceil /\ sh aceil < AHI_LO)).
            { destruct R7 as [P|P]; [left; exact (sh_aapp_lo_range Dz N P R3) | right; exact (sh_aapp_hi_range Dz N P R3)]. }
            assert (SHT : sh aceil <= 0x10007fff7000).
            { unfold sh. rewrite ASHADOW_BASE_val. assert (A8 : 0 < 8) by lia. assert (ACL : aceil <= 0x7fffff800000) by lia.
              pose proof (Z.div_le_mono _ _ _ A8 ACL) as DM. change (0x7fffff800000 / 8) with 0xffffff00000 in DM. lia. }
            clear - RS SHR SHT H0. induction rs as [|[r k] rs IH]; [exact I|]. cbn. split.
            * pose proof (RS (r, k) (or_introl eq_refl)) as X. cbn [fst snd] in X. unfold AHI_LO in SHR. destruct X as [X|[X|[X|[X|X]]]]; lia.
            * apply IH. intros r' Hr'. apply RS. right. exact Hr'.
      Qed.

      Lemma flag_atr : forall rr, In rr regTf_w -> atr_region rr.
      Proof. intros rr Hr. unfold regTf_w, AAEF in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. unfold atr_region. cbn [fst snd]. rewrite u_small by lia. lia. Qed.
      Lemma flag_quiet : forall rr, In rr regTf_w -> quiet_region rr.
      Proof. intros rr Hr. unfold regTf_w, AAEF in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. unfold quiet_region. cbn [fst snd]. rewrite u_small by lia. lia. Qed.
      Lemma flag_tframe : forall m m' x0 x1 x2 x3 x4 x5 x6 x7,
        tframe sp m x0 x1 x2 x3 x4 x5 x6 x7 -> frame_mod m m' regTf_w -> tframe sp m' x0 x1 x2 x3 x4 x5 x6 x7.
      Proof.
        intros m m' x0 x1 x2 x3 x4 x5 x6 x7 TF FM. pose proof SPlo. eapply atframe_agree; [exact TF|]. intros x Hx. apply (proj1 FM). apply outside_of_disjoint.
        intros rr Hr. unfold regTf_w, AAEF in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia.
      Qed.

      Lemma tr_call_harness : forall (fx : DFP) k r regs m msF mo sC LBc (Kx : TSet),
        (k < calls)%nat -> FPSteps.frm_zero (@dfp_csr fx) ->
        as_VIS H sC msF = @mkst fx regs (Z_to_bv 64 0xe877c) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate k k r regs m mo sC LBc ->
        (forall (fx' : DFP) regs' m' msF' mo' sC' LBc',
           FPSteps.frm_zero (@dfp_csr fx') ->
           as_VIS H sC' msF' = @mkst fx' regs' (Z_to_bv 64 0xe884c) m' rom -> as_AKREL H sC' (mkCfg msF' mo') ->
           lstate k (S k) r regs' m' mo' sC' LBc' ->
           getr regs' 1 = Z_to_bv 64 0xe87a0 -> getr regs' 11 = Z_to_bv 64 0 -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes asegs (mkCfg msF' mo') Kx) ->
        realizes asegs (mkCfg msF mo) Kx.
      Proof.
        intros fx k r regs m msF mo sC LBc Kx Hk HFRM HV HA [LR R21 K4 TI TF RH PERM MP CPY CELLS CADDR STO HAL] HK.
        pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. unfold ATR_STACK in HCL. pose proof Hcalls as HC.
        pose proof (adl_live H DL) as [LV1 LV2]. pose proof (atr_live _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as [LV3 LV4].
        pose proof LB0_bytes as [LBB LBL]. pose proof HN as HN'.

        eapply (seg_T5 H DL sp SP16 SPlo SPhi sC msF mo regs m _ _ _ (getr regs 19) _ Kx LR eq_refl R21
                  (atinv_stk128 _ m TI) (atinv_ro _ m TI) (ti_relro _ _ TI) (atinv_latch _ m TI)); [| exact HV | exact HA].
        intros regs1 mem1 msF1 mo1 HV1 HA1 SB1 LR1 Q19 Q21' Q1 Q10 Q11 K4a FM1 STK1 LATCH1 AEF1.
        pose proof LR1 as (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23).
        assert (TI1 : atinv (adrv_cellsT_of 1) mem1).
        { eapply atinv_frame; [exact TI | exact FM1 | exact flag_atr |].
          eapply (cells_flag 0 1); [exact TB0 | exact (ti_cells _ _ TI) | exact FM1 | exact AEF1]. }
        pose proof (flag_tframe m mem1 _ _ _ _ _ _ _ _ TF FM1) as TF1.
        assert (RH1 : as_RHEAP H sC LBc mem1) by (eapply aheap_frame_tr; [exact RH | exact FM1 | exact flag_atr]).
        pose proof (copy_frame m mem1 _ FM1 flag_atr) as (CF1 & CF2 & CF3).
        assert (ST1 : sto k mem1) by (eapply sto_frame; [lia | exact STO | exact FM1 | exact flag_quiet]).
        assert (MP1 : as_MPRES H mo0 mo1) by (eapply (ah_mpres_trans H HH); [exact MP | apply (adl_sb H DL); exact SB1]).
        destruct (ti_aux _ _ TI1) as [B' [AUX1 HB']]. destruct (ti_errno _ _ TI1) as [errv ERR]. destruct (ti_sh0 _ _ TI1) as [shi [SH0 Hshi]].

        assert (HCOST : atr_cost H FZP data = as_Cm H N + as_Cf H N + Z.of_nat calls * fz_cost FZP N) by reflexivity.
        pose proof HAL0 as AL0. rewrite HCOST in AL0. unfold spent in HAL.
        destruct COSTS as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (C3 N ltac:(lia)) as CF0. pose proof (fuzz_cost_nonneg N ltac:(lia)) as FZ0.
        assert (ALok : fz_cost FZP N <= as_AL H sC).
        { assert (M : Z.of_nat k * fz_cost FZP N + fz_cost FZP N <= Z.of_nat calls * fz_cost FZP N) by nia. lia. }
        assert (HDr : 0 < Dz /\ Dz + Z.of_nat (length ds) <= 2 ^ 64).
        { rewrite Hds. destruct COPY as [(N0 & ED & _) | (_ & _ & pD & _ & HBR)]; [rewrite ED, N0; unfold AFUZZ_EMPTY; lia |].
          acb. destruct HBR as (R1 & R2 & R3 & R4 & R5 & R6). lia. }
        change (Z_to_bv 64 0xe8894) with (Z_to_bv 64 P_FUZZ_ENTRY) in HV1.
        eapply (afuzz_call H HH DL FZP FZ regs1 mem1 msF1 mo1 sC LBc Dz N (bv_unsigned sp - ATR_STACK) B' shi ds errv 0xe8790 Kx HV1 HA1 HFRM Q1);
          [ lia | reflexivity | exact Q4 | exact Q10 | exact Q11
          | apply ardn_bytes_at; [apply CF1; exact CPY | lia | lia]
          | rewrite Hds; lia | lia | exact HD16
          | intros HN1; exact (copy_in LBc PERM HN1)
          | intros HN0; destruct COPY as [(_ & ED & _) | (HN1 & _)]; [exact ED | lia]
          | exact RH1
          | rewrite (lb_small_perm LB0 LBc PERM);
            pose proof (lb_small_le LB0); pose proof LB0_bytes as [_ LB0L];
            destruct PO as (_ & _ & _ & _ & _ & PO1 & _); nia
          | rewrite (Permutation_length PERM); pose proof LB0_bytes as [_ LB0L]; destruct PO as (_ & _ & _ & _ & _ & _ & PO2 & _); lia
          | rewrite (nlarge_perm LB0 LBc PERM); pose proof (nlarge_bound LB0); pose proof LB0_bytes as [_ LB0L];
            destruct PO as (_ & _ & _ & _ & _ & _ & _ & PO3); lia
          | exact AUX1 | rewrite Q2, u_small by lia; lia | lia
          | rewrite Q2, u_small by lia; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
          | rewrite Q2, u_small by lia; exact (atinv_stklo _ mem1 TI1)
          | acb; unfold ATR_STACK; lia
          | rewrite Q2, u_small by lia; unfold AFUZZ_STACK, ATR_STACK; lia
          | rewrite Q4; unfold AERRNO; rewrite u_small by (unfold ATP; lia); exact ERR
          | exact (ti_inv _ _ TI1) | apply FZINV; [exact (ti_inv _ _ TI1) | exact (ti_relro _ _ TI1) | exact (ti_ac _ _ TI1) | exact (ti_dstat _ _ TI1)] | exact (ti_ac _ _ TI1)
          | intros HN1; apply CF3; [exact HN1 | exact (CADDR HN1)] | exact (ti_rfs _ _ TI1)
          | exact SH0 | rewrite Q2, u_small by lia; lia
          | left; rewrite Q8, u_small by lia; acb; lia
          | destruct TRC as (_ & _ & _ & _ & _ & _ & T7 & _); exact T7
          | destruct TRC as (_ & _ & _ & _ & _ & _ & _ & T8); exact T8
          | exact ALok |].
        intros fx2 regs2 mem2 msF2 mo2 s2 LB2 XS errv2 HFRM2 HV2 HA2 MP2 KEPT A0 INV2 STK2 ERR2 AUX2 RH2 PERM2 HSC X2 RFS2 AC2 ST02 HAL2 HFI2.
        rewrite Q2, u_small in STK2, X2 by lia. rewrite Q4 in ERR2.
        pose proof (KEPT 2%bv ltac:(in_solve)) as S2'. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
        pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 20%bv ltac:(in_solve)) as S20.
        pose proof (KEPT 21%bv ltac:(in_solve)) as S21. pose proof (KEPT 22%bv ltac:(in_solve)) as S22. pose proof (KEPT 23%bv ltac:(in_solve)) as S23.
        assert (LR2 : loop_base sp regs2 (Z_to_bv 64 N) (Z_to_bv 64 Dz) (Z_to_bv 64 OWz)).
        { unfold loop_base. rewrite S2', S4, S8, S9, S18, S20, S22, S23. exact LR1. }
        assert (TI2 : atinv (adrv_cellsT_of 1) mem2).
        { apply (atinv_xpres 1 mem1 mem2 LBc XS sC mem1 B' errv2 TB1 TI1 X2 HSC (ti_rfs _ _ TI1) RH1 (blkA_in LBc PERM) INV2 STK2 AC2 AUX2 HB').
          - rewrite u_small in ERR2 by (unfold ATP; lia). exact ERR2.
          - exact RFS2.
          - exists shi. split; [exact ST02 | exact Hshi].
          - exact (FZINV' _ HFI2). }
        pose proof (copy_xpres mem1 mem2 LBc XS sC mem1 PERM RH1 (ti_rfs _ _ TI1) HSC X2) as (CP1 & CP2 & CP3).
        assert (TF2 : tframe sp mem2 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)).
        { eapply atframe_agree; [exact TF1|]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq.
          refine (proj1 (X2 _ (u64_range x) _)). split; [left; lia|].
          apply not_rin_far_td; [eapply scratch_far; [exact (ti_rfs _ _ TI1) | exact HSC] | right; acb; lia | acb; unfold RtB_Td.ATDLOC; lia]. }
        assert (ST2 : sto k mem2) by (eapply sto_xpres; [lia | exact ST1 | exact X2 | exact HSC | exact (ti_rfs _ _ TI1) | exact (FZINV' _ HFI2)]).

        eapply (seg_T6 H DL sp SP16 SPlo SPhi s2 msF2 mo2 regs2 mem2 _ _ _ _ Kx LR2 ltac:(rewrite S21; exact Q21') A0
                  (atinv_stk128 _ mem2 TI2) (atinv_ro _ mem2 TI2) (ti_relro _ _ TI2) (atinv_latch _ mem2 TI2)); [| exact HV2 | exact HA2].
        intros regs3 mem3 msF3 mo3 HV3 HA3 SB3 LR3 T19 T21 T1 T11 K4b FM3 STK3 LATCH3 AEF3.
        assert (TI3 : atinv (adrv_cellsT_of 0) mem3).
        { eapply atinv_frame; [exact TI2 | exact FM3 | exact flag_atr |].
          eapply (cells_flag 1 0); [exact TB1 | exact (ti_cells _ _ TI2) | exact FM3 | exact AEF3]. }
        pose proof (copy_frame mem2 mem3 _ FM3 flag_atr) as (CG1 & CG2 & CG3).
        apply (HK fx2 regs3 mem3 msF3 mo3 s2 LB2 HFRM2 HV3 HA3); [| exact T1 | exact T11 | exact T19].
        split.
        - exact LR3.
        - exact T21.
        - intros rr Hrr. rewrite (K4b rr Hrr), (KEPT rr) by (unfold aheap_kept; in_from Hrr). rewrite (K4a rr Hrr). apply K4. exact Hrr.
        - exact TI3.
        - exact (flag_tframe mem2 mem3 _ _ _ _ _ _ _ _ TF2 FM3).
        - eapply aheap_frame_tr; [exact RH2 | exact FM3 | exact flag_atr].
        - eapply Permutation_trans; [exact PERM2 | exact PERM].
        - eapply (ah_mpres_trans H HH); [exact MP1 |]. eapply (ah_mpres_trans H HH); [exact MP2 | apply (adl_sb H DL); exact SB3].
        - apply CG1. apply CP1. apply CF1. exact CPY.
        - intros HN1. apply CG2; [exact HN1|]. apply CP2; [exact HN1|]. apply CF2; [exact HN1 | exact (CELLS HN1)].
        - intros HN1. apply CG3; [exact HN1|]. apply CP3; [exact HN1|]. apply CF3; [exact HN1 | exact (CADDR HN1)].
        - eapply sto_frame; [lia | exact ST2 | exact FM3 | exact flag_quiet].
        - unfold spent. rewrite Nat2Z.inj_succ. lia.
      Qed.

      Ltac pf_still Hr :=
        cbn [In] in Hr;
        repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
        unfold still_region, ATR_STACK; cbn [fst snd]; rewrite ?u_small by lia; lia.

      Section FPL3.
      Context {fx : DFP}.

      Lemma tr_printf_buf : forall k r regs m msF mo sC LBc (Kx : TSet),
        (1 <= k <= 3)%nat ->
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0xe884c) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate k (S k) r regs m mo sC LBc ->
        getr regs 1 = Z_to_bv 64 0xe87a0 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 0 ->
        (forall regs' m' msF' mo',
           as_VIS H sC msF' = mkst regs' (Z_to_bv 64 0xe87a0) m' rom -> as_AKREL H sC (mkCfg msF' mo') ->
           lstate (S k) (S k) r regs' m' mo' sC LBc -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes asegs (mkCfg msF' mo') Kx) ->
        realizes asegs (mkCfg msF mo) Kx.
      Proof.
        intros k r regs m msF mo sC LBc Kx Hk HV HA [LR R21 K4 TI TF RH PERM MP CPY CELLS CADDR STO HAL] R1 R11 R19 HK.
        pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb.
        destruct k as [|k']; [lia|]. cbn [sto] in STO.
        destruct (ti_can _ _ TI) as [can [CAN CAN64]]. destruct (ti_sh0 _ _ TI) as [shi [SH0 Hshi]].
        pose proof LR as (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23).
        set (w := ABUF + 2 * Z.of_nat k').
        assert (PH : apbH m (Z_to_bv 64 (bv_unsigned sp - 80)) w can).
        { split; rewrite ?u_small by lia.
          - rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
          - unfold ASP_LO. lia.
          - unfold ASP_HI. lia.
          - eapply astk_stk_ok; [exact (ti_stk _ _ TI) | unfold ATR_STACK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | lia | lia].
          - exact (atinv_ro _ _ TI).
          - exact (ti_relro _ _ TI).
          - subst w. apply apb_cells_of; [exact (ti_ac _ _ TI) | exact STO].
          - exact CAN.
          - exact CAN64.
          - intros a Ha. eapply (stack0_qsh0 m _ _ (bv_unsigned sp - 80) SH0); [unfold ATR_STACK; lia | lia | rewrite ASHADOW_BASE_val; exact Ha]. }
        eapply (drv_printf_buf H DL k' sC msF mo regs m (Z_to_bv 64 (bv_unsigned sp - 80)) can Kx ltac:(lia) PH R1 ltac:(exact Q2) R11 HV HA).
        intros regs' mem' msF' mo' KCS FM BY WP FL HV' HA' SB'.
        rewrite u_small in FM by lia. subst w. unfold ABUF in *.
        assert (RS : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 3400), 3400); (Z_to_bv 64 0x189b00, 4); (Z_to_bv 64 0x189b28, 8);
                                       (Z_to_bv 64 (0x6e6480 + 2 * Z.of_nat k'), 2)] -> still_region rr).
        { intros rr Hr. pf_still Hr. }
        assert (T : forall (a : Z) (n : nat) bs, 0x189b04 <= a -> a + Z.of_nat n < 2 ^ 64 ->
                  (a + Z.of_nat n <= 0x189b28 \/ 0x189b30 <= a) -> a + Z.of_nat n <= 0x6e6480 + 2 * Z.of_nat k' ->
                  rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> rdn RSEGS mem' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Ha Hn Hor Hw HD. eapply ardn_frame; [exact FM | exact HD | lia | lia |].
          intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite u_small by lia; lia. }
        pose proof (copy_frame m mem' _ FM (fun rr Hr => still_atr rr (RS rr Hr))) as (CP1 & CP2 & CP3).
        apply (HK regs' mem' msF' mo' HV' HA').
        - split.
          + unfold loop_base. rewrite !(KCS _) by (unfold callee_saved; in_solve). exact LR.
          + rewrite (KCS _) by (unfold callee_saved; in_solve). exact R21.
          + intros rr Hrr. rewrite (KCS rr) by (unfold callee_saved; in_from Hrr). apply K4. exact Hrr.
          + eapply atinv_frame_still; [exact TB0 | exact TI | exact FM | exact RS].
          + eapply atframe_agree; [exact TF|]. intros x Hx. apply (proj1 FM). apply outside_of_disjoint.
            intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
          + eapply aheap_frame_tr; [exact RH | exact FM | intros rr Hr; apply still_atr; apply RS; exact Hr].
          + exact PERM.
          + eapply (ah_mpres_trans H HH); [exact MP | apply (adl_sb H DL); exact SB'].
          + apply CP1. exact CPY.
          + intros HN1. apply CP2; [exact HN1 | exact (CELLS HN1)].
          + intros HN1. apply CP3; [exact HN1 | exact (CADDR HN1)].
          + cbn [sto]. destruct STO as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 LBF]. split.
            * exact FL.
            * eapply T; [ | | | | exact F2]; cbn; lia.
            * eapply T; [ | | | | exact F3]; cbn; lia.
            * eapply T; [ | | | | exact F4]; cbn; lia.
            * replace (0x6e6480 + 2 * Z.of_nat (S k')) with (0x6e6480 + 2 * Z.of_nat k' + 2) by lia. exact WP.
            * eapply T; [ | | | | exact F6]; cbn; lia.
            * eapply T; [ | | | | exact F7]; cbn; lia.
            * eapply T; [ | | | | exact F8]; cbn; lia.
            * eapply T; [ | | | | exact F9]; cbn; lia.
            * eapply T; [ | | | | exact F10]; cbn; lia.
            * eapply T; [ | | | | exact F11]; cbn; lia.
            * eapply T; [ | | | | exact F12]; cbn; lia.
            * eapply T; [ | | | | exact F13]; cbn; lia.
            * rewrite <- zero_lines_snoc. replace (2 * S k')%nat with (2 * k' + 2)%nat by lia.
              apply rdn_app_Z; [ | | lia | lia].
              -- eapply ardn_frame; [exact FM | exact LBF | lia | lia |].
                 intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
              -- replace (0x6e6480 + Z.of_nat (2 * k')) with (0x6e6480 + 2 * Z.of_nat k') by lia. exact BY.
          + exact HAL.
        - rewrite (KCS _) by (unfold callee_saved; in_solve). exact R19.
      Qed.

      Lemma tr_printf_first : forall r regs m msF mo sC LBc (Kx : TSet),
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0xe884c) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate 0 1 r regs m mo sC LBc ->
        getr regs 1 = Z_to_bv 64 0xe87a0 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 0 -> Kx [] ->
        (forall regs' m' msF' mo',
           as_VIS H sC msF' = mkst regs' (Z_to_bv 64 0xe87a0) m' rom -> as_AKREL H sC (mkCfg msF' mo') ->
           lstate 1 1 r regs' m' mo' sC LBc -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes asegs (mkCfg msF' mo') Kx) ->
        realizes asegs (mkCfg msF mo) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) Kx).
      Proof.
        intros r regs m msF mo sC LBc Kx HV HA [LR R21 K4 TI TF RH PERM MP CPY CELLS CADDR STO HAL] R1 R11 R19 K0 HK.
        pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb. cbn [sto] in STO.
        destruct (ti_can _ _ TI) as [can [CAN CAN64]]. destruct (ti_sh0 _ _ TI) as [shi [SH0 Hshi]].
        pose proof LR as (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23).
        assert (PH : ap1H regs m (Z_to_bv 64 (bv_unsigned sp - 80)) can).
        { split; rewrite ?u_small by lia.
          - exact R1.
          - exact Q2.
          - exact R11.
          - rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
          - unfold ASP_LO. lia.
          - unfold ASP_HI. lia.
          - eapply astk_stk_ok; [exact (ti_stk _ _ TI) | unfold ATR_STACK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | lia | lia].
          - exact (atinv_ro _ _ TI).
          - exact (ti_relro _ _ TI).
          - apply apf1_cells_of; [exact (ti_ac _ _ TI) | exact STO].
          - exact CAN.
          - exact CAN64.
          - intros a Ha. eapply (stack0_qsh0 m _ _ (bv_unsigned sp - 80) SH0); [unfold ATR_STACK; lia | lia | rewrite ASHADOW_BASE_val; exact Ha]. }
        unfold W. cbn [map].
        apply (drv_printf_first H DL sC msF mo regs m (Z_to_bv 64 (bv_unsigned sp - 80)) can Kx PH HV HA (Hfd1 mo MP) K0).
        intros regs' mem' msF' mo' PP HV' HA' SB'. destruct PP. rewrite u_small in P_frame by lia.
        assert (RS : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 3400), 3400); (Z_to_bv 64 0x189b00, 232); (Z_to_bv 64 0x6e6480, 1)] -> still_region rr).
        { intros rr Hr. pf_still Hr. }
        pose proof (copy_frame m mem' _ P_frame (fun rr Hr => still_atr rr (RS rr Hr))) as (CP1 & CP2 & CP3).
        apply (HK regs' mem' msF' mo' HV' HA').
        - split.
          + unfold loop_base. rewrite (P_cs 4%bv), (P_cs 8%bv), (P_cs 9%bv), (P_cs 18%bv), (P_cs 20%bv), (P_cs 22%bv), (P_cs 23%bv) by in_solve. rewrite P_sp.
            split; [reflexivity | exact (proj2 LR)].
          + rewrite (P_cs _) by in_solve. exact R21.
          + intros rr Hrr. rewrite (P_cs rr) by (in_from Hrr). apply K4. exact Hrr.
          + eapply atinv_frame_still; [exact TB0 | exact TI | exact P_frame | exact RS].
          + eapply atframe_agree; [exact TF|]. intros x Hx. apply (proj1 P_frame). apply outside_of_disjoint.
            intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
          + eapply aheap_frame_tr; [exact RH | exact P_frame | intros rr Hr; apply still_atr; apply RS; exact Hr].
          + exact PERM.
          + eapply (ah_mpres_trans H HH); [exact MP | apply (adl_sb H DL); exact SB'].
          + apply CP1. exact CPY.
          + intros HN1. apply CP2; [exact HN1 | exact (CELLS HN1)].
          + intros HN1. apply CP3; [exact HN1 | exact (CADDR HN1)].
          + cbn [sto]. split; try assumption; first [reflexivity | replace (0x6e6480 + 2 * Z.of_nat 0) with 0x6e6480 by lia; exact P_wpos].
          + exact HAL.
        - rewrite (P_cs _) by in_solve. exact R19.
      Qed.
      End FPL3.

      Lemma tr_after_printf : forall (rn k : nat) (fx : DFP) regs m msF mo sC LBc,
        (1 <= rn)%nat -> (k + rn = calls + 1)%nat -> (1 <= k)%nat -> FPSteps.frm_zero (@dfp_csr fx) ->
        as_VIS H sC msF = @mkst fx regs (Z_to_bv 64 0xe87a0) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate k k (Z.of_nat rn) regs m mo sC LBc -> getr regs 19 = Z_to_bv 64 0 ->
        realizes asegs (mkCfg msF mo) K.
      Proof.
        induction rn as [|rn IH]; intros k fx regs m msF mo sC LBc Hrn Hk Hk1 HFRM HV HA LS R19; [lia|].
        pose proof Hcalls as HC. pose proof SPlo. pose proof SPhi.
        destruct rn as [|rn'].
        - assert (Ek : k = calls) by lia. subst k. eapply tr_free; [exact HV | exact HA | exact LS | exact R19].
        - destruct LS as [LR R21 K4 TI TF RH PERM MP CPY CELLS CADDR STO HAL].
          eapply (seg_T7more H DL sp SP16 SPlo SPhi sC msF mo regs m _ _ _ (Z.of_nat (S (S rn'))) K LR R19 R21 ltac:(lia)
                    (atinv_stk128 _ m TI) (atinv_ro _ m TI) (ti_relro _ _ TI) (atinv_latch _ m TI)); [| exact HV | exact HA].
          intros regs1 msF1 mo1 HV1 HA1 SB1 LR1 Q21 K4a.
          replace (Z.of_nat (S (S rn')) - 1) with (Z.of_nat (S rn')) in Q21 by lia.
          assert (LS1 : lstate k k (Z.of_nat (S rn')) regs1 m mo1 sC LBc).
          { split; try assumption.
            - intros rr Hrr. rewrite (K4a rr Hrr). apply K4. exact Hrr.
            - eapply (ah_mpres_trans H HH); [exact MP | apply (adl_sb H DL); exact SB1]. }
          eapply (tr_call_harness fx k _ regs1 m msF1 mo1 sC LBc K ltac:(lia) HFRM HV1 HA1 LS1).
          intros fx2 regs2 m2 msF2 mo2 sC2 LBc2 HFRM2 HV2 HA2 LS2 T1 T11 T19.
          eapply (tr_printf_buf (fx := fx2) k _ regs2 m2 msF2 mo2 sC2 LBc2 K ltac:(lia) HV2 HA2 LS2 T1 T11 T19).
          intros regs3 m3 msF3 mo3 HV3 HA3 LS3 U19.
          eapply (IH (S k) fx2); [lia | lia | lia | exact HFRM2 | exact HV3 | exact HA3 | exact LS3 | exact U19].
      Qed.

      Lemma tr_loop : forall regs m msF mo sC LBc,
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0xe877c) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate 0 0 (Z.of_nat calls) regs m mo sC LBc -> K [] ->
        realizes asegs (mkCfg msF mo) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
      Proof.
        intros regs m msF mo sC LBc HV HA LS K0. pose proof Hcalls as HC.
        eapply (tr_call_harness dfp_default 0 _ regs m msF mo sC LBc _ ltac:(lia) ltac:(reflexivity) HV HA LS).
        intros fx2 regs2 m2 msF2 mo2 sC2 LBc2 HFRM2 HV2 HA2 LS2 T1 T11 T19.
        eapply (tr_printf_first (fx := fx2) _ regs2 m2 msF2 mo2 sC2 LBc2 K HV2 HA2 LS2 T1 T11 T19 K0).
        intros regs3 m3 msF3 mo3 HV3 HA3 LS3 U19.
        eapply (tr_after_printf calls 1 fx2); [lia | lia | lia | exact HFRM2 | exact HV3 | exact HA3 | exact LS3 | exact U19].
      Qed.
    End Loop.

    Lemma calls_of_hdr : forall c, nth 2 data (Z_to_bv 8 0) = c -> Z.of_nat calls = calls_of cfg c.
    Proof.
      intros c Hc. subst calls cfg. unfold hdr_calls, calls_of, hdr_b. rewrite Hc. pose proof (hdr_cfg_range data) as HR.
      pose proof (bv_unsigned_in_range 8 c) as H8. unfold bv_modulus in H8. cbn in H8.
      destruct (Z.eqb_spec (hdr_cfg data) 0) as [E|E].
      - rewrite E. reflexivity.
      - destruct (Z.to_nat (hdr_cfg data)) eqn:EN; [lia|].
        replace (Z.land (bv_unsigned c) 3) with (bv_unsigned c mod 4)%Z by (symmetry; apply (Z.land_ones (bv_unsigned c) 2); lia).
        pose proof (Z.mod_pos_bound (bv_unsigned c) 4 ltac:(lia)). lia.
    Qed.

    Lemma atinv0 : atinv adrv_cells mem0.
    Proof.
      pose proof PRE as P. destruct (atr_st _ _ _ _ _ _ _ _ _ _ _ _ _ P) as [INV AC REL GLB CELLS TID ERR CAN RFS SH0 DST].
      split; try assumption.
      - exact (atr_stkcj _ _ _ _ _ _ _ _ _ _ _ _ _ P).
      - intros a _. reflexivity.
      - exact (atr_aux _ _ _ _ _ _ _ _ _ _ _ _ _ P).
      - exact (atr_addr _ _ _ _ _ _ _ _ _ _ _ _ _ P).
      - exact (atr_data _ _ _ _ _ _ _ _ _ _ _ _ _ P).
      - exact (atr_cb _ _ _ _ _ _ _ _ _ _ _ _ _ P).
    Qed.

    Variable K : TSet.
    Hypothesis K0 : K [].
    Hypothesis HPOST : forall (fx' : DFP) regs' mem' msF' mo' s', ATRpost H FZP fx' sp A cap data p s0 LB mo0 regs0 mem0 regs' mem' msF' mo' s' ->
       realizes asegs (mkCfg msF' mo') K.

    Theorem as_target_run_ok : realizes asegs (mkCfg msF0 mo0) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
    Proof.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof HN as HN'. pose proof Hcfg as Hcfg'. pose proof Hcalls as HC. pose proof Hds as Hds'.
      pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb.
      pose proof PRE as P.
      destruct P as [HV0 HA0 R1 R2 R4 R10 R11 R12 R13 L6 LHI _ _ _ STK STKC RH BLK [LB1 LB2] HAL AUX CAP DATA ADDR JCB0 ST OUT [ib Hib] TRC LIVE FD1 FD2].
      pose proof atinv0 as TI0. pose proof (ti_cells _ _ TI0) as CELLS0.
      pose proof blkA as (B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold AIMG_TOP in B4.
      pose proof (ah_costs H HH) as (C1 & C2 & C3 & C4 & _).
      pose proof (C1 N ltac:(lia)) as CM0. pose proof (C3 N ltac:(lia)) as CF0.
      assert (HCOST : atr_cost H FZP data = as_Cm H N + as_Cf H N + Z.of_nat calls * fz_cost FZP N) by reflexivity.
      set (c := nth 2 data (Z_to_bv 8 0)).
      pose proof (calls_of_hdr c eq_refl) as ECALLS.

      assert (Hib0 : rdn RSEGS mem0 (Z_to_bv 64 AINIT) 1 = Some [Z_to_bv 8 0]).
      { pose proof (cells_ok_In mem0 adrv_cells (0x6c3690, 1%nat, 0) CELLS0 ltac:(in_cells)) as C. exact C. }
      assert (TC0 : tcells mem0 atx_cells0).
      { pose proof (cells_ok_sub mem0 adrv_cells [(0x6e5aeb, 1%nat, 0); (0x6e58a8, 1%nat, 0); (0x6e58ac, 4%nat, 0); (0x6e58b0, 4%nat, 3); (0x6e58b8, 8%nat, 0x6e58c0)]
                      CELLS0 ltac:(vm_compute; reflexivity)) as C. exact C. }

      eapply (seg_T0 H DL sp SP16 SPlo SPhi s0 msF0 mo0 regs0 mem0 (Z_to_bv 64 CP) (Z_to_bv 64 cfg) (Z_to_bv 64 PL) (Z_to_bv 64 N) _
                R1 R2 R4 R10 R11 R12 R13 Hib0 (atinv_stk128 _ mem0 TI0) (atinv_ro _ mem0 TI0) (ti_relro _ _ TI0) (atinv_latch _ mem0 TI0) (atinv_atx _ mem0 TI0) TC0);
        [| exact HV0 | exact HA0].
      intros regs1 mem1 msF1 mo1 HV1 HA1 SB1 LR1 K4a FM1 STK1 TF1 TC1.
      assert (Q1 : forall r, In r (regT0_w sp) -> quiet_region r).
      { intros r Hr. unfold regT0_w, AINIT, AX_SLOT, AX_F3, AX_A3 in Hr. cbn [In] in Hr. unfold quiet_region, ATR_STACK.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; rewrite u_small by lia; lia. }
      assert (TI1 : atinv (adrv_cellsT_of 0) mem1).
      { eapply atinv_frame; [exact TI0 | exact FM1 | intros r Hr; apply quiet_atr; apply Q1; exact Hr | exact (cells_T0 mem0 mem1 CELLS0 FM1 TC1)]. }
      assert (RH1 : as_RHEAP H s0 LB mem1) by (eapply aheap_frame_tr; [exact RH | exact FM1 | intros r Hr; apply quiet_atr; apply Q1; exact Hr]).
      assert (ST1 : sto 0 mem1) by (eapply (sto_frame 0); [lia | exact OUT | exact FM1 | exact Q1]).
      pose proof (ti_data _ _ TI1) as DATA1.
      assert (HC1 : cfg <> 0 -> rdn RSEGS mem1 (Z_to_bv 64 CP) 1 = Some [c]).
      { intros _. subst c CP. pose proof (rdn_nth RSEGS mem1 (length data) (Z_to_bv 64 A) data 2 DATA1 ltac:(lia)) as R.
        unfold nat_to_word in R. rewrite lit_add_lit in R. exact R. }
      assert (MP1 : as_MPRES H mo0 mo1) by (apply (adl_sb H DL); exact SB1).
      clear TI0 RH DATA.
      destruct (Z.eq_dec N 0) as [N0|N1].
      -
        rewrite N0 in LR1.
        eapply (seg_T1zero H DL sp SP16 SPlo SPhi s0 msF1 mo1 regs1 mem1 cfg _ _ c _ LR1 ltac:(lia) HC1 ltac:(subst CP; rewrite u_small by lia; lia)
                  (atinv_stk128 _ mem1 TI1) (atinv_ro _ mem1 TI1) (ti_relro _ _ TI1) (atinv_latch _ mem1 TI1)); [| exact HV1 | exact HA1].
        intros regs2 msF2 mo2 HV2 HA2 SB2 LR2 Q21 K4b.
        eapply (tr_loop AFUZZ_EMPTY 0 [] ltac:(left; repeat split; lia) K HPOST regs2 mem1 msF2 mo2 s0 LB HV2 HA2); [| exact K0].
        split; try assumption.
        + rewrite N0. exact LR2.
        + rewrite ECALLS. exact Q21.
        + intros rr Hrr. rewrite (K4b rr Hrr). apply K4a. exact Hrr.
        + apply Permutation_refl.
        + eapply (ah_mpres_trans H HH); [exact MP1 | apply (adl_sb H DL); exact SB2].
        + assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. reflexivity.
        + intros; lia.
        + intros; lia.
        + unfold spent. rewrite N0 in *. lia.
      -
        eapply (seg_T1pos H DL sp SP16 SPlo SPhi s0 msF1 mo1 regs1 mem1 N cfg _ _ c _ LR1 ltac:(lia) ltac:(lia) HC1 ltac:(subst CP; rewrite u_small by lia; lia)
                  (atinv_stk128 _ mem1 TI1) (atinv_ro _ mem1 TI1) (ti_relro _ _ TI1) (atinv_latch _ mem1 TI1)); [| exact HV1 | exact HA1].
        intros regs2 msF2 mo2 HV2 HA2 SB2 LR2 Q21 K4b.
        eapply (seg_T2 H DL sp SP16 SPlo SPhi s0 msF2 mo2 regs2 mem1 _ _ _ _ _ _ LR2 Q21
                  (atinv_stk128 _ mem1 TI1) (atinv_ro _ mem1 TI1) (ti_relro _ _ TI1) (atinv_latch _ mem1 TI1)); [| exact HV2 | exact HA2].
        intros regs3 msF3 mo3 HV3 HA3 SB3 LR3 U21 U1 U10 K4c.
        pose proof LR3 as (V2 & V4 & V8 & V9 & V18 & V19 & V20).
        destruct (ti_aux _ _ TI1) as [B' [AUX1 HB']]. destruct (ti_errno _ _ TI1) as [errv ERR].
        assert (MP3 : as_MPRES H mo0 mo3).
        { eapply (ah_mpres_trans H HH); [exact MP1|]. eapply (ah_mpres_trans H HH); apply (adl_sb H DL); [exact SB2 | exact SB3]. }
        change (Z_to_bv 64 0xba108) with (Z_to_bv 64 AMALLOC_STUB) in HV3.
        eapply (amalloc_call H HH DL regs3 mem1 msF3 mo3 s0 LB N (bv_unsigned sp - ATR_STACK) B' errv 0xe8728 [] _ HV3 HA3 U1);
          [ lia | reflexivity | exact V4 | exact U10 | lia | exact RH1
          | apply (ah_alloc H HH s0 LB mem1 N RH1); [lia | unfold ADRV_LIVE in LIVE; lia | unfold ADRV_CNT in LIVE; lia]
          | rewrite HCOST in HAL; pose proof (fuzz_cost_nonneg N ltac:(lia)); nia
          | exact AUX1 | rewrite V2, u_small by lia; lia
          | rewrite V2, u_small by lia; exact (atinv_stklo _ mem1 TI1)
          | unfold ATR_STACK; lia | rewrite V2, u_small by lia; unfold AMALLOC_STACK, ATR_STACK; lia
          | rewrite V2, u_small by lia; unfold ATR_STACK; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
          | rewrite V4; unfold AERRNO; rewrite u_small by (unfold ATP; lia); exact ERR | exact (ti_inv _ _ TI1) | exact (ti_ac _ _ TI1)
          | apply (ah_chain_nil H HH); rewrite V8, u_small by lia; lia
          | cbn [map snd]; destruct TRC as (_ & _ & _ & _ & T5 & _); exact T5 |].
        intros regs4 mem4 msF4 mo4 D pD s4 errv4 junk HV4 HA4 MP4 KEPT W10 INV4 STK4 ERR4 AUX4 HP4 HBR4 RH4 CB4 AD4 AC4 HAL4.
        rewrite V2, u_small in STK4, HP4 by lia. rewrite V4 in ERR4.
        pose proof HBR4 as (D1 & D2 & D3 & D4 & D5 & D6 & D7). unfold AIMG_TOP in D4.
        assert (TI4 : atinv (adrv_cellsT_of 0) mem4).
        { eapply (atinv_apres 0 mem1 mem4 LB B' _ TB0); try assumption.
          - rewrite u_small in ERR4 by (unfold ATP; lia). exact ERR4.
          - eapply (RFS_via_apres H HH); [exact (ti_rfs _ _ TI1) | exact HP4].
          - intros shi SH. eapply stack0_xpres; [apply xpres_of_apres; exact HP4 | exact SH | constructor]. }
        assert (TF4 : tframe sp mem4 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)).
        { eapply atframe_agree; [exact TF1|]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP4 _ (u64_range x) ltac:(left; lia))). }
        assert (ST4 : sto 0 mem4) by (eapply (sto_apres 0); [lia | exact ST1 | exact HP4]).
        pose proof (ti_data _ _ TI4) as DATA4.

        pose proof (KEPT 2%bv ltac:(in_solve)) as S2. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
        pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 19%bv ltac:(in_solve)) as S19.
        pose proof (KEPT 20%bv ltac:(in_solve)) as S20. pose proof (KEPT 21%bv ltac:(in_solve)) as S21.
        assert (LR4 : regs138 sp regs4 (Z_to_bv 64 N) (Z_to_bv 64 PL) (Z_to_bv 64 cfg) (Z_to_bv 64 CP)).
        { unfold regs138. rewrite S2, S4, S8, S9, S18, S19, S20. exact LR3. }
        eapply (seg_T3 H DL sp SP16 SPlo SPhi s4 msF4 mo4 regs4 mem4 _ _ _ _ _ (Z_to_bv 64 D) _ LR4 ltac:(rewrite S21; exact U21) W10 ltac:(rewrite u_small by lia; lia)
                  (atinv_stk128 _ mem4 TI4) (atinv_ro _ mem4 TI4) (ti_relro _ _ TI4) (atinv_latch _ mem4 TI4)); [| exact HV4 | exact HA4].
        intros regs5 msF5 mo5 HV5 HA5 SB5 LR5 X21 X1 X10 X11 X12 K4d.
        pose proof LR5 as (Y2 & Y4 & Y8 & Y9 & Y18 & Y19 & Y20).

        assert (DJ0 : D + N + 16 <= A \/ A + cap + 16 <= D).
        { assert (Hp : pD <> p).
          { intros E. subst pD. pose proof (ah_nodup H HH _ _ _ RH4) as ND. cbn [map blk_id fst] in ND. inversion ND as [|x l Hni Hnd]; subst.
            apply Hni. replace p with (blk_id (p, A, cap)) by reflexivity. apply in_map. exact BLK. }
          pose proof (ah_disj H HH _ _ _ (pD, D, N) (p, A, cap) RH4 ltac:(left; reflexivity) ltac:(right; exact BLK) Hp) as DJ.
          cbn [blk_addr blk_size fst snd] in DJ. exact DJ. }
        assert (DISJ : PL + N <= D \/ D + N <= PL) by (subst PL N cfg; unfold hdr_payload_len in *; lia).
        assert (SRC : rdn RSEGS mem4 (Z_to_bv 64 PL) (length ds) = Some ds).
        { subst ds PL. rewrite Hds.
          pose proof (rdn_skipn RSEGS mem4 (length data) (Z_to_bv 64 A) data (Z.to_nat (6 + cfg)) DATA4 ltac:(lia)) as R.
          unfold nat_to_word in R. rewrite lit_add_lit, Z2Nat.id in R by lia.
          replace (A + 2 + hdr_cfg data + 4) with (A + (6 + cfg)) by (subst cfg; lia).
          eapply rdn_firstn; [exact R | subst N cfg; unfold hdr_payload_len; lia]. }
        assert (HPL : A + 6 <= PL /\ PL + N <= A + cap /\ PL + N = A + Z.of_nat (length data)).
        { subst PL N cfg. unfold hdr_payload_len in *. lia. }
        destruct HPL as (PL1 & PL2 & PL3).
        change (Z_to_bv 64 0xb8580) with (Z_to_bv 64 AMEMCPY_STUB) in HV5.
        eapply (amemcpy_call regs5 mem4 msF5 mo5 s4 (bv_unsigned sp - 80) D PL N (bv_unsigned sp - ATR_STACK) ds junk 0xe873c _ HV5 HA5 X1);
          [ lia | reflexivity | exact Y2 | exact X10 | exact X11 | exact X12
          | apply ardn_bytes_at; [exact SRC | lia | rewrite Hds; lia]
          | exact Hds | exact CB4 | exact DISJ | lia | lia | lia
          | eapply addressable_accessible; [exact (ti_addr _ _ TI4) | lia | lia | unfold AAPP_HI; lia]
          | eapply addressable_accessible; [exact AD4 | lia | lia | unfold AAPP_HI; lia]
          | eapply shvis_sub; [eapply (ah_blk_shvis H HH); [exact RH4 | right; exact BLK] | lia | lia | lia | lia | lia]
          | eapply (ah_blk_shvis H HH); [exact RH4 | left; reflexivity]
          | eapply aapp_in_app_mem; [exact B7 | lia | lia]
          | eapply aapp_in_app_mem; [exact D7 | lia | lia]
          | eapply aconst_ok_aapp; [exact D7 | lia | lia]
          | exact (atinv_stklo _ mem4 TI4) | unfold ATR_STACK; lia | unfold ATR_STACK; lia | lia
          | left; unfold ATR_STACK; lia | left; unfold ATR_STACK; lia
          | exact (ti_inv _ _ TI4) | exact (ti_ac _ _ TI4) |].
        intros regs6 mem5 msF6 mo6 HV6 HA6 MP6 KEEP6 Z10 MU5 WM5 INV5 STK5 CB5 BY5 AC5.
        assert (TI5 : atinv (adrv_cellsT_of 0) mem5).
        { eapply (atinv_copy 0 mem4 mem5 D N ((pD, D, N) :: LB) s4 TB0 TI4 MU5 WM5 INV5 STK5 AC5 HBR4 ltac:(clear -DJ0; lia) RH4); [right; exact BLK | exists pD; left; reflexivity]. }
        assert (TF5 : tframe sp mem5 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)).
        { eapply atframe_agree; [exact TF4|]. intros x Hx. apply MU5. cbn. lia. }
        assert (CW : Forall (aclient_write_ok H ((pD, D, N) :: LB)) [(D, D + N); (bv_unsigned sp - 80 - 4096, bv_unsigned sp - 80)]%Z).
        { constructor; [| constructor; [| constructor]].
          - right; right; left. exists (pD, D, N). split; [left; reflexivity | cbn; lia].
          - left. cbn. lia. }
        assert (RH5 : as_RHEAP H s4 ((pD, D, N) :: LB) mem5).
        { eapply (ah_RHEAP_frame H HH); [exact RH4 | exact MU5 | exact WM5 | exact CW]. }
        assert (ST5 : sto 0 mem5).
        { cbn [sto]. eapply cells_ok_munch; [apply astdout0_wf | exact ST4 | exact MU5 |].
          eapply Forall_impl; [| apply astdout0_range]. intros [[a w] v] Ra. cbn. lia. }
        assert (CPY5 : rdn RSEGS mem5 (Z_to_bv 64 D) (length ds) = Some ds).
        { pose proof (rw_rdn mem5 D _ CB5) as R. cbn [cells_size csize cells_bytes cbytes Nat.add] in R.
          rewrite Nat.add_0_r, app_nil_r, <- Hds in R. exact R. }
        assert (AD5 : addressable mem5 D N).
        { eapply addressable_transport; [exact AD4 | exact MU5 | exact WM5 |].
          pose proof (aapp_disjoint_sh D N D N D7 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as SD.
          pose proof (sh_nsh_high D N ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)).
          cbn. unfold AHI_LO in *. repeat split; lia. }
        assert (MP6' : as_MPRES H mo0 mo6).
        { eapply (ah_mpres_trans H HH); [exact MP3|]. eapply (ah_mpres_trans H HH); [exact MP4|].
          eapply (ah_mpres_trans H HH); [apply (adl_sb H DL); exact SB5 | exact MP6]. }
        pose proof (KEEP6 2%bv ltac:(in_solve)) as T2. pose proof (KEEP6 4%bv ltac:(in_solve)) as T4. pose proof (KEEP6 8%bv ltac:(in_solve)) as T8.
        pose proof (KEEP6 9%bv ltac:(in_solve)) as T9. pose proof (KEEP6 18%bv ltac:(in_solve)) as T18. pose proof (KEEP6 19%bv ltac:(in_solve)) as T19.
        pose proof (KEEP6 20%bv ltac:(in_solve)) as T20. pose proof (KEEP6 21%bv ltac:(in_solve)) as T21.
        assert (LR6 : regs138 sp regs6 (Z_to_bv 64 N) (Z_to_bv 64 PL) (Z_to_bv 64 D) (Z_to_bv 64 CP)).
        { unfold regs138. rewrite T2, T4, T8, T9, T18, T19, T20. exact LR5. }
        eapply (seg_T4 H DL sp SP16 SPlo SPhi s4 msF6 mo6 regs6 mem5 _ _ (Z_to_bv 64 cfg) _ _ _ _ LR6 ltac:(rewrite T21; exact X21)
                  (atinv_stk128 _ mem5 TI5) (atinv_ro _ mem5 TI5) (ti_relro _ _ TI5) (atinv_latch _ mem5 TI5)); [| exact HV6 | exact HA6].
        intros regs7 msF7 mo7 HV7 HA7 SB7 LR7 Z21 K4e.
        eapply (tr_loop D D [(pD, D, N)] ltac:(right; split; [lia | split; [reflexivity | exists pD; split; [reflexivity | exact HBR4]]]) K HPOST
                  regs7 mem5 msF7 mo7 s4 ((pD, D, N) :: LB) HV7 HA7); [| exact K0].
        split; try assumption.
        + rewrite ECALLS. exact Z21.
        + intros rr Hrr. rewrite (K4e rr Hrr), (KEEP6 rr) by (unfold aheap_kept; in_from Hrr).
          rewrite (K4d rr Hrr), (KEPT rr) by (unfold aheap_kept; in_from Hrr).
          rewrite (K4c rr Hrr), (K4b rr Hrr). apply K4a. exact Hrr.
        + apply Permutation_refl.
        + eapply (ah_mpres_trans H HH); [exact MP6' | apply (adl_sb H DL); exact SB7].
        + intros _. exact CB5.
        + intros _. exact AD5.
        + unfold spent. lia.
    Qed.

  End Call.

  Theorem as_target_run : as_target_run_stmt H FZP.
  Proof.
    intros sp A cap data p s LB msF mo regs mem K PRE K0 HPOST.
    exact (as_target_run_ok sp A cap data p s LB msF mo regs mem PRE K K0 HPOST).
  Qed.
End TR.

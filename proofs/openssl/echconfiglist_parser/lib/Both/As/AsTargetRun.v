(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts AgentLib
  SymExec2 SymExec2Sound SymRun SymDriveX MemSplit Spec LibTail RefPrintfLib RefMemcpyLib
  SReach RegsEquivM MainEqv HeapCeil LazyRestrict LazySR MainWalk_defs MainSegs MainMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep Exec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0 AsAuxv
  ECH_Xpres ECH_Iface AsCall AsCallX RefExitBase AsPrintfFirst AsPrintfBuf
  AsDrvHeap AsDrvRun AsDrvIO AsDrvFuzz AsDrvMem AsDrvDefs AsTRWalk_defs AsTRSegs.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac in_solve := cbn [In]; repeat (first [ left; reflexivity | right ]).
Ltac in_from H := cbn [In] in H; decompose [or] H; clear H; try contradiction; subst; in_solve.

Lemma lb_bytes_perm : forall LB LB', Permutation LB' LB -> lb_bytes LB' = lb_bytes LB.
Proof.
  intros LB LB' P. induction P; cbn [lb_bytes fold_right] in *; try lia;
    try (fold (lb_bytes l) (lb_bytes l') in *; lia); try (fold (lb_bytes l); lia).
Qed.

(* [comment removed for export] *)
Lemma ardn_S : forall m (a : word) n bs,
  rdn RSEGS m a (S n) = Some bs ->
  exists b r, bs = b :: r /\ mrd asegs m a = Some b /\ rdn RSEGS m (a + 1)%bv n = Some r.
Proof.
  intros m a n bs HR. change (rdn RSEGS) with (OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.rdn asegs) in HR |- *.
  rewrite rdn_unfold in HR. destruct (mrd asegs m a) as [b|]; [|discriminate].
  destruct (OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.rdn asegs m (a + 1)%bv n) as [r|]; [|discriminate].
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
  Variable L : alib.
  Hypothesis LOK : alib_ok L.
  Hypothesis FZ : fuzz_stmt H L.

  Let rom := seg_rom asegs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Call.
    Variables (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s0 : as_St H) (LB : list block)
              (msF0 : machine_state) (mo0 : Model) (regs0 : bvmap 5 word) (mem0 : word -> option byte).
    Hypothesis PRE : ATRpre H L sp A cap data p s0 LB msF0 mo0 regs0 mem0.

    Let cfg : Z := hdr_cfg data.
    Let N : Z := hdr_payload_len data.
    Let CP : Z := A + 2.
    Let PL : Z := A + 2 + hdr_cfg data + 4.
    (* [comment removed for export] *)
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

    (* [comment removed for export] *)
    Definition atr_region (r : word * Z) : Prop :=
      (bv_unsigned sp - ATR_STACK <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= bv_unsigned sp /\ 0 <= snd r)
      \/ (0x5ede88 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0x5edf70 /\ 0 <= snd r)
      \/ (0xc027a8 <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= 0xc027b0 /\ 0 <= snd r)
      \/ (bv_unsigned (fst r) = 0xbdcf50 /\ snd r = 1)
      \/ (bv_unsigned (fst r) = 0xbdcf54 /\ snd r = 1)
      \/ ((bv_unsigned (fst r) = 0xc01ce8 /\ snd r = 4) \/ (bv_unsigned (fst r) = 0xc01d08 /\ snd r = 8) \/ (bv_unsigned (fst r) = 0xc01e08 /\ snd r = 8)).

    Record atinv (m : word -> option byte) : Prop := ATI {
      ti_inv   : mem_inv asegs m;
      ti_stk   : stk asegs m (bv_unsigned sp - ATR_STACK) (bv_unsigned sp);
      ti_ac    : ACONST m;
      ti_relro : arelro_none m;
      ti_glb   : aglb_none m;
      ti_cells : cells_ok m adrv_cells;
      ti_tid   : exists t, atid_cell m t;
      ti_errno : exists e, rw_cells asegs m AERRNO [C4 e];
      ti_can   : exists can, acanary m can;
      ti_rfs   : as_RFS H [] m;
      ti_sh0   : exists shi, stack0 m (bv_unsigned sp - ATR_STACK) shi /\ bv_unsigned sp <= shi;
      ti_above : forall a : word, bv_unsigned sp <= bv_unsigned a -> m a = mem0 a;
      ti_aux   : exists B', as_rauxv_ok H m B' /\ bv_unsigned sp + 128 <= B' < 2 ^ 64 /\ aauxv_ok m B';   (* [comment removed for export] *)
      ti_addr  : addressable m A cap;
      ti_data  : rdn RSEGS m (Z_to_bv 64 A) (length data) = Some data;
      ti_cb    : exists junk, rw_cells asegs m A [CB (Z.to_nat cap) junk] }.

    Lemma adrv_cells_wf : forallb cell_wf_b adrv_cells = true. Proof. vm_compute. reflexivity. Qed.
    Lemma adrv_cells_range :
      Forall (fun c : Z * nat * Z => match c with (a, w, _) =>
        ((0x5ea840 <= a /\ a + Z.of_nat w <= 0x5edd3c) \/ (a = 0x6a7290 /\ w = 1%nat) \/ (0xc01ce0 <= a /\ a + Z.of_nat w <= 0xc01f24) \/ (a = 0xc02388 /\ w = 8%nat))
        /\ (a + Z.of_nat w <= 0xc01ce8 \/ 0xc01cec <= a) /\ (a + Z.of_nat w <= 0xc01d08 \/ 0xc01d10 <= a) /\ (a + Z.of_nat w <= 0xc01e08 \/ 0xc01e10 <= a) end) adrv_cells.
    Proof. unfold adrv_cells. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; (first [clear; (first [clear; lia | lia]) | lia])|]). apply Forall_nil. Qed.
    Lemma astdout0_wf : forallb cell_wf_b astdout0 = true. Proof. vm_compute. reflexivity. Qed.

    (* [comment removed for export] *)
    Lemma blkA : ablock_range H A cap.
    Proof. exact (ah_blocks H HH _ _ _ _ (atr_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) (atr_blk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE)). Qed.

    Lemma atinv_frame : forall m m' rs,
      atinv m -> frame_mod m m' rs -> (forall r, In r rs -> atr_region r) -> atinv m'.
    Proof.
      intros m m' rs [INV STK AC RELRO GLB CELLS [t TID] [e ERR] [can [CAN CAN64]] RFS [shi [SH0 Hshi]] ABOVE [B' [AUX [HB' AUXV]]] ADDR DATA [junk JCB]] FM RS.
      pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. acb. unfold ATR_STACK in HCL.
      pose proof FM as [Hout Hg]. unfold atr_region, ATR_STACK in RS.
      pose proof (frame_mod_munch _ _ _ FM) as MU. pose proof (aframe_mod_wmono _ _ _ FM) as WM.
      pose proof blkA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
      assert (IVS : forall iv, In iv (ivls rs) -> exists r, In r rs /\ iv = (bv_unsigned (fst r), bv_unsigned (fst r) + snd r)).
      { intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr). eauto. }
      split.
      - eapply amem_inv_frame; [exact INV | exact FM |]. apply Forall_forall. intros r Hr. pose proof (u64_range (fst r)). destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
      - apply (astk_grows m m'); [exact STK | unfold AIMG_TOP in *; lia | lia | exact Hg].
      - eapply ACONST_frame; [exact AC | exact MU | exact WM |].
        apply Forall_forall. intros iv Hiv. destruct (IVS iv Hiv) as (r & Hr & ->).
        destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; [apply aconst_ok_hi; unfold AHI_LO; lia | | | | |];
          apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
            AF_DCO_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP in *;
            rewrite ?ASHADOW_BASE_val; cbn [fst snd]; (first [clear - X; lia | lia]).
      - refine (arange_none_frame m m' rs _ _ RELRO FM _ _ _); [| lia | lia]. intros r Hr. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
      - destruct GLB as [G1 G2]. split.
        + refine (arange_none_frame m m' rs _ _ G1 FM _ _ _); [| lia | lia]. intros r Hr. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
        + refine (arange_none_frame_hole m m' rs _ _ _ _ G2 FM _ _ _); [| lia | lia].   (* [comment removed for export] *) intros r Hr. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
      - eapply acells_ok_frame; [apply adrv_cells_wf | exact CELLS | exact FM |].
        eapply Forall_impl; [| apply adrv_cells_range]. intros [[a w] v] Ra r Hr. cbn [fst snd].
        destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | (first [clear - X Ra ACEILB HCL; lia | lia])].
      - exists t. destruct TID as [TID Ht]. split; [|exact Ht]. eapply ardn_frame; [exact FM | exact TID | lia | cbn; lia |].
        intros r Hr. cbn. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
      - exists e. eapply arw_cells_frame; [exact ERR | exact FM |]. intros r Hr. cbn. unfold AERRNO, ATP. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
      - exists can. split; [|exact CAN64]. eapply ardn_frame; [exact FM | exact CAN | lia | cbn; lia |].
        intros r Hr. cbn. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
      - pose proof (ah_RFS_range H HH _ _ RFS) as [(F1 & F2 & F3 & F4) _].
        eapply (ah_RFS_frame H HH); [exact RFS | exact MU | exact WM |].
        apply Forall_forall. intros iv Hiv. destruct (IVS iv Hiv) as (r & Hr & ->). unfold afs_write_ok. left. cbn [fst snd].
        unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
      - exists shi. split; [|exact Hshi]. eapply stack0_transport; [exact SH0 | exact MU | exact WM |].
        apply Forall_forall. intros iv Hiv. destruct (IVS iv Hiv) as (r & Hr & ->). unfold stack0_ok. cbn [fst snd].
        assert (SHT : 0x80178800 <= sh aceil).
        { unfold sh. rewrite ASHADOW_BASE_val. assert (A8 : 0 < 8) by lia. assert (ACL : 0x7fff7f800000 <= aceil) by lia.
          pose proof (Z.div_le_mono _ _ _ A8 ACL) as DM.
          change (0x7fff7f800000 / 8) with 0xfffeff00000 in DM. lia. }
        unfold AHI_LO. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
      - intros a Ha. rewrite <- (ABOVE a Ha). apply Hout. apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
      - exists B'. split; [|split; [exact HB'|]].
        + eapply (ah_rauxv_frame H HH LB); [exact AUX | exact MU | exact WM |].
          apply Forall_forall. intros iv Hiv. destruct (IVS iv Hiv) as (r & Hr & ->). unfold aclient_write_ok, aimg_client_w. cbn [fst snd].
          unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ALIBC_PGSZ, ATP in *. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
        + eapply aauxv_ok_frame; [exact AUXV | exact MU | exact WM |].
          apply Forall_forall. intros iv Hiv. destruct (IVS iv Hiv) as (r & Hr & ->). unfold aauxv_win_ok, AAUXV_CELL. cbn [fst snd].
          destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL HB'; lia | lia].
      - eapply addressable_transport; [exact ADDR | exact MU | exact WM |].
        assert (SHR : (0x80178800 <= sh A /\ sh A + nsh cap <= 0x8fff6e00) \/ (0x2008fff7000 <= sh A /\ sh A + nsh cap <= sh aceil /\ sh aceil < AHI_LO)).
        { destruct BA7 as [P|P]; [left; exact (sh_aapp_lo_range A cap P BA3) | right; exact (sh_aapp_hi_range A cap P BA3)]. }
        assert (SHT : sh aceil <= 0x10007fff7000).
        { unfold sh. rewrite ASHADOW_BASE_val. assert (A8 : 0 < 8) by lia. assert (ACL : aceil <= 0x7fffff800000) by lia.
          pose proof (Z.div_le_mono _ _ _ A8 ACL) as DM. change (0x7fffff800000 / 8) with 0xffffff00000 in DM. lia. }
        clear - RS SHR SHT SPlo. induction rs as [|[r k] rs IH]; [exact I|]. cbn. split.
        + pose proof (RS (r, k) (or_introl eq_refl)) as X. cbn [fst snd] in X. unfold AHI_LO in SHR. destruct X as [X|[X|[X|[X|[X|X]]]]]; lia.
        + apply IH. intros r' Hr'. apply RS. right. exact Hr'.
      - eapply ardn_frame; [exact FM | exact DATA | lia | pose proof (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE); acb; lia |].
        intros r Hr. pose proof (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). unfold AIMG_TOP in *. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
      - exists junk. eapply arw_cells_frame; [exact JCB | exact FM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        intros r Hr. unfold AIMG_TOP in *. destruct (RS r Hr) as [X|[X|[X|[X|[X|X]]]]]; first [clear - X HCL; lia | lia].
    Qed.

    (* [comment removed for export] *)
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
      forallb cell_wf_b cs = true -> cells_ok m cs -> apres H LB1 SP m m' ->
      Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x end) cs ->
      cells_ok m' cs.
    Proof.
      intros LB1 SP m m' cs Hwf Hc HP Hd. unfold cells_ok in *.
      induction cs as [|[[a w] v] cs IH]; [constructor|].
      cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
      inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
      unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
      repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
      unfold cell_ok in *. eapply rdn_apres; [exact HP | exact Hok | lia | lia |]. intros y Hy. right; left. apply Hx. exact Hy.
    Qed.

    Lemma adrv_cells_client :
      Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x end) adrv_cells.
    Proof using HCEIL H sp A cap data p s0 LB msF0 mo0 regs0 mem0 PRE. unfold adrv_cells, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; (first [clear - H0; lia | lia])|]). apply Forall_nil. Qed.
    Lemma astdout0_client :
      Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x end) astdout0.
    Proof. unfold astdout0, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil. Qed.

    (* [comment removed for export] *)
    Lemma atinv_apres : forall m m' LB1 B2 e',
      atinv m -> apres H LB1 (bv_unsigned sp - 80) m m' -> In (p, A, cap) LB1 ->
      mem_inv asegs m' -> stk asegs m' (bv_unsigned sp - ATR_STACK) (bv_unsigned sp - 80) -> ACONST m' ->
      as_rauxv_ok H m' B2 -> bv_unsigned sp + 128 <= B2 < 2 ^ 64 -> aauxv_ok m' B2 ->
      rw_cells asegs m' AERRNO [C4 e'] -> as_RFS H [] m' ->
      (forall shi, stack0 m (bv_unsigned sp - ATR_STACK) shi -> stack0 m' (bv_unsigned sp - ATR_STACK) shi) ->
      atinv m'.
    Proof.
      intros m m' LB1 B2 e' [INV STK AC RELRO GLB CELLS [t [TID Ht]] ERR [can [CAN CAN64]] RFS [shi [SH0 Hshi]] ABOVE AUX ADDR DATA [junk JCB]]
             HP HIn INV' STK' AC' AUX' HB2 AUXV' ERR' RFS' SH'.
      pose proof SPlo. pose proof SPhi.
      assert (AG : forall x : word, bv_unsigned sp - 80 <= bv_unsigned x -> m' x = m x).
      { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP _ (u64_range x) ltac:(left; lia))). }
      split; try assumption.
      - destruct STK as (S1 & S2 & S3). destruct STK' as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
        intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp - 80)) as [Lc|Lc]; [apply S3'; lia|].
        assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by lia; lia).
        unfold wview, mrd. rewrite E. apply S3. lia.
      - intros i Hi. rewrite <- (RELRO i Hi). rewrite <- wa_eq.
        assert (Hi64 : 0 <= i < 2 ^ 64) by lia.
        exact (proj1 (HP i Hi64 ltac:(right; left; unfold aimg_client; lia))).
      - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq;
          (assert (Hi64 : 0 <= i < 2 ^ 64) by lia); exact (proj1 (HP i Hi64 ltac:(right; left; unfold aimg_client; lia))).
      - eapply cells_ok_apres; [apply adrv_cells_wf | exact CELLS | exact HP | apply adrv_cells_client].
      - exists t. split; [|exact Ht]. eapply rdn_apres; [exact HP | exact TID | lia | cbn; lia |]. intros x Hx. right; left. unfold aimg_client. cbn in Hx. lia.
      - exists e'. exact ERR'.
      - exists can. split; [|exact CAN64]. eapply rdn_apres; [exact HP | exact CAN | lia | cbn; lia |]. intros x Hx. right; left. unfold aimg_client. cbn in Hx. lia.
      - exists shi. split; [apply SH'; exact SH0 | exact Hshi].
      - intros a Ha. rewrite <- (ABOVE a Ha). apply AG. lia.
      - exists B2. split; [assumption | split; assumption].
      - eapply apres_addressable; [exact HP | exact ADDR | exact HIn].
      - pose proof (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as HC. pose proof blkA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
        eapply rdn_apres; [exact HP | exact DATA | lia | acb; lia |].
        intros x Hx. right; right; left. exists (p, A, cap). split; [exact HIn | cbn; lia].
      - exists junk. eapply apres_rw_cells; [exact HP | exact JCB |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (pose proof blkA as (_ & _ & B3 & _); exact B3).
        eapply aclient_range_block; [exact HIn | lia | lia].
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

    (* [comment removed for export] *)
    Definition sto (j : nat) (m : word -> option byte) : Prop :=
      match j with O => cells_ok m astdout0 | S k => astdout_after m k end.

    (* [comment removed for export] *)
    Definition quiet_region (r : word * Z) : Prop :=
      (bv_unsigned sp - ATR_STACK <= bv_unsigned (fst r) /\ bv_unsigned (fst r) + snd r <= bv_unsigned sp /\ 0 <= snd r)
      \/ (bv_unsigned (fst r) = 0xbdcf50 /\ snd r = 1)
      \/ (bv_unsigned (fst r) = 0xbdcf54 /\ snd r = 1)
      \/ ((bv_unsigned (fst r) = 0xc01ce8 /\ snd r = 4) \/ (bv_unsigned (fst r) = 0xc01d08 /\ snd r = 8) \/ (bv_unsigned (fst r) = 0xc01e08 /\ snd r = 8)).
    Lemma quiet_atr : forall r, quiet_region r -> atr_region r.
    Proof. intros r [X|[X|[X|X]]]; unfold atr_region; tauto. Qed.

    Lemma astdout0_range : Forall (fun c : Z * nat * Z => match c with (a, w, _) => 0x5ede88 <= a /\ a + Z.of_nat w <= 0x5edf1c end) astdout0.
    Proof. unfold astdout0. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.

    Lemma sto_frame : forall j m m' rs, (j <= 4)%nat -> sto j m -> frame_mod m m' rs -> (forall r, In r rs -> quiet_region r) -> sto j m'.
    Proof.
      intros j m m' rs Hj ST FM RS. pose proof SPlo. unfold quiet_region, ATR_STACK in RS. destruct j as [|k]; cbn [sto] in *.
      - eapply acells_ok_frame; [apply astdout0_wf | exact ST | exact FM |].
        eapply Forall_impl; [| apply astdout0_range]. intros [[a w] v] RR r Hr. cbn [fst snd]. destruct (RS r Hr) as [X|[X|[X|X]]]; lia.
      - destruct ST as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 LBF].
        assert (T : forall (a : Z) (n : nat) bs, 0x5ede88 <= a -> a + Z.of_nat n <= 0xc02ba8 -> (a + Z.of_nat n <= 0x5edf58 \/ 0xc027a8 <= a) ->
                  rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Ha Hn Hor HD. eapply ardn_frame; [exact FM | exact HD | lia | lia |]. intros r Hr. destruct (RS r Hr) as [X|[X|[X|X]]]; lia. }
        split; (eapply T; [ | | | eassumption]); cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]; (first [clear - Hj; lia | lia]).
    Qed.

    Lemma sto_apres : forall j m m' LB1, (j <= 4)%nat -> sto j m -> apres H LB1 (bv_unsigned sp - 80) m m' -> sto j m'.
    Proof.
      intros j m m' LB1 Hj ST HP. pose proof SPlo. destruct j as [|k]; cbn [sto] in *.
      - eapply cells_ok_apres; [apply astdout0_wf | exact ST | exact HP | apply astdout0_client].
      - destruct ST as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 LBF].
        split; (eapply rdn_apres; [exact HP | eassumption | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]; lia |]);
          intros x Hx; right; left; unfold aimg_client, ATLS_PRIV_LO, ATP; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul] in Hx; (first [clear - Hds Hcalls Hx SPlo Hj; lia | lia]).
    Qed.

    Lemma atinv_stk128 : forall m, atinv m -> stk_ok RSEGS m sp 128.
    Proof. intros m TI. pose proof SPlo. pose proof SPhi. eapply astk_stk_ok; [exact (ti_stk _ TI) | unfold ATR_STACK; lia | lia | lia | lia]. Qed.
    Lemma atinv_stklo : forall m, atinv m -> stk asegs m (bv_unsigned sp - ATR_STACK) (bv_unsigned sp - 80).
    Proof. intros m TI. destruct (ti_stk _ TI) as (S1 & S2 & S3). split; [exact S1|]. split; [lia|]. intros a Ha. apply S3. lia. Qed.
    Lemma atinv_ro : forall m, atinv m -> aro_none m.
    Proof. intros m TI. exact (amem_inv_ro_none m (ti_inv _ TI)). Qed.
    Lemma atinv_latch : forall m, atinv m -> latch_ok m.
    Proof.
      (* [comment removed for export] *)
      intros m TI. split; intros a n Ha Hn; apply store_ok_data; rewrite !u_small in * by lia; lia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
(* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma fuzz_cost_nonneg : forall n, 0 <= n -> 0 <= fuzz_cost H L n.
    Proof.
      intros n Hn. unfold fuzz_cost. exact (alo_cost0 L LOK H n HH Hn).   (* [comment removed for export] *)
    Qed.

    (* [comment removed for export] *)
    Definition xfar (XS : list (Z * Z)) : Prop := Forall (fun iv : Z * Z => AIMG_TOP <= fst iv /\ snd iv <= aceil) XS.

    Lemma scratch_iv : forall m iv, as_RFS H [] m -> fs_scratch H [] iv -> AIMG_TOP <= fst iv /\ snd iv <= aceil.
    Proof.
      intros m iv RFS SC. pose proof (ah_RFS_range H HH _ _ RFS) as [(F1 & F2 & F3 & F4) _]. acb.
      destruct SC as [-> | (k & ff & fp & FF & E)]; [cbn; unfold AFS_FLAGS, AFS_SIZE in *; lia|].
      pose proof (fresh_frame_facts H _ _ _ _ FF) as (Kk & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)) as FP. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
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

    (* [comment removed for export] *)
    Definition xsafe (X : list (Z * Z)) : Prop := forall a, rin_ivs X a -> alibw_ok a \/ (AIMG_TOP <= a /\ a < aceil).
    Lemma xsafe_of_far : forall XS, xfar XS -> xsafe (AERRNO_X ++ al_LIBX L ++ XS).
    Proof.
      intros XS F a Ha. apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [left; right; cbn in Ha; unfold ATP in *; lia|].
      apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [left; left; exact (alo_libx L LOK a Ha)|].
      right. destruct (Z_lt_le_dec a AIMG_TOP) as [X|X]; [exfalso; exact (not_rin_far XS a F (or_introl X) Ha)|].
      destruct (Z_lt_le_dec a aceil) as [Y|Y]; [lia | exfalso; exact (not_rin_far XS a F (or_intror Y) Ha)].
    Qed.
    Lemma not_rin_safe : forall X a, xsafe X -> ~ alibw_ok a -> (a < AIMG_TOP \/ aceil <= a) -> ~ rin_ivs X a.
    Proof. intros X a SX NA Ha R. destruct (SX a R) as [K|K]; [exact (NA K) | lia]. Qed.
    Ltac nlibx := unfold alibw_ok, alibx_ok in *; lia.
    Lemma rin_ivs_In : forall X a iv, In iv X -> fst iv <= a < snd iv -> rin_ivs X a.
    Proof. intros X a iv HIn Ha. induction X as [|y X IH]; [destruct HIn|]. cbn. destruct HIn as [<-|HIn]; [left; exact Ha | right; exact (IH HIn)]. Qed.
    (* [comment removed for export] *)
    Lemma libx_low : Forall (fun iv : Z * Z => 0x5ed1a0 <= fst iv /\ snd iv <= 0xc03570) (al_LIBX L).
    Proof.
      apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) (alo_libx_wf L LOK) iv Hiv) as NE. cbn in NE.
      assert (R1 : rin_ivs (al_LIBX L) (fst iv)) by (apply (rin_ivs_In _ _ iv Hiv); lia).
      assert (R2 : rin_ivs (al_LIBX L) (snd iv - 1)) by (apply (rin_ivs_In _ _ iv Hiv); lia).
      pose proof (alo_libx L LOK _ R1) as W1. pose proof (alo_libx L LOK _ R2) as W2.
      unfold alibx_ok in W1, W2. lia.
    Qed.
    (* [comment removed for export] *)
    Lemma libx_miss : forall lo hi, 0xc03570 <= lo -> Forall (fun iv : Z * Z => hi <= fst iv \/ snd iv <= lo) (al_LIBX L).
    Proof. intros lo hi Hlo. eapply Forall_impl; [| apply libx_low]. cbn. intros iv [W1 W2]. lia. Qed.
    (* [comment removed for export] *)
    Lemma auxv_wins : forall XS B', xfar XS -> bv_unsigned sp <= B' -> Forall (aauxv_win_ok B') (AERRNO_X ++ al_LIBX L ++ XS).
    Proof.
      intros XS B' F HB'. pose proof SPlo. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb.
      apply Forall_app. split; [| apply Forall_app; split].
      - apply Forall_cons; [| apply Forall_nil]. unfold aauxv_win_ok, AAUXV_CELL, ATP. cbn [fst snd]. lia.
      - apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) libx_low iv Hiv) as [W1 W2].
        pose proof (proj1 (Forall_forall _ _) (alo_libx_wf L LOK) iv Hiv) as NE. cbn in NE.
        unfold aauxv_win_ok. split; [lia|].
        destruct (Z_lt_le_dec (fst iv) (AAUXV_CELL + 8)) as [X1|X1]; [| right; lia].
        destruct (Z_lt_le_dec AAUXV_CELL (snd iv)) as [X2|X2]; [| left; lia]. exfalso.
        destruct (Z_lt_le_dec AAUXV_CELL (fst iv)) as [X3|X3].
        + assert (R : fst iv <= fst iv < snd iv) by lia.
          pose proof (alo_libx L LOK (fst iv) (rin_ivs_In _ _ iv Hiv R)) as K. unfold alibx_ok, AAUXV_CELL in K, X1, X3. clear - K X1 X3. lia.
        + assert (R : fst iv <= AAUXV_CELL < snd iv) by lia.
          pose proof (alo_libx L LOK AAUXV_CELL (rin_ivs_In _ _ iv Hiv R)) as K. unfold alibx_ok, AAUXV_CELL in K. clear - K. lia.
      - eapply Forall_impl; [| exact F]. intros iv [X1 X2]. unfold aauxv_win_ok, AAUXV_CELL, AIMG_TOP in *. clear - X1 X2 HCL HB'. lia.
    Qed.
    Lemma not_rin_of_Forall : forall XS a, Forall (fun iv : Z * Z => a < fst iv \/ snd iv <= a) XS -> ~ rin_ivs XS a.
    Proof.
      intros XS a F. induction XS as [|iv XS IH]; cbn; [tauto|].
      pose proof (Forall_inv F) as F1. cbn in F1. pose proof (Forall_inv_tail F) as F2. intros [R|R]; [lia | exact (IH F2 R)].
    Qed.

    (* [comment removed for export] *)
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

    Lemma cells_ok_xpres : forall LB1 SP XS m m' cs,
      forallb cell_wf_b cs = true -> cells_ok m cs -> xpres H LB1 SP XS m m' -> xsafe XS ->
      Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x /\ ~ alibw_ok x end) cs ->
      cells_ok m' cs.
    Proof.
      intros LB1 SP XS m m' cs Hwf Hc HP HF Hd. unfold cells_ok in *.
      induction cs as [|[[a w] v] cs IH]; [constructor|].
      cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
      inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
      unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
      repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
      unfold cell_ok in *. eapply rdn_xpres; [exact HP | exact Hok | lia | lia |]. intros y Hy.
      pose proof (Hx y Hy) as [CY NY]. split; [right; left; exact CY|]. apply not_rin_safe; [exact HF| exact NY |]. left. unfold aimg_client, AIMG_TOP in *. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma adrv_cells_clientx :
      Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x /\ ~ alibw_ok x end) adrv_cells.
    Proof using HCEIL H sp A cap data p s0 LB msF0 mo0 regs0 mem0 PRE L. unfold adrv_cells, aimg_client, alibw_ok, alibx_ok. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; (first [clear - H0; lia | lia])|]). apply Forall_nil. Qed.
    Lemma astdout0_clientx :
      Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x /\ ~ alibw_ok x end) astdout0.
    Proof. unfold astdout0, aimg_client, alibw_ok, alibx_ok. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil. Qed.

    (* [comment removed for export] *)
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

    (* [comment removed for export] *)
    Lemma atinv_xpres : forall m m' LB1 LBr XS sx m1 B2 e',
      atinv m -> xpres H LB1 (bv_unsigned sp - 80) (AERRNO_X ++ al_LIBX L ++ XS) m m' -> Forall (fs_scratch H []) XS -> as_RFS H [] m1 ->
      as_RHEAP H sx LBr m -> In (p, A, cap) LB1 -> (forall b, In b LB1 -> In b LBr) ->
      mem_inv asegs m' -> stk asegs m' (bv_unsigned sp - ATR_STACK) (bv_unsigned sp - 80) -> ACONST m' ->
      as_rauxv_ok H m' B2 -> bv_unsigned sp + 128 <= B2 < 2 ^ 64 -> aauxv_ok m' B2 ->
      rw_cells asegs m' AERRNO [C4 e'] -> as_RFS H [] m' ->
      (exists shi, stack0 m' (bv_unsigned sp - ATR_STACK) shi /\ bv_unsigned sp <= shi) ->
      atinv m'.
    Proof.
      intros m m' LB1 LBr XS sx m1 B2 e' [INV STK AC RELRO GLB CELLS [t [TID Ht]] ERR [can [CAN CAN64]] RFS SH0 ABOVE AUX ADDR DATA [junk JCB]]
             HP HSC RFS1 RH HIn SUBr INV' STK' AC' AUX' HB2 AUXV' ERR' RFS' SH'.
      pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb.
      pose proof (scratch_far m1 XS RFS1 HSC) as FAR. pose proof (xsafe_of_far XS FAR) as SAFE.
      pose proof (blk_scratch sx LBr m m1 XS p A cap RH (SUBr _ HIn) RFS1 HSC) as [BF BS].
      assert (AG : forall x : word, bv_unsigned sp - 80 <= bv_unsigned x -> m' x = m x).
      { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq.
        refine (proj1 (HP _ (u64_range x) _)). split; [left; lia|]. apply not_rin_safe; [exact SAFE | nlibx | right; lia]. }
      assert (IMG : forall x, aimg_client x -> ~ alibw_ok x -> 0 <= x < 2 ^ 64 -> m' (wa x) = m (wa x)).
      { intros x Hx Nx Hx64. refine (proj1 (HP x Hx64 _)). split; [right; left; exact Hx|]. apply not_rin_safe; [exact SAFE | exact Nx | left].
        unfold aimg_client, AIMG_TOP in *. lia. }
      split; try assumption.
      - destruct STK as (S1 & S2 & S3). destruct STK' as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
        intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp - 80)) as [Lc|Lc]; [apply S3'; lia|].
        assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by lia; lia).
        unfold wview, mrd. rewrite E. apply S3. lia.
      - intros i Hi. rewrite <- (RELRO i Hi). rewrite <- wa_eq. apply IMG; [unfold aimg_client; lia | nlibx | lia].
      - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq;
          apply IMG; first [lia | unfold aimg_client; lia | nlibx].
      - eapply cells_ok_xpres; [apply adrv_cells_wf | exact CELLS | exact HP | exact SAFE | apply adrv_cells_clientx].
      - exists t. split; [|exact Ht]. eapply rdn_xpres; [exact HP | exact TID | lia | cbn; lia |]. intros x Hx. cbn in Hx.
        split; [right; left; unfold aimg_client; lia|]. apply not_rin_safe; [exact SAFE | nlibx | left; unfold AIMG_TOP; lia].
      - exists e'. exact ERR'.
      - exists can. split; [|exact CAN64]. eapply rdn_xpres; [exact HP | exact CAN | lia | cbn; lia |]. intros x Hx. cbn in Hx.
        split; [right; left; unfold aimg_client; lia|]. apply not_rin_safe; [exact SAFE | nlibx | left; unfold AIMG_TOP; lia].
      - intros a Ha. rewrite <- (ABOVE a Ha). apply AG. lia.
      - exists B2. split; [assumption | split; assumption].
      - eapply (xpres_addressable H); [exact HP | exact ADDR |]. split; [eapply aclient_range_block_sh; exact HIn |].
        pose proof blkA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7). pose proof (sh_mono AIMG_TOP A ltac:(lia)) as SM.
        apply Forall_app. split.
        { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right. unfold ATP. unfold sh, AIMG_TOP in SM |- *. rewrite ASHADOW_BASE_val in SM |- *. lia. }
        apply Forall_app. split; [| exact BS].
        apply libx_miss. unfold sh, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. lia.
      - pose proof (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as HC. pose proof blkA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
        eapply rdn_xpres; [exact HP | exact DATA | lia | lia |].
        intros x Hx. split.
        + right; right; left. exists (p, A, cap). split; [exact HIn | cbn; lia].
        + intros R. apply rin_ivs_app in R. destruct R as [R|R]; [revert R; cbn; unfold ATP, AIMG_TOP in *; lia|].
          apply rin_ivs_app in R. destruct R as [R|R]; [pose proof (alo_libx L LOK x R); unfold AIMG_TOP in *; nlibx|].
          revert R. apply not_rin_of_Forall. eapply Forall_impl; [| exact BF]. cbn. intros iv Hiv. lia.
      - exists junk. eapply (xpres_rw_cells H); [exact HP | exact JCB |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (pose proof blkA as (_ & _ & B3 & _); exact B3).
        split; [eapply aclient_range_block; [exact HIn | lia | lia] |].
        pose proof blkA as (_ & _ & _ & BA4 & _).
        apply Forall_app. split; [apply Forall_cons; [| apply Forall_nil]; cbn [fst snd]; unfold ATP, AIMG_TOP in *; lia|].
        apply Forall_app. split; [| exact BF]. apply libx_miss. unfold AIMG_TOP in *. lia.
    Qed.

    Lemma sto_xpres : forall j m m' LB1 XS m1, (j <= 4)%nat -> sto j m -> xpres H LB1 (bv_unsigned sp - 80) (AERRNO_X ++ al_LIBX L ++ XS) m m' ->
      Forall (fs_scratch H []) XS -> as_RFS H [] m1 -> sto j m'.
    Proof.
      intros j m m' LB1 XS m1 Hj ST HP HSC RFS1. pose proof SPlo. pose proof (scratch_far m1 XS RFS1 HSC) as FAR. pose proof (xsafe_of_far XS FAR) as SAFE.
      destruct j as [|k]; cbn [sto] in *.
      - eapply cells_ok_xpres; [apply astdout0_wf | exact ST | exact HP | exact SAFE | apply astdout0_clientx].
      - destruct ST as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 LBF].
        split; (eapply rdn_xpres; [exact HP | eassumption | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]; lia |]);
          intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul] in Hx;
          (split; [right; left; unfold aimg_client, ATLS_PRIV_LO, ATP; lia | apply not_rin_safe; [exact SAFE | nlibx | left; unfold AIMG_TOP; lia]]).
    Qed.

    (* [comment removed for export] *)
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
      rewrite ov_rdn in RD. cbn [rdn Lib.PropExec.rdn] in RD. unfold mrd in RD.
      destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
      - cbn in RD. unfold TacX.b8 in RD. congruence.
      - exfalso. change asegs with RSEGS in RD. rewrite (aseg_rom_high (Z_to_bv 64 a)) in RD; [discriminate|].
        rewrite u_small; [lia | unfold AAPP_HI in *; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma rw_rdn : forall m a cs, rw_cells asegs m a cs -> rdn RSEGS m (Z_to_bv 64 a) (cells_size cs) = Some (cells_bytes cs).
    Proof.
      intros m a cs [[WF BA] _].
      pose proof (bytes_at_rdn asegs m a (cells_bytes cs) 0 (cells_size cs) BA) as R.
      rewrite Z.add_0_r, firstn_all2 in R; [| cbn [skipn]; rewrite cells_bytes_length by exact WF; lia].
      apply R. cbn [skipn]. rewrite cells_bytes_length by exact WF. lia.
    Qed.

    Lemma cell_of_C8 : forall m a v, rw_cells asegs m a [C8 (TacX.wz v)] -> cell_ok m (a, 8%nat, v).
    Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. unfold cell_ok. cbn [cells_size csize Nat.add] in R. rewrite R. cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity. Qed.
    Lemma cell_of_C4 : forall m a v, rw_cells asegs m a [C4 (TacX.wz v)] -> cell_ok m (a, 4%nat, v).
    Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. unfold cell_ok. cbn [cells_size csize Nat.add] in R. rewrite R. cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity. Qed.

    Lemma cells_of_C8C8 : forall m a v1 v2, rw_cells asegs m a [C8 (TacX.wz v1); C8 (TacX.wz v2)] -> 0 <= a -> a + 16 < 2 ^ 64 ->
      cell_ok m (a, 8%nat, v1) /\ cell_ok m (a + 8, 8%nat, v2).
    Proof.
      intros m a v1 v2 RC Ha Ha2. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. unfold cell_ok. split.
      - pose proof (rdn_firstn RSEGS m 16 (Z_to_bv 64 a) _ 8 R ltac:(lia)) as R1. rewrite R1. cbn [cells_bytes cbytes app].
        rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by (rewrite length_le8; lia). reflexivity.
      - pose proof (rdn_skipn RSEGS m 16 (Z_to_bv 64 a) _ 8 R ltac:(lia)) as R2. unfold nat_to_word in R2.
        change (16 - 8)%nat with 8%nat in R2. replace (Z.of_nat 8) with 8 in R2 by reflexivity. rewrite lit_add_lit in R2.
        rewrite R2. cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (drop_app_length' _ _ 8) by (rewrite length_le8; reflexivity). reflexivity.
    Qed.
    Lemma cells_of_C1C1 : forall m a v1 v2, rw_cells asegs m a [C1 (TacX.b8 v1); C1 (TacX.b8 v2)] -> 0 <= a -> a + 2 < 2 ^ 64 ->
      rdn RSEGS m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v1] /\ rdn RSEGS m (Z_to_bv 64 (a + 1)) 1 = Some [Z_to_bv 8 v2].
    Proof.
      intros m a v1 v2 RC Ha Ha2. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. split.
      - pose proof (rdn_firstn RSEGS m 2 (Z_to_bv 64 a) _ 1 R ltac:(lia)) as R1. rewrite R1. reflexivity.
      - pose proof (rdn_skipn RSEGS m 2 (Z_to_bv 64 a) _ 1 R ltac:(lia)) as R2. unfold nat_to_word in R2.
        change (2 - 1)%nat with 1%nat in R2. replace (Z.of_nat 1) with 1 in R2 by reflexivity. rewrite lit_add_lit in R2.
        rewrite R2. reflexivity.
    Qed.
    Lemma cell_of_C1 : forall m a v, rw_cells asegs m a [C1 (TacX.b8 v)] -> rdn RSEGS m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v].
    Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. rewrite R. reflexivity. Qed.

    Lemma cells_ok_In : forall m cs c, cells_ok m cs -> In c cs -> cell_ok m c.
    Proof. intros m cs c CO IN. exact (proj1 (Forall_forall _ _) CO _ IN). Qed.


    (* [comment removed for export] *)
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

    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    Lemma aheap_frame_tr : forall m m' s1 LB1 rs,
      as_RHEAP H s1 LB1 m -> frame_mod m m' rs -> (forall r, In r rs -> atr_region r) -> as_RHEAP H s1 LB1 m'.
    Proof.
      intros m m' s1 LB1 rs RH FM RS. pose proof SPlo. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb. unfold atr_region, ATR_STACK in RS.
      eapply (ah_RHEAP_frame H HH); [exact RH | apply frame_mod_munch; exact FM | exact (aframe_mod_wmono _ _ _ FM) |].
      apply Forall_forall. intros iv Hiv. unfold ivls in Hiv. apply in_map_iff in Hiv. destruct Hiv as (r & <- & Hr).
      unfold aclient_write_ok, aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ALIBC_PGSZ, ATP. cbn [fst snd].
      destruct (RS r Hr) as [X|[X|[X|X]]]; [left; lia | right; left; lia | right; left; lia | right; left; (first [clear - X; lia | lia])].
    Qed.

    Ltac pf_region Hr :=
      cbn [In] in Hr;
      repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
      unfold atr_region, ATR_STACK; cbn [fst snd]; rewrite ?u_small by lia; lia.

    Lemma zero_lines_snoc : forall k, zero_lines k ++ [Z_to_bv 8 48; Z_to_bv 8 10] = zero_lines (S k).
    Proof. induction k as [|k IH]; [reflexivity|]. cbn [zero_lines app]. rewrite IH. reflexivity. Qed.

    (* [comment removed for export] *)
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

    (* [comment removed for export] *)
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

    (* [comment removed for export] *)
    Lemma atinv_copy : forall m m' (D Nn : Z) LB1 sx,
      atinv m -> munch [(D, D + Nn); (bv_unsigned sp - 80 - 4096, bv_unsigned sp - 80)]%Z m m' -> wmono asegs m m' ->
      mem_inv asegs m' -> stk asegs m' (bv_unsigned sp - ATR_STACK) (bv_unsigned sp - 80) -> ACONST m' ->
      ablock_range H D Nn -> (D + Nn <= A \/ A + cap <= D) -> as_RHEAP H sx LB1 m -> In (p, A, cap) LB1 -> (exists q, In (q, D, Nn) LB1) ->
      atinv m'.
    Proof.
      intros m m' D Nn LB1 sx [INV STK AC RELRO GLB CELLS [t [TID Ht]] [e ERR] [can [CAN CAN64]] RFS [shi [SH0 Hshi]] ABOVE [B' [AUX [HB' AUXV]]] ADDR DATA [junk JCB]]
             MU WM INV' STK' AC' HBR DISJ RH HIn [q HInD].
      pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb.
      pose proof HBR as (R1 & R2 & R3 & R4 & R5 & R6 & R7). unfold AIMG_TOP in R4.
      pose proof blkA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7). unfold AIMG_TOP in BA4. pose proof (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as HC.
      pose proof (ah_RFS_range H HH _ _ RFS) as [(F1 & F2 & F3 & F4) _].
      assert (AG : forall x : word, bv_unsigned sp - 80 <= bv_unsigned x -> m' x = m x).
      { intros x Hx. apply MU. cbn. lia. }
      assert (IMG : forall x n, x + n <= 0xc04000 -> disjoint_from [(D, D + Nn); (bv_unsigned sp - 80 - 4096, bv_unsigned sp - 80)]%Z x n).
      { intros x n Hx. cbn. lia. }
      assert (CW : Forall (aclient_write_ok H LB1) [(D, D + Nn); (bv_unsigned sp - 80 - 4096, bv_unsigned sp - 80)]%Z).
      { constructor; [| constructor; [| constructor]].
        - right; right; left. exists (q, D, Nn). split; [exact HInD | cbn; lia].
        - left. cbn. lia. }
      split; try assumption.
      - destruct STK as (S1 & S2 & S3). destruct STK' as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
        intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp - 80)) as [Lc|Lc]; [apply S3'; lia|].
        assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by (first [clear - Lc Ha HC BA5 BA4 HCL H1; lia | lia]); lia).
        unfold wview, mrd. rewrite E. apply S3. lia.
      - intros i Hi. rewrite <- (RELRO i Hi). rewrite <- wa_eq. apply MU. rewrite wa_eq, u_small by lia. cbn. (first [clear - Hi R5 R4 R3 HCL; lia | lia]).
      - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq;
          apply MU; rewrite wa_eq, u_small by lia; cbn; (first [clear - Hi R5 R4 R3 HCL; lia | lia]).
      - eapply cells_ok_munch; [apply adrv_cells_wf | exact CELLS | exact MU |].
        eapply Forall_impl; [| apply adrv_cells_range]. intros [[a w] v] Ra. apply IMG. (first [clear - Ra; lia | lia]).
      - exists t. split; [|exact Ht]. eapply rdn_munch; [exact MU | exact TID | lia | cbn; lia |]. intros x Hx. cbn in Hx |- *. lia.
      - exists e. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. apply IMG. unfold AERRNO, ATP. cbn. lia.
      - exists can. split; [|exact CAN64]. eapply rdn_munch; [exact MU | exact CAN | lia | cbn; lia |]. intros x Hx. cbn in Hx |- *. lia.
      - eapply (ah_RFS_frame H HH); [exact RFS | exact MU | exact WM |].
        constructor; [| constructor; [| constructor]]; left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP; lia.
      - exists shi. split; [|exact Hshi]. eapply stack0_transport; [exact SH0 | exact MU | exact WM |].
        constructor; [eapply stack0_ok_aapp; [exact R7 | lia | lia] | constructor; [apply stack0_ok_app; unfold AHI_LO; lia | constructor]].
      - intros a Ha. rewrite <- (ABOVE a Ha). apply AG. lia.
      - exists B'. split; [|split; [exact HB'|]]; [eapply (ah_rauxv_frame H HH LB1); [exact AUX | exact MU | exact WM | exact CW]|].
        eapply aauxv_ok_frame; [exact AUXV | exact MU | exact WM |].
        constructor; [| constructor; [| constructor]]; unfold aauxv_win_ok, AAUXV_CELL; cbn [fst snd]; (first [clear - R4 R5 HB' HCL; lia | lia]).
      - eapply addressable_transport; [exact ADDR | exact MU | exact WM |].
        pose proof (aapp_disjoint_sh D Nn A cap R7 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as SD.
        pose proof (sh_below_aceil (A + cap) ltac:(unfold AAPP_HI; (first [clear - HC BA5 BA4 ACEILB; lia | lia]))).
        pose proof (sh_nsh_high A cap ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; (first [clear - BA5 ACEILB; lia | lia]))). 
        pose proof (sh_mono A (A + cap) ltac:(lia)).
        cbn. unfold AHI_LO in *. repeat split; (first [clear - SD H3 H0; lia | lia]).
      - eapply rdn_munch; [exact MU | exact DATA | lia | lia |]. intros x Hx. cbn. lia.
      - exists junk. eapply rw_cells_transport; [exact JCB | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. (first [clear - BA5 HCL DISJ; lia | lia]).
    Qed.


    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition atx_ok (r : word * Z) : Prop :=
      (bv_unsigned (fst r) + snd r <= 0xc01ce8 \/ 0xc01cec <= bv_unsigned (fst r)) /\ (bv_unsigned (fst r) + snd r <= 0xc01d08 \/ 0xc01d10 <= bv_unsigned (fst r))
      /\ (bv_unsigned (fst r) + snd r <= 0xc01e08 \/ 0xc01e10 <= bv_unsigned (fst r)).
    Lemma atx_frame : forall m m' rs, cells_ok m atexit_done_cells -> frame_mod m m' rs -> (forall r, In r rs -> atx_ok r /\ 0 <= snd r) ->
      cells_ok m' atexit_done_cells.
    Proof.
      intros m m' rs HC FM RS. eapply acells_ok_frame; [vm_compute; reflexivity | exact HC | exact FM |].
      unfold atexit_done_cells. repeat (apply Forall_cons; [intros r Hr; cbn [Z.of_nat Pos.of_succ_nat Pos.succ fst snd]; destruct (RS r Hr) as [(X1 & X2 & X3) X0]; lia |]).
      apply Forall_nil.
    Qed.
    Lemma atx_apres : forall m m' LB1 SP, cells_ok m atexit_done_cells -> apres H LB1 SP m m' -> cells_ok m' atexit_done_cells.
    Proof.
      intros m m' LB1 SP HC HP. eapply cells_ok_apres; [vm_compute; reflexivity | exact HC | exact HP |].
      unfold atexit_done_cells, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil.
    Qed.
    Lemma atx_xpres : forall m m' LB1 SP XS m1, cells_ok m atexit_done_cells -> xpres H LB1 SP (AERRNO_X ++ al_LIBX L ++ XS) m m' ->
      Forall (fs_scratch H []) XS -> as_RFS H [] m1 -> cells_ok m' atexit_done_cells.
    Proof.
      intros m m' LB1 SP XS m1 HC HP HSC RFS1. pose proof (xsafe_of_far XS (scratch_far m1 XS RFS1 HSC)) as SAFE.
      eapply cells_ok_xpres; [vm_compute; reflexivity | exact HC | exact HP | exact SAFE |].
      unfold atexit_done_cells, aimg_client, alibw_ok, alibx_ok. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil.
    Qed.
    Lemma atx_munch : forall W m m', cells_ok m atexit_done_cells -> munch W m m' ->
      (forall x n, x + n <= 0xc04000 -> disjoint_from W x n) -> cells_ok m' atexit_done_cells.
    Proof.
      intros W m m' HC MU IMG. eapply cells_ok_munch; [vm_compute; reflexivity | exact HC | exact MU |].
      unfold atexit_done_cells. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; apply IMG; lia |]). apply Forall_nil.
    Qed.

    Definition incb (v : Z) (m : word -> option byte) : Prop := rdn RSEGS m (Z_to_bv 64 0xbdcf54) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 v)).
    Lemma incb_frame : forall v m m' rs, incb v m -> frame_mod m m' rs ->
      (forall r, In r rs -> bv_unsigned (fst r) + snd r <= 0xbdcf54 \/ 0xbdcf55 <= bv_unsigned (fst r)) -> incb v m'.
    Proof.
      intros v m m' rs HB FM RS. unfold incb in *. eapply ardn_frame; [exact FM | exact HB | lia | cbn; lia |].
      intros r Hr. cbn. destruct (RS r Hr); lia.
    Qed.
    Lemma incb_apres : forall v m m' LB1 SP, incb v m -> apres H LB1 SP m m' -> incb v m'.
    Proof.
      intros v m m' LB1 SP HB HP. unfold incb in *. eapply rdn_apres; [exact HP | exact HB | lia | cbn; lia |].
      intros x Hx. right; left. unfold aimg_client. cbn in Hx. lia.
    Qed.
    Lemma incb_xpres : forall v m m' LB1 SP XS m1, incb v m -> xpres H LB1 SP (AERRNO_X ++ al_LIBX L ++ XS) m m' ->
      Forall (fs_scratch H []) XS -> as_RFS H [] m1 -> incb v m'.
    Proof.
      intros v m m' LB1 SP XS m1 HB HP HSC RFS1. pose proof (xsafe_of_far XS (scratch_far m1 XS RFS1 HSC)) as SAFE. unfold incb in *.
      eapply rdn_xpres; [exact HP | exact HB | lia | cbn; lia |]. intros x Hx. cbn in Hx.
      split; [right; left; unfold aimg_client; lia|]. apply not_rin_safe; [exact SAFE | nlibx | left; unfold AIMG_TOP; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma atr_region_libx : forall r a, atr_region r -> alibx_ok a -> a < bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= a.
    Proof. intros r a Hr Ha. pose proof SPlo. unfold atr_region, ATR_STACK in Hr. unfold alibx_ok in Ha. lia. Qed.

    Lemma alib_frame : forall st LIBc sx LBx m m' rs,
      al_LIBST L st LIBc m -> as_RHEAP H sx LBx m -> (forall b, In b LIBc -> In b LBx) ->
      frame_mod m m' rs -> (forall r, In r rs -> atr_region r) -> al_LIBST L st LIBc m'.
    Proof.
      intros st LIBc sx LBx m m' rs HL RH SUB FM RS. pose proof SPlo. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb.
      pose proof FM as [Hout Hg].
      apply (alo_frame L LOK st LIBc m m' HL). intros a Ha64 Ha.
      assert (OUT : OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside (wa a) rs).
      { apply outside_of_disjoint. intros r Hr. rewrite wa_eq, u_small by lia. destruct Ha as [Ha|[(b & Hb & Hab)|(b & Hb & Hab)]].
        - exact (atr_region_libx r a (RS r Hr) (alo_libx L LOK a Ha)).
        - pose proof (ah_blocks H HH _ _ _ b RH (SUB b Hb)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). unfold AIMG_TOP in R4.
          pose proof (RS r Hr) as X. unfold atr_region, ATR_STACK in X. lia.
        - (* [comment removed for export] *)
          pose proof (ah_blocks H HH _ _ _ b RH (SUB b Hb)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
          pose proof (sh_aapp_range _ _ R7 R3) as (S1 & S2 & S3). pose proof aceil_range as AR. unfold AHI_LO in S3.
          assert (S0 : sh AIMG_TOP = ltac:(let v := eval vm_compute in (sh AIMG_TOP) in exact v)) by reflexivity. rewrite S0 in S1.
          pose proof (RS r Hr) as X. unfold atr_region, ATR_STACK in X. lia. }
      split; [apply Hout; exact OUT|]. intros W. unfold wview, mrd in *. rewrite (Hout _ OUT). exact W.
    Qed.

    Lemma alib_apres : forall st LIBc LB1 SP m m',
      al_LIBST L st LIBc m -> apres H LB1 SP m m' -> (forall b, In b LIBc -> In b LB1) -> al_LIBST L st LIBc m'.
    Proof.
      intros st LIBc LB1 SP m m' HL HP SUB. apply (alo_frame L LOK st LIBc m m' HL). intros a Ha64 Ha. apply (HP a Ha64).
      destruct Ha as [Ha|[(b & Hb & Hab)|(b & Hb & Hab)]].
      - right; left. pose proof (alo_libx L LOK a Ha) as W. unfold aimg_client, alibx_ok in *. lia.
      - right; right; left. exists b. split; [exact (SUB b Hb) | exact Hab].
      - (* [comment removed for export] *) right; right; right; left. exists b. split; [exact (SUB b Hb) | exact Hab].
    Qed.

    Lemma alib_munch : forall st W m m',
      al_LIBST L st [] m -> munch W m m' -> wmono asegs m m' -> (forall x, alibx_ok x -> outside W x) -> al_LIBST L st [] m'.
    Proof.
      intros st W m m' HL MU WM HO. apply (alo_frame L LOK st [] m m' HL). intros a Ha64 Ha.
      destruct Ha as [Ha|[(b & Hb & _)|(b & Hb & _)]]; [|destruct Hb|destruct Hb].
      assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_eq, u_small by lia; apply HO; exact (alo_libx L LOK a Ha)).
      split; [exact E|]. intros Wv. apply WM. exact Wv.
    Qed.
    Section Loop.
      (* [comment removed for export] *)
      Variables (Dz OWz : Z) (cb : list block).
      Hypothesis COPY : (N = 0 /\ Dz = AFUZZ_EMPTY /\ OWz = 0 /\ cb = [])
                        \/ (1 <= N /\ OWz = Dz /\ exists pD, cb = [(pD, Dz, N)] /\ ablock_range H Dz N).
      Let LB0 : list block := cb ++ LB.
      (* [comment removed for export] *)
      Variable K : TSet.
      Hypothesis HPOST : forall regs' mem' msF' mo' s', ATRpost H L sp A cap data p s0 LB mo0 regs0 mem0 regs' mem' msF' mo' s' ->
         realizes asegs (mkCfg msF' mo') K.

      (* [comment removed for export] *)
      Definition spent (k : nat) : Z := as_Cm H N + Z.of_nat k * fuzz_cost H L N.

      Let HD16 : Dz mod 16 = 0.
      Proof. destruct COPY as [(_ & -> & _) | (_ & _ & pD & _ & (_ & R2 & _))]; [reflexivity | exact R2]. Qed.

      (* [comment removed for export] *)
      Record lstate (k kc : nat) (r : Z) (regs : bvmap 5 word) (m : word -> option byte) (mo : Model) (sC : as_St H)
                    (LIBc LBc : list block) (st : al_st L) : Prop := LS {
        ls_regs  : loop_base sp regs (Z_to_bv 64 N) (Z_to_bv 64 Dz) (Z_to_bv 64 OWz);
        ls_r     : getr regs 21 = Z_to_bv 64 r;
        ls_k4    : forall rr : reg, In rr ([24; 25; 26; 27]%bv : list reg) -> getr regs rr = getr regs0 rr;
        ls_tinv  : atinv m;
        ls_frame : tframe sp m (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23);
        ls_heap  : as_RHEAP H sC (LIBc ++ LBc) m;
        ls_perm  : Permutation LBc LB0;
        ls_lib   : al_LIBST L st LIBc m;
        ls_libn  : Z.of_nat (length LIBc) + (if al_is_fresh L st then ALIB_CNT_MAX else 0) <= ALIB_CNT_MAX
                   /\ lb_bytes LIBc + (if al_is_fresh L st then ALIB_BYTES_MAX else 0) <= ALIB_BYTES_MAX;
        ls_mpres : as_MPRES H mo0 mo;
        ls_copy  : rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds;
        ls_cells : 1 <= N -> rw_cells asegs m Dz [CB (Z.to_nat N) ds];
        ls_caddr : 1 <= N -> addressable m Dz N;
        ls_sto   : sto k m;
        ls_atx   : cells_ok m atexit_done_cells;
        ls_incb  : incb 0 m;
        ls_al    : as_AL H sC >= as_AL H s0 - spent kc }.

      Lemma lb_bytes_app : forall L1 L2, lb_bytes (L1 ++ L2) = lb_bytes L1 + lb_bytes L2.
      Proof. intros L1 L2. induction L1 as [|b L1 IH]; [reflexivity|]. cbn [app]. rewrite !lb_bytes_cons, IH. lia. Qed.
      Lemma aatexit_reg_cells_eq : aatexit_reg_cells = atexit_done_cells ++ [(0xbdcf54, 1%nat, 0)].
      Proof. reflexivity. Qed.

      Let Hfd1 : forall mo, as_MPRES H mo0 mo -> fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
      Proof. intros mo MP. destruct (adl_mpres H DL _ _ MP) as (_ & E & _). rewrite E. exact (atr_fd1 _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
      Let Hfd2 : forall mo, as_MPRES H mo0 mo -> fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
      Proof. intros mo MP. destruct (adl_mpres H DL _ _ MP) as (_ & E & _). rewrite E. exact (atr_fd2 _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
      Let Hfs : forall mo, as_MPRES H mo0 mo -> m_fs mo = m_fs mo0.
      Proof. intros mo MP. exact (proj1 (adl_mpres H DL _ _ MP)). Qed.

      (* [comment removed for export] *)
      Lemma lb_remove_perm : forall Lx q Ak n, List.NoDup (map blk_id Lx) -> In (q, Ak, n) Lx ->
        Permutation Lx ((q, Ak, n) :: as_lb_remove H q Lx).
      Proof.
        destruct (ah_lb_remove H HH) as (L1 & L2 & L3).
        induction Lx as [|b Lx IH]; intros q Ak n ND HIn; [destruct HIn|].
        inversion ND as [|x l Hni Hnd]; subst.
        destruct HIn as [-> | HIn].
        - rewrite (L1 q Ak n Lx Hni). apply Permutation_refl.
        - assert (NE : blk_id b <> q).
          { intros E. apply Hni. rewrite E. replace q with (blk_id (q, Ak, n)) by reflexivity. apply in_map. exact HIn. }
          rewrite (L2 q b Lx NE). eapply Permutation_trans; [apply perm_skip; apply (IH q Ak n Hnd HIn) | apply perm_swap].
      Qed.

      (* [comment removed for export] *)
      Lemma tr_ret : forall regs m msF mo sC LIBc LBall st,
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0x1ef0f4) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        loop_base sp regs (Z_to_bv 64 N) (Z_to_bv 64 Dz) (Z_to_bv 64 OWz) ->
        (forall rr : reg, In rr ([24; 25; 26; 27]%bv : list reg) -> getr regs rr = getr regs0 rr) ->
        atinv m -> tframe sp m (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23) ->
        as_RHEAP H sC LBall m -> (forall b, In b LB -> In b LBall) -> al_LIBST L st LIBc m ->
        as_MPRES H mo0 mo -> sto calls m -> cells_ok m atexit_done_cells -> incb 0 m ->
        as_AL H sC >= as_AL H s0 - atr_cost H L data ->
        realizes asegs (mkCfg msF mo) K.
      Proof.
        intros regs m msF mo sC LIBc LBall st HV HA LR K4 TI TF RH INCL HL MP STO ATX INCB HAL. pose proof SPlo. pose proof SPhi.
        eapply (seg_T8 H DL sp SP16 SPlo SPhi sC msF mo regs m _ _ _ _ _ _ _ _ _ _ _ K LR (atinv_stk128 m TI) (atinv_ro m TI) (ti_relro m TI) (atinv_latch m TI) TF);
          [| exact HV | exact HA].
        intros regs' msF' mo' HV' HA' SB' Q2 Q4 Q10 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 KP K4'.
        apply (HPOST regs' m msF' mo' sC). destruct TI as [INV STK AC RELRO GLB CELLS TID ERR CAN RFS SH0 ABOVE [B' [AUX [HB' AUXV]]] ADDR DATA JCB].
        destruct calls as [|k'] eqn:EC; [lia|]. cbn [sto] in STO.
        split; try assumption.
        - eapply (ah_mpres_trans H HH); [exact MP| apply (adl_sb H DL); exact SB'].
        - intros rr Hrr. cbn [In] in Hrr.
          destruct Hrr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]];
            first [assumption | rewrite K4' by in_solve; apply K4; in_solve].
        - eapply astk_stk_ok; [exact STK | lia | lia | unfold ATR_STACK; lia | lia].
        - exists LBall. split; [exact RH | exact INCL].
        - exists B'. split; [exact AUX|]. split; [lia | exact AUXV].
        - split; try assumption.
        - change (hdr_calls data) with calls. rewrite EC. cbn [Nat.pred]. exact STO.
        - rewrite aatexit_reg_cells_eq. unfold cells_ok in *. apply Forall_app. split; [exact ATX|]. constructor; [exact INCB | constructor].
        - rewrite <- wa_eq. exact (alo_clean L LOK st LIBc m HL).
        - rewrite (same_but_materialized_fs _ _ SB'). apply Hfs. exact MP.
        - rewrite (same_but_materialized_fds _ _ SB'). apply Hfd1. exact MP.
        - rewrite (same_but_materialized_fds _ _ SB'). apply Hfd2. exact MP.
      Qed.



      Let TRC : adrv_traces H L. Proof. exact (atr_tr _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
      Let HCAP : Z.of_nat (length data) <= cap. Proof. exact (atr_cap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
      Let HAL0 : atr_cost H L data <= as_AL H s0. Proof. exact (atr_al _ _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.
      Let COSTS : cost_laws H. Proof. exact (ah_costs H HH). Qed.

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

      (* [comment removed for export] *)
      Lemma tr_free : forall regs m msF mo sC LIBc LBc st,
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0x1ef0d8) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate calls calls 1 regs m mo sC LIBc LBc st -> getr regs 19 = Z_to_bv 64 0 ->
        realizes asegs (mkCfg msF mo) K.
      Proof.
        intros regs m msF mo sC LIBc LBc st HV HA [LR R21 K4 TI TF RH PERM HL HLN MP CPY CELLS CADDR STO ATX INCB HAL] R19. pose proof SPlo. pose proof SPhi.
        pose proof HCLO as HCL. unfold ATR_STACK in HCL. pose proof HN as HN'.
        assert (HCOST : atr_cost H L data = as_Cm H N + as_Cf H N + Z.of_nat calls * fuzz_cost H L N) by reflexivity.
        pose proof HAL0 as AL0. rewrite HCOST in AL0. unfold spent in HAL.
        destruct COSTS as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (C1 N ltac:(lia)). pose proof (C3 N ltac:(lia)). pose proof (C3 0 ltac:(lia)).
        pose proof (C4 0 N ltac:(lia)).
        eapply (seg_T7free H DL sp SP16 SPlo SPhi sC msF mo regs m _ _ _ K LR R19 R21 (atinv_stk128 m TI) (atinv_ro m TI) (ti_relro m TI) (atinv_latch m TI));
          [| exact HV | exact HA].
        intros regs1 msF1 mo1 HV1 HA1 SB1 (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23) Q19 Q1 Q10 K4'.
        destruct (ti_aux _ TI) as [B' [AUX1 [HB' AUXV1]]]. destruct (ti_errno _ TI) as [errv ERR].
        assert (MP1 : as_MPRES H mo0 mo1) by (eapply (ah_mpres_trans H HH); [exact MP | apply (adl_sb H DL); exact SB1]).
        assert (SUBL : forall b, In b LIBc -> In b (LIBc ++ LBc)) by (intros b Hb; apply in_or_app; left; exact Hb).
        destruct COPY as [(N0 & ED & EOW & Ecb) | (N1 & EOW & pD & Ecb & HBR)].
        - (* [comment removed for export] *)
          rewrite EOW in Q10.
          eapply (afree_null_call H HH DL regs1 m msF1 mo1 sC (LIBc ++ LBc) (bv_unsigned sp - ATR_STACK) B' errv 0x1ef0f4 [] K HV1 HA1 Q1);
            [ lia | reflexivity | exact Q4 | exact Q10 | exact RH | lia
            | exact AUX1 | rewrite Q2, u_small by lia; lia
            | rewrite Q2, u_small by lia; exact (atinv_stklo m TI)
            | acb; unfold ATR_STACK; lia | rewrite Q2, u_small by lia; unfold AFREE_STACK, ATR_STACK; lia
            | rewrite Q2, u_small by lia; unfold ATR_STACK; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
            | rewrite Q4; unfold AERRNO; rewrite u_small by (unfold ATP; lia); exact ERR | exact (ti_inv _ TI) | exact (ti_ac _ TI)
            | apply (ah_chain_nil H HH); rewrite Q8, u_small by lia; acb; lia |].
          intros regs2 mem2 msF2 mo2 s2 HV2 HA2 MP2 KEPT Hinv2 STK2 ERR2 AUX2 HP2 RH2 AC2 HAL2.
          rewrite Q2, u_small in STK2, HP2 by lia. rewrite Q4 in ERR2. unfold AERRNO in *.
          pose proof (KEPT 2%bv ltac:(in_solve)) as S2'. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
          pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 20%bv ltac:(in_solve)) as S20.
          pose proof (KEPT 22%bv ltac:(in_solve)) as S22. pose proof (KEPT 23%bv ltac:(in_solve)) as S23.
          eapply (tr_ret regs2 mem2 msF2 mo2 s2 LIBc (LIBc ++ LBc) st HV2 HA2).
          + unfold loop_base. rewrite S2', S4, S8, S9, S18, S20, S22, S23. repeat split; assumption.
          + intros rr Hrr. rewrite (KEPT rr) by (unfold aheap_kept; in_from Hrr). rewrite (K4' rr Hrr). apply K4. exact Hrr.
          + eapply (atinv_apres m mem2 (LIBc ++ LBc) B'); try assumption.
            * apply in_or_app. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. subst LB0. rewrite Ecb. cbn. apply (atr_blk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE).
            * eapply (aauxv_ok_apres H); [exact AUXV1 | exact HP2 | lia].
            * rewrite u_small in ERR2 by (unfold ATP; lia). exact ERR2.
            * eapply (RFS_via_apres H HH); [exact (ti_rfs _ TI) | exact HP2].
            * intros shi SH. eapply stack0_xpres; [apply xpres_of_apres; exact HP2 | exact SH | constructor].
          + eapply atframe_agree; [exact TF|]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP2 _ (u64_range x) ltac:(left; lia))).
          + exact RH2.
          + intros b Hb. apply in_or_app. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. subst LB0. rewrite Ecb. exact Hb.
          + eapply alib_apres; [exact HL | exact HP2 | exact SUBL].
          + eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
          + eapply sto_apres; [lia | exact STO | exact HP2].
          + eapply atx_apres; [exact ATX | exact HP2].
          + eapply incb_apres; [exact INCB | exact HP2].
          + rewrite HCOST. rewrite N0 in *. lia.
        - (* [comment removed for export] *)
          assert (HInc : In (pD, Dz, N) LBc) by (eapply Permutation_in; [apply Permutation_sym; exact PERM|]; subst LB0; rewrite Ecb; left; reflexivity).
          assert (HIn : In (pD, Dz, N) (LIBc ++ LBc)) by (apply in_or_app; right; exact HInc).
          assert (HInAc : In (p, A, cap) LBc) by (eapply Permutation_in; [apply Permutation_sym; exact PERM|]; subst LB0; rewrite Ecb; right; apply (atr_blk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE)).
          destruct (CADDR N1) as [_ SHD].
          rewrite EOW in Q10.
          eapply (afree_call H HH DL regs1 m msF1 mo1 sC (LIBc ++ LBc) pD Dz N (bv_unsigned sp - ATR_STACK) B' errv 0x1ef0f4 [] ds (shadow_of N) K HV1 HA1 Q1);
            [ lia | reflexivity | exact Q4 | exact Q10 | exact RH | exact HIn | lia
            | exact (CELLS N1) | exact SHD | apply shadow_of_length; lia
            | exact AUX1 | rewrite Q2, u_small by lia; lia
            | rewrite Q2, u_small by lia; exact (atinv_stklo m TI)
            | acb; unfold ATR_STACK; lia | rewrite Q2, u_small by lia; unfold AFREE_STACK, ATR_STACK; lia
            | rewrite Q2, u_small by lia; unfold ATR_STACK; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
            | rewrite Q4; unfold AERRNO; rewrite u_small by (unfold ATP; lia); exact ERR | exact (ti_inv _ TI) | exact (ti_ac _ TI)
            | apply (ah_chain_nil H HH); rewrite Q8, u_small by lia; acb; lia
            | cbn [map snd app]; destruct TRC as (_ & _ & _ & _ & _ & T6 & _); exact T6 |].
          intros regs2 mem2 msF2 mo2 s2 HV2 HA2 MP2 KEPT Hinv2 STK2 ERR2 AUX2 HP2 RH2 AC2 HAL2.
          rewrite Q2, u_small in STK2, HP2 by lia. rewrite Q4 in ERR2. unfold AERRNO in *.
          pose proof (KEPT 2%bv ltac:(in_solve)) as S2'. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
          pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 20%bv ltac:(in_solve)) as S20.
          pose proof (KEPT 22%bv ltac:(in_solve)) as S22. pose proof (KEPT 23%bv ltac:(in_solve)) as S23.
          pose proof (lb_remove_perm (LIBc ++ LBc) pD Dz N (ah_nodup H HH _ _ _ RH) HIn) as P1.
          assert (PERM2 : Permutation (as_lb_remove H pD (LIBc ++ LBc)) (LIBc ++ LB)).
          { apply (Permutation_cons_inv (a:=(pD, Dz, N))). eapply Permutation_trans; [apply Permutation_sym; exact P1|].
            eapply Permutation_trans; [apply Permutation_app_head; exact PERM|]. subst LB0. rewrite Ecb. cbn [app].
            apply Permutation_sym. apply Permutation_middle. }
          eapply (tr_ret regs2 mem2 msF2 mo2 s2 LIBc (as_lb_remove H pD (LIBc ++ LBc)) st HV2 HA2).
          + unfold loop_base. rewrite S2', S4, S8, S9, S18, S20, S22, S23. repeat split; assumption.
          + intros rr Hrr. rewrite (KEPT rr) by (unfold aheap_kept; in_from Hrr). rewrite (K4' rr Hrr). apply K4. exact Hrr.
          + eapply (atinv_apres m mem2 (as_lb_remove H pD (LIBc ++ LBc)) B'); try assumption.
            * eapply Permutation_in; [apply Permutation_sym; exact PERM2 | apply in_or_app; right; apply (atr_blk _ _ _ _ _ _ _ _ _ _ _ _ _ PRE)].
            * eapply (aauxv_ok_apres H); [exact AUXV1 | exact HP2 | lia].
            * rewrite u_small in ERR2 by (unfold ATP; lia). exact ERR2.
            * eapply (RFS_via_apres H HH); [exact (ti_rfs _ TI) | exact HP2].
            * intros shi SH. eapply stack0_xpres; [apply xpres_of_apres; exact HP2 | exact SH | constructor].
          + eapply atframe_agree; [exact TF|]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP2 _ (u64_range x) ltac:(left; lia))).
          + exact RH2.
          + intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM2 | apply in_or_app; right; exact Hb].
          + eapply alib_apres; [exact HL | exact HP2 |]. intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM2 | apply in_or_app; left; exact Hb].
          + eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
          + eapply sto_apres; [lia | exact STO | exact HP2].
          + eapply atx_apres; [exact ATX | exact HP2].
          + eapply incb_apres; [exact INCB | exact HP2].
          + rewrite HCOST. lia.
      Qed.
      (* [comment removed for export] *)
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
            destruct (RS r Hr) as [X|[X|[X|X]]]; first [clear - X HCL; lia | lia].
          + intros _ RC. eapply arw_cells_frame; [exact RC | exact FM |]. cbn [cells_size csize]. intros r Hr.
            destruct (RS r Hr) as [X|[X|[X|X]]]; first [clear - X HCL; lia | lia].
          + intros _ AD. eapply addressable_transport; [exact AD | apply frame_mod_munch; exact FM | exact (aframe_mod_wmono _ _ _ FM) |].
            assert (SHR : (0x80178800 <= sh Dz /\ sh Dz + nsh N <= 0x8fff6e00) \/ (0x2008fff7000 <= sh Dz /\ sh Dz + nsh N <= sh aceil /\ sh aceil < AHI_LO)).
            { destruct R7 as [P|P]; [left; exact (sh_aapp_lo_range Dz N P R3) | right; exact (sh_aapp_hi_range Dz N P R3)]. }
            assert (SHT : sh aceil <= 0x10007fff7000).
            { unfold sh. rewrite ASHADOW_BASE_val. assert (A8 : 0 < 8) by lia. assert (ACL : aceil <= 0x7fffff800000) by lia.
              pose proof (Z.div_le_mono _ _ _ A8 ACL) as DM. change (0x7fffff800000 / 8) with 0xffffff00000 in DM. lia. }
            clear - RS SHR SHT H0. induction rs as [|[r k] rs IH]; [exact I|]. cbn. split.
            * pose proof (RS (r, k) (or_introl eq_refl)) as X. cbn [fst snd] in X. unfold AHI_LO in SHR. destruct X as [X|[X|[X|X]]]; lia.
            * apply IH. intros r' Hr'. apply RS. right. exact Hr'.
      Qed.

      (* [comment removed for export] *)
      Lemma copy_xpres : forall m m' LIBc LBc XS sx m1, Permutation LBc LB0 -> as_RHEAP H sx (LIBc ++ LBc) m -> as_RFS H [] m1 ->
        Forall (fs_scratch H []) XS -> xpres H LBc (bv_unsigned sp - 80) (AERRNO_X ++ al_LIBX L ++ XS) m m' ->
        (rdn RSEGS m (Z_to_bv 64 Dz) (length ds) = Some ds -> rdn RSEGS m' (Z_to_bv 64 Dz) (length ds) = Some ds)
        /\ (1 <= N -> rw_cells asegs m Dz [CB (Z.to_nat N) ds] -> rw_cells asegs m' Dz [CB (Z.to_nat N) ds])
        /\ (1 <= N -> addressable m Dz N -> addressable m' Dz N).
      Proof.
        intros m m' LIBc LBc XS sx m1 HPm RH RFS1 HSC HP. pose proof HN as HN'. pose proof Hds as Hds'.
        destruct COPY as [(N0 & _ & _ & _) | (N1 & _ & pD & Ecb & HBR)].
        - assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. split; [reflexivity|]. split; intros; lia.
        - assert (HInc : In (pD, Dz, N) LBc).
          { eapply Permutation_in; [apply Permutation_sym; exact HPm|]. subst LB0. rewrite Ecb. left. reflexivity. }
          assert (HIn : In (pD, Dz, N) (LIBc ++ LBc)) by (apply in_or_app; right; exact HInc).
          pose proof (blk_scratch sx (LIBc ++ LBc) m m1 XS pD Dz N RH HIn RFS1 HSC) as [BF BS].
          pose proof HBR as (R1 & R2 & R3 & R4 & R5 & R6 & R7). acb.
          assert (LF : Forall (fun iv : Z * Z => Dz + N <= fst iv \/ snd iv <= Dz) (al_LIBX L)) by (apply libx_miss; unfold AIMG_TOP in *; lia).
          assert (LS : Forall (fun iv : Z * Z => sh Dz + nsh N <= fst iv \/ snd iv <= sh Dz) (al_LIBX L)).
          { pose proof (sh_mono AIMG_TOP Dz ltac:(lia)) as SM. apply libx_miss. unfold sh, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. lia. }
          split; [| split].
          + intros HC. eapply rdn_xpres; [exact HP | exact HC | lia | rewrite Hds; lia |]. rewrite Hds. intros x Hx. split.
            * right; right; left. exists (pD, Dz, N). split; [exact HInc | cbn; lia].
            * apply not_rin_of_Forall. apply Forall_app. split; [apply Forall_cons; [cbn; unfold ATP, AIMG_TOP in *; lia| apply Forall_nil]|].
              apply Forall_app. split; (eapply Forall_impl; [| first [exact LF | exact BF]]); cbn; intros iv Hiv; lia.
          + intros _ RC. eapply (xpres_rw_cells H); [exact HP | exact RC |]. cbn [cells_size csize]. split.
            * eapply aclient_range_block; [exact HInc | lia | lia].
            * apply Forall_app. split; [apply Forall_cons; [cbn; unfold ATP, AIMG_TOP in *; lia| apply Forall_nil]|].
              apply Forall_app. split; (eapply Forall_impl; [| first [exact LF | exact BF]]); cbn; intros iv Hiv; lia.
          + intros _ AD. eapply (xpres_addressable H); [exact HP | exact AD |]. split; [eapply aclient_range_block_sh; exact HInc |].
            apply Forall_app. split; [apply Forall_cons; [| apply Forall_nil]| apply Forall_app; split; [exact LS | exact BS]].
            cbn [fst snd]. right. pose proof (sh_mono AIMG_TOP Dz ltac:(lia)) as SMz. unfold sh, AIMG_TOP, ATP in *. rewrite ?ASHADOW_BASE_val in *. lia.
      Qed.
      (* [comment removed for export] *)
      Lemma tr_call_harness : forall k r regs m msF mo sC LIBc LBc st (Kx : TSet),
        (k < calls)%nat ->
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0x1ef0b4) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate k k r regs m mo sC LIBc LBc st ->
        (forall regs' m' msF' mo' sC' LIBc' LBc' st',
           as_VIS H sC' msF' = mkst regs' (Z_to_bv 64 0x1ef184) m' rom -> as_AKREL H sC' (mkCfg msF' mo') ->
           lstate k (S k) r regs' m' mo' sC' LIBc' LBc' st' ->
           getr regs' 1 = Z_to_bv 64 0x1ef0d8 -> getr regs' 11 = Z_to_bv 64 0 -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes asegs (mkCfg msF' mo') Kx) ->
        realizes asegs (mkCfg msF mo) Kx.
      Proof.
        intros k r regs m msF mo sC LIBc LBc st Kx Hk HV HA [LR R21 K4 TI TF RH PERM HL HLN MP CPY CELLS CADDR STO ATX INCB HAL] HK.
        pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. unfold ATR_STACK in HCL. pose proof Hcalls as HC.
        pose proof (adl_live H DL) as [LV1 LV2]. pose proof (atr_live _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as [LV3 LV4].
        pose proof LB0_bytes as [LBB LBL]. pose proof HN as HN'.
        (* [comment removed for export] *)
        eapply (seg_T5 H DL sp SP16 SPlo SPhi sC msF mo regs m _ _ _ (getr regs 19) _ Kx LR eq_refl R21
                  (atinv_stk128 m TI) (atinv_ro m TI) (ti_relro m TI) (atinv_latch m TI)); [| exact HV | exact HA].
        intros regs1 m1 msF1 mo1 HV1 HA1 SB1 (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23) Q19 Q21' Q1 Q10 Q11 K4a FM1 STK1 IB1.
        assert (RS1 : forall rr, In rr (regTc_w sp) -> atr_region rr).
        { intros rr Hrr. unfold regTc_w in Hrr. cbn [In] in Hrr. destruct Hrr as [<-|[]]. unfold atr_region. cbn [fst snd]. rewrite u_small by lia. lia. }
        assert (TI1 : atinv m1) by (eapply atinv_frame; [exact TI | exact FM1 | exact RS1]).
        assert (TF1 : tframe sp m1 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)).
        { eapply atframe_agree; [exact TF|]. intros x Hx. apply (proj1 FM1). apply outside_of_disjoint.
          intros rr Hrr. unfold regTc_w in Hrr. cbn [In] in Hrr. destruct Hrr as [<-|[]]; cbn [fst snd]; rewrite u_small by lia; lia. }
        assert (RH1 : as_RHEAP H sC (LIBc ++ LBc) m1) by (eapply aheap_frame_tr; [exact RH | exact FM1 | exact RS1]).
        assert (HL1 : al_LIBST L st LIBc m1) by (eapply alib_frame; [exact HL | exact RH | intros b Hb; apply in_or_app; left; exact Hb | exact FM1 | exact RS1]).
        pose proof (copy_frame m m1 _ FM1 RS1) as (CF1 & CF2 & CF3).
        assert (ST1 : sto k m1).
        { eapply sto_frame; [lia | exact STO | exact FM1 |]. intros rr Hrr. unfold regTc_w in Hrr. cbn [In] in Hrr. destruct Hrr as [<-|[]].
          unfold quiet_region. right. right. left. cbn [fst snd]. rewrite u_small by lia. lia. }
        assert (ATX1 : cells_ok m1 atexit_done_cells).
        { eapply atx_frame; [exact ATX | exact FM1 |]. intros rr Hrr. unfold regTc_w in Hrr. cbn [In] in Hrr. destruct Hrr as [<-|[]].
          unfold atx_ok. cbn [fst snd]. rewrite u_small by lia. lia. }
        destruct (ti_aux _ TI1) as [B' [AUX1 [HB' AUXV1]]]. destruct (ti_errno _ TI1) as [errv ERR]. destruct (ti_sh0 _ TI1) as [shi [SH0 Hshi]].
        assert (MP1 : as_MPRES H mo0 mo1) by (eapply (ah_mpres_trans H HH); [exact MP | apply (adl_sb H DL); exact SB1]).
        (* [comment removed for export] *)
        assert (HCOST : atr_cost H L data = as_Cm H N + as_Cf H N + Z.of_nat calls * fuzz_cost H L N) by reflexivity.
        pose proof HAL0 as AL0. rewrite HCOST in AL0. unfold spent in HAL.
        destruct COSTS as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (C3 N ltac:(lia)) as CF0. pose proof (fuzz_cost_nonneg N ltac:(lia)) as FZ0.
        assert (ALok : fuzz_cost H L N <= as_AL H sC).
        { assert (M : Z.of_nat k * fuzz_cost H L N + fuzz_cost H L N <= Z.of_nat calls * fuzz_cost H L N) by (first [clear - SPlo Hds Hcalls COPY Hk HC FZ0; nia | nia]). lia. }
        assert (HDr : 0 < Dz /\ Dz + Z.of_nat (length ds) <= 2 ^ 64).
        { rewrite Hds. destruct COPY as [(N0 & ED & _) | (_ & _ & pD & _ & HBR)]; [rewrite ED, N0; unfold AFUZZ_EMPTY; lia |].
          acb. destruct HBR as (R1 & R2 & R3 & R4 & R5 & R6). lia. }
        (* [comment removed for export] *)
        assert (BUD1 : lb_bytes (LIBc ++ LBc) + afuzz_live L st <= as_LIVE_MAX H).
        { rewrite lb_bytes_app, (lb_bytes_perm LB0 LBc PERM). unfold afuzz_live, AFUZZ_LIVE, ALIB_BYTES_MAX, ADRV_LIVE in *.
          destruct HLN as [_ HB]. destruct (al_is_fresh L st); lia. }
        assert (BUD2 : Z.of_nat (length (LIBc ++ LBc)) + afuzz_cnt L st <= as_LIVE_CNT_MAX H).
        { rewrite length_app, Nat2Z.inj_add, (Permutation_length PERM). unfold afuzz_cnt, ATRANS_CNT, ALIB_CNT_MAX, ADRV_CNT in *.
          destruct HLN as [HCn _]. destruct (al_is_fresh L st); lia. }
        change (Z_to_bv 64 0x1ef1d0) with (Z_to_bv 64 P_FUZZ_ENTRY) in HV1.
        eapply (afuzz_call H HH L DL FZ regs1 m1 msF1 mo1 sC LIBc LBc st Dz N (bv_unsigned sp - ATR_STACK) B' shi ds errv 0x1ef0c8 Kx HV1 HA1 Q1);
          [ lia | reflexivity | exact Q4 | exact Q10 | exact Q11
          | apply ardn_bytes_at; [apply CF1; exact CPY | lia | lia]
          | rewrite Hds; lia | lia | exact HD16
          | intros HN1; exact (copy_in LBc PERM HN1)
          | intros HN0; destruct COPY as [(_ & ED & _) | (HN1 & _)]; [exact ED | lia]
          | exact RH1 | exact HL1
          | exact BUD1 | exact BUD2
          | exact AUX1 | exact AUXV1 | rewrite Q2, u_small by lia; lia | lia
          | rewrite Q2, u_small by lia; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
          | rewrite Q2, u_small by lia; exact (atinv_stklo m1 TI1)
          | acb; unfold ATR_STACK; lia
          | rewrite Q2, u_small by lia; unfold AFUZZ_STACK, ATR_STACK; lia
          | rewrite Q4; unfold AERRNO; rewrite u_small by (unfold ATP; lia); exact ERR
          | exact (ti_inv _ TI1) | intros i Hi; rewrite wa_eq; apply (ti_relro _ TI1); exact Hi | exact (ti_ac _ TI1)
          | intros HN1; apply CF3; [exact HN1 | exact (CADDR HN1)] | exact (ti_rfs _ TI1)
          | exact SH0 | rewrite Q2, u_small by lia; lia
          | left; rewrite Q8, u_small by lia; acb; lia
          | destruct TRC as (_ & _ & _ & _ & _ & _ & T7 & _); exact T7
          | destruct TRC as (_ & _ & _ & _ & _ & _ & _ & T8); exact T8
          | exact (alo_frames L LOK)
          | exact ALok |].
        intros regs2 mem2 msF2 mo2 s2 LIB2 LB2 st2 XS errv2 HV2 HA2 MP2 KEPT A0 INV2 REL2 STK2 ERR2 AUX2 RH2 PERM2 HL2 HNF2 HLC2 HLB2 HKEEP HSC X2 RFS2 AC2 ST02 HAL2.
        rewrite Q2, u_small in STK2, X2 by lia. rewrite Q4 in ERR2.
        pose proof (KEPT 2%bv ltac:(in_solve)) as S2'. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
        pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 20%bv ltac:(in_solve)) as S20.
        pose proof (KEPT 21%bv ltac:(in_solve)) as S21. pose proof (KEPT 22%bv ltac:(in_solve)) as S22. pose proof (KEPT 23%bv ltac:(in_solve)) as S23.
        assert (LR2 : loop_base sp regs2 (Z_to_bv 64 N) (Z_to_bv 64 Dz) (Z_to_bv 64 OWz)).
        { unfold loop_base. rewrite S2', S4, S8, S9, S18, S20, S22, S23. repeat split; assumption. }
        assert (SUBc : forall b, In b LBc -> In b (LIBc ++ LBc)) by (intros b Hb; apply in_or_app; right; exact Hb).
        assert (TI2 : atinv mem2).
        { apply (atinv_xpres m1 mem2 LBc (LIBc ++ LBc) XS sC m1 B' errv2 TI1 X2 HSC (ti_rfs _ TI1) RH1 (blkA_in LBc PERM) SUBc INV2 STK2 AC2 AUX2 HB'
                   (aauxv_ok_xpres H _ _ _ _ _ _ AUXV1 X2 ltac:(clear - HB'; lia) (auxv_wins XS B' (scratch_far m1 XS (ti_rfs _ TI1) HSC) ltac:(clear - HB'; lia)))).
          - rewrite u_small in ERR2 by (unfold ATP; lia). exact ERR2.
          - exact RFS2.
          - exists shi. split; [exact ST02 | exact Hshi]. }
        assert (TF2 : tframe sp mem2 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)).
        { eapply atframe_agree; [exact TF1|]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq.
          refine (proj1 (X2 _ (u64_range x) _)). split; [left; lia|].
          apply not_rin_safe; [apply xsafe_of_far; eapply scratch_far; [exact (ti_rfs _ TI1) | exact HSC] | nlibx | right; acb; lia]. }
        pose proof (copy_xpres m1 mem2 LIBc LBc XS sC m1 PERM RH1 (ti_rfs _ TI1) HSC X2) as (CP1 & CP2 & CP3).
        (* [comment removed for export] *)
        eapply (seg_T6 H DL sp SP16 SPlo SPhi s2 msF2 mo2 regs2 mem2 _ _ _ _ Kx LR2 ltac:(rewrite S21; exact Q21') A0
                  (atinv_stk128 mem2 TI2) (atinv_ro mem2 TI2) (ti_relro mem2 TI2) (atinv_latch mem2 TI2)); [| exact HV2 | exact HA2].
        intros regs3 m3 msF3 mo3 HV3 HA3 SB3 LR3 T19 T21 T1 T11 K4b FM3 STK3 IB3.
        assert (RS3 : forall rr, In rr (regTc_w sp) -> atr_region rr) by exact RS1.
        pose proof (copy_frame mem2 m3 _ FM3 RS3) as (CG1 & CG2 & CG3).
        apply (HK regs3 m3 msF3 mo3 s2 LIB2 LB2 st2 HV3 HA3); [| exact T1 | exact T11 | exact T19].
        split.
        - exact LR3.
        - exact T21.
        - intros rr Hrr. rewrite (K4b rr Hrr), (KEPT rr) by (unfold aheap_kept; in_from Hrr). rewrite (K4a rr Hrr). apply K4. exact Hrr.
        - eapply atinv_frame; [exact TI2 | exact FM3 | exact RS3].
        - eapply atframe_agree; [exact TF2|]. intros x Hx. apply (proj1 FM3). apply outside_of_disjoint.
          intros rr Hrr. unfold regTc_w in Hrr. cbn [In] in Hrr. destruct Hrr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia.
        - eapply aheap_frame_tr; [exact RH2 | exact FM3 | exact RS3].
        - eapply Permutation_trans; [exact PERM2 | exact PERM].
        - eapply alib_frame; [exact HL2 | exact RH2 | intros b Hb; apply in_or_app; left; exact Hb | exact FM3 | exact RS3].
        - rewrite HNF2. split; lia.
        - eapply (ah_mpres_trans H HH); [exact MP1 |]. eapply (ah_mpres_trans H HH); [exact MP2 | apply (adl_sb H DL); exact SB3].
        - apply CG1. apply CP1. apply CF1. exact CPY.
        - intros HN1. apply CG2; [exact HN1|]. apply CP2; [exact HN1|]. apply CF2; [exact HN1 | exact (CELLS HN1)].
        - intros HN1. apply CG3; [exact HN1|]. apply CP3; [exact HN1|]. apply CF3; [exact HN1 | exact (CADDR HN1)].
        - eapply sto_frame; [lia | eapply sto_xpres; [lia | exact ST1 | exact X2 | exact HSC | exact (ti_rfs _ TI1)] | exact FM3 |].
          intros rr Hrr. unfold regTc_w in Hrr. cbn [In] in Hrr. destruct Hrr as [<-|[]]. unfold quiet_region. right. right. left. cbn [fst snd]. rewrite u_small by lia. lia.
        - eapply atx_frame; [eapply atx_xpres; [exact ATX1 | exact X2 | exact HSC | exact (ti_rfs _ TI1)] | exact FM3 |].
          intros rr Hrr. unfold regTc_w in Hrr. cbn [In] in Hrr. destruct Hrr as [<-|[]]. unfold atx_ok. cbn [fst snd]. rewrite u_small by lia. lia.
        - exact IB3.
        - unfold spent. rewrite Nat2Z.inj_succ. lia.
      Qed.
      (* [comment removed for export] *)
      Lemma tr_printf_buf : forall k r regs m msF mo sC LIBc LBc st (Kx : TSet),
        (1 <= k <= 3)%nat ->
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0x1ef184) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate k (S k) r regs m mo sC LIBc LBc st ->
        getr regs 1 = Z_to_bv 64 0x1ef0d8 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 0 ->
        (forall regs' m' msF' mo',
           as_VIS H sC msF' = mkst regs' (Z_to_bv 64 0x1ef0d8) m' rom -> as_AKREL H sC (mkCfg msF' mo') ->
           lstate (S k) (S k) r regs' m' mo' sC LIBc LBc st -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes asegs (mkCfg msF' mo') Kx) ->
        realizes asegs (mkCfg msF mo) Kx.
      Proof.
        intros k r regs m msF mo sC LIBc LBc st Kx Hk HV HA [LR R21 K4 TI TF RH PERM HL HLN MP CPY CELLS CADDR STO ATX INCB HAL] R1 R11 R19 HK.
        pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb.
        destruct k as [|k']; [lia|]. cbn [sto] in STO.
        destruct (ti_can _ TI) as [can [CAN CAN64]]. destruct (ti_sh0 _ TI) as [shi [SH0 Hshi]].
        pose proof LR as (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23).
        set (w := ABUF + 2 * Z.of_nat k').
        assert (PH : apbH m (Z_to_bv 64 (bv_unsigned sp - 80)) w can).
        { split; rewrite ?u_small by lia.
          - rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
          - unfold ASP_LO. lia.
          - unfold ASP_HI. lia.
          - eapply astk_stk_ok; [exact (ti_stk _ TI) | unfold ATR_STACK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | lia | lia].
          - exact (atinv_ro _ TI).
          - exact (ti_relro _ TI).
          - subst w. apply apb_cells_of; [exact (ti_ac _ TI) | exact STO].
          - exact CAN.
          - exact CAN64.
          - intros a Ha. eapply (stack0_qsh0 m _ _ (bv_unsigned sp - 80) SH0); [unfold ATR_STACK; lia | lia | rewrite ASHADOW_BASE_val; exact Ha]. }
        eapply (drv_printf_buf H DL k' sC msF mo regs m (Z_to_bv 64 (bv_unsigned sp - 80)) can Kx ltac:(lia) PH R1 ltac:(exact Q2) R11 HV HA).
        intros regs' mem' msF' mo' KCS FM BY WP FL HV' HA' SB'.
        rewrite u_small in FM by lia. subst w. unfold ABUF in *.
        assert (RS : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 3400), 3400); (Z_to_bv 64 0x5ede88, 4); (Z_to_bv 64 0x5edeb0, 8);
                                       (Z_to_bv 64 (0xc027a8 + 2 * Z.of_nat k'), 2)] -> atr_region rr).
        { intros rr Hr. pf_region Hr. }
        assert (RSx : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 3400), 3400); (Z_to_bv 64 0x5ede88, 4); (Z_to_bv 64 0x5edeb0, 8);
                                        (Z_to_bv 64 (0xc027a8 + 2 * Z.of_nat k'), 2)] -> atx_ok rr /\ 0 <= snd rr).
        { intros rr Hr. cbn [In] in Hr. unfold atx_ok.
          repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; cbn [fst snd]; rewrite ?u_small by lia; lia. }
        assert (T : forall (a : Z) (n : nat) bs, 0x5ede8c <= a -> a + Z.of_nat n < 2 ^ 64 ->
                  (a + Z.of_nat n <= 0x5edeb0 \/ 0x5edeb8 <= a) -> a + Z.of_nat n <= 0xc027a8 + 2 * Z.of_nat k' ->
                  rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> rdn RSEGS mem' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Ha Hn Hor Hw HD. eapply ardn_frame; [exact FM | exact HD | lia | lia |].
          intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite u_small by lia; (first [clear - Hw ACEILB HCL Hk Ha Hor; lia | lia]). }
        pose proof (copy_frame m mem' _ FM RS) as (CP1 & CP2 & CP3).
        apply (HK regs' mem' msF' mo' HV' HA').
        - split.
          + unfold loop_base. rewrite !(KCS _) by (unfold callee_saved; in_solve). exact LR.
          + rewrite (KCS _) by (unfold callee_saved; in_solve). exact R21.
          + intros rr Hrr. rewrite (KCS rr) by (unfold callee_saved; in_from Hrr). apply K4. exact Hrr.
          + eapply atinv_frame; [exact TI | exact FM | exact RS].
          + eapply atframe_agree; [exact TF|]. intros x Hx. apply (proj1 FM). apply outside_of_disjoint.
            intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
          + eapply aheap_frame_tr; [exact RH | exact FM | exact RS].
          + exact PERM.
          + eapply alib_frame; [exact HL | exact RH | intros b Hb; apply in_or_app; left; exact Hb | exact FM | exact RS].
          + exact HLN.
          + eapply (ah_mpres_trans H HH); [exact MP | apply (adl_sb H DL); exact SB'].
          + apply CP1. exact CPY.
          + intros HN1. apply CP2; [exact HN1 | exact (CELLS HN1)].
          + intros HN1. apply CP3; [exact HN1 | exact (CADDR HN1)].
          + cbn [sto]. destruct STO as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 LBF]. split.
            * exact FL.
            * eapply T; [ | | | | exact F2]; cbn; lia.
            * eapply T; [ | | | | exact F3]; cbn; lia.
            * eapply T; [ | | | | exact F4]; cbn; lia.
            * replace (0xc027a8 + 2 * Z.of_nat (S k')) with (0xc027a8 + 2 * Z.of_nat k' + 2) by lia. exact WP.
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
              -- replace (0xc027a8 + Z.of_nat (2 * k')) with (0xc027a8 + 2 * Z.of_nat k') by lia. exact BY.
          + eapply atx_frame; [exact ATX | exact FM | exact RSx].
          + eapply incb_frame; [exact INCB | exact FM |].
            intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
          + exact HAL.
        - rewrite (KCS _) by (unfold callee_saved; in_solve). exact R19.
      Qed.

      (* [comment removed for export] *)
      Lemma tr_printf_first : forall r regs m msF mo sC LIBc LBc st (Kx : TSet),
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0x1ef184) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate 0 1 r regs m mo sC LIBc LBc st ->
        getr regs 1 = Z_to_bv 64 0x1ef0d8 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 0 -> Kx [] ->
        (forall regs' m' msF' mo',
           as_VIS H sC msF' = mkst regs' (Z_to_bv 64 0x1ef0d8) m' rom -> as_AKREL H sC (mkCfg msF' mo') ->
           lstate 1 1 r regs' m' mo' sC LIBc LBc st -> getr regs' 19 = Z_to_bv 64 0 ->
           realizes asegs (mkCfg msF' mo') Kx) ->
        realizes asegs (mkCfg msF mo) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) Kx).
      Proof.
        intros r regs m msF mo sC LIBc LBc st Kx HV HA [LR R21 K4 TI TF RH PERM HL HLN MP CPY CELLS CADDR STO ATX INCB HAL] R1 R11 R19 K0 HK.
        pose proof SPlo. pose proof SPhi. pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb. cbn [sto] in STO.
        destruct (ti_can _ TI) as [can [CAN CAN64]]. destruct (ti_sh0 _ TI) as [shi [SH0 Hshi]].
        pose proof LR as (Q2 & Q4 & Q8 & Q9 & Q18 & Q20 & Q22 & Q23).
        assert (PH : ap1H regs m (Z_to_bv 64 (bv_unsigned sp - 80)) can).
        { split; rewrite ?u_small by lia.
          - exact R1.
          - exact Q2.
          - exact R11.
          - rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
          - unfold ASP_LO. lia.
          - unfold ASP_HI. lia.
          - eapply astk_stk_ok; [exact (ti_stk _ TI) | unfold ATR_STACK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | lia | lia].
          - exact (atinv_ro _ TI).
          - exact (ti_relro _ TI).
          - apply apf1_cells_of; [exact (ti_ac _ TI) | exact STO].
          - exact CAN.
          - exact CAN64.
          - intros a Ha. eapply (stack0_qsh0 m _ _ (bv_unsigned sp - 80) SH0); [unfold ATR_STACK; lia | lia | rewrite ASHADOW_BASE_val; exact Ha]. }
        unfold W. cbn [map].
        apply (drv_printf_first H DL sC msF mo regs m (Z_to_bv 64 (bv_unsigned sp - 80)) can Kx PH HV HA (Hfd1 mo MP) K0).
        intros regs' mem' msF' mo' PP HV' HA' SB'. destruct PP. rewrite u_small in P_frame by lia.
        assert (RS : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 3400), 3400); (Z_to_bv 64 0x5ede88, 232); (Z_to_bv 64 0xc027a8, 1)] -> atr_region rr).
        { intros rr Hr. pf_region Hr. }
        assert (RSx : forall rr, In rr [(Z_to_bv 64 (bv_unsigned sp - 80 - 3400), 3400); (Z_to_bv 64 0x5ede88, 232); (Z_to_bv 64 0xc027a8, 1)] -> atx_ok rr /\ 0 <= snd rr).
        { intros rr Hr. cbn [In] in Hr. unfold atx_ok.
          repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; cbn [fst snd]; rewrite ?u_small by lia; lia. }
        pose proof (copy_frame m mem' _ P_frame RS) as (CP1 & CP2 & CP3).
        apply (HK regs' mem' msF' mo' HV' HA').
        - split.
          + unfold loop_base. rewrite (P_cs 4%bv), (P_cs 8%bv), (P_cs 9%bv), (P_cs 18%bv), (P_cs 20%bv), (P_cs 22%bv), (P_cs 23%bv) by in_solve. rewrite P_sp. split; [reflexivity | exact (proj2 LR)].
          + rewrite (P_cs _) by in_solve. exact R21.
          + intros rr Hrr. rewrite (P_cs rr) by (in_from Hrr). apply K4. exact Hrr.
          + eapply atinv_frame; [exact TI | exact P_frame | exact RS].
          + eapply atframe_agree; [exact TF|]. intros x Hx. apply (proj1 P_frame). apply outside_of_disjoint.
            intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
          + eapply aheap_frame_tr; [exact RH | exact P_frame | exact RS].
          + exact PERM.
          + eapply alib_frame; [exact HL | exact RH | intros b Hb; apply in_or_app; left; exact Hb | exact P_frame | exact RS].
          + exact HLN.
          + eapply (ah_mpres_trans H HH); [exact MP | apply (adl_sb H DL); exact SB'].
          + apply CP1. exact CPY.
          + intros HN1. apply CP2; [exact HN1 | exact (CELLS HN1)].
          + intros HN1. apply CP3; [exact HN1 | exact (CADDR HN1)].
          + cbn [sto]. split; try assumption; first [reflexivity | replace (0xc027a8 + 2 * Z.of_nat 0) with 0xc027a8 by lia; exact P_wpos].
          + eapply atx_frame; [exact ATX | exact P_frame | exact RSx].
          + eapply incb_frame; [exact INCB | exact P_frame |].
            intros rr Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd]; rewrite u_small by lia; lia.
          + exact HAL.
        - rewrite (P_cs _) by in_solve. exact R19.
      Qed.
      (* [comment removed for export] *)
      Lemma tr_after_printf : forall (rn k : nat) regs m msF mo sC LIBc LBc st,
        (1 <= rn)%nat -> (k + rn = calls + 1)%nat -> (1 <= k)%nat ->
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0x1ef0d8) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate k k (Z.of_nat rn) regs m mo sC LIBc LBc st -> getr regs 19 = Z_to_bv 64 0 ->
        realizes asegs (mkCfg msF mo) K.
      Proof.
        induction rn as [|rn IH]; intros k regs m msF mo sC LIBc LBc st Hrn Hk Hk1 HV HA LS R19; [lia|].
        pose proof Hcalls as HC. pose proof SPlo. pose proof SPhi.
        destruct rn as [|rn'].
        - assert (Ek : k = calls) by lia. subst k. eapply tr_free; [exact HV | exact HA | exact LS | exact R19].
        - destruct LS as [LR R21 K4 TI TF RH PERM HL HLN MP CPY CELLS CADDR STO ATX INCB HAL].
          eapply (seg_T7more H DL sp SP16 SPlo SPhi sC msF mo regs m _ _ _ (Z.of_nat (S (S rn'))) K LR R19 R21 ltac:(lia)
                    (atinv_stk128 m TI) (atinv_ro m TI) (ti_relro m TI) (atinv_latch m TI)); [| exact HV | exact HA].
          intros regs1 msF1 mo1 HV1 HA1 SB1 LR1 Q19 Q21 K4a.
          replace (Z.of_nat (S (S rn')) - 1) with (Z.of_nat (S rn')) in Q21 by lia.
          assert (LS1 : lstate k k (Z.of_nat (S rn')) regs1 m mo1 sC LIBc LBc st).
          { split; try assumption.
            - intros rr Hrr. rewrite (K4a rr Hrr). apply K4. exact Hrr.
            - eapply (ah_mpres_trans H HH); [exact MP | apply (adl_sb H DL); exact SB1]. }
          eapply (tr_call_harness k _ regs1 m msF1 mo1 sC LIBc LBc st K ltac:(lia) HV1 HA1 LS1).
          intros regs2 m2 msF2 mo2 sC2 LIBc2 LBc2 st2 HV2 HA2 LS2 T1 T11 T19.
          eapply (tr_printf_buf k _ regs2 m2 msF2 mo2 sC2 LIBc2 LBc2 st2 K ltac:(lia) HV2 HA2 LS2 T1 T11 T19).
          intros regs3 m3 msF3 mo3 HV3 HA3 LS3 U19.
          eapply (IH (S k)); [lia | lia | lia | exact HV3 | exact HA3 | exact LS3 | exact U19].
      Qed.

      (* [comment removed for export] *)
      Lemma tr_loop : forall regs m msF mo sC LIBc LBc st,
        as_VIS H sC msF = mkst regs (Z_to_bv 64 0x1ef0b4) m rom -> as_AKREL H sC (mkCfg msF mo) ->
        lstate 0 0 (Z.of_nat calls) regs m mo sC LIBc LBc st -> K [] ->
        realizes asegs (mkCfg msF mo) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
      Proof.
        intros regs m msF mo sC LIBc LBc st HV HA LS K0. pose proof Hcalls as HC.
        eapply (tr_call_harness 0 _ regs m msF mo sC LIBc LBc st _ ltac:(lia) HV HA LS).
        intros regs2 m2 msF2 mo2 sC2 LIBc2 LBc2 st2 HV2 HA2 LS2 T1 T11 T19.
        eapply (tr_printf_first _ regs2 m2 msF2 mo2 sC2 LIBc2 LBc2 st2 K HV2 HA2 LS2 T1 T11 T19 K0).
        intros regs3 m3 msF3 mo3 HV3 HA3 LS3 U19.
        eapply (tr_after_printf calls 1); [lia | lia | lia | exact HV3 | exact HA3 | exact LS3 | exact U19].
      Qed.
    End Loop.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
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

    Lemma atinv0 : atinv mem0.
    Proof.
      pose proof PRE as P. destruct (atr_st _ _ _ _ _ _ _ _ _ _ _ _ _ P) as [INV AC REL GLB CELLS TID ERR CAN RFS SH0].
      split; try assumption.
      - exact (atr_stkcj _ _ _ _ _ _ _ _ _ _ _ _ _ P).
      - intros a _. reflexivity.
      - exact (atr_aux _ _ _ _ _ _ _ _ _ _ _ _ _ P).
      - exact (atr_addr _ _ _ _ _ _ _ _ _ _ _ _ _ P).
      - exact (atr_data _ _ _ _ _ _ _ _ _ _ _ _ _ P).
      - exact (atr_cb _ _ _ _ _ _ _ _ _ _ _ _ _ P).
    Qed.

    (* [comment removed for export] *)
    Lemma pre_cells0 : cells_ok mem0 atexit_pre_cells /\ rdn RSEGS mem0 (Z_to_bv 64 0xbdcf50) 1 = Some [Z_to_bv 8 0] /\ incb 0 mem0.
    Proof.
      pose proof PRE as P. destruct (atr_st _ _ _ _ _ _ _ _ _ _ _ _ _ P) as [INV AC REL GLB CELLS TID ERR CAN RFS SH0].
      pose proof (atr_reg _ _ _ _ _ _ _ _ _ _ _ _ _ P) as RG. unfold aatexit_pre_cells, cells_ok in RG.
      inversion RG as [|c1 l1 G1 RG1]; subst. inversion RG1 as [|c2 l2 G2 RG2]; subst. inversion RG2 as [|c3 l3 G3 RG3]; subst.
      split; [| split; [exact G2 | exact G3]].
      unfold atexit_pre_cells, cells_ok. repeat apply Forall_cons; try apply Forall_nil;
        first [ exact G1 | eapply (cells_ok_In mem0 adrv_cells); [exact CELLS | solve [in_solve]] ].
    Qed.
    Lemma lib0 : al_LIBST L (al_fresh L) [] mem0.
    Proof.
      apply (alo_fresh L LOK); [| exact (atr_musl0 _ _ _ _ _ _ _ _ _ _ _ _ _ PRE)].   (* [comment removed for export] *)
      intros a Ha. rewrite wa_eq. exact (atr_lib _ _ _ _ _ _ _ _ _ _ _ _ _ PRE a Ha).
    Qed.

    Variable K : TSet.
    Hypothesis K0 : K [].
    Hypothesis HPOST : forall regs' mem' msF' mo' s', ATRpost H L sp A cap data p s0 LB mo0 regs0 mem0 regs' mem' msF' mo' s' ->
       realizes asegs (mkCfg msF' mo') K.

    Theorem as_target_run_ok : realizes asegs (mkCfg msF0 mo0) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
    Proof.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof HN as HN'. pose proof Hcfg as Hcfg'. pose proof Hcalls as HC. pose proof Hds as Hds'.
      pose proof HCLO as HCL. unfold ATR_STACK in HCL. acb.
      pose proof PRE as P.
      destruct P as [HV0 HA0 R1 R2 R4 R10 R11 R12 R13 L6 LHI _ _ _ STK STKC RH BLK [LB1 LB2] HAL AUX CAP DATA ADDR JCB0 ST OUT REG LIBP TRC LIVE FD1 FD2].
      pose proof atinv0 as TI0. pose proof pre_cells0 as (APC & Hib & INCB0). pose proof lib0 as HL0. set (ib := Z_to_bv 8 0) in Hib.
      pose proof blkA as (B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold AIMG_TOP in B4.
      pose proof (ah_costs H HH) as (C1 & C2 & C3 & C4 & _).
      pose proof (C1 N ltac:(lia)) as CM0. pose proof (C3 N ltac:(lia)) as CF0.
      assert (HCOST : atr_cost H L data = as_Cm H N + as_Cf H N + Z.of_nat calls * fuzz_cost H L N) by reflexivity.
      set (c := nth 2 data (Z_to_bv 8 0)).
      pose proof (calls_of_hdr c eq_refl) as ECALLS.
      (* [comment removed for export] *)
      eapply (seg_T0 H DL sp SP16 SPlo SPhi s0 msF0 mo0 regs0 mem0 (Z_to_bv 64 CP) (Z_to_bv 64 cfg) (Z_to_bv 64 PL) (Z_to_bv 64 N) ib _
                R1 R2 R4 R10 R11 R12 R13 Hib APC (atinv_stk128 mem0 TI0) (atinv_ro mem0 TI0) (ti_relro mem0 TI0) (atinv_latch mem0 TI0));
        [| exact HV0 | exact HA0].
      intros regs1 mem1 msF1 mo1 HV1 HA1 SB1 LR1 K6a FM1 STK1 TF1 HAD.
      assert (Q1 : forall r, In r (regTb_w sp) -> quiet_region r).
      { intros r Hr. unfold regTb_w in Hr. cbn [In] in Hr. unfold quiet_region, ATR_STACK.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; rewrite u_small by lia; lia. }
      assert (TI1 : atinv mem1) by (eapply atinv_frame; [exact TI0 | exact FM1 | intros r Hr; apply quiet_atr; apply Q1; exact Hr]).
      assert (RH1 : as_RHEAP H s0 LB mem1) by (eapply aheap_frame_tr; [exact RH | exact FM1 | intros r Hr; apply quiet_atr; apply Q1; exact Hr]).
      assert (ST1 : sto 0 mem1) by (eapply (sto_frame 0); [lia | exact OUT | exact FM1 | exact Q1]).
      assert (ATX1 : cells_ok mem1 atexit_done_cells) by (apply HAD; subst ib; reflexivity).
      assert (INCB1 : incb 0 mem1).
      { eapply incb_frame; [exact INCB0 | exact FM1 |]. intros r Hr. unfold regTb_w in Hr. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; rewrite u_small by lia; lia. }
      assert (HL1 : al_LIBST L (al_fresh L) [] mem1).
      { eapply (alib_frame (al_fresh L) [] s0 LB); [exact HL0 | exact RH | intros b [] | exact FM1 | intros r Hr; apply quiet_atr; apply Q1; exact Hr]. }
      pose proof (ti_data _ TI1) as DATA1.
      assert (HC1 : cfg <> 0 -> rdn RSEGS mem1 (Z_to_bv 64 CP) 1 = Some [c]).
      { intros _. subst c CP. pose proof (rdn_nth RSEGS mem1 (length data) (Z_to_bv 64 A) data 2 DATA1 ltac:(lia)) as R.
        unfold nat_to_word in R. rewrite lit_add_lit in R. exact R. }
      assert (MP1 : as_MPRES H mo0 mo1) by (apply (adl_sb H DL); exact SB1).
      clear TI0 RH DATA.
      pose proof (alo_fresh_b L LOK) as FB.
      destruct (Z.eq_dec N 0) as [N0|N1].
      - (* [comment removed for export] *)
        rewrite N0 in LR1.
        eapply (seg_T1zero H DL sp SP16 SPlo SPhi s0 msF1 mo1 regs1 mem1 cfg _ _ c _ LR1 ltac:(lia) HC1 ltac:(subst CP; rewrite u_small by lia; lia)
                  (atinv_stk128 mem1 TI1) (atinv_ro mem1 TI1) (ti_relro mem1 TI1) (atinv_latch mem1 TI1)); [| exact HV1 | exact HA1].
        intros regs2 msF2 mo2 HV2 HA2 SB2 LR2 Q21 K4b.
        eapply (tr_loop AFUZZ_EMPTY 0 [] ltac:(left; repeat split; lia) K HPOST regs2 mem1 msF2 mo2 s0 [] LB (al_fresh L) HV2 HA2); [| exact K0].
        split; try assumption.
        + rewrite N0. exact LR2.
        + rewrite ECALLS. exact Q21.
        + intros rr Hrr. rewrite (K4b rr Hrr). apply K6a. cbn [In] in Hrr |- *. tauto.
        + apply Permutation_refl.
        + rewrite FB. cbn [length Z.of_nat lb_bytes fold_right]. unfold ALIB_CNT_MAX, ALIB_BYTES_MAX. lia.
        + eapply (ah_mpres_trans H HH); [exact MP1 | apply (adl_sb H DL); exact SB2].
        + assert (E : ds = []) by (apply length_zero_iff_nil; rewrite Hds, N0; reflexivity). rewrite E. reflexivity.
        + intros; lia.
        + intros; lia.
        + unfold spent. rewrite N0 in *. lia.
      - (* [comment removed for export] *)
        eapply (seg_T1pos H DL sp SP16 SPlo SPhi s0 msF1 mo1 regs1 mem1 N cfg _ _ c _ LR1 ltac:(lia) ltac:(lia) HC1 ltac:(subst CP; rewrite u_small by lia; lia)
                  (atinv_stk128 mem1 TI1) (atinv_ro mem1 TI1) (ti_relro mem1 TI1) (atinv_latch mem1 TI1)); [| exact HV1 | exact HA1].
        intros regs2 msF2 mo2 HV2 HA2 SB2 LR2 Q21 K6b.
        eapply (seg_T2 H DL sp SP16 SPlo SPhi s0 msF2 mo2 regs2 mem1 _ _ _ _ _ _ LR2 Q21
                  (atinv_stk128 mem1 TI1) (atinv_ro mem1 TI1) (ti_relro mem1 TI1) (atinv_latch mem1 TI1)); [| exact HV2 | exact HA2].
        intros regs3 msF3 mo3 HV3 HA3 SB3 LR3 U21 U1 U10 K6c.
        pose proof LR3 as (V2 & V4 & V8 & V9 & V18 & V19 & V21).
        destruct (ti_aux _ TI1) as [B' [AUX1 [HB' AUXV1]]]. destruct (ti_errno _ TI1) as [errv ERR].
        assert (MP3 : as_MPRES H mo0 mo3).
        { eapply (ah_mpres_trans H HH); [exact MP1|]. eapply (ah_mpres_trans H HH); apply (adl_sb H DL); [exact SB2 | exact SB3]. }
        change (Z_to_bv 64 0x1bf174) with (Z_to_bv 64 AMALLOC_STUB) in HV3.
        eapply (amalloc_call H HH DL regs3 mem1 msF3 mo3 s0 LB N (bv_unsigned sp - ATR_STACK) B' errv 0x1ef05c [] _ HV3 HA3 U1);
          [ lia | reflexivity | exact V4 | exact U10 | lia | exact RH1
          | apply (ah_alloc H HH s0 LB mem1 N RH1); [lia | unfold ADRV_LIVE in LIVE; lia | unfold ADRV_CNT in LIVE; lia]
          | rewrite HCOST in HAL; pose proof (fuzz_cost_nonneg N ltac:(lia)); nia
          | exact AUX1 | rewrite V2, u_small by lia; lia
          | rewrite V2, u_small by lia; exact (atinv_stklo mem1 TI1)
          | unfold ATR_STACK; lia | rewrite V2, u_small by lia; unfold AMALLOC_STACK, ATR_STACK; lia
          | rewrite V2, u_small by lia; unfold ATR_STACK; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
          | rewrite V4; unfold AERRNO; rewrite u_small by (unfold ATP; lia); exact ERR | exact (ti_inv _ TI1) | exact (ti_ac _ TI1)
          | apply (ah_chain_nil H HH); rewrite V8, u_small by lia; lia
          | cbn [map snd]; destruct TRC as (_ & _ & _ & _ & T5 & _); exact T5 |].
        intros regs4 mem4 msF4 mo4 D pD s4 errv4 junk HV4 HA4 MP4 KEPT W10 INV4 STK4 ERR4 AUX4 HP4 HBR4 RH4 CB4 AD4 AC4 HAL4.
        rewrite V2, u_small in STK4, HP4 by lia. rewrite V4 in ERR4.
        pose proof HBR4 as (D1 & D2 & D3 & D4 & D5 & D6 & D7). unfold AIMG_TOP in D4.
        assert (TI4 : atinv mem4).
        { eapply (atinv_apres mem1 mem4 LB B'); try assumption.
          - eapply (aauxv_ok_apres H); [exact AUXV1 | exact HP4 | lia].
          - rewrite u_small in ERR4 by (unfold ATP; lia). exact ERR4.
          - eapply (RFS_via_apres H HH); [exact (ti_rfs _ TI1) | exact HP4].
          - intros shi SH. eapply stack0_xpres; [apply xpres_of_apres; exact HP4 | exact SH | constructor]. }
        assert (TF4 : tframe sp mem4 (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)).
        { eapply atframe_agree; [exact TF1|]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP4 _ (u64_range x) ltac:(left; lia))). }
        assert (ST4 : sto 0 mem4) by (eapply (sto_apres 0); [lia | exact ST1 | exact HP4]).
        assert (ATX4 : cells_ok mem4 atexit_done_cells) by (eapply atx_apres; [exact ATX1 | exact HP4]).
        assert (INCB4 : incb 0 mem4) by (eapply incb_apres; [exact INCB1 | exact HP4]).
        assert (HL4 : al_LIBST L (al_fresh L) [] mem4) by (eapply alib_apres; [exact HL1 | exact HP4 | intros b []]).
        pose proof (ti_data _ TI4) as DATA4.
        (* [comment removed for export] *)
        pose proof (KEPT 2%bv ltac:(in_solve)) as S2. pose proof (KEPT 4%bv ltac:(in_solve)) as S4. pose proof (KEPT 8%bv ltac:(in_solve)) as S8.
        pose proof (KEPT 9%bv ltac:(in_solve)) as S9. pose proof (KEPT 18%bv ltac:(in_solve)) as S18. pose proof (KEPT 19%bv ltac:(in_solve)) as S19.
        pose proof (KEPT 20%bv ltac:(in_solve)) as S20. pose proof (KEPT 21%bv ltac:(in_solve)) as S21.
        assert (LR4 : regs138 sp regs4 (Z_to_bv 64 N) (Z_to_bv 64 PL) (Z_to_bv 64 cfg) (Z_to_bv 64 CP)).
        { unfold regs138. rewrite S2, S4, S8, S9, S18, S19, S20. exact LR3. }
        eapply (seg_T3 H DL sp SP16 SPlo SPhi s4 msF4 mo4 regs4 mem4 _ _ _ _ _ (Z_to_bv 64 D) _ LR4 ltac:(rewrite S21; exact U21) W10 ltac:(rewrite u_small by lia; lia)
                  (atinv_stk128 mem4 TI4) (atinv_ro mem4 TI4) (ti_relro mem4 TI4) (atinv_latch mem4 TI4)); [| exact HV4 | exact HA4].
        intros regs5 msF5 mo5 HV5 HA5 SB5 LR5 X21 X1 X10 X11 X12 K6d.
        pose proof LR5 as (Y2 & Y4 & Y8 & Y9 & Y18 & Y19 & Y21).
        (* [comment removed for export] *)
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
          eapply rdn_firstn; [exact R | subst N cfg; unfold hdr_payload_len; (first [clear - Hcfg'; lia | lia])]. }
        assert (HPL : A + 6 <= PL /\ PL + N <= A + cap /\ PL + N = A + Z.of_nat (length data)).
        { subst PL N cfg. unfold hdr_payload_len in *. lia. }
        destruct HPL as (PL1 & PL2 & PL3).
        change (Z_to_bv 64 0x1bdaac) with (Z_to_bv 64 AMEMCPY_STUB) in HV5.
        eapply (amemcpy_call regs5 mem4 msF5 mo5 s4 (bv_unsigned sp - 80) D PL N (bv_unsigned sp - ATR_STACK) ds junk 0x1ef070 _ HV5 HA5 X1);
          [ lia | reflexivity | exact Y2 | exact X10 | exact X11 | exact X12
          | apply ardn_bytes_at; [exact SRC | lia | rewrite Hds; lia]
          | exact Hds | exact CB4 | exact DISJ | lia | lia | lia
          | eapply addressable_accessible; [exact (ti_addr _ TI4) | lia | lia | unfold AAPP_HI; lia]
          | eapply addressable_accessible; [exact AD4 | lia | lia | unfold AAPP_HI; lia]
          | eapply shvis_sub; [eapply (ah_blk_shvis H HH); [exact RH4 | right; exact BLK] | lia | lia | lia | lia | lia]
          | eapply (ah_blk_shvis H HH); [exact RH4 | left; reflexivity]
          | eapply aapp_in_app_mem; [exact B7 | lia | lia]
          | eapply aapp_in_app_mem; [exact D7 | lia | lia]
          | eapply aconst_ok_aapp; [exact D7 | lia | lia]
          | exact (atinv_stklo mem4 TI4) | unfold ATR_STACK; lia | unfold ATR_STACK; lia | lia
          | left; unfold ATR_STACK; lia | left; unfold ATR_STACK; lia
          | exact (ti_inv _ TI4) | exact (ti_ac _ TI4) |].
        intros regs6 mem5 msF6 mo6 HV6 HA6 MP6 KEEP6 Z10 MU5 WM5 INV5 STK5 CB5 BY5 AC5.
        assert (TI5 : atinv mem5).
        { eapply (atinv_copy mem4 mem5 D N ((pD, D, N) :: LB) s4 TI4 MU5 WM5 INV5 STK5 AC5 HBR4 ltac:(clear -DJ0; lia) RH4); [right; exact BLK | exists pD; left; reflexivity]. }
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
          eapply Forall_impl; [| apply astdout0_range]. intros [[a w] v] Ra. cbn. (first [clear - Ra D5 D4 D3 HCL; lia | lia]). }
        assert (CPY5 : rdn RSEGS mem5 (Z_to_bv 64 D) (length ds) = Some ds).
        { pose proof (rw_rdn mem5 D _ CB5) as R. cbn [cells_size csize cells_bytes cbytes Nat.add] in R.
          rewrite Nat.add_0_r, app_nil_r, <- Hds in R. exact R. }
        assert (AD5 : addressable mem5 D N).
        { eapply addressable_transport; [exact AD4 | exact MU5 | exact WM5 |].
          pose proof (aapp_disjoint_sh D N D N D7 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as SD.
          pose proof (sh_nsh_high D N ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; (first [clear - D5 ACEILB; lia | lia]))).
          cbn. unfold AHI_LO in *. repeat split; (first [clear - SD H0 Hlo; lia | lia]). }
        assert (IMG5 : forall x n, x + n <= 0xc04000 -> disjoint_from [(D, D + N); (bv_unsigned sp - 80 - 4096, bv_unsigned sp - 80)]%Z x n).
        { intros x n Hx. cbn. lia. }
        assert (ATX5 : cells_ok mem5 atexit_done_cells) by (eapply atx_munch; [exact ATX4 | exact MU5 | exact IMG5]).
        assert (INCB5 : incb 0 mem5).
        { unfold incb in *. eapply rdn_munch; [exact MU5 | exact INCB4 | lia | cbn; lia |]. intros x Hx. cbn in Hx |- *. lia. }
        assert (HL5 : al_LIBST L (al_fresh L) [] mem5).
        { eapply alib_munch; [exact HL4 | exact MU5 | exact WM5 |]. intros x Hx. unfold alibx_ok in Hx. cbn. lia. }
        assert (MP6' : as_MPRES H mo0 mo6).
        { eapply (ah_mpres_trans H HH); [exact MP3|]. eapply (ah_mpres_trans H HH); [exact MP4|].
          eapply (ah_mpres_trans H HH); [apply (adl_sb H DL); exact SB5 | exact MP6]. }
        pose proof (KEEP6 2%bv ltac:(in_solve)) as T2. pose proof (KEEP6 4%bv ltac:(in_solve)) as T4. pose proof (KEEP6 8%bv ltac:(in_solve)) as T8.
        pose proof (KEEP6 9%bv ltac:(in_solve)) as T9. pose proof (KEEP6 18%bv ltac:(in_solve)) as T18. pose proof (KEEP6 19%bv ltac:(in_solve)) as T19.
        pose proof (KEEP6 20%bv ltac:(in_solve)) as T20. pose proof (KEEP6 21%bv ltac:(in_solve)) as T21.
        assert (LR6 : regs138 sp regs6 (Z_to_bv 64 N) (Z_to_bv 64 PL) (Z_to_bv 64 D) (Z_to_bv 64 CP)).
        { unfold regs138. rewrite T2, T4, T8, T9, T18, T19, T20. exact LR5. }
        eapply (seg_T4 H DL sp SP16 SPlo SPhi s4 msF6 mo6 regs6 mem5 _ _ (Z_to_bv 64 cfg) _ _ _ _ LR6 ltac:(rewrite T21; exact X21)
                  (atinv_stk128 mem5 TI5) (atinv_ro mem5 TI5) (ti_relro mem5 TI5) (atinv_latch mem5 TI5)); [| exact HV6 | exact HA6].
        intros regs7 msF7 mo7 HV7 HA7 SB7 LR7 Z21 K4e.
        eapply (tr_loop D D [(pD, D, N)] ltac:(right; split; [lia | split; [reflexivity | exists pD; split; [reflexivity | exact HBR4]]]) K HPOST
                  regs7 mem5 msF7 mo7 s4 [] ((pD, D, N) :: LB) (al_fresh L) HV7 HA7); [| exact K0].
        split; try assumption.
        + rewrite ECALLS. exact Z21.
        + intros rr Hrr. assert (Hrr6 : In rr ([22; 23; 24; 25; 26; 27]%bv : list reg)) by (cbn [In] in Hrr |- *; tauto).
          rewrite (K4e rr Hrr), (KEEP6 rr) by (unfold aheap_kept; in_from Hrr).
          rewrite (K6d rr Hrr6), (KEPT rr) by (unfold aheap_kept; in_from Hrr).
          rewrite (K6c rr Hrr6), (K6b rr Hrr6). apply K6a. exact Hrr6.
        + apply Permutation_refl.
        + rewrite FB. cbn [length Z.of_nat lb_bytes fold_right]. unfold ALIB_CNT_MAX, ALIB_BYTES_MAX. lia.
        + eapply (ah_mpres_trans H HH); [exact MP6' | apply (adl_sb H DL); exact SB7].
        + intros _. exact CB5.
        + intros _. exact AD5.
        + unfold spent. lia.
    Qed.

  End Call.

  (* [comment removed for export] *)
  Theorem as_target_run : as_target_run_stmt H L.
  Proof.
    intros sp A cap data p s LB msF mo regs mem K PRE K0 HPOST.
    exact (as_target_run_ok sp A cap data p s LB msF mo regs mem PRE K K0 HPOST).
  Qed.
End TR.

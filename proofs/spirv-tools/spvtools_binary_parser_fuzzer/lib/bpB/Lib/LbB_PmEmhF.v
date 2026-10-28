From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem LbB_RwStm.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_Own LbB_HEmpStmt LbB_DStat.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmEmhW.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmEmh.

Section EmhF.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Definition emh_W (spz ff fp : Z) : list (Z * Z) :=
    [(aceil, spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)].

  Definition emh_in (spz ff fp : Z) (iv : Z * Z) : Prop :=
    exists w, In w (emh_W spz ff fp) /\ fst w <= fst iv /\ snd iv <= snd w.

  Lemma emh_fresh : forall LF m ff fp, as_RFS H ((1, ff, fp) :: LF) m -> fresh_frame H LF 1 ff fp.
  Proof using HHbp.
    intros LF m ff fp RF. pose proof (rt_bp_base H HHbp) as HB.
    destruct (ah_RFS_range H HB _ _ RF) as [FO FR].
    pose proof (ah_RFS_nodup H HB _ _ RF) as ND. cbn [map ff_addr fst snd] in ND. apply NoDup_cons_iff in ND as [NI _].
    split; [exact (FR (1, ff, fp) (or_introl eq_refl)) | split; [exact FO |]].
    intros f Hf. assert (Hne : ff <> ff_addr f) by (intros E; apply NI; rewrite E; apply in_map; exact Hf).
    exact (ah_RFS_disj H HB _ _ (1, ff, fp) f RF (or_introl eq_refl) (or_intror Hf) Hne).
  Qed.

  Lemma emh_place : forall LF m0 LB0 obj spz ff fp, as_RFS H LF m0 -> fresh_frame H LF 1 ff fp ->
    map_live_frame LF obj -> aceil + 128 <= spz -> spz <= 2 ^ 47 -> spz mod 16 = 0 ->
    AIMG_TOP <= ff /\ ff + 128 <= emh_sq spz /\ ff mod 64 = 0 /\ (ff + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= ff)
    /\ AIMG_TOP <= fp /\ fp + 1 <= ff /\ (fp + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= fp)
    /\ emp_src H LB0 (emh_sq spz) obj (ff + 32) 8.
  Proof using HHbp.
    intros LF m0 LB0 obj spz ff fp _ FF (f & INF & OB1 & OB2) SPLO _ _.
    pose proof (fresh_frame_facts H LF 1 ff fp FF) as (_ & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    destruct FF as (_ & _ & FDJ). destruct (FDJ f INF) as [FD _].
    change (fsz 1) with 128 in R2, P6, FD.
    unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in P9. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in *.
    assert (SQ : spz - 96 < emh_sq spz) by (unfold emh_sq; Z.div_mod_to_equations; lia).
    assert (SH1 : sh (as_FSB H) <= sh (ff + 32)) by (apply sh_mono; lia).
    assert (SH2 : sh (ff + 32) + nsh 8 <= sh (as_FSB H + 0xb09000)).
    { change (nsh 8) with 1. rewrite <- (sh_add8 (ff + 32) 1). apply sh_mono. lia. }
    split; [lia|]. split; [lia|]. split; [exact M64|]. split; [lia|].
    split; [lia|]. split; [lia|]. split; [lia|].
    unfold emp_src, aclient_range, apart. split; [|split].
    - do 4 right. left. unfold AFS_SIZE. lia.
    - do 5 right. left. split; [exact SH1 | exact SH2].
    - destruct FD; lia.
  Qed.

  Lemma emh_rfs : forall LF0 m m' W spz ff fp, as_RFS H LF0 m -> munch W m m' -> wmono asegs m m' -> spz <= 2 ^ 47 ->
    (forall iv, In iv W -> (aceil <= fst iv /\ snd iv <= spz)
       \/ (In (1, ff, fp) LF0 /\ ((ff <= fst iv /\ snd iv <= ff + fsz 1) \/ (sh ff <= fst iv /\ snd iv <= sh ff + fshn 1)))) ->
    as_RFS H LF0 m'.
  Proof using HHbp.
    intros LF0 m m' W spz ff fp RFS MU WM _ HW.
    pose proof (ah_RFS_range H (proj1 HHbp) LF0 m RFS) as [(_ & FS2 & _ & FS4) FR].
    pose proof aceil_facts as [[C1 _] _].
    eapply (ah_RFS_frame H (proj1 HHbp)); [exact RFS | exact MU | exact WM |].
    apply Forall_forall. intros iv Hiv. unfold afs_write_ok.
    destruct (HW iv Hiv) as [[S1 _] | [HIn [[F1 F2] | [D1 D2]]]].
    -
      left. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. split; right; lia.
    -
      right. exists (1, ff, fp). split; [exact HIn|]. cbn [ff_addr ff_class fst snd]. lia.
    -
      left. pose proof (FR _ HIn) as (_ & R1 & R2 & _). cbn [ff_addr ff_class ff_flag fst snd] in R1, R2.
      change (fsz 1) with 128 in R2. change (fshn 1) with 16 in D2. unfold AFS_HDR in R1.
      pose proof (aapp_bounds _ _ FS4 ltac:(lia)) as (_ & _ & B3 & B4 & _).
      assert (A1 : 0 <= ff) by lia. assert (A2 : ff + 128 <= AAPP_HI) by lia.
      pose proof (sh_in_shadowland ff ltac:(lia)) as [Y _].
      unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, ALOWSH_LO in *.
      destruct (aapp_disjoint_sh _ _ ff 128 FS4 A1 A2 ltac:(lia)) as [X | X]; change (nsh 128) with 16 in X.
      +
        split; [left | right]; lia.
      +
        split; right; lia.
  Qed.

  Lemma emh_release_flag0 : forall m a, fldA m a 1 0 -> mrd asegs m (wa a) = Some (b8 0).
  Proof.
    intros m a F. unfold fldA, fld in F. unfold mrd, wa.
    assert (WB : word_to_le_bytes 1 (Z_to_bv 64 0) = [b8 0]) by (vm_compute; reflexivity).
    rewrite WB in F. simpl in F.
    destruct (m (Z_to_bv 64 a)) as [x|].
    - injection F as F. subst x. reflexivity.
    - change (seg_rom asegs (Z_to_bv 64 a)) with (PropExec.seg_rom ASEGS (Z_to_bv 64 a)).
      destruct (PropExec.seg_rom ASEGS (Z_to_bv 64 a)) as [x|]; [injection F as F; subst x; reflexivity | discriminate F].
  Qed.

  Lemma emh_release : forall LF m m' ff fp,
    as_RFS H ((1, ff, fp) :: LF) m -> munch [(sh ff, sh ff + 16); (ff, ff + 8); (fp, fp + 1)] m m' -> wmono asegs m m' ->
    fldA m' fp 1 0 -> as_RFS H LF m'.
  Proof using HHbp.
    intros LF m m' ff fp RF MU WM FL.
    pose proof (rt_bp_base H HHbp) as HH.
    pose proof (ah_RFS_range H HH _ _ RF) as [(FS1 & _ & _ & FS4) FR].
    assert (FSB_BAND : (as_FSB H + AFS_SIZE <= 0x7fff7000) \/ (0x10007fff8000 <= as_FSB H)).
    { unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AFS_SIZE in FS4 |- *. destruct FS4; [left | right]; lia. }
    pose proof (FR (1, ff, fp) (or_introl eq_refl)) as (_ & AF1 & AF2 & _).
    unfold ff_class, ff_addr in AF1, AF2. cbn [fst snd] in AF1, AF2. rewrite fsz_1 in AF2.
    pose proof (ah_release H HH _ m m' _ 1 ff fp RF (or_introl eq_refl) MU WM) as KR.
    rewrite lf_remove_head in KR. apply KR; [| exact (emh_release_flag0 m' fp FL)].
    repeat apply Forall_cons; try apply Forall_nil.
    - left. left. cbn [fst snd]. unfold sh, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. rewrite ASHADOW_BASE_val.
      unfold AIMG_TOP, AFS_HDR, AFS_SIZE in FS1, AF1, AF2, FSB_BAND |- *. Z.div_mod_to_equations. split; [destruct FSB_BAND|]; lia.
    - left. right. exists (1, ff, fp). split; [left; reflexivity|].
      unfold ff_addr, ff_class. cbn [fst snd]. rewrite fsz_1. lia.
    - right. cbn [fst snd]. split; reflexivity.
  Qed.

  Lemma emh_keep_achi : forall lo hi, AHI_LO <= lo -> aconst_ok (lo, hi).
  Proof.
    intros lo hi L1. apply aconst_ok_high; cbn; [| unfold AHI_LO in *; lia].
    pose proof (sh_below_app AIMG_TOP ltac:(unfold AIMG_TOP, AAPP_HI; lia)). apply (Z.le_trans _ AHI_LO); [| exact L1].
    unfold sh, AIMG_TOP, AHI_LO. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
  Qed.

  Lemma emh_keep_acap : forall A n lo hi, aapp A n -> A <= lo -> hi <= A + n -> aconst_ok (lo, hi).
  Proof.
    intros A n lo hi AP L1 L2. destruct AP as [[P1 P2]|[P1 P2]]; [| apply emh_keep_achi; lia].
    apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
      AF_DCO_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP, ALOWSH_LO in *;
      rewrite ?ASHADOW_BASE_val; try lia.
  Qed.

  Lemma emh_keep_acsh : forall A lo hi, AIMG_TOP <= A -> sh A <= lo -> aconst_ok (lo, hi).
  Proof.
    intros A lo hi HA HS. apply aconst_ok_high; cbn.
    - pose proof (sh_mono AIMG_TOP A HA). lia.
    - right; left. unfold sh, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. lia.
  Qed.

  Lemma emh_keep_dj : forall (W : list (Z * Z)) a n,
    Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
  Proof.
    induction W as [|[l h] W IH]; intros a n F; cbn; [exact I|].
    pose proof (Forall_inv F) as F1. cbn in F1. split; [lia | exact (IH a n (Forall_inv_tail F))].
  Qed.

  Lemma emh_keep_win : forall (LB : list block) LF spz ff fp iv,
    fresh_frame H LF 1 ff fp -> emh_in spz ff fp iv ->
    aclient_write_ok H LB iv /\ aconst_ok iv /\ stack0_ok iv /\ AIMG_TOP <= fst iv
    /\ ((aceil <= fst iv /\ snd iv <= spz)
        \/ forall a, fst iv <= a < snd iv ->
           rin_ivs [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] a).
  Proof.
    intros LB LF spz ff fp [l h] (FR & FO & _) (w & Hw & L & R). cbn [fst snd] in *.
    destruct FR as (K0 & K1 & K2 & (K3 & K4) & K5 & K6). destruct FO as (F0 & F1 & F2 & F3).
    change (fsz 1) with 128 in *. change (fshn 1) with 16 in *. acb.
    pose proof (eq_refl : AFS_HDR = 0x9000) as EH. pose proof (eq_refl : AFS_FLAGS = 0x1000) as EF.
    pose proof (eq_refl : AFS_SIZE = 0xb09000) as ES. pose proof (eq_refl : AIMG_TOP = 0x6e8000) as EI.
    pose proof (sh_below_aceil AIMG_TOP ltac:(unfold AIMG_TOP, AAPP_HI; lia)) as SA.
    unfold emh_W in Hw. cbn [In] in Hw.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in L, R; try change (fsz 1) with 128 in *; try change (fshn 1) with 16 in *.
    - split; [left; cbn [fst snd]; lia|]. split; [apply emh_keep_achi; unfold AHI_LO; lia|].
      split; [left; cbn [fst snd]; unfold AHI_LO; lia|]. split; [unfold AIMG_TOP in *; lia|]. left; lia.
    - split; [right; right; right; right; left; cbn [fst snd]; unfold AFS_FLAGS, AFS_SIZE in *; lia|].
      split; [apply (emh_keep_acap (as_FSB H) AFS_SIZE); [exact F3 | lia | unfold AFS_FLAGS, AFS_SIZE in *; lia]|].
      split; [apply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F3 | lia | unfold AFS_FLAGS, AFS_SIZE in *; lia]|].
      split; [lia|]. right. intros a Ha. cbn [rin_ivs fst snd]. lia.
    - split; [right; right; right; right; left; cbn [fst snd]; unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *; lia|].
      split; [apply (emh_keep_acap (as_FSB H) AFS_SIZE); [exact F3 | unfold AFS_FLAGS in *; lia | unfold AFS_HDR, AFS_SIZE in *; lia]|].
      split; [apply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F3 | unfold AFS_FLAGS in *; lia | unfold AFS_HDR, AFS_SIZE in *; lia]|].
      split; [unfold AFS_FLAGS in *; lia|]. right. intros a Ha. cbn [rin_ivs fst snd]. lia.
    - split; [right; right; right; right; left; cbn [fst snd]; unfold AFS_HDR in *; lia|].
      split; [apply (emh_keep_acap (as_FSB H) AFS_SIZE); [exact F3 | unfold AFS_HDR in *; lia | lia]|].
      split; [apply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F3 | unfold AFS_HDR in *; lia | lia]|].
      split; [unfold AFS_HDR in *; lia|]. right. intros a Ha. cbn [rin_ivs fst snd]. lia.
    - pose proof (sh_add8 ff 16) as E. pose proof (sh_mono (ff + 8 * 16) (as_FSB H + AFS_SIZE) ltac:(lia)) as M1.
      pose proof (sh_mono (as_FSB H) ff ltac:(unfold AFS_HDR in *; lia)) as M2.
      pose proof (sh_mono (ff + 8 * 16) (@aceil HCEIL) ltac:(lia)) as M3.
      pose proof (sh_above_image ff ltac:(unfold AIMG_TOP in *; lia)) as M4.
      split; [right; right; right; right; right; left; cbn [fst snd]; lia|].
      split; [apply (emh_keep_acsh ff); [unfold AFS_HDR in *; lia | exact L]|].
      split; [right; cbn [fst snd]; lia|]. split; [lia|]. right. intros a Ha. cbn [rin_ivs fst snd]. lia.
  Qed.

  Lemma emh_keep_xr : forall (LB : list block) LF m0 spz ff fp O n, as_RFS H LF m0 -> fresh_frame H LF 1 ff fp ->
    fsobj H LF O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> aapp O n -> aclient_range H LB spz O n ->
    xclient_range H LB spz [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] O n.
  Proof using HHbp.
    intros LB LF m0 spz ff fp O n RF FF FO H0 Hn Ht Ha AR. split; [exact AR|].
    pose proof (fsobj_scratch H (rt_bp_base H HHbp) LF O n m0) as S.
    apply Forall_forall. intros iv Hiv. apply (S iv RF FO H0 Hn Ht Ha).
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]].
    - left; reflexivity.
    - right; exists 1, ff, fp; split; [exact FF | right; left; reflexivity].
    - right; exists 1, ff, fp; split; [exact FF | left; reflexivity].
    - right; exists 1, ff, fp; split; [exact FF | right; right; reflexivity].
  Qed.

  Lemma emh_keep_xs : forall (LB : list block) LF m0 spz ff fp O n, as_RFS H LF m0 -> fresh_frame H LF 1 ff fp ->
    fsobj H LF O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> aclient_range H LB spz (sh O) (nsh n) ->
    xclient_range H LB spz [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] (sh O) (nsh n).
  Proof using HHbp.
    intros LB LF m0 spz ff fp O n RF FF FO H0 Hn Ht AR. split; [exact AR|].
    pose proof (fsobj_scratch_sh H (rt_bp_base H HHbp) LF O n m0) as S.
    apply Forall_forall. intros iv Hiv. apply (S iv RF FO H0 Hn Ht).
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]].
    - left; reflexivity.
    - right; exists 1, ff, fp; split; [exact FF | right; left; reflexivity].
    - right; exists 1, ff, fp; split; [exact FF | left; reflexivity].
    - right; exists 1, ff, fp; split; [exact FF | right; right; reflexivity].
  Qed.

  Lemma emh_keep_fo : forall LF m0 O n, as_RFS H LF m0 -> 0 <= n ->
    (exists f, In f LF /\ ff_addr f <= O /\ O + n <= ff_addr f + fsz (ff_class f)) ->
    fsobj H LF O n /\ as_FSB H + AFS_HDR <= O /\ O + n <= as_FSB H + AFS_SIZE /\ as_FSB H mod 4096 = 0
    /\ aapp O n /\ 0 <= O /\ O + n <= AAPP_HI.
  Proof using HHbp.
    intros LF m0 O n RF Hn (f & Hf & L1 & L2).
    destruct (ah_RFS_range H (rt_bp_base H HHbp) LF m0 RF) as [(F0 & F1 & F2 & F3) FR].
    destruct (FR f Hf) as (K0 & K1 & K2 & _). pose proof (eq_refl : AFS_HDR = 0x9000) as EH.
    assert (AP : aapp O n) by (eapply aapp_sub; [exact F3 | lia | lia]).
    pose proof (aapp_bounds O n AP Hn) as B.
    split; [right; exists f; auto|]. split; [lia|]. split; [lia|]. split; [exact F2|]. split; [exact AP|]. lia.
  Qed.

  Lemma emh_keep_blk : forall s (LB LBm : list block) m p n, as_RHEAP H s LB m -> (forall b, In b LBm -> In b LB) ->
    In (p, n) (lbl LBm) -> ablock_range H p n /\ exists b, In b LB /\ blk_addr b = p /\ blk_size b = n.
  Proof using HHbp.
    intros s LB LBm m p n RH SUB Hin. unfold lbl in Hin. apply in_map_iff in Hin as (b & Eb & Hb).
    apply SUB in Hb. pose proof (ah_blocks H (rt_bp_base H HHbp) s LB m b RH Hb) as AB.
    inversion Eb; subst p n. split; [exact AB|]. exists b. split; [exact Hb|]. split; reflexivity.
  Qed.

  Lemma emh_keep_ag : forall (LB : list block) spz X m m' A n, xpres H LB spz X m m' -> xclient_range H LB spz X A n ->
    0 <= A -> A + n <= 2 ^ 64 -> forall a, A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
  Proof.
    intros LB spz X m m' A n XP XR H0 H1 a Ha.
    destruct (XP a ltac:(lia) (xclient_range_addr H LB spz X A n a XR Ha)) as [E _]. exact E.
  Qed.

  Lemma emh_keep_adr : forall (LB : list block) spz X m m' A n, xpres H LB spz X m m' -> addressable m A n ->
    xclient_range H LB spz X (sh A) (nsh n) -> addressable m' A n.
  Proof.
    intros LB spz X m m' A n XP [Hn (S0 & S8 & UB & UW)] XR.
    assert (XR' : xclient_range H LB spz X (sh A) (Z.of_nat (length (shadow_of n)))) by (rewrite shadow_of_length by lia; exact XR).
    split; [exact Hn|]. split; [exact S0|]. split; [exact S8|]. split.
    - exact (xpres_bytes_at H LB spz X m m' (sh A) (shadow_of n) XP UB XR').
    - exact (xpres_wr_at H LB spz X m m' (sh A) _ XP UW XR').
  Qed.

  Lemma emh_keep : forall (s : as_St H) (LB LB0 LBm : list block) (LF : list fframe) (obj bl bc keyp key : Z)
      (ents : list (Z * (Z * Z))) (B lo shi spz ff fp : Z) (errv tp : word) (m0 m m' : mem) (W : list (Z * Z)),
    fresh_frame H LF 1 ff fp -> as_RFS H LF m0 -> map_live_frame LF obj ->
    (exists f, In f LF /\ ff_addr f <= keyp /\ keyp + 4 <= ff_addr f + fsz (ff_class f)) ->
    as_RHEAP H s LB m -> Permutation LB (LB0 ++ LBm) -> Permutation (lbl LBm) (umap_blocks 24 bl bc ents) ->
    obj + 40 <= aceil -> aceil <= lo -> spz <= 2 ^ 47 -> tp = Z_to_bv 64 ATP ->
    munch W m m' -> wmono asegs m m' -> Forall (emh_in spz ff fp) W ->
    (umapx MI_A 24 (nval24 ASEGS) (lbl LB) m obj bl bc ents -> umapx MI_A 24 (nval24 ASEGS) (lbl LB) m' obj bl bc ents)
    /\ (umap_sh m 24 (bl, bc, ents) -> umap_sh m' 24 (bl, bc, ents))
    /\ (addressable m obj 40 -> addressable m' obj 40)
    /\ (fldA m keyp 4 key -> fldA m' keyp 4 key) /\ (accessible m keyp 4 -> accessible m' keyp 4)
    /\ as_RHEAP H s LB m' /\ (as_rauxv_ok H m B -> as_rauxv_ok H m' B)
    /\ (rw_cells asegs m (errno_addr tp) [C4 errv] -> rw_cells asegs m' (errno_addr tp) [C4 errv])
    /\ (ACONST m -> ACONST m') /\ (stack0 m lo shi -> stack0 m' lo shi) /\ (relro0 m -> relro0 m')
    /\ xpres H LB0 spz [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] m m'.
  Proof using HHbp.
    intros s LB LB0 LBm LF obj bl bc keyp key ents B lo shi spz ff fp errv tp m0 m m' W
      FF RF ML KF RH PL PU OA LO SPZ TP MU WM FW.
    pose proof (rt_bp_base H HHbp) as HB.
    pose proof (eq_refl : AAPP_HI = 0x800000000000) as EA. pose proof (eq_refl : 2 ^ 64 = 0x10000000000000000) as E64.
    pose proof (Forall_impl _ (fun iv Hi => emh_keep_win LB LF spz ff fp iv FF Hi) FW) as WK.
    assert (WA : Forall (aclient_write_ok H LB) W) by (eapply Forall_impl; [| exact WK]; intros iv K; exact (proj1 K)).
    assert (WC : Forall aconst_ok W) by (eapply Forall_impl; [| exact WK]; intros iv K; exact (proj1 (proj2 K))).
    assert (WS : Forall stack0_ok W) by (eapply Forall_impl; [| exact WK]; intros iv K; exact (proj1 (proj2 (proj2 K)))).
    assert (XP : xpres H LB spz [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] m m').
    { eapply (xpres_of_munch H s LB spz _ W m m m' HB RH MU WM). eapply Forall_impl; [| exact WK]. intros iv K. exact (proj2 (proj2 (proj2 (proj2 K)))). }
    assert (SUB : forall b, In b LBm -> In b LB)
      by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL | apply in_or_app; right; exact Hb]).
    assert (UB : forall p n, In (p, n) (umap_blocks 24 bl bc ents) ->
      xclient_range H LB spz [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] p n
      /\ xclient_range H LB spz [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] (sh p) (nsh n)
      /\ 0 <= p /\ p + n <= AAPP_HI).
    { intros p n Hin. apply (Permutation_in _ (Permutation_sym PU)) in Hin.
      destruct (emh_keep_blk s LB LBm m p n RH SUB Hin) as (AB & b & Hb & Ea & Es).
      pose proof AB as (A0 & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (aapp_bounds p n A6 A2) as BB. pose proof (eq_refl : AFS_SIZE = 0xb09000) as ES.
      assert (FO : fsobj H LF p n) by (left; lia).
      split; [| split; [| lia]].
      - apply (emh_keep_xr LB LF m0 spz ff fp p n RF FF FO ltac:(lia) A2 ltac:(lia) A6).
        right; right; left. exists b. split; [exact Hb|]. lia.
      - apply (emh_keep_xs LB LF m0 spz ff fp p n RF FF FO ltac:(lia) A2 ltac:(lia)).
        right; right; right; left. exists b. split; [exact Hb|]. rewrite Ea, Es. lia. }
    destruct (emh_keep_fo LF m0 obj 40 RF ltac:(lia) ML) as (OF & O1 & O2 & O3 & O4 & O5 & O6).
    pose proof (eq_refl : AFS_SIZE = 0xb09000) as ES. pose proof (eq_refl : AFS_HDR = 0x9000) as EH.
    assert (XO : xclient_range H LB spz [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] obj 40).
    { apply (emh_keep_xr LB LF m0 spz ff fp obj 40 RF FF OF O5 ltac:(lia) O6 O4). right; right; right; right; left. lia. }
    split.
    { intros U. eapply (HRepFacts.umapx_agree ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (HRepFacts.nval24_agree ASEGS) ltac:(lia)); [exact U | |].
      - intros a Ha. unfold umap_foot in Ha. destruct Ha as [Ha|[(Hbc & Ha)|(p & Hp & Ha)]].
        + exact (emh_keep_ag LB spz _ m m' obj 40 XP XO O5 ltac:(lia) a Ha).
        + assert (IB : In (bl, 8 * bc) (umap_blocks 24 bl bc ents)).
          { unfold umap_blocks. destruct (Z.eqb_spec bc 0); [contradiction|]. apply in_or_app. left. left. reflexivity. }
          destruct (UB _ _ IB) as (X1 & _ & X3 & X4).
          exact (emh_keep_ag LB spz _ m m' bl (8 * bc) XP X1 X3 ltac:(lia) a Ha).
        + apply in_map_iff in Hp. destruct Hp as [[p' [k v]] [Ep Hin]]. cbn in Ep. subst p'.
          assert (IB : In (p, 24) (umap_blocks 24 bl bc ents)).
          { unfold umap_blocks. apply in_or_app. right. apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin]. }
          destruct (UB _ _ IB) as (X1 & _ & X3 & X4).
          exact (emh_keep_ag LB spz _ m m' p 24 XP X1 X3 ltac:(lia) a Ha).
      - intros p n _ Hin. exact Hin. }
    split.
    { intros [U1 U2]. cbn [t3a t3b t3c fst snd] in U1, U2 |- *. split.
      - intros Hbc. specialize (U1 Hbc).
        assert (IB : In (bl, 8 * bc) (umap_blocks 24 bl bc ents)).
        { unfold umap_blocks. destruct (Z.eqb_spec bc 0); [contradiction|]. apply in_or_app. left. left. reflexivity. }
        destruct (UB _ _ IB) as (_ & X2 & _). exact (emh_keep_adr LB spz _ m m' bl (8 * bc) XP U1 X2).
      - intros p k v Hin. specialize (U2 p k v Hin).
        assert (IB : In (p, 24) (umap_blocks 24 bl bc ents)).
        { unfold umap_blocks. apply in_or_app. right. apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin]. }
        destruct (UB _ _ IB) as (_ & X2 & _). exact (emh_keep_adr LB spz _ m m' p 24 XP U2 X2). }
    split.
    { intros AD. apply (emh_keep_adr LB spz _ m m' obj 40 XP AD).
      apply (emh_keep_xs LB LF m0 spz ff fp obj 40 RF FF OF O5 ltac:(lia) O6).
      right; right; right; right; right; left.
      pose proof (sh_add8 obj 5) as E. pose proof (sh_mono (obj + 8 * 5) (as_FSB H + AFS_SIZE) ltac:(lia)) as M1.
      pose proof (sh_mono (as_FSB H) obj ltac:(lia)) as M2.
      change (nsh 40) with 5. lia. }
    destruct (emh_keep_fo LF m0 keyp 4 RF ltac:(lia) KF) as (KO & K1 & K2 & K3 & K4 & K5 & K6).
    split.
    { intros Fk. unfold fldA in *. eapply CRep.fld_agree; [lia | cbn; lia | exact Fk |].
      intros x Hx. unfold zwin in Hx.
      assert (XK : xclient_range H LB spz [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] keyp 4).
      { apply (emh_keep_xr LB LF m0 spz ff fp keyp 4 RF FF KO K5 ltac:(lia) K6 K4). right; right; right; right; left. lia. }
      exact (emh_keep_ag LB spz _ m m' keyp 4 XP XK K5 ltac:(lia) x ltac:(cbn in Hx; lia)). }
    split.
    { intros (A0 & A1 & AC). split; [exact A0|]. split; [exact A1|]. intros x Hx.
      destruct (AC x Hx) as (v & Hv & Hr & Hb). exists v. split; [exact Hv|]. split; [|exact Hb].
      rewrite <- Hr. unfold mrd.
      destruct (emh_keep_fo LF m0 x 1 RF ltac:(lia) ltac:(destruct KF as (f & Hf & L1 & L2); exists f; split; [exact Hf | lia]))
        as (XO1 & X1 & X2 & X3 & X4 & X5 & X6).
      assert (XS : xclient_range H LB spz [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] (sh x) (nsh 1)).
      { apply (emh_keep_xs LB LF m0 spz ff fp x 1 RF FF XO1 X5 ltac:(lia) X6).
        right; right; right; right; right; left. change (nsh 1) with 1.
        pose proof (sh_mono (as_FSB H) x ltac:(lia)) as M2.
        unfold sh. unfold sh in M2. Z.div_mod_to_equations. lia. }
      pose proof (sh_below_app x ltac:(lia)) as SB. pose proof (sh_above_image x ltac:(lia)) as SA.
      change (wa (sh x)) with (Z_to_bv 64 (sh x)).
      rewrite (emh_keep_ag LB spz _ m m' (sh x) (nsh 1) XP XS ltac:(unfold AIMG_TOP in *; lia)
                 ltac:(change (nsh 1) with 1; unfold AHI_LO in *; lia) (sh x) ltac:(change (nsh 1) with 1; lia)).
      reflexivity. }
    split; [eapply (ah_RHEAP_frame H HB); [exact RH | exact MU | exact WM | exact WA]|].
    split; [intros RA; eapply (ah_rauxv_frame H HB); [exact RA | exact MU | exact WM | exact WA]|].
    split.
    { intros ER. eapply rw_cells_transport; [exact ER | exact MU | exact WM |]. apply emh_keep_dj.
      eapply Forall_impl; [| exact WK]. intros iv K. destruct K as (_ & _ & _ & K & _). left.
      subst tp. rewrite HLib.u64_of_Z by (unfold ATP; lia). cbn. unfold ATP, AIMG_TOP in *. lia. }
    split; [intros AC; exact (ACONST_frame W m m' AC MU WM WC)|].
    split; [intros S0; exact (stack0_transport W m m' lo shi S0 MU WM WS)|].
    split.
    { intros R i Hi. rewrite (MU (Z_to_bv 64 i)); [apply R; exact Hi|].
      rewrite HLib.u64_of_Z by lia. apply (disjoint_outside W i 1 i); [| lia]. apply emh_keep_dj.
      eapply Forall_impl; [| exact WK]. intros iv K. destruct K as (_ & _ & _ & K & _). left. unfold AIMG_TOP in *. lia. }
    eapply (xpres_weaken H LB LB0 spz spz _ _ m m' XP (Z.le_refl _)); [| intros a K; exact K].
    intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PL | apply in_or_app; left; exact Hb].
  Qed.
End EmhF.

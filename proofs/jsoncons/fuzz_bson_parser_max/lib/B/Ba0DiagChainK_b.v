(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvPiece_b Ba0DiagLoopK_b Ba0DrvStdio_b Ba0DrvPrintfK_b Ba0DrvPrintf1_b Ba0DrvExit_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Ba0DiagKit_b Ba0DiagGlue_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation u64A := (L5Defs.L5.u64_at ASEGS).
#[local] Notation u32A := (L5Defs.L5.u32_at ASEGS).
#[local] Notation filew := Ba0DiagGlue_b.DG.filew.
#[local] Notation agree0 := Ba0DiagGlue_b.DG.agree0.
#[local] Notation rom := (seg_rom ASEGS).

(* [comment removed for export] *)
Record dg_wvA (usp S : Z) (RE : bvmap 5 word) (ME : word -> option byte) (wlo q c b1 l1 b2 l2 : Z) (bs1 bs2 : list byte) : Prop := DG_WVA {
  dw_regs : getr RE 17%bv = Z_to_bv 64 66 /\ getr RE 10%bv = Z_to_bv 64 2 /\ getr RE 11%bv = Z_to_bv 64 q /\ getr RE 12%bv = Z_to_bv 64 c
            /\ getr RE 9%bv = Z_to_bv 64 1293512 /\ getr RE 18%bv = Z_to_bv 64 c /\ getr RE 22%bv = Z_to_bv 64 (l1 + l2) /\ getr RE 19%bv = Z_to_bv 64 q;
  dw_win : S - 5440 <= wlo /\ wlo + 32 + 16 <= S /\ wlo <= q /\ q + 16 * c <= wlo + 32 /\ (c = 1 \/ c = 2);
  dw_iov0 : u64A ME q b1 /\ u64A ME (q + 8) l1;
  dw_b1 : 0 <= b1 /\ 0 <= l1 /\ b1 + l1 <= 2 ^ 47 /\ (l1 = 0 \/ b1 + l1 <= wlo \/ wlo + 32 <= b1) /\ (l1 = 0 \/ b1 + l1 <= 0x696000 \/ usp - 8388608 <= b1)
          /\ rdn ASEGS ME (Z_to_bv 64 b1) (Z.to_nat l1) = Some bs1;
  dw_c1 : c = 1 -> l2 = 0 /\ bs2 = [];
  dw_c2 : c = 2 -> u64A ME (q + 16) b2 /\ u64A ME (q + 24) l2 /\ 1 <= l1 + l2
          /\ 0 <= b2 /\ 0 <= l2 /\ b2 + l2 <= 2 ^ 47 /\ (l2 = 0 \/ b2 + l2 <= wlo \/ wlo + 32 <= b2) /\ (l2 = 0 \/ b2 + l2 <= 0x696000 \/ usp - 8388608 <= b2)
          /\ rdn ASEGS ME (Z_to_bv 64 b2) (Z.to_nat l2) = Some bs2;
  dw_tot : l1 + l2 <= 2 ^ 30;
  dw_fd : u32A ME 1293632 2
}.

(* [comment removed for export] *)
Definition dg_finA (M0 : word -> option byte) (S Sf : Z) (RF : bvmap 5 word) (MF : word -> option byte) : Prop :=
  getr RF 10%bv = Z_to_bv 64 2 /\ getr RF 2%bv = Z_to_bv 64 Sf /\ getr RF 4%bv = Z_to_bv 64 6765824
  /\ agree0 M0 MF S
  /\ u64A MF 1293552 0 /\ u64A MF 1293568 0 /\ u64A MF 1293520 0 /\ u64A MF 1293528 0.

Fixpoint dg_chain (usp : Z) (M0 : word -> option byte) (S Sf : Z) (parts : list (list byte)) (fx : PropExec.FPState) (R : bvmap 5 word) (pc : Z) (M : word -> option byte) : Prop :=
  match parts with
  | [] => exists fxF RF MF, msteps ASEGS (@mkst fx R (Z_to_bv 64 pc) M rom) (@mkst fxF RF (Z_to_bv 64 0x118878) MF rom) /\ dg_finA M0 S Sf RF MF
  | bs :: rest =>
      exists fxE RE ME wlo q c b1 l1 b2 l2 bs1 bs2,
        msteps ASEGS (@mkst fx R (Z_to_bv 64 pc) M rom) (@mkst fxE RE (Z_to_bv 64 0x120258) ME rom)
        /\ dg_wvA usp S RE ME wlo q c b1 l1 b2 l2 bs1 bs2 /\ bs = bs1 ++ bs2
        /\ agree0 M0 ME S
        /\ forall RX MX,
             (forall x : word, ~ (wlo <= bv_unsigned x < wlo + 32) -> MX x = ME x) -> mem_grows ME MX ->
             (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (Z_to_bv 5 (Z.of_nat k)) = getr RE (Z_to_bv 5 (Z.of_nat k))) ->
             dg_chain usp M0 S Sf rest fxE RX 0x120264 MX
  end.

(* [comment removed for export] *)
Definition dg_shape (parts : list (list byte)) (fs : Fs.Fs) : TSet := fold_right (fun bs K => t_emit (W 2 bs) K) (t_exit (exit_code 2) fs) parts.
Lemma dg_shape_nil : forall parts fs, dg_shape parts fs [].
Proof. intros [|bs rest] fs; cbn [dg_shape fold_right]; [apply t_exit_has_nil | apply t_emit_has_nil]. Qed.
Lemma t_emit_congrA : forall evs T T', t_eq T T' -> t_eq (t_emit evs T) (t_emit evs T').
Proof. intros evs T T' H tr. unfold t_emit. split; (intros [X|(tr' & E & Y)]; [left; exact X | right; exists tr'; split; [exact E | apply H; exact Y]]). Qed.
Lemma dg_shape_eq : forall parts fs, t_eq (dg_shape parts fs) (t_emit (W 2 (concat parts)) (t_exit (exit_code 2) fs)).
Proof.
  induction parts as [|bs rest IH]; intros fs; cbn [dg_shape fold_right concat].
  - apply t_eq_sym. apply t_emit_W_nil. apply t_exit_has_nil.
  - fold (dg_shape rest fs). eapply t_eq_trans; [|apply t_emit_W_app]. apply t_emit_congrA. apply IH.
Qed.

Section FPX_1.
Variable scfg : SpuriousCfg.
Section Chain.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hex : incl EX_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition dgW (S a : Z) : Prop := S - 5440 <= a < S \/ filew a.
  #[using="Hsp M0"] Lemma dgW_cwa : forall LB S a, usp - 4096 <= S <= usp -> dgW S a -> CWA sp0 LB a.
  Proof.
    intros LB S a HS [Ha|Ha]; unfold CWA; [right; left; pose proof Hsp; lia|]. right; right.
    exists 0x13bcc8, 0x13bfc0. split; [unfold IMG_W_A; cbn [In]; tauto | unfold Ba0DiagGlue_b.DG.filew in Ha; lia].
  Qed.
  #[using="sp0 M0"] Lemma agree0_Z : forall (Ma Mb : word -> option byte) S, agree0 Ma Mb S -> forall a, 0 <= a < 2 ^ 64 -> ~ dgW S a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a).
  Proof. intros Ma Mb S AG a Ha Hn. apply AG; rewrite u64_lit by lia; intros X; apply Hn; [left | right]; exact X. Qed.
  #[using="sp0 M0"] Lemma agree0_trans2 : forall (Mi Ma Mb : word -> option byte) S, agree0 Mi Ma S -> agree0 Mi Mb S -> forall a, 0 <= a < 2 ^ 64 -> ~ dgW S a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a).
  Proof. intros Mi Ma Mb S A1 A2 a Ha Hn. rewrite (agree0_Z Mi Mb S A2 a Ha Hn), (agree0_Z Mi Ma S A1 a Ha Hn). reflexivity. Qed.

  #[using="Type"] Lemma keep_nat : forall (R R' : bvmap 5 word), (forall r, In r WV_KEEP -> getr R' r = getr R r) ->
    forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k)).
  Proof.
    intros R R' KR k Hk. apply KR. unfold WV_KEEP. cbn [In] in Hk |- *.
    repeat (destruct Hk as [<-|Hk]; [repeat first [left; apply bv_eq; reflexivity | right]|]). destruct Hk.
  Qed.

  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex"] Theorem dg_chain_run : forall parts LB LK cr A (MVi : word -> option byte) (S Sf tid : Z) fs (fx : PropExec.FPState) R pc M (model : Model),
    dinvA LB LK cr A M model -> m_fs model = fs ->
    agree0 MVi (mrestrict (ahid A model) M) S -> mem_grows MVi (mrestrict (ahid A model) M) ->
    usp - 4096 <= S <= usp -> S <= Sf <= usp -> Sf mod 16 = 0 ->
    (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVi (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1282048 -> MVi (Z_to_bv 64 i) = None) ->
    exitE tid MVi -> stdoutPA MVi ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    dg_chain usp MVi S Sf parts fx R pc (mrestrict (ahid A model) M) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 pc) M rom) model) (dg_shape parts fs).
  Proof.
    induction parts as [|bs rest IH]; intros LB LK cr A MVi S Sf tid fs fx R pc M model D EFS AGI MGI HS HSf HSf16 WINi IMGi XAi SOPi FD2 CH; pose proof Hsp as Hsp'.
    - (* [comment removed for export] *)
      cbn [dg_chain] in CH. destruct CH as (fxF & RF & MF & MS & (F10 & F2 & F4 & AGF & C1 & C2 & C3 & C4)).
      pose proof (ArtBridge.msteps_mem_grows ASEGS _ _ MS) as MGF. cbn [ms_mem] in MGF.
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fxF R (Z_to_bv 64 pc) RF (Z_to_bv 64 0x118878) MF (dgW S) _ D MS MGF
               (agree0_trans2 MVi _ MF S AGI AGF) (fun a Ha => dgW_cwa LB S a HS Ha)).
      intros M1 model1 D1 SBM1 VIS1 FRM1.
      assert (FRi : forall a, 0 <= a < 2 ^ 64 -> ~ dgW S a -> MF (Z_to_bv 64 a) = MVi (Z_to_bv 64 a)) by (exact (agree0_Z MVi MF S AGF)).
      assert (MGiF : mem_grows MVi MF) by (eapply mem_grows_trans; [exact MGI | exact MGF]).
      assert (TR : forall a (n : nat) bs0, rdn ASEGS MVi (Z_to_bv 64 a) n = Some bs0 ->
                   (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) && ((a + Z.of_nat n <=? 1293512) || (1293652 <=? a)) && ((a + Z.of_nat n <=? 0x7fff00000000)) = true ->
                   rdn ASEGS MF (Z_to_bv 64 a) n = Some bs0).
      { intros a n bs0 Hr Hb. apply andb_prop in Hb as (Hb & B4). apply andb_prop in Hb as (Hb & B3). apply andb_prop in Hb as (B1 & B2).
        apply Z.leb_le in B1, B2, B4. apply (TRf MVi MF (dgW S) FRi a n bs0 Hr); [lia | lia|].
        intros i Hi [X|X]; [lia|]. unfold Ba0DiagGlue_b.DG.filew in X. apply orb_prop in B3 as [B3|B3]; apply Z.leb_le in B3; lia. }
      destruct XAi as (XC & TIDC & HTr & DESC). destruct SOPi as (P1 & P2 & P3 & P4 & P5).
      assert (XP : exit_preE ar HI sp0 M0 LB LK cr A M1 model1 Sf tid).
      { unfold exit_preE. rewrite VIS1. split; [exact D1|]. split; [lia|]. split; [lia|]. split; [exact HSf16|].
        split; [intros a n Ha Hn d k Hd Hk; apply (store_ok_mono ASEGS k MVi MF _ MGiF); apply (WINi a n); assumption|].
        split; [intros i Hi; rewrite FRi; [apply IMGi; exact Hi | lia | intros [X|X]; [lia | unfold Ba0DiagGlue_b.DG.filew in X; lia]]|].
        unfold exitE. split; [|split; [exact (TR _ _ _ TIDC eq_refl) | split; [exact HTr|]]].
        - unfold cells_at in *. rewrite Forall_forall in *. intros c Hin. pose proof (XC c Hin) as Hc.
          unfold XC_CELLS_E in Hin. cbn [In] in Hin.
          repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hc |- *; first [exact C1 | exact C2 | exact C3 | exact C4 | exact (TR _ _ _ Hc eq_refl)]|]). destruct Hin.
        - intros i Hi. rewrite FRi; [apply DESC; exact Hi | lia | intros [X|X]; [lia | unfold Ba0DiagGlue_b.DG.filew in X; lia]]. }
      rewrite <- EFS. rewrite <- (proj2 (sbm_fds model model1 SBM1)). cbn [dg_shape fold_right]. unfold exit_code.
      apply (exit_run_e scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hex M0 LB LK cr A M1 model1 RF Sf 2 tid XP ltac:(lia) F2 F4 F10).
      rewrite VIS1. unfold stdoutPA. repeat split; first [exact (TR _ _ _ P1 eq_refl) | exact (TR _ _ _ P2 eq_refl) | exact (TR _ _ _ P3 eq_refl) | exact (TR _ _ _ P4 eq_refl) | exact (TR _ _ _ P5 eq_refl)].
    - (* [comment removed for export] *)
      cbn [dg_chain] in CH. destruct CH as (fxE & RE & ME & wlo & q & c & b1 & l1 & b2 & l2 & bs1 & bs2 & MS & WV & Ebs & AGE & KONT).
      destruct WV as [(G17 & G10 & G11 & G12 & G9 & G18 & G22 & G19) (W1 & W2 & W3 & W4 & Wc) (I0 & I1) (B1a & B1b & B1c & B1d & B1e & B1r) HC1 HC2 HTOT HFD].
      pose proof (ArtBridge.msteps_mem_grows ASEGS _ _ MS) as MGE. cbn [ms_mem] in MGE.
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fxE R (Z_to_bv 64 pc) RE (Z_to_bv 64 0x120258) ME (dgW S) _ D MS MGE
               (agree0_trans2 MVi _ ME S AGI AGE) (fun a Ha => dgW_cwa LB S a HS Ha)).
      intros M1 model1 D1 SBM1 VIS1 FRM1.
      assert (MGiE : mem_grows MVi ME) by (eapply mem_grows_trans; [exact MGI | exact MGE]).
      pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D1) as (HH1 & HL1 & HA1 & HM1 & Hh1).
      assert (Hq : 0 <= wlo /\ wlo <= wlo + 32 /\ wlo + 32 + 16 <= 2 ^ 47) by lia.
      assert (Hf : 0 <= 1293512 /\ (1293512 + 124 <= wlo \/ wlo + 32 + 16 <= 1293512 + 120) /\ 1293512 + 124 < 2 ^ 63) by lia.
      assert (NLq : forall x, wlo <= x < wlo + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model1) = false).
      { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D1); lia. }
      assert (FD1 : fd_lookup (m_fds model1) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite (sbm_fds' _ _ SBM1); exact FD2).
      rewrite Ebs. cbn [dg_shape fold_right]. fold (dg_shape rest fs). unfold W at 1.
      apply (@wv_loop fxE scfg (ahid A model1) A HH1 (m_vm_lazy model1) HL1 HA1 1293512 2 ltac:(lia) wlo (wlo + 32) Hq Hf NLq (dg_shape rest fs) (dg_shape_nil rest fs)
               (length (bs1 ++ bs2)) true RE M1 model1 q c b1 l1 b2 l2 bs1 bs2).
      + lia.
      + reflexivity.
      + exact HM1.
      + exact Hh1.
      + exact FD1.
      + unfold wv_regs. repeat split; assumption.
      + rewrite VIS1. unfold wv_iov. split; [exact W3|]. split; [exact W4|]. split; [exact Wc|]. split; [exact I0|]. split; [exact I1|].
        split. { replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia). apply (store_ok_mono ASEGS _ MVi ME _ MGiE). apply (WINi q (16 * c)); lia. }
        split. { unfold wv_buf. split; [exact B1a|]. split; [exact B1b|]. split; [exact B1c|]. split; [exact B1d|]. split; [exact B1r|].
                 intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D1); lia. }
        split; [exact HC1|]. intros Hc2. destruct (HC2 Hc2) as (I2 & I3 & T1 & B2a & B2b & B2c & B2d & B2e & B2r).
        split; [exact I2|]. split; [exact I3|]. split; [|exact T1].
        unfold wv_buf. split; [exact B2a|]. split; [exact B2b|]. split; [exact B2c|]. split; [exact B2d|]. split; [exact B2r|].
        intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D1); lia.
      + exact HTOT.
      + rewrite VIS1. exact HFD.
      + (* [comment removed for export] *)
        intros R3 M3 model3 MI3 SBM3 KR3 FRM3 FRV3 GRM3 GRV3.
        assert (D3 : dinvA LB LK cr A M3 model3).
        { apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M1 M3 model1 model3 D1).
          - intros a Ha Hn. apply FRM3; [exact Ha|]. intros X. apply Hn. unfold CWA. right; left. lia.
          - exact GRM3.
          - exact (sbm_vml _ _ SBM3).
          - exact MI3.
          - rewrite (sbm_halted_eq _ _ SBM3). exact Hh1. }
        pose proof (ahid_sbm A model1 model3 SBM3) as AH3. rewrite VIS1 in FRV3, GRV3. rewrite <- AH3 in FRV3, GRV3.
        set (MV3 := mrestrict (ahid A model3) M3) in *.
        apply (IH LB LK cr A MVi S Sf tid fs fxE R3 0x120264 M3 model3 D3).
        * rewrite <- EFS. rewrite <- (proj2 (sbm_fds model model1 SBM1)). exact (proj2 (sbm_fds model1 model3 SBM3)).
        * intros x Hx Hfw. fold MV3. pose proof (u64_range x) as Ux. rewrite <- (Z_to_bv_bv_unsigned 64 x). rewrite FRV3 by lia. rewrite Z_to_bv_bv_unsigned. apply AGE; assumption.
        * fold MV3. eapply mem_grows_trans; [exact MGiE | exact GRV3].
        * exact HS.
        * exact HSf.
        * exact HSf16.
        * exact WINi.
        * exact IMGi.
        * exact XAi.
        * exact SOPi.
        * rewrite (sbm_fds' _ _ SBM3). exact FD1.
        * fold MV3. apply (KONT R3 MV3).
          -- intros x Hx. pose proof (u64_range x) as Ux. rewrite <- (Z_to_bv_bv_unsigned 64 x). rewrite FRV3 by lia. reflexivity.
          -- exact GRV3.
          -- exact (keep_nat RE R3 KR3).
  Qed.
End Chain.
End FPX_1.

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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare MemSplit AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  RefNodes RefMemcpyLib HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b
  Ba0RegionPoisoned_b Ba0AsanMemcpy_b Ba0ReadIcpt_b Ba0DrvHIcpt_b Ba0DrvRead_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition TP_A : Z := 0x673d00.
Definition ERRNO_A : Z := 0x673c5c.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_NOERRNO : list (Z * Z) :=
  [(0x10000, 0x139000); (0x13bbe0, 0x13c580); (0x662290, 0x673c5c); (0x673c60, 0x673ca8); (0x673cb0, 0x673cf8); (0x673d14, 0x673d28); (0x673d30, 0x6951b8);
   (0x6951c0, 0x696000)].
Definition keep_readEA (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 2200 bls vbnd [] IMG_NOERRNO IMG_RW_A kn.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvReadDir.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hcells : incl RD_CELLS (asc_cells C).
  Variable M0 : word -> option byte.

  #[local] Abbreviation dinvA := (dinv ar HI sp0 M0).

  Lemma wseg_errno : wseg_ok ASEGS (Z_to_bv 64 0x673c5c) 4 = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma aread_dir_site : forall vals ebs sr kn R M (model : Model) LB LK cr A (cnt : Z) so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 4 = Z_to_bv 64 TP_A ->
    getr R 10 = Z_to_bv 64 3 -> getr R 11 = Z_to_bv 64 STAGE -> getr R 12 = Z_to_bv 64 cnt -> 1 <= cnt <= 65536 ->
    getr R 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    dinvA LB LK cr A M model ->
    fd_lookup (m_fds model) (Z_to_bv 64 3) = Some FdDir ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    (forall R' M' (model' : Model),
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       vals_ev vals' (length vals + 10) = Z_to_bv 64 18446744073709551615 ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A model') M') (keep_readEA so bls vbnd kn) ->
       dinvA LB LK cr A M' model' ->
       m_fds model' = m_fds model -> m_fs model' = m_fs model ->
       (forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp0 + so - 2200 <= a < bv_unsigned sp0 + so) -> ~ (ERRNO_A <= a < ERRNO_A + 4) ->
                  M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x63390) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A cnt so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal R4 R10 R11 R12 Hcnt R1 Hra Hra2 DI Hfd Hbl Hvb CONT.
    pose proof Hsp as Hsp'. unfold STAGE, TP_A, ERRNO_A in *.
    set (s := bv_unsigned sp0 + so) in *. set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
    pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
    destruct (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ DI) as (HOFF & HLC & HAWF & _ & _). fold H in HOFF, HLC.
    assert (Hs : 0x1000000 <= s - 2200 /\ s < 2 ^ 64) by (unfold s; lia).
    assert (WOK : store_ok ASEGS MV (Z_to_bv 64 (s - 2200)) 2200 = true).
    { replace (s - 2200) with (bv_unsigned sp0 + (so - 2200)) by (unfold s; ring).
      apply (window_store_ok sp0 vals ebs MV kn (so - 2200) 2200 HK Hiw P0); lia. }
    assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x696000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LB a) -> H (Z_to_bv 64 a) = false)
      by (intros a Ha Hc; exact (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH Ha Hc)).
    assert (VFR : forall x : word, s - 2200 <= bv_unsigned x < s -> H x = false).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply VIS; unfold s in Hx; lia. }
    assert (VST : forall x : word, Ba0DrvRead_b.STAGE <= bv_unsigned x < Ba0DrvRead_b.STAGE + 65536 -> H x = false).
    { intros x Hx. unfold Ba0DrvRead_b.STAGE in Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply VIS; lia. }
    assert (CV : forall a n v, In (a, n, v) RD_CELLS ->
                 rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v))).
    { intros a n v Hin. unfold MV, H. rewrite rdn_mrestrict_eq; [exact (rd_cell scfg L ar C IL HI HIok sp0 DL Hcells _ _ _ _ _ _ _ a n v HH Hin)|].
      apply (avoid_img scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ _ a (Z.to_nat n) HH);
        unfold RD_CELLS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]); destruct Hin. }
    (* [comment removed for export] *)
    destruct (wrap_read_pre_run MV (seg_rom ASEGS) (Z_to_bv 64 s) (Z_to_bv 64 ra) s 3 0x662290 cnt
                ltac:(apply u_small; lia) Hs WOK ltac:(lia) ltac:(lia) ltac:(lia)) with (regs := R)
      as (Ra & RUN1 & A17 & A10 & A11 & A12 & _ & _ & _ & _ & A2 & A1 & A8 & A9 & A18 & A19 & A20 & KB1).
    1: { rewrite <- (w_lit 0x140918 (0x140918%bv : word) eq_refl). exact (CV 0x140918 1 1 ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
    1: { rewrite <- (w_lit 0x139318 (0x139318%bv : word) eq_refl). exact (CV 0x139318 8 0x130304 ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
    1: exact R10. 1: exact R11. 1: exact R12. 1: exact R2. 1: exact R1.
    rewrite (w_lit 0x63390 (0x63390%bv : word) eq_refl).
    apply (rz_msteps_lz ASEGS scfg H A R _ M Ra _ _ model K HOFF asegs_wx HLC HAWF HMI Hh RUN1).
    intros model1 MI1 SBM1 EQV1.
    destruct (sbm_fds _ _ SBM1) as (F1 & F2).
    (* [comment removed for export] *)
    eapply (rz_read_dir_cnt_lz ASEGS scfg Ra _ _ model1 ECALLW (Z_to_bv 64 3) cnt K); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - rewrite (sbm_halted_eq _ _ SBM1). exact Hh.
    - exact A17.
    - exact A10.
    - rewrite u_small by lia. lia.
    - rewrite F1. exact Hfd.
    - exact A12.
    - lia.
    - rewrite A11, u_small by lia. unfold TASK_SIZE. lia.
    - replace (v_addi (0x12a8d8%bv : word) 4) with (0x12a8dc%bv : word) by (apply bv_eq; reflexivity).
      set (raw := Z_to_bv 64 ra) in *.
      set (R2' := regupd Ra 10 (errno_ret EISDIR)).
      assert (Hbs : Z.of_nat (length (@nil byte)) <= 65536) by (cbn; lia).
      change (munrestrict H M (RDA MV raw s R)) with (rd_M2 H M s raw R []).
      set (M2 := rd_M2 H M s raw R []).
      set (MV2 := rd_MV2 H M s raw R []).
      assert (EL1 : m_vm_lazy model1 = m_vm_lazy model) by exact (sbm_lazy_eq _ _ SBM1).
      assert (EH1 : ahid A model1 = H) by (unfold H; apply ahid_same_lazy; exact EL1).
      assert (Hh1 : m_halted model1 = None) by (rewrite (sbm_halted_eq _ _ SBM1); exact Hh).
      (* [comment removed for export] *)
      pose proof (RDA_slots (mrestrict H M) raw s Hs R) as (SL1 & SL2 & SL3 & SL4 & SL5 & SL6 & SL7).
      assert (T1 : rdn ASEGS MV2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 raw)) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 8) by lia; exact SL1).
      assert (T2 : rdn ASEGS MV2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 16) by lia; exact SL2).
      assert (T3 : rdn ASEGS MV2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr R 9))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 24) by lia; exact SL3).
      assert (T4 : rdn ASEGS MV2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr R 18))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 32) by lia; exact SL4).
      assert (T5 : rdn ASEGS MV2 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr R 19))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 40) by lia; exact SL5).
      assert (T6 : rdn ASEGS MV2 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr R 20))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 48) by lia; exact SL6).
      assert (T7 : rdn ASEGS MV2 (Z_to_bv 64 (s - 2136)) 8 = Some (word_to_le_bytes 8 (0x655bc%bv : word))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 2136) by lia; exact SL7).
      assert (Hret : ret_ok raw) by (apply ret_ok_even; unfold raw; rewrite u_small by lia; exact Hra2).
      assert (Q4 : getr R2' 4 = Z_to_bv 64 0x673d00).
      { unfold R2'. rewrite getr_other by discriminate. rewrite (KB1 4%bv); [exact R4 | cbv; tauto | cbv; intuition discriminate]. }
      destruct (read_icpt_post_err_run (seg_rom ASEGS) raw s 0x673d00 Hs ltac:(lia) Hret R R2' MV2) as (R3 & RUN3 & O10 & O2 & O1 & O8 & O9 & O18 & O19 & O20 & KB3).
      1: { unfold R2'. rewrite getr_same by discriminate. apply bv_eq. vm_compute. reflexivity. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A2. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A1. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A8. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A20. }
      1: exact Q4.
      1: { apply (store_ok_mono ASEGS _ (mrestrict H M) MV2); [exact (rd_MV2_grows H M s raw R []) | exact WOK]. }
      1: { apply (store_ok_window ASEGS _ (Z_to_bv 64 0x673c5c) (Z_to_bv 64 (0x673d00 - 164)) 4%nat 4%nat 0x673c5c 0x673c60);
             first [exact wseg_errno | reflexivity | lia | (rewrite u_small by lia; lia)]. }
      1: exact T7. 1: exact T1. 1: exact T2. 1: exact T3. 1: exact T4. 1: exact T5. 1: exact T6.
      set (M3' := RDE s 0x673d00 MV2) in *.
      assert (MI1' : MInv A model1) by exact MI1.
      apply (rz_msteps_lz ASEGS scfg H A R2' _ M2 R3 _ M3' model1 K HOFF asegs_wx ltac:(rewrite EL1; exact HLC) HAWF MI1' Hh1 RUN3).
      intros model3 MI3 SBM3 EQV3.
      set (M3 := munrestrict H M2 M3') in *.
      assert (OUT3 : forall x : word, ~ (s - 2200 <= bv_unsigned x < s) -> ~ (0x673c5c <= bv_unsigned x < 0x673c60) -> M3' x = MV2 x).
      { intros x N1 N2. unfold M3'. apply RDE_out; lia. }
      assert (GR3 : mem_grows MV2 M3') by (unfold M3'; apply RDE_grows).
      (* [comment removed for export] *)
      assert (FRM : forall a, 0 <= a < 2 ^ 64 -> ~ (s - 2200 <= a < s) -> ~ (0x673c5c <= a < 0x673c5c + 4) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha N1 N2. unfold M3, munrestrict.
        assert (E2 : M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { unfold M2, rd_M2. cbn [wbytes]. unfold munrestrict. destruct (H (Z_to_bv 64 a)) eqn:Hx; [reflexivity|].
          rewrite (RDA_out (mrestrict H M) raw s Hs R (Z_to_bv 64 a)) by (rewrite u_small by lia; lia). unfold mrestrict. rewrite Hx. reflexivity. }
        destruct (H (Z_to_bv 64 a)) eqn:Hx; [exact E2|].
        rewrite OUT3 by (rewrite u_small by lia; lia). unfold MV2, rd_MV2, mrestrict. rewrite Hx. exact E2. }
      assert (GRW : forall x : word, M x <> None -> M3 x <> None).
      { intros x Hd. unfold M3, munrestrict.
        assert (E2 : M2 x <> None) by (unfold M2; apply (rd_M2_grows H M s raw R []); exact Hd).
        destruct (H x) eqn:Hx; [exact E2|]. apply GR3. unfold MV2, rd_MV2, mrestrict. rewrite Hx. exact E2. }
      assert (EV3 : vml_of model3 = vml_of model) by (rewrite (sbm_vml _ _ SBM3); exact (sbm_vml _ _ SBM1)).
      assert (Hh3 : m_halted model3 = None) by (rewrite (sbm_halted_eq _ _ SBM3); exact Hh1).
      assert (EH3 : ahid A model3 = H) by (rewrite (ahid_sbm A model1 model3 SBM3); exact EH1).
      assert (DI3 : dinvA LB LK cr A M3 model3).
      { apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M M3 model model3 DI); [ | exact GRW | exact EV3 | exact MI3 | exact Hh3].
        intros a Ha NC. apply FRM; [exact Ha | |]; intros Hr; apply NC; unfold CWA.
        - right. left. unfold s in Hr. lia.
        - right. right. exists 0x662290, 0x673ca8. split; [unfold IMG_W_A; cbn [In]; tauto | lia]. }
      assert (HL' : length (vals ++ junk_vals R3) = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R3) 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (KEPT : forall r : reg, In r c_kept -> getr R3 r = getr R r).
      { assert (KK : forall r : reg, In r callee_saved -> ~ In r Ba0ReadIcpt_b.RIPL -> getr R3 r = getr R r).
        { intros r Hr Hn'. rewrite (KB3 r Hr Hn'). unfold R2'. rewrite getr_other; [exact (KB1 r Hr Hn')|].
          intros ->. clear - Hr. cbv in Hr. intuition discriminate. }
        intros r Hr. unfold c_kept in Hr. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
        - rewrite O2, R2. reflexivity.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - exact O8.
        - exact O9.
        - exact O18.
        - exact O19.
        - exact O20.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate. }
      apply (CONT R3 M3 model3 HL').
      + rewrite (vals_ev_junkA vals R3 10) by lia. exact O10.
      + exact (regs_after_keeps vals ebs sr R R3 c_kept Hsv HR KEPT c_kept_no0A).
      + (* [comment removed for export] *) rewrite EH3. unfold keep_readEA.
        pose proof (env_app_know ASEGS vals (junk_vals R3) ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so 2200 bls vbnd [] IMG_NOERRNO IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R3)) ebs)
                  (fun a => H (Z_to_bv 64 a) = false /\ ~ (s - 2200 <= a < s) /\ ~ (0x673c5c <= a < 0x673c5c + 4))
                  (fun a => s - 2200 <= a < s)
                  _ MV (mrestrict H M3) _ _ kn HK1).
        * constructor; cbn [ev]; rewrite ?P0'.
          -- lia.
          -- lia.
          -- intros z Hz Hnot. split; [apply VIS; lia|]. unfold s. split; lia.
          -- intros z Hz. right. unfold s. lia.
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & SBk). rewrite vals_ev_app_l by exact Hi32.
             pose proof (sub_blockA_hz L ar IL sp0 DL _ _ _ SBk) as (Z1 & Z2 & Z3).
             destruct SBk as (cap & Hnb & Hin & HB).
             split; [lia|]. intros z Hz. split; [|unfold s; split; lia].
             apply VIS; [lia|]. right. right. exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin | cbn [fst snd]; lia].
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
          -- intros i [].
          -- intros lo hi Hin. unfold IMG_NOERRNO in Hin. cbn [In] in Hin.
             repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; (split; [apply VIS; lia | unfold s; split; lia])|]).
             destruct Hin.
          -- intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
             intros Mx d m Hd Hm.
             apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x662290) (Z_to_bv 64 d) 65536%nat m 0x662290 0x672290);
               first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
        * intros a Ha (V1 & N1 & N2). unfold MV, mrestrict. rewrite V1. apply FRM; assumption.
        * intros a Ha. unfold mrestrict. rewrite (VFR (Z_to_bv 64 a)) by (rewrite u_small by (unfold s in Ha; lia); exact Ha).
          apply GRW. apply (window_defined sp0 Hsp vals ebs H M kn HK Hiw P0). unfold s in Ha. lia.
      + exact DI3.
      + rewrite (proj1 (sbm_fds _ _ SBM3)). exact F1.
      + rewrite (proj2 (sbm_fds _ _ SBM3)). exact F2.
      + exact FRM.
  Qed.
End DrvReadDir.
End FPX_1.

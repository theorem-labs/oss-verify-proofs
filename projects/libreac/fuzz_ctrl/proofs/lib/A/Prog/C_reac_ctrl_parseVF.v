(* lib/A/Prog/C_reac_ctrl_parseVF.v -- fuzz_ctrl image A (asan, libreac v1.9.0): world facts for the cgif-form glue
   pb_reac_ctrl_parse, at a state the core's AR describes: the side-stack premises of the stretches' Sections
   (reac_ctrl_parseF_rpost.RPostFOn and its twins): the free frames X (XF0 / XB0), the tls premise (TLS0) and the
   free-frame side-stack premise fpx (FP0).
   - rcpVF_Xok: the free-frame list X of the record o (empty when o = 0 or o's frame is not of class 1, else o's
     class-1 frame).
   - rcpVF_XF: every entry of X is a live class-1 frame, flag byte 1, index below fs_M 1.
     Source: A.ProgWorld_Fs.ctl_fs_of_AR (the flag clause, 1 iff mem_pos (frames S) c j), A.ProgWorld_Fs.pw_F_above,
     A.ProgWorld.ctl_fs_geom, YG0s.frame_facts.
   - rcpVF_tls: reac_ctrl_parse_tls for the window [Sp - 8800, Sp) inside the real stack.
     Source: A.ProgWorldTlsApart.fp_tls_apart (cs = [1]).
   - rcpVF_fpx: fpx [1] for the window [Sp - 8800, Sp), the writes reac_ctrl_parse_W o Sp and the data ranges
     reac_ctrl_parse_D f n o.
     Source: A.ProgWorld_Fs.ctl_fp_of_AR (D := []), whose write premise is from A.ProgWorldTlsOwned.fp_tls_owned (each
     thread-cell byte is owned, the window and record bytes are not) and the layout (the side stack ends below
     alloc_ceiling <= Sp - 8800, o lies in a frame above the header); the data premise against fp_wx [1] FS X: f's block
     by A.ProgWorldBlkApart.ctl_block_apart_fs, YG0d.al_blocks (in_app), A.ProgWorldTlsApart.cls_fp_dj / pw_cls /
     fp_w1_cls and RcAsanFP.fp_dj_cover / fp_wx_cover; the record o by YG0s.frame_facts / frame_off_bounds (o's
     frame of class co: co <> 1 lies in another class region, co = 1 lies in the hole cut out of fp_wx1),
     RcAsanFP.cut_ivls_in / In_filter_drop and A.ProgWorldTlsApart.sh_lo / sh_hi (the shadow pieces).
   AR_laws: YG0q.AR_laws_ok (proved, no premise).  CtrlTSyms B: the Section hypothesis TS.
   Route (C): no ctlrt_of_AR / shadow_rw_of_AR / rt_of_core / RT_used_of_AR, no VIS0 / OWNED_RO hypothesis.
   Twin rule: every project module is Required without Import and named through a full-path Module alias.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AsanRT AF0m ProgWorld ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldTlsApart ProgWorldTlsOwned ProgWorldBlkApart.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c RcAsanFP reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YA0n YM05 YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0s YG0q.
Import ListNotations.
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module RL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLay.
Module AI0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.
Module PW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld.
Module PWF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld_Fs.
Module PWTA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldTlsApart.
Module PWTO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldTlsOwned.
Module PWBA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldBlkApart.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP.
Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parse_c.
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RG0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0s.
Module RG0q := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0q.
Local Notation rsegs := AI0.rsegs (only parsing).

(* ---------------------------------------------------------------------------------------------------------
   1. Helpers (closed arithmetic and list facts). *)

(* A live frame named in the list is found by mem_pos. *)
Lemma rcpVF_mem_pos : forall l c p, In (c, p) l -> RG00.mem_pos l c p = true.
Proof.
  induction l as [|[c' p'] l IH]; intros c p H; cbn [In] in H; [destruct H|].
  cbn [RG00.mem_pos]. destruct H as [E|H].
  - injection E as -> ->. rewrite !Z.eqb_refl. reflexivity.
  - rewrite (IH c p H). apply Bool.orb_true_r.
Qed.

(* Two nonempty ranges with no common byte are apart (RcLay.ly_dj). *)
Lemma rcpVF_dj_bytes : forall a b c d, a < b -> c < d ->
  (forall x, a <= x < b -> c <= x < d -> False) -> RL.ly_dj a b c d.
Proof.
  intros a b c d Hab Hcd H. unfold RL.ly_dj.
  destruct (Z_le_gt_dec b c) as [E|E]; [left; exact E|].
  destruct (Z_le_gt_dec d a) as [E'|E']; [right; exact E'|].
  exfalso. destruct (Z_le_gt_dec a c) as [E''|E''].
  - apply (H c); lia.
  - apply (H a); lia.
Qed.

(* Every thread cell of fp_tls is a nonempty range. *)
Lemma rcpVF_tls_ne : forall TP (DT TS C T DB : word) k d,
  In d (FP.fp_tls TP DT TS C T DB k) -> fst d < snd d.
Proof.
  intros TP DT TS C T DB k d Hd. unfold FP.fp_tls in Hd. cbn [In] in Hd.
  repeat (destruct Hd as [<-|Hd]; [cbn [fst snd]; lia|]). destruct Hd.
Qed.

(* The pieces of [lo, hi) with one hole [a, b) cut out: below the hole or above it. *)
Lemma rcpVF_cut1 : forall lo hi a b r, In r (FP.cut_ivls lo hi [(a, b)]) ->
  (fst r = lo /\ snd r <= a) \/ (b <= fst r /\ snd r = hi).
Proof.
  intros lo hi a b r Hr. unfold FP.cut_ivls, FP.nonempty in Hr. apply FP.In_filter_drop in Hr.
  cbn [FP.cut_ivls0 In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd].
  - left. split; [reflexivity | apply Z.le_min_l].
  - right. split; [apply Z.le_max_l | reflexivity].
Qed.

(* The class-1 geometry of the side stack at F (and the header end), in numerals. *)
Lemma rcpVF_geo : forall F j,
  SMC.fs_frame F 1 j = F + 1085440 + j * 128 /\ SMC.fs_frame F 0 0 = F + 36864 /\
  SMC.fs_flag F 1 j = F + 20480 + j /\ SMC.fs_hint F 1 = F + 8 /\ SMC.fs_M 1 = 8192.
Proof.
  intros F j.
  assert (E1 : SMC.fs_frame F 1 j = F + SMC.fs_frame 0 1 0 + j * SMC.fs_B 1) by (unfold SMC.fs_frame; ring).
  assert (E2 : SMC.fs_frame F 0 0 = F + SMC.fs_frame 0 0 0) by (unfold SMC.fs_frame; ring).
  assert (E3 : SMC.fs_flag F 1 j = F + SMC.fs_flag 0 1 0 + j) by (unfold SMC.fs_flag; ring).
  assert (E4 : SMC.fs_hint F 1 = F + SMC.fs_hint 0 1) by (unfold SMC.fs_hint; ring).
  change (SMC.fs_frame 0 1 0) with 1085440 in E1. change (SMC.fs_B 1) with 128 in E1.
  change (SMC.fs_frame 0 0 0) with 36864 in E2.
  change (SMC.fs_flag 0 1 0) with 20480 in E3.
  change (SMC.fs_hint 0 1) with 8 in E4.
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
  reflexivity.
Qed.

(* The core's class-1 frame address, in numerals. *)
Lemma rcpVF_fa1 : forall ly po, RG0f.frame_addr ly 1 po = RG0f.ly_F ly + 1085440 + po * 128.
Proof.
  intros ly po.
  assert (E : RG0f.fs_frame_off 1 po = RG0f.fs_frame_off 1 0 + po * RG00.fs_frame_bytes 1)
    by (unfold RG0f.fs_frame_off; ring).
  change (RG0f.fs_frame_off 1 0) with 1085440 in E. change (RG00.fs_frame_bytes 1) with 128 in E.
  unfold RG0f.frame_addr. rewrite E. ring.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The free frames X, the tls premise and the side-stack premise fpx. *)
Section VF.
Context {fx : RK11.FPState} {rc : RM05.RunCeil}.
Variable B : RG0f.asyms.
Hypothesis TS : AF.CtrlTSyms B.
(* AR_laws of the bundle: the core's own proof (lib/Reusable/YG0q.v AR_laws_ok), no premise. *)
Local Notation LAWS := (RG0q.AR_laws_ok rsegs B).

Definition rcpVF_Xok (ly : RG0f.alayout) (S : RG00.astate) (o : Z) (X : list (nat * Z)) : Prop :=
  (o = 0 /\ X = []) \/
  (o <> 0 /\ exists co po, In (co, po) (RG01.frames S) /\ RG0f.frame_addr ly co po <= o /\
     o + 36 <= RG0f.frame_addr ly co po + RG00.fs_frame_bytes co /\
     X = (if co =? 1 then [(1%nat, po)] else [])).

Lemma rcpVF_XF : forall ly S (W : RA0n.world rsegs) m md o X,
  RG0n.AR rsegs B ly S W m md -> rcpVF_Xok ly S o X ->
  Forall (fun ci => fst ci = 1%nat /\
            LM.bytes_at rsegs m (SMC.fs_flag (RG0f.ly_F ly) (fst ci) (snd ci)) [Z_to_bv 8 1]) X /\
  Forall (fun ci => 0 <= snd ci < SMC.fs_M 1) X.
Proof.
  intros ly S W m md o X HAR HX.
  destruct HX as [(_ & ->)|(_ & co & po & Hin & _ & _ & ->)]; [split; apply Forall_nil|].
  destruct (Z.eqb_spec co 1) as [->|_]; [|split; apply Forall_nil].
  pose proof HAR as (M & _).
  destruct (RG0s.frame_facts B ly S _ 1 po M Hin) as (_ & Hpo & _).
  assert (EM : SMC.fs_M 1 = RG00.fs_frames 1) by reflexivity.
  pose proof (PWF.pw_F_above B ly S W m md HAR) as HGT.
  pose proof (PWF.ctl_fs_of_AR B PW.ctl_fs_geom LAWS ly S W m md HAR HGT) as HF. cbv zeta in HF.
  destruct HF as (_ & Hfl & _).
  pose proof (Hfl 1%nat po ltac:(lia) ltac:(rewrite EM; exact Hpo)) as Hb.
  change (Z.of_nat 1) with 1 in Hb. rewrite (rcpVF_mem_pos _ _ _ Hin) in Hb.
  split; apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - split; [reflexivity | exact Hb].
  - rewrite EM. exact Hpo.
Qed.

Lemma rcpVF_tls : forall ly S (W : RA0n.world rsegs) m md Sp,
  RG0n.AR rsegs B ly S W m md ->
  RG0f.ly_stk_lo ly <= Sp - 8800 -> Sp <= RG0f.ly_stk_hi ly ->
  PC.reac_ctrl_parse_tls m ART.RT_TP (RG0f.ly_F ly) (Sp - 8800) Sp.
Proof.
  intros ly S W m md Sp HAR Hlo Hhi DT TS0 C T DB k Hc.
  exact (PWTA.fp_tls_apart B TS LAWS ly S W m md [1%nat] (Sp - 8800) Sp HAR
           ltac:(apply Forall_cons; [lia | apply Forall_nil]) Hlo Hhi DT TS0 C T DB k Hc).
Qed.

Lemma rcpVF_fpx : forall ly S (W : RA0n.world rsegs) m md f n o Sp X,
  RG0n.AR rsegs B ly S W m md ->
  RM05.alloc_ceiling <= Sp - 8800 -> ART.HIGHMEM_BEG <= Sp - 8800 -> Sp <= ART.APPMEM_END ->
  (forall a, Sp - 8800 <= a < Sp -> ~ RG0n.aowned B ly S a) ->
  (o <> 0 -> forall a, o <= a < o + 36 -> ~ RG0n.aowned B ly S a) ->
  (50 <= n -> exists Lf, In (f, Lf) (RG0d.ablocks B ly S) /\ 50 <= RG00.req_size Lf) ->
  rcpVF_Xok ly S o X ->
  FP.fpx [1%nat] m ART.RT_TP (RG0f.ly_F ly) (Sp - 8800) Sp (PC.reac_ctrl_parse_W o Sp) (PC.reac_ctrl_parse_D f n o) X.
Proof.
  intros ly S W m md f n o Sp X HAR Hce Hhm Hae Hwin Hrec Hf HX.
  pose proof HAR as (M & _).
  pose proof (RG0n.am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (RG0f.lo_app _ LO) _ (PWF.pw_F_in_owned ly)) as F1. cbn [fst snd] in F1.
  pose proof (@RG0f.ASAN_CEIL_range rc) as [CR _]. unfold RG0f.ASAN_CEIL in CR.
  (* the side stack: in application memory, ending at or below alloc_ceiling <= Sp - 8800 *)
  assert (HFS : 4096 <= RG0f.ly_F ly /\ RG0f.ly_F ly + 11571200 <= RM05.alloc_ceiling /\
                (RG0f.ly_F ly + 11571200 <= 0x7fff7000 \/ 0x10007fff8000 <= RG0f.ly_F ly)).
  { destruct F1 as [F0 F2].
    unfold RG0f.kFakeStackSize, RG0f.kLowShadowBeg, RG0f.kHighMemBeg, RG0f.ASAN_CEIL in F2. lia. }
  (* the record o: in a frame (co, po) of S, above the header, inside the class-co frame region *)
  assert (HOG : o <> 0 -> exists co po, 0 <= co <= 10 /\
      RG0f.ly_F ly + 36864 + co * 1048576 <= o /\ o + 36 <= RG0f.ly_F ly + 36864 + (co + 1) * 1048576 /\
      o + 36 <= RG0f.ly_F ly + 11571200 /\
      X = (if co =? 1 then [(1%nat, po)] else []) /\
      (co = 1 -> RG0f.ly_F ly + 1085440 + po * 128 <= o /\ o + 36 <= RG0f.ly_F ly + 1085440 + po * 128 + 128)).
  { intros Ho. destruct HX as [(Ho' & _)|(_ & co & po & Hin & Hlo & Hhi & EX)]; [contradiction|].
    destruct (RG0s.frame_facts B ly S _ co po M Hin) as (Hc & Hp & _).
    destruct (RG0s.frame_off_bounds co po Hc Hp) as (B1 & B2 & _ & _ & _ & B6).
    change (2 ^ 20) with 1048576 in B1, B2, B6.
    unfold RG0f.kFakeFramesOff, RG0f.kFakeStackSize in B1, B2, B6.
    exists co, po. split; [exact Hc|].
    split; [unfold RG0f.frame_addr in Hlo; lia|].
    split; [unfold RG0f.frame_addr in Hhi; lia|].
    split; [unfold RG0f.frame_addr in Hhi; lia|].
    split; [exact EX|].
    intros ->. rewrite rcpVF_fa1 in Hlo, Hhi. change (RG00.fs_frame_bytes 1) with 128 in Hhi. lia. }
  (* fp with the data ranges D := [] from AR *)
  assert (FP0 : FP.fp [1%nat] m ART.RT_TP (RG0f.ly_F ly) (Sp - 8800) Sp (PC.reac_ctrl_parse_W o Sp) []).
  { apply (PWF.ctl_fp_of_AR B TS LAWS ly S W m md [1%nat] (Sp - 8800) Sp _ [] HAR).
    - apply Forall_cons; [lia | apply Forall_nil].
    - unfold SMC.FS_SIZE. lia.
    - intros a Ha. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in *. right. lia.
    - (* the writes are apart from the thread cells (owned bytes) and from the header (below the frames) *)
      unfold FP.fp_dj. apply Forall_forall. intros w Hw. apply Forall_forall. intros d Hd.
      assert (Hw' : fst w < snd w /\ (forall a, fst w <= a < snd w -> ~ RG0n.aowned B ly S a) /\
                    RG0f.ly_F ly + 36864 <= fst w).
      { revert Hw. unfold PC.reac_ctrl_parse_W, PC.REAC_CTRL_PARSE_K.
        destruct (Z.eqb_spec o 0) as [Ho|Ho]; intros Hw; cbn [In] in Hw.
        - destruct Hw as [<-|[]]. cbn [fst snd]. split; [lia|]. split; [exact Hwin | lia].
        - destruct Hw as [<-|[<-|[]]]; cbn [fst snd].
          + split; [lia|]. split; [exact Hwin | lia].
          + destruct (HOG Ho) as (co & po & Hc & O1 & _).
            split; [lia|]. split; [exact (Hrec Ho) | lia]. }
      destruct Hw' as (Hw1 & Hw2 & Hw3).
      apply in_app_or in Hd as [Hd|Hd].
      + apply rcpVF_dj_bytes; [exact Hw1 | exact (rcpVF_tls_ne _ _ _ _ _ _ _ _ Hd) |].
        intros x Hx Hxd. apply (Hw2 x Hx).
        apply (PWTO.fp_tls_owned B TS LAWS ly S W m md x HAR).
        apply Exists_exists. exists d. split; [exact Hd | exact Hxd].
      + destruct Hd as [<-|[]]. unfold RL.ly_dj. cbn [fst snd]. right.
        rewrite (proj1 (proj2 (rcpVF_geo (RG0f.ly_F ly) 0))). lia.
    - unfold FP.fp_dj. apply Forall_nil. }
  (* f's 50 bytes are apart from fp_w [1] FS, hence from fp_wx [1] FS X *)
  assert (DF : FP.fp_dj (if n <? 50 then [] else [(f, f + 50)]) (FP.fp_wx [1%nat] (RG0f.ly_F ly) X)).
  { destruct (Z.ltb_spec n 50) as [Hn|Hn]; [unfold FP.fp_dj; apply Forall_nil|].
    destruct (Hf Hn) as (Lf & HinF & HLf).
    pose proof (PWBA.ctl_block_apart_fs B LAWS ly S W m md f Lf HAR HinF) as Hap.
    destruct (RG0d.al_blocks _ _ LAWS ly S W m md f Lf HAR HinF) as (_ & _ & _ & Hia & _).
    apply (FP.fp_dj_cover _ _ (FP.fp_w [1%nat] (RG0f.ly_F ly)));
      [intros r Hr; exact (FP.fp_wx_cover _ _ _ r Hr)|].
    apply (PWTA.cls_fp_dj (RG0f.ly_F ly)).
    - apply Forall_cons; [|apply Forall_nil]. unfold PWTA.pw_cls. cbn [fst snd].
      unfold RG0f.in_app, RG0f.kLowShadowBeg, RG0f.kHighMemBeg in Hia. lia.
    - apply Forall_forall. intros d Hd. unfold FP.fp_w in Hd. apply in_flat_map in Hd as (c & Hc & Hd).
      destruct Hc as [<-|[]].
      apply (PWTA.fp_w1_cls _ 1 d); [lia | lia | unfold RG0f.kFakeStackSize; lia | exact Hd]. }
  (* the record o is apart from fp_wx [1] FS X *)
  assert (DO : FP.fp_dj (if o =? 0 then [] else [(o, o + 36)]) (FP.fp_wx [1%nat] (RG0f.ly_F ly) X)).
  { destruct (Z.eqb_spec o 0) as [Ho|Ho]; [unfold FP.fp_dj; apply Forall_nil|].
    destruct (HOG Ho) as (co & po & Hc & O1 & O2 & O3 & EX & O4).
    destruct (rcpVF_geo (RG0f.ly_F ly) 0) as (G0 & _ & G1 & G2 & GM).
    destruct (rcpVF_geo (RG0f.ly_F ly) (SMC.fs_M 1)) as (GE & _).
    pose proof (PWTA.sh_lo (SMC.fs_frame (RG0f.ly_F ly) 1 0) ltac:(lia)) as SL.
    pose proof (PWTA.sh_hi (SMC.fs_frame (RG0f.ly_F ly) 1 (SMC.fs_M 1)) ltac:(lia)) as SH.
    unfold FP.fp_dj. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    subst X. destruct (Z.eqb_spec co 1) as [Eco|Hco]; apply Forall_forall; intros d Hd.
    - (* class 1: X = [(1, po)], o lies in the hole of fp_wx1 *)
      destruct (O4 Eco) as [O5 O6].
      unfold FP.fp_wx, FP.fp_wx1 in Hd. cbn [flat_map filter map fst snd Nat.eqb] in Hd.
      rewrite app_nil_r, !in_app_iff in Hd.
      destruct Hd as [Hd|[Hd|Hd]].
      + cbn [In] in Hd. destruct Hd as [<-|[<-|[]]]; unfold RL.ly_dj; cbn [fst snd]; right; lia.
      + apply rcpVF_cut1 in Hd. cbn [fst snd] in Hd.
        destruct (rcpVF_geo (RG0f.ly_F ly) po) as (Gp & _).
        destruct (rcpVF_geo (RG0f.ly_F ly) (po + 1)) as (Gp1 & _).
        cbv beta. unfold RL.ly_dj. lia.
      + apply FP.cut_ivls_in in Hd. cbv beta. unfold RL.ly_dj. lia.
    - (* another class: X = [], o's frame lies outside the class-1 frame region *)
      unfold FP.fp_wx, FP.fp_w, FP.fp_w1 in Hd. cbn [flat_map app In] in Hd.
      cbv beta. unfold RL.ly_dj.
      destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; lia. }
  destruct FP0 as (DT & TS0 & C & T & DB & k & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _).
  exists DT, TS0, C, T, DB, k.
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 _))))))))).
  unfold PC.reac_ctrl_parse_D, FP.fp_dj. apply Forall_app. split; [exact DF | exact DO].
Qed.

End VF.

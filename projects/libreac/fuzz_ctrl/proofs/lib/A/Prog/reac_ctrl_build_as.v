From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth RcLay
  RcLayLib RcFin RcEmit RcEmitLib RcAsan RcAsanLib RcLeafLib reac_ctrl_build_as_c reac_ctrl_build_as.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  ctrl_emit_as_c reac_box_model_upstream_width_c reac_ctrl_build_as_c reac_box_model_block_c.
Local Ltac lia ::= em_lia.
Import ListNotations.
Open Scope Z_scope.

(* The models and their facts (ba_facts, ba_E_eq, ba_len_eq, ba_res, ba_go_false, ba_go_true, ba_cases, ba_fr_len)
   are the plain build's (lib/Prog/reac_ctrl_build_as.v); the addresses are this build's. *)

Ltac afixret :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

Lemma aba_row_at : forall segs m b, bytes_at segs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) ba_tbl -> 0 <= b <= 6 ->
  bytes_at segs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b) (ba_fr (ba_row b)).
Proof.
  intros segs m b H Hb.
  apply (ba_sub segs m _ _ (Z.to_nat (24 * (ba_row b - 3))) _ _ H).
  all: destruct (ba_cases b Hb) as [->|[->|[->|[->|[->|[->| -> ]]]]]].
  all: first [ apply Nat.leb_le; vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.

Lemma aaddr_sub : forall m p n p' n', addressable m p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Section Build.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (o md b d s ns FS : Z) (mb nb db sb junk : list byte).

  Local Abbreviation SP0 := (bv_unsigned sp).
  Local Abbreviation LO := (bv_unsigned sp - 4640).
  Local Abbreviation NN := (bm_uw md (firstn 8 (skipn 16 mb))).
  Local Abbreviation LEN := (52 + 36 * bm_uw md (firstn 8 (skipn 16 mb))).
  Local Abbreviation GO := (ba_go o md b).
  Local Abbreviation EE := (ba_E (bm_uw md (firstn 8 (skipn 16 mb))) mb b).
  Local Abbreviation NM := ((b = 5 \/ b = 6) /\ has mb <> 0 /\ rname mb <> 0).
  Local Abbreviation RR := (if ba_go o md b && ba_E (bm_uw md (firstn 8 (skipn 16 mb))) mb b
                            then 52 + 36 * bm_uw md (firstn 8 (skipn 16 mb)) else 0).
  Local Abbreviation WW := [(bv_unsigned sp - 4640, bv_unsigned sp);
                            (o, o + (if ba_go o md b && ba_E (bm_uw md (firstn 8 (skipn 16 mb))) mb b
                                     then 52 + 36 * bm_uw md (firstn 8 (skipn 16 mb)) else 0))].
  Local Abbreviation DD := [(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 240); (md, md + 296); (d, d + 6); (s, s + 6);
                            (o, o + (if ba_go o md b && ba_E (bm_uw md (firstn 8 (skipn 16 mb))) mb b
                                     then 52 + 36 * bm_uw md (firstn 8 (skipn 16 mb)) else 0))].

  Hypothesis HEA : ctrl_emit_as_contract.
  Hypothesis HUW : reac_box_model_upstream_width_contract.
  Hypothesis Ho : 0 <= o < 2^64.
  Hypothesis Hmd : 0 <= md < 2^64.
  Hypothesis Hb : 0 <= b < 2^64.
  Hypothesis Hns : -2^31 <= ns <= 0.
  Hypothesis HS16 : SP0 mod 16 = 0.
  Hypothesis HST : em_stk rsegs m LO SP0.
  Hypothesis HT : em_at rsegs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) ba_tbl.
  Hypothesis DsT : ly_dj LO SP0 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 240).
  Hypothesis Hdb : length db = 6%nat.
  Hypothesis HD : em_at rsegs m d db.
  Hypothesis Dsd : ly_dj LO SP0 d (d + 6).
  Hypothesis Hsb : length sb = 6%nat.
  Hypothesis HSb : em_at rsegs m s sb.
  Hypothesis Dss : ly_dj LO SP0 s (s + 6).
  Hypothesis HM : md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ em_at rsegs m md mb /\
                             ly_dj LO SP0 md (md + 296).
  Hypothesis HN : md <> 0 -> NM -> name_ok nb /\ em_at rsegs m (rname mb) nb /\
                                   ly_dj LO SP0 (rname mb) (rname mb + Z.of_nat (length nb)).
  Hypothesis Ho1492 : o <> 0 -> o + 1492 <= 2^64.
  Hypothesis HEo : GO && EE = true ->
       rw_cells rsegs m o [CB (Z.to_nat LEN) junk] /\ ly_dj LO SP0 o (o + LEN) /\
       ly_dj o (o + LEN) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 240) /\ ly_dj o (o + LEN) md (md + 296) /\
       (NM -> ly_dj o (o + LEN) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + LEN) d (d + 6) /\ ly_dj o (o + LEN) s (s + 6).
  Hypothesis MI0 : em_mi rsegs m.
  Hypothesis HAC : asan_cells m.
  Hypothesis HSW : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= LO.
  Hypothesis HAE : SP0 <= APPMEM_END.
  Hypothesis AWIN : addressable m LO 4640.
  Hypothesis ASW : addressable m BA_SW 56.
  Hypothesis ATB : addressable m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) 168.
  Hypothesis AD : addressable m d 6.
  Hypothesis AS : addressable m s 6.
  Hypothesis APD : app_mem (d + 6) /\ app_mem (d + 7).
  Hypothesis APS : app_mem (s + 6) /\ app_mem (s + 7).
  Hypothesis AM : md <> 0 -> addressable m md 296.
  Hypothesis AN : md <> 0 -> NM -> addressable m (rname mb) (Z.of_nat (length nb)).
  Hypothesis AO : GO && EE = true -> addressable m o LEN /\ app_mem (o + LEN) /\ (o + LEN <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ14 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ13 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis FP : fp [0%nat; 1%nat] m (bv_unsigned tp) FS LO SP0 WW DD.
  Hypothesis FPN : md <> 0 -> NM -> fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS).
  Hypothesis FPT : reac_ctrl_build_as_tls m (bv_unsigned tp) FS LO SP0.

  Definition aRESb (m' : word -> option byte) : Prop :=
    bytes_at rsegs m' o
      (em_fr db sb (bv_unsigned a5 mod 65536) (Z_to_bv 8 205) (Z_to_bv 8 234) (ba_X md mb nb b) LEN)
    /\ em_wok NN = true
    /\ (b <= 1 -> blocksum (ba_X md mb nb b) = 0)
    /\ (blocksum (ly_Z md mb nb b) = 0 -> ba_X md mb nb b = ly_Z md mb nb b).

  Definition aQb : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 RR)
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch (WW ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr LO, shadow_addr SP0)]) m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' LO SP0
      /\ asan_cells m' /\ shadow_rw m' /\ addressable m' LO 4640
      /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS LO SP0 WW DD
      /\ (GO = false -> munch [(SP0 - 80, SP0)] m m')
      /\ (GO && EE = true -> aRESb m').

  Lemma arng_sp : 4640 <= SP0 < 2^64.
  Proof. pose proof (zr_word sp) as R. unfold inr64 in R. destruct HST as (H1 & _). lia. Qed.

  Lemma aframe_sub : forall X, sub_fp [(SP0 + -80, SP0)] ((LO, SP0) :: X).
  Proof. intros X x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. Qed.

  Lemma ain_sub : forall lo', LO <= lo' -> sub_fp [(lo', SP0)] [(LO, SP0)].
  Proof. intros lo' H x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. Qed.

  (* The asan facts in a memory that differs from m only inside [LO, SP0). *)
  Lemma atr : forall W' mc, munch W' m mc -> wmono rsegs m mc -> sub_fp W' [(LO, SP0)] ->
    asan_cells mc /\ shadow_rw mc /\ fp [0%nat; 1%nat] mc (bv_unsigned tp) FS LO SP0 WW DD /\
    (forall p n, addressable m p n -> addressable mc p n).
  Proof.
    intros W' mc MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' LO SP0 x Hs HHM Hx)).
    split; [|split; [|split]].
    - apply (fl_asan_cells W' m mc HAC MU). intros x Hx. apply (fl_out_lo W' LO SP0 x Hs). left.
      unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - exact (fl_shadow_rw W' m mc HSW MU WM SHo).
    - exact (fl_fp _ m mc (bv_unsigned tp) FS LO SP0 _ DD W' FP MU WM Hs).
    - intros p n H. exact (fl_addressable W' m mc p n H MU SHo).
  Qed.

  (* 0x849a4: a refusal returns 0. *)
  Lemma afail : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                       u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte),
    GO = false ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evt rsegs aQb
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x849a4) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 mc j
      HG FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    destruct (atr _ mc MU WM (ain_sub (SP0 + -80) ltac:(lia))) as (AC1 & SW1 & FP1 & ADT1).
    do 12 step.
    apply evt_done. unfold aQb.
    assert (R0 : RR = 0) by (rewrite HG; reflexivity). rewrite R0 in FP1 |- *.
    do 14 eexists. exists mc.
    split; [reflexivity|].
    split; [exact (munch_weaken _ _ m mc (aframe_sub _) MU)|].
    split; [exact WM|]. split; [exact MI|].
    split; [release_frame FR ST (bv_unsigned sp); exact ST|].
    split; [exact AC1|]. split; [exact SW1|]. split; [exact (ADT1 _ _ AWIN)|]. split; [exact FP1|].
    split.
    - intros _. apply (munch_weaken [(SP0 + -80, SP0)]); [|exact MU].
      intros x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I].
    - rewrite HG. intros H. cbn [andb] in H. discriminate H.
  Qed.

  (* 0x84948: the width, the frame pops, and the tail jump to ctrl_emit_as. *)
  Lemma atail : forall (u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 : word) (mc : word -> option byte)
                       (j : list byte) (f : Z),
    GO = true -> f = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evt rsegs aQb
      (MS (mkR ra (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 (Z_to_bv 64 ns) a6 x10 x11 x12 x13 x14 a5 a6
               (Z_to_bv 64 ns) a5 (Z_to_bv 64 s) (Z_to_bv 64 d) (Z_to_bv 64 md) (Z_to_bv 64 o) (Z_to_bv 64 f)
               s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x84948) fc None mc (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 mc j f HG -> FR ST MU WM MI.
    pose proof arng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof HG as HG'. apply andb_true_iff in HG' as [HG1 Hb6]. apply andb_true_iff in HG1 as [Ho0 Hm0].
    apply negb_true_iff, Z.eqb_neq in Ho0. apply negb_true_iff, Z.eqb_neq in Hm0. apply Z.leb_le in Hb6.
    assert (Hb6' : 0 <= b <= 6) by lia.
    destruct (ba_facts b Hb6') as (FK & KR & FBB & FC & FL & FG & FA & F18 & F19 & FAO & FAL).
    destruct (HM Hm0) as (M8 & M296 & ML & HMm & DM).
    pose proof DM as DMu. unfold ly_dj in DMu.
    pose proof (em_obj0 rsegs m mc (SP0 + -80) SP0 md mb 296 MU HMm ltac:(rewrite ML; reflexivity)
                  ltac:(lia)) as HMc.
    pose proof (bm_uw_range md (firstn 8 (skipn 16 mb))) as RN.
    destruct (atr _ mc MU WM (ain_sub (SP0 + -80) ltac:(lia))) as (AC1 & SW1 & _ & ADT1).
    (* reac_box_model_upstream_width(m) *)
    step. step.
    eapply evt_cut.
    { eapply HUW with (mp := md) (lo := LO) (bs := firstn 8 (skipn 16 mb)).
      - rewrite unsigned_lit by lia. reflexivity.
      - intros _. split; [lia|]. split.
        + rewrite length_firstn, length_skipn, ML. reflexivity.
        + pose proof (ly_bytes_sub rsegs mc md mb 16 8 HMc ltac:(rewrite ML; lia)) as H16.
          change (Z.of_nat 16) with 16 in H16. exact H16.
      - rewrite unsigned_lit by lia. exact ST.
      - rewrite unsigned_lit by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME. lia.
      - intros _. rewrite unsigned_lit by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME. lia.
      - exact AC1.
      - exact SW1.
      - intros _. apply (aaddr_sub mc md 296); [exact (ADT1 _ _ (AM Hm0)) | lia | lia | lia].
      - intros x Hx. rewrite unsigned_lit by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME.
        cbn [outside]. split; [|exact I].
        unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    intros ms' (y1 & y2 & y3 & y4 & mu & -> & MUu & WMu & MIu & STu). afixret.
    rewrite unsigned_lit in MUu, STu by lia. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME in MUu.
    pose proof (MIu MI) as MI2.
    pose proof (rw_cells_transport rsegs [(SP0 + -80 - 16, SP0 + -80)] mc mu (SP0 + -80) _ FR MUu WMu
                  ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR2.
    (* the arguments, the restores and the jump *)
    do 21 step.
    release_frame FR2 STu (bv_unsigned sp).
    (* the memory at the jump differs from m only inside [LO, SP0) *)
    assert (MUt : munch [(LO, SP0)] m mu).
    { apply (munch_trans _ m mc mu).
      - apply (munch_weaken _ _ m mc (ain_sub (SP0 + -80) ltac:(lia)) MU).
      - apply (munch_weaken _ _ mc mu (ain_sub (SP0 + -80 - 16) ltac:(lia))). eapply munch_weaken; [|exact MUu].
        intros x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. }
    pose proof (wmono_trans rsegs m mc mu WM WMu) as WMt.
    destruct (atr _ mu MUt WMt (fun x Hx => Hx)) as (AC2 & SW2 & FP2 & ADT2).
    (* the facts ctrl_emit_as needs, in the memory at the jump *)
    pose proof DsT as DsTu. unfold ly_dj in DsTu.
    pose proof (aba_row_at rsegs mu b
                  (em_obj0 rsegs m mu LO SP0 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) ba_tbl 168 MUt HT ltac:(vm_compute; reflexivity)
                     ltac:(lia)) Hb6')
      as HRc.
    pose proof Dsd as Dsdu. unfold ly_dj in Dsdu. pose proof Dss as Dssu. unfold ly_dj in Dssu.
    pose proof (em_obj0 rsegs m mu LO SP0 d db 6 MUt HD ltac:(rewrite Hdb; reflexivity) ltac:(lia)) as HDc.
    pose proof (em_obj0 rsegs m mu LO SP0 s sb 6 MUt HSb ltac:(rewrite Hsb; reflexivity) ltac:(lia)) as HSc.
    pose proof (em_obj0 rsegs m mu LO SP0 md mb 296 MUt HMm ltac:(rewrite ML; reflexivity) ltac:(lia)) as HMu.
    assert (NMc : forall X : Prop, (NM -> X) ->
              (3 <= ly_k (ba_fr (ba_row b)) <= 9 /\
               (ly_bb (ly_k (ba_fr (ba_row b))) = 5 \/ ly_bb (ly_k (ba_fr (ba_row b))) = 6)) /\
              has mb <> 0 /\ rname mb <> 0 -> X).
    { intros X HX ((_ & B56) & H1 & H2). apply HX. rewrite FK, FBB in B56. split; [exact B56 | split; assumption]. }
    (* the data ranges apart from the class-1 side-stack bytes *)
    pose proof (fl_fp_dj _ _ _ _ _ _ _ _ FP) as DJ.
    apply fl_dj_cons in DJ as (DJT & DJ). apply fl_dj_cons in DJ as (DJM & DJ).
    apply fl_dj_cons in DJ as (DJd & DJ). apply fl_dj_cons in DJ as (DJs & DJo).
    pose proof KR as Rrow.
    assert (DJf : fp_dj [(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b + 24)] (fp_w [0%nat; 1%nat] FS))
      by (apply (fl_dj_sub _ _ _ _ _ DJT); lia).
    assert (AF : addressable mu (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b) 24)
      by (apply (aaddr_sub mu (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 72) 168); [exact (ADT2 _ _ ATB) | lia | lia | lia]).
    pose proof HEA as HE. unfold ctrl_emit_as_contract, CTRL_EMIT_AS_K in HE. cbv zeta in HE.
    eapply evt_cut.
    { eapply HE with (o := o) (f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b) (md := md) (d := d) (s := s) (g := 0) (n := NN)
        (ns := ns) (FS := FS) (row := ba_fr (ba_row b)) (tb := []) (mb := mb) (nb := nb) (gb := []) (db := db)
        (sb := sb) (junk := junk).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - exact HS16.
      - exact STu.
      - apply (em_dj_sub _ _ _ _ _ _ _ _ DsT); lia.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - exact DM.
      - apply NMc. intros NMx. destruct (HN Hm0 NMx) as (_ & _ & DN). exact DN.
      - exact Dsd.
      - exact Dss.
      - intros G0. exfalso. exact (G0 eq_refl).
      - unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR. lia.
      - unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR. lia.
      - unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.BA_FR. lia.
      - apply ba_fr_len.
      - exact HRc.
      - rewrite FK. lia.
      - rewrite FC. destruct (b <=? 1); lia.
      - lia.
      - lia.
      - lia.
      - rewrite FAO, FAL. lia.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - rewrite FC. destruct (b <=? 1); intros C2; exfalso; lia.
      - intros L2. lia.
      - exact Hm0.
      - exact M8.
      - exact M296.
      - exact ML.
      - exact HMu.
      - apply NMc. intros NMx. destruct (HN Hm0 NMx) as (NO & NB & DN). split; [exact NO|].
        pose proof DN as DNu. unfold ly_dj in DNu.
        exact (em_obj0 rsegs m mu LO SP0 _ nb _ MUt NB eq_refl ltac:(lia)).
      - lia.
      - exact (Ho1492 Ho0).
      - rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6'). intros E1.
        assert (GE : GO && EE = true) by (rewrite HG; exact E1).
        destruct (HEo GE) as (HO & Dso & DoT & Dom & Don & Dod & Dos).
        pose proof Dso as Dsou. unfold ly_dj in Dsou.
        split.
        { apply (rw_cells_transport rsegs [(LO, SP0)] m mu o _ HO MUt WMt).
          cbn [disjoint_from cells_size csize]. lia. }
        split; [exact Dso|]. split; [apply (em_dj_sub _ _ _ _ _ _ _ _ DoT); lia|].
        split; [intros K2; exfalso; rewrite FK in K2; lia|].
        split; [exact Dom|]. split; [apply NMc; exact Don|].
        split; [exact Dod|]. split; [exact Dos|].
        intros G0. exfalso. exact (G0 eq_refl).
      - exact Hdb.
      - exact HDc.
      - exact Hsb.
      - exact HSc.
      - intros G0. exfalso. exact (G0 eq_refl).
      - intros _. lia.
      - exact MI2.
      - exact AC2.
      - exact SW2.
      - exact HHM.
      - exact HAE.
      - exact (ADT2 _ _ AWIN).
      - exact AF.
      - exact (ADT2 _ _ (AM Hm0)).
      - exact (ADT2 _ _ AD).
      - exact (ADT2 _ _ AS).
      - exact APD.
      - exact APS.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - apply NMc. intros NMx. exact (ADT2 _ _ (AN Hm0 NMx)).
      - intros G0. exfalso. exact (G0 eq_refl).
      - intros G0. exfalso. exact (G0 eq_refl).
      - rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6'). intros E1.
        assert (GE : GO && EE = true) by (rewrite HG; exact E1).
        destruct (AO GE) as (AOo & AOe & AOr). split; [exact (ADT2 _ _ AOo)|]. split; assumption.
      - intros K5. rewrite FK in K5. apply ADT2, AJ14. rewrite <- FBB, K5. reflexivity.
      - intros K6. rewrite FK in K6. apply ADT2, AJ13. rewrite <- FBB, K6. reflexivity.
      - rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6').
        rewrite HG in FP2, DJo. cbn [andb] in FP2, DJo.
        apply (fl_fp_D _ _ _ _ _ _ _ _ _ FP2).
        apply fl_dj_cons. split; [exact DJf|]. apply fl_dj_cons. split; [exact DJM|].
        apply fl_dj_cons. split; [exact DJd|]. apply fl_dj_cons. split; [exact DJs|]. exact DJo.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - apply NMc. intros NMx. exact (FPN Hm0 NMx).
      - intros G0. exfalso. exact (G0 eq_refl).
      - unfold ctrl_emit_as_tls. exact (fl_tls _ m mu _ FS _ _ _ _ _ _ FP MUt (fun x Hx => Hx) FPT). }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                MU' & WM' & MI' & ST' & AC' & SW' & AW' & FP' & RES').
    apply evt_done. unfold aQb.
    rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6') in MU', FP'. rewrite (ba_E_eq b NN mb Hb6') in RES'.
    rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6').
    rewrite HG. cbn [andb].
    rewrite HG in DJo. cbn [andb] in DJo.
    do 14 eexists. exists m'.
    split; [reflexivity|].
    split.
    { apply (munch_trans _ m mu m'); [|exact MU'].
      apply (munch_weaken [(LO, SP0)] _ m mu); [|exact MUt].
      intros x Hx. cbn [outside app] in *. destruct Hx as [H1 _]. split; [exact H1 | exact I]. }
    split; [exact (wmono_trans rsegs m mu m' WMt WM')|]. split; [exact MI'|]. split; [exact ST'|].
    split; [exact AC'|]. split; [exact SW'|]. split; [exact AW'|].
    split.
    { apply (fl_fp_D _ _ _ _ _ _ _ _ _ FP').
      apply fl_dj_cons. split; [exact DJT|]. apply fl_dj_cons. split; [exact DJM|].
      apply fl_dj_cons. split; [exact DJd|]. apply fl_dj_cons. split; [exact DJs|]. exact DJo. }
    split; [intros H; discriminate H|].
    intros E1. destruct (RES' E1) as (B & W & CL).
    exact (ba_res rsegs m' o b md NN (bv_unsigned a5 mod 65536) mb nb [] [] db sb Hb6' B W CL).
  Qed.

  Lemma amain : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    evt rsegs aQb
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 md) (Z_to_bv 64 b) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 a6 (Z_to_bv 64 ns) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x848ac) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t4 t5 t6.
    pose proof arng_sp as Rsp.
    pose proof (HST : stk rsegs m (bv_unsigned sp - 4640) (bv_unsigned sp)) as ST. pose proof ST as (Rlo & _ & _).
    pose proof (MI0 : mem_inv rsegs m) as MI.
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* the runtime's cells and the switch table's shadow, apart from the frame *)
    assert (HW : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
                   outside [(bv_unsigned sp + -80, bv_unsigned sp)] x).
    { intros x Hx. cbn [outside]. split; [|exact I].
      unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    pose proof (rt_asan_rt m _ HAC HW) as HRT.
    pose proof (rt_shadow_rd m BA_SW 56 _ ASW (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
    pose proof (rt_addressable m BA_SW 56 ASW) as HAD.
    pose proof (rt_rt3 m BA_SW 56 ASW) as H3.
    step. carve_frame 80%nat ST. do 9 step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (asan_rt_munch rsegs m m1 _ _ ASAN_K _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_shadow_rd_munch rsegs m m1 ASAN_K BA_SW 56 _ _ HSR MU (fun x Hx => Hx)) as HSR1.
    pose proof (asan_addressable_munch rsegs m m1 ASAN_K BA_SW 56 _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
    pose proof (asan_rt3_munch rsegs m m1 ASAN_K BA_SW 56 _ _ H3 HSR MU (fun x Hx => Hx)) as H31.
    (* o = 0 *)
    step. rewrite rc_eqb by lia. destruct (Z.eqb_spec o 0) as [O0|O0]; cbv iota.
    { eapply afail; [apply ba_go_false; left; exact O0 | eassumption ..]. }
    (* m = 0 *)
    step. step. rewrite rc_eqb by lia. destruct (Z.eqb_spec md 0) as [M0|M0]; cbv iota.
    { eapply afail; [apply ba_go_false; right; left; exact M0 | eassumption ..]. }
    (* b > 6 *)
    step. step. step. rewrite rc_ltu by lia. destruct (Z.ltb_spec 6 b) as [B6|B6]; cbv iota.
    { eapply afail; [apply ba_go_false; right; right; exact B6 | eassumption ..]. }
    assert (HG : GO = true) by (apply ba_go_true; assumption).
    (* the shadow byte of the table word b is 0 *)
    destruct (asan_shadow_read_at rsegs m1 ASAN_K BA_SW 56 _ (8 * b) ((BA_SW + 8 * b) / 8 + ASAN_K) HSR1
                ltac:(lia) eq_refl) as (k & RK & BK).
    pose proof (asan_check_8 rsegs m1 ASAN_K BA_SW 56 (8 * b) k HAD1 H31 ltac:(lia) ltac:(lia)
                  ltac:(unfold BA_SW; lia) BK) as K0.
    pose proof (rc_signed0_unsigned0 k K0) as K0u.
    pose proof (asan_rt_got_read rsegs m1 _ _ ASAN_K _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ ASAN_K _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    (* row(b) from the table and f = CTRL_FRAMES + 24 row(b) *)
    destruct (ba_cases b ltac:(lia)) as [Eb|[Eb|[Eb|[Eb|[Eb|[Eb|Eb]]]]]]; rewrite Eb in RK |- *;
      unfold BA_SW, ASAN_K in RK;
      do 11 step;
      rewrite (rcl_zxb_eqb k 0) by lia; rewrite K0u; cbn [Z.eqb negb];
      do 12 step;
      (eapply atail; [exact HG | rewrite Eb; reflexivity | eassumption ..]).
  Qed.
End Build.

Theorem reac_ctrl_build_as_holds :
  ctrl_emit_as_contract -> reac_box_model_upstream_width_contract -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.reac_ctrl_build_as_contract.
Proof.
  intros HEA HUW. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.reac_ctrl_build_as_contract, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns FS mb nb db sb junk.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 -> Hns HS16 HST HT DsT Hdb HD Dsd Hsb HSb Dss HM HN Ho1492 HEo MI0
    HAC HSW HHM HAE AWIN ASW ATB AD AS APD APS AM AN AO AJ14 AJ13 FP FPN FPT.
  pose proof (rc_word_range a0 o Ha0) as Ro. apply rc_word in Ha0. subst a0.
  pose proof (rc_word_range a1 md Ha1) as Rmd. apply rc_word in Ha1. subst a1.
  pose proof (rc_word_range a2 b Ha2) as Rb. apply rc_word in Ha2. subst a2.
  apply rc_word in Ha3. subst a3.
  apply rc_word in Ha4. subst a4.
  eapply amain; eassumption.
Qed.

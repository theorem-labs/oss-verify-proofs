(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Asn1Aux CellsX HeapIface Frame Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM HMFrame AW_DepotB AW_DepotTop AW_MallocB AW_IAInit AW_FreeA AW_FreeC AW_FreeP AW_FreeR AW_FreeG
     AW_FakeDefs AW_FakeRep AHeapR AHeapB AHeapZ AHeapZW AMallocPost AHeapM AHeapL.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AHeapFreeNull () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.ranges_apart_b"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.ia_ranges"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.in_rangesZ"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.ro_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.rwstat_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.dep_zone"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.quar_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.sec_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.emb_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.iagree"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapZ.rzone"; "RocqVerifyHarness.AgentSubmission.BHeap.HMLib.kept"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeA.A_FREE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HM_i"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.htop_i"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcs_i"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.call_postA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hstkhi_i"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hflag_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.havol_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hfr_i"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HK_i"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
#[using="Type"] Lemma zeros_eq : forall n, zeros n = repeat (Z_to_bv 8 0) (Z.to_nat n).
Proof. intros n. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rw_C1_agree : ltac2:(CDefT.buildp (gd_tbl_AHeapFreeNull ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$2.Pv,(0.&8.)P,(3.$4.R4.R2.(5.$6.(7.R1.)(8.$6.)))P,(3.$4.R4.R3.(5.$6.(7.R2.)(8.$6.)))P,(9.(:.(;.R4.+1.)+10000.)(:.+65?000.R4.))(<.(1.(0.&8.))A1.R6.(=.R5.)A1.R7.(=.R5.))")
(* [comment removed for export] *).
Proof.
  (intros m m' A v dd_H; ddestruct dd_H as [[_ (A0 & _ & B)] (_ & A64 & W)]; intros dd_H; ddestruct dd_H as [[_ (_ & _ & B')] (_ & _ & W')]; intros OFF).
  specialize (B 0%nat ltac:(cbn; lia)). specialize (B' 0%nat ltac:(cbn; lia)). cbn [nth_error length cells_bytes cbytes app Z.of_nat] in B, B'.
  specialize (W 0 ltac:(cbn; lia)). specialize (W' 0 ltac:(cbn; lia)). rewrite Z.add_0_r in B, B', W, W'. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in A64.
  destruct (wr_off_byte m A A0 OFF ltac:(clear - A64; lia) W) as [b E]. destruct (wr_off_byte m' A A0 OFF ltac:(clear - A64; lia) W') as [b' E'].
  unfold mrd in B, B'. rewrite E in B. rewrite E' in B'. rewrite E, E'. congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFrameIA.
  Variable STKLO : Z.
  Local Notation hok := (hok STKLO).
  Variables (h : ahst) (m m' : mem).
  Hypothesis HOK : hok h.
  Hypothesis WM : wmono asegs m m'.
  Hypothesis AG : zagree (fun a => rzone h a /\ ~ in_rangesZ ia_ranges a) m m'.
  Hypothesis IAC : ia_cells m'.

  #[using="h AG"] Lemma zimg_sub_ia : ltac2:(CDefT.buildp (gd_tbl_AHeapFreeNull ()) "PRS,(>.(?.$2.$2.))P,(<.$10.(11.R1.$12.)$13.)P,Pa,$2.P,(14.R3.R1.)(14.(15.(?.$2.$2.)$16.(15.(?.$2.$2.)$17.(15.(?.$2.$2.)$18.(15.(?.$2.$2.)$19.(15.(?.$2.$2.)$1:.(15.(?.$2.$2.)$12.$1;.))))))R2.)(1<.R3.Vm,Vm',)")
(* [comment removed for export] *).
  Proof.
    intros RS AP SUB. eapply (iagree_of_zagree _ RS m m' AG). intros a Ha. split; [| exact (ranges_apart_b_sound RS ia_ranges a AP Ha)].
    left. apply (ranges_cover_b_sound _ IMGZ a hm_img_cover). apply SUB, Ha.
  Qed.

  #[using="AG"] Lemma kzi : ltac2:(CDefT.buildp (gd_tbl_AHeapFreeNull ()) "PA,$2.Pn,$2.P,Pa,$2.P,(1=.(:.R3.R1.)(1>.R1.(;.R3.R2.)))(1=.(1?.Vh,R2.)(9.(1>.R2.+10000.)(:.+65?000.R2.)))(20.Vm,Vm',R3.R2.)")
(* [comment removed for export] *).
  Proof. intros A n H. eapply kept_of_zagree; [exact AG|]. intros a Ha. destruct (H a Ha) as [Z1 Z2]. split; [exact Z1|]. unfold ia_ranges. cbn. clear - Z2. lia. Qed.

  #[using="STKLO HOK WM AG IAC"] Theorem HMc_zframe_ia : forall LB LF LF', HMc h LB LF m -> hm_fake h LF' m' -> HMc (set_ia h true) LB LF' m'.
  Proof.
    intros LB LF LF' HM0 GF'. dpose HOK as (EL & AW & VW).
    dpose HM0 as (HP & GM & (GRO & GRW) & GT & GD & GC & GR & GQ & GS & GF & GI & GE).
    dpose AW as ([WL _] & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG).
    pose proof (Lfacts STKLO h HOK) as LF0. unfold kHighMemBeg, kPrimHullLen, kPaHullLen, kFakeBytes in LF0.
    assert (TLO : Timg (l_T (h_L h)) /\ 0 <= l_fs (h_L h)) by (unfold wf_L, lowhigh, kHighMemBeg in WL; clear - WL; lia).
    pose proof (Limg STKLO h HOK) as [TI DI].
    dpose GM as (_ & _ & _ & WRT & _).
    (* [comment removed for export] *)
    assert (K63 : forall k, In k (h_chunks h) -> 0x65f000 <= ck_ab k /\ 0x65f000 <= ck_user k /\ (ck_prim k = false -> 0x65f000 + 4096 <= ck_ab k)).
    { intros k Hk. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & _ & _ & [E5 _] & _).
      unfold ext_lo in E1, E5. unfold ck_hdr, ck_user, ck_map_beg, kChunkHeaderSize in *. pose proof (rz_size_bound' (ck_n k)) as RZ. unfold ck_rz in *.
      destruct (ck_prim k).
      - clear - E1 E2 E5 RZ. split; [lia|]. split; [lia|]. intros X; discriminate X.
      - clear - E1 E2 E5 RZ. split; [lia|]. split; [lia|]. intros _; lia. }
    assert (B63 : forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> 0x65f000 <= b_addr b).
    { intros b Hb. ddestruct (batch_slot h b (WFR_of_awf' h AW) Hb) as (i & Hi & ->). dpose LF0 as (_ & _ & B1 & _ & B2 & _).
      unfold chunk_at, region_beg, kRegionSize, kBatchClass. pose proof (class_size_range 24 ltac:(lia)). clear - Hi B1 B2 H. nia. }
    assert (G1' : hm_statics (h_L h) m').
    { split.
      + eapply hm_ro_frame; [exact GRO| | | | |].
        * apply zimg_sub_ia; [vm_compute; reflexivity|]. intros a Ha. rewrite !in_rangesZ_app. tauto.
        * apply kzi. intros a Ha. split; [right; left; clear - Ha; lia| clear - Ha TI; lia].
        * apply kzi. intros a Ha. split; [right; right; left; unfold wf_L in WL; clear - Ha WL; lia| clear - Ha LF0; lia].
        * apply kzi. intros a Ha. split; [right; right; left; unfold wf_L in WL; clear - Ha WL; lia| clear - Ha LF0; lia].
        * apply kzi. intros a Ha. split; [do 15 right; clear - Ha; lia| clear - Ha DI; lia].
      + eapply hm_rwstat_frame; [exact WM| exact GRW|]. apply zimg_sub_ia; [vm_compute; reflexivity|]. intros a Ha. rewrite !in_rangesZ_app. tauto. }
    assert (G2' : hm_thread h m').
    { eapply hm_thread_frame; [exact WM| exact GT| | | | exact WRT| clear - TLO; lia].
      + apply kzi. intros a Ha. split; [right; left; clear - Ha; lia| clear - Ha TI; lia].
      + intros c Hc. apply kzi. intros a Ha. split; [right; left; clear - Ha Hc; lia| clear - Ha Hc TI; lia].
      + apply kzi. intros a Ha. split; [right; left; clear - Ha; lia| clear - Ha TI; lia]. }
    assert (G3' : hm_depot h m').
    { eapply hm_depot_frame; [exact GD| exact WM| | |].
      + apply zimg_sub_ia; [vm_compute; reflexivity|]. intros a Ha. rewrite !in_rangesZ_app. tauto.
      + intros b Hb. dpose WD as (_ & _ & F & _). pose proof (proj1 (Forall_forall _ _) F b Hb) as (Hb63 & _).
        apply kzi. intros a Ha. split; [do 3 right; left; exists b; auto| clear - Ha Hb63; lia].
      + intros b Hb. dpose WD as (_ & _ & _ & _ & _ & F & _). pose proof (proj1 (Forall_forall _ _) F b Hb) as (Hb63 & _).
        apply kzi. intros a Ha. split; [do 4 right; left; exists b; auto| clear - Ha Hb63; lia]. }
    assert (G4' : hm_chunks h m').
    { eapply hm_chunks_frame; [exact WM| exact GC| exact AW|]. intros k Hk. ddestruct (K63 k Hk) as (KA & KU & _). split; [| split].
      + apply kzi. intros a Ha. split; [do 5 right; left; exists k; split; [exact Hk|]; unfold ck_user; clear - Ha; lia| clear - Ha KA; lia].
      + intros ST. apply kzi. intros a Ha. split; [do 6 right; left; exists k; auto|]. unfold HM.shad, AW_FreeG.shad in Ha. pose proof (Z.div_mod (ck_user k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ck_user k) 8 ltac:(lia)). clear - Ha KU H H0. lia.
      + intros ST. apply kzi. intros a Ha. split; [do 7 right; left; exists k; auto| clear - Ha KU; lia]. }
    assert (G5' : hm_regions h m').
    { eapply hm_regions_frame; [exact WM| exact GR| exact WR|]. intros c Hc. dpose LF0 as (_ & _ & B1 & _ & B2 & _). split; [| split; [| split]].
      + apply kzi. intros a Ha. split; [do 8 right; left; exists c; auto| unfold ri_addr, ri_base, space_end, kSpaceSize in Ha; clear - Ha Hc B1 B2; lia].
      + apply kzi. intros a Ha. split; [do 9 right; left; exists c; auto| unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset in Ha; clear - Ha Hc B1 B2; nia].
      + apply kzi. intros a Ha. split; [do 10 right; left; exists c; split; [exact Hc|]; cbn zeta; exact Ha|]. unfold HM.shad, AW_FreeG.shad in Ha.
        pose proof (WR c ltac:(unfold kNumClasses; clear - Hc; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _).
        set (q := region_beg (h_L h) c + r_alloc_user (h_reg h c)) in *. pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
        unfold region_beg, kRegionSize in q. clear - Ha Hc B1 B2 AUMU H H0. lia.
      + intros k Hk. apply kzi. intros a Ha. split; [do 11 right; left; dexists c, k; split; [exact Hc|]; split; [exact Hk|]; clear - Ha; lia|]. unfold HM.shad, AW_FreeG.shad in Ha.
        set (q := chunk_at (h_L h) c k) in *. pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)). pose proof (class_size_range c Hc).
        unfold chunk_at, region_beg, kRegionSize in q. clear - Ha Hc Hk B1 B2 H H0 H1. nia. }
    assert (G6' : hm_quar h m').
    { eapply hm_quar_frame; [exact WM| exact GQ| | |].
      + apply zimg_sub_ia; [vm_compute; reflexivity|]. intros a Ha. rewrite !in_rangesZ_app. tauto.
      + apply kzi. intros a Ha. split; [right; left; clear - Ha; lia| clear - Ha TI; lia].
      + intros b Hb. pose proof (B63 b Hb) as Hb63. apply kzi. intros a Ha. split; [do 12 right; left; exists b; auto| clear - Ha Hb63; lia]. }
    assert (G7' : hm_sec h m').
    { eapply hm_sec_frame; [exact WM| exact GS| exact WS| | |].
      + apply zimg_sub_ia; [vm_compute; reflexivity|]. intros a Ha. rewrite !in_rangesZ_app. tauto.
      + apply kzi. intros a Ha. split; [do 13 right; left; exact Ha| clear - Ha LF0; lia].
      + intros sh Hsh. destruct (In_nth_error _ _ Hsh) as [i Ni]. dpose WK as (_ & _ & WK3). ddestruct (WK3 i sh Ni) as (k & Hk & PK & MB & MS).
        ddestruct (K63 k Hk) as (_ & _ & KA). specialize (KA PK). unfold ck_map_beg in MB.
        apply kzi. intros a Ha. split; [do 14 right; left; exists sh; auto| clear - Ha KA MB; lia]. }
    assert (G9' : hm_ia (set_ia h true) m').
    { unfold hm_ia. cbn [h_ia set_ia]. ddestruct IAC as (I1 & I2 & I3 & I4 & I5 & I6 & (cs5 & I7 & S7)).
      split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [dexists (Z_to_bv 64 4096), (Z_to_bv 64 (A_IA + 0x40dd0)); split; [exact I5| intros _; split; reflexivity]|].
      split; [exact I6|]. exists cs5. split; [exact I7| rewrite S7; reflexivity]. }
    (* [comment removed for export] *)
    split; [exact HP|]. split; [exact (hm_maps_frame _ _ _ GM WM)|]. split; [exact G1'|]. split; [exact G2'|]. split; [exact G3'|]. split; [exact G4'|].
    split; [exact G5'|]. split; [exact G6'|]. split; [exact G7'|]. split; [exact GF'|]. split; [exact G9'|].
    (* [comment removed for export] *)
    apply (hm_emb_frame_i m m' WM h _ GE); [reflexivity| reflexivity|]. apply zimg_sub_ia; [vm_compute; reflexivity|]. intros a Ha. rewrite !in_rangesZ_app. tauto.
  Qed.

  #[using="Type"] Lemma rtc_cells_ia_apart : forallb (fun c : rtc_cell => let '(a, n, v) := c in ranges_apart_b [(a, a + Z.of_nat (cells_size [rtc_mkcell n v]))] ia_ranges) rtc_cells = true.
  Proof. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma rtc_prist_ia_apart : ranges_apart_b rtc_pristine ia_ranges = true.
  Proof. vm_compute. reflexivity. Qed.

  #[using="h AG"] Lemma XR_zframe_ia : XR m -> XR m'.
  Proof.
    (intros dd_H; ddestruct dd_H as ([RC PR] & ISH & XF)). split; [split| split].
    - apply Forall_forall. intros [[a n] v] Hin. pose proof (proj1 (Forall_forall _ _) RC _ Hin) as H. unfold rtc_holds in H |- *.
      pose proof rtc_cells_cover as CV. unfold rtc_cells_in_b in CV. rewrite forallb_forall in CV. specialize (CV _ Hin). cbn beta iota in CV.
      pose proof rtc_cells_ia_apart as AP. rewrite forallb_forall in AP. specialize (AP _ Hin). cbn beta iota in AP.
      eapply keep_ro; [exact H|]. eapply kept_of_zagree; [exact AG|]. intros x Hx. split; [left; eapply range_in_b_sound; [exact CV| exact Hx]|].
      eapply ranges_apart_b_sound; [exact AP|]. cbn. left. exact Hx.
    - intros a Ha. pose proof (PR a Ha) as E. unfold rtc_prist in Ha.
      assert (IN : in_rangesZ rtc_pristine a).
      { clear - Ha. unfold rtc_pristine in *. apply Exists_exists in Ha. ddestruct Ha as ([lo hi] & Hin & R). cbn in R.
        cbn in Hin. cbn. destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as <- <-; unfold AGLOB_LO, AGLOB_HI in *; lia. }
      pose proof (ranges_cover_b_sound _ _ a rtc_prist_cover IN) as INZ.
      assert (RA : 0 <= a < 2^64).
      { clear - INZ. unfold IMGZ, RT in INZ. cbn in INZ. lia. }
      rewrite <- E. pose proof (AG (wa a)) as X. rewrite wa_unsigned in X by exact RA. apply X. split; [left; exact INZ|].
      exact (ranges_apart_b_sound _ _ a rtc_prist_ia_apart IN).
    - intros g Hg NR. pose proof (ISH g Hg NR) as B.
      eapply (bytes_at_transport _ _ m m'); [exact B| apply (kept_munch m m' (shadow_of AL0 (8 * g)) 1); [unfold shadow_of, AL0; cbn; clear - Hg; unfold IMG_GLO in Hg; lia|]|].
      + eapply kept_of_zagree; [exact AG|]. intros a Ha. unfold shadow_of, AL0, IMG_GLO, IMG_GHI in *. cbn [al_sb] in Ha.
        rewrite Z.mul_comm, Z.div_mul in Ha by lia. split; [left; unfold IMGZ, RT; cbn; clear - Ha Hg; lia| unfold ia_ranges; cbn; clear - Ha Hg; lia].
      + cbn [disjoint_from length Z.of_nat Pos.of_succ_nat]. unfold shadow_of. clear. repeat split; lia.
    - (* [comment removed for export] *)
      unfold xf_cells in *. eapply keep_ro; [exact XF|]. eapply kept_of_zagree; [exact AG|]. intros a Ha. unfold A_FLAGS in Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
      split; [left; unfold IMGZ, RT; cbn; clear - Ha; lia| unfold ia_ranges; cbn; clear - Ha; lia].
  Qed.
End ZFrameIA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FN.
  Variable STKLO : Z.
  Hypothesis STKLO_OK : ACEIL <= STKLO.
  Let R := R0 STKLO.
  Local Notation hok := (hok STKLO).
  Local Notation hst := (hst STKLO).
  Local Notation HMi := (HM_i STKLO).
  Local Notation HKi := (HK_i STKLO).
  Local Notation hcs := (hcs_i STKLO).

  (* [comment removed for export] *)
  #[using="Type"] Lemma free_tramp0 : ltac2:(CDefT.buildp (gd_tbl_AHeapFreeNull ()) "PCS,P,$2.SpPra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(21.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(22.$23.R23.)(24.$4.$23.R24.Lms',$25.(<.$25.R1.(26.(27.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(28.&40.$29.)R4.(2:.(0.&40.))R3.(2;.$4.)))(26.(27.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(28.&40.+6947<.)R3.(2:.(0.&40.))R2.(2;.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof AL0_wf as ALWF'; unfold al_wf in ALWF'. pose proof AL0_img as IMG'; unfold asan_img_ok in IMG'.
    unfold A_FREE. zstep. apply evtA_done. reflexivity.
  Qed.

  #[using="STKLO_OK"] Theorem free_null_field : ltac2:(CDefT.buildp (gd_tbl_AHeapFreeNull ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(21.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))Ps,(2<.VhAR,VSTKLO,)PLB,(>.$2=.)PLF,(>.$2=.)Plo,$2.P,(2>.VhAR,VSTKLO,R4.R3.R2.R5.)P,(2?.$4.R6.R2.(30.&40.R26.))P,(:.(31.VR,)R3.)P,(:.R4.(32.(30.&40.R28.)(33.VR,)))P,(:.(30.&40.R29.)(34.VhAR,VSTKLO,R8.))P,(<.$2.(35.(30.&40.R2:.)+10.)=)P,(36.$4.R;.)P,(<.(0.&40.)R2:.(28.&40.(37.VR,)))P,(<.(0.&40.)R25.(28.&40.=))(24.$4.$23.(38.VhAR,VSTKLO,R=.)(39.$4.R2?.R2>.R2=.R2<.R28.R27.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R10.R?.L,(0.&40.)Lm',P,(0.&40.)(1.(0.&8.))(1=.(36.$4.R1.)(1=.(2?.$4.R1.R<.(30.&40.R30.))(1=.(3:.$4.R10.R1.)(1=.(3;.$4.VR,R>.R=.(30.&40.R30.)(31.VR,)(3<.VhAR,VSTKLO,R?.)(8.$3=.)R10.R1.)(3>.(2<.VhAR,VSTKLO,)Ls',(2<.VhAR,VSTKLO,)(1=.(<.P,$2.Sp(38.VhAR,VSTKLO,R1.)(38.VhAR,VSTKLO,R10.))(1=.(<.$2.(34.VhAR,VSTKLO,R1.)(34.VhAR,VSTKLO,R10.))(1=.(<.$2.(3<.VhAR,VSTKLO,R1.)(3<.VhAR,VSTKLO,R10.))(1=.(<.$2.(3?.VhAR,VSTKLO,R1.)(3?.VhAR,VSTKLO,R10.))(1=.(<.$2.(40.VhAR,VSTKLO,R1.)(40.VhAR,VSTKLO,R10.))(1=.(<.$2.(41.VhAR,VSTKLO,R1.)(41.VhAR,VSTKLO,R10.))(1=.Pmo,$42.(43.(44.VhAR,VSTKLO,R2.R1.)(44.VhAR,VSTKLO,R11.R1.))(2>.VhAR,VSTKLO,R1.R?.R>.R2.))))))))))))))(26.(27.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(28.&40.(45.VR,))R?.(2:.(0.&40.))R>.(2;.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [h HOK] LB LF lo
      [HM0 [XR0 HA0]] ST LO SPL SPT SPA MI -> ->.
    unfold hcs_i, htop_i, hstkhi_i, hflag_i, havol_i, hfr_i, HK_i in *. cbn [hh arl_stklo arl_free arl_tp arl_need_free R R0] in *.
    dpose HOK as (EL & AW & VW). dpose (hok_L STKLO h HOK) as (_ & _ & _ & SHI & _ & T1 & T2). pose proof (Lfacts STKLO h HOK) as LF0.
    dpose (Lbands STKLO h HOK) as (TB & CB & _). pose proof (Limg STKLO h HOK) as [TI _].
    unfold kHighMemBeg, kPrimHullLen, kPaHullLen, kFakeBytes in LF0.
    dpose VW as (TWF & APT & _).
    pose proof AW as ([WL _] & _). dpose WL as (_ & _ & _ & _ & _ & _ & _ & _ & TOP23 & TOPHI & _).
    dpose HM0 as (HP & GM & (GRO & GRW) & GT & GD & GC & GR & GQ & GS & GF & GI & GE).
    dpose GM as (SHLO & SHHI & STKW & TW & CTXW & FSW).
    dpose GRO as (MS8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TH & THR & TSW & _).
    pose proof GT as (UNW & _).
    dpose GI as (IA1 & IA2 & IA3 & (cs2 & IA4 & IS4) & (p0 & p1 & IA5 & IP) & (cs4 & IA6 & IS6) & (cs5 & IA7 & IS7)).
    set (SP := bv_unsigned sp) in *. assert (ESP : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
    set (L := h_L h) in *. set (T := l_T L) in *. set (CTX := l_ctx L) in *. set (TOP := l_top L) in *.
    assert (LOIMG : ACEIL <= lo) by (clear - LO STKLO_OK; lia).
    (* [comment removed for export] *)
    assert (TC : T + 4096 <= CTX \/ CTX + 0x10000 <= T).
    { destruct (APT _ _ (tr_of_T h) (tr_of_ctx h)) as [E|X]; [exfalso; injection E; subst L; clear - LF0; lia|].
      unfold t_hi in X. cbn [t_lo t_len] in X. subst T CTX L. clear - X LF0. lia. }
    (* [comment removed for export] *)
    assert (STT : stk asegs m SP TOP).
    { destruct (Z.le_gt_cases SP TOP) as [LEt|GTt].
      - apply wr_at_high_stk; [| clear - LOIMG SPL; lia| exact LEt].
        pose proof (wr_at_sub m (l_stk_lo L) _ (SP - l_stk_lo L) (TOP - SP) STKW ltac:(subst L; clear - EL LO SPL; lia) ltac:(clear - LEt; lia) ltac:(subst TOP L; clear - TOPHI; lia)) as W.
        replace (l_stk_lo L + (SP - l_stk_lo L)) with SP in W by (clear; lia). exact W.
      - split; [clear - LOIMG SPL; lia|]. split; [subst TOP L; clear - TOPHI SHI; lia|]. intros a Ha. exfalso. clear - Ha GTt. lia. }
    eapply evtA_cut; [apply (free_tramp0 (hcsA h)); exact (hcsA_ok STKLO h HOK)|]. cbn beta. intros ms0 ->.
    assert (Q1 : TOP <= 2^47) by (subst TOP L; clear - TOPHI SHI; lia).
    assert (Q2 : SP + 16 <= 2^47) by (subst L; clear - SPT T2 SHI; lia).
    assert (Q3 : T + 4096 <= ACEIL) by (subst T L; clear - LF0; lia).
    assert (Q4 : 0x65f000 <= CTX) by (subst CTX L; clear - LF0; lia).
    assert (Q5 : CTX + 0x10000 <= ACEIL) by (subst CTX L; clear - LF0; lia).
    assert (Q6 : crange (hcsA h) T 4096) by (intros x Hx; left; apply (crange_T AL0 h); exact Hx).
    assert (Q7 : crange (hcsA h) CTX 0x10000).
    { intros x Hx; left; apply (crange_ctx AL0 h). subst CTX L. dpose LF0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). rewrite CL. exact Hx. }
    assert (Q8 : crange (hcsA h) SP (TOP - SP)) by (intros x Hx; apply (hcsA_stack STKLO h HOK); subst TOP L; clear - Hx LO SPL TOPHI; lia).
    assert (Q9 : lo <= SP - 4096) by (clear - SPL; lia).
    assert (Q10 : crange (hcsA h) lo (SP - lo)) by (intros x Hx; apply (hcsA_stack STKLO h HOK); subst L; clear - Hx LO SPT T2; lia).
    rewrite (zeros_eq 0x40000) in IA3.   (* [comment removed for export] *)
    eapply evtA_mono.
    { (* [comment removed for export] *)
      exact (free_null_seg AL0 AL0_img AL0_wf (hcsA h) (hcsA_ok STKLO h HOK)
               ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP lo T CTX TOP F fc m (h_ia h) cs2 cs4 cs5 p0 p1
               IA1 IA2 IA3 IA4 IS4 IA5 IP IA6 IS6 IA7 IS7 MS8 THR TSW UNW TOP23 Q1 Q2 TI Q3 Q4 Q5 TC Q6 Q7 STT Q8 ST LOIMG Q9 SPA Q10 MI). }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (m' & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & MU & WM & MI' & UNW' & ST' & SR' & IAC')).
    (* [comment removed for export] *)
    assert (LT3168 : rzone h (T + 3168)) by (right; left; subst T L; clear; lia).
    pose proof (rzone_lt_stklo STKLO h HOK _ LT3168) as T3.
    assert (TOFF : T + 3168 + 1 <= 0x10000 \/ 0x65f000 <= T + 3168) by (clear - TI; lia).
    assert (OUTW : forall a, a <> T + 3168 -> ~ (lo <= a < SP) -> ~ in_rangesZ ia_ranges a -> outside ((T + 3168, T + 3169) :: ia_W lo SP) a).
    { intros a N1 N2 N3. unfold ia_W, A_IA, A_IA_INIT. unfold ia_ranges in N3. cbn in N3. cbn [outside]. clear - N1 N2 N3. repeat split; lia. }
    assert (AG : zagree (fun a => rzone h a /\ ~ in_rangesZ ia_ranges a) m m').
    { intros x [Zx NIA]. pose proof (rzone_lt_stklo STKLO h HOK _ Zx) as LT.
      destruct (Z.eq_dec (bv_unsigned x) (T + 3168)) as [E|NE].
      - rewrite <- (wa_unsigned_id x), E. exact (rw_C1_agree m m' (T + 3168) (b8 0) UNW UNW' TOFF).
      - apply MU. apply OUTW; [exact NE| clear - LT LO; lia| exact NIA]. }
    (* [comment removed for export] *)
    assert (HA' : hm_absent h m').
    { apply (hm_absent_agree h m m' HA0). intros x Zx. apply MU.
      dpose (habs_zone_out STKLO h (bv_unsigned x) HOK Zx) as (Y1 & Y2 & Y3).
      assert (NT : ~ (l_T (h_L h) <= bv_unsigned x < l_T (h_L h) + 4096)).
      { intros X. apply (habs_zone_tr h (bv_unsigned x) _ Zx (tr_of_T h)). unfold t_hi. cbn [t_lo t_len]. exact X. }
      apply OUTW; [subst T L; clear - NT; lia| clear - Y3 LO; lia| unfold ia_ranges; cbn; clear - Y1; lia]. }
    (* [comment removed for export] *)
    assert (FST : T + 4096 <= l_fs L \/ l_fs L + kFakeBytes <= T).
    { destruct (APT _ _ (tr_of_T h) (fs_tr_in h)) as [E|X]; [exfalso; injection E; unfold kFakeBytes; clear; lia|].
      unfold t_hi in X. cbn [t_lo t_len] in X. subst T L. clear - X. lia. }
    assert (AGF : zagree (fzone h LF) m m').
    { intros x Fx. apply MU. pose proof (u64_range x).
      assert (FR : l_fs L <= bv_unsigned x < l_fs L + kFakeBytes).
      { destruct Fx as [F1|(fb & Hfb & F2)]; [subst L; unfold kFakeBytes; clear - F1; lia|].
        dpose (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & G3). subst L. clear - F2 G1 G2 G3. lia. }
      unfold kFakeBytes in *. apply OUTW; [clear - FR FST; lia| subst L; clear - FR LF0 LO STKLO_OK; lia| unfold ia_ranges; cbn; subst L; clear - FR LF0; lia]. }
    assert (BT : forall A n a, In (A, n) LB -> A <= a < A + n -> 0x65f000 <= a < ACEIL /\ a <> T + 3168).
    { intros A n a HB Ra. dpose (block_bounds STKLO h LB LF m HOK HM0 A n HB) as (BB1 & BB2 & BB3 & _). split; [clear - Ra BB1 BB3; lia|].
      pose proof HP as [_ HLB]. rewrite HLB in HB. ddestruct (live_block h A n HB) as (k & Hk & _ & -> & ->).
      ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & [(PK & C30 & R1 & R2 & _)|(PK & sh & Hsh & SQ1 & SQ2)]).
      - dpose AW as (_ & _ & WR & _). pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; clear - C30; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _).
        ddestruct (user_point_unit h (ck_cls k) a AW ltac:(clear - C30; lia) ltac:(clear - Ra E1 E2 E3 R1 R2 AUMU; lia)) as (j & INj & Rj).
        destruct (APT _ _ (tr_of_T h) INj) as [E|X]; [exfalso; unfold uunit_tr in E; discriminate E|].
        unfold t_hi, uunit_tr in X, Rj. cbn [t_lo t_len] in X, Rj. subst T L. clear - X Rj. lia.
      - destruct (APT _ _ (tr_of_T h) (tr_of_sec h sh Hsh)) as [E|X].
        + exfalso. dpose AW as (_ & _ & _ & _ & _ & WS & _). dpose WS as (_ & _ & _ & _ & _ & _ & _ & SHW). pose proof (proj1 (Forall_forall _ _) SHW sh Hsh) as (_ & SM & _).
          unfold sec_tr in E. injection E as E1' E2'. clear - E2' SM. lia.
        + unfold t_hi, sec_tr in X. cbn [t_lo t_len] in X. subst T L. clear - X Ra E1 E2 E3 SQ1 SQ2. lia. }
    (* [comment removed for export] *)
    pose proof (hm_fake_zframe STKLO h m m' HOK WM LF GF AGF) as GF'.
    pose proof (HMc_zframe_ia STKLO h m m' HOK WM AG IAC' LB LF LF HM0 GF') as HM'.
    pose proof (XR_zframe_ia h m m' AG XR0) as XR'.
    (* [comment removed for export] *)
    unfold call_postA. dexists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact WM|].
    split.
    { apply (presA_intro STKLO h LB LF m m' SP WM).
      - intros a Ha CA. apply MU. rewrite wa_unsigned by exact Ha.
        destruct CA as [S|[C|(b & Hb & Rb)]].
        + apply OUTW; [clear - S T3 LO SPL STKLO_OK; lia| clear - S; lia| unfold ia_ranges; cbn; clear - S LO SPL STKLO_OK ; pose proof aceil_bounds; lia].
        + cbn [hl_data_lo hl_data_hi hl_static HL0 arl_L R R0] in C. destruct C as [C1 C2]. unfold RT in C2. cbn [in_rangesZ] in C2.
          apply OUTW; [clear - C1 TI; lia| clear - C1 LO STKLO_OK; pose proof aceil_bounds; lia| unfold ia_ranges; cbn; clear - C1 C2; lia].
        + apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
          * destruct b as [B j]. cbn [fst snd] in Rb. destruct (BT B j a Hb Rb) as [R1 R2].
            apply OUTW; [exact R2| clear - R1 LO STKLO_OK; lia| unfold ia_ranges; cbn; clear - R1; lia].
          * ddestruct (fdata_sub LF (fst b) (snd b) ltac:(destruct b; exact Hb)) as (fb & [(Hfb & F1 & F2)|(Hfb & F40)]);
              dpose (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & G3); [| clear - F40 G3; lia].
            unfold kFakeBytes in *. apply OUTW; [subst T L; clear - Rb F1 F2 G1 G2 FST; lia| subst L; clear - Rb F1 F2 G1 G2 LF0 LO STKLO_OK; lia| unfold ia_ranges; cbn; subst L; clear - Rb F1 F2 G1 G2 LF0; lia].
      - intros c Hc Hr. apply MU. rewrite wa_unsigned by exact Hr.
        assert (SHC : shadow_of AL0 c = HM.shad c) by reflexivity. rewrite SHC in *.
        assert (C47 : 0 <= c < 2^47).
        { destruct (cshd_cases STKLO h LB LF c Hc) as [S|[(A & n & HIn & RA)|[(fb & Hfb & Rfb)|C]]].
          - subst L. clear - S LO SHI STKLO_OK; pose proof aceil_bounds; lia.
          - destruct (BT A n c HIn RA) as [R1 _]. clear - R1; pose proof aceil_bounds; lia.
          - dpose (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & _). subst L. unfold kFakeBytes in *. clear - G1 G2 Rfb LF0; pose proof aceil_bounds; lia.
          - clear - C; lia. }
        assert (SB : 0x7fff8000 <= HM.shad c < kHighMemBeg) by (unfold HM.shad, kHighMemBeg; pose proof (Z.div_mod c 8 ltac:(lia)); pose proof (Z.mod_pos_bound c 8 ltac:(lia)); clear - C47 H H0; lia).
        unfold kHighMemBeg in SB. apply OUTW; [clear - SB TB; lia| clear - SB LO STKLO_OK; pose proof aceil_bounds; lia| unfold ia_ranges; cbn; clear - SB; lia]. }
    assert (HOK' : hok (set_ia h true)) by exact HOK.
    exists (HS STKLO (set_ia h true) HOK'). cbn [hh].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [intros mo; split; intros X; exact X|].
    exact (conj HM' (conj XR' HA')).
  Qed.
End FN.
End ARUN_1.

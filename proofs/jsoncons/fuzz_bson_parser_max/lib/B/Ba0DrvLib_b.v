(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma no_bls : forall (P : nat -> Z -> Prop) i nb, DrvKitA.find_nz i [] = Some nb -> P i nb.
Proof. intros P i nb H. discriminate H. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.

Section DrvLayoutA.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.

  (* [comment removed for export] *)
  Record drv_layoutA : Prop := DLA {
    dla_segs : hl_segs L = ASEGS;
    dla_malloc : hl_malloc L = 0x79818; dla_free : hl_free L = 0x79814; dla_memcpy : icl_memcpy IL = 0x77c90;
    dla_tp : hl_tp L = 0x673d00;
    dla_img_lo : hl_img_lo L = 0x10000; dla_img_hi : hl_img_hi L = 0x696000;
    dla_sptop : ar_sptop ar = bv_unsigned sp0;
    dla_scr : 0 <= hl_scr_malloc L <= 4096 /\ 0 <= hl_scr_free L <= 4096 /\ 0 <= hl_scr_mem L <= 4096;
    (* [comment removed for export] *)
    dla_client : forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> ~ hl_rt_static L a;
    (* [comment removed for export] *)
    dla_ro : forall lo hi a, In (lo, hi) IMG_W_A -> lo <= a < hi -> ~ hl_rt_ro L a;
    dla_ro_img : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x696000
  }.
  Hypothesis DL : drv_layoutA.

  Lemma wseg_stage : wseg_ok ASEGS (Z_to_bv 64 0x662290) 65536 = true.
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma vis_of_inv : forall LB FF LK cr A M model a,
    ri_inv HI LB FF LK cr A M (vml_of model) -> 0 <= a < 2 ^ 64 ->
    (a < 0x696000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LB a) ->
    ahid A model (Z_to_bv 64 a) = false.
  Proof.
    intros LB FF LK cr A M model a HH Ha Hc.
    destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [exfalso | reflexivity].
    unfold ahid, mkH in Hh. apply andb_prop in Hh as [Hl _].
    destruct (aiob_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
    specialize (LZ (Z_to_bv 64 a) Hl). cbv zeta in LZ. rewrite u_small in LZ by lia.
    rewrite (dla_img_hi DL), (dla_sptop DL) in LZ. destruct LZ as (Z1 & Z2 & Z3 & _).
    destruct Hc as [Hc|[Hc|Hc]]; [lia | lia | exact (Z3 Hc)].
  Qed.

  (* [comment removed for export] *)
  Lemma nolazy_of_inv : forall LB FF LK cr A M (model : Model) (a : word) n,
    ri_inv HI LB FF LK cr A M (vml_of model) -> bv_unsigned a + n <= 2 ^ 64 ->
    (forall k, 0 <= k < n -> bv_unsigned a + k < 0x696000 \/ bv_unsigned sp0 - 8388608 <= bv_unsigned a + k \/ in_block LB (bv_unsigned a + k)) ->
    nolazy_rng (m_vm_lazy model) a n.
  Proof.
    intros LB FF LK cr A M model a n HH Hn Hc k Hk. pose proof (u64_range a) as Ua.
    destruct (page_in_ranges (page_base_of (bv_unsigned a + k)) (m_vm_lazy model)) eqn:Hp; [exfalso | reflexivity].
    destruct (aiob_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
    specialize (LZ (Z_to_bv 64 (bv_unsigned a + k))). unfold page_base in LZ. rewrite u_small in LZ by lia.
    specialize (LZ Hp). cbv zeta in LZ. rewrite (dla_img_hi DL), (dla_sptop DL) in LZ. destruct LZ as (Z1 & Z2 & Z3 & _).
    destruct (Hc k Hk) as [H1|[H1|H1]]; [lia | lia | exact (Z3 H1)].
  Qed.

  (* [comment removed for export] *)
  Definition CPa (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (H H' : word -> bool) (a : Z) : Prop :=
    aclient L ar LB FF sp scr a /\ H (Z_to_bv 64 a) = false /\ H' (Z_to_bv 64 a) = false.
  Definition SCa (sp scr : Z) (a : Z) : Prop := sp - scr <= a < sp.

  (* [comment removed for export] *)
  Definition sub_blockA (LB : list (Z * Z)) (A nb : Z) : Prop :=
    exists cap, 0 < nb <= cap /\ In (A, cap) LB /\ ablock_range L ar A cap.

  Definition hzA (A n : Z) : Prop := 4096 <= A /\ (A + n <= 0x10000 \/ 0x696000 <= A) /\ A + n <= bv_unsigned sp0 - 8388608.
  Lemma hzA_of_block_range : forall A n, ablock_range L ar A n -> hzA A n.
  Proof.
    clear Hsp Hal. intros A n (B1 & B2 & B3 & B4 & B5 & B6). rewrite (dla_img_lo DL), (dla_img_hi DL) in B2. rewrite (dla_sptop DL) in B5.
    unfold hzA. repeat split; lia.
  Qed.
  Lemma sub_blockA_hz : forall LB A nb, sub_blockA LB A nb -> hzA A nb.
  Proof. clear Hsp Hal. intros LB A nb (cap & Hnb & _ & HB). apply hzA_of_block_range in HB. unfold hzA in *. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma regions_callA : forall vals ebs so scr bls vbnd LBc LB LB' FF FF' LK LK' cr cr' A A' M M' model model',
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    - 2 ^ 22 <= so <= 0 -> 0 <= scr <= 4096 ->
    ri_inv HI LB FF LK cr A M (vml_of model) -> ri_inv HI LB' FF' LK' cr' A' M' (vml_of model') ->
    (forall a, in_block LBc a -> in_block LB a) -> (forall a, in_block LBc a -> in_block LB' a) ->
    (forall i nb, find_nz i bls = Some nb -> sub_blockA LBc (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> bv_unsigned (vals_ev vals v) <= b) ->
    regions_ok ASEGS 0 so scr bls vbnd [] IMG_CLIENT_A IMG_RW_A E
               (CPa LBc FF (bv_unsigned sp0 + so) scr (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) scr).
  Proof.
    intros vals ebs so scr bls vbnd LBc LB LB' FF FF' LK LK' cr cr' A A' M M' model model' E P0 Hso Hscr HH HH' Hsub Hsub' Hbl Hvb.
    pose proof Hsp as Hsp'.
    assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x696000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LBc a) ->
                  ahid A model (Z_to_bv 64 a) = false /\ ahid A' model' (Z_to_bv 64 a) = false).
    { intros a Ha Hc. split.
      - apply (vis_of_inv _ _ _ _ _ _ _ a HH Ha). destruct Hc as [Hc|[Hc|Hc]]; auto.
      - apply (vis_of_inv _ _ _ _ _ _ _ a HH' Ha). destruct Hc as [Hc|[Hc|Hc]]; auto. }
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPa. split; [|apply VIS; lia].
      unfold aclient. right. left. rewrite (dla_sptop DL). lia.
    - intros z Hz. right. unfold SCa. lia.
    - intros i nb Hf. pose proof (sub_blockA_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
      destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hzA_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
      split; [lia|]. intros z Hz.
      assert (IB : in_block LBc (bv_unsigned (vals_ev vals i) + z)).
      { exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia. }
      unfold CPa. split; [left; exact IB | apply VIS; [lia | right; right; exact IB]].
    - exact Hvb.
    - intros i [].
    - intros lo hi Hin. pose proof (dla_client DL lo hi) as NS. destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3).
      split; [lia|]. split; [lia|]. intros a Ha. unfold CPa. split; [|apply VIS; lia]. unfold aclient. right. right. left.
      rewrite (dla_img_lo DL), (dla_img_hi DL). split; [lia|]. exact (NS a Hin Ha).
    - intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
      intros Mx d m Hd Hm.
      apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x662290) (Z_to_bv 64 d) 65536%nat m 0x662290 0x672290);
        first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
  Qed.

  (* [comment removed for export] *)
  Lemma regs_preserved_keptA : forall R R', regs_preserved R R' -> forall r : reg, In r c_kept -> getr R' r = getr R r.
  Proof.
    intros R R' HP r Hr. apply HP. unfold c_kept in Hr. unfold callee_saved_idx.
    repeat (destruct Hr as [<-|Hr]; [cbn; tauto|]). destruct Hr.
  Qed.
  Lemma c_kept_no0A : ~ In (0%bv : reg) c_kept.
  Proof. unfold c_kept. intros H. repeat (destruct H as [H|H]; [discriminate|]). exact H. Qed.

  Lemma vals_ev_junkA : forall vals R' i, (i < 32)%nat ->
    vals_ev (vals ++ junk_vals R') (length vals + i) = getr R' (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros vals R' i Hi. rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite nth_map_seq by exact Hi. reflexivity.
  Qed.

  Lemma aclient_scr_mono : forall LB FF sp scr scr' a, 0 <= scr' <= scr -> aclient L ar LB FF sp scr a -> aclient L ar LB FF sp scr' a.
  Proof.
    intros LB FF sp scr scr' a Hs Hc. unfold aclient, aclient_g in *.
    destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc | right; left; split; [tauto | lia] | right; right; exact Hc].
  Qed.

  (* [comment removed for export] *)
  Definition has_window (kn : list kentry) : bool := existsb (kentry_eqb (KWr (SA (EVar 0) (-8388608)) 8388608)) kn.
  Lemma has_window_nth : forall kn, has_window kn = true -> exists i, nth_error kn i = Some (KWr (SA (EVar 0) (-8388608)) 8388608).
  Proof.
    intros kn H. unfold has_window in H. apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    apply In_nth_error in Hin. exact Hin.
  Qed.

  Lemma window_store_ok : forall vals ebs MV kn (z : Z) (m : nat),
    let E := Env (vals_ev vals) ebs in
    know_ok ASEGS E MV kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
    - 8388608 <= z -> z + Z.of_nat m <= 0 ->
    store_ok ASEGS MV (Z_to_bv 64 (bv_unsigned sp0 + z)) m = true.
  Proof.
    intros vals ebs MV kn z m E HK Hw P0 Hz Hm. destruct (has_window_nth kn Hw) as [i Hn].
    pose proof (kwr_store_ok ASEGS E MV kn i (EVar 0) (-8388608) 8388608 z m HK Hn ltac:(lia) ltac:(lia)) as W.
    unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W. exact W.
  Qed.

  Lemma segs_belowA : segs_below_b ASEGS 0x696000 = true.
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma store_ok_defined : forall (Mx : word -> option byte) a, 0x696000 <= a < 2 ^ 64 ->
    store_ok ASEGS Mx (Z_to_bv 64 a) 1 = true -> Mx (Z_to_bv 64 a) <> None.
  Proof.
    intros Mx a Ha Hs. cbn [store_ok] in Hs. unfold wview in Hs.
    destruct (Mx (Z_to_bv 64 a)) as [b|]; [discriminate|]. exfalso.
    rewrite (find_segment1_none_above ASEGS 0x696000 (bv_unsigned (Z_to_bv 64 a)) segs_belowA) in Hs by (rewrite u_small by lia; lia). discriminate.
  Qed.

  Lemma window_defined : forall vals ebs (H : word -> bool) M kn,
    let E := Env (vals_ev vals) ebs in
    know_ok ASEGS E (mrestrict H M) kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
    forall a, bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 -> M (Z_to_bv 64 a) <> None.
  Proof.
    intros vals ebs H M kn E HK Hw P0 a Ha. pose proof Hsp as Hsp'.
    pose proof (window_store_ok vals ebs _ kn (a - bv_unsigned sp0) 1 HK Hw P0 ltac:(lia) ltac:(lia)) as W.
    replace (bv_unsigned sp0 + (a - bv_unsigned sp0)) with a in W by ring.
    apply (store_ok_of_mrestrict ASEGS) in W. apply store_ok_defined; [lia | exact W].
  Qed.

  (* [comment removed for export] *)
  Lemma astack_ok_of_window : forall vals ebs (H : word -> bool) M kn so scr LB FF LK cr A V,
    let E := Env (vals_ev vals) ebs in
    know_ok ASEGS E (mrestrict H M) kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
    - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 -> 0 <= scr <= 4096 ->
    ri_inv HI LB FF LK cr A M V ->
    defined M (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0) ->
    astack_ok L ar M scr (bv_unsigned sp0 + so).
  Proof.
    intros vals ebs H M kn so scr LB FF LK cr A V E HK Hw P0 Hso Hsoal Hscr HH Hdef. pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    unfold astack_ok. rewrite (dla_sptop DL), (dla_segs DL).
    split; [rewrite Z.add_mod, Hal', Hsoal by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
    - intros d m Hd Hm. apply (store_ok_of_mrestrict ASEGS H).
      replace (bv_unsigned sp0 + so - scr + d) with (bv_unsigned sp0 + (so - scr + d)) by ring.
      apply (window_store_ok vals ebs _ kn _ m HK Hw P0); lia.
    - intros i Hi. destruct (Z_lt_le_dec (bv_unsigned sp0 + so + i) (bv_unsigned sp0)) as [Hlt|Hge].
      + apply (window_defined vals ebs H M kn HK Hw P0). lia.
      + replace (bv_unsigned sp0 + so + i) with (bv_unsigned sp0 + (so + i)) by ring. apply Hdef. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kn_blkA_ok : forall vals ebs Mx v n u,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals v = Z_to_bv 64 u -> vals_ev vals 0 = sp0 ->
    ablock_range L ar u n -> defined Mx u n ->
    know_ok ASEGS E Mx (kn_blkA v n).
  Proof.
    intros vals ebs Mx v n u E Pv P0 HBR Hdef. pose proof HBR as (_ & _ & B2 & B3 & _).
    pose proof (hzA_of_block_range _ _ HBR) as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
    assert (EA : bv_unsigned (edenot E (EVar v)) = u) by (cbn [edenot ev E]; rewrite Pv; apply u_small; lia).
    unfold kn_blkA, know_ok.
    apply Forall_cons. { cbn [kentry_ok]. rewrite EA. lia. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite EA. split; [lia | exact B2]. }
    apply Forall_cons.
    { cbn [kentry_ok]. split. { unfold flat, estart. cbn [a_base a_off]. rewrite EA. lia. }
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. rewrite EA.
      destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
      apply store_ok_of_all; [rewrite u_small by lia; lia|].
      intros x Hx. rewrite u_small in Hx by lia.
      specialize (Hdef (bv_unsigned x - u) ltac:(lia)). replace (u + (bv_unsigned x - u)) with (bv_unsigned x) in Hdef by lia.
      rewrite Z_to_bv_bv_unsigned in Hdef. unfold wview. destruct (Mx x); [discriminate | exfalso; apply Hdef; reflexivity]. }
    apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E]. rewrite P0.
                         change (ev E v) with (vals_ev vals v). rewrite Pv, u_small by lia. right. lia. }
    apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E].
                         change (ev E v) with (vals_ev vals v). rewrite Pv, !u_small by lia. lia. }
    apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  Lemma lzinv_of_inv : forall LB FF LK cr A M model,
    ri_inv HI LB FF LK cr A M (vml_of model) -> MInv A model -> m_halted model = None ->
    lzinv ASEGS (ahid A model) A model.
  Proof.
    intros LB FF LK cr A M model HH HM Hh.
    destruct (aiob_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
    unfold lzinv. split.
    { intros a Ha. unfold ahid, mkH in Ha. apply andb_prop in Ha as [Hl _].
      apply (find_segment1_none_above ASEGS 0x696000 _ segs_belowA).
      pose proof (LZ a Hl) as (Z1 & _). cbv zeta in Z1. rewrite (dla_img_hi DL) in Z1. exact Z1. }
    split; [unfold ahid; apply lazy_cover_mkH; intros r Hr; exact Hr|].
    split; [exact AWF|]. split; [exact HM | exact Hh].
  Qed.

  Lemma model_rt_halted : forall m m', model_rt m m' -> m_halted m' = m_halted m.
  Proof. intros m m' ->. destruct m; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CWA (LB : list (Z * Z)) (a : Z) : Prop :=
    in_block LB a \/ bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 \/ (exists lo hi, In (lo, hi) IMG_W_A /\ lo <= a < hi).

  Lemma img_w_client : forall lo hi, In (lo, hi) IMG_W_A -> exists lo' hi', In (lo', hi') IMG_CLIENT_A /\ lo' <= lo /\ hi <= hi' /\ 0x10000 <= lo /\ hi <= 0x696000.
  Proof.
    intros lo hi Hin. destruct (img_w_sub lo hi Hin) as (lo' & hi' & Hin' & H1 & H2). destruct (img_client_rng lo' hi' Hin') as (I1 & I2 & I3).
    exists lo', hi'. split; [exact Hin'|]. split; [exact H1|]. split; [exact H2|].
    unfold IMG_W_A in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma cwa_not_bshadow : forall LB FF LK cr A M V a, ri_inv HI LB FF LK cr A M V -> CWA LB a -> ~ block_shadow LB a.
  Proof.
    intros LB FF LK cr A M V a HH HC (b' & Hb' & X'). pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
    destruct (WB b' Hb') as ((Q0 & _ & Q16 & Q3 & Q4 & Q5) & _). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
    unfold in_shadow_of, S, SB in X'. rewrite (dla_sptop DL) in Q4. pose proof Hsp as HSP.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
    - destruct HB as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. lia.
    - lia.
    - destruct (img_w_client lo hi Hin) as (lo' & hi' & Hin' & H1 & H2 & H3 & H4). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  Lemma cwa_not_private : forall LB FF LK cr A M V a, ri_inv HI LB FF LK cr A M V -> 0 <= a < 2 ^ 64 -> CWA LB a -> ~ art_private L ar LB FF a.
  Proof.
    intros LB FF LK cr A M V a HH Ha HC [NC|[RO|BS]]; [| |exact (cwa_not_bshadow _ _ _ _ _ _ _ a HH HC BS)].
    - apply NC. unfold aclient. destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
      + left. exact HB.
      + right. left. rewrite (dla_sptop DL). pose proof Hsp. lia.
      + right. right. left. destruct (img_w_client lo hi Hin) as (lo' & hi' & Hin' & H1 & H2 & H3 & H4).
        rewrite (dla_img_lo DL), (dla_img_hi DL). split; [lia|]. apply (dla_client DL lo' hi' a Hin'). lia.
    - pose proof (dla_ro_img DL a RO) as RI. destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
      + destruct HB as (b & Hb & Hr). destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
        destruct (WF b Hb) as (HBR & _). apply hzA_of_block_range in HBR. unfold hzA in HBR. lia.
      + pose proof Hsp. lia.
      + exact (dla_ro DL lo hi a Hin Hr RO).
  Qed.

  (* [comment removed for export] *)
  Lemma ainv_frame : forall LB FF LK cr A M M' (model model' : Model),
    ri_inv HI LB FF LK cr A M (vml_of model) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ CWA LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    vml_of model' = vml_of model ->
    ri_inv HI LB FF LK cr A M' (vml_of model').
  Proof.
    intros LB FF LK cr A M M' model model' HH FR GR EV. rewrite EV.
    apply (aiob_frame _ _ _ _ _ HIok LB FF LK cr A M M' _ HH); [|exact GR].
    intros a Ha HP. apply FR; [exact Ha|]. intros HC. exact (cwa_not_private _ _ _ _ _ _ _ a HH Ha HC HP).
  Qed.

  Lemma sbm_vml : forall m m', same_but_materialized m m' -> vml_of m' = vml_of m.
  Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.
  Lemma sbm_fds : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
  Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. split; reflexivity. Qed.
  Lemma model_rt_fds : forall m m', model_rt m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
  Proof. intros m m' ->. destruct m; split; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma regions_writeA : forall vals ebs bls LB FF LK cr A M V,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    ri_inv HI LB FF LK cr A M V ->
    (forall i nb, find_nz i bls = Some nb -> sub_blockA LB (bv_unsigned (vals_ev vals i)) nb) ->
    regions_ok ASEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W_A [] E (CWA LB) (fun _ => True).
  Proof.
    intros vals ebs bls LB FF LK cr A M V E P0 HH Hbl. pose proof Hsp as Hsp'.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CWA. right. left. lia.
    - intros z Hz. right. exact I.
    - intros i nb Hf. pose proof (sub_blockA_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
      destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). split; [lia|]. intros z Hz. unfold CWA. left.
      exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4).
      split; [lia|]. split; [lia|]. intros a Ha. unfold CWA. right. right. exists lo, hi. auto.
    - intros lo hi [].
  Qed.

  (* [comment removed for export] *)
  Lemma block_frame : forall vals ebs bls LB FF LK cr A M M' (model : Model) log,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    ri_inv HI LB FF LK cr A M (vml_of model) ->
    (forall i nb, find_nz i bls = Some nb -> sub_blockA LB (bv_unsigned (vals_ev vals i)) nb) ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) bls [] IMG_W_A log = true ->
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ CWA LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ (forall a : word, M a <> None -> M' a <> None).
  Proof.
    intros vals ebs bls LB FF LK cr A M M' model log E P0 HH Hbl Hlog EQM EQH.
    pose proof (regions_writeA vals ebs bls LB FF LK cr A M _ P0 HH Hbl) as RG.
    split.
    - intros a Ha HC. destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [apply EQH; exact Hh|].
      assert (E1 : M' (Z_to_bv 64 a) = mrestrict (ahid A model) M' (Z_to_bv 64 a)) by (unfold mrestrict; rewrite Hh; reflexivity).
      rewrite E1, EQM.
      rewrite (mem_denot_frame_Z ASEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W_A _ (CWA LB) (fun _ => True) [] RG _ log a Hlog Ha HC).
      unfold mrestrict. rewrite Hh. reflexivity.
    - intros a Hd. destruct (ahid A model a) eqn:Hh; [rewrite (EQH a Hh); exact Hd|].
      assert (E1 : M' a = mrestrict (ahid A model) M' a) by (unfold mrestrict; rewrite Hh; reflexivity).
      rewrite E1, EQM. apply (mem_denot_grows E (mrestrict (ahid A model) M) log a). unfold mrestrict. rewrite Hh. exact Hd.
  Qed.

  (* [comment removed for export] *)
  Variable M0 : word -> option byte.
  (* [comment removed for export] *)
  Definition STKTOP : Z := Z.max (ar_sptop ar) (ar_stack_top ar).
  Lemma stksh_rng : forall LB FF LK cr A M V x, ri_inv HI LB FF LK cr A M V -> in_shadow_of (ahl_ceil ar) (STKTOP - ahl_ceil ar) x ->
    0x7fff8000 + 0xfffeff00000 <= x <= 0x7fff8000 + 0xfffffffffff /\ in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x.
  Proof.
    intros LB FF LK cr A M V x HH HS. pose proof Hsp as Hsp'.
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
    unfold in_shadow_of, S, SB, STKTOP in *. rewrite (dla_sptop DL) in *.
    assert (X2 : x <= 0x7fff8000 + (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) / 8).
    { destruct HS as [_ HS]. replace (bv_unsigned sp0 - 8388608 + (Z.max (bv_unsigned sp0) (ar_stack_top ar) - (bv_unsigned sp0 - 8388608)) - 1)
        with (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) in HS by ring. lia. }
    assert (D1 : (0x7fff80000000 - 8388608) / 8 <= (bv_unsigned sp0 - 8388608) / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
    replace (bv_unsigned sp0 - 8388608 + (2 ^ 47 - (bv_unsigned sp0 - 8388608)) - 1) with (2 ^ 47 - 1) by ring.
    change ((0x7fff80000000 - 8388608) / 8) with 0xfffeff00000 in D1. change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in D2 |- *. lia.
  Qed.

  Record dinv (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) : Prop := DINV {
    di_inv : ri_inv HI LB [] LK cr A M (vml_of model);
    di_minv : MInv A model;
    di_halt : m_halted model = None;
    di_above : forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a);
    di_stksh : forall x, in_shadow_of (ahl_ceil ar) (STKTOP - ahl_ceil ar) x -> byte_at M x 0;
    (* [comment removed for export] *)
    di_hish : forall x, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> byte_at M x 0
  }.

  Lemma dinv_lzinv : forall LB LK cr A M model, dinv LB LK cr A M model -> lzinv ASEGS (ahid A model) A model.
  Proof. intros LB LK cr A M model D. exact (lzinv_of_inv _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D) (di_minv _ _ _ _ _ _ D) (di_halt _ _ _ _ _ _ D)). Qed.

  (* [comment removed for export] *)
  Lemma stksh_not_cwa : forall LB FF LK cr A M V x, ri_inv HI LB FF LK cr A M V ->
    in_shadow_of (ahl_ceil ar) (STKTOP - ahl_ceil ar) x -> ~ CWA LB x.
  Proof.
    intros LB FF LK cr A M V x HH HS HC. pose proof Hsp as Hsp'. destruct (stksh_rng _ _ _ _ _ _ _ x HH HS) as ((X1 & X2) & _).
    destruct HC as [HB|[HSt|(lo & hi & Hin & Hr)]].
    - destruct HB as (b & Hb & Hr). destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
      destruct (WF b Hb) as (HBR & _). destruct HBR as (_ & _ & _ & _ & _ & (_ & AM & _)). unfold BIGSHADOW_LO, BIGSHADOW_HI in AM. lia.
    - lia.
    - destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
  Qed.

  Lemma hish_rng : forall x, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> 0x7fff8000 + 0xfffeff00000 <= x <= 0x7fff8000 + 0xfffffffffff.
  Proof.
    intros x HS. pose proof Hsp as Hsp'. unfold in_shadow_of, S, SB, ahl_ceil in *. rewrite (dla_sptop DL) in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    clear - HS Hsp'. lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma hish_not_cwa : forall LB FF LK cr A M V x, ri_inv HI LB FF LK cr A M V ->
    in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> ~ CWA LB x.
  Proof.
    intros LB FF LK cr A M V x HH HS HC. pose proof Hsp as Hsp'. destruct (hish_rng x HS) as (X1 & X2).
    destruct HC as [HB|[HSt|(lo & hi & Hin & Hr)]].
    - destruct HB as (b & Hb & Hr). destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
      destruct (WF b Hb) as (HBR & _). destruct HBR as (_ & _ & _ & _ & _ & (_ & AM & _)). unfold BIGSHADOW_LO, BIGSHADOW_HI in AM. lia.
    - lia.
    - destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dinv_frame : forall LB LK cr A M M' (model model' : Model),
    dinv LB LK cr A M model ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ CWA LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    vml_of model' = vml_of model -> MInv A model' -> m_halted model' = None ->
    dinv LB LK cr A M' model'.
  Proof.
    intros LB LK cr A M M' model model' D FR GR EV MI HL. pose proof Hsp as Hsp'. constructor.
    - exact (ainv_frame _ _ _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D) FR GR EV).
    - exact MI.
    - exact HL.
    - intros a Ha. rewrite <- (di_above _ _ _ _ _ _ D a Ha). apply FR; [lia|].
      intros [HB|[HSt|(lo & hi & Hin & Hr)]].
      + destruct HB as (b & Hb & Hr). destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D)) as (WF & _).
        destruct (WF b Hb) as (HBR & _). apply hzA_of_block_range in HBR. unfold hzA in HBR. lia.
      + lia.
      + destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
    - intros x Hx. unfold byte_at. rewrite FR; [exact (di_stksh _ _ _ _ _ _ D x Hx) | | exact (stksh_not_cwa _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx)].
      destruct (stksh_rng _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx) as (X & _). lia.
    - intros x Hx. unfold byte_at. rewrite FR; [exact (di_hish _ _ _ _ _ _ D x Hx) | | exact (hish_not_cwa _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx)].
      pose proof (hish_rng x Hx). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dinv_block : forall vals ebs bls LB LK cr A M M' (model model' : Model) log,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    dinv LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> sub_blockA LB (bv_unsigned (vals_ev vals i)) nb) ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) bls [] IMG_W_A log = true ->
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    lzinv ASEGS (ahid A model) A model' -> same_but_materialized model model' ->
    dinv LB LK cr A M' model'.
  Proof.
    intros vals ebs bls LB LK cr A M M' model model' log E P0 D Hbl Hlog EQM EQH HZ SBM.
    destruct (block_frame vals ebs bls LB [] LK cr A M M' model log P0 (di_inv _ _ _ _ _ _ D) Hbl Hlog EQM EQH) as (FR & GR).
    destruct HZ as (_ & _ & _ & MI & HL).
    exact (dinv_frame _ _ _ _ _ _ _ _ D FR GR (sbm_vml _ _ SBM) MI HL).
  Qed.

  (* [comment removed for export] *)
  Lemma minv_same_vm : forall A (m m' : Model), m_vm m' = m_vm m -> MInv A m -> MInv A m'.
  Proof.
    intros A m m' EV [I1 I2 I3 I4 I5].
    constructor; unfold m_vm_materialized, m_vm_lazy, m_vmmaps, eager_used, m_vmmaps, m_vm_lazy in *; rewrite EV; assumption.
  Qed.
  Lemma vml_same_vm : forall (m m' : Model), m_vm m' = m_vm m -> vml_of m' = vml_of m.
  Proof. intros m m' EV. unfold vml_of, m_vmmaps, m_vm_lazy. rewrite EV. reflexivity. Qed.
  Lemma with_fds_vm : forall f (m : Model), m_vm (with_fds f m) = m_vm m.
  Proof. intros f m. destruct m. reflexivity. Qed.
  Lemma with_fds_fs : forall f (m : Model), m_fs (with_fds f m) = m_fs m.
  Proof. intros f m. destruct m. reflexivity. Qed.
  Lemma with_fds_fds : forall f (m : Model), m_fds (with_fds f m) = f.
  Proof. intros f m. destruct m as [[t p] v i fsy pr l tm]. reflexivity. Qed.

  Lemma ahid_same_lazy : forall A (m m' : Model), m_vm_lazy m' = m_vm_lazy m -> ahid A m' = ahid A m.
  Proof. intros A m m' EL. unfold ahid. rewrite EL. reflexivity. Qed.
  Lemma ahid_sbm : forall A (m m' : Model), same_but_materialized m m' -> ahid A m' = ahid A m.
  Proof. intros A m m' SB. apply ahid_same_lazy. exact (sbm_lazy_eq _ _ SB). Qed.

  Lemma dinv_model : forall LB LK cr A M (model model' : Model),
    dinv LB LK cr A M model -> m_vm model' = m_vm model -> m_halted model' = None -> dinv LB LK cr A M model'.
  Proof.
    intros LB LK cr A M model model' D EV HL.
    apply (dinv_frame LB LK cr A M M model model' D); [reflexivity | auto | exact (vml_same_vm _ _ EV) | exact (minv_same_vm _ _ _ EV (di_minv _ _ _ _ _ _ D)) | exact HL].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).

  Lemma dinv_stack_defined : forall LB LK cr A M model, dinv LB LK cr A M model ->
    defined M (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Proof.
    intros LB LK cr A M model D i Hi.
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
    rewrite (di_above _ _ _ _ _ _ D) by lia. apply M0_def. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma dinv_call : forall LB LBc LB' LK LK' cr cr' A A' M M' (model model' : Model) sp scr,
    dinv LB LK cr A M model -> sp <= bv_unsigned sp0 ->
    (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBc [] sp scr a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    ri_inv HI LB' [] LK' cr' A' M' (vml_of model') -> MInv A' model' -> model_rt model model' ->
    dinv LB' LK' cr' A' M' model'.
  Proof.
    intros LB LBc LB' LK LK' cr cr' A A' M M' model model' sp scr D Hsp1 PR HH' MI RT. pose proof Hsp as Hsp'. constructor.
    - exact HH'.
    - exact MI.
    - rewrite (model_rt_halted _ _ RT). exact (di_halt _ _ _ _ _ _ D).
    - intros a Ha. rewrite <- (di_above _ _ _ _ _ _ D a Ha). apply PR; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
    - intros x Hx. destruct (stksh_rng _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx) as (X & XC).
      unfold byte_at. rewrite PR; [exact (di_stksh _ _ _ _ _ _ D x Hx) | lia | unfold aclient; right; right; right; right; left; exact XC].
    - intros x Hx. pose proof (hish_rng x Hx) as X.
      unfold byte_at. rewrite PR; [exact (di_hish _ _ _ _ _ _ D x Hx) | lia | unfold aclient; right; right; right; right; left; exact Hx].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma amalloc_site : forall vals ebs sr kn R M (model : Model) LB LK cr A n so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat ->
    vals_ev vals 0 = sp0 ->
    has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10 = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 -> acredit_ok L cr n ->
    getr R 4 = Z_to_bv 64 0x673d00 -> getr R 1 = Z_to_bv 64 ra -> (0 <= ra < 2 ^ 64)%Z -> (ra mod 2 = 0)%Z ->
    dinv LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model) A' (u : Z),
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       vals_ev vals' (length vals + 10) = Z_to_bv 64 u ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A' model') M') (kn_blkA (length vals + 10) n ++ keep_allocA so 4096 bls vbnd kn) ->
       dinv ((u, n) :: LB) LK (adebit L cr n) A' M' model' -> model_rt model model' -> incl A A' ->
       ablock_range L ar u n -> blocks_apart u n LB -> shadow_blk M' u n ->
       (forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x79818) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A n so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal R10 Hn Hcr R4 R1 Hra Hra2 DI Hbl Hvb HK0 CONT.
    set (FF := @nil fframe) in *.
    pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
    pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
    pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
    pose proof (aiob_malloc _ _ _ _ _ HIok fx R M model LB FF LK cr A n K) as MS.
    cbv zeta in MS. rewrite (dla_segs DL), (dla_malloc DL), (dla_tp DL) in MS. rewrite R1 in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) apply ret_ok_even. rewrite u_small by lia. exact Hra2.
    - (* [comment removed for export] *) rewrite R2, u_small by lia.
      eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia.
    - unfold amalloc_post. intros R' M' model' A' u HA HP HBR HAP HFA HDEF HSHB HPRES HRT HINC HMI' HH'.
      rewrite (dla_segs DL), R1. rewrite R2, u_small in HPRES by lia. destruct HPRES as (PR1 & PR2).
      assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (HA' : vals_ev (vals ++ junk_vals R') (length vals + 10) = Z_to_bv 64 u) by (rewrite vals_ev_junkA by lia; exact HA).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (CLI : forall a, aclient L ar LB FF (bv_unsigned sp0 + so) 4096 a -> aclient L ar LB FF (bv_unsigned sp0 + so) (hl_scr_malloc L) a)
        by (intros a; apply aclient_scr_mono; lia).
      apply (CONT R' M' model' A' u HL' HA'); try assumption.
      + (* [comment removed for export] *) apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
      + (* [comment removed for export] *) apply Forall_app. split.
        * eapply kn_blkA_ok; [exact HA' | exact P0' | exact HBR |].
          intros i Hi. unfold mrestrict.
          rewrite (vis_of_inv _ _ _ _ _ _ _ (u + i) HH'); [apply HDEF; exact Hi | destruct HBR as (B1 & _ & _ & _ & B5 & _); rewrite (dla_sptop DL) in B5; lia |].
          right. right. exists (u, n). split; [left; reflexivity | cbn [fst snd]; lia].
        * unfold keep_allocA.
          pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
          refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
                    (Env (vals_ev (vals ++ junk_vals R')) ebs)
                    (CPa LB FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) 4096)
                    _ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
          -- eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd LB LB ((u, n) :: LB) FF FF LK LK cr (adebit L cr n) A A' M M' model model');
               [exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
             ++ intros a Ha; exact Ha.
             ++ intros a (b & Hb & Hr). exists b. split; [right; exact Hb | exact Hr].
             ++ intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
             ++ intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
          -- intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; [exact Ha | apply CLI; exact HC].
          -- intros a HS. unfold SCa in HS. unfold mrestrict.
             rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
             destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_malloc L)) as [Hlo|Hhi].
             ++ rewrite PR1; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia |].
                unfold aclient. right. left. rewrite (dla_sptop DL). lia.
             ++ apply PR2. lia.
      + (* [comment removed for export] *)
        apply (dinv_call LB LB ((u, n) :: LB) LK LK cr (adebit L cr n) A A' M M' model model' (bv_unsigned sp0 + so) (hl_scr_malloc L) DI ltac:(lia)); assumption.
      + (* [comment removed for export] *) intros a Ha. apply PR1; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
      + intros a Ha Hb. apply PR1; [exact Ha | left; exact Hb].
      + intros lo hi a Hin Ha. assert (0 <= a < 2 ^ 64).
        { destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3). lia. }
        apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
        split; [destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin Ha)].
  Qed.
  Lemma in_lb_remove_in : forall u (LB : list (Z * Z)) b, In b (lb_remove u LB) -> In b LB.
  Proof.
    intros u LB b. induction LB as [|c LB' IH]; [intros []|]. cbn [lb_remove].
    destruct (Z.eqb (fst c) u); [intros H; right; exact H|]. intros [<-|H]; [left; reflexivity | right; apply IH; exact H].
  Qed.
  Lemma in_block_remove : forall u LB a, in_block (lb_remove u LB) a -> in_block LB a.
  Proof. intros u LB a (b & Hb & Hr). exists b. split; [exact (in_lb_remove_in u LB b Hb) | exact Hr]. Qed.

  (* [comment removed for export] *)
  Lemma afree_site : forall vals ebs sr kn R M (model : Model) LB LK cr A (u n : Z) so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat ->
    vals_ev vals 0 = sp0 ->
    has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    In (u, n) LB -> getr R 10 = Z_to_bv 64 u ->
    getr R 4 = Z_to_bv 64 0x673d00 -> getr R 1 = Z_to_bv 64 ra -> (0 <= ra < 2 ^ 64)%Z -> (ra mod 2 = 0)%Z ->
    dinv LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA (lb_remove u LB) (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model) A',
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A' model') M') (keep_allocA so 4096 bls vbnd kn) ->
       dinv (lb_remove u LB) LK cr A' M' model' -> model_rt model model' -> incl A A' ->
       (forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block (lb_remove u LB) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x79814) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A u n so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal Hin R10 R4 R1 Hra Hra2 DI Hbl Hvb HK0 CONT.
    set (FF := @nil fframe) in *.
    pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
    pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
    pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
    pose proof (aiob_free _ _ _ _ _ HIok fx R M model LB FF LK cr A u n K) as MS.
    cbv zeta in MS. rewrite (dla_segs DL), (dla_free DL), (dla_tp DL) in MS. rewrite R1 in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) apply ret_ok_even. rewrite u_small by lia. exact Hra2.
    - (* [comment removed for export] *) rewrite R2, u_small by lia.
      eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia.
    - intros R' M' model' A' HP HPRES HRT HINC HMI' HH'.
      rewrite R2, u_small in HPRES by lia. destruct HPRES as (PR1 & PR2).
      assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (CLI : forall a, aclient L ar (lb_remove u LB) FF (bv_unsigned sp0 + so) 4096 a ->
                              aclient L ar (lb_remove u LB) FF (bv_unsigned sp0 + so) (hl_scr_free L) a)
        by (intros a; apply aclient_scr_mono; lia).
      apply (CONT R' M' model' A' HL'); try assumption.
      + (* [comment removed for export] *) apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
      + (* [comment removed for export] *) unfold keep_allocA.
        pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R')) ebs)
                  (CPa (lb_remove u LB) FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) 4096)
                  _ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
        * eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd (lb_remove u LB) LB (lb_remove u LB) FF FF LK LK cr cr A A' M M' model model');
            [exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
          -- intros a Ha. exact (in_block_remove u LB a Ha).
          -- intros a Ha; exact Ha.
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
        * intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; [exact Ha | apply CLI; exact HC].
        * intros a HS. unfold SCa in HS. unfold mrestrict.
          rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
          destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_free L)) as [Hlo|Hhi].
          -- rewrite PR1; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia |].
             unfold aclient. right. left. rewrite (dla_sptop DL). lia.
          -- apply PR2. lia.
      + (* [comment removed for export] *)
        apply (dinv_call LB (lb_remove u LB) (lb_remove u LB) LK LK cr cr A A' M M' model model' (bv_unsigned sp0 + so) (hl_scr_free L) DI ltac:(lia)); assumption.
      + (* [comment removed for export] *) intros a Ha. apply PR1; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
      + intros a Ha Hb. apply PR1; [exact Ha | left; exact Hb].
      + intros lo hi a Hin' Ha. assert (0 <= a < 2 ^ 64).
        { destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3). lia. }
        apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
        split; [destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin' Ha)].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.

  Lemma rdn_of_bytes_at : forall (Mx : word -> option byte) n (a : word) bs,
    length bs = n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall j, (j < n)%nat -> Mx (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
    rdn ASEGS Mx a n = Some bs.
  Proof.
    intros Mx n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
    - destruct bs; [reflexivity | cbn in Hlen; lia].
    - destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen. cbn [rdn].
      pose proof (Hpt 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [nth] in H0.
      rewrite H0.
      destruct n as [|n']; [destruct bs'; [reflexivity | cbn in Hlen; lia]|].
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      rewrite (IH (a + 1)%bv bs'); [reflexivity | lia | rewrite Hu1; lia |].
      intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (Datatypes.S j)) by lia.
      exact (Hpt (Datatypes.S j) ltac:(lia)).
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma aacc_of_blkA : forall M u n p m, shadow_blk M u n -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + m <= u + n -> aacc M p m.
  Proof.
    intros M u n p m [SZ SP] U8 U0 H1 H2 a Ha. unfold shadow_zero, byte_at in SZ, SP |- *.
    assert (E : S a = S u + (a / 8 - u / 8)) by (unfold S; lia).
    destruct (Z_lt_le_dec (a / 8 - u / 8) (n / 8)) as [LT|GE].
    - left. rewrite E. apply SZ. lia.
    - right. exists (n mod 8). assert (NZ : n mod 8 <> 0) by lia. assert (G : a / 8 - u / 8 = n / 8) by lia.
      split; [rewrite E, G; apply SP; exact NZ | lia].
  Qed.
  Lemma u16_u8 : forall u, u mod 16 = 0 -> u mod 8 = 0.
  Proof. intros u H. lia. Qed.
  Lemma S_mono : forall a b, a <= b -> S a <= S b.
  Proof. intros a b H. unfold S. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma src_blk_aacc : forall LB FF LK cr A M V (As caps src n : Z),
    ri_inv HI LB FF LK cr A M V -> In (As, caps) LB -> As <= src -> src + n <= As + caps -> aacc M src n.
  Proof.
    intros LB FF LK cr A M V As caps src n HH Hin H1 H2.
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
    destruct (WF (As, caps) Hin) as (HBR & _ & HSB & _). cbn [fst snd] in HBR, HSB. destruct HBR as (B1 & _ & B3 & _).
    apply (aacc_of_blkA M As caps src n HSB (u16_u8 _ B3)); lia.
  Qed.
  (* [comment removed for export] *)
  Lemma src_blk_app_rng : forall LB FF LK cr A M V (As caps src n : Z),
    ri_inv HI LB FF LK cr A M V -> In (As, caps) LB -> As <= src -> src + n <= As + caps -> app_rng ar src n.
  Proof.
    intros LB FF LK cr A M V As caps src n HH Hin H1 H2.
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
    destruct (WF (As, caps) Hin) as (HBR & _). cbn [fst snd] in HBR. destruct HBR as (B1 & _ & _ & _ & B5 & (_ & BAM & _)).
    unfold app_rng. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
  Qed.
  Lemma src_stage_app_rng : forall (src n : Z), 0x662290 <= src -> src + n <= 0x672290 -> app_rng ar src n.
  Proof. intros src n H1 H2. pose proof Hsp. unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. rewrite (dla_sptop DL). lia. Qed.
  (* [comment removed for export] *)
  Lemma src_stage_aacc : forall LB FF LK cr A M V (src n : Z),
    ri_inv HI LB FF LK cr A M V -> 0x662290 <= src -> src + n <= 0x672290 -> aacc M src n.
  Proof.
    intros LB FF LK cr A M V src n HH H1 H2 a Ha. left.
    destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH src n) as (Z0 & _).
    - rewrite (dla_img_lo DL). lia.
    - rewrite (dla_img_hi DL). lia.
    - lia.
    - rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - apply Z0. unfold in_shadow_of. split; apply S_mono; lia.
  Qed.

  Lemma aclient_remove : forall u LB FF sp scr a, aclient L ar (lb_remove u LB) FF sp scr a -> aclient L ar LB FF sp scr a.
  Proof.
    intros u LB FF sp scr a Hc. unfold aclient, aclient_g in *.
    destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]; [left; exact (in_block_remove u LB a Hc) | tauto | tauto | tauto | tauto | tauto |].
    right. right. right. right. right. right. destruct Hc as (b & Hb & Hr). exists b. split; [exact (in_lb_remove_in u LB b Hb) | exact Hr].
  Qed.

  Lemma ablock_range_prefix : forall u n nb, ablock_range L ar u n -> 0 < nb <= n -> ablock_range L ar u nb.
  Proof. intros u n nb (B1 & B2 & B3 & B4 & B5 & (B6 & B7 & B8)) Hnb. unfold ablock_range, app_mem. repeat split; lia. Qed.

  (* [comment removed for export] *)
  Lemma kn_blkA_of_inv : forall vals ebs LB LK cr A M (model : Model) v (u cap nb : Z),
    let E := Env (vals_ev vals) ebs in
    dinv LB LK cr A M model -> In (u, cap) LB -> 0 < nb <= cap ->
    vals_ev vals v = Z_to_bv 64 u -> vals_ev vals 0 = sp0 ->
    know_ok ASEGS E (mrestrict (ahid A model) M) (kn_blkA v nb).
  Proof.
    intros vals ebs LB LK cr A M model v u cap nb E D Hin Hnb Pv P0.
    pose proof (di_inv _ _ _ _ _ _ D) as HH.
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
    destruct (WF (u, cap) Hin) as (HBR & HDEF & _). cbn [fst snd] in HBR, HDEF.
    eapply kn_blkA_ok; [exact Pv | exact P0 | exact (ablock_range_prefix _ _ _ HBR Hnb) |].
    intros i Hi. unfold mrestrict.
    rewrite (vis_of_inv _ _ _ _ _ _ _ (u + i) HH); [apply HDEF; lia | destruct HBR as (B1 & _ & _ & _ & B5 & _); rewrite (dla_sptop DL) in B5; pose proof Hsp; lia |].
    right. right. exists (u, cap). split; [exact Hin | cbn [fst snd]; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma amemcpy_site : forall vals ebs sr kn R M (model : Model) LB LK cr A (Ad capd dst src n : Z) (bs : list byte) so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat ->
    vals_ev vals 0 = sp0 ->
    has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10 = Z_to_bv 64 dst -> getr R 11 = Z_to_bv 64 src -> getr R 12 = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 ->
    getr R 4 = Z_to_bv 64 0x673d00 -> getr R 1 = Z_to_bv 64 ra -> (0 <= ra < 2 ^ 64)%Z -> (ra mod 2 = 0)%Z ->
    dinv LB LK cr A M model ->
    In (Ad, capd) LB -> Ad <= dst -> dst + n <= Ad + capd ->
    aacc M src n -> 0 <= src -> src + n <= 2 ^ 47 -> app_rng ar src n ->
    (forall i, 0 <= i < n -> 0x10000 <= src + i < 0x696000 \/ in_block LB (src + i)) ->      (* [comment removed for export] *)
    rdn ASEGS M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
    (dst + n <= src \/ src + n <= dst) ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA (lb_remove Ad LB) (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model),
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A model') M') (keep_allocA so 4096 bls vbnd kn) ->
       dinv LB LK cr A M' model' -> model_rt model model' ->
       rdn ASEGS M' (Z_to_bv 64 dst) (Z.to_nat n) = Some bs ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> ~ (dst <= a < dst + n) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x77c90) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A Ad capd dst src n bs so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal R10 R11 R12 Hn R4 R1 Hra Hra2 DI Hin Hd1 Hd2 Hacc Hs0 Hs1 Happ Hsrc Hrd Hdj Hbl Hvb HK0 CONT.
    set (FF := @nil fframe) in *.
    pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
    pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
    pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
    destruct (WF (Ad, capd) Hin) as (HBR & HDEF & HSB & _ & HAP & _). cbn [fst snd] in HBR, HDEF, HSB, HAP.
    pose proof (hzA_of_block_range _ _ HBR) as (Y1 & Y2 & Y3). pose proof HBR as (_ & _ & B3 & _ & _ & (_ & BAM & _)).
    assert (INB : forall i, 0 <= i < n -> in_block LB (dst + i)).
    { intros i Hi. exists (Ad, capd). split; [exact Hin | cbn [fst snd]; lia]. }
    pose proof (aic_memcpy_libc _ _ _ _ _ ICok fx R M model LB FF LK cr A dst src n bs K) as MS.
    unfold amemcpy_libc_spec, amemcpy_spec_at in MS. rewrite (dla_segs DL), (dla_memcpy DL) in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) unfold amem_pre. rewrite (dla_tp DL), (dla_segs DL), R1, R2, u_small by lia.
      split; [exact HH|]. split; [exact Hh|]. split; [exact HMI|]. split; [exact R10|]. split; [exact R12|]. split; [lia|].
      split; [exact R4|]. split; [apply ret_ok_even; rewrite u_small by lia; exact Hra2|].
      split; [eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia|].
      split; [apply (aacc_of_blkA M Ad capd dst n HSB (u16_u8 _ B3)); lia|].
      split; [intros i Hi; left; exact (INB i Hi)|].
      split; [|split; [exact HK0 | unfold app_rng; rewrite (dla_sptop DL); lia]].                      (* [comment removed for export] *)
      intros i m Hi Hm. destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
      apply store_ok_of_all; [rewrite u_small by lia; lia|].
      intros x Hx. rewrite u_small in Hx by lia.
      specialize (HDEF (bv_unsigned x - Ad) ltac:(lia)). replace (Ad + (bv_unsigned x - Ad)) with (bv_unsigned x) in HDEF by lia.
      rewrite Z_to_bv_bv_unsigned in HDEF. unfold wview. destruct (M x); [discriminate | exfalso; apply HDEF; reflexivity].
    - split; assumption.
    - intros i Hi. destruct (Hsrc i Hi) as [X|X]; [left; rewrite (dla_img_lo DL), (dla_img_hi DL); exact X | right; left; exact X].     (* [comment removed for export] *)
    - intros _. exact Hdj.
    - (* [comment removed for export] *) unfold amem_post. cbv zeta. intros R' M' model' HA HP HNEW HPRES HSCR HRT HMI' HH'.
      rewrite (dla_segs DL), R1. rewrite R2, u_small in HPRES, HSCR by lia.
      assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      (* [comment removed for export] *)
      assert (NDST : forall a, aclient L ar (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 a -> ~ (dst <= a < dst + n)).
      { intros a Hc Hr. unfold aclient, aclient_g in Hc. rewrite (dla_img_lo DL), (dla_img_hi DL), (dla_sptop DL) in Hc.
        destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
        - destruct Hc as (b & Hb & Hbr). destruct (HAP b Hb) as [Q|Q]; lia.
        - lia.
        - lia.
        - destruct Hc as (f & [] & _).
        - unfold in_shadow_of, S, SB in Hc. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAM.
          assert (D0 : 0 <= (bv_unsigned sp0 - 8388608) / 8) by (apply Z.div_pos; lia).
          replace (bv_unsigned sp0 - 8388608 + (2 ^ 47 - (bv_unsigned sp0 - 8388608)) - 1) with (2 ^ 47 - 1) in Hc by ring.
          change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in Hc. lia.
        - destruct Hc as (f & [] & _).
        - destruct Hc as (b & Hb & Hbr). pose proof (in_lb_remove_in _ _ _ Hb) as Hb'.
          destruct (WF b Hb') as ((C1 & _ & _ & C4 & C5 & (_ & _ & C8)) & _).
          unfold in_shadow_of, S, SB in Hbr. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAM.
          assert (D0 : 0 <= fst b / 8) by (apply Z.div_pos; lia).
          assert (D2 : (fst b + snd b - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
          change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in D2. lia. }
      assert (PR1 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha Hc. apply HPRES; [exact Ha | | exact (NDST a Hc)].
        apply (aclient_scr_mono _ _ _ 4096 (hl_scr_mem L)); [lia|]. exact (aclient_remove Ad LB FF _ _ a Hc). }
      apply (CONT R' M' model' HL'); try assumption.
      + (* [comment removed for export] *) apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
      + (* [comment removed for export] *) unfold keep_allocA.
        pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R')) ebs)
                  (CPa (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A model')) (SCa (bv_unsigned sp0 + so) 4096)
                  _ (mrestrict (ahid A model) M) (mrestrict (ahid A model') M') _ _ kn HK1).
        * eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd (lb_remove Ad LB) LB LB FF FF LK LK cr cr A A M M' model model');
            [exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
          -- intros a Ha. exact (in_block_remove Ad LB a Ha).
          -- intros a Ha. exact (in_block_remove Ad LB a Ha).
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
        * intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; assumption.
        * intros a HS. unfold SCa in HS. unfold mrestrict.
          rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
          destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_mem L)) as [Hlo|Hhi].
          -- rewrite HPRES; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia | | lia].
             unfold aclient. right. left. rewrite (dla_sptop DL). lia.
          -- apply HSCR. lia.
      + (* [comment removed for export] *)
        apply (dinv_call LB (lb_remove Ad LB) LB LK LK cr cr A A M M' model model' (bv_unsigned sp0 + so) 4096 DI ltac:(lia)); assumption.
      + (* [comment removed for export] *)
        pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
        apply rdn_of_bytes_at; [exact Hlen | rewrite u_small by lia; lia |].
        intros j Hj. rewrite u_small by lia.
        destruct (HNEW (Z.of_nat j) ltac:(lia)) as (v & (Hnth & Hv) & Hb). rewrite Nat2Z.id in Hnth.
        unfold byte_at in Hb. rewrite Hb. f_equal. symmetry. apply nth_error_nth. exact Hnth.
      + (* [comment removed for export] *) intros a Ha Hb Hnd. apply HPRES; [exact Ha | left; exact Hb | exact Hnd].
      + intros lo hi a Hin' Ha. assert (0 <= a < 2 ^ 64).
        { destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3). lia. }
        apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
        split; [destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin' Ha)].
  Qed.
End DrvLayoutA.
End FPX_1.

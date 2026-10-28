(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec StoreOk Frame MallocDefs AgentLib MmapSim ShapeAlg Spec
  HUEnframeBase HUTargetPre HUWorld HUWorldK HUReadBase HUReadStage HUTargetFull.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require LedgerCfg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import H0Lim.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hreserved_top : reserved_top (segments_reserved RSEGS) = 0x354000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma vm_exact_ledger_inv : forall (VM : VmMaps) (sp0 mb bw B : word) (nb : Z),
  vm_reserved VM = segments_reserved RSEGS -> LIM <= vm_limit VM -> vm_init_sp VM = sp0 ->     (* [comment removed for export] *)
  0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000 ->
  vm_exact VM sp0 mb bw B nb ->
  0 < nb < 2 ^ 62 -> nb mod 4096 = 0 ->
  0 < bv_unsigned mb -> bv_unsigned mb mod 4096 = 0 -> bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608 ->
  LedgerCfg.ledger_inv (segments_reserved RSEGS) LIM 2 (nb + 8192) VM.
Proof.
  intros VM sp0 mb bw B nb Vres Vlim Visp Hsp (Xm & Xn & Xs & Xb & Xbw & Xr & Xal & Xpos & Xtop & Xrf & Xdj & Xbrk) Hnb Hnbal Hmb Hmbal Hmbtop.
  assert (Un : bv_unsigned (Z_to_bv 64 nb) = nb) by (apply LedgerCfg.u64_lit; lia).
  assert (U8 : bv_unsigned (Z_to_bv 64 8192) = 8192) by (apply LedgerCfg.u64_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 4096) = 4096) by (apply LedgerCfg.u64_lit; lia).
  assert (Ub : bv_unsigned (Z_to_bv 64 (bv_unsigned mb + 8192)) = bv_unsigned mb + 8192) by (apply LedgerCfg.u64_lit; lia).
  assert (Atop : alloc_top VM = bv_unsigned sp0 - 8388608) by (unfold alloc_top, stack_max_size; rewrite Visp; reflexivity).
  constructor; rewrite ?Xm, ?Xn, ?Xs, ?Xb, ?Atop.
  - exact Vres.
  - exact Vlim.
  - rewrite Visp. unfold sp_window_lo. lia.
  - rewrite Visp. unfold sp_window_hi. lia.
  - repeat constructor; unfold LedgerCfg.e_sz; cbn [snd]; lia.
  - repeat constructor; unfold LedgerCfg.e_sz, LedgerCfg.e_lo, page_size; cbn [fst snd]; rewrite ?Un, ?U8; try assumption; reflexivity.
  - repeat constructor; unfold LedgerCfg.e_hi, LedgerCfg.e_sz, LedgerCfg.e_lo; cbn [fst snd]; rewrite ?Un, ?U8; lia.
  - constructor; [|constructor; [|constructor]].
    + apply LedgerCfg.region_free_iff. exact Xrf.
    + apply LedgerCfg.region_free_iff. apply LedgerCfg.region_free_above_top. exact Xr.
  - cbn [LedgerCfg.pw_disj]. split; [|split; [constructor | exact I]].
    constructor; [|constructor]. unfold LedgerCfg.e_disj, LedgerCfg.e_hi, LedgerCfg.e_sz, LedgerCfg.e_lo. cbn [fst snd]. rewrite Un, U8. lia.
  - cbn [length]. lia.
  - rewrite !LedgerCfg.live_bytes_cons. unfold LedgerCfg.e_sz. cbn [snd live_bytes]. rewrite Un, U8. lia.
  - constructor; [|constructor]. split.
    + unfold LedgerCfg.e_sz. cbn [snd]. lia.
    + exists (mb, Z_to_bv 64 8192). split; [right; left; reflexivity|].
      unfold LedgerCfg.e_inside, LedgerCfg.e_hi, LedgerCfg.e_sz, LedgerCfg.e_lo. cbn [fst snd]. rewrite U4, U8. lia.
  - rewrite Ub. lia.
  - rewrite Ub. unfold page_size. rewrite Z.add_mod, Hmbal by lia. reflexivity.
  - rewrite Ub. lia.
  - exact Xr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxSpec FxInstr FxState FxRel FxHandoff.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HoBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
Definition PC_TARGET : Z := 0xe1c8c.

(* [comment removed for export] *)
Definition T_STK : int := 1%uint63.   (* [comment removed for export] *)
Definition T_BRK : int := 2%uint63.   (* [comment removed for export] *)
Definition T_BUF : int := 3%uint63.   (* [comment removed for export] *)
Definition T_CAN : int := 4%uint63.   (* [comment removed for export] *)
Definition T_SEC : int := 5%uint63.   (* [comment removed for export] *)
Definition T_TID : int := 6%uint63.   (* [comment removed for export] *)
Definition T_ERR : int := 7%uint63.   (* [comment removed for export] *)
Definition T_REG (r : Z) : int := ioz (100 + r).   (* [comment removed for export] *)
Definition T_UID : int := 200%uint63.  (* [comment removed for export] *)
Definition T_GID : int := 201%uint63.

Definition rho_of (sp0 mb B : word) (can sec tid err : Z) (R : bvmap 5 word) (uw gw : word) : int -> word := fun t =>
  if (t =? 1)%uint63 then Z_to_bv 64 (bv_unsigned sp0 - 8388608)
  else if (t =? 2)%uint63 then mb else if (t =? 3)%uint63 then B
  else if (t =? 4)%uint63 then Z_to_bv 64 can else if (t =? 5)%uint63 then Z_to_bv 64 sec
  else if (t =? 6)%uint63 then Z_to_bv 64 tid else if (t =? 7)%uint63 then Z_to_bv 64 err
  else if ((100 <=? t) && (t <? 132))%uint63 then getr R (Z_to_bv 5 (to_Z t - 100))
  else if (t =? 200)%uint63 then uw else if (t =? 201)%uint63 then gw
  else Z_to_bv 64 0.

(* [comment removed for export] *)
Definition facts_regs_opaque : list hfact :=
  map (fun r => HReg (ioz r) (FV (T_REG r) w_zero)) [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31].
Definition facts_regs (bufoff : Z) : list hfact :=
  [ hreg 1 0 0xe1b18; hreg 2 T_STK (8388608 - 128); hreg 3 0 0x10800; hreg 4 0 0x331ae8;
    hreg 8 T_BUF (bufoff + 2); hreg 9 T_BUF bufoff; hreg 10 T_BUF (bufoff + 2); hreg 22 0 STAGE; hreg 23 0 0 ].

(* [comment removed for export] *)
Definition facts_frame : list hfact :=
  [ hcell T_STK (8388608 - 56) 8 0x2b1158; hval T_STK (8388608 - 64) T_STK (8388608 + 8); hcell T_STK (8388608 - 72) 8 2;
    hcell T_STK (8388608 - 80) 8 0xe1984; hval T_STK (8388608 - 88) T_STK (8388608 + 32);
    hcell T_STK (8388608 - 96) 8 0; hcell T_STK (8388608 - 104) 8 0; hcell T_STK (8388608 - 112) 8 0; hcell T_STK (8388608 - 120) 8 0;
    hcell 0 0x351d78 1 1;
    hwr T_STK 0 8388608 ].

(* [comment removed for export] *)
Definition facts_img : list hfact := map (fun iv => hclear (fst iv) (snd iv)) img_clear_ivs.

(* [comment removed for export] *)
Definition facts_libc : list hfact :=
  [ hcell 0 0x331a20 8 0x331a20; hopq 0 0x351b28 T_CAN; hcell 0 0x351da8 8 4096;
    hbytesf 0 0x331a40 4 T_TID; hbytesf 0 0x331a44 4 T_ERR ].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition facts_ctx0 : list hfact :=
  [ hopq 0 ctx_secret T_SEC; hcell 0 ctx_init_done 4 1; hcell 0 ctx_mmap_counter 4 1; hcell 0 ctx_free_meta_head 8 0;
    hval 0 ctx_avail_meta T_BRK (4096 + 64); hcell 0 ctx_avail_meta_count 8 100; hcell 0 ctx_avail_meta_area_count 8 0;
    hcell 0 ctx_meta_alloc_shift 8 0; hval 0 ctx_meta_area_head T_BRK 4096; hval 0 ctx_meta_area_tail T_BRK 4096;
    hval 0 ctx_avail_meta_areas T_BRK 8192; hval 0 (ctx_active 44) T_BRK (4096 + 24); hcell 0 (ctx_usage 44) 8 1; hcell 0 ctx_seq 1 1;
    hval 0 ctx_brk T_BRK 8192 ].
Definition facts_area0 : list hfact :=
  [ hopq T_BRK 4096 T_SEC; hcell T_BRK (4096 + 8) 8 0; hcell T_BRK (4096 + 16) 8 101;
    hval T_BRK (4096 + 24) T_BRK (4096 + 24); hval T_BRK (4096 + 32) T_BRK (4096 + 24); hval T_BRK (4096 + 40) T_BUF 0;
    hcell T_BRK (4096 + 48) 8 0; hcell T_BRK (4096 + 56) 8 W64K; hzero T_BRK (4096 + 64) (4096 - 64); hwr T_BRK 4096 4096 ].
Definition facts_grp0 : list hfact :=
  [ hval T_BUF 0 T_BRK (4096 + 24); hcell T_BUF 8 1 0; hzero T_BUF 9 4; hzero T_BUF 69628 4; hwr T_BUF 0 69632 ].
(* [comment removed for export] *)
Definition facts_slot0 : list hfact :=
  [ hcell T_BUF 13 1 224; hcell T_BUF 14 2 1; hzero T_BUF 16 12; hcell T_BUF 28 1 0; hcell T_BUF 29 1 160; hcell T_BUF 30 2 1;
    hcell T_BUF 65568 1 0; hzero T_BUF 65569 4054; hcell T_BUF 69623 1 0; hcell T_BUF 69624 4 4060 ].

(* [comment removed for export] *)
Definition facts_geom (nb : Z) : list hfact :=
  [ hregion T_STK 0 8388608 4; hregion T_BRK 0 8192 12; hregion T_BRK 4096 8192 12; hregion T_BUF 0 nb 12;
    hdisj 0 0x10000 0x354000 T_STK 0 8388608; hdisj 0 0x10000 0x354000 T_BRK 0 8192; hdisj 0 0x10000 0x354000 T_BRK 4096 8192;
    hdisj 0 0x10000 0x354000 T_BUF 0 nb; hdisj T_STK 0 8388608 T_BRK 0 8192; hdisj T_STK 0 8388608 T_BRK 4096 8192;
    hdisj T_STK 0 8388608 T_BUF 0 nb; hdisj T_BRK 0 8192 T_BUF 0 nb; hdisj T_BRK 4096 8192 T_BUF 0 nb ].

Definition facts_k0 : list hfact :=
  facts_regs_opaque ++ facts_regs 32 ++ facts_frame ++ facts_img ++ facts_libc ++ facts_ctx0 ++ facts_area0 ++ facts_grp0 ++ facts_geom 69632.
Definition facts_k0b : list hfact := facts_k0 ++ facts_slot0.     (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zclosed := vm_compute; split; [discriminate | reflexivity].
Ltac zside := first [reflexivity | lia | zclosed].

(* [comment removed for export] *)
Lemma byte_rdn1 : forall (M : word -> option byte) (a v : Z), 0 <= v < 2 ^ 64 ->
  M (Z_to_bv 64 a) = Some (Z_to_bv 8 v) -> rdn RSEGS M (Z_to_bv 64 a) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 v)).
Proof.
  intros M a v Hv H. rewrite SeqExec.N_to_le_bytes_1_small, (AgentLib.u64_lit v) by exact Hv. apply HUEnframeBase.rdn1_of_mem. exact H.
Qed.

Section Common.
  Variables (sp0 mb B : word) (can sec tid err : Z) (R : bvmap 5 word) (uw gw : word) (pc : word) (M : word -> option byte).
  Notation rho := (rho_of sp0 mb B can sec tid err R uw gw).
  Notation ms := (mkst R pc M (seg_rom RSEGS)).

  Lemma rho0 : rho 0%uint63 = Z_to_bv 64 0. Proof. reflexivity. Qed.
  Lemma rho1 : rho T_STK = Z_to_bv 64 (bv_unsigned sp0 - 8388608). Proof. reflexivity. Qed.
  Lemma rho2 : rho T_BRK = Z_to_bv 64 (bv_unsigned mb). Proof. cbn. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  Lemma rho3 : rho T_BUF = Z_to_bv 64 (bv_unsigned B). Proof. cbn. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  Lemma rho4 : rho T_CAN = Z_to_bv 64 can. Proof. reflexivity. Qed.
  Lemma rho5 : rho T_SEC = Z_to_bv 64 sec. Proof. reflexivity. Qed.
  Lemma rho6 : rho T_TID = Z_to_bv 64 tid. Proof. reflexivity. Qed.
  Lemma rho7 : rho T_ERR = Z_to_bv 64 err. Proof. reflexivity. Qed.

  Lemma regs_opaque_ok : Forall (hholds RSEGS rho ms) facts_regs_opaque.
  Proof.
    unfold facts_regs_opaque. cbn [map].
    repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    all: lazymatch goal with |- hholds _ _ _ (HReg (ioz ?r) _) =>
           change (ioz r) with (ireg (Z_to_bv 5 r)); apply hreg_opaque_ok; [vm_compute; reflexivity | reflexivity] end.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_ok : main_frame (bv_unsigned sp0) M -> stack_writableZ M (bv_unsigned sp0) ->
    Forall (hholds RSEGS rho ms) facts_frame.
  Proof.
    intros [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10] SW. unfold facts_frame.
    repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - eapply (hcell_ok RSEGS rho R pc M); [exact rho1 | | | | | exact F1]; zside.
    - eapply (hval_ok RSEGS rho R pc M); [exact rho1 | | | exact rho1 | | | exact F2]; zside.
    - eapply (hcell_ok RSEGS rho R pc M); [exact rho1 | | | | | exact F3]; zside.
    - eapply (hcell_ok RSEGS rho R pc M); [exact rho1 | | | | | exact F4]; zside.
    - eapply (hval_ok RSEGS rho R pc M); [exact rho1 | | | exact rho1 | | | exact F5]; zside.
    - eapply (hcell_ok RSEGS rho R pc M); [exact rho1 | | | | | exact F6]; zside.
    - eapply (hcell_ok RSEGS rho R pc M); [exact rho1 | | | | | exact F7]; zside.
    - eapply (hcell_ok RSEGS rho R pc M); [exact rho1 | | | | | exact F8]; zside.
    - eapply (hcell_ok RSEGS rho R pc M); [exact rho1 | | | | | exact F9]; zside.
    - eapply (hcell_ok RSEGS rho R pc M); [exact rho0 | | | | | exact F10]; zside.
    - eapply (hwr_ok_store RSEGS rho R pc M); [exact rho1 | reflexivity | zclosed | zclosed |].
      intros i Hi. rewrite Z.add_0_r. apply (SW i 1%nat); lia.
  Qed.

  Lemma img_ok : Forall (fun iv => img_clear M (fst iv) (snd iv)) img_clear_ivs -> Forall (hholds RSEGS rho ms) facts_img.
  Proof.
    intros H. unfold facts_img. apply Forall_forall. intros f Hf. apply in_map_iff in Hf as ([lo hi] & <- & Hin).
    pose proof (proj1 (Forall_forall _ _) H _ Hin) as Hc. cbn [fst snd] in *.
    assert (0 <= lo < 2 ^ 63 /\ 0 <= hi < 2 ^ 63).
    { unfold img_clear_ivs in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; split; zclosed|]). destruct Hin. }
    apply hclear_ok; [tauto | tauto | exact Hc].
  Qed.

  Lemma geom_ok : forall nb,
    0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000 ->
    bv_unsigned sp0 mod 16 = 0 -> bv_unsigned mb mod 4096 = 0 -> bv_unsigned B mod 4096 = 0 ->
    0 < nb < 2 ^ 62 -> 0x354000 <= bv_unsigned mb -> 0x354000 <= bv_unsigned B ->
    bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608 -> bv_unsigned B + nb <= bv_unsigned sp0 - 8388608 ->
    (bv_unsigned mb + 8192 <= bv_unsigned B \/ bv_unsigned B + nb <= bv_unsigned mb) ->
    Forall (hholds RSEGS rho ms) (facts_geom nb).
  Proof.
    intros nb Hsp Hsp16 Hmbal HBal Hnb Hmb HB Hmbtop HBtop Hdj.
    pose proof (u64_range sp0) as Us. pose proof (u64_range mb) as Um. pose proof (u64_range B) as Ub.
    unfold facts_geom. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - eapply (hregion_ok RSEGS rho R pc M); [exact rho1 | | | | | | | | ]; try lia; try reflexivity.
    - eapply (hregion_ok RSEGS rho R pc M); [exact rho2 | | | | | | | | ]; try lia; try reflexivity; try exact Hmbal.
    - eapply (hregion_ok RSEGS rho R pc M); [exact rho2 | | | | | | | | ]; try lia; try reflexivity; try exact Hmbal.
    - eapply (hregion_ok RSEGS rho R pc M); [exact rho3 | | | | | | | | ]; try lia; try reflexivity; try exact HBal.
    - eapply (hdisj_ok RSEGS rho R pc M); [exact rho0 | exact rho1 | | | | | | | ]; lia.
    - eapply (hdisj_ok RSEGS rho R pc M); [exact rho0 | exact rho2 | | | | | | | ]; lia.
    - eapply (hdisj_ok RSEGS rho R pc M); [exact rho0 | exact rho2 | | | | | | | ]; lia.
    - eapply (hdisj_ok RSEGS rho R pc M); [exact rho0 | exact rho3 | | | | | | | ]; lia.
    - eapply (hdisj_ok RSEGS rho R pc M); [exact rho1 | exact rho2 | | | | | | | ]; lia.
    - eapply (hdisj_ok RSEGS rho R pc M); [exact rho1 | exact rho2 | | | | | | | ]; lia.
    - eapply (hdisj_ok RSEGS rho R pc M); [exact rho1 | exact rho3 | | | | | | | ]; lia.
    - eapply (hdisj_ok RSEGS rho R pc M); [exact rho2 | exact rho3 | | | | | | | ]; lia.
    - eapply (hdisj_ok RSEGS rho R pc M); [exact rho2 | exact rho3 | | | | | | | ]; lia.
  Qed.
End Common.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section K0.
  Variables (sp0 mb bw B : word) (can sec tid err brkv mas : Z) (R : bvmap 5 word) (uw gw : word) (pc : word) (M : word -> option byte).
  Variables (buf : Z) (content : list byte) (VM : VmMaps).
  Notation rho := (rho_of sp0 mb B can sec tid err R uw gw).
  Notation ms := (mkst R pc M (seg_rom RSEGS)).
  Hypothesis TE : tgt_entry (bv_unsigned sp0) buf can content R M.
  Hypothesis Hbuf : buf = bv_unsigned B + 32.
  Hypothesis W : world0 (bv_unsigned sp0) (bv_unsigned mb + 4096) (bv_unsigned B) brkv mas tid can sec M.
  Hypothesis Hbw : bv_unsigned bw = brkv.
  Hypothesis VP : vm_pre VM sp0 mb bw B.
  Hypothesis Herr : 0 <= err < 2 ^ 32 /\ HUWorld.cell M 0x331a44 4 err.

  Let Hsp := w_sp0 _ _ _ _ _ _ _ _ _ W.

  (* [comment removed for export] *)
  Lemma k0_brk_world : brkv = bv_unsigned mb + 8192 /\ mas = 0.
  Proof.
    destruct VP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & Xbw & _)).
    pose proof (w_world _ _ _ _ _ _ _ _ _ W) as WW. pose proof (w_area_rng _ _ _ _ _ _ _ _ _ W) as AR.
    rewrite Hbw in Xbw. destruct WW as [[E1 E2] | [E1 E2]]; [split; [lia | exact E2] | exfalso; lia].
  Qed.

  Lemma k0_regs : Forall (hholds RSEGS rho ms) (facts_regs 32).
  Proof.
    unfold facts_regs. destruct TE as [Tra Tsp Tgp Ttp Ta0 Ta1 Ta2 Ta3 Ts0 Ts1 Ts2 Ts3 Ts4 Ts5 Ts6 Ts7 _ _ _ _ _ _ _ _ _].
    repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - eapply (hreg_ok RSEGS rho R pc M 1%bv); [exact (rho0 sp0 mb B can sec tid err R uw gw) | | | exact Tra]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 2%bv); [exact (rho1 sp0 mb B can sec tid err R uw gw) | | | exact Tsp]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 3%bv); [exact (rho0 sp0 mb B can sec tid err R uw gw) | | | exact Tgp]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 4%bv); [exact (rho0 sp0 mb B can sec tid err R uw gw) | | | exact Ttp]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 8%bv); [exact (rho3 sp0 mb B can sec tid err R uw gw) | | | exact Ts0]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 9%bv); [exact (rho3 sp0 mb B can sec tid err R uw gw) | | | exact Ts1]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 10%bv); [exact (rho3 sp0 mb B can sec tid err R uw gw) | | | exact Ta0]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 22%bv); [exact (rho0 sp0 mb B can sec tid err R uw gw) | | | exact Ts6]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 23%bv); [exact (rho0 sp0 mb B can sec tid err R uw gw) | | | exact Ts7]; zside.
  Qed.

  Let r0 := rho0 sp0 mb B can sec tid err R uw gw.
  Let r1 := rho1 sp0 mb B can sec tid err R uw gw.
  Let r2 := rho2 sp0 mb B can sec tid err R uw gw.
  Let r3 := rho3 sp0 mb B can sec tid err R uw gw.
  Let r4 := rho4 sp0 mb B can sec tid err R uw gw.
  Let r5 := rho5 sp0 mb B can sec tid err R uw gw.
  Ltac hc Hr F := eapply (hcell_ok RSEGS rho R pc M); [exact Hr | | | | | exact F]; zside.
  Ltac hv Hr Hv F := eapply (hval_ok RSEGS rho R pc M); [exact Hr | | | exact Hv | | | exact F]; zside.
  Ltac ho Hr Hv F := eapply (hopq_ok RSEGS rho R pc M); [exact Hr | | | exact Hv | | exact F]; zside.

  Lemma k0_libc : Forall (hholds RSEGS rho ms) facts_libc.
  Proof.
    unfold facts_libc. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - hc r0 (w_self _ _ _ _ _ _ _ _ _ W).
    - ho r0 r4 (w_canary _ _ _ _ _ _ _ _ _ W).
    - hc r0 (w_pagesz _ _ _ _ _ _ _ _ _ W).
    - pose proof (w_tidr _ _ _ _ _ _ _ _ _ W) as TR.
      eapply (hbytesf_ok RSEGS rho R pc M); [exact r0 | | | | | reflexivity | | exact (w_tid _ _ _ _ _ _ _ _ _ W)]; zside.
    - eapply (hbytesf_ok RSEGS rho R pc M); [exact r0 | | | | | reflexivity | | exact (proj2 Herr)]; zside.
  Qed.

  Lemma k0_ctx : Forall (hholds RSEGS rho ms) facts_ctx0.
  Proof.
    destruct k0_brk_world as [Ebrk Emas].
    pose proof (w_mas _ _ _ _ _ _ _ _ _ W) as Fmas. rewrite Emas in Fmas.
    pose proof (w_brk _ _ _ _ _ _ _ _ _ W) as Fbrk. rewrite Ebrk in Fbrk.
    unfold facts_ctx0. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - ho r0 r5 (w_secret _ _ _ _ _ _ _ _ _ W).
    - hc r0 (w_init _ _ _ _ _ _ _ _ _ W).
    - hc r0 (w_ctr _ _ _ _ _ _ _ _ _ W).
    - hc r0 (w_fmh _ _ _ _ _ _ _ _ _ W).
    - hv r0 r2 (w_am _ _ _ _ _ _ _ _ _ W).
    - hc r0 (w_amc _ _ _ _ _ _ _ _ _ W).
    - hc r0 (w_amac _ _ _ _ _ _ _ _ _ W).
    - hc r0 Fmas.
    - hv r0 r2 (w_mah _ _ _ _ _ _ _ _ _ W).
    - hv r0 r2 (w_mat _ _ _ _ _ _ _ _ _ W).
    - hv r0 r2 (w_amas _ _ _ _ _ _ _ _ _ W).
    - hv r0 r2 (w_active44 _ _ _ _ _ _ _ _ _ W).
    - hc r0 (w_usage44 _ _ _ _ _ _ _ _ _ W).
    - hc r0 (w_seq _ _ _ _ _ _ _ _ _ W).
    - hv r0 r2 Fbrk.
  Qed.

  Lemma k0_area : Forall (hholds RSEGS rho ms) facts_area0.
  Proof.
    unfold facts_area0. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - ho r2 r5 (w_area_chk _ _ _ _ _ _ _ _ _ W).
    - hc r2 (w_area_next _ _ _ _ _ _ _ _ _ W).
    - hc r2 (w_area_ns _ _ _ _ _ _ _ _ _ W).
    - hv r2 r2 (w_slot0_prev _ _ _ _ _ _ _ _ _ W).
    - hv r2 r2 (w_slot0_next _ _ _ _ _ _ _ _ _ W).
    - hv r2 r3 (w_slot0_mem _ _ _ _ _ _ _ _ _ W).
    - hc r2 (w_slot0_msk _ _ _ _ _ _ _ _ _ W).
    - hc r2 (w_slot0_W _ _ _ _ _ _ _ _ _ W).
    - eapply (hzero_ok RSEGS rho R pc M); [exact r2 | | | | exact (w_area_rest _ _ _ _ _ _ _ _ _ W)]; zside.
    - eapply (hwr_ok_defined RSEGS rho R pc M); [exact r2 | | | | exact (w_area_def _ _ _ _ _ _ _ _ _ W)]; zside.
  Qed.

  Lemma k0_grp : Forall (hholds RSEGS rho ms) facts_grp0.
  Proof.
    unfold facts_grp0. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - hv r3 r2 (w_grp_meta _ _ _ _ _ _ _ _ _ W).
    - hc r3 (w_grp_aidx _ _ _ _ _ _ _ _ _ W).
    - eapply (hzero_ok RSEGS rho R pc M); [exact r3 | | | | exact (w_grp_pad _ _ _ _ _ _ _ _ _ W)]; zside.
    - eapply (hzero_ok RSEGS rho R pc M); [exact r3 | | | | exact (w_grp_tail _ _ _ _ _ _ _ _ _ W)]; zside.
    - eapply (hwr_ok_defined RSEGS rho R pc M); [exact r3 | | | | exact (w_grp_def _ _ _ _ _ _ _ _ _ W)]; zside.
  Qed.

  (* [comment removed for export] *)
  Lemma k0_slot : Forall (hholds RSEGS rho ms) facts_slot0.
  Proof.
    pose proof (w_gm_rng _ _ _ _ _ _ _ _ _ W) as GRs. pose proof (w_sp0 _ _ _ _ _ _ _ _ _ W) as Hsps.
    destruct (w_enframe _ _ _ _ _ _ _ _ _ W) as [P_p P_e P_r P_q Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Pr]. cbn zeta in *. subst P_p P_e P_r P_q.
    change (res_code (69616 - 4 - 65536 - 16 * 1)) with 5 in Pm3. change (69616 * 0 / 16 + 1) with 1 in Pm2.
    unfold facts_slot0. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - hc r3 (byte_rdn1 M _ 224 ltac:(lia) (Ps3 ltac:(lia))).
    - hc r3 (Ps2 ltac:(lia)).
    - eapply (hzero_ok RSEGS rho R pc M); [exact r3 | | | | exact (w_grp_zhd _ _ _ _ _ _ _ _ _ W)]; zside.
    - hc r3 (byte_rdn1 M _ 0 ltac:(lia) Pm4).
    - hc r3 (byte_rdn1 M _ 160 ltac:(lia) Pm3).
    - hc r3 Pm2.
    - hc r3 (byte_rdn1 M _ 0 ltac:(lia) (Pzr ltac:(lia))).
    - eapply (hzero_ok RSEGS rho R pc M); [exact r3 | | | | exact (w_grp_zsl _ _ _ _ _ _ _ _ _ W)]; zside.
    - hc r3 (byte_rdn1 M _ 0 ltac:(lia) (Pe5 ltac:(lia))).
    - hc r3 (Pe4 ltac:(lia)).
  Qed.
End K0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem handoff_k0x : forall (sp0 : word) (buf : Z) (can : word) (content : list byte) (VM : VmMaps) (R : bvmap 5 word)
    (M : word -> option byte) (pc uw gw : word),
  tgt_entry_full sp0 0 buf can content VM R M ->
  exists (mb bw B : word) (sec tid err : Z),
    let rho := rho_of sp0 mb B (bv_unsigned can) sec tid err R uw gw in
    rho 0%uint63 = Z_to_bv 64 0
    /\ buf = bv_unsigned B + 32
    /\ Forall (hholds RSEGS rho (mkst R pc M (seg_rom RSEGS))) facts_k0b
    /\ vm_reserved VM = segments_reserved RSEGS /\ (LIM <= vm_limit VM) /\ vm_init_sp VM = sp0
    /\ vm_exact VM sp0 mb bw B 69632
    /\ LedgerCfg.ledger_inv (segments_reserved RSEGS) LIM 2 (69632 + 8192) VM
    /\ 0 < tid < 2 ^ 22
    /\ 0 <= err < 2 ^ 32.      (* [comment removed for export] *)
Proof.
  intros sp0 buf can content VM R M pc uw gw [TE MF (mb & bw & B & brkv & mas & tid & sec & Hbw & HW)].
  destruct HW as [(_ & HL & Hbuf & W & VP) | (Hk & _)]; [|lia].
  destruct (w_errno _ _ _ _ _ _ _ _ _ W) as (err & Herr).
  exists mb, bw, B, sec, tid, err. cbv zeta.
  pose proof (w_sp0 _ _ _ _ _ _ _ _ _ W) as Hsp. pose proof (w_area_rng _ _ _ _ _ _ _ _ _ W) as AR.
  pose proof (w_area_al _ _ _ _ _ _ _ _ _ W) as AA. pose proof (w_gm_al _ _ _ _ _ _ _ _ _ W) as GA.
  pose proof (w_gm_rng _ _ _ _ _ _ _ _ _ W) as GR.
  assert (Hmbal : bv_unsigned mb mod 4096 = 0).
  { replace (bv_unsigned mb + 4096) with (bv_unsigned mb + 1 * 4096) in AA by lia. rewrite Z_mod_plus_full in AA. exact AA. }
  pose proof VP as (Vres & Vlim & Visp & _ & _ & _ & _ & _ & _ & _ & Vex).
  pose proof Vex as (_ & _ & _ & _ & _ & Xr & _ & _ & _ & _ & Xdj & _). rewrite hreserved_top in Xr.
  split; [reflexivity|]. split; [exact Hbuf|]. split.
  - unfold facts_k0b. apply Forall_app; split; [|exact (k0_slot sp0 mb B (bv_unsigned can) sec tid err brkv mas R uw gw pc M W)].
    unfold facts_k0. repeat (apply Forall_app; split).
    + apply regs_opaque_ok.
    + exact (k0_regs sp0 mb B (bv_unsigned can) sec tid err R uw gw pc M buf content TE Hbuf).
    + apply frame_ok; [exact MF | exact (te_stack _ _ _ _ _ _ TE)].
    + apply img_ok. exact (w_img _ _ _ _ _ _ _ _ _ W).
    + exact (k0_libc sp0 mb B (bv_unsigned can) sec tid err brkv mas R uw gw pc M W Herr).
    + exact (k0_ctx sp0 mb bw B (bv_unsigned can) sec tid err brkv mas R uw gw pc M VM W Hbw VP).
    + exact (k0_area sp0 mb B (bv_unsigned can) sec tid err brkv mas R uw gw pc M W).
    + exact (k0_grp sp0 mb B (bv_unsigned can) sec tid err brkv mas R uw gw pc M W).
    + apply geom_ok; try lia. exact (proj2 (te_sp0 _ _ _ _ _ _ TE)).
  - split; [exact Vres|]. split; [exact Vlim|]. split; [exact Visp|]. split; [exact Vex|].
    split; [|split; [exact (w_tidr _ _ _ _ _ _ _ _ _ W) | exact (proj1 Herr)]].
    apply (vm_exact_ledger_inv VM sp0 mb bw B 69632 Vres Vlim Visp Hsp Vex); try lia; try reflexivity.
Qed.

Theorem handoff_k0 : forall (sp0 : word) (buf : Z) (can : word) (content : list byte) (VM : VmMaps) (R : bvmap 5 word)
    (M : word -> option byte) (pc uw gw : word),
  tgt_entry_full sp0 0 buf can content VM R M ->
  exists (mb bw B : word) (sec tid err : Z),
    let rho := rho_of sp0 mb B (bv_unsigned can) sec tid err R uw gw in
    rho 0%uint63 = Z_to_bv 64 0
    /\ buf = bv_unsigned B + 32
    /\ Forall (hholds RSEGS rho (mkst R pc M (seg_rom RSEGS))) facts_k0
    /\ vm_reserved VM = segments_reserved RSEGS /\ (LIM <= vm_limit VM) /\ vm_init_sp VM = sp0
    /\ vm_exact VM sp0 mb bw B 69632
    /\ LedgerCfg.ledger_inv (segments_reserved RSEGS) LIM 2 (69632 + 8192) VM.
Proof.
  intros sp0 buf can content VM R M pc uw gw TF.
  destruct (handoff_k0x sp0 buf can content VM R M pc uw gw TF) as (mb & bw & B & sec & tid & err & H).
  exists mb, bw, B, sec, tid, err. cbv zeta in *. destruct H as (H0 & Hb & HF & Hrest). unfold facts_k0b in HF. apply Forall_app in HF as [HF _]. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition slotCo (k : Z) : Z := 4096 + 24 + 40 * (k mod 2).    (* [comment removed for export] *)
Definition slotFo (k : Z) : Z := 4096 + 64 - 40 * (k mod 2).    (* [comment removed for export] *)

Definition facts_ctxk (k : Z) : list hfact :=
  [ hopq 0 ctx_secret T_SEC; hcell 0 ctx_init_done 4 1; hcell 0 ctx_mmap_counter 4 (1 + k);
    hval 0 ctx_free_meta_head T_BRK (slotFo k); hval 0 ctx_avail_meta T_BRK (4096 + 104); hcell 0 ctx_avail_meta_count 8 99;
    hcell 0 ctx_avail_meta_area_count 8 0; hcell 0 ctx_meta_alloc_shift 8 0; hval 0 ctx_meta_area_head T_BRK 4096;
    hval 0 ctx_meta_area_tail T_BRK 4096; hval 0 ctx_avail_meta_areas T_BRK 8192; hcell 0 (ctx_active 44) 8 0;
    hcell 0 (ctx_usage 44) 8 0; hcell 0 ctx_seq 1 (1 + 2 * k); hval 0 ctx_brk T_BRK 8192 ].
Definition facts_areak (k : Z) : list hfact :=
  [ hopq T_BRK 4096 T_SEC; hcell T_BRK (4096 + 8) 8 0; hcell T_BRK (4096 + 16) 4 101;
    hcell T_BRK (slotCo k) 8 0; hcell T_BRK (slotCo k + 8) 8 0; hval T_BRK (slotCo k + 16) T_BUF 0;
    hcell T_BRK (slotCo k + 24) 4 0; hcell T_BRK (slotCo k + 28) 4 0; hcell T_BRK (slotCo k + 32) 8 (Wk k);
    hval T_BRK (slotFo k) T_BRK (slotFo k); hval T_BRK (slotFo k + 8) T_BRK (slotFo k); hcell T_BRK (slotFo k + 16) 8 0;
    hcell T_BRK (slotFo k + 24) 8 0; hcell T_BRK (slotFo k + 32) 8 0;
    hzero T_BRK (4096 + 104) (4096 - 104); hwr T_BRK 4096 4096 ].
Definition facts_grpk (k : Z) : list hfact :=
  [ hval T_BUF 0 T_BRK (slotCo k); hcell T_BUF 8 1 0; hzero T_BUF 9 4; hzero T_BUF (nbk k - 4) 4; hwr T_BUF 0 (nbk k) ].
(* [comment removed for export] *)
Definition facts_slotk (k : Z) : list hfact :=
  [ hcell T_BUF 13 1 224; hcell T_BUF 14 2 (k + 1);
    hcell T_BUF (offk k - 4) 1 0; hcell T_BUF (offk k - 3) 1 160; hcell T_BUF (offk k - 2) 2 (k + 1);
    hcell T_BUF (offk k + capk k) 1 0; hcell T_BUF (nbk k - 9) 1 0; hcell T_BUF (nbk k - 8) 4 (resk k) ].

Definition facts_k (k : Z) : list hfact :=
  facts_regs_opaque ++ facts_regs (offk k) ++ facts_frame ++ facts_img ++ facts_libc ++ facts_ctxk k ++ facts_areak k ++ facts_grpk k
  ++ facts_geom (nbk k).
Definition facts_kb (k : Z) : list hfact := facts_k k ++ facts_slotk k.     (* [comment removed for export] *)

Lemma capk_bounds : forall k, 1 <= k <= 10 -> 131072 <= capk k <= 67108864 /\ capk k mod 4096 = 0.
Proof.
  intros k Hk. assert (E : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
  repeat (destruct E as [-> | E]); try subst k; vm_compute; repeat split; congruence.
Qed.

Section KK.
  Variables (sp0 mb bw B : word) (can sec tid err brkv mas k : Z) (R : bvmap 5 word) (uw gw : word) (pc : word) (M : word -> option byte).
  Variables (buf : Z) (content : list byte) (VM : VmMaps).
  Notation rho := (rho_of sp0 mb B can sec tid err R uw gw).
  Notation ms := (mkst R pc M (seg_rom RSEGS)).
  Hypothesis TE : tgt_entry (bv_unsigned sp0) buf can content R M.
  Hypothesis Hbuf : buf = bv_unsigned B + offk k.
  Hypothesis W : world_k (bv_unsigned sp0) k (bv_unsigned mb + 4096) (bv_unsigned B) brkv mas tid can sec M.
  Hypothesis Hbw : bv_unsigned bw = brkv.
  Hypothesis VS : vm_stage VM sp0 mb bw B (nbk k).
  Hypothesis Herr : 0 <= err < 2 ^ 32 /\ HUWorld.cell M 0x331a44 4 err.

  Let Hk := wk_k _ _ _ _ _ _ _ _ _ _ W.
  Let r0 := rho0 sp0 mb B can sec tid err R uw gw.
  Let r1 := rho1 sp0 mb B can sec tid err R uw gw.
  Let r2 := rho2 sp0 mb B can sec tid err R uw gw.
  Let r3 := rho3 sp0 mb B can sec tid err R uw gw.
  Let r4 := rho4 sp0 mb B can sec tid err R uw gw.
  Let r5 := rho5 sp0 mb B can sec tid err R uw gw.

  Lemma kk_vm_exact : vm_exact VM sp0 mb bw B (nbk k).
  Proof. destruct VS as (_ & _ & _ & rest & _ & _ & _ & _ & _ & _ & _ & _ & Vex). exact Vex. Qed.

  Lemma kk_brk_world : brkv = bv_unsigned mb + 8192 /\ mas = 0.
  Proof.
    pose proof kk_vm_exact as (_ & _ & _ & _ & Xbw & _).
    pose proof (wk_world _ _ _ _ _ _ _ _ _ _ W) as WW. pose proof (wk_area_rng _ _ _ _ _ _ _ _ _ _ W) as AR.
    pose proof (wk_sp0 _ _ _ _ _ _ _ _ _ _ W) as Hsp.
    rewrite Hbw in Xbw. destruct WW as [[E1 E2] | [E1 E2]]; [split; [lia | exact E2] | exfalso; lia].
  Qed.

  Ltac zsideK := pose proof Hk; pose proof (capk_bounds k Hk); unfold slotCo, slotFo, slotC, slotF, Wk, nbk, offk in *; first [reflexivity | lia | zclosed].
  Ltac hcK Hr F := let H := fresh "F" in pose proof F as H; unfold slotC, slotF, Wk, nbk in H;
                    eapply (hcell_ok RSEGS rho R pc M); [exact Hr | | | | | exact H]; zsideK.
  Ltac hvK Hr Hv F := let H := fresh "F" in pose proof F as H; unfold slotC, slotF, Wk, nbk in H;
                    eapply (hval_ok RSEGS rho R pc M); [exact Hr | | | exact Hv | | | exact H]; zsideK.
  Ltac hoK Hr Hv F := eapply (hopq_ok RSEGS rho R pc M); [exact Hr | | | exact Hv | | exact F]; zsideK.

  Lemma kk_regs : Forall (hholds RSEGS rho ms) (facts_regs (offk k)).
  Proof.
    unfold facts_regs. destruct TE as [Tra Tsp Tgp Ttp Ta0 Ta1 Ta2 Ta3 Ts0 Ts1 Ts2 Ts3 Ts4 Ts5 Ts6 Ts7 _ _ _ _ _ _ _ _ _].
    repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - eapply (hreg_ok RSEGS rho R pc M 1%bv); [exact r0 | | | exact Tra]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 2%bv); [exact r1 | | | exact Tsp]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 3%bv); [exact r0 | | | exact Tgp]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 4%bv); [exact r0 | | | exact Ttp]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 8%bv); [exact r3 | | | exact Ts0]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 9%bv); [exact r3 | | | exact Ts1]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 10%bv); [exact r3 | | | exact Ta0]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 22%bv); [exact r0 | | | exact Ts6]; zside.
    - eapply (hreg_ok RSEGS rho R pc M 23%bv); [exact r0 | | | exact Ts7]; zside.
  Qed.

  Lemma kk_libc : Forall (hholds RSEGS rho ms) facts_libc.
  Proof.
    unfold facts_libc. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - hcK r0 (wk_self _ _ _ _ _ _ _ _ _ _ W).
    - hoK r0 r4 (wk_canary _ _ _ _ _ _ _ _ _ _ W).
    - hcK r0 (wk_pagesz _ _ _ _ _ _ _ _ _ _ W).
    - pose proof (wk_tidr _ _ _ _ _ _ _ _ _ _ W) as TR.
      eapply (hbytesf_ok RSEGS rho R pc M); [exact r0 | | | | | reflexivity | | exact (wk_tid _ _ _ _ _ _ _ _ _ _ W)]; zside.
    - eapply (hbytesf_ok RSEGS rho R pc M); [exact r0 | | | | | reflexivity | | exact (proj2 Herr)]; zside.
  Qed.

  Lemma kk_ctx : Forall (hholds RSEGS rho ms) (facts_ctxk k).
  Proof.
    destruct kk_brk_world as [Ebrk Emas].
    pose proof (wk_mas _ _ _ _ _ _ _ _ _ _ W) as Fmas. rewrite Emas in Fmas.
    pose proof (wk_brk _ _ _ _ _ _ _ _ _ _ W) as Fbrk. rewrite Ebrk in Fbrk.
    unfold facts_ctxk. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - hoK r0 r5 (wk_secret _ _ _ _ _ _ _ _ _ _ W).
    - hcK r0 (wk_init _ _ _ _ _ _ _ _ _ _ W).
    - hcK r0 (wk_ctr _ _ _ _ _ _ _ _ _ _ W).
    - hvK r0 r2 (wk_fmh _ _ _ _ _ _ _ _ _ _ W).
    - hvK r0 r2 (wk_am _ _ _ _ _ _ _ _ _ _ W).
    - hcK r0 (wk_amc _ _ _ _ _ _ _ _ _ _ W).
    - hcK r0 (wk_amac _ _ _ _ _ _ _ _ _ _ W).
    - hcK r0 Fmas.
    - hvK r0 r2 (wk_mah _ _ _ _ _ _ _ _ _ _ W).
    - hvK r0 r2 (wk_mat _ _ _ _ _ _ _ _ _ _ W).
    - hvK r0 r2 (wk_amas _ _ _ _ _ _ _ _ _ _ W).
    - hcK r0 (wk_active44 _ _ _ _ _ _ _ _ _ _ W).
    - hcK r0 (wk_usage44 _ _ _ _ _ _ _ _ _ _ W).
    - hcK r0 (wk_seq _ _ _ _ _ _ _ _ _ _ W).
    - hvK r0 r2 Fbrk.
  Qed.

  Lemma kk_area : Forall (hholds RSEGS rho ms) (facts_areak k).
  Proof.
    unfold facts_areak. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - hoK r2 r5 (wk_area_chk _ _ _ _ _ _ _ _ _ _ W).
    - hcK r2 (wk_area_next _ _ _ _ _ _ _ _ _ _ W).
    - hcK r2 (wk_area_ns _ _ _ _ _ _ _ _ _ _ W).
    - hcK r2 (wk_cur_prev _ _ _ _ _ _ _ _ _ _ W).
    - hcK r2 (wk_cur_next _ _ _ _ _ _ _ _ _ _ W).
    - hvK r2 r3 (wk_cur_mem _ _ _ _ _ _ _ _ _ _ W).
    - hcK r2 (wk_cur_avail _ _ _ _ _ _ _ _ _ _ W).
    - hcK r2 (wk_cur_freed _ _ _ _ _ _ _ _ _ _ W).
    - hcK r2 (wk_cur_W _ _ _ _ _ _ _ _ _ _ W).
    - hvK r2 r2 (wk_free_prev _ _ _ _ _ _ _ _ _ _ W).
    - hvK r2 r2 (wk_free_next _ _ _ _ _ _ _ _ _ _ W).
    - hcK r2 (wk_free_mem _ _ _ _ _ _ _ _ _ _ W).
    - hcK r2 (wk_free_msk _ _ _ _ _ _ _ _ _ _ W).
    - hcK r2 (wk_free_W _ _ _ _ _ _ _ _ _ _ W).
    - eapply (hzero_ok RSEGS rho R pc M); [exact r2 | | | | exact (wk_area_rest _ _ _ _ _ _ _ _ _ _ W)]; zside.
    - eapply (hwr_ok_defined RSEGS rho R pc M); [exact r2 | | | | exact (wk_area_def _ _ _ _ _ _ _ _ _ _ W)]; zside.
  Qed.

  Lemma kk_grp : Forall (hholds RSEGS rho ms) (facts_grpk k).
  Proof.
    unfold facts_grpk. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - hvK r3 r2 (wk_grp_meta _ _ _ _ _ _ _ _ _ _ W).
    - hcK r3 (wk_grp_aidx _ _ _ _ _ _ _ _ _ _ W).
    - eapply (hzero_ok RSEGS rho R pc M); [exact r3 | | | | exact (wk_grp_pad _ _ _ _ _ _ _ _ _ _ W)]; zside.
    - pose proof (wk_grp_tail _ _ _ _ _ _ _ _ _ _ W) as F. eapply (hzero_ok RSEGS rho R pc M); [exact r3 | | | | exact F]; zsideK.
    - pose proof (wk_grp_def _ _ _ _ _ _ _ _ _ _ W) as F. eapply (hwr_ok_defined RSEGS rho R pc M); [exact r3 | | | | exact F]; zsideK.
  Qed.

  (* [comment removed for export] *)
  Lemma kk_slot : Forall (hholds RSEGS rho ms) (facts_slotk k).
  Proof.
    pose proof (wk_B_rng _ _ _ _ _ _ _ _ _ _ W) as GRs. pose proof (wk_sp0 _ _ _ _ _ _ _ _ _ _ W) as Hsps. pose proof (capk_bounds k Hk) as (CBs & CMs).
    destruct (wk_enframe _ _ _ _ _ _ _ _ _ _ W) as [P_p P_e P_r P_q Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Pr]. cbn zeta in *. subst P_p P_e P_r P_q.
    assert (Er : nbk k - 16 - 4 - capk k - 16 * (k + 1) = resk k) by (unfold nbk, resk; lia).
    assert (Eq : (nbk k - 16) * 0 / 16 + (k + 1) = k + 1) by (rewrite Z.mul_0_r; cbn; lia).
    rewrite Er in *. rewrite Eq in *.
    assert (E5 : res_code (resk k) = 5) by (unfold res_code, resk; destruct (Z.ltb_spec (4060 - 16 * k) 5); lia).
    rewrite E5 in Pm3. change (0 + 32 * 5) with 160 in Pm3.
    assert (Hr5 : 5 <= resk k) by (unfold resk; lia).
    unfold facts_slotk. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
    - eapply (hcell_ok RSEGS rho R pc M); [exact r3 | | | | | exact (byte_rdn1 M _ 224 ltac:(lia) (Ps3 ltac:(lia)))]; zsideK.
    - eapply (hcell_ok RSEGS rho R pc M); [exact r3 | | | | | exact (Ps2 ltac:(lia))]; zsideK.
    - eapply (hcell_ok RSEGS rho R pc M); [exact r3 | | | | | exact (byte_rdn1 M _ 0 ltac:(lia) Pm4)]; zsideK.
    - eapply (hcell_ok RSEGS rho R pc M); [exact r3 | | | | | exact (byte_rdn1 M _ 160 ltac:(lia) Pm3)]; zsideK.
    - eapply (hcell_ok RSEGS rho R pc M); [exact r3 | | | | | exact Pm2]; zsideK.
    - eapply (hcell_ok RSEGS rho R pc M); [exact r3 | | | | | exact (byte_rdn1 M _ 0 ltac:(lia) (Pzr ltac:(lia)))]; zsideK.
    - eapply (hcell_ok RSEGS rho R pc M); [exact r3 | | | | | exact (byte_rdn1 M _ 0 ltac:(lia) (Pe5 Hr5))]; zsideK.
    - eapply (hcell_ok RSEGS rho R pc M); [exact r3 | | | | | exact (Pe4 Hr5)]; zsideK.
  Qed.
End KK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem handoff_kx : forall (sp0 : word) (k buf : Z) (can : word) (content : list byte) (VM : VmMaps) (R : bvmap 5 word)
    (M : word -> option byte) (pc uw gw : word),
  1 <= k <= 10 ->
  tgt_entry_full sp0 k buf can content VM R M ->
  exists (mb bw B : word) (sec tid err : Z),
    let rho := rho_of sp0 mb B (bv_unsigned can) sec tid err R uw gw in
    rho 0%uint63 = Z_to_bv 64 0
    /\ buf = bv_unsigned B + offk k
    /\ Forall (hholds RSEGS rho (mkst R pc M (seg_rom RSEGS))) (facts_kb k)
    /\ vm_reserved VM = segments_reserved RSEGS /\ (LIM <= vm_limit VM) /\ vm_init_sp VM = sp0
    /\ vm_exact VM sp0 mb bw B (nbk k)
    /\ LedgerCfg.ledger_inv (segments_reserved RSEGS) LIM 2 (nbk k + 8192) VM
    /\ 0 < tid < 2 ^ 22
    /\ 0 <= err < 2 ^ 32.      (* [comment removed for export] *)
Proof.
  intros sp0 k buf can content VM R M pc uw gw Hk [TE MF (mb & bw & B & brkv & mas & tid & sec & Hbw & HW)].
  destruct HW as [(Hk0 & _) | (_ & HL & Hbuf & W & VS)]; [lia|].
  destruct (wk_errno _ _ _ _ _ _ _ _ _ _ W) as (err & Herr).
  exists mb, bw, B, sec, tid, err. cbv zeta.
  pose proof (wk_sp0 _ _ _ _ _ _ _ _ _ _ W) as Hsp. pose proof (wk_area_rng _ _ _ _ _ _ _ _ _ _ W) as AR.
  pose proof (wk_area_al _ _ _ _ _ _ _ _ _ _ W) as AA. pose proof (wk_B_al _ _ _ _ _ _ _ _ _ _ W) as GA.
  pose proof (wk_B_rng _ _ _ _ _ _ _ _ _ _ W) as GR. pose proof (capk_bounds k Hk) as (CB & CM).
  assert (Hmbal : bv_unsigned mb mod 4096 = 0).
  { replace (bv_unsigned mb + 4096) with (bv_unsigned mb + 1 * 4096) in AA by lia. rewrite Z_mod_plus_full in AA. exact AA. }
  pose proof VS as (Vres & Vlim & Visp & _).
  pose proof (kk_vm_exact sp0 mb bw B k VM VS) as Vex.
  pose proof Vex as (_ & _ & _ & _ & _ & Xr & _ & _ & _ & _ & Xdj & _). rewrite hreserved_top in Xr.
  assert (Hnb : 0 < nbk k < 2 ^ 62 /\ nbk k mod 4096 = 0).
  { unfold nbk. split; [lia|]. replace (capk k + 4096) with (capk k + 1 * 4096) by lia. rewrite Z_mod_plus_full. exact CM. }
  split; [reflexivity|]. split; [exact Hbuf|]. split.
  - unfold facts_kb. apply Forall_app; split; [|exact (kk_slot sp0 mb B (bv_unsigned can) sec tid err brkv mas k R uw gw pc M W)].
    unfold facts_k. repeat (apply Forall_app; split).
    + apply regs_opaque_ok.
    + exact (kk_regs sp0 mb B (bv_unsigned can) sec tid err k R uw gw pc M buf content TE Hbuf).
    + apply frame_ok; [exact MF | exact (te_stack _ _ _ _ _ _ TE)].
    + apply img_ok. exact (wk_img _ _ _ _ _ _ _ _ _ _ W).
    + exact (kk_libc sp0 mb B (bv_unsigned can) sec tid err brkv mas k R uw gw pc M W Herr).
    + exact (kk_ctx sp0 mb bw B (bv_unsigned can) sec tid err brkv mas k R uw gw pc M VM W Hbw VS).
    + exact (kk_area sp0 mb B (bv_unsigned can) sec tid err brkv mas k R uw gw pc M W).
    + exact (kk_grp sp0 mb B (bv_unsigned can) sec tid err brkv mas k R uw gw pc M W).
    + apply geom_ok; try lia. exact (proj2 (te_sp0 _ _ _ _ _ _ TE)).
  - split; [exact Vres|]. split; [exact Vlim|]. split; [exact Visp|]. split; [exact Vex|].
    split; [|split; [exact (wk_tidr _ _ _ _ _ _ _ _ _ _ W) | exact (proj1 Herr)]].
    apply (vm_exact_ledger_inv VM sp0 mb bw B (nbk k) Vres Vlim Visp Hsp Vex); try lia; try tauto.
Qed.

Theorem handoff_k : forall (sp0 : word) (k buf : Z) (can : word) (content : list byte) (VM : VmMaps) (R : bvmap 5 word)
    (M : word -> option byte) (pc uw gw : word),
  1 <= k <= 10 ->
  tgt_entry_full sp0 k buf can content VM R M ->
  exists (mb bw B : word) (sec tid err : Z),
    let rho := rho_of sp0 mb B (bv_unsigned can) sec tid err R uw gw in
    rho 0%uint63 = Z_to_bv 64 0
    /\ buf = bv_unsigned B + offk k
    /\ Forall (hholds RSEGS rho (mkst R pc M (seg_rom RSEGS))) (facts_k k)
    /\ vm_reserved VM = segments_reserved RSEGS /\ (LIM <= vm_limit VM) /\ vm_init_sp VM = sp0
    /\ vm_exact VM sp0 mb bw B (nbk k)
    /\ LedgerCfg.ledger_inv (segments_reserved RSEGS) LIM 2 (nbk k + 8192) VM.
Proof.
  intros sp0 k buf can content VM R M pc uw gw Hk TF.
  destruct (handoff_kx sp0 k buf can content VM R M pc uw gw Hk TF) as (mb & bw & B & sec & tid & err & H).
  exists mb, bw, B, sec, tid, err. cbv zeta in *. destruct H as (H0 & Hb & HF & Hrest). unfold facts_kb in HF. apply Forall_app in HF as [HF _]. tauto.
Qed.

(* [comment removed for export] *)
Lemma model_post_creds : forall V (inp : ProcInput) fs tid,
  m_creds (model_post V (ModelAmb.amb_of inp) fs tid)
  = mkCreds (in_uid inp) (in_uid inp) (in_uid inp) (in_gid inp) (in_gid inp) (in_gid inp) (in_groups inp).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rho_reg : forall sp0 mb B can sec tid err R uw gw (r : Z), 0 <= r < 32 ->
  rho_of sp0 mb B can sec tid err R uw gw (T_REG r) = getr R (Z_to_bv 5 r).
Proof.
  intros sp0 mb B can sec tid err R uw gw r Hr.
  assert (E : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/ r = 10 \/ r = 11 \/ r = 12 \/ r = 13
              \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25
              \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/ r = 30 \/ r = 31) by lia.
  repeat (destruct E as [-> | E]; [reflexivity|]). subst r. reflexivity.
Qed.

Lemma handoff_teqs : forall (sp0 : word) (k buf : Z) (can : word) (content : list byte) (VM : VmMaps) (R : bvmap 5 word)
    (M : word -> option byte) (mb B : word) (sec tid err : Z) (uw gw : word),
  tgt_entry_full sp0 k buf can content VM R M ->
  let rho := rho_of sp0 mb B (bv_unsigned can) sec tid err R uw gw in
     bv_unsigned (rho 111%uint63) = hdr_cfglen content
  /\ bv_unsigned (rho 112%uint63) = buf + 6 + hdr_cfglen content
  /\ bv_unsigned (rho 113%uint63) = hdr_paylen content
  /\ bv_unsigned (rho 118%uint63) = hdr_cfglen content
  /\ bv_unsigned (rho 119%uint63) = buf + 6 + hdr_cfglen content
  /\ bv_unsigned (rho 120%uint63) = hdr_paylen content
  /\ 0 <= hdr_cfglen content < 32768
  /\ 0 <= hdr_paylen content
  /\ 6 + hdr_cfglen content + hdr_paylen content = Z.of_nat (length content)
  /\ Z.of_nat (length content) < (if k =? 0 then 65536 else capk k)
  /\ 0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000 /\ bv_unsigned sp0 mod 16 = 0
  /\ rdn RSEGS M (Z_to_bv 64 buf) (length content) = Some content.
Proof.
  intros sp0 k buf can content VM R M mb B sec tid err uw gw [TE MF HW]. cbv zeta.
  destruct TE as [Tra Tsp Tgp Ttp Ta0 Ta1 Ta2 Ta3 Ts0 Ts1 Ts2 Ts3 Ts4 Ts5 Ts6 Ts7 Tsp0 Tlen Tbuf Tcan Tstack Timg Tinit Tcanary Tcontent].
  assert (Hc : 0 <= hdr_cfglen content < 32768) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  assert (Hp : 0 <= hdr_paylen content) by (unfold hdr_paylen; lia).
  assert (HL : Z.of_nat (length content) < (if k =? 0 then 65536 else capk k)).
  { destruct HW as (mb' & bw' & B' & brkv & mas & tid' & sec' & _ & [(-> & HL & _) | (Hk & HL & _)]).
    - exact HL.
    - destruct (Z.eqb_spec k 0); [lia | exact (proj2 HL)]. }
  assert (Hreg : forall r v, 0 <= r < 32 -> getr R (Z_to_bv 5 r) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
            bv_unsigned (rho_of sp0 mb B (bv_unsigned can) sec tid err R uw gw (T_REG r)) = v).
  { intros r v Hr E Hv. rewrite rho_reg by exact Hr. rewrite E. apply AgentLib.u64_lit. exact Hv. }
  pose proof (u64_range sp0) as Us.
  assert (Hb : 0 <= buf + 6 + hdr_cfglen content < 2 ^ 64) by lia.
  assert (Hpl : 0 <= hdr_paylen content < 2 ^ 64) by (unfold hdr_paylen in *; lia).
  split; [exact (Hreg 11 _ ltac:(lia) Ta1 ltac:(lia))|].
  split; [exact (Hreg 12 _ ltac:(lia) Ta2 Hb)|].
  split; [exact (Hreg 13 _ ltac:(lia) Ta3 Hpl)|].
  split; [exact (Hreg 18 _ ltac:(lia) Ts2 ltac:(lia))|].
  split; [exact (Hreg 19 _ ltac:(lia) Ts3 Hb)|].
  split; [exact (Hreg 20 _ ltac:(lia) Ts4 Hpl)|].
  split; [exact Hc|]. split; [exact Hp|]. split; [unfold hdr_paylen; lia|]. split; [exact HL|].
  split; [exact (proj1 Tsp0)|]. split; [exact (proj2 Tsp0)|]. exact Tcontent.
Qed.

(* [comment removed for export] *)
Lemma handoff_teq_s5 : forall (sp0 : word) (k buf : Z) (can : word) (content : list byte) (VM : VmMaps) (R : bvmap 5 word)
    (M : word -> option byte) (mb B : word) (sec tid err : Z) (uw gw : word),
  tgt_entry_full sp0 k buf can content VM R M ->
  let rho := rho_of sp0 mb B (bv_unsigned can) sec tid err R uw gw in
     bv_unsigned (rho 121%uint63) = (if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64)
  /\ 0 <= hdr_b1 content < 256
  /\ (32768 <=? cfg_word content) = negb (hdr_b1 content <? 128).
Proof.
  intros sp0 k buf can content VM R M mb B sec tid err uw gw [TE _ _]. cbv zeta.
  assert (Hb : 0 <= hdr_b1 content < 256).
  { unfold hdr_b1. pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256 in H. exact H. }
  assert (Hb0 : 0 <= byte_at content 0 < 256).
  { unfold byte_at. pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256 in H. exact H. }
  split; [|split; [exact Hb|]].
  - change 121%uint63 with (T_REG 21). rewrite rho_reg by lia.
    assert (E : getr R (Z_to_bv 5 21) = Z_to_bv 64 (if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64))
      by exact (te_s5 _ _ _ _ _ _ TE).
    rewrite E.
    apply AgentLib.u64_lit. destruct (hdr_b1 content <? 128); lia.
  - unfold cfg_word. change (byte_at content 1) with (hdr_b1 content).
    destruct (Z.ltb_spec (hdr_b1 content) 128); cbn [negb]; [apply Z.leb_gt | apply Z.leb_le]; lia.
Qed.

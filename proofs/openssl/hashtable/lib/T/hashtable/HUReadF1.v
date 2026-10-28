(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib MemSplit Frame StreamSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib RefNodes PhaseG LibKnowFrame LibKnowXfer RefReadLib
  HUReadBase HUReadStage HUReadChunk.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HU_code_26b000_26c000 HU_code_26c000_26d000 HU_code_26d000_26e000 HU_code_276000_277000 HU_code_dd000_de000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import HUReadChunk.H0ReadChunkW.
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

(* [comment removed for export] *)
Ltac noncert_qtautoF :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition FFUEL : nat := 5000.
Definition FSTOPS : list Z :=
  [0x2bc024; 0x2b1b10; 0x2b1c50; 0x2b31f4; 0x2b1e20; 0x2b17ec; 0xe1aa0; 0xe1c1c; 0xe1bf8; 0xe1a24; 0xe1a68]%Z.
Definition fscr0 : scripts := SCR [] [] [].

Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 42%nat -> map (vals_ev vals) (seq 0 42) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.

(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Ltac norm_know HK :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
    let kn' := eval vm_compute in kn in
    let EQ := fresh "EQkn" in
    assert (EQ : kn = kn') by (vm_compute; reflexivity);
    try rewrite EQ in HK; clear EQ end.
Ltac norm_regs HR :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let sr' := eval vm_compute in sr in
    let EQ := fresh "EQsr" in
    assert (EQ : sr = sr') by (vm_compute; reflexivity);
    try rewrite EQ in HR; clear EQ end.
Ltac grow_vals HL extra newlen :=
  lazymatch type of HL with length ?vals = ?n =>
    let HL' := fresh "HL" in
    assert (HL' : length (vals ++ extra) = newlen)
      by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
    repeat match goal with
    | P : vals_ev vals ?i = ?v |- _ =>
        let P' := fresh "P" in
        assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
        clear P; rename P' into P
    end;
    let v' := fresh "vals" in
    set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
  end.

(* [comment removed for export] *)
Ltac regq HR :=
  lazymatch goal with |- getr _ ?rr = _ =>
    regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
    lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
    rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

(* [comment removed for export] *)
Module H0ReadF2.

(* [comment removed for export] *)

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX true.

Section F.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb bw gm B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)).

  Definition full_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG (cap_of j') V)).

  Theorem fill2 : forall mode Q R M V B e M0 K,
    half 2 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (262144 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch mode Q 2 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 131072 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 266240 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 266240%Z 131136%Z (Z.to_nat 131072) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 131136)%Z with (bv_unsigned B + 64 + 131072)%Z in SOKb by lia.
    replace (Z.to_nat 131072) with (Z.to_nat (262144 - 131072)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 64 (ELit 131072) 2%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 2%nat) with (gblobs content 2%nat) in HELD. rewrite (gblobs_hb 2) in HELD by lia. change (held_of 2) with 131072%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 131072) R M (bv_unsigned sp0) (bv_unsigned B + 64) 131072 262144 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((262144 - 131072)%Z) with (131072%Z) in FR. change ((262144 - 131072)%Z) with (131072%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 131136 131072)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 131136)%Z with (bv_unsigned B + 64 + 131072)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 131072 (dropz 131072 content))) = 131072%Z)
        by (pose proof (pref_length 131072 (dropz 131072 content) ltac:(lia)); pose proof (dropz_length 131072 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 131136) (ELit 131072) 3%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 131136 131072 3%nat (pref 131072 (dropz 131072 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 3%nat) with (gblobs content 3%nat). rewrite (gblobs_cb 2) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 131072 (dropz 131072 content))) with (Z.to_nat 131072) by lia.
          replace (bv_unsigned B + 131136)%Z with (bv_unsigned B + 64 + 131072)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb SW VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 74%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 64)) (ridx 23) (bx 64)) (ridx 19) (ELit 262144)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; ELit 0] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb bw gm L B e can sec (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 2) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 2) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin2 : forall mode Q R M V B e M0 K,
    half 2 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (131072 <= L < 262144)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch mode Q 2 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 131072 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 266240 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 266240%Z 131136%Z (Z.to_nat 131072) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 131136)%Z with (bv_unsigned B + 64 + 131072)%Z in SOKb by lia.
    replace (Z.to_nat 131072) with (Z.to_nat (262144 - 131072)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 64 (ELit 131072) 2%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 2%nat) with (gblobs content 2%nat) in HELD. rewrite (gblobs_hb 2) in HELD by lia. change (held_of 2) with 131072%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 131072) R M (bv_unsigned sp0) (bv_unsigned B + 64) 131072 262144 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 64 + 131072), 131072%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a [O1 [O2 [O3 _]]]. cbn [outside loop_regions]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !(u_small (bv_unsigned B + 64 + 131072)) in * by lia. lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 131136 131072)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 131136)%Z with (bv_unsigned B + 64 + 131072)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtautoF). regq HR.
      + exact Q22.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 2)%Z with (bv_unsigned B + 64)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 64) 131072); try lia; [|exact PM].
        replace (Z.to_nat 131072) with (length (pref 131072 content)) by (pose proof (pref_length 131072 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 42)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 2) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.

End H0ReadF2.

(* [comment removed for export] *)
Module H0ReadF3.

(* [comment removed for export] *)

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX true.

Section F.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb bw gm B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)).

  Definition full_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG (cap_of j') V)).

  Theorem fill3 : forall mode Q R M V B e M0 K,
    half 3 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (524288 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch mode Q 3 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 262144 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 528384 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 528384%Z 262224%Z (Z.to_nat 262144) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 262224)%Z with (bv_unsigned B + 80 + 262144)%Z in SOKb by lia.
    replace (Z.to_nat 262144) with (Z.to_nat (524288 - 262144)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 80 (ELit 262144) 4%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 4%nat) with (gblobs content 4%nat) in HELD. rewrite (gblobs_hb 3) in HELD by lia. change (held_of 3) with 262144%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 262144) R M (bv_unsigned sp0) (bv_unsigned B + 80) 262144 524288 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((524288 - 262144)%Z) with (262144%Z) in FR. change ((524288 - 262144)%Z) with (262144%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 262224 262144)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 262224)%Z with (bv_unsigned B + 80 + 262144)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 262144 (dropz 262144 content))) = 262144%Z)
        by (pose proof (pref_length 262144 (dropz 262144 content) ltac:(lia)); pose proof (dropz_length 262144 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 262224) (ELit 262144) 5%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 262224 262144 5%nat (pref 262144 (dropz 262144 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 5%nat) with (gblobs content 5%nat). rewrite (gblobs_cb 3) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 262144 (dropz 262144 content))) with (Z.to_nat 262144) by lia.
          replace (bv_unsigned B + 262224)%Z with (bv_unsigned B + 80 + 262144)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb SW VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 74%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 80)) (ridx 23) (bx 80)) (ridx 19) (ELit 524288)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; ELit 0] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb bw gm L B e can sec (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 3) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 3) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin3 : forall mode Q R M V B e M0 K,
    half 3 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (262144 <= L < 524288)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch mode Q 3 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 262144 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 528384 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 528384%Z 262224%Z (Z.to_nat 262144) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 262224)%Z with (bv_unsigned B + 80 + 262144)%Z in SOKb by lia.
    replace (Z.to_nat 262144) with (Z.to_nat (524288 - 262144)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 80 (ELit 262144) 4%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 4%nat) with (gblobs content 4%nat) in HELD. rewrite (gblobs_hb 3) in HELD by lia. change (held_of 3) with 262144%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 262144) R M (bv_unsigned sp0) (bv_unsigned B + 80) 262144 524288 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 80 + 262144), 262144%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a [O1 [O2 [O3 _]]]. cbn [outside loop_regions]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !(u_small (bv_unsigned B + 80 + 262144)) in * by lia. lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 262224 262144)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 262224)%Z with (bv_unsigned B + 80 + 262144)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtautoF). regq HR.
      + exact Q22.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 3)%Z with (bv_unsigned B + 80)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 80) 262144); try lia; [|exact PM].
        replace (Z.to_nat 262144) with (length (pref 262144 content)) by (pose proof (pref_length 262144 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 42)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 3) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.

End H0ReadF3.

(* [comment removed for export] *)
Module H0ReadF4.

(* [comment removed for export] *)

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX true.

Section F.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb bw gm B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)).

  Definition full_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG (cap_of j') V)).

  Theorem fill4 : forall mode Q R M V B e M0 K,
    half 4 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (1048576 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch mode Q 4 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 524288 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 1052672 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 1052672%Z 524384%Z (Z.to_nat 524288) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 524384)%Z with (bv_unsigned B + 96 + 524288)%Z in SOKb by lia.
    replace (Z.to_nat 524288) with (Z.to_nat (1048576 - 524288)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 96 (ELit 524288) 6%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 6%nat) with (gblobs content 6%nat) in HELD. rewrite (gblobs_hb 4) in HELD by lia. change (held_of 4) with 524288%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 524288) R M (bv_unsigned sp0) (bv_unsigned B + 96) 524288 1048576 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((1048576 - 524288)%Z) with (524288%Z) in FR. change ((1048576 - 524288)%Z) with (524288%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 524384 524288)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 524384)%Z with (bv_unsigned B + 96 + 524288)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 524288 (dropz 524288 content))) = 524288%Z)
        by (pose proof (pref_length 524288 (dropz 524288 content) ltac:(lia)); pose proof (dropz_length 524288 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 524384) (ELit 524288) 7%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 524384 524288 7%nat (pref 524288 (dropz 524288 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 7%nat) with (gblobs content 7%nat). rewrite (gblobs_cb 4) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 524288 (dropz 524288 content))) with (Z.to_nat 524288) by lia.
          replace (bv_unsigned B + 524384)%Z with (bv_unsigned B + 96 + 524288)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb SW VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 74%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 96)) (ridx 23) (bx 96)) (ridx 19) (ELit 1048576)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; ELit 0] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb bw gm L B e can sec (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 4) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 4) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin4 : forall mode Q R M V B e M0 K,
    half 4 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (524288 <= L < 1048576)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch mode Q 4 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 524288 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 1052672 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 1052672%Z 524384%Z (Z.to_nat 524288) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 524384)%Z with (bv_unsigned B + 96 + 524288)%Z in SOKb by lia.
    replace (Z.to_nat 524288) with (Z.to_nat (1048576 - 524288)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 96 (ELit 524288) 6%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 6%nat) with (gblobs content 6%nat) in HELD. rewrite (gblobs_hb 4) in HELD by lia. change (held_of 4) with 524288%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 524288) R M (bv_unsigned sp0) (bv_unsigned B + 96) 524288 1048576 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 96 + 524288), 524288%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a [O1 [O2 [O3 _]]]. cbn [outside loop_regions]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !(u_small (bv_unsigned B + 96 + 524288)) in * by lia. lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 524384 524288)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 524384)%Z with (bv_unsigned B + 96 + 524288)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtautoF). regq HR.
      + exact Q22.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 4)%Z with (bv_unsigned B + 96)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 96) 524288); try lia; [|exact PM].
        replace (Z.to_nat 524288) with (length (pref 524288 content)) by (pose proof (pref_length 524288 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 42)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 4) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.

End H0ReadF4.

(* [comment removed for export] *)
Module H0ReadF5.

(* [comment removed for export] *)

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX true.

Section F.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb bw gm B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)).

  Definition full_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG (cap_of j') V)).

  Theorem fill5 : forall mode Q R M V B e M0 K,
    half 5 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (2097152 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch mode Q 5 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 1048576 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 2101248 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 2101248%Z 1048688%Z (Z.to_nat 1048576) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z in SOKb by lia.
    replace (Z.to_nat 1048576) with (Z.to_nat (2097152 - 1048576)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 112 (ELit 1048576) 8%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 8%nat) with (gblobs content 8%nat) in HELD. rewrite (gblobs_hb 5) in HELD by lia. change (held_of 5) with 1048576%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 1048576) R M (bv_unsigned sp0) (bv_unsigned B + 112) 1048576 2097152 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((2097152 - 1048576)%Z) with (1048576%Z) in FR. change ((2097152 - 1048576)%Z) with (1048576%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 1048688 1048576)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 1048576 (dropz 1048576 content))) = 1048576%Z)
        by (pose proof (pref_length 1048576 (dropz 1048576 content) ltac:(lia)); pose proof (dropz_length 1048576 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 1048688) (ELit 1048576) 9%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 1048688 1048576 9%nat (pref 1048576 (dropz 1048576 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 9%nat) with (gblobs content 9%nat). rewrite (gblobs_cb 5) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 1048576 (dropz 1048576 content))) with (Z.to_nat 1048576) by lia.
          replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb SW VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 74%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 112)) (ridx 23) (bx 112)) (ridx 19) (ELit 2097152)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; ELit 0] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb bw gm L B e can sec (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 5) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 5) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin5 : forall mode Q R M V B e M0 K,
    half 5 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (1048576 <= L < 2097152)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch mode Q 5 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 1048576 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 2101248 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 2101248%Z 1048688%Z (Z.to_nat 1048576) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z in SOKb by lia.
    replace (Z.to_nat 1048576) with (Z.to_nat (2097152 - 1048576)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 112 (ELit 1048576) 8%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 8%nat) with (gblobs content 8%nat) in HELD. rewrite (gblobs_hb 5) in HELD by lia. change (held_of 5) with 1048576%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 1048576) R M (bv_unsigned sp0) (bv_unsigned B + 112) 1048576 2097152 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 112 + 1048576), 1048576%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a [O1 [O2 [O3 _]]]. cbn [outside loop_regions]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !(u_small (bv_unsigned B + 112 + 1048576)) in * by lia. lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 1048688 1048576)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtautoF). regq HR.
      + exact Q22.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 5)%Z with (bv_unsigned B + 112)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 112) 1048576); try lia; [|exact PM].
        replace (Z.to_nat 1048576) with (length (pref 1048576 content)) by (pose proof (pref_length 1048576 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 42)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 5) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.

End H0ReadF5.

(* [comment removed for export] *)
Module H0ReadF6.

(* [comment removed for export] *)

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX true.

Section F.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb bw gm B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)).

  Definition full_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG (cap_of j') V)).

  Theorem fill6 : forall mode Q R M V B e M0 K,
    half 6 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (4194304 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch mode Q 6 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 2097152 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 4198400 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 4198400%Z 2097280%Z (Z.to_nat 2097152) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 2097280)%Z with (bv_unsigned B + 128 + 2097152)%Z in SOKb by lia.
    replace (Z.to_nat 2097152) with (Z.to_nat (4194304 - 2097152)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 128 (ELit 2097152) 10%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 10%nat) with (gblobs content 10%nat) in HELD. rewrite (gblobs_hb 6) in HELD by lia. change (held_of 6) with 2097152%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 2097152) R M (bv_unsigned sp0) (bv_unsigned B + 128) 2097152 4194304 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((4194304 - 2097152)%Z) with (2097152%Z) in FR. change ((4194304 - 2097152)%Z) with (2097152%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 2097280 2097152)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 2097280)%Z with (bv_unsigned B + 128 + 2097152)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 2097152 (dropz 2097152 content))) = 2097152%Z)
        by (pose proof (pref_length 2097152 (dropz 2097152 content) ltac:(lia)); pose proof (dropz_length 2097152 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 2097280) (ELit 2097152) 11%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 2097280 2097152 11%nat (pref 2097152 (dropz 2097152 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 11%nat) with (gblobs content 11%nat). rewrite (gblobs_cb 6) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 2097152 (dropz 2097152 content))) with (Z.to_nat 2097152) by lia.
          replace (bv_unsigned B + 2097280)%Z with (bv_unsigned B + 128 + 2097152)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb SW VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 74%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 128)) (ridx 23) (bx 128)) (ridx 19) (ELit 4194304)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; ELit 0] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb bw gm L B e can sec (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 6) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 6) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin6 : forall mode Q R M V B e M0 K,
    half 6 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (2097152 <= L < 4194304)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch mode Q 6 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 2097152 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 4198400 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 4198400%Z 2097280%Z (Z.to_nat 2097152) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 2097280)%Z with (bv_unsigned B + 128 + 2097152)%Z in SOKb by lia.
    replace (Z.to_nat 2097152) with (Z.to_nat (4194304 - 2097152)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 128 (ELit 2097152) 10%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 10%nat) with (gblobs content 10%nat) in HELD. rewrite (gblobs_hb 6) in HELD by lia. change (held_of 6) with 2097152%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 2097152) R M (bv_unsigned sp0) (bv_unsigned B + 128) 2097152 4194304 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 128 + 2097152), 2097152%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a [O1 [O2 [O3 _]]]. cbn [outside loop_regions]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !(u_small (bv_unsigned B + 128 + 2097152)) in * by lia. lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 2097280 2097152)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 2097280)%Z with (bv_unsigned B + 128 + 2097152)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtautoF). regq HR.
      + exact Q22.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 6)%Z with (bv_unsigned B + 128)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 128) 2097152); try lia; [|exact PM].
        replace (Z.to_nat 2097152) with (length (pref 2097152 content)) by (pose proof (pref_length 2097152 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 42)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 6) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.

End H0ReadF6.

(* [comment removed for export] *)
Module H0ReadF7.

(* [comment removed for export] *)

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX true.

Section F.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb bw gm B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)).

  Definition full_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG (cap_of j') V)).

  Theorem fill7 : forall mode Q R M V B e M0 K,
    half 7 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (8388608 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch mode Q 7 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 4194304 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 8392704 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 8392704%Z 4194448%Z (Z.to_nat 4194304) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 4194448)%Z with (bv_unsigned B + 144 + 4194304)%Z in SOKb by lia.
    replace (Z.to_nat 4194304) with (Z.to_nat (8388608 - 4194304)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 144 (ELit 4194304) 12%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 12%nat) with (gblobs content 12%nat) in HELD. rewrite (gblobs_hb 7) in HELD by lia. change (held_of 7) with 4194304%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 4194304) R M (bv_unsigned sp0) (bv_unsigned B + 144) 4194304 8388608 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((8388608 - 4194304)%Z) with (4194304%Z) in FR. change ((8388608 - 4194304)%Z) with (4194304%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 4194448 4194304)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 4194448)%Z with (bv_unsigned B + 144 + 4194304)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 4194304 (dropz 4194304 content))) = 4194304%Z)
        by (pose proof (pref_length 4194304 (dropz 4194304 content) ltac:(lia)); pose proof (dropz_length 4194304 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 4194448) (ELit 4194304) 13%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 4194448 4194304 13%nat (pref 4194304 (dropz 4194304 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 13%nat) with (gblobs content 13%nat). rewrite (gblobs_cb 7) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 4194304 (dropz 4194304 content))) with (Z.to_nat 4194304) by lia.
          replace (bv_unsigned B + 4194448)%Z with (bv_unsigned B + 144 + 4194304)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb SW VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 74%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 144)) (ridx 23) (bx 144)) (ridx 19) (ELit 8388608)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; ELit 0] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb bw gm L B e can sec (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 7) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 7) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin7 : forall mode Q R M V B e M0 K,
    half 7 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (4194304 <= L < 8388608)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch mode Q 7 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 4194304 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 8392704 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 8392704%Z 4194448%Z (Z.to_nat 4194304) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 4194448)%Z with (bv_unsigned B + 144 + 4194304)%Z in SOKb by lia.
    replace (Z.to_nat 4194304) with (Z.to_nat (8388608 - 4194304)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 144 (ELit 4194304) 12%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 12%nat) with (gblobs content 12%nat) in HELD. rewrite (gblobs_hb 7) in HELD by lia. change (held_of 7) with 4194304%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 4194304) R M (bv_unsigned sp0) (bv_unsigned B + 144) 4194304 8388608 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 144 + 4194304), 4194304%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a [O1 [O2 [O3 _]]]. cbn [outside loop_regions]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !(u_small (bv_unsigned B + 144 + 4194304)) in * by lia. lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 4194448 4194304)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 4194448)%Z with (bv_unsigned B + 144 + 4194304)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtautoF). regq HR.
      + exact Q22.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 7)%Z with (bv_unsigned B + 144)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 144) 4194304); try lia; [|exact PM].
        replace (Z.to_nat 4194304) with (length (pref 4194304 content)) by (pose proof (pref_length 4194304 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 42)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 7) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.

End H0ReadF7.

(* [comment removed for export] *)
Module H0ReadF8.

(* [comment removed for export] *)

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX true.

Section F.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb bw gm B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)).

  Definition full_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG (cap_of j') V)).

  Theorem fill8 : forall mode Q R M V B e M0 K,
    half 8 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (16777216 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch mode Q 8 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 8388608 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 16781312 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 16781312%Z 8388768%Z (Z.to_nat 8388608) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 8388768)%Z with (bv_unsigned B + 160 + 8388608)%Z in SOKb by lia.
    replace (Z.to_nat 8388608) with (Z.to_nat (16777216 - 8388608)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 160 (ELit 8388608) 14%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 14%nat) with (gblobs content 14%nat) in HELD. rewrite (gblobs_hb 8) in HELD by lia. change (held_of 8) with 8388608%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 8388608) R M (bv_unsigned sp0) (bv_unsigned B + 160) 8388608 16777216 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((16777216 - 8388608)%Z) with (8388608%Z) in FR. change ((16777216 - 8388608)%Z) with (8388608%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 8388768 8388608)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 8388768)%Z with (bv_unsigned B + 160 + 8388608)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 8388608 (dropz 8388608 content))) = 8388608%Z)
        by (pose proof (pref_length 8388608 (dropz 8388608 content) ltac:(lia)); pose proof (dropz_length 8388608 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 8388768) (ELit 8388608) 15%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 8388768 8388608 15%nat (pref 8388608 (dropz 8388608 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 15%nat) with (gblobs content 15%nat). rewrite (gblobs_cb 8) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 8388608 (dropz 8388608 content))) with (Z.to_nat 8388608) by lia.
          replace (bv_unsigned B + 8388768)%Z with (bv_unsigned B + 160 + 8388608)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb SW VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 74%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 160)) (ridx 23) (bx 160)) (ridx 19) (ELit 16777216)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; ELit 0] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb bw gm L B e can sec (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 8) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 8) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin8 : forall mode Q R M V B e M0 K,
    half 8 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (8388608 <= L < 16777216)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch mode Q 8 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 8388608 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 16781312 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 16781312%Z 8388768%Z (Z.to_nat 8388608) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 8388768)%Z with (bv_unsigned B + 160 + 8388608)%Z in SOKb by lia.
    replace (Z.to_nat 8388608) with (Z.to_nat (16777216 - 8388608)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 160 (ELit 8388608) 14%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 14%nat) with (gblobs content 14%nat) in HELD. rewrite (gblobs_hb 8) in HELD by lia. change (held_of 8) with 8388608%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 8388608) R M (bv_unsigned sp0) (bv_unsigned B + 160) 8388608 16777216 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 160 + 8388608), 8388608%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a [O1 [O2 [O3 _]]]. cbn [outside loop_regions]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !(u_small (bv_unsigned B + 160 + 8388608)) in * by lia. lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 8388768 8388608)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 8388768)%Z with (bv_unsigned B + 160 + 8388608)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtautoF). regq HR.
      + exact Q22.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 8)%Z with (bv_unsigned B + 160)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 160) 8388608); try lia; [|exact PM].
        replace (Z.to_nat 8388608) with (length (pref 8388608 content)) by (pose proof (pref_length 8388608 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 42)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 8) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.

End H0ReadF8.

(* [comment removed for export] *)
Module H0ReadF9.

(* [comment removed for export] *)

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX true.

Section F.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb bw gm B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)).

  Definition full_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG (cap_of j') V)).

  Theorem fill9 : forall mode Q R M V B e M0 K,
    half 9 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (33554432 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch mode Q 9 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 16777216 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 33558528 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 33558528%Z 16777392%Z (Z.to_nat 16777216) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 16777392)%Z with (bv_unsigned B + 176 + 16777216)%Z in SOKb by lia.
    replace (Z.to_nat 16777216) with (Z.to_nat (33554432 - 16777216)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 176 (ELit 16777216) 16%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 16%nat) with (gblobs content 16%nat) in HELD. rewrite (gblobs_hb 9) in HELD by lia. change (held_of 9) with 16777216%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 16777216) R M (bv_unsigned sp0) (bv_unsigned B + 176) 16777216 33554432 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((33554432 - 16777216)%Z) with (16777216%Z) in FR. change ((33554432 - 16777216)%Z) with (16777216%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 16777392 16777216)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 16777392)%Z with (bv_unsigned B + 176 + 16777216)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 16777216 (dropz 16777216 content))) = 16777216%Z)
        by (pose proof (pref_length 16777216 (dropz 16777216 content) ltac:(lia)); pose proof (dropz_length 16777216 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 16777392) (ELit 16777216) 17%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 16777392 16777216 17%nat (pref 16777216 (dropz 16777216 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 17%nat) with (gblobs content 17%nat). rewrite (gblobs_cb 9) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 16777216 (dropz 16777216 content))) with (Z.to_nat 16777216) by lia.
          replace (bv_unsigned B + 16777392)%Z with (bv_unsigned B + 176 + 16777216)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb SW VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 74%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 176)) (ridx 23) (bx 176)) (ridx 19) (ELit 33554432)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; ELit 0] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb bw gm L B e can sec (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 9) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 9) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin9 : forall mode Q R M V B e M0 K,
    half 9 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (16777216 <= L < 33554432)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch mode Q 9 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 16777216 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 33558528 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 33558528%Z 16777392%Z (Z.to_nat 16777216) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 16777392)%Z with (bv_unsigned B + 176 + 16777216)%Z in SOKb by lia.
    replace (Z.to_nat 16777216) with (Z.to_nat (33554432 - 16777216)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 176 (ELit 16777216) 16%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 16%nat) with (gblobs content 16%nat) in HELD. rewrite (gblobs_hb 9) in HELD by lia. change (held_of 9) with 16777216%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 16777216) R M (bv_unsigned sp0) (bv_unsigned B + 176) 16777216 33554432 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 176 + 16777216), 16777216%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a [O1 [O2 [O3 _]]]. cbn [outside loop_regions]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !(u_small (bv_unsigned B + 176 + 16777216)) in * by lia. lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 16777392 16777216)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 16777392)%Z with (bv_unsigned B + 176 + 16777216)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtautoF). regq HR.
      + exact Q22.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 9)%Z with (bv_unsigned B + 176)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 176) 16777216); try lia; [|exact PM].
        replace (Z.to_nat 16777216) with (length (pref 16777216 content)) by (pose proof (pref_length 16777216 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 42)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 9) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.

End H0ReadF9.

(* [comment removed for export] *)
Module H0ReadF10.

(* [comment removed for export] *)

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX true.

Section F.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb bw gm B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)).

  Definition full_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG (cap_of j') V)).

  Theorem fill10 : forall mode Q R M V B e M0 K,
    half 10 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (67108864 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch mode Q 10 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 33554432 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 67112960 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 67112960%Z 33554624%Z (Z.to_nat 33554432) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 33554624)%Z with (bv_unsigned B + 192 + 33554432)%Z in SOKb by lia.
    replace (Z.to_nat 33554432) with (Z.to_nat (67108864 - 33554432)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 192 (ELit 33554432) 18%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 18%nat) with (gblobs content 18%nat) in HELD. rewrite (gblobs_hb 10) in HELD by lia. change (held_of 10) with 33554432%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 33554432) R M (bv_unsigned sp0) (bv_unsigned B + 192) 33554432 67108864 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((67108864 - 33554432)%Z) with (33554432%Z) in FR. change ((67108864 - 33554432)%Z) with (33554432%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 33554624 33554432)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 33554624)%Z with (bv_unsigned B + 192 + 33554432)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 33554432 (dropz 33554432 content))) = 33554432%Z)
        by (pose proof (pref_length 33554432 (dropz 33554432 content) ltac:(lia)); pose proof (dropz_length 33554432 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 33554624) (ELit 33554432) 19%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 33554624 33554432 19%nat (pref 33554432 (dropz 33554432 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 19%nat) with (gblobs content 19%nat). rewrite (gblobs_cb 10) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 33554432 (dropz 33554432 content))) with (Z.to_nat 33554432) by lia.
          replace (bv_unsigned B + 33554624)%Z with (bv_unsigned B + 192 + 33554432)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb SW VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 74%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 192)) (ridx 23) (bx 192)) (ridx 19) (ELit 67108864)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; ELit 0] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb bw gm L B e can sec (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 10) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 10) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin10 : forall mode Q R M V B e M0 K,
    half 10 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (33554432 <= L < 67108864)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch mode Q 10 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 33554432 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 67112960 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 67112960%Z 33554624%Z (Z.to_nat 33554432) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 33554624)%Z with (bv_unsigned B + 192 + 33554432)%Z in SOKb by lia.
    replace (Z.to_nat 33554432) with (Z.to_nat (67108864 - 33554432)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 192 (ELit 33554432) 18%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 18%nat) with (gblobs content 18%nat) in HELD. rewrite (gblobs_hb 10) in HELD by lia. change (held_of 10) with 33554432%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 33554432) R M (bv_unsigned sp0) (bv_unsigned B + 192) 33554432 67108864 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 192 + 33554432), 33554432%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a [O1 [O2 [O3 _]]]. cbn [outside loop_regions]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !(u_small (bv_unsigned B + 192 + 33554432)) in * by lia. lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 33554624 33554432)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 33554624)%Z with (bv_unsigned B + 192 + 33554432)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtautoF). regq HR.
      + exact Q22.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 10)%Z with (bv_unsigned B + 192)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 192) 33554432); try lia; [|exact PM].
        replace (Z.to_nat 33554432) with (length (pref 33554432 content)) by (pose proof (pref_length 33554432 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 42)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 10) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.

  (* [comment removed for export] *)
  Theorem refused10 : forall R M V B e M0 TREF,
    full 10 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    (forall R' M' off V', oom_leaf sp0 M0 R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0xe1bf8) M' (seg_rom RSEGS)) (modelG off V')) TREF) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG 67108864 V)) TREF.
  Proof.
    intros R M V B e M0 TREF ST HspR HREF.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => set (M1 := Mc) in * end.
    (* [comment removed for export] *)
    pose proof (conj HK I) as HKb. run_block_keep fscr0 42%nat.
    lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mn _) _) _ =>
      assert (PRES2 : pres M0 Mn sp0)
        by (rewrite EQM; eapply (pres_mem_denot_trans E M0 M1 _ _ sp0 (proj1 HKb)); [subst E; exact P0 | exact HspR | vm_compute; reflexivity | exact PRES]) end.
    clear HKb.
    apply HREF. split; [|split; [|split; [|split]]].
    + regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
    + regv HR (3 : reg). reflexivity.
    + regv HR (4 : reg). reflexivity.
    + exact PRES2.
    + intros d m Hd Hm.
      lazymatch type of HK with know_ok _ ?E' ?Mc ?kn =>
        let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in
        pose proof (kwr_store_ok RSEGS E' Mc kn i (EVar 0) (-8388608)%Z 8388608%Z (-8388608 + d)%Z m HK eq_refl ltac:(lia) ltac:(lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. subst E. cbn [ev] in ST. rewrite P0 in ST.
      replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia. exact ST.
  Qed.
End F.

End H0ReadF10.

(* [comment removed for export] *)

(* [comment removed for export] *)

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FFUEL FSTOPS scr NX true.

Section F.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb bw gm B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1aa0) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)).

  Definition full_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG (cap_of j') V)).

  Theorem fill1 : forall mode Q R M V B e M0 K,
    half 1 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (131072 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch mode Q 1 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 65536 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 135168 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 135168%Z 65584%Z (Z.to_nat 65536) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 65584)%Z with (bv_unsigned B + 48 + 65536)%Z in SOKb by lia.
    replace (Z.to_nat 65536) with (Z.to_nat (131072 - 65536)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 48 (ELit 65536) 0%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 0%nat) with (gblobs content 0%nat) in HELD. rewrite (gblobs_hb 1) in HELD by lia. change (held_of 1) with 65536%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 65536) R M (bv_unsigned sp0) (bv_unsigned B + 48) 65536 131072 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((131072 - 65536)%Z) with (65536%Z) in FR. change ((131072 - 65536)%Z) with (65536%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 65584 65536)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 65584)%Z with (bv_unsigned B + 48 + 65536)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 65536 (dropz 65536 content))) = 65536%Z)
        by (pose proof (pref_length 65536 (dropz 65536 content) ltac:(lia)); pose proof (dropz_length 65536 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 65584) (ELit 65536) 1%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 65584 65536 1%nat (pref 65536 (dropz 65536 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 1%nat) with (gblobs content 1%nat). rewrite (gblobs_cb 1) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 65536 (dropz 65536 content))) with (Z.to_nat 65536) by lia.
          replace (bv_unsigned B + 65584)%Z with (bv_unsigned B + 48 + 65536)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb SW VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 74%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 48)) (ridx 23) (bx 48)) (ridx 19) (ELit 131072)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; ELit 0] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb bw gm L B e can sec (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 1) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 1) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin1 : forall mode Q R M V B e M0 K,
    half 1 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (65536 <= L < 131072)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch mode Q 1 M0 K ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG 65536 V)).
  Proof.
    intros mode Q R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; can; sec; Z_to_bv 64 0] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off edenot ev] in KBD. subst E. cbn [ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + 135168 <= bv_unsigned sp0 - 8388608)%Z) by lia. clear KBD. rename KBD' into KBD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 135168%Z 65584%Z (Z.to_nat 65536) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 65584)%Z with (bv_unsigned B + 48 + 65536)%Z in SOKb by lia.
    replace (Z.to_nat 65536) with (Z.to_nat (131072 - 65536)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    assert (SW : stage_writable M).
    { intros d m Hd Hm.
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (ELit 0) 0x31e000%Z 1%Z) in exact i) (ELit 0) 0x31e000%Z 0x36000%Z (STAGE + d)%Z m HK eq_refl ltac:(unfold STAGE; lia) ltac:(unfold STAGE; lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
      rewrite Z.add_0_l in ST. exact ST. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 48 (ELit 65536) 0%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 0%nat) with (gblobs content 0%nat) in HELD. rewrite (gblobs_hb 1) in HELD by lia. change (held_of 1) with 65536%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop_mid path content stdin0 fs0 tid V Hfile mode Q (Z.to_nat 65536) R M (bv_unsigned sp0) (bv_unsigned B + 48) 65536 131072 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - exact SOKb.
    - exact SW.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q19 & Q22 & Q23 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 48 + 65536), 65536%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a [O1 [O2 [O3 _]]]. cbn [outside loop_regions]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !(u_small (bv_unsigned B + 48 + 65536)) in * by lia. lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 5) 65584 65536)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 65584)%Z with (bv_unsigned B + 48 + 65536)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtautoF). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtautoF). regq HR.
      + exact Q22.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 1)%Z with (bv_unsigned B + 48)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 48) 65536); try lia; [|exact PM].
        replace (Z.to_nat 65536) with (length (pref 65536 content)) by (pose proof (pref_length 65536 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 42)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb bw gm (Z.of_nat (length content)) B e can sec extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 1) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

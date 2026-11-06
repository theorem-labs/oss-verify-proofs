(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SpecConsts.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes
  MmapSim AllocSim FileSim AgentLib MemSplit Frame StreamSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib UbMemcpyBase UbMemcpy
  MallocDefs UbEnframeBase UbEnframe UbGetMeta
  RefNodes LibKnowFrame LibKnowXfer RefReadLib UbReadBase UbReadStage UbReadChunk.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := ImgU.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.

Definition RFUEL : nat := 5000.
Definition RSTOPS : list Z :=
  [0xa6e20; 0xa73a0; 0xa787c; 0xa6d24; 0x32ad4; 0x99ff4; 0x98c20; 0x9678c; 0x32730; 0x3289c; 0x3287c; 0x32700]%Z.   (* [comment removed for export] *)
Definition scr0 : scripts := SCR [] [] [].
Definition scrT : scripts := SCR [true] [] [].
End FPW_1.


#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.
Section FPW_2. Context {fx : PropExec.FPState}.


#[using="Type"] Lemma bv_add_0_l : forall x : word, (Z_to_bv 64 0 + x)%bv = x.
Proof. intros x. apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_l. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
End FPW_2.

Ltac kwr_solve HK :=
  lazymatch goal with |- store_ok _ _ (adenot _ (SA ?b ?k)) ?m = true =>
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let i := kidx kn (is_kwr_cov b k 1%Z) in
      eapply (kwr_store_ok segs E M kn i b _ _ k m HK eq_refl); [lia | try lia]
    end end.
Section FPW_3. Context {fx : PropExec.FPState}.


#[using="Type"] Lemma lxor_m1_bound : forall x : Z, (0 <= x < 2 ^ 64)%Z -> (x <> 2 ^ 64 - 1)%Z ->
  (0 < Z.lxor x (2 ^ 64 - 1) < 2 ^ 64)%Z.
Proof.
  intros x Hx Hne.
  assert (NZ : Z.lxor x (2 ^ 64 - 1) <> 0%Z) by (intros H0; apply Z.lxor_eq in H0; lia).
  assert (NN : (0 <= Z.lxor x (2 ^ 64 - 1))%Z) by (apply (proj2 (Z.lxor_nonneg _ _)); lia).
  split; [lia|].
  destruct (Z.eq_dec x 0) as [->|Hx0].
  - rewrite Z.lxor_0_l. lia.
  - apply (proj2 (Z.log2_lt_pow2 (Z.lxor x (2 ^ 64 - 1)) 64 ltac:(lia))).
    eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
    apply Z.max_lub_lt; [apply (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia))); lia | apply (proj1 (Z.log2_lt_pow2 (2 ^ 64 - 1) 64 ltac:(lia))); lia].
Qed.

#[using="Type"] Lemma xor_m1_ne0 : forall E (b : expr),
  (bv_unsigned (edenot E b) < 2 ^ 64 - 1)%Z ->
  branch_taken BC_NE (edenot E (EAlu ALU_XOR b (ELit (-1)))) (edenot E (ELit 0)) = true.
Proof.
  intros E b Hb. cbn [edenot]. rewrite alu_xor. unfold v_xor. cbn [branch_taken].
  apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq.
  pose proof (u64_range (edenot E b)) as Hr. set (x := edenot E b) in *.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1)%Z by (vm_compute; reflexivity).
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  pose proof (lxor_m1_bound (bv_unsigned x) Hr ltac:(lia)) as HB.
  rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition is_kzero_cov (b : expr) (k m : Z) (K : kentry) : bool :=
  match K with
  | KZero (SA c kk) (ELit l) => expr_eqb b c && Z.leb kk k && Z.leb (k + m) (kk + l) && Z.ltb l (2 ^ 64) && Z.leb 0 l
  | _ => false
  end.

#[using="Type"] Lemma kzero_byte : forall segs E M kn i b kk l (k : Z),
  know_ok segs E M kn -> nth_error kn i = Some (KZero (SA b kk) (ELit l)) ->
  (0 <= l < 2 ^ 64)%Z -> (kk <= k < kk + l)%Z ->
  M (Z_to_bv 64 (bv_unsigned (edenot E b) + k)) = Some (Z_to_bv 8 0).
Proof.
  intros segs E M kn i b kk l k HK Hn Hl Hk.
  pose proof (know_nth segs E M kn i _ HK Hn) as H. cbn [kentry_ok] in H. destruct H as [Hf Hz].
  unfold elenZ, estart in Hz. cbn [a_base a_off edenot] in Hz. rewrite u_small in Hz by lia.
  replace (bv_unsigned (edenot E b) + k)%Z with (bv_unsigned (edenot E b) + kk + (k - kk))%Z by lia.
  apply Hz. lia.
Qed.
End FPW_3.


Ltac kzero_at HK b k H :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
    let i := kidx kn (is_kzero_cov b k 1%Z) in
    lazymatch eval vm_compute in (nth_error kn i) with
    | Some (KZero (SA _ ?kk) (ELit ?l)) =>
        pose proof (kzero_byte segs E M kn i b kk l k HK eq_refl ltac:(lia) ltac:(lia)) as H
    end end.
Section FPW_4. Context {fx : PropExec.FPState}.


#[using="Type"] Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
Proof.
  unfold callee_saved. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

#[using="Type"] Lemma kimg_none : forall segs E M kn i lo hi,
  know_ok segs E M kn -> nth_error kn i = Some (KImg lo hi) ->
  forall a, (lo <= a < hi)%Z -> M (Z_to_bv 64 a) = None.
Proof.
  intros segs E M kn i lo hi HK Hn a Ha.
  pose proof (know_nth segs E M kn i _ HK Hn) as H. cbn [kentry_ok] in H. apply (proj2 (proj2 H)). exact Ha.
Qed.



(* [comment removed for export] *)
Definition gm_kept : list reg :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
#[using="Type"] Lemma gm_keeps_kept : forall a b, gm_keeps a b -> forall r : reg, In r gm_kept -> getr b r = getr a r.
Proof.
  intros a b K r Hr. apply K. unfold gm_clob. intros Hc.
  cbv [gm_kept In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [cbv [In] in Hc; intuition discriminate|]). exact Hr.
Qed.
#[using="Type"] Lemma gm_kept_no0 : ~ In (0%bv : reg) gm_kept.
Proof.
  unfold gm_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

Section G0.
  Variables (sp0 p1 mb gm can sec : word) (path content : list byte).   (* [comment removed for export] *)
  Variables (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (UbReadStage.modelG path stdin0 fs0 tid) (only parsing).
  #[local] Notation oom_branch := (UbReadStage.oom_branch sp0 path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  #[using="Type"] Lemma map_has_of_In : forall maps (a n : word), In (a, n) maps -> map_has maps a n = true.
  Proof.
    intros maps a n Hin. unfold map_has. apply existsb_exists. exists (a, n). split; [exact Hin|].
    cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
  Qed.

  #[using="content L"] Lemma In_map_has : forall maps (a n : word), map_has maps a n = true -> In (a, n) maps.
  Proof.
    intros maps a n H. unfold map_has in H. apply existsb_exists in H as ([b m] & Hin & Hb).
    cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2].
    assert (b = a) by (apply bv_eq; unfold bv_eqb in H1; lia).
    assert (m = n) by (apply bv_eq; unfold bv_eqb in H2; lia). subst. exact Hin.
  Qed.

  (* [comment removed for export] *)
  Definition half1_branch (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half 1 sp0 p1 mb gm L B e can sec content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32700) M (seg_rom RSEGS)) (modelG (held_of 1) V)) K.

  (* [comment removed for export] *)
  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  (* [comment removed for export] *)
  Ltac save_know HK := pose proof (conj HK I) as HKb.

  (* [comment removed for export] *)
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

  #[using="Type"] Theorem grow0 : forall R M (e : word) M0 K TOOM,
    full0 sp0 p1 mb gm L e can sec content M0 R M -> vm_pre VM sp0 mb gm ->
    (65536 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    (0x1000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0xe6000 <= bv_unsigned gm)%Z -> (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z -> (bv_unsigned gm mod 4096 = 0)%Z ->
    oom_branch M0 TOOM -> half1_branch M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x326c8) M (seg_rom RSEGS)) (modelG 65536 VM)) (t_alt2 TOOM K).
  Proof.
    intros R M e M0 K TOOM F0 VP HL64 Hsp Hmb0 Hmb1 Hmba Hgm0 Hgm1 Hgma HOOM HK1.
    assert (Hgm : (0xe6000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z /\ (bv_unsigned gm mod 4096 = 0)%Z) by (repeat split; assumption).
    assert (Hmb : (0x1000 <= bv_unsigned mb)%Z /\ (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z /\ (bv_unsigned mb mod 4096 = 0)%Z) by (repeat split; assumption).
    pose proof (proj1 Hsp) as HspR.
    destruct F0 as ((extra & HLx & HR & HK) & PRES).
    rename M0 into Minit.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L (Z_to_bv 64 0) e can sec extra) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals_RD; rewrite length_app; destruct extra; [discriminate|]; cbn [length tl] in HLx |- *; lia).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.   (* [comment removed for export] *)
    clearbody vals. clear HLx extra.
    norm_know HK. norm_regs HR.
    assert (EB1 : gblobs content 0%nat = pref 65536 content) by (apply (gblobs_fb 0); lia).
    assert (RL1 : length (pref 65536 content) = Z.to_nat 65536)
      by (pose proof (pref_length 65536 content ltac:(lia)); lia).
    (* [comment removed for export] *)
    pose (R0 := tt). pose (M0 := M).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 40%nat. note_pres HKb EQM PRES.
      destruct VP as (Vres & Visp & Vlim & Vhas & Vsz & Vlen & Vlive & Vcont & Vseps).
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x9a8e4) Mc MD ECALLW 131092 TOOM K fetch_9a72c is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 131092) with 135168%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | ];
          cbv [m_vmmaps UbReadStage.modelG mkModelA m_vm vmst_maps]; rewrite ?Vres, ?Vlim, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite target_alloc_limit_val. lia.
        * unfold init_sp_ok, sp_window_lo. rewrite Visp. lia.   (* [comment removed for export] *)
      + (* [comment removed for export] *)
        intros err Herr. cbn [mmap_errnos In] in Herr. destruct Herr as [<-|[]].
        rewrite v_addi_pc4 by lia. change (633060 + 4)%Z with 0x9a8e8%Z.
        lazymatch type of HR with regs_ok ?E _ _ =>
          pose proof (regs_set_a0 E _ _ (errno_ret ENOMEM) (ELit (- 12)) HR eq_refl) as HR2 end.
        clear HR. rename HR2 into HR.
        save_know HK. run_block_keep scr0 40%nat. note_pres HKb EQM PRES.
        apply HOOM. split; [|split; [|split; [|split]]].
        * regv HR (2 : reg). cbn [spx edenot ev]. rewrite alu_add, P0. unfold v_add. apply bv_eq.
          rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. f_equal; lia.
        * regv HR (3 : reg). reflexivity.
        * regv HR (4 : reg). reflexivity.
        * exact PRES.
        * intros d m Hd Hm.
          lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
            let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in
            pose proof (kwr_store_ok RSEGS E Mc kn i (EVar 0) (-8388608)%Z 8388608%Z (-8388608 + d)%Z m HK eq_refl ltac:(lia) ltac:(lia)) as ST end.
          unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. rewrite P0 in ST.
          replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia. exact ST.
      + (* [comment removed for export] *)
        intros B HG.
        change (page_round_up_Z 131092) with 135168%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (633060 + 4)%Z with 0x9a8e8%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        unfold alloc_top, stack_max_size in GC. unfold page_size in GA.
        cbv [m_vmmaps UbReadStage.modelG mkModelA m_vm vmst_maps] in GC. rewrite Visp in GC.   (* [comment removed for export] *)
        cbv [m_vmmaps UbReadStage.modelG mkModelA m_vm vmst_maps] in GF, GLv. rewrite Vres, rsegs_reserved in GF.
        (* [comment removed for export] *)
        assert (GB1 : (0xe6000 <= bv_unsigned B)%Z).
        { (* [comment removed for export] *)
          pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 139264) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X1.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 204800) (Z_to_bv 64 499712) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X2.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 704512) (Z_to_bv 64 28672) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X3.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 733184) (Z_to_bv 64 208896) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X1 by lia. rewrite !u_small in X2 by lia. rewrite !u_small in X3 by lia.
          rewrite !u_small in X by lia. pose proof (u64_range B). lia. }
        assert (GB2 : (bv_unsigned B + 135168 <= bv_unsigned gm \/ bv_unsigned gm + 69632 <= bv_unsigned B)%Z).
        { pose proof (region_free_In _ _ _ gm (Z_to_bv 64 69632) GF
                        ltac:(apply in_or_app; right; apply In_map_has; exact Vhas)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B + 135168 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B)%Z).
        { destruct Vcont as ([cb cs] & Cin & Cne & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK.
        assert (P40 : vals_ev (vals ++ [B]) 40 = B) by (rewrite <- HL; apply vals_ev_last).
        assert (P0' : vals_ev (vals ++ [B]) 0 = sp0) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
        assert (P1' : vals_ev (vals ++ [B]) 1 = p1) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
        assert (P2' : vals_ev (vals ++ [B]) 2 = mb) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
        assert (P3' : vals_ev (vals ++ [B]) 3 = gm) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
        assert (P4' : vals_ev (vals ++ [B]) 4 = Z_to_bv 64 L) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
        assert (P6' : vals_ev (vals ++ [B]) 6 = e) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
        assert (P7' : vals_ev (vals ++ [B]) 7 = can) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P7).
        assert (P8' : vals_ev (vals ++ [B]) 8 = sec) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P8).
        assert (HL1 : length (vals ++ [B]) = 41%nat) by (rewrite length_app, HL; reflexivity).
        set (vals1 := vals ++ [B]) in *. clearbody vals1.
        clear HL P0 P1 P2 P3 P4 P6 P7 P8 vals. rename vals1 into vals. rename HL1 into HL.
        rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P3' into P3. rename P4' into P4. rename P6' into P6. rename P7' into P7. rename P8' into P8.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD40 : adenot E (SA (EVar 40) 0) = B).
        { unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P40. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B (EVar 40) HR2 ltac:(cbn [edenot ev]; subst E; exact P40)) as HR. clear HR2.
        assert (KA40 : kentry_ok RSEGS E M1 (KAlign (EVar 40) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. exact GA. }
        assert (KR40 : kentry_ok RSEGS E M1 (KRange (EVar 40) 0xe6000 (CEIL - 135168))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. unfold CEIL. lia. }
        assert (KD40a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 40) 0) 135168 (SA (EVar 3) 0) 69632)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P40, P3. lia. }
        assert (KD40b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 40) 0) 135168 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P40, P2. lia. }
        assert (KD40c : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BELOW (SA (EVar 40) 0) 135168)).   (* [comment removed for export] *)
        { cbn [kentry_ok]. unfold estart, BELOW. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P40, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA40 (know_ok_cons _ _ _ _ _ KR40
                     (know_ok_cons _ _ _ _ _ KD40a (know_ok_cons _ _ _ _ _ KD40b (know_ok_cons _ _ _ _ _ KD40c HK2))))) as HK2'.
        clear KA40 KR40 KD40a KD40b KD40c HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 40) 0 135168 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD40 in HK3. clear HK2'.
        assert (KW40 : kentry_ok RSEGS E (zfill B (Z_to_bv 64 135168) M1) (KWr (SA (EVar 40) 0) 135168)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P40.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW40 HK3) as HK. clear KW40 HK3.
        norm_know HK.
        assert (PRES2 : pres Minit (zfill B (Z_to_bv 64 135168) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 135168); [lia | lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 41%nat.
        { (* [comment removed for export] *) apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P40. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4176%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P40 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 40) 12%Z Z12. kzero_at HK (EVar 40) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P40 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 2) (bv_unsigned mb + 4160) (bv_unsigned B) 139232 0 131072 0 0 135152 (bv_unsigned B + 16) 2) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact RW0.
          - replace (bv_unsigned B + 16 - 4)%Z with (bv_unsigned B + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B + 16 - 3)%Z with (bv_unsigned B + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B + 16 - 3)) with (adenot E (SA (EVar 40) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off edenot ev]; subst E; cbn [ev]; rewrite P40; f_equal; lia).
            kwr_solve HK.
          - intros j Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x1abc8 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x326dc)) by (apply bv_eq; vm_compute; reflexivity).
        assert (G1 : getr R2 1 = Z_to_bv 64 0x326dc) by (regv HR (1:reg); reflexivity).
        assert (G10 : getr R2 10 = Z_to_bv 64 (bv_unsigned mb + 4160)).
        { regv HR (10:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity. }
        assert (G11 : getr R2 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity).
        assert (G12 : getr R2 12 = Z_to_bv 64 131072) by (regv HR (12:reg); reflexivity).
        assert (G13 : getr R2 13 = Z_to_bv 64 2) by (regv HR (13:reg); reflexivity).
        destruct (ref_enframe R2 M2 (seg_rom RSEGS) (Z_to_bv 64 0x326dc) (Z_to_bv 64 2) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
          as (R3 & M3 & RUN & KEEP & A0 & FR & POST).
        clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13.
        replace (Z_to_bv 64 630772) with (0x99ff4 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD40. subst E.
        grow_vals HL (junk_vals R3) 73%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 40) (ELit 48))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev].
          subst E. cbn [ev]. rewrite P40. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        (* [comment removed for export] *)
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 40) 13) \/ estart E (SA (EVar 40) 13) + 135151 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P40 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 40) 13 135151 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (135152 - 4 - 131072 - 16 * 2))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (135152 * 0 / 16 + 2)%Z with 2%Z in Pm2 by (vm_compute; reflexivity).
        replace (135152 - 4 - 131072 - 16 * 2)%Z with 4044%Z in Pe4 by reflexivity.
        assert (EV40 : edenot E (EVar 40) = B) by (cbn [edenot ev]; subst E; cbn [ev]; exact P40).
        Ltac hdr_byte EV40 Pf off :=
          lazymatch type of EV40 with _ = ?B =>
          eapply (kword1_of_mem RSEGS _ _ (EVar 40) _ off _ EV40); [lia | lia | lia |
            lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
        Ltac hdr_word EV40 Pf off w z :=
          lazymatch type of EV40 with _ = ?B =>
          eapply (kword_intro RSEGS _ _ (EVar 40) _ off w (ELit z) (Z_to_bv 64 z) EV40 eq_refl); [lia | lia | lia | lia |
            lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 44) 1 (ELit 0))) by (hdr_byte EV40 Pm4 44%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 45) 1 (ELit 160))) by (hdr_byte EV40 Pm3 45%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 46) 2 (ELit 2))) by (hdr_word EV40 Pm2 46%Z 2%nat 2%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 131120) 1 (ELit 0))) by (hdr_byte EV40 Pzr 131120%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 135159) 1 (ELit 0))) by (hdr_byte EV40 Pe5 135159%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 135160) 4 (ELit 4044))) by (hdr_word EV40 Pe4 135160%Z 4%nat 4044%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 13) 1 (ELit 224))) by (hdr_byte EV40 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 40) 14) 2 (ELit 2))) by (hdr_word EV40 Ps2 14%Z 2%nat 2%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres Minit M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B + 13) 135151); [lia | lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 73%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 3) 32 (ELit 65536) 0%nat HK ltac:(vm_compute; reflexivity)) as SRC end.
        change (eb E 0%nat) with (gblobs content 0%nat) in SRC. rewrite EB1 in SRC.
        set (dst := adenot E (SA (EVar 40) 48)). set (src := adenot E (SA (EVar 3) 32)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B + 48)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P40, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned gm + 32)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P3, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 65536 (pref 65536 content)) end.
        { constructor.
          - lia.
          - exact RL1.
          - exact SRC.
          - subst dst. rewrite RL1. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x326f8)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x326f8) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 65536) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 65536 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x326f8) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 683552) with (0xa6e20 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 40) 48 0%nat (pref 65536 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P40, ?RL1; lia)
                        EB1 ltac:(rewrite RL1; lia) ltac:(rewrite RL1; lia)) as HK2 end.
        fold dst in HK2. rewrite RL1, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B + 48)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres Minit (wbytes M4 (Z_to_bv 64 (bv_unsigned B + 48)) (pref 65536 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B + 48) 65536); [lia | lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RL1 by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV40.
        grow_vals HL (junk_vals R5) 105%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR.
        norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 105%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat3 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 69632)%Z -> flat E (SA (EVar 3) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P3; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 3%nat 28%Z 1%nat Gb4. { apply Hflat3; lia. }
        krdv HK 3%nat 29%Z 1%nat Gb3. { apply Hflat3; lia. }
        krdv HK 3%nat 30%Z 2%nat Goff. { apply Hflat3; lia. }
        krdv HK 3%nat 0%Z 8%nat Gmeta. { apply Hflat3; lia. }
        krdv HK 2%nat 4136%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4144%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4148%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0xe5428%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P3 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        cbn [ev] in Gsec. rewrite P8 in Garea, Gsec.   (* [comment removed for export] *)
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned gm + 32) (bv_unsigned gm) (bv_unsigned mb + 4120) 0 5 1 72480 0 0 sec) end.   (* [comment removed for export] *)
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned gm + 32 - 4)%Z with (bv_unsigned gm + 28)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned gm + 32 - 3)%Z with (bv_unsigned gm + 29)%Z by lia. exact Gb3.
          - replace (bv_unsigned gm + 32 - 2)%Z with (bv_unsigned gm + 30)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4120)) with 4120%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4120 + 24)%Z with (bv_unsigned mb + 4144)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4120 + 28)%Z with (bv_unsigned mb + 4148)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4120) mod 4096 = 24)%Z)
              by (rewrite <- Zplus_mod_idemp_l, (proj2 (proj2 Hmb)); reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4120 - 24)%Z with (bv_unsigned mb + 4096)%Z by lia. exact Garea.
          - exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let j := kidx kn (is_kimg_cov 0x1abc8 96) in exact j) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned gm + 32) (bv_unsigned gm) (bv_unsigned mb + 4120) 0 5 1 72480 0 0).
        { constructor.
          all: try (change (w_lastidx 72480) with 0%Z); try (change (w_sizeclass 72480) with 44%Z);
               try (change (w_maplen 72480) with 17%Z); try (change (size_class 44) with 4680%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned gm mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact (proj2 (proj2 Hgm))]. }
          all: try lia.
          all: try reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat3.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x98a78)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned gm + 32))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; subst E; cbn [ev]; rewrite P3; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x98a78) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x98a78) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 625696) with (0x98c20 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 137%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4120)) (ridx 11) (ELit 1)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR.
        norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 137%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x9aa50) Mc MD ECALLW gm 69632 K fetch_9a898 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P3.
        * unfold page_size. exact (proj2 (proj2 Hgm)).
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 69632) with 69632%Z. rewrite task_size_val. lia.   (* [comment removed for export] *)
        * change (page_round_up_Z 69632) with 69632%Z. cbv [m_vmmaps mmap_model with_vmmaps UbReadStage.modelG mkModelA m_vm vmst_maps vm_maps]. apply map_has_cons. exact Vhas.
        * change (page_round_up_Z 69632) with 69632%Z.
          rewrite v_addi_pc4 by lia. change (0x9aa50 + 4)%Z with 0x9aa54%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD3 : adenot E (SA (EVar 3) 0) = gm).
          { unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P3. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 3) 0 69632 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P3; lia) ltac:(lia)) as HK2 end.
          rewrite AD3 in HK2. clear HK AD3. rename HK2 into HK.
          norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres Minit Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned gm) 69632); [lia | lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 137%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               UbReadStage.modelG mkModelA]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V _ _) _ _ _ _ _)) _ =>   (* [comment removed for export] *)
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x32700) Mc (seg_rom RSEGS)) (modelG (held_of 1) V)) K) end.
          unfold half1_branch in HK1. apply (HK1 _ _ _ B (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 40; EExt true 0 4 (EVar 6); EVar 7] ++ (EVar 8 :: tl srf));
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B (edenot E (EExt true 0 4 (EVar 6))) can sec (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 1) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 1) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- (* [comment removed for export] *)
            intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- (* [comment removed for export] *)
            match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- (* [comment removed for export] *)
            unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app tl].
            cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P40, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
            unfold vm_stage. cbn [vm_reserved vm_init_sp vm_limit vm_maps]. split; [exact Vres|]. split; [exact Visp|]. split; [exact Vlim|].
            assert (Hbg : bv_eqb B gm = false).
            { unfold bv_eqb. apply Z.eqb_neq. intros HH. lia. }
            exists (map_remove (vm_maps VM) gm). split; [|split; [|split; [|split; [|split; [|split]]]]].
            ++ change (nb_of 1) with 135168%Z. rewrite map_remove_skip; [reflexivity|]. intros HH. rewrite HH in Hbg. rewrite bv_eqb_refl in Hbg. discriminate.
            ++ apply incl_Forall with (l1 := vm_maps VM); [|exact Vsz]. unfold map_remove. apply incl_filter.
            ++ pose proof (map_remove_length (vm_maps VM) gm). lia.
            ++ pose proof (live_bytes_map_remove_le (vm_maps VM) gm). lia.
            ++ destruct Vcont as (pc & Cin & Cne & C1 & C2). exists pc. split; [|split; assumption].
               unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst] in Cne |- *.
               apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH. apply Cne. apply bv_eq. exact HH.
            ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 1) with 135168%Z.
               unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
               pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; exact Hq)) as X.
               rewrite u_small in X by lia. lia.
            ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.

End G0.
End FPW_4.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

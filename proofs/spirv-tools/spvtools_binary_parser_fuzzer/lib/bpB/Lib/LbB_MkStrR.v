(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts StrLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_ContStmt LbB_ContV4R LbB_StrPbR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition MS_ENTRY : Z := 0xea650.
Definition MS_EXIT : Z := 0xea788.
Definition MS_HEAD : Z := 0xea6f8.
Definition MS_RET : Z := 0xea7b4.

Definition MSSAVED : list reg := [24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.

Lemma w_mulp : forall k x, 0 <= k < 64 -> 0 <= x < 2 ^ 64 ->
  mul_div M_MUL (Z_to_bv 64 (2 ^ k)) (Z_to_bv 64 x) = Z_to_bv 64 ((2 ^ k * x) mod 2 ^ 64).
Proof.
  intros k x Hk Hx. apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  assert (0 < 2 ^ k < 2 ^ 64) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
  rewrite (Z.mod_small x), (Z.mod_small (2 ^ k)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma w_srlk : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k < 64 ->
  alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 k) = Z_to_bv 64 (x / 2 ^ k).
Proof.
  intros x k Hx Hk. apply bv_eq. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small x) by lia.
  assert (EK : bv_unsigned (bv_and (Z_to_bv 64 k) (Z_to_bv 64 63)) = k).
  { rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite (Z.mod_small k), (Z.mod_small 63) by lia.
    change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 6) with 64. lia. }
  rewrite EK.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.mod_small; [reflexivity|]. split; [apply Z.div_pos; lia|].
  apply (Z.le_lt_trans _ x); [apply Z.div_le_upper_bound; nia | lia].
Qed.

Lemma ms_byte1_w : forall x, 0 <= x < 2 ^ 32 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 281474976710656) (Z_to_bv 64 x)) (Z_to_bv 64 56) = Z_to_bv 64 ((x / 256) mod 256).
Proof.
  intros x Hx. change 281474976710656 with (2 ^ 48). rewrite w_mulp by lia.
  assert (E : (2 ^ 48 * x) mod 2 ^ 64 = (x mod 2 ^ 16) * 2 ^ 48).
  { rewrite (Z.mul_comm (2 ^ 48) x). change (2 ^ 64) with (2 ^ 16 * 2 ^ 48). rewrite Z.mul_mod_distr_r by lia. reflexivity. }
  rewrite E. pose proof (Z.mod_pos_bound x (2 ^ 16) ltac:(lia)).
  rewrite w_srlk by lia. f_equal. change (2 ^ 56) with (2 ^ 56). rewrite <- (byte1_via_shifts x Hx). reflexivity.
Qed.

Lemma ms_byte2_w : forall x, 0 <= x < 2 ^ 32 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 1099511627776) (Z_to_bv 64 x)) (Z_to_bv 64 56) = Z_to_bv 64 ((x / 256 / 256) mod 256).
Proof.
  intros x Hx. change 1099511627776 with (2 ^ 40). rewrite w_mulp by lia.
  assert (E : (2 ^ 40 * x) mod 2 ^ 64 = (x mod 2 ^ 24) * 2 ^ 40).
  { rewrite (Z.mul_comm (2 ^ 40) x). change (2 ^ 64) with (2 ^ 24 * 2 ^ 40). rewrite Z.mul_mod_distr_r by lia. reflexivity. }
  rewrite E. pose proof (Z.mod_pos_bound x (2 ^ 24) ltac:(lia)).
  rewrite w_srlk by lia. f_equal. rewrite <- (byte2_via_shifts x Hx). reflexivity.
Qed.

Lemma ms_byte3_w : forall x, 0 <= x < 2 ^ 32 ->
  alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 24) = Z_to_bv 64 ((x / 256 / 256 / 256) mod 256).
Proof. intros x Hx. rewrite w_srlk by lia. f_equal. apply byte3_val. exact Hx. Qed.

Lemma ms_and255_w : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 255) = Z_to_bv 64 (x mod 256).
Proof. intros x Hx. rewrite w_and by lia. f_equal. apply land_255. lia. Qed.

Lemma ms_andff00_w : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 65280) = Z_to_bv 64 (256 * ((x / 256) mod 256)).
Proof. intros x Hx. rewrite w_and by lia. f_equal. apply land_ff00. lia. Qed.

Lemma ms_andff0000_w : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 16711680) = Z_to_bv 64 (65536 * ((x / 256 / 256) mod 256)).
Proof. intros x Hx. rewrite w_and by lia. f_equal. apply land_ff0000. lia. Qed.

Ltac ms_sc :=
  cbn [sc_denot]; evs; unfold wz in *;
  rewrite ?ms_and255_w, ?ms_andff00_w, ?ms_andff0000_w, ?ms_byte3_w by lia;
  rewrite ?w_add, ?w_addm by lia;
  first [ rewrite br_eq by lia | rewrite br_ne by lia ];
  bool_lia.

Lemma ms_nullxor : forall w n, 0 <= w < 2 ^ 64 -> 0 <= n -> w + n < 2 ^ 64 -> (0 < n -> w <> 0) ->
  branch_taken BC_EQ (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 w)) (alu64 ALU_SLTU (Z_to_bv 64 (w + n)) (Z_to_bv 64 1)) = false.
Proof.
  intros w n Hw Hn Hwn NZ. rewrite !HWord.w_sltu by lia.
  destruct (Z.ltb_spec 0 w); destruct (Z.ltb_spec (w + n) 1); try lia; vm_compute; reflexivity.
Qed.

Ltac ms_scw :=
  cbn [sc_denot]; evs; unfold wz; rewrite ?w_mul by lia; rewrite ?w_add by lia;
  first [ apply ms_nullxor; lia | rewrite br_ltu by lia; bool_lia ].

Definition MSK1 : list reg := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ms_sr1 : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (2%bv, EVar 35)].
Definition ms_kn1 : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
    KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
    KWr (SA (EVar 35) (-80)) (ELit 80); KRange (EVar 35) (2 ^ 45 + 80) (2 ^ 47);
    KRange (EVar 32) 1 (2 ^ 47); KRange (EVar 33) 0 (2 ^ 47); KRange (EVar 34) 0 (2 ^ 24) ].
Definition ms_x1 := sym_exec asegs 200 true [AASAN_MEMSET] (SCR [false; false] [] []) (SS MS_ENTRY ms_sr1 [] ms_kn1 40) [].
Definition ms_ss1 : sym_state := Eval vm_compute in fst (fst ms_x1).
Definition ms_scs1 : list sidecond := Eval vm_compute in snd (fst ms_x1).
Lemma ms_x1_eq : ms_x1 = (ms_ss1, ms_scs1, SCR [] [] []). Proof. vmeq. Qed.

Definition ms_B1 : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (p w nw spz lo : Z),
    getr R 10 = wz p -> getr R 11 = wz w -> getr R 12 = wz nw -> getr R 2 = wz spz ->
    ACONST m -> stk asegs m lo spz -> lo <= spz - 80 -> 2 ^ 45 + 80 <= spz -> spz <= 2 ^ 47 ->
    1 <= p <= 2 ^ 47 -> 0 <= w -> 0 <= nw <= 2 ^ 24 -> w + 4 * nw <= 2 ^ 47 -> (0 < nw -> w <> 0) ->
    exists R' M1,
      CatSim.msteps asegs (MS R F (wz MS_ENTRY) fc None m (seg_rom asegs)) (MS R' F (wz AASAN_MEMSET) fc None M1 (seg_rom asegs))
      /\ munch [(spz - 80, spz)] m M1 /\ wmono asegs m M1
      /\ rw_cells asegs M1 (spz - 80) (map (fun r => C8 (getr R r)) MSSAVED)
      /\ getr R' 1 = wz 0xea6d4 /\ getr R' 2 = wz (spz - 80) /\ getr R' 8 = wz w /\ getr R' 9 = wz p /\ getr R' 10 = wz p
      /\ getr R' 11 = wz 0 /\ getr R' 12 = wz 24 /\ getr R' 18 = wz nw /\ getr R' 19 = wz (4 * nw) /\ getr R' 20 = wz 0x7fff8000
      /\ (forall r, In r MSK1 -> getr R' r = getr R r).

Ltac ms_frame E Hlf :=
  first
  [ lazymatch goal with |- munch _ ?m0 (mem_denot _ _ _) =>
      let MU := fresh "MU" in
      pose proof (munch_mem_denot_sb [(-80, 0)] (EVar 35) E m0 _ Hlf ltac:(vm_cast_no_check (@eq_refl bool true))) as MU;
      eapply v4_munch_eqW; [exact MU | cbn [map fst snd]; evs; rewrite u64_of_Z by lia; repeat f_equal; lia] end
  | lazymatch goal with |- rw_cells _ (mem_denot _ _ ?lg) _ _ =>
      change lg with (v4_c8log (EVar 35) (-80) [EVar 24; EVar 23; EVar 22; EVar 21; EVar 20; EVar 19; EVar 18; EVar 9; EVar 8; EVar 1]);
      eapply rw_cells_mem_eq_list;
      [ apply v4_rw_cells_c8log;
        [ exact Hlf | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off a_base]; lia
        | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; eapply wr_at_of_stk_win; [eassumption | lia | lia] ]
      | reflexivity ] end ].

Lemma ms_B1_ok : ms_B1.
Proof.
  intros R F fc m p w nw spz lo H10 H11 H12 H2 AC ST LO SPL SPH PR W0 NR WH WNZ.
  set (E := Eseed R [wz p; wz w; wz nw; wz spz]).
  assert (HR : regs_ok E ms_sr1 R) by (unfold ms_sr1; v4_seed).
  pose proof (ACONST_shbase m AC) as [CG CS].
  assert (HK : know_ok asegs E m ms_kn1).
  { unfold ms_kn1, know_ok.
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
    apply Forall_cons.
    { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                         | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]. apply Forall_nil. }
  assert (HS : scs_denot asegs m E ms_scs1) by (unfold ms_scs1, scs_denot; repeat (apply Forall_cons; [ms_scw|]); apply Forall_nil).
  pose proof ms_x1_eq as EQ. unfold ms_x1 in EQ.
  v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss1.
  sp_exists E Hlf Hms.
  split; [exact Hms|]. split; [ms_frame E Hlf|]. split; [apply wmono_mem_denot|]. split; [ms_frame E Hlf|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' MSK1 HR HR'); [vm_compute; reflexivity | exact Hr]).
  all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; try reflexivity; wsolve end.
Qed.

Definition MSKB2 : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition MSKB2N : list reg := [1; 2; 3; 4; 8; 9; 19; 20; 24; 25; 26; 27]%bv.
Definition ms_sr2 : list expr := srs sr_id [(18%bv, EVar 32); (8%bv, EVar 33)].
Definition ms_kn2 : list kentry := [KRange (EVar 32) 0 (2 ^ 24); KRange (EVar 33) 0 (2 ^ 47); KAlign (EVar 33) 4].
Definition ms_x2 (d : list bool) := sym_exec asegs 200 true [MS_EXIT; MS_HEAD] (SCR d [] []) (SS 0xea6d4 ms_sr2 [] ms_kn2 40) [].
Definition ms_ss2z : sym_state := Eval vm_compute in fst (fst (ms_x2 [true])).
Definition ms_scs2z : list sidecond := Eval vm_compute in snd (fst (ms_x2 [true])).
Definition ms_ss2n : sym_state := Eval vm_compute in fst (fst (ms_x2 [false; false])).
Definition ms_scs2n : list sidecond := Eval vm_compute in snd (fst (ms_x2 [false; false])).
Lemma ms_x2z_eq : ms_x2 [true] = (ms_ss2z, ms_scs2z, SCR [] [] []). Proof. vmeq. Qed.
Lemma ms_x2n_eq : ms_x2 [false; false] = (ms_ss2n, ms_scs2n, SCR [] [] []). Proof. vmeq. Qed.

Definition ms_B2 : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (nw w : Z),
    getr R 18 = wz nw -> getr R 8 = wz w -> 0 <= nw <= 2 ^ 24 -> 0 <= w <= 2 ^ 47 -> w mod 4 = 0 -> (nw <> 0 -> w <> 0) ->
    exists R',
      (nw = 0 -> CatSim.msteps asegs (MS R F (wz 0xea6d4) fc None m (seg_rom asegs)) (MS R' F (wz MS_EXIT) fc None m (seg_rom asegs))
                 /\ (forall r, In r MSKB2 -> getr R' r = getr R r))
      /\ (nw <> 0 -> CatSim.msteps asegs (MS R F (wz 0xea6d4) fc None m (seg_rom asegs)) (MS R' F (wz MS_HEAD) fc None m (seg_rom asegs))
                 /\ getr R' 18 = getr R 8 /\ getr R' 21 = wz 0xff0000 /\ getr R' 22 = wz 0xff00 /\ getr R' 23 = wz (2 ^ 64 - 4)
                 /\ (forall r, In r MSKB2N -> getr R' r = getr R r)).

Lemma ms_B2_ok : ms_B2.
Proof.
  intros R F fc m nw w H18 H8 NR WR W4 WNZ.
  set (E := Eseed R [wz nw; wz w]).
  assert (HR : regs_ok E ms_sr2 R) by (unfold ms_sr2; v4_seed).
  assert (HK : know_ok asegs E m ms_kn2).
  { unfold ms_kn2, know_ok.
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; split; [lia | exact W4]|]. apply Forall_nil. }
  destruct (Z.eq_dec nw 0) as [Z0|NZ].
  - assert (HS : scs_denot asegs m E ms_scs2z) by (unfold ms_scs2z, scs_denot; repeat (apply Forall_cons; [ms_sc|]); apply Forall_nil).
    pose proof ms_x2z_eq as EQ. unfold ms_x2 in EQ.
    v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss2z.
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    exists R'. split; [intros _; split; [exact Hms|] | intros K; contradiction].
    intros r Hr. eapply (syms_same_sound E _ R _ R' MSKB2 HR HR'); [vm_compute; reflexivity | exact Hr].
  - pose proof (WNZ NZ) as WN.
    assert (HS : scs_denot asegs m E ms_scs2n) by (unfold ms_scs2n, scs_denot; repeat (apply Forall_cons; [ms_sc|]); apply Forall_nil).
    pose proof ms_x2n_eq as EQ. unfold ms_x2 in EQ.
    v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss2n.
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    exists R'. split; [intros K; contradiction|]. intros _. split; [exact Hms|].
    repeat match goal with |- _ /\ _ => split end.
    all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' MSKB2N HR HR'); [vm_compute; reflexivity | exact Hr]).
    all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; evs; try reflexivity; try (rewrite H8; reflexivity); wsolve end.
Qed.

Definition MSK3X : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv.
Definition MSK3C : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv.
Definition ms_sr3 : list expr := srs sr_id [(8%bv, EVar 32); (18%bv, EVar 32); (9%bv, EVar 33); (20%bv, ELit 0x7fff8000)].
Definition ms_kn3 (kk : expr) (extra : list kentry) : list kentry :=
  [ KWord (SA (EVar 32) 0) 4 (EVar 34); KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 0x7fff8000) 1 kk;
    KRange (EVar 32) 0 (2 ^ 47); KRange (EVar 34) 0 (2 ^ 32 - 1); KAlign (EVar 32) 4 ] ++ extra.
Definition ms_x3 (d : list bool) (kk : expr) (extra : list kentry) :=
  sym_exec asegs 200 true [SPB_ENTRY; MS_EXIT] (SCR d [] []) (SS MS_HEAD ms_sr3 [] (ms_kn3 kk extra) 40) [].
Definition ms_ss3a : sym_state := Eval vm_compute in fst (fst (ms_x3 [true] (ELit 0) [])).
Definition ms_scs3a : list sidecond := Eval vm_compute in snd (fst (ms_x3 [true] (ELit 0) [])).
Definition ms_ss3b : sym_state := Eval vm_compute in fst (fst (ms_x3 [false] (ELit 0) [])).
Definition ms_scs3b : list sidecond := Eval vm_compute in snd (fst (ms_x3 [false] (ELit 0) [])).
Definition ms_ss3c : sym_state := Eval vm_compute in fst (fst (ms_x3 [true; true] (EVar 35) [KRange (EVar 35) 1 7])).
Definition ms_scs3c : list sidecond := Eval vm_compute in snd (fst (ms_x3 [true; true] (EVar 35) [KRange (EVar 35) 1 7])).
Definition ms_ss3d : sym_state := Eval vm_compute in fst (fst (ms_x3 [true; false] (EVar 35) [KRange (EVar 35) 1 7])).
Definition ms_scs3d : list sidecond := Eval vm_compute in snd (fst (ms_x3 [true; false] (EVar 35) [KRange (EVar 35) 1 7])).
Lemma ms_x3a_eq : ms_x3 [true] (ELit 0) [] = (ms_ss3a, ms_scs3a, SCR [] [] []). Proof. vmeq. Qed.
Lemma ms_x3b_eq : ms_x3 [false] (ELit 0) [] = (ms_ss3b, ms_scs3b, SCR [] [] []). Proof. vmeq. Qed.
Lemma ms_x3c_eq : ms_x3 [true; true] (EVar 35) [KRange (EVar 35) 1 7] = (ms_ss3c, ms_scs3c, SCR [] [] []). Proof. vmeq. Qed.
Lemma ms_x3d_eq : ms_x3 [true; false] (EVar 35) [KRange (EVar 35) 1 7] = (ms_ss3d, ms_scs3d, SCR [] [] []). Proof. vmeq. Qed.

Definition ms_B3pre (R : bvmap 5 word) (m : mem) (a p x k : Z) : Prop :=
  getr R 8 = wz a /\ getr R 18 = wz a /\ getr R 9 = wz p /\ getr R 20 = wz 0x7fff8000
  /\ fldA m a 4 x /\ LbB_Kit.shk m a k /\ (k = 0 \/ a mod 8 + 4 <= k < 8) /\ 0 <= x < 2 ^ 32
  /\ a mod 4 = 0 /\ 0 <= a /\ a + 4 <= 2 ^ 47.

Definition ms_B3 : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (a p x k : Z),
    ms_B3pre R m a p x k ->
    exists R',
      (x mod 256 = 0 -> CatSim.msteps asegs (MS R F (wz MS_HEAD) fc None m (seg_rom asegs)) (MS R' F (wz MS_EXIT) fc None m (seg_rom asegs))
                        /\ (forall r, In r MSK3X -> getr R' r = getr R r))
      /\ (x mod 256 <> 0 -> CatSim.msteps asegs (MS R F (wz MS_HEAD) fc None m (seg_rom asegs)) (MS R' F (wz SPB_ENTRY) fc None m (seg_rom asegs))
                        /\ getr R' 1 = wz 0xea71c /\ getr R' 10 = wz p /\ getr R' 11 = wz (x mod 256) /\ getr R' 24 = wz x
                        /\ (forall r, In r MSK3C -> getr R' r = getr R r)).

Ltac ms_kn3_tac E m :=
  unfold ms_kn3, know_ok; cbn [app];
  repeat (apply Forall_cons; [ v4_kentry E m |]); apply Forall_nil.

Lemma ms_B3_ok : ms_B3.
Proof.
  intros R F fc m a p x k (H8 & H18 & H9 & H19 & FX & SK & KC & XR & A4 & A0 & AH).
  pose proof (div8_b a ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 256 ltac:(lia)).
  assert (KB : 0 <= k < 256) by lia.
  destruct KC as [K0|KS].
  - subst k. set (E := Eseed R [wz a; wz p; wz x]).
    assert (HR : regs_ok E ms_sr3 R) by (unfold ms_sr3; v4_seed).
    assert (HK : know_ok asegs E m (ms_kn3 (ELit 0) [])) by ms_kn3_tac E m.
    destruct (Z.eq_dec (x mod 256) 0) as [B0|B0].
    + assert (HS : scs_denot asegs m E ms_scs3a) by (unfold ms_scs3a, scs_denot; repeat (apply Forall_cons; [ms_sc|]); apply Forall_nil).
      pose proof ms_x3a_eq as EQ. unfold ms_x3 in EQ.
      v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss3a.
      lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
      exists R'. split; [intros _; split; [exact Hms|] | intros K; contradiction].
      intros r Hr. eapply (syms_same_sound E _ R _ R' MSK3X HR HR'); [vm_compute; reflexivity | exact Hr].
    + assert (HS : scs_denot asegs m E ms_scs3b) by (unfold ms_scs3b, scs_denot; repeat (apply Forall_cons; [ms_sc|]); apply Forall_nil).
      pose proof ms_x3b_eq as EQ. unfold ms_x3 in EQ.
      v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss3b.
      lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
      exists R'. split; [intros K; contradiction|]. intros _. split; [exact Hms|].
      repeat match goal with |- _ /\ _ => split end.
      all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' MSK3C HR HR'); [vm_compute; reflexivity | exact Hr]).
      all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; evs; try reflexivity; unfold wz; rewrite ?ms_and255_w by lia; reflexivity end.
  - set (E := Eseed R [wz a; wz p; wz x; wz k]).
    assert (HR : regs_ok E ms_sr3 R) by (unfold ms_sr3; v4_seed).
    assert (HK : know_ok asegs E m (ms_kn3 (EVar 35) [KRange (EVar 35) 1 7])) by ms_kn3_tac E m.
    destruct (Z.eq_dec (x mod 256) 0) as [B0|B0].
    + assert (HS : scs_denot asegs m E ms_scs3c).
      { unfold ms_scs3c, scs_denot. repeat (apply Forall_cons; [first [ms_sc | v4_sc3]|]). apply Forall_nil. }
      pose proof ms_x3c_eq as EQ. unfold ms_x3 in EQ.
      v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss3c.
      lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
      exists R'. split; [intros _; split; [exact Hms|] | intros K; contradiction].
      intros r Hr. eapply (syms_same_sound E _ R _ R' MSK3X HR HR'); [vm_compute; reflexivity | exact Hr].
    + assert (HS : scs_denot asegs m E ms_scs3d).
      { unfold ms_scs3d, scs_denot. repeat (apply Forall_cons; [first [ms_sc | v4_sc3]|]). apply Forall_nil. }
      pose proof ms_x3d_eq as EQ. unfold ms_x3 in EQ.
      v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss3d.
      lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
      exists R'. split; [intros K; contradiction|]. intros _. split; [exact Hms|].
      repeat match goal with |- _ /\ _ => split end.
      all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' MSK3C HR HR'); [vm_compute; reflexivity | exact Hr]).
      all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; evs; try reflexivity; unfold wz; rewrite ?ms_and255_w by lia; reflexivity end.
Qed.

Definition MSK4X : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition MSK4C : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ms_sr4 : list expr := srs sr_id [(24%bv, EVar 32); (22%bv, ELit 0xff00); (21%bv, ELit 0xff0000); (9%bv, EVar 33)].
Definition ms_kn4 : list kentry := [KRange (EVar 32) 0 (2 ^ 32 - 1)].
Definition ms_x4 (pc : Z) (d : list bool) := sym_exec asegs 200 true [SPB_ENTRY; MS_EXIT] (SCR d [] []) (SS pc ms_sr4 [] ms_kn4 40) [].
Definition ms_ss4x : sym_state := Eval vm_compute in fst (fst (ms_x4 0xea71c [true])).
Definition ms_scs4x : list sidecond := Eval vm_compute in snd (fst (ms_x4 0xea71c [true])).
Definition ms_ss4c : sym_state := Eval vm_compute in fst (fst (ms_x4 0xea71c [false])).
Definition ms_scs4c : list sidecond := Eval vm_compute in snd (fst (ms_x4 0xea71c [false])).
Definition ms_ss5x : sym_state := Eval vm_compute in fst (fst (ms_x4 0xea734 [true])).
Definition ms_scs5x : list sidecond := Eval vm_compute in snd (fst (ms_x4 0xea734 [true])).
Definition ms_ss5c : sym_state := Eval vm_compute in fst (fst (ms_x4 0xea734 [false])).
Definition ms_scs5c : list sidecond := Eval vm_compute in snd (fst (ms_x4 0xea734 [false])).
Definition ms_ss6x : sym_state := Eval vm_compute in fst (fst (ms_x4 0xea74c [true])).
Definition ms_scs6x : list sidecond := Eval vm_compute in snd (fst (ms_x4 0xea74c [true])).
Definition ms_ss6c : sym_state := Eval vm_compute in fst (fst (ms_x4 0xea74c [false])).
Definition ms_scs6c : list sidecond := Eval vm_compute in snd (fst (ms_x4 0xea74c [false])).
Lemma ms_x4x_eq : ms_x4 0xea71c [true] = (ms_ss4x, ms_scs4x, SCR [] [] []). Proof. vmeq. Qed.
Lemma ms_x4c_eq : ms_x4 0xea71c [false] = (ms_ss4c, ms_scs4c, SCR [] [] []). Proof. vmeq. Qed.
Lemma ms_x5x_eq : ms_x4 0xea734 [true] = (ms_ss5x, ms_scs5x, SCR [] [] []). Proof. vmeq. Qed.
Lemma ms_x5c_eq : ms_x4 0xea734 [false] = (ms_ss5c, ms_scs5c, SCR [] [] []). Proof. vmeq. Qed.
Lemma ms_x6x_eq : ms_x4 0xea74c [true] = (ms_ss6x, ms_scs6x, SCR [] [] []). Proof. vmeq. Qed.
Lemma ms_x6c_eq : ms_x4 0xea74c [false] = (ms_ss6c, ms_scs6c, SCR [] [] []). Proof. vmeq. Qed.

Definition wbyte (x : Z) (j : nat) : Z := nth j (word_chars x 4) 0.
Lemma wbyte_0 : forall x, wbyte x 0 = x mod 256. Proof. reflexivity. Qed.
Lemma wbyte_1 : forall x, wbyte x 1 = (x / 256) mod 256. Proof. reflexivity. Qed.
Lemma wbyte_2 : forall x, wbyte x 2 = (x / 256 / 256) mod 256. Proof. reflexivity. Qed.
Lemma wbyte_3 : forall x, wbyte x 3 = (x / 256 / 256 / 256) mod 256. Proof. reflexivity. Qed.

Definition ms_Bj (pc ra : Z) (j : nat) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (p x : Z),
    getr R 24 = wz x -> getr R 22 = wz 0xff00 -> getr R 21 = wz 0xff0000 -> getr R 9 = wz p -> 0 <= x < 2 ^ 32 ->
    exists R',
      (wbyte x j = 0 -> CatSim.msteps asegs (MS R F (wz pc) fc None m (seg_rom asegs)) (MS R' F (wz MS_EXIT) fc None m (seg_rom asegs))
                        /\ (forall r, In r MSK4X -> getr R' r = getr R r))
      /\ (wbyte x j <> 0 -> CatSim.msteps asegs (MS R F (wz pc) fc None m (seg_rom asegs)) (MS R' F (wz SPB_ENTRY) fc None m (seg_rom asegs))
                        /\ getr R' 1 = wz ra /\ getr R' 10 = wz p /\ getr R' 11 = wz (wbyte x j)
                        /\ (forall r, In r MSK4C -> getr R' r = getr R r)).

Lemma ms_B4_ok : ms_Bj 0xea71c 0xea734 1.
Proof.
  intros R F fc m p x H23 H21 H22 H9 XR.
  set (E := Eseed R [wz x; wz p]).
  assert (HR : regs_ok E ms_sr4 R) by (unfold ms_sr4; v4_seed).
  assert (HK : know_ok asegs E m ms_kn4) by (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]).
  pose proof (Z.mod_pos_bound x 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (x / 256 / 256) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256 / 256 / 256) 256 ltac:(lia)).
  rewrite wbyte_1.
  destruct (Z.eq_dec ((x / 256) mod 256) 0) as [B0|B0].
  - assert (HS : scs_denot asegs m E ms_scs4x) by (unfold ms_scs4x, scs_denot; repeat (apply Forall_cons; [ms_sc|]); apply Forall_nil).
    pose proof ms_x4x_eq as EQ. unfold ms_x4 in EQ.
    v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss4x.
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    exists R'. split; [intros _; split; [exact Hms|] | intros K; contradiction].
    intros r Hr. eapply (syms_same_sound E _ R _ R' MSK4X HR HR'); [vm_compute; reflexivity | exact Hr].
  - assert (HS : scs_denot asegs m E ms_scs4c) by (unfold ms_scs4c, scs_denot; repeat (apply Forall_cons; [ms_sc|]); apply Forall_nil).
    pose proof ms_x4c_eq as EQ. unfold ms_x4 in EQ.
    v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss4c.
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    exists R'. split; [intros K; contradiction|]. intros _. split; [exact Hms|].
    repeat match goal with |- _ /\ _ => split end.
    all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' MSK4C HR HR'); [vm_compute; reflexivity | exact Hr]).
    all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; evs; try reflexivity; unfold wz;
           rewrite ?ms_byte1_w, ?ms_byte2_w, ?ms_byte3_w by lia; reflexivity end.
Qed.

Lemma ms_B5_ok : ms_Bj 0xea734 0xea74c 2.
Proof.
  intros R F fc m p x H23 H21 H22 H9 XR.
  set (E := Eseed R [wz x; wz p]).
  assert (HR : regs_ok E ms_sr4 R) by (unfold ms_sr4; v4_seed).
  assert (HK : know_ok asegs E m ms_kn4) by (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]).
  pose proof (Z.mod_pos_bound x 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (x / 256 / 256) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256 / 256 / 256) 256 ltac:(lia)).
  rewrite wbyte_2.
  destruct (Z.eq_dec ((x / 256 / 256) mod 256) 0) as [B0|B0].
  - assert (HS : scs_denot asegs m E ms_scs5x) by (unfold ms_scs5x, scs_denot; repeat (apply Forall_cons; [ms_sc|]); apply Forall_nil).
    pose proof ms_x5x_eq as EQ. unfold ms_x4 in EQ.
    v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss5x.
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    exists R'. split; [intros _; split; [exact Hms|] | intros K; contradiction].
    intros r Hr. eapply (syms_same_sound E _ R _ R' MSK4X HR HR'); [vm_compute; reflexivity | exact Hr].
  - assert (HS : scs_denot asegs m E ms_scs5c) by (unfold ms_scs5c, scs_denot; repeat (apply Forall_cons; [ms_sc|]); apply Forall_nil).
    pose proof ms_x5c_eq as EQ. unfold ms_x4 in EQ.
    v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss5c.
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    exists R'. split; [intros K; contradiction|]. intros _. split; [exact Hms|].
    repeat match goal with |- _ /\ _ => split end.
    all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' MSK4C HR HR'); [vm_compute; reflexivity | exact Hr]).
    all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; evs; try reflexivity; unfold wz;
           rewrite ?ms_byte1_w, ?ms_byte2_w, ?ms_byte3_w by lia; reflexivity end.
Qed.

Lemma ms_B6_ok : ms_Bj 0xea74c 0xea75c 3.
Proof.
  intros R F fc m p x H23 H21 H22 H9 XR.
  set (E := Eseed R [wz x; wz p]).
  assert (HR : regs_ok E ms_sr4 R) by (unfold ms_sr4; v4_seed).
  assert (HK : know_ok asegs E m ms_kn4) by (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]).
  pose proof (Z.mod_pos_bound x 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (x / 256 / 256) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256 / 256 / 256) 256 ltac:(lia)).
  rewrite wbyte_3.
  destruct (Z.eq_dec ((x / 256 / 256 / 256) mod 256) 0) as [B0|B0].
  - assert (HS : scs_denot asegs m E ms_scs6x) by (unfold ms_scs6x, scs_denot; repeat (apply Forall_cons; [ms_sc|]); apply Forall_nil).
    pose proof ms_x6x_eq as EQ. unfold ms_x4 in EQ.
    v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss6x.
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    exists R'. split; [intros _; split; [exact Hms|] | intros K; contradiction].
    intros r Hr. eapply (syms_same_sound E _ R _ R' MSK4X HR HR'); [vm_compute; reflexivity | exact Hr].
  - assert (HS : scs_denot asegs m E ms_scs6c) by (unfold ms_scs6c, scs_denot; repeat (apply Forall_cons; [ms_sc|]); apply Forall_nil).
    pose proof ms_x6c_eq as EQ. unfold ms_x4 in EQ.
    v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss6c.
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    exists R'. split; [intros K; contradiction|]. intros _. split; [exact Hms|].
    repeat match goal with |- _ /\ _ => split end.
    all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' MSK4C HR HR'); [vm_compute; reflexivity | exact Hr]).
    all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; evs; try reflexivity; unfold wz;
           rewrite ?ms_byte1_w, ?ms_byte2_w, ?ms_byte3_w by lia; reflexivity end.
Qed.

Definition MSK7 : list reg := [1; 2; 3; 4; 9; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ms_sr7 : list expr := srs sr_id [(8%bv, EVar 32); (18%bv, EVar 32); (19%bv, EMd M_MUL (ELit 4) (EVar 33)); (23%bv, ELit (2 ^ 64 - 4))].
Definition ms_kn7 : list kentry := [KRange (EVar 32) 0 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 24)].
Definition ms_x7 (d : list bool) := sym_exec asegs 200 true [MS_HEAD; MS_EXIT] (SCR d [] []) (SS 0xea75c ms_sr7 [] ms_kn7 40) [].
Definition ms_ss7l : sym_state := Eval vm_compute in fst (fst (ms_x7 [true])).
Definition ms_scs7l : list sidecond := Eval vm_compute in snd (fst (ms_x7 [true])).
Definition ms_ss7x : sym_state := Eval vm_compute in fst (fst (ms_x7 [false])).
Definition ms_scs7x : list sidecond := Eval vm_compute in snd (fst (ms_x7 [false])).
Lemma ms_x7l_eq : ms_x7 [true] = (ms_ss7l, ms_scs7l, SCR [] [] []). Proof. vmeq. Qed.
Lemma ms_x7x_eq : ms_x7 [false] = (ms_ss7x, ms_scs7x, SCR [] [] []). Proof. vmeq. Qed.

Definition ms_B7 : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (a r : Z),
    getr R 8 = wz a -> getr R 18 = wz a -> getr R 19 = wz (4 * r) -> getr R 23 = wz (2 ^ 64 - 4) ->
    1 <= r <= 2 ^ 24 -> 0 <= a -> a + 4 <= 2 ^ 47 ->
    exists R',
      (r <> 1 -> CatSim.msteps asegs (MS R F (wz 0xea75c) fc None m (seg_rom asegs)) (MS R' F (wz MS_HEAD) fc None m (seg_rom asegs))
                 /\ getr R' 8 = wz (a + 4) /\ getr R' 18 = wz (a + 4) /\ getr R' 19 = wz (4 * (r - 1))
                 /\ (forall r, In r MSK7 -> getr R' r = getr R r))
      /\ (r = 1 -> CatSim.msteps asegs (MS R F (wz 0xea75c) fc None m (seg_rom asegs)) (MS R' F (wz MS_EXIT) fc None m (seg_rom asegs))
                 /\ (forall r, In r MSK7 -> getr R' r = getr R r)).

Lemma ms_B7_ok : ms_B7.
Proof.
  intros R F fc m a r H8 H18 H19 H23 RR A0 AH.
  set (E := Eseed R [wz a; wz r]).
  assert (HR : regs_ok E ms_sr7 R) by (unfold ms_sr7; v4_seed).
  assert (HK : know_ok asegs E m ms_kn7).
  { apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
  destruct (Z.eq_dec r 1) as [R1|R1].
  - assert (HS : scs_denot asegs m E ms_scs7x).
    { unfold ms_scs7x, scs_denot. repeat (apply Forall_cons; [cbn [sc_denot]; evs; unfold wz; rewrite w_mul, w_addm by lia; rewrite br_ne by lia; bool_lia|]). apply Forall_nil. }
    pose proof ms_x7x_eq as EQ. unfold ms_x7 in EQ.
    v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss7x.
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    exists R'. split; [intros K; contradiction|]. intros _. split; [exact Hms|].
    intros r' Hr. eapply (syms_same_sound E _ R _ R' MSK7 HR HR'); [vm_compute; reflexivity | exact Hr].
  - assert (HS : scs_denot asegs m E ms_scs7l).
    { unfold ms_scs7l, scs_denot. repeat (apply Forall_cons; [cbn [sc_denot]; evs; unfold wz; rewrite w_mul, w_addm by lia; rewrite br_ne by lia; bool_lia|]). apply Forall_nil. }
    pose proof ms_x7l_eq as EQ. unfold ms_x7 in EQ.
    v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ss7l.
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    exists R'. split; [|intros K; contradiction]. intros _. split; [exact Hms|].
    repeat match goal with |- _ /\ _ => split end.
    all: try (intros r' Hr; eapply (syms_same_sound E _ R _ R' MSK7 HR HR'); [vm_compute; reflexivity | exact Hr]).
    all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; evs; unfold wz; rewrite ?w_mul, ?w_add, ?w_addm by lia; f_equal; lia end.
Qed.

Definition MSKX : list reg := [3; 4; 25; 26; 27]%bv.
Definition ms_srx : list expr := srs sr_id [(2%bv, EVar 32)].
Definition ms_knx : list kentry :=
  [ KWord (SA (EVar 32) 0) 8 (EVar 42);
    KWord (SA (EVar 32) 8) 8 (EVar 33); KWord (SA (EVar 32) 16) 8 (EVar 34); KWord (SA (EVar 32) 24) 8 (EVar 35);
    KWord (SA (EVar 32) 32) 8 (EVar 36); KWord (SA (EVar 32) 40) 8 (EVar 37); KWord (SA (EVar 32) 48) 8 (EVar 38);
    KWord (SA (EVar 32) 56) 8 (EVar 39); KWord (SA (EVar 32) 64) 8 (EVar 40); KWord (SA (EVar 32) 72) 8 (EVar 41);
    KRange (EVar 32) (2 ^ 45) (2 ^ 47) ].
Definition ms_xx := sym_exec asegs 200 true [] (SCR [] [] []) (SS MS_EXIT ms_srx [] ms_knx 50) [].
Definition ms_ssx : sym_state := Eval vm_compute in fst (fst ms_xx).
Definition ms_scsx : list sidecond := Eval vm_compute in snd (fst ms_xx).
Lemma ms_xx_eq : ms_xx = (ms_ssx, ms_scsx, SCR [] [] []). Proof. vmeq. Qed.

Definition ms_BX : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (spz : Z) (x24 x23 x22 x21 x20 x19 x18 x9 x8 x1 : word),
    getr R 2 = wz (spz - 80) ->
    rw_cells asegs m (spz - 80) (map (fun w => C8 w) [x24; x23; x22; x21; x20; x19; x18; x9; x8; x1]) ->
    2 ^ 45 <= spz - 80 -> spz <= 2 ^ 47 ->
    exists R',
      CatSim.msteps asegs (MS R F (wz MS_EXIT) fc None m (seg_rom asegs)) (MS R' F (wz MS_RET) fc None m (seg_rom asegs))
      /\ getr R' 1 = x1 /\ getr R' 2 = wz spz /\ getr R' 8 = x8 /\ getr R' 9 = x9 /\ getr R' 18 = x18 /\ getr R' 19 = x19
      /\ getr R' 20 = x20 /\ getr R' 21 = x21 /\ getr R' 22 = x22 /\ getr R' 23 = x23 /\ getr R' 24 = x24
      /\ (forall r, In r MSKX -> getr R' r = getr R r).

Lemma ms_BX_ok : ms_BX.
Proof.
  intros R F fc m spz x24 x23 x22 x21 x20 x19 x18 x9 x8 x1 H2 CF SPL SPH.
  set (E := Eseed R [wz (spz - 80); x23; x22; x21; x20; x19; x18; x9; x8; x1; x24]).
  assert (HR : regs_ok E ms_srx R) by (unfold ms_srx; v4_seed).
  assert (HK : know_ok asegs E m ms_knx).
  { unfold ms_knx, know_ok. cbn [map] in CF.
    apply Forall_cons; [kword_cell CF 0%nat (C8 x24)|].
    apply Forall_cons; [kword_cell CF 8%nat (C8 x23)|]. apply Forall_cons; [kword_cell CF 16%nat (C8 x22)|].
    apply Forall_cons; [kword_cell CF 24%nat (C8 x21)|]. apply Forall_cons; [kword_cell CF 32%nat (C8 x20)|].
    apply Forall_cons; [kword_cell CF 40%nat (C8 x19)|]. apply Forall_cons; [kword_cell CF 48%nat (C8 x18)|].
    apply Forall_cons; [kword_cell CF 56%nat (C8 x9)|]. apply Forall_cons; [kword_cell CF 64%nat (C8 x8)|].
    apply Forall_cons; [kword_cell CF 72%nat (C8 x1)|].
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]. apply Forall_nil. }
  assert (HS : scs_denot asegs m E ms_scsx) by (unfold ms_scsx, scs_denot; apply Forall_nil).
  pose proof ms_xx_eq as EQ. unfold ms_xx in EQ.
  v4_run (PropExec.mkFP F fc) EQ HR HK HS ms_ssx.
  lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
  exists R'. split; [exact Hms|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' MSKX HR HR'); [vm_compute; reflexivity | exact Hr]).
  all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; try reflexivity; wsolve end.
Qed.

Lemma ms_ret_ok : v4_ret_ok MS_RET.
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  step. apply evt_done. exact HQ.
Qed.

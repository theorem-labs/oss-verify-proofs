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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX BArr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_FKit LbB_Bridge LbB_Call LbB_Conv LbB_TopH2 LbB_TopL1 LbB_Vec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_TopKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition TOP_MS_RA : Z := 0xe8a7c.
Definition TOP_RS_RA : Z := 0xe8a8c.

Lemma map_bv8_unsigned : forall (bs : list byte), map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof.
  intros bs. induction bs as [|b bs IH]; cbn [map]; [reflexivity|]. rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | apply bv_unsigned_in_range].
Qed.

Ltac m1_ar := rewrite ?w_addm, ?w_add by lia; rewrite ?u64_of_Z by lia.

Ltac m1_rwc1 Hlf HR0 WW WS1 :=
  let t k := (eapply (rw_cells_log_nth _ _ _ k);
               [ exact Hlf | reflexivity | idtac | unfold estart; cbn [a_base a_off]; evs; m1_ar; lia
               | idtac | reflexivity | exact I | cbn [cbytes]; evs; rewrite ?HR0; m1_ar; reflexivity ]);
             [ cbn [firstn]; repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; evs; m1_ar; lia |]);
               apply Forall_nil
             | first [apply WW; lia | apply WS1; lia] ] in
  first [ t 0%nat | t 1%nat | t 2%nat | t 3%nat | t 4%nat | t 5%nat | t 6%nat | t 7%nat | t 8%nat | t 9%nat
        | t 10%nat | t 11%nat | t 12%nat | t 13%nat | t 14%nat | t 15%nat ].

Ltac m1_cells Hlf HR0 WW WS1 :=
  repeat (lazymatch goal with |- rw_cells ?sg ?mm ?A (?c :: ?rest) =>
            lazymatch rest with
            | [] => fail
            | _ => apply (proj2 (rw_cells_app sg mm A [c] rest)); split; [m1_rwc1 Hlf HR0 WW WS1 | cbn [cells_size csize]]
            end end);
  m1_rwc1 Hlf HR0 WW WS1.

Lemma srl2_val : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 2) = Z_to_bv 64 (x / 4).
Proof.
  intros x Hx. apply bv_eq. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small x) by lia.
  replace (bv_unsigned (bv_and (Z_to_bv 64 2) (Z_to_bv 64 63))) with 2 by (vm_compute; reflexivity).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  assert (0 <= x / 4 < 2 ^ 64) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small (x / 4)) by lia. reflexivity.
Qed.

Section TopM1.
  Context {HCEIL : HeapCeil}.

  Lemma hMS1 : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s8 s9 s10 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff N A lo : Z),
    0x6e6000 <= ff -> ff + 4096 <= 2 ^ 47 -> 0 < A < 2 ^ 47 ->
    2 ^ 45 <= S1 -> S1 + 224 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    wr_at asegs m (sh ff + 334) 3 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (fun ms' => exists x13' x14' x15' x16' x17' m1,
        ms' = MS (mkR (Z_to_bv 64 TOP_MS_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 (ff + 2672))
                      (Z_to_bv 64 0) (Z_to_bv 64 24) x13' x14' x15' x16' x17' (Z_to_bv 64 (ff + 2672)) (Z_to_bv 64 (sh ff + 4))
                      (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N)
                      x28 x29 x30 x31) F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
        /\ munch [(S1 + 24, S1 + 64); (sh ff + 334, sh ff + 337)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
        /\ u8arr asegs m1 (sh ff + 334) (repeat (b8 0) 3)
        /\ rw_cells asegs m1 (S1 + 24) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (sh ff + 4)); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 (sh ff));
                                         C8 (Z_to_bv 64 ff)])
      (MS (mkR (Z_to_bv 64 TOP_CTX_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 A)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff))
               (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31)
          F (Z_to_bv 64 TOP_CTX_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s8 s9 s10 x28 x29 x30 x31 F fc m SP S1 ff N A lo
      FLO FHI AR S1L S1H SPH LO WS ST MI.
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000)
      by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (WW : forall a n, lo <= a -> a + n <= SP -> 0 <= n -> wr_at asegs m a n).
    { intros a n H1 H2 H3. destruct (stk_split asegs m lo a SP ST ltac:(lia)) as [_ S2].
      destruct (stk_split asegs m a (a + n) SP S2 ltac:(lia)) as [S3 _].
      pose proof (wr_at_of_stk asegs m a (a + n) S3) as W. replace (a + n - a) with n in W by lia. exact W. }
    assert (WS1 : forall a n, sh ff + 334 <= a -> a + n <= sh ff + 337 -> 0 <= n -> wr_at asegs m a n).
    { intros a n H1 H2 H3. pose proof WS as W0.
      replace 3 with ((a - (sh ff + 334)) + (3 - (a - (sh ff + 334)))) in W0 by lia.
      apply (proj1 (wr_at_app asegs m (sh ff + 334) (a - (sh ff + 334)) (3 - (a - (sh ff + 334))) ltac:(lia) ltac:(lia))) in W0.
      destruct W0 as [_ W1]. replace (sh ff + 334 + (a - (sh ff + 334))) with a in W1 by lia.
      replace (3 - (a - (sh ff + 334))) with (n + (3 - (a - (sh ff + 334)) - n)) in W1 by lia.
      apply (proj1 (wr_at_app asegs m a n (3 - (a - (sh ff + 334)) - n) ltac:(lia) ltac:(lia))) in W1.
      exact (proj1 W1). }
    remember (mkR (Z_to_bv 64 TOP_CTX_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 N; Z_to_bv 64 0; Z_to_bv 64 A; Z_to_bv 64 (sh ff)]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (9%bv, EVar 33); (10%bv, EVar 37); (18%bv, EVar 32); (19%bv, EAlu ALU_ADD (EVar 38) (ELit 4)); (20%bv, EVar 32); (21%bv, EVar 38); (22%bv, ELit 0x7fff8000); (23%bv, EAlu ALU_ADD (EVar 32) (ELit 32)); (27%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor.
      all: cbn [fst snd]; try (intros X; discriminate X).
      all: subst R; evs.
      all: try reflexivity.
      all: rewrite ?w_add by lia.
      all: first [reflexivity | refine (eq_trans (y := Z_to_bv 64 _) eq_refl _); f_equal; lia]. }
    assert (EP : bv_unsigned (edenot E (EVar 33)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (ES : bv_unsigned (edenot E (EVar 38)) = sh ff) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [KWr (SA (EVar 33) 24) (ELit 40); KWr (SA (EVar 38) 334) (ELit 3); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e6000 (2 ^ 47 - 4096); KRange (EVar 37) 1 (2 ^ 47)]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite EP; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EP; evs; rewrite u64_of_Z by lia; lia
                                  | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; lia
                                  | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_CTX_RA m (seg_rom asegs) HR HK 80%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs.
      all: cbn [sc_denot]; unfold flat, elenZ, estart; cbn [a_base a_off]; rewrite ES; evs; rewrite ?u64_of_Z by lia; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    rreg HR' 2%bv L2.
    rreg HR' 9%bv L9.
    rreg HR' 10%bv L10.
    rreg HR' 11%bv L11.
    rreg HR' 12%bv L12.
    rreg HR' 18%bv L18.
    rreg HR' 19%bv L19.
    rreg HR' 20%bv L20.
    rreg HR' 21%bv L21.
    rreg HR' 22%bv L22.
    rreg HR' 23%bv L23.
    rreg HR' 27%bv L27.
    assert (L1' : getr R' 1 = (Z_to_bv 64 TOP_MS_RA)) by (rewrite L1; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L2' : getr R' 2 = (Z_to_bv 64 S1)) by (rewrite L2; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L9' : getr R' 9 = (Z_to_bv 64 S1)) by (rewrite L9; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L10' : getr R' 10 = (Z_to_bv 64 (ff + 2672))) by (rewrite L10; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L11' : getr R' 11 = (Z_to_bv 64 0)) by (rewrite L11; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L12' : getr R' 12 = (Z_to_bv 64 24)) by (rewrite L12; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L18' : getr R' 18 = (Z_to_bv 64 (ff + 2672))) by (rewrite L18; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L19' : getr R' 19 = (Z_to_bv 64 (sh ff + 4))) by (rewrite L19; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L20' : getr R' 20 = (Z_to_bv 64 ff)) by (rewrite L20; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L21' : getr R' 21 = (Z_to_bv 64 (sh ff))) by (rewrite L21; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L22' : getr R' 22 = (Z_to_bv 64 0x7fff8000)) by (rewrite L22; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L23' : getr R' 23 = (Z_to_bv 64 (ff + 32))) by (rewrite L23; m1_ar; first [reflexivity | f_equal; lia]).
    assert (L27' : getr R' 27 = (Z_to_bv 64 N)) by (rewrite L27; m1_ar; first [reflexivity | f_equal; lia]).
    assert (MU1 : munch [(S1 + 24, S1 + 64); (sh ff + 334, sh ff + 337)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; evs; m1_ar;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (U8 : u8arr asegs M1 (sh ff + 334) (repeat (b8 0) 3)).
    { apply (u8arr_of_rw_cells asegs M1 (sh ff + 334) 3).
      change (CB 3 (repeat (b8 0) 3)) with
        (CB (cells_size [C1 (b8 0); C1 (b8 0); C1 (b8 0)]) (cells_bytes [C1 (b8 0); C1 (b8 0); C1 (b8 0)])).
      apply rw_cells_to_CB. subst M1. m1_cells Hlf HR0 WW WS1. }
    assert (RC : rw_cells asegs M1 (S1 + 24) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (sh ff + 4)); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 (sh ff));
                                               C8 (Z_to_bv 64 ff)]).
    { subst M1. m1_cells Hlf HR0 WW WS1. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L2', L9', L10', L11', L12', L18', L19', L20', L21', L22', L23', L27'.
    apply evt_done.
    do 6 eexists; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].
    split; [exact U8 | exact RC].
  Qed.

  Lemma hMS2 : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s8 s9 s10 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff N V lo : Z),
    0 <= N < 2 ^ 26 -> 0 <= V < 2 ^ 64 -> 2 ^ 45 <= S1 -> S1 + 224 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (fun ms' => exists m1,
        ms' = MS (mkR (Z_to_bv 64 TOP_RS_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 V)
                      (Z_to_bv 64 (N / 4)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 V) (Z_to_bv 64 (sh ff + 4))
                      (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N)
                      x28 x29 x30 x31) F (Z_to_bv 64 VRESIZE) fc None m1 (seg_rom asegs)
        /\ munch [(S1 + 80, S1 + 88)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
        /\ rw_cells asegs m1 (S1 + 80) [C8 (Z_to_bv 64 V)])
      (MS (mkR (Z_to_bv 64 TOP_MS_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 V) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000)
               (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31)
          F (Z_to_bv 64 TOP_MS_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros NR VR S1L S1H SPH LO ST MI.
    remember (mkR (Z_to_bv 64 TOP_MS_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 V) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 V; Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 N]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (9%bv, EVar 33); (18%bv, EVar 32); (27%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        reflexivity. }
    assert (EP : bv_unsigned (edenot E (EVar 33)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWr (SA (EVar 33) 80) (ELit 8); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 35) 0 (2 ^ 26) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite EP; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EP; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_MS_RA m (seg_rom asegs) HR HK 40%nat [VRESIZE] (SCR [] [] []) 50%N.
    { split_scs. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 18%bv L18.
    rreg HR' 27%bv L27.
    assert (L11' : getr R' 11 = Z_to_bv 64 (N / 4)) by (rewrite L11; apply srl2_val; lia).
    assert (W80 : wr_at asegs m (S1 + 80) 8).
    { pose proof ST as (ST0 & ST1 & STW). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (STW (S1 + 80 + i) ltac:(lia))). }
    assert (MU1 : munch [(S1 + 80, S1 + 88)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (RC : rw_cells asegs M1 (S1 + 80) [C8 (Z_to_bv 64 V)]).
    { subst M1. eapply (rw_cells_mem_denot_w _ m [] _ 8 (EVar 32) []); [exact Hlf | apply Forall_nil | | exact W80 | reflexivity | exact I | reflexivity].
      unfold estart; evs; rewrite u64_of_Z by lia; lia. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L9, L10, L11', L18, L27.
    apply evt_done.
    exists M1. split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. exact RC.
  Qed.
End TopM1.

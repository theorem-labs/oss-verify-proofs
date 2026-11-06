(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import RealizeS SeamA0 A0Prog AssembleA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_exit RF_mainA_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import F_syscalls RDriverA_lib RDriverA_iface RF_mainA_B1 RF_mainA_B2 RF_mainA_B3 RF_mainA_B4 RF_mainA_C.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require F_atexitA.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac zst := zstep; fix_lit_store.

Lemma land3_range : forall a, 0 <= Z.land a 3 <= 3.
Proof.
  intros a. change (Z.land a 3) with (Z.land a (Z.ones 2)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound a (2 ^ 2) ltac:(lia)). lia.
Qed.

Lemma djf_app_atx : forall W1 W2 a n, disjoint_from W1 a n -> disjoint_from W2 a n -> disjoint_from (W1 ++ W2) a n.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a n D1 D2; cbn [app disjoint_from] in *; [exact D2|]. destruct D1 as [D0 D1]. split; [exact D0| exact (IH W2 a n D1 D2)]. Qed.

Local Ltac asf_atx G MU DJ := eapply rw_cells_transport_mo; [exact G| exact MU| cbn [cells_size csize Nat.add]; apply DJ; vm_compute; repeat first [ left; reflexivity | right ]].

Lemma asan_env_atx : forall (m m' : word -> option byte) W,
  asan_env asegs m -> munch (W ++ [(0x607628, 0x607630); (0x607728, 0x607730)]) m m' -> env_safe W -> asan_env asegs m'.
Proof.
  intros m m' W ((G1 & G2 & G3 & G4) & H & IE) MU SAFE.
  unfold A0_GOT_SHADOW, A0_SHADOW_CELL, A0_GOT_UAR, A0_UAR_CELL in *.
  assert (DJ : forall A n, In (A, n) env_cell_list -> disjoint_from (W ++ [(0x607628, 0x607630); (0x607728, 0x607730)]) A n).
  { intros A n HIn. apply djf_app_atx; [exact (env_safe_cells W SAFE A n HIn)|].
    unfold env_cell_list in HIn. repeat (destruct HIn as [E|HIn]; [inversion E; subst; cbn; repeat split; lia|]). destruct HIn. }
  split; [| split].
  - unfold asan_globals, A0_GOT_SHADOW, A0_SHADOW_CELL, A0_GOT_UAR, A0_UAR_CELL.
    split; [asf_atx G1 MU DJ|]. split; [asf_atx G2 MU DJ|]. split; [asf_atx G3 MU DJ| asf_atx G4 MU DJ].
  - destruct H as ([fw HF] & (b0 & b1 & b2 & HO) & D1 & D2 & D3 & D4 & D5 & D6). split; [| split].
    + exists fw. asf_atx HF MU DJ.
    + exists b0, b1, b2. asf_atx HO MU DJ.
    + split; [asf_atx D1 MU DJ|]. split; [asf_atx D2 MU DJ|]. split; [asf_atx D3 MU DJ|]. split; [asf_atx D4 MU DJ|]. split; [asf_atx D5 MU DJ|].
      eapply rw_cells_transport_mo; [exact D6| exact MU|]. replace (Z.of_nat (cells_size (desc_cells A0_DESCS))) with 5184 by (vm_compute; reflexivity).
      apply DJ. vm_compute. repeat first [ left; reflexivity | right ].
  - destruct IE as ((E1 & E2) & (L1 & L2) & I1 & R1 & M1 & C1 & F1 & (S1 & S2 & S3) & (O1 & O2) & K1 & A1 & (B1 & B2 & B3 & B4) & B5 & B6 & B7 & (B8a & B8b)).
    unfold icpt_env, env_shadow, env_layout, env_inited, env_ric, env_real_mem, env_cf, env_flags, env_real_str, env_real_io, env_ckpf, env_aflags, env_real_lib, env_real_lib2, env_got_rms, env_got_rmem, env_real_cmp in *.
    split; [split; [asf_atx E1 MU DJ| asf_atx E2 MU DJ]|]. split; [split; [asf_atx L1 MU DJ| asf_atx L2 MU DJ]|].
    split; [asf_atx I1 MU DJ|]. split; [asf_atx R1 MU DJ|]. split; [asf_atx M1 MU DJ|]. split; [asf_atx C1 MU DJ|]. split; [asf_atx F1 MU DJ|].
    split; [split; [asf_atx S1 MU DJ| split; [asf_atx S2 MU DJ| asf_atx S3 MU DJ]]|]. split; [split; [asf_atx O1 MU DJ| asf_atx O2 MU DJ]|].
    split; [asf_atx K1 MU DJ|]. split; [asf_atx A1 MU DJ|].
    split; [split; [asf_atx B1 MU DJ|]; split; [asf_atx B2 MU DJ|]; split; [asf_atx B3 MU DJ| asf_atx B4 MU DJ]|]. split; [asf_atx B5 MU DJ|]. split; [asf_atx B6 MU DJ|]. split; [asf_atx B7 MU DJ|]. split; [asf_atx B8a MU DJ| asf_atx B8b MU DJ].
Qed.

Lemma ratexitA_exitc_lit : forall (t : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  EXITC t m -> rw_cells asegs m 0x5e6b94 [C1 (Z_to_bv 8 0)] ->
  stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
  a0 = Z_to_bv 64 0x86484 ->
  lo <= bv_unsigned sp - 48 -> 0x608000 <= lo ->
  evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                         F (ret_pc ra) fc None m' (seg_rom asegs)
                /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x607608, 0x60760c); (0x607628, 0x607630); (0x607728, 0x607730)] m m'
                /\ wmono asegs m m' /\ mem_inv asegs m'
                /\ stk asegs m' lo (bv_unsigned sp)
                /\ EXITC2 t m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x955d0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros EX ICB ST MI E0 LO LOLO.
  exact (F_atexitA.ratexitA_exitc t ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo EX ICB ST MI E0 LO LOLO).
Qed.

Section T.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Variable PZ : mem -> Prop.
  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (MPAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 2^31.
  Hypothesis AC : am_contracts FI AI (JA FI AI).
  Hypothesis FPR : @fprintf_diag_stmt HC ASt.
  Hypothesis EXK : forall TID, 0 < TID < 2^31 -> exit_k_stmtA TID.
  Hypothesis FWR : @fwrite_diagA_stmt HC ASt.
  Hypothesis MCI : memcpy_i_stmt.
  Hypothesis RDF : read_front_stmt.
  Hypothesis RDB : read_back_stmt.
  Hypothesis BSR : forall s LB m b, RHEAP_A FI AI s LB m -> In b LB -> sh_readable m (blk_addr b) (blk_size b).

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE_A PZ sp0 argv envp uid hw rnd TID stdout_init).
  Notation FRAME' mm := (MFRAME sp0 argv mm MPAD S7 S6 S5 S4).
  Notation RUN0' := (RUN0 FI AI PZ sp0 argv envp uid hw rnd TID MPAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_parserA' := (rat_parserA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Local Notation K := (am_K FI AI).

  Notation TST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 RSVA) (Z_to_bv 64 0) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 RSVA) (Z_to_bv 64 0) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac trat p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
  Ltac trwalk p := do 48 (try (tryif trat p then fail else (zst; try (first [if_true | if_false])))).
  Ltac trb2 AG HP A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; apply HP; [unfold base_addr; cbn in Ha; lia| cbn in Ha; lia]].
  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_A2_of_A : forall (P : Z -> Prop) m m',
    BASE' m -> gagree_on P m m' ->
    (forall a, base_addr sp0 argv envp uid hw rnd a -> ~ ((0x607608 <= a < 0x60760c) \/ (0x607628 <= a < 0x607630) \/ (0x607728 <= a < 0x607730)) -> P a) ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' -> EXITC2 TID m' ->
    BASE_A2 PZ sp0 argv envp uid hw rnd TID stdout_init m'.
  Proof.
    intros P m m' (ST & MI & EX & MC & IMG & SE & SOF0 & RSS & SI & SZ & ENV & GSH & HPZ & CRT) AG HP MI' ST' RSS' ENV' EX2.
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|]. split; [exact EX2|].
    split. { destruct MC as (A1 & A2 & [G1 G2]). unfold MAINC0, ssp_cells, got_ssp, ssp_guard in *.
             split; [trb2 AG HP A1|]. split; [trb2 AG HP A2|]. split; [trb2 AG HP G1| trb2 AG HP G2]. }
    split; [eapply IMGK_agree; [exact AG| exact IMG| intros a Ha; apply HP; [unfold base_addr; lia| lia]]|].
    split; [eapply stderr_wfile0_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold stderr_addr in Ha; lia]| exact SE]|].
    split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold stdout_addr in Ha; lia]| exact SOF0]|].
    split; [exact RSS'|].
    split; [eapply stdin_file_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold stdin_addr in Ha; lia]| exact SI]|].
    split.
    { destruct SZ as ([Z1 R1] & [Z2 R2] & [Z3 R3] & [Z4 R4]).
      repeat split; (first [ eapply shz_agree; [exact AG| | | | eassumption] | eapply shr_agree; [exact AG| | | | eassumption] ]);
        unfold sh, SHADOW_OFF, SH_HI;
        first [ intros a Ha; apply HP; [unfold base_addr, pz_band, sh, SHADOW_OFF, SH_HI; Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia]
              | Z.div_mod_to_equations; lia ]. }
    split; [exact ENV'|].
    split; [eapply globals_shadow_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; lia| lia]| exact GSH]|].
    split; [eapply PZ_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold pz_band in Ha; lia]| exact HPZ]|].
    apply wr_at_crt.
  Qed.

  #[using="VSP CEIL"] Lemma tr_calls : forall (Q : machine_state -> Prop) x1 t0 t1 t2 (x9 a0 a1 : word) a2 a3 a4 a5 a6 a7 (x20 x21 : word) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (A cap L PLv : Z) (DATA junk : list byte),
    rw_cells asegs m A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk] ->
    6 + L <= Z.of_nat (length DATA) -> 0 <= L < 32768 -> (0x609000 <= A /\ A + cap + 16 <= alloc_ceiling /\ A mod 16 = 0 /\ win_ok A (cap + 16)) -> Z.of_nat (length DATA) <= cap -> 0 <= PLv < 2^27 ->
    (forall a0', evt asegs Q (TST (if PLv =? 0 then 0x863d4 else 0x86388) x1 t0 t1 t2 (Z_to_bv 64 PLv) x9 a0' a1 a2 a3 a4 a5 a6 a7
                                  (Z_to_bv 64 L) (Z_to_bv 64 (A + 2)) x20 (Z_to_bv 64 (1 + Z.land (if 0 <? L then znth (map bv_unsigned DATA) 2 else 0) 3)) t3 t4 t5 t6 F fc m)) ->
    evt asegs Q (TST 0x86374 x1 t0 t1 t2 (Z_to_bv 64 PLv) x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 (A + 2)) x20 x21 t3 t4 t5 t6 F fc m).
  Proof.
    intros until junk. intros BLK HL1 HL2 BR HCP HPL K.
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof alloc_ceiling_bounds as CB'. unfold LO in SF.
    pose proof BR as (BR1 & BR2 & BR3 & BR4).
    destruct (list6 DATA ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED).
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    zstep. if_cases K0; zify_cond K0.
    -
      replace (0 <? L) with false in K by (symmetry; apply Z.ltb_ge; rewrite ?unsigned_lit in K0 by lia; lia). cbn [Z.land Z.add] in K.
      zstep. zstep. if_cases K1; zify_cond K1.
      + replace (PLv =? 0) with false in K by (symmetry; apply Z.eqb_neq; rewrite ?unsigned_lit in K1 by lia; lia). apply K.
      + replace (PLv =? 0) with true in K by (symmetry; apply Z.eqb_eq; rewrite ?unsigned_lit in K1 by lia; lia). apply K.
    -
      replace (0 <? L) with true in K by (symmetry; apply Z.ltb_lt; rewrite ?unsigned_lit in K0 by lia; lia).
      rewrite ED in K. rewrite znth2_cons in K. rewrite ED in BLKB.
      pose proof (u8ro_read asegs m _ _ 2 d2 (wa (A + 2)) BLKB eq_refl ltac:(lia) eq_refl) as R2.
      zstep. clear R2. cbv beta. zstep. zstep.
      replace (Z.land (bv_unsigned d2) 3 + 1) with (1 + Z.land (bv_unsigned d2) 3) by lia.
      zstep. if_cases K1; zify_cond K1.
      + replace (PLv =? 0) with true in K by (symmetry; apply Z.eqb_eq; rewrite ?unsigned_lit in K1 by lia; lia). apply K.
      + replace (PLv =? 0) with false in K by (symmetry; apply Z.eqb_neq; rewrite ?unsigned_lit in K1 by lia; lia). apply K.
  Qed.

  #[using="AMS PZ_agree arg0 arg1 VSP CEIL VARGV ESF EARGV HT AC MCI BSR"] Lemma phaseT : forall b A cap DATA cw L cfg sc so ms g (Q : at_parser (ptr:=unit) -> ASt -> machine_state -> gst -> Prop),
    RUN0' b A cap DATA cw L cfg sc so ms g ->
    (forall ap so1 ms1 g1, rat_parserA' ap so1 ms1 g1 -> Q ap so1 ms1 g1) ->
    djM (main_tailA b (map bv_unsigned DATA) cw L cfg) so Q ms g.
  Proof.
    intros b A cap DATA cw L cfg sc so ms g Q RU HQ.
    destruct RU as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & junk & errv & kb
                    & -> & HD & HP0 & -> & BLK & BSH & FR & BA & CJ & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'. unfold LO in SF.
    pose proof BA as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. destruct MC as (G28 & GSE & SSP).
    unfold RERRNOA in ERR. unfold MFRAME in FR.
    pose proof HD as (HD1 & HD2 & HD3 & BR & HCW & HL & HL2 & HL3 & ECW & ECFG & HCFG & HSC & HCNT). unfold MAX_INPUT in HD3.
    pose proof BR as (BR1 & BR2 & BR3 & BR4).
    destruct CJ as [CI C2].
    assert (ICB : rw_cells asegs mm 0x5e6b94 [C1 (Z_to_bv 8 0)]).
    { pose proof CI as X. apply (proj1 (rw_cells_app _ _ _ [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3)] _)) in X. exact (proj2 X). }
    apply (proj1 (rw_cells_app _ _ _ [C1 (Z_to_bv 8 0)] _)) in CI. destruct CI as [CI _].
    unfold main_tailA. unfold HDR_MIN. unfold zlength. rewrite length_map.
    set (PL := Z.of_nat (length DATA) - 6 - L).

    assert (BLK' : id (rw_cells asegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk])) by exact BLK.
    assert (ERR' : id (rw_cells asegs mm 6190348 [C4 errv])) by exact ERR.
    assert (FR' : id (FRAME' mm)) by exact FR.
    assert (C2' : id (rw_cells asegs mm 0x5e6ba0 [CB 16 (repeat (Z_to_bv 8 0) 16)])) by exact C2.
    assert (BSH' : id (rw_cells asegs mm (sh A) (shadow_cells (block_shadow cap)))) by exact BSH. clear BSH.
    pose proof (munch_refl [(usp0 - 256, usp0 + -128); (0x5e6b90, 0x5e6b91); (0x607608, 0x60760c); (0x607628, 0x607630); (0x607728, 0x607730)] mm) as MU.
    pose proof (munch_refl [(usp0 - 208, usp0 + -128); (0x5e6b90, 0x5e6b91)] mm) as MU0.
    pose proof (wmono_refl asegs mm) as WM.
    eapply djM_evt; [| intros msr' H; exact H].

    zstep. zstep. zstep. zstep. zstep.
    zstep. carve_frame 80%nat ST.
    trwalk 0x955d0%Z. trat 0x955d0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (EXm : EXITC TID mx) by (eapply EXITC_munch; [exact MU0| exact WM| intros a Ha; unfold exitc_addr in Ha; cbn; lia| exact EX]) end.
    clear MU0.
    call_sp (ratexitA_exitc_lit TID); [first [exact EXm | exact ICB | exact ST | exact MI | reflexivity | lia] .. | ].
    trwalk 0x86374%Z. trat 0x86374%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m1 end.
    lazymatch goal with H : rw_cells asegs m1 (usp0 + -208) _ |- _ => rename H into TFR end.
    lazymatch goal with H : stk asegs m1 (usp0 - 8388608) _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells asegs m1 0x5e6b90 _ |- _ => rename H into C1' end.
    lazymatch goal with H : EXITC2 TID m1 |- _ => rename H into EX2 end.
    unfold id in BLK', ERR', FR', C2', BSH'.
    pose proof (gagree_on_of_munch _ _ _ MU WM) as AG1.
    assert (OUT1 : forall a, ((a < usp0 - 256 \/ usp0 - 128 <= a) /\ a <> 0x5e6b90 /\ ~ (0x607608 <= a < 0x60760c) /\ ~ (0x607628 <= a < 0x607630) /\ ~ (0x607728 <= a < 0x607730)) ->
                   (fun a0 : Z => outside [(usp0 - 256, usp0 + -128); (0x5e6b90, 0x5e6b91); (0x607608, 0x60760c); (0x607628, 0x607630); (0x607728, 0x607730)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (BLK1 : rw_cells asegs m1 A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]).
    { eapply rw_cells_gagree; [exact AG1| exact BLK'|]. intros a Ha. apply OUT1. cbn [cells_size csize Nat.add] in Ha. lia. }
    assert (ERR1 : rw_cells asegs m1 6190348 [C4 errv]).
    { eapply rw_cells_gagree; [exact AG1| exact ERR'|]. intros a Ha. apply OUT1. cbn in Ha. lia. }
    assert (FR1 : FRAME' m1).
    { unfold MFRAME. eapply rw_cells_gagree; [exact AG1| exact FR'|]. intros a Ha. apply OUT1. cbn in Ha. lia. }
    assert (C21 : rw_cells asegs m1 0x5e6ba0 [CB 16 (repeat (Z_to_bv 8 0) 16)]).
    { eapply rw_cells_gagree; [exact AG1| exact C2'|]. intros a Ha. apply OUT1. cbn in Ha. lia. }
    assert (BSH1 : rw_cells asegs m1 (sh A) (shadow_cells (block_shadow cap))).
    { eapply bshadow_transport; [lia| exact BSH'| exact MU| exact WM| cbn [disjoint_from]; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia]. }
    assert (HP1 : HEAP FI AI m1 g [(kb, A, cap)]).
    { destruct HP0 as (sA & stA & RH & RF & Eg). exists sA, stA. split; [| split; [| exact Eg]].
      - eapply (am_heap_frame FI AI); [exact RH| exact MU| exact WM|].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          first [ left; lia
                | right; left; exists 0x5d6b80, 0x5e6bc0; split; [apply AMS; unfold a0_static; lia| unfold a0_wsafe; lia]
                | right; left; exists 0x607600, 0x607820; split; [apply AMS; unfold a0_static; lia| unfold a0_wsafe; lia] ].
      - pose proof (fsb_ok FI) as FB. unfold app_mem in FB.
        eapply (rfake_frame FI); [exact RF| exact MU| exact WM|].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia. }
    assert (ENV1 : asan_env asegs m1).
    { apply (asan_env_atx mm m1 [(usp0 - 256, usp0 + -128); (0x5e6b90, 0x5e6b91); (0x607608, 0x60760c)]); [exact ENV| exact MU| env_safe_tac]. }
    assert (STF1 : stk asegs m1 (usp0 - 8388608) (usp0 + -128)).
    { eapply stk_merge; [exact ST1| | lia]. pose proof (stk_of_rw_cells asegs m1 _ _ TFR) as X. cbn [cells_size csize Nat.add] in X.
      replace (usp0 + -208 + Z.of_nat 80) with (usp0 + -128) in X by lia. exact X. }
    assert (BA1 : BASE_A2 PZ sp0 argv envp uid hw rnd TID stdout_init m1).
    { eapply BASE_A2_of_A; [exact BA| exact AG1| | exact MI1| unfold LO; exact STF1| | exact ENV1| exact EX2].
      - intros a Ha Hn. apply OUT1. unfold base_addr, exitc_addr, stdout_addr, stderr_addr, stdin_addr, pz_band, sh, SHADOW_OFF, SH_HI in *.
        clear -Ha Hn SF IL47 CB'. Z.div_mod_to_equations. lia.
      - pose proof BA as (_ & _ & _ & _ & _ & _ & _ & RSS0 & _). eapply stk_transport_disjoint; [exact RSS0| exact MU| exact WM| cbn [disjoint_from]; unfold RSVA; lia]. }
    assert (CJ1' : CJ1 m1) by (split; [exact C1'| exact C21]).
    clear AG1 MU WM BLK' ERR' FR' C2' OUT1 BSH'. try clear BLK. try clear ERR. try clear FR. try clear C2. try clear ST. try clear MI.
    try clear EX; try clear EXm; try clear EX2; try clear ICB; try clear G28; try clear GSE; try clear SSP; try clear IMG; try clear SE; try clear SOF; try clear RSS; try clear SI; try clear SZ; try clear ENV; try clear GSH; try clear HPZ; try clear CRT. clear BA HP0.

    eapply (tr_calls _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A cap L PL DATA junk BLK1); [lia| lia| exact BR| lia| lia|].
    intros a0x. rewrite <- ECFG.
    destruct (Z.eq_dec PL 0) as [PL0|PLP].
    -
      rewrite (proj2 (Z.eqb_eq PL 0) PL0). replace (0 <? PL) with false by (symmetry; apply Z.ltb_ge; lia).
      zstep. zstep. zstep. zstep.
      apply evt_done.
      apply djM_mret_bind. cbv beta iota. apply djM_ret.
      apply HQ.
      destruct HP1 as (sA & stA & RH & RF & Eg & FSL & NSI).
      unfold lb_bytes in NSI; cbn in NSI.
      unfold rat_parserA. do 16 eexists. exists F, fc, m1, A, cap, L, sc, EMPTY_OBJ_A, 0, DATA, junk, MPAD. do 1 eexists. exists errv, [(kb, A, cap)], sA, stA, kb.
      unfold ap_payload_len. cbn [ap_content ap_config_len ap_calls ap_owned ap_buf ap_count]. unfold HDR_MIN, zlength. rewrite length_map. fold PL. rewrite PL0.
      split; [reflexivity|]. split; [exact FRM|]. split; [reflexivity|]. split; [exact Eg|].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HCNT|].
      split; [pose proof (land3_range cfg); lia|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BR|].
      split; [repeat split; reflexivity|].
      split; [exact RH|]. split; [exact RF|]. split; [exact FSL|].
      split; [pose proof (land3_range cfg); unfold FZ_NSEC, A0_NSEC_MAX in *; lia|].
      split; [exact BLK1|]. split; [exact BSH1|]. split; [rewrite PL0 in TFR; exact TFR|]. split; [exact FR1|]. split; [exact ST1|].
      split; [exact BA1|]. split; [exact ERR1| exact CJ1'].
    -
      rewrite (proj2 (Z.eqb_neq PL 0) PLP). replace (0 <? PL) with true by (symmetry; apply Z.ltb_lt; lia).
      zstep. zstep. apply evt_done.
      apply djM_mret_bind2. apply djM_mret_bind. cbv beta iota.
      destruct HP1 as (sA & stA & RH & RF & Eg & FSL & NSI). subst g.
      unfold lb_bytes in NSI; cbn in NSI.
      pose proof (am_stack_ok FI AI) as SOK.
      pose proof BA1 as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. destruct MC as (G28 & GSE & SSP).
      eapply djM_seam.
      { eapply ((ac_malloc FI AI (JA FI AI) AC)) with (lo := usp0 - 8388608) (n := PL) (ras := []);
          rewrite ?unsigned_lit by lia;
          first [ exact RH | exact ENV | exact RF | exact ST1 | exact MI1 | reflexivity | lia | unfold A0_RT_STACK; lia | unfold A0_MAXREQ; lia
                | cbn [fpchain]; unfold valid_frame; lia
                | cbn; tauto
                | (apply (am_budget_short FI AI); [lia| cbn [length]; lia| repeat constructor; cbn; lia| unfold lb_bytes; cbn; lia| unfold A0_NSEC_MAX in *; lia])
                | clear -SF; Z.div_mod_to_equations; lia ]. }
      cbv beta. intros msr2 g2 (s2 & LB2 & -> & PO).
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & kp & A' & junk' & -> & AFR & -> & RH2 & NBLK & NBSH & WM2 & NS2).
      pose proof (am_block_range FI AI _ _ _ (kp, A', PL) RH2 ltac:(left; reflexivity)) as NBR. cbn [blk_addr blk_size fst snd] in NBR.
      pose proof (am_blocks_nodup FI AI _ _ _ RH2) as ND.
      assert (NE : kp <> kb).
      { intros E. pose proof ND as ND'. rewrite E in ND'. cbn [map blk_id fst] in ND'. inversion ND' as [|xh lt NI ND'']; subst. apply NI. constructor. }
      assert (DISJ : A' + PL <= A \/ A + cap <= A').
      { pose proof (am_blocks_disjoint FI AI _ _ _ (kp, A', PL) (kb, A, cap) RH2 ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
        cbn [blk_addr blk_size fst snd] in D. apply D. intros E. apply NE. congruence. }
      assert (BA2 : BASE_A2 PZ sp0 argv envp uid hw rnd TID stdout_init m2) by (eapply (BASE_A2_alloc_q FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init (usp0 + -208)); [unfold LO; lia| exact BA1| unfold LO; exact AFR]).
      destruct AFR as (MI2 & ST2 & ENV2 & RF2 & AP2).
      assert (FR2 : FRAME' m2) by (unfold MFRAME in *; eapply (apres_rw_cells FI AI); [exact AP2| exact FR1| apply aclient_range_above; lia]).
      lazymatch type of TFR with rw_cells _ _ _ ?cs =>
        assert (TFR2 : rw_cells asegs m2 (usp0 + -208) cs) by (eapply (apres_rw_cells FI AI); [exact AP2| exact TFR| apply aclient_range_above; lia]) end.
      assert (CJ2 : CJ1 m2).
      { destruct CJ1' as [X1 X2]. split; (eapply (apres_rw_cells FI AI); [exact AP2| eassumption| eapply (aclient_range_static FI AI _ _ _ _ 0x5d6b80 0x5e6bc0); [apply AMS; unfold a0_static; lia| cbn; lia| cbn; lia]]). }
      assert (ERR2 : rw_cells asegs m2 6190348 [C4 errv]).
      { eapply (apres_rw_cells FI AI); [exact AP2| exact ERR1| eapply (aclient_range_static FI AI _ _ _ _ 0x5e7508 0x5e7510); [apply AMS; unfold a0_static; lia| cbn; lia| cbn; lia]]. }
      assert (BLK2 : rw_cells asegs m2 A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]).
      { eapply (apres_rw_cells FI AI); [exact AP2| exact BLK1| eapply aclient_range_block; [left; reflexivity| cbn; lia| cbn -[Z.of_nat Z.add]; simpl_sizes; lia]]. }
      pose proof (am_block_shadow FI AI _ _ _ (kb, A, cap) RH2 ltac:(right; left; reflexivity)) as BSH2. cbn [blk_addr blk_size fst snd] in BSH2.
      clear AP2 WM2 TFR FR1 BLK1 ST1 MI1 ERR1 CJ1' BA1 BSH1 ST MI EX G28 GSE SSP IMG SE SOF RSS SI SZ ENV GSH HPZ CRT STF1 ENV1.
      pose proof BA2 as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. destruct MC as (G28 & GSE & SSP).
      replace (ret_pc (Z_to_bv 64 0x86390)) with (Z_to_bv 64 0x86390) by (symmetry; rpc).

      pose proof BLK2 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in SRC. destruct SRC as [SRC _].
      pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
      assert (PAYB : bytes_at asegs m2 (A + 6 + L) (skipn (Z.to_nat (6 + L)) DATA)).
      { rewrite <- (firstn_skipn (Z.to_nat (6 + L)) DATA) in SRCB. apply bytes_at_app in SRCB. destruct SRCB as [_ X].
        rewrite length_firstn in X. replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length DATA))) with (A + 6 + L) in X by lia. exact X. }
      eapply djM_evt; [| intros msr' H; exact H].
      zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
      zstep. zstep. zstep. zstep.

      eapply evt_cut.
      { eapply (memcpy_i_callq MCI (usp0 - 8388608)) with (src := skipn (Z.to_nat (6 + L)) DATA) (junk := junk'); rewrite ?unsigned_lit by lia;
          first [ exact PAYB | exact MI2 | exact ENV2 | exact ST2 | rewrite length_skipn; lia | lia
                | exact NBLK
                | unfold A0_RT_STACK; lia | env_safe_tac | idtac ].
        - split; [| split; [| unfold win_ok in *; lia]].
          + eapply (accessible_of_block_shadow m2 A' PL); [exact NBSH | clear -NBR; Z.div_mod_to_equations; lia | lia | reflexivity | lia | lia].
          + eapply sh_readable_sub; [eapply (BSR s2 _ m2 (kp, A', PL)); [exact RH2| left; reflexivity] | cbn; lia | cbn; lia | lia].
        - split; [| split; [| unfold win_ok in *; lia]].
          + eapply (accessible_of_block_shadow m2 A cap); [exact BSH2 | clear -BR3; Z.div_mod_to_equations; lia | lia | reflexivity | lia | lia].
          + eapply sh_readable_sub; [eapply (BSR s2 _ m2 (kb, A, cap)); [exact RH2| right; left; reflexivity] | cbn; lia | cbn; lia | lia].
        - pose proof (@alloc_ceiling_bounds HC) as CBX; unfold icpt_rng, icpt_win, win_ok, RSVA in *; lia.
        - pose proof (@alloc_ceiling_bounds HC) as CBX; unfold icpt_rng, icpt_win, win_ok, RSVA in *; lia. }
      cbv beta. intros ms' PO.
      destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MUc & WMc & MI3 & ST3 & ENV3 & NB3 & _).
      rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia.
      replace (ret_pc (Z_to_bv 64 0x863a4)) with (Z_to_bv 64 0x863a4) by (symmetry; rpc).
      assert (RH3 : RHEAP_A FI AI s2 [(kp, A', PL); (kb, A, cap)] m3).
      { eapply (am_heap_frame FI AI); [exact RH2| exact MUc| exact WMc|].
        apply Forall_cons; [| apply Forall_cons; [left; cbn; lia| apply Forall_nil]].
        right; right; left. exists (kp, A', PL). split; [left; reflexivity|]. cbn. lia. }
      assert (RF3 : RFAKE FI stA m3).
      { pose proof (fsb_ok FI) as FB. unfold app_mem in FB.
        eapply (rfake_frame FI); [exact RF2| exact MUc| exact WMc|].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia. }
      assert (WOKW : Forall (WOKA sp0) [(A', A' + PL); (usp0 - 8388608, usp0 + -208)]).
      { unfold WOKA. constructor; [right; right; cbn [fst snd]; split; [lia| split; [lia| app_iv_tac]]|]. constructor; [left; cbn [fst snd]; unfold LO; lia| constructor]. }
      assert (STF3 : stk asegs m3 (usp0 - 8388608) (usp0 + -128)).
      { assert (HQ' : usp0 - 8388608 <= usp0 + -208 <= usp0 + -128) by lia. destruct (stk_split asegs m2 _ (usp0 + -208) _ ST HQ') as [_ SThi].
        eapply stk_merge; [exact ST3| | lia]. eapply stk_transport_disjoint; [exact SThi| exact MUc| exact WMc| cbn [disjoint_from]; lia]. }
      assert (BA3 : BASE_A2 PZ sp0 argv envp uid hw rnd TID stdout_init m3) by (eapply (BASE_A2_munch PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA2| exact WOKW| exact MUc| exact WMc| exact MI3| unfold LO; exact STF3| exact ENV3]).
      assert (CJ3 : CJ1 m3).
      { destruct CJ2 as [X1 X2]. split; (eapply rw_cells_transport; [eassumption| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]). }
      assert (ERR3 : rw_cells asegs m3 6190348 [C4 errv]).
      { eapply rw_cells_transport; [exact ERR2| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]. }
      assert (FR3 : FRAME' m3).
      { unfold MFRAME in *. eapply rw_cells_transport; [exact FR2| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]. }
      lazymatch type of TFR2 with rw_cells _ _ _ ?cs =>
        assert (TFR3 : rw_cells asegs m3 (usp0 + -208) cs) by (eapply rw_cells_transport; [exact TFR2| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]) end.
      assert (BLK3 : rw_cells asegs m3 A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]).
      { eapply rw_cells_transport; [exact BLK2| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]. }
      pose proof (am_block_shadow FI AI _ _ _ (kb, A, cap) RH3 ltac:(right; left; reflexivity)) as BSH3. cbn [blk_addr blk_size fst snd] in BSH3.
      pose proof (am_block_shadow FI AI _ _ _ (kp, A', PL) RH3 ltac:(left; reflexivity)) as NBSH3. cbn [blk_addr blk_size fst snd] in NBSH3.
      clear MUc WMc WOKW.

      zstep. zstep. zstep. zstep.
      apply evt_done. apply djM_ret.
      apply HQ.
      unfold rat_parserA. do 16 eexists. exists F, fc, m3, A, cap, L, sc, A', A', DATA, junk, MPAD. do 1 eexists. exists errv, [(kp, A', PL); (kb, A, cap)], s2, stA, kb.
      unfold ap_payload_len. cbn [ap_content ap_config_len ap_calls ap_owned ap_buf ap_count]. unfold HDR_MIN, zlength. rewrite length_map. fold PL.
      split; [reflexivity|]. split; [exact FRM|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HCNT|].
      split; [pose proof (land3_range cfg); lia|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BR|].
      split; [exists kp; split; [lia|]; split; [reflexivity|]; split; [reflexivity|]; split; [exact NB3| exact NBSH3]|].
      split; [exact RH3|]. split; [exact RF3|]. split; [exact FSL|].
      split; [pose proof (land3_range cfg); rewrite NS2; destruct (a0_cls PL =? 0); unfold FZ_NSEC, A0_NSEC_MAX in *; lia|].
      split; [exact BLK3|]. split; [exact BSH3|]. split; [exact TFR3|]. split; [exact FR3|]. split; [exact ST3|].
      split; [exact BA3|]. split; [exact ERR3| exact CJ3].
  Qed.
End T.

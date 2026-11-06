(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_exit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import AssembleA0.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma u64ro_read : forall m A ws (i : Z) w a,
  bytes_at asegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
  ov_read_bytes asegs m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read asegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Definition RERRNOA : Z := 0x5e68cc.

Section AgreeKit.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.

  #[using="Type"] Lemma apres_agree : forall LB q m m', apres FI AI LB q m m' -> gagree_on (aclient FI AI LB q) m m'.
  Proof. intros LB q m m' H a Ha Hc. exact (H a Ha Hc). Qed.

  #[using="Type"] Lemma shz_agree : forall (P : Z -> Prop) m m' lo hi, gagree_on P m m' -> (forall a, lo <= a < hi -> P a) ->
    0 <= lo -> hi <= 2^64 -> shz m lo hi -> shz m' lo hi.
  Proof.
    intros P m m' lo hi AG HP H0 H1 Z a Ha. exact (gkeep_mrd _ _ _ _ (proj1 (AG a ltac:(lia) (HP a Ha))) (Z a Ha)).
  Qed.
  #[using="Type"] Lemma shr_agree : forall (P : Z -> Prop) m m' lo hi, gagree_on P m m' -> (forall a, lo <= a < hi -> P a) ->
    0 <= lo -> hi <= 2^64 -> shr m lo hi -> shr m' lo hi.
  Proof.
    intros P m m' lo hi AG HP H0 H1 R a Ha. destruct (R a Ha) as [v Hv]. exists v. exact (gkeep_mrd _ _ _ v (proj1 (AG a ltac:(lia) (HP a Ha))) Hv).
  Qed.
End AgreeKit.

Section A.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.

  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.

  Variable PZ : mem -> Prop.
  Definition pz_band (a : Z) : Prop :=
    (0x10000 <= a < 0xabde8) \/ (0xae6c0 <= a < 0xaeac8) \/ (0x5e5f80 <= a < 0x5e5fa0) \/ (0x5e5fc0 <= a < 0x5e6060) \/ (0x7fffa000 <= a < 0x800b9200).

  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.

  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (TID : Z).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis HT : 0 < TID < 2^31.

  Variable SO : stdout_st.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).

  #[using="VSP CEIL"] Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ alloc_ceiling = LO' /\ LO' + 8388608 = usp0.
  Proof. destruct VSP as (A & B & C). rewrite CEIL. unfold LO, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.

  #[using="ESF"] Lemma IMGB_len47 : usp0 + Z.of_nat (length IMGB) <= 2^47.
  Proof.
    pose proof (build_stack_bytes_within_span rph sp0 argv envp uid hw rnd). unfold entry_stack_fits, sp_window_hi in ESF. lia.
  Qed.

  Definition MAINC0 (mm : mem) : Prop :=
    rw_cells asegs mm 0xaad30 [C8 (Z_to_bv 64 0xa9fc8); C8 z64]
    /\ rw_cells asegs mm 0xa9fc8 [C8 (Z_to_bv 64 0xaeac8)]
    /\ ssp_cells mm guard_word.
  Definition CJ0 (mm : mem) : Prop :=
    rw_cells asegs mm 0x5e5f50 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 0)] /\ rw_cells asegs mm 0x5e5f60 [CB 16 (repeat (Z_to_bv 8 0) 16)].

  Definition BASE_A (mm : mem) : Prop :=
    stk asegs mm LO' (usp0 + -128) /\ mem_inv asegs mm /\ EXITC TID mm /\ MAINC0 mm /\ IMGK sp0 argv envp uid hw rnd mm
    /\ stderr_wfile0 mm /\ stdout_file mm SO /\ stk asegs mm RSVA (RSVA + 65536) /\ stdin_file mm
    /\ SHZ sp0 argv envp uid hw rnd mm /\ asan_env asegs mm /\ globals_shadow mm /\ PZ mm /\ wr_at asegs mm 0xb0290 1.

  Definition base_addr (a : Z) : Prop :=
    exitc_addr a \/ (0xaad30 <= a < 0xaad40) \/ (0xa9fc8 <= a < 0xa9fd0) \/ (0xaad68 <= a < 0xaad70) \/ (0x6069b0 <= a < 0x6069b8)
    \/ (usp0 <= a < usp0 + Z.of_nat (length IMGB))
    \/ stdout_addr a \/ stderr_addr a \/ stdin_addr a
    \/ (0x7fffa000 <= a < 0x800b9200) \/ (sh alloc_ceiling - sh alloc_ceiling mod 8 <= a < SH_HI)
    \/ pz_band a.

  Definition BASE_A2 (mm : mem) : Prop :=
    stk asegs mm LO' (usp0 + -128) /\ mem_inv asegs mm /\ EXITC2 TID mm /\ MAINC0 mm /\ IMGK sp0 argv envp uid hw rnd mm
    /\ stderr_wfile0 mm /\ stdout_file mm SO /\ stk asegs mm RSVA (RSVA + 65536) /\ stdin_file mm
    /\ SHZ sp0 argv envp uid hw rnd mm /\ asan_env asegs mm /\ globals_shadow mm /\ PZ mm /\ wr_at asegs mm 0xb0290 1.

  Definition base_addr2 (a : Z) : Prop := base_addr a \/ (0x5e5f54 <= a < 0x5e5f55).

  #[using="Type"] Lemma wr_at_crt : forall mm : mem, wr_at asegs mm 0xb0290 1.
  Proof.
    intros mm. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i.
    unfold wview. destruct (mm (wa (721552 + 0))); [discriminate|]. vm_compute. discriminate.
  Qed.

  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_A_agree0 : forall (P : Z -> Prop) m m',
    BASE_A m -> gagree_on P m m' -> (forall a, base_addr a -> P a) ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' ->
    BASE_A m'.
  Proof.
    intros P m m' (ST & MI & EX & MC & IMG & SE & SOF0 & RSS & SI & SZ & ENV & GSH & HPZ & CRT) AG HP MI' ST' RSS' ENV'.
    pose proof sp_facts as SF. pose proof IMGB_len47 as IL. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|].
    split; [eapply EXITC_agree; [exact AG| intros a Ha; apply HP; left; exact Ha| exact EX]|].
    split. { destruct MC as (A1 & A2 & [G1 G2]). unfold MAINC0, ssp_cells, got_ssp, ssp_guard in *.
             Ltac trb AG HP A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; apply HP; unfold base_addr; cbn in Ha; lia].
             split; [trb AG HP A1|]. split; [trb AG HP A2|]. split; [trb AG HP G1| trb AG HP G2]. }
    split; [eapply IMGK_agree; [exact AG| exact IMG| intros a Ha; apply HP; unfold base_addr; lia]|].
    split; [eapply stderr_wfile0_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact SE]|].
    split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact SOF0]|].
    split; [exact RSS'|].
    split; [eapply stdin_file_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact SI]|].
    split.
    { destruct SZ as ([Z1 R1] & [Z2 R2] & [Z3 R3] & [Z4 R4]).
      repeat split; (first [ eapply shz_agree; [exact AG| | | | eassumption] | eapply shr_agree; [exact AG| | | | eassumption] ]);
        unfold sh, SHADOW_OFF, SH_HI;
        first [ intros a Ha; apply HP; unfold base_addr, pz_band, sh, SHADOW_OFF, SH_HI; Z.div_mod_to_equations; lia
              | Z.div_mod_to_equations; lia ]. }
    split; [exact ENV'|].
    split; [eapply globals_shadow_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; lia| exact GSH]|].
    split; [eapply PZ_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact HPZ]|].
    apply wr_at_crt.
  Qed.
  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_A_agree : forall (P : Z -> Prop) m m',
    BASE_A m -> gagree_on P m m' -> (forall a, base_addr a -> P a) -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' ->
    BASE_A m'.
  Proof. intros P m m' BA AG HP _. eapply BASE_A_agree0; eassumption. Qed.

  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_A_agree_se : forall (P : Z -> Prop) m m',
    BASE_A m -> gagree_on P m m' -> (forall a, base_addr a -> ~ stderr_addr a -> P a) -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' -> stderr_wfile0 m' ->
    BASE_A m'.
  Proof.
    intros P m m' (ST & MI & EX & MC & IMG & SE & SOF0 & RSS & SI & SZ & ENV & GSH & HPZ & CRT) AG HP WM MI' ST' RSS' ENV' SE'.
    pose proof sp_facts as SF. pose proof IMGB_len47 as IL. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|].
    split; [eapply EXITC_agree; [exact AG| intros a Ha; apply HP; [left; exact Ha| unfold exitc_addr in Ha; unfold stderr_addr; lia]| exact EX]|].
    split. { destruct MC as (A1 & A2 & [G1 G2]). unfold MAINC0, ssp_cells, got_ssp, ssp_guard in *.
             Ltac trbs AG HP A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; apply HP; unfold base_addr, stderr_addr; cbn in Ha; lia].
             split; [trbs AG HP A1|]. split; [trbs AG HP A2|]. split; [trbs AG HP G1| trbs AG HP G2]. }
    split; [eapply IMGK_agree; [exact AG| exact IMG| intros a Ha; apply HP; unfold base_addr, stderr_addr; lia]|].
    split; [exact SE'|].
    split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold stdout_addr in Ha; unfold stderr_addr; lia]| exact SOF0]|].
    split; [exact RSS'|].
    split; [eapply stdin_file_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold stdin_addr in Ha; unfold stderr_addr; lia]| exact SI]|].
    split.
    { destruct SZ as ([Z1 R1] & [Z2 R2] & [Z3 R3] & [Z4 R4]).
      repeat split; (first [ eapply shz_agree; [exact AG| | | | eassumption] | eapply shr_agree; [exact AG| | | | eassumption] ]);
        unfold sh, SHADOW_OFF, SH_HI;
        first [ intros a Ha; apply HP; unfold base_addr, pz_band, stderr_addr, sh, SHADOW_OFF, SH_HI; Z.div_mod_to_equations; lia
              | Z.div_mod_to_equations; lia ]. }
    split; [exact ENV'|].
    split; [eapply globals_shadow_agree; [exact AG| intros a Ha; apply HP; unfold base_addr, stderr_addr; lia| exact GSH]|].
    split; [eapply PZ_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold pz_band in Ha; unfold stderr_addr; lia]| exact HPZ]|].
    eapply wr_at_transport; [exact CRT| exact WM].
  Qed.

  Definition WOKA (iv : Z * Z) : Prop :=
    (LO' <= fst iv /\ snd iv <= usp0 + -128) \/ (fst iv = RERRNOA /\ snd iv = RERRNOA + 4)
    \/ (0x609000 <= fst iv /\ snd iv <= alloc_ceiling /\ app_iv iv).

  Definition WOKRA (iv : Z * Z) : Prop := WOKA iv \/ (RSVA <= fst iv /\ snd iv <= RSVA + 65536).

  #[using="Type"] Lemma WOKA_WOKRA : forall W, Forall WOKA W -> Forall WOKRA W.
  Proof. intros W H. eapply Forall_impl; [| exact H]. intros iv Hiv. left. exact Hiv. Qed.

  #[using="VSP CEIL ESF"] Lemma WOKRA_outside : forall W a, Forall WOKRA W -> base_addr a -> outside W a.
  Proof.
    pose proof sp_facts as SF. pose proof IMGB_len47 as IL. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOKRA, WOKA, LO, RERRNOA, RSVA, app_iv, SH_HI in H1. cbn [fst snd] in H1.
    unfold base_addr, exitc_addr, stdout_addr, stderr_addr, stdin_addr, pz_band, sh, SHADOW_OFF, SH_HI in Ha.
    Z.div_mod_to_equations. lia.
  Qed.

  #[using="VSP CEIL"] Lemma WOKRA_app : forall W, Forall WOKRA W -> app_ivs W.
  Proof.
    pose proof sp_facts as SF. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    intros W H. unfold app_ivs. eapply Forall_impl; [| exact H]. intros [lo1 hi1] Hiv.
    unfold WOKRA, WOKA, LO, RERRNOA, RSVA in Hiv. unfold app_iv, SH_HI in *. cbn [fst snd] in *. lia.
  Qed.

  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_A_munchR : forall W m m', BASE_A m -> Forall WOKRA W -> munch W m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' -> BASE_A m'.
  Proof.
    intros W m m' BA HW MU WM MI' ST' RSS' ENV'.
    eapply BASE_A_agree; [exact BA| eapply gagree_on_of_munch; [exact MU| exact WM]| intros a Ha; cbn beta; apply WOKRA_outside; assumption| exact WM| exact MI'| exact ST'| exact RSS'| exact ENV'].
  Qed.

  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_A_munch : forall W m m', BASE_A m -> Forall WOKA W -> munch W m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> asan_env asegs m' -> BASE_A m'.
  Proof.
    intros W m m' BA HW MU WM MI' ST' ENV'. pose proof sp_facts as SF. unfold LO in *.
    eapply BASE_A_munchR; [exact BA| apply WOKA_WOKRA; exact HW| exact MU| exact WM| exact MI'| exact ST'| | exact ENV'].
    destruct BA as (_ & _ & _ & _ & _ & _ & _ & RSS & _).
    eapply stk_transport_disjoint; [exact RSS| exact MU| exact WM|].
    clear - HW SF. unfold RSVA. induction W as [|[lo1 hi1] W IH]; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; exact H2].
    unfold WOKA, LO, RERRNOA in H1. cbn [fst snd] in H1. pose proof alloc_ceiling_bounds. lia.
  Qed.

  #[using="AMS VSP CEIL ESF"] Lemma base_addr_aclient : forall LB a, base_addr a -> aclient FI AI LB (usp0 + -128) a.
  Proof.
    pose proof sp_facts as SF. pose proof IMGB_len47 as IL. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    intros LB a Ha. unfold base_addr, exitc_addr, stdout_addr, stderr_addr, stdin_addr, pz_band in Ha.
    Ltac band AMS l h := right; left; exists l, h; split; [apply AMS; unfold a0_static; split; [lia|]; lia | lia].
    repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end.
    all: try (left; lia).
    all: try (band AMS 0x10000 0xabde8). all: try (band AMS 0xae6c0 0xaedc0). all: try (band AMS 0x5e5f80 0x5e5fa0). all: try (band AMS 0x5e5fc0 0x5e6060).
    all: try (band AMS 0x5e68c8 0x5e68d0). all: try (band AMS 0x6069b0 0x6069b8). all: try (band AMS 0x6069c0 0x606be0). all: try (band AMS 0x1457a0 0x1457a1). all: try (band AMS 0x606be0 0x606be4).
    all: try (band AMS 0x606c00 0x606c08). all: try (band AMS 0x606fc0 0x607480). all: try (band AMS 0x7fffa000 0x800b9200).

    right; left. exists (sh alloc_ceiling - sh alloc_ceiling mod 8), 0x10007fff8000. unfold SH_HI in Ha. split; [| lia].
    apply AMS. exact a0_static_s6.
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma BASE_A_alloc : forall LB st m m', BASE_A m -> alloc_frame_A FI AI (usp0 + -128) LO' st m m' LB -> BASE_A m'.
  Proof.
    intros LB st m m' BA (MI' & ST' & ENV' & RF' & AP). pose proof sp_facts as SF. unfold LO in *.
    pose proof (apres_agree FI AI _ _ _ _ AP) as AG.
    eapply BASE_A_agree0; [exact BA| exact AG| intros a Ha; apply base_addr_aclient; exact Ha| exact MI'| exact ST'| | exact ENV'].
    destruct BA as (_ & _ & _ & _ & _ & _ & _ & RSS & _).
    eapply stk_gagree; [exact AG| exact RSS|]. intros a Ha. right; left. exists 0x5d5f40, 0x5e5f80. split; [apply AMS; unfold a0_static; lia| unfold RSVA in Ha; lia].
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma BASE_A_alloc_q : forall q LB st m m', LO' <= q <= usp0 + -128 -> BASE_A m -> alloc_frame_A FI AI q LO' st m m' LB -> BASE_A m'.
  Proof.
    intros q LB st m m' HQ BA (MI' & ST' & ENV' & RF' & AP). pose proof sp_facts as SF. unfold LO in *.
    pose proof (apres_agree FI AI _ _ _ _ AP) as AG.
    assert (HA : forall a, base_addr a -> aclient FI AI LB q a).
    { intros a Ha. pose proof (base_addr_aclient LB a Ha) as X. unfold aclient in *. destruct X as [X|X]; [left; lia| right; exact X]. }
    eapply BASE_A_agree0; [exact BA| exact AG| exact HA| exact MI'| | | exact ENV'].
    - destruct BA as (ST & _). assert (HQ' : usp0 - 8388608 <= q <= usp0 + -128) by lia. destruct (stk_split asegs m _ q _ ST HQ') as [_ STq].
      eapply stk_merge; [exact ST'| | unfold LO; lia]. eapply stk_gagree; [exact AG| exact STq| intros a Ha; left; lia].
    - destruct BA as (_ & _ & _ & _ & _ & _ & _ & RSS & _).
      eapply stk_gagree; [exact AG| exact RSS|]. intros a Ha. right; left. exists 0x5d5f40, 0x5e5f80. split; [apply AMS; unfold a0_static; lia| unfold RSVA in Ha; lia].
  Qed.

  Ltac bx_tr AG HP A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; apply HP; unfold base_addr; cbn in Ha; lia].
  Ltac bx_trs AG HP A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; apply HP; unfold base_addr, stderr_addr; cbn in Ha; lia].

  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_A2_agree0 : forall (P : Z -> Prop) m m',
    BASE_A2 m -> gagree_on P m m' -> (forall a, base_addr2 a -> P a) ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' ->
    BASE_A2 m'.
  Proof.
    intros P m m' (ST & MI & EX & MC & IMG & SE & SOF0 & RSS & SI & SZ & ENV & GSH & HPZ & CRT) AG HP2 MI' ST' RSS' ENV'.
    assert (HP : forall a, base_addr a -> P a) by (intros a Ha; apply HP2; left; exact Ha).
    pose proof sp_facts as SF. pose proof IMGB_len47 as IL. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|].
    split; [eapply EXITC2_agree; [exact AG| intros a Ha; apply HP2; destruct Ha as [Ha|Ha]; [left; left; exact Ha| right; exact Ha]| exact EX]|].
    split. { destruct MC as (A1 & A2 & [G1 G2]). unfold MAINC0, ssp_cells, got_ssp, ssp_guard in *.
             split; [bx_tr AG HP A1|]. split; [bx_tr AG HP A2|]. split; [bx_tr AG HP G1| bx_tr AG HP G2]. }
    split; [eapply IMGK_agree; [exact AG| exact IMG| intros a Ha; apply HP; unfold base_addr; lia]|].
    split; [eapply stderr_wfile0_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact SE]|].
    split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact SOF0]|].
    split; [exact RSS'|].
    split; [eapply stdin_file_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact SI]|].
    split.
    { destruct SZ as ([Z1 R1] & [Z2 R2] & [Z3 R3] & [Z4 R4]).
      repeat split; (first [ eapply shz_agree; [exact AG| | | | eassumption] | eapply shr_agree; [exact AG| | | | eassumption] ]);
        unfold sh, SHADOW_OFF, SH_HI;
        first [ intros a Ha; apply HP; unfold base_addr, pz_band, sh, SHADOW_OFF, SH_HI; Z.div_mod_to_equations; lia
              | Z.div_mod_to_equations; lia ]. }
    split; [exact ENV'|].
    split; [eapply globals_shadow_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; lia| exact GSH]|].
    split; [eapply PZ_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact HPZ]|].
    apply wr_at_crt.
  Qed.
  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_A2_agree : forall (P : Z -> Prop) m m',
    BASE_A2 m -> gagree_on P m m' -> (forall a, base_addr2 a -> P a) -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' ->
    BASE_A2 m'.
  Proof. intros P m m' BA AG HP _. eapply BASE_A2_agree0; eassumption. Qed.

  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_A2_agree_se : forall (P : Z -> Prop) m m',
    BASE_A2 m -> gagree_on P m m' -> (forall a, base_addr2 a -> ~ stderr_addr a -> P a) -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' -> stderr_wfile0 m' ->
    BASE_A2 m'.
  Proof.
    intros P m m' (ST & MI & EX & MC & IMG & SE & SOF0 & RSS & SI & SZ & ENV & GSH & HPZ & CRT) AG HP2 WM MI' ST' RSS' ENV' SE'.
    assert (HP : forall a, base_addr a -> ~ stderr_addr a -> P a) by (intros a Ha Hs; apply HP2; [left; exact Ha| exact Hs]).
    pose proof sp_facts as SF. pose proof IMGB_len47 as IL. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|].
    split; [eapply EXITC2_agree; [exact AG| intros a Ha; apply HP2; [destruct Ha as [Ha|Ha]; [left; left; exact Ha| right; exact Ha]| unfold exitc2_addr, exitc_addr in Ha; unfold stderr_addr; lia]| exact EX]|].
    split. { destruct MC as (A1 & A2 & [G1 G2]). unfold MAINC0, ssp_cells, got_ssp, ssp_guard in *.
             split; [bx_trs AG HP A1|]. split; [bx_trs AG HP A2|]. split; [bx_trs AG HP G1| bx_trs AG HP G2]. }
    split; [eapply IMGK_agree; [exact AG| exact IMG| intros a Ha; apply HP; unfold base_addr, stderr_addr; lia]|].
    split; [exact SE'|].
    split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold stdout_addr in Ha; unfold stderr_addr; lia]| exact SOF0]|].
    split; [exact RSS'|].
    split; [eapply stdin_file_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold stdin_addr in Ha; unfold stderr_addr; lia]| exact SI]|].
    split.
    { destruct SZ as ([Z1 R1] & [Z2 R2] & [Z3 R3] & [Z4 R4]).
      repeat split; (first [ eapply shz_agree; [exact AG| | | | eassumption] | eapply shr_agree; [exact AG| | | | eassumption] ]);
        unfold sh, SHADOW_OFF, SH_HI;
        first [ intros a Ha; apply HP; unfold base_addr, pz_band, stderr_addr, sh, SHADOW_OFF, SH_HI; Z.div_mod_to_equations; lia
              | Z.div_mod_to_equations; lia ]. }
    split; [exact ENV'|].
    split; [eapply globals_shadow_agree; [exact AG| intros a Ha; apply HP; unfold base_addr, stderr_addr; lia| exact GSH]|].
    split; [eapply PZ_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold pz_band in Ha; unfold stderr_addr; lia]| exact HPZ]|].
    eapply wr_at_transport; [exact CRT| exact WM].
  Qed.

  #[using="VSP CEIL ESF"] Lemma WOKRA_outside2 : forall W a, Forall WOKRA W -> base_addr2 a -> outside W a.
  Proof.
    pose proof sp_facts as SF. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    intros W a HW [Ha|Ha]; [apply WOKRA_outside; assumption|].
    induction W as [|[lo1 hi1] W IH]; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOKRA, WOKA, LO, RERRNOA, RSVA, app_iv, SH_HI in H1. cbn [fst snd] in H1.
    Z.div_mod_to_equations. lia.
  Qed.

  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_A2_munchR : forall W m m', BASE_A2 m -> Forall WOKRA W -> munch W m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' -> BASE_A2 m'.
  Proof.
    intros W m m' BA HW MU WM MI' ST' RSS' ENV'.
    eapply BASE_A2_agree; [exact BA| eapply gagree_on_of_munch; [exact MU| exact WM]| intros a Ha; cbn beta; apply WOKRA_outside2; assumption| exact WM| exact MI'| exact ST'| exact RSS'| exact ENV'].
  Qed.

  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_A2_munch : forall W m m', BASE_A2 m -> Forall WOKA W -> munch W m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> asan_env asegs m' -> BASE_A2 m'.
  Proof.
    intros W m m' BA HW MU WM MI' ST' ENV'. pose proof sp_facts as SF. unfold LO in *.
    eapply BASE_A2_munchR; [exact BA| apply WOKA_WOKRA; exact HW| exact MU| exact WM| exact MI'| exact ST'| | exact ENV'].
    destruct BA as (_ & _ & _ & _ & _ & _ & _ & RSS & _).
    eapply stk_transport_disjoint; [exact RSS| exact MU| exact WM|].
    clear - HW SF. unfold RSVA. induction W as [|[lo1 hi1] W IH]; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; exact H2].
    unfold WOKA, LO, RERRNOA in H1. cbn [fst snd] in H1. pose proof alloc_ceiling_bounds. lia.
  Qed.

  #[using="AMS VSP CEIL ESF"] Lemma base_addr2_aclient : forall LB a, base_addr2 a -> aclient FI AI LB (usp0 + -128) a.
  Proof.
    intros LB a [Ha|Ha]; [apply base_addr_aclient; exact Ha|].
    right; left. exists 0x5d5f40, 0x5e5f80. split; [apply AMS; unfold a0_static; lia| lia].
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma BASE_A2_alloc : forall LB st m m', BASE_A2 m -> alloc_frame_A FI AI (usp0 + -128) LO' st m m' LB -> BASE_A2 m'.
  Proof.
    intros LB st m m' BA (MI' & ST' & ENV' & RF' & AP). pose proof sp_facts as SF. unfold LO in *.
    pose proof (apres_agree FI AI _ _ _ _ AP) as AG.
    eapply BASE_A2_agree0; [exact BA| exact AG| intros a Ha; apply base_addr2_aclient; exact Ha| exact MI'| exact ST'| | exact ENV'].
    destruct BA as (_ & _ & _ & _ & _ & _ & _ & RSS & _).
    eapply stk_gagree; [exact AG| exact RSS|]. intros a Ha. right; left. exists 0x5d5f40, 0x5e5f80. split; [apply AMS; unfold a0_static; lia| unfold RSVA in Ha; lia].
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma BASE_A2_alloc_q : forall q LB st m m', LO' <= q <= usp0 + -128 -> BASE_A2 m -> alloc_frame_A FI AI q LO' st m m' LB -> BASE_A2 m'.
  Proof.
    intros q LB st m m' HQ BA (MI' & ST' & ENV' & RF' & AP). pose proof sp_facts as SF. unfold LO in *.
    pose proof (apres_agree FI AI _ _ _ _ AP) as AG.
    assert (HA : forall a, base_addr2 a -> aclient FI AI LB q a).
    { intros a Ha. pose proof (base_addr2_aclient LB a Ha) as X. unfold aclient in *. destruct X as [X|X]; [left; lia| right; exact X]. }
    eapply BASE_A2_agree0; [exact BA| exact AG| exact HA| exact MI'| | | exact ENV'].
    - destruct BA as (ST & _). assert (HQ' : usp0 - 8388608 <= q <= usp0 + -128) by lia. destruct (stk_split asegs m _ q _ ST HQ') as [_ STq].
      eapply stk_merge; [exact ST'| | unfold LO; lia]. eapply stk_gagree; [exact AG| exact STq| intros a Ha; left; lia].
    - destruct BA as (_ & _ & _ & _ & _ & _ & _ & RSS & _).
      eapply stk_gagree; [exact AG| exact RSS|]. intros a Ha. right; left. exists 0x5d5f40, 0x5e5f80. split; [apply AMS; unfold a0_static; lia| unfold RSVA in Ha; lia].
  Qed.

  #[using="HC VSP CEIL"] Lemma main_prologue : forall (Q : machine_state -> Prop) (ra s0 s1 a0 a1 a2 s2 s3 t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk asegs m LO' (usp0 + -48) -> mem_inv asegs m ->
    (forall m' (pad : list byte), rw_cells asegs m' (usp0 + -128) [CB 8 pad; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk asegs m' LO' (usp0 + -128) ->
        munch [(usp0 - 128, usp0 - 48)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
        evt asegs Q (MS (mkR ra (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x860a0) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra (Z_to_bv 64 (usp0 + -48)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x86074) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST MI K. pose proof sp_facts as SF. unfold LO in *.
    pose proof (munch_refl [(usp0 - 128, usp0 - 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. carve_frame 80%nat ST.
    do 10 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end; [exact FR| exact ST| exact MU| exact WM| assumption].
  Qed.

  Definition P1_A (ms : machine_state) (g : gst) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (pad : list byte)
           (s : aps FI AI) (st : fsstate FI) (e : word),
      ms = MS (mkR (Z_to_bv 64 0x94384) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
                   (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                   (Z_to_bv 64 0x86074) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x860a4) fc None mm (seg_rom asegs)
      /\ MFRAME sp0 argv mm pad s7 s6 s5 s4 /\ BASE_A mm /\ RHEAP_A FI AI s [] mm /\ RFAKE FI st mm /\ (g = gh FI AI s /\ fs_live FI st = [] /\ am_nsec FI AI s = 0) /\ CJ0 mm
      /\ rw_cells asegs mm RERRNOA [C4 e] /\ frm0 fc.
End A.

Section ASO.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable PZ : mem -> Prop.
  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (TID : Z).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Notation usp0 := (bv_unsigned sp0).
  Notation LO' := (LO sp0).

  #[using="PZ_agree VSP CEIL ESF"] Lemma BASE_A_agree_so : forall (P : Z -> Prop) so so' m m',
    BASE_A PZ sp0 argv envp uid hw rnd TID so m -> gagree_on P m m' -> (forall a, base_addr sp0 argv envp uid hw rnd a -> ~ stdout_addr a -> P a) -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' -> stdout_file m' so' ->
    BASE_A PZ sp0 argv envp uid hw rnd TID so' m'.
  Proof.
    intros P so so' m m' (ST & MI & EX & MC & IMG & SE & SOF0 & RSS & SI & SZ & ENV & GSH & HPZ & CRT) AG HP WM MI' ST' RSS' ENV' SOF'.
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|].
    split; [eapply EXITC_agree; [exact AG| intros a Ha; apply HP; [left; exact Ha| unfold exitc_addr in Ha; unfold stdout_addr; lia]| exact EX]|].
    split. { destruct MC as (A1 & A2 & [G1 G2]). unfold MAINC0, ssp_cells, got_ssp, ssp_guard in *.
             Ltac trbo AG HP A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; apply HP; unfold base_addr, stdout_addr; cbn in Ha; lia].
             split; [trbo AG HP A1|]. split; [trbo AG HP A2|]. split; [trbo AG HP G1| trbo AG HP G2]. }
    split; [eapply IMGK_agree; [exact AG| exact IMG| intros a Ha; apply HP; unfold base_addr, stdout_addr; lia]|].
    split; [eapply stderr_wfile0_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold stderr_addr in Ha; unfold stdout_addr; lia]| exact SE]|].
    split; [exact SOF'|].
    split; [exact RSS'|].
    split; [eapply stdin_file_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold stdin_addr in Ha; unfold stdout_addr; lia]| exact SI]|].
    split.
    { destruct SZ as ([Z1 R1] & [Z2 R2] & [Z3 R3] & [Z4 R4]).
      repeat split; (first [ eapply shz_agree; [exact AG| | | | eassumption] | eapply shr_agree; [exact AG| | | | eassumption] ]);
        unfold sh, SHADOW_OFF, SH_HI;
        first [ intros a Ha; apply HP; unfold base_addr, pz_band, stdout_addr, sh, SHADOW_OFF, SH_HI; Z.div_mod_to_equations; lia
              | Z.div_mod_to_equations; lia ]. }
    split; [exact ENV'|].
    split; [eapply globals_shadow_agree; [exact AG| intros a Ha; apply HP; unfold base_addr, stdout_addr; lia| exact GSH]|].
    split; [eapply PZ_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold pz_band in Ha; unfold stdout_addr; lia]| exact HPZ]|].
    eapply wr_at_transport; [exact CRT| exact WM].
  Qed.

  Ltac bx_tro AG HP A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; apply HP; unfold base_addr, stdout_addr; cbn in Ha; lia].

  #[using="PZ_agree VSP CEIL ESF"] Lemma BASE_A2_agree_so : forall (P : Z -> Prop) so so' m m',
    BASE_A2 PZ sp0 argv envp uid hw rnd TID so m -> gagree_on P m m' -> (forall a, base_addr2 sp0 argv envp uid hw rnd a -> ~ stdout_addr a -> P a) -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' -> stdout_file m' so' ->
    BASE_A2 PZ sp0 argv envp uid hw rnd TID so' m'.
  Proof.
    intros P so so' m m' (ST & MI & EX & MC & IMG & SE & SOF0 & RSS & SI & SZ & ENV & GSH & HPZ & CRT) AG HP2 WM MI' ST' RSS' ENV' SOF'.
    assert (HP : forall a, base_addr sp0 argv envp uid hw rnd a -> ~ stdout_addr a -> P a) by (intros a Ha Hs; apply HP2; [left; exact Ha| exact Hs]).
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|].
    split; [eapply EXITC2_agree; [exact AG| intros a Ha; apply HP2; [destruct Ha as [Ha|Ha]; [left; left; exact Ha| right; exact Ha]| unfold exitc2_addr, exitc_addr in Ha; unfold stdout_addr; lia]| exact EX]|].
    split. { destruct MC as (A1 & A2 & [G1 G2]). unfold MAINC0, ssp_cells, got_ssp, ssp_guard in *.
             split; [bx_tro AG HP A1|]. split; [bx_tro AG HP A2|]. split; [bx_tro AG HP G1| bx_tro AG HP G2]. }
    split; [eapply IMGK_agree; [exact AG| exact IMG| intros a Ha; apply HP; unfold base_addr, stdout_addr; lia]|].
    split; [eapply stderr_wfile0_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold stderr_addr in Ha; unfold stdout_addr; lia]| exact SE]|].
    split; [exact SOF'|].
    split; [exact RSS'|].
    split; [eapply stdin_file_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold stdin_addr in Ha; unfold stdout_addr; lia]| exact SI]|].
    split.
    { destruct SZ as ([Z1 R1] & [Z2 R2] & [Z3 R3] & [Z4 R4]).
      repeat split; (first [ eapply shz_agree; [exact AG| | | | eassumption] | eapply shr_agree; [exact AG| | | | eassumption] ]);
        unfold sh, SHADOW_OFF, SH_HI;
        first [ intros a Ha; apply HP; unfold base_addr, pz_band, stdout_addr, sh, SHADOW_OFF, SH_HI; Z.div_mod_to_equations; lia
              | Z.div_mod_to_equations; lia ]. }
    split; [exact ENV'|].
    split; [eapply globals_shadow_agree; [exact AG| intros a Ha; apply HP; unfold base_addr, stdout_addr; lia| exact GSH]|].
    split; [eapply PZ_agree; [exact AG| intros a Ha; apply HP; [unfold base_addr; tauto| unfold pz_band in Ha; unfold stdout_addr; lia]| exact HPZ]|].
    eapply wr_at_transport; [exact CRT| exact WM].
  Qed.
End ASO.

Section A2.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Variable PZ : mem -> Prop.
  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Local Notation BASE_A' := (fun TID => BASE_A PZ sp0 argv envp uid hw rnd TID stdout_init).

  #[using="PZ_agree VSP CEIL ESF"] Lemma main_to_test : forall (msr : machine_state) (g : gst) (Q : machine_state -> Prop),
    rat_mainA FI AI PZ sp0 argv envp uid hw rnd msr g ->
    (forall (TID : Z) (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (pad : list byte)
            (s : aps FI AI) (st : fsstate FI) (e : word),
        0 < TID < 2^31 ->
        MFRAME sp0 argv mm pad s7 s6 s5 s4 -> BASE_A' TID mm -> RHEAP_A FI AI s [] mm -> RFAKE FI st mm -> (g = gh FI AI s /\ fs_live FI st = [] /\ am_nsec FI AI s = 0) -> CJ0 mm ->
        rw_cells asegs mm RERRNOA [C4 e] -> frm0 fc ->
        evt asegs Q (MS (mkR (Z_to_bv 64 0x94384) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
                          (Z_to_bv 64 2) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                          (Z_to_bv 64 0x86074) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x860a0) fc None mm (seg_rom asegs))) ->
    evt asegs Q msr.
  Proof.
    intros msr g Q AM K.
    destruct AM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & t & e0 & m & s & st
                    & -> & FRM & MI & ST & ERR & EX & Ht & CRT & MC & SOF & SEF & SIF & RSS & IMG & HP & RF & ENV & Eg0 & FSL0 & NS0 & SZ & GSH & HPZ).
    pose proof (conj Eg0 (conj FSL0 NS0)) as Eg.
    destruct MC as (MC1 & MC2 & MC3 & MC4 & MC5).
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL. unfold LO in *.
    replace (usp0 - 8388608) with (usp0 + -8388608) in ST by lia.
    eapply (main_prologue sp0 VSP CEIL); [unfold LO; replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST| exact MI|].
    intros m1 pad FR ST1 MU WM MI1. unfold LO in ST1.
    pose proof (gagree_on_of_munch _ _ _ MU WM) as AG.
    assert (OUT : forall a, (a < usp0 - 128 \/ usp0 - 48 <= a) -> (fun a0 : Z => outside [(usp0 - 128, usp0 - 48)] a0) a) by (intros a Ha; cbn; lia).
    pose proof alloc_ceiling_bounds as CB'.
    apply (K t t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 pad s st e0 Ht).
    - exact FR.
    - split; [unfold LO; replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST1|]. split; [exact MI1|].
      split; [eapply (EXITC_agree t _ _ _ AG); [intros a Ha; apply OUT; unfold exitc_addr in Ha; lia| exact EX]|].
      split. { unfold MAINC0, ssp_cells, got_ssp, ssp_guard in *. destruct MC3 as [G1 G2].
               repeat split; (eapply rw_cells_gagree; [exact AG| eassumption| intros a Ha; apply OUT; cbn in Ha; lia]). }
      split; [eapply IMGK_agree; [exact AG| exact IMG| intros a Ha; apply OUT; lia]|].
      split; [eapply (stderr_wfile0_agree _ _ _ AG); [intros a Ha; apply OUT; unfold stderr_addr in Ha; lia| exact SEF]|].
      split; [eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT; unfold stdout_addr in Ha; lia| exact SOF]|].
      split; [eapply (stk_gagree _ _ _ _ _ AG); [exact RSS| intros a Ha; apply OUT; unfold RSVA in Ha; lia]|].
      split; [eapply (stdin_file_agree _ _ _ AG); [intros a Ha; apply OUT; unfold stdin_addr in Ha; lia| exact SIF]|].
      split; [eapply SHZ_frame; [exact SZ| exact MU| unfold app_ivs; apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil]]|].
      split; [eapply asan_env_frame; [exact ENV| exact MU| exact WM| env_safe_tac]|].
      split; [eapply globals_shadow_frame; [exact GSH| exact MU| exact WM| unfold app_ivs; apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil]]|].
      split; [eapply PZ_agree; [exact AG| intros a Ha; apply OUT; unfold pz_band in Ha; lia| exact HPZ]|].
      eapply wr_at_transport; [exact CRT| exact WM].
    - eapply (am_heap_frame FI AI); [exact HP| exact MU| exact WM|]. constructor; [| constructor]. left. cbn [fst snd]. lia.
    - pose proof (fsb_ok FI) as FB. unfold app_mem in FB.
      eapply (rfake_frame FI); [exact RF| exact MU| exact WM|]. constructor; [| constructor]. left. cbn [fst snd].
      unfold sh, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
    - exact Eg.
    - split; (eapply rw_cells_gagree; [exact AG| eassumption| intros a Ha; apply OUT; cbn in Ha; lia]).
    - unfold RERRNOA. eapply rw_cells_gagree; [exact AG| exact ERR| intros a Ha; apply OUT; cbn in Ha; lia].
    - exact FRM.
  Qed.
End A2.

Section A3.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Variable PZ : mem -> Prop.
  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.

  Hypothesis FPR : @fprintf_diag_stmt HC ASt.
  Hypothesis EXK : forall TID, 0 < TID < 2^31 -> exit_k_stmtA TID.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Local Notation BASE_A' := (fun TID => BASE_A PZ sp0 argv envp uid hw rnd TID stdout_init).
  Local Notation P1_A' := (fun TID => P1_A FI AI PZ sp0 argv envp uid hw rnd TID stdout_init).

  #[using="PZ_agree VSP CEIL ESF"] Lemma main_to_P1 : forall (arg0 arg1 : list byte) (msr : machine_state) (g : gst) (Q : machine_state -> Prop),
    argv = [arg0; arg1] -> rat_mainA FI AI PZ sp0 argv envp uid hw rnd msr g ->
    (forall TID ms', 0 < TID < 2^31 -> P1_A' TID ms' g -> evt asegs Q ms') ->
    evt asegs Q msr.
  Proof.
    intros arg0 arg1 msr g Q EARGV AM K.
    eapply (main_to_test FI AI PZ PZ_agree sp0 argv envp uid hw rnd VSP CEIL ESF msr g Q AM).
    intros TID t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm pad s st e HT FR BA HP RF Eg CJ ERR FRM.
    unfold argc. rewrite EARGV. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- EARGV.
    pose proof BA as (ST & MI & _).
    zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    apply (K TID); [exact HT|].
    unfold P1_A. do 20 eexists. exists F, fc, mm, pad, s, st, e. split; [reflexivity|].
    split; [exact FR|]. split; [exact BA|]. split; [exact HP|]. split; [exact RF|]. split; [exact Eg|]. split; [exact CJ|]. split; [exact ERR| exact FRM].
  Qed.

  #[using="PZ_agree VSP CEIL VARGV ESF FPR EXK"] Lemma main_usage_impl : forall msr g (Q : at_parser -> ASt -> machine_state -> Prop),
    rat_mainA FI AI PZ sp0 argv envp uid hw rnd msr g -> Z.of_nat (length argv) <> 2 ->
    implM asegs (drv_preA RSVA (argv_Z argv)) stdout_init Q msr.
  Proof.
    intros msr g Q AM HARGC.
    unfold drv_preA, drv_pre. unfold argv_Z at 1. rewrite length_map.
    replace (Z.of_nat (length argv) =? 2) with false by (symmetry; apply Z.eqb_neq; exact HARGC). cbn [negb].
    eapply implM_evt with (P := fun ms' => implM asegs
        (io_diag ioA (DUsage (nth 0 (argv_Z argv) []));;; exit_k ioA 2) stdout_init Q ms');
      [| intros ms' H; exact H].
    eapply (main_to_test FI AI PZ PZ_agree sp0 argv envp uid hw rnd VSP CEIL ESF msr g _ AM).
    intros TID t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm pad s st e HT FR BA HP RF Eg CJ ERR FRM.
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'. unfold LO in *.
    pose proof BA as (ST & MI & EX & MC & IMG & SE & SOF0 & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST.
    destruct MC as (G28 & GSE & SSP).
    destruct VARGV as (ARGC & _ & ARGLEN & NONUL & _).
    destruct argv as [|arg0 argv'] eqn:EARGV; [cbn in ARGC; lia|]. rewrite <- EARGV in *.

    destruct (argv_cstring sp0 argv envp uid hw rnd mm IMG 0 arg0 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
      as (p0 & slack0 & HP0 & P0LO & P0HI & STR0 & SLK0). unfold str_base, struct_size, argc, envc in P0LO.
    pose proof (stack_argv2 sp0 argv envp uid hw rnd mm IMG ltac:(rewrite EARGV; cbn [length]; lia)) as ARGVP.
    assert (A0NN : ~ In (Z_to_bv 8 0) arg0) by (rewrite EARGV in NONUL; inversion NONUL; assumption).
    assert (A0LEN : Z.of_nat (length arg0) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN; assumption).
    unfold argc. zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.

    zstep. zstep. zstep.
    pose proof (u64ro_read mm (usp0 + 8) (firstn 2 (argv_ptrs sp0 argv envp ++ [Z_to_bv 64 0])) 0 (Z_to_bv 64 p0) (Z_to_bv 64 (usp0 + 8))
                  ARGVP ltac:(apply nth_error_firstn2; [cbn; lia|]; rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP0) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep.

    apply evt_done.
    eapply implM_bind.
    { eapply (FPR (PDUsage (nth 0 (argv_Z argv) []))) with (lo := usp0 - 8388608) (canary := guard_word);
        rewrite ?unsigned_lit by lia.
      all: first [ apply stderr_wfile0_wfile; exact SE | reflexivity | exact ST || (replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST)
                 | unfold FPRINTF_DEPTH; lia | unfold GLOBALS_TOP; lia | lia | exact SSP | exact MI | exact FRM | exact ENV
                 | unfold RO_LO, RO_SZ; apply (SHZ_ro sp0 argv envp uid hw rnd); exact SZ
                 | apply (SHZ_stack sp0 argv envp uid hw rnd); [exact SZ | lia | pose proof (build_stack_bytes_length rph sp0 argv envp uid hw rnd); lia | lia | lia]
                 | idtac ].
      { cbn [diag_args pdiag_fmt]. split; [reflexivity|]. exists slack0.
        rewrite EARGV. cbn [argv_Z map nth]. rewrite unsigned_lit by lia.
        unfold zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
        split; [exact STR0|]. split; [apply map_unsigned_pos; exact A0NN|]. split; [lia|].
        split; [lia|]. split; [right; lia|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|].
        apply (SHZ_stack sp0 argv envp uid hw rnd); [exact SZ | lia | lia | lia | lia]. }
    }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ENV2 & ->).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x86228)) with (Z_to_bv 64 0x86228) by (symmetry; rpc).
    pose proof (gagree_on_of_munch _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp0 - 128 <= a /\ ~ (0xaeac8 <= a < 0xaeac8 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0xaeac8, 0xaeac8 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (OUT2 : forall a, (a < 0x10008000000 /\ ~ (0xaeac8 <= a < 0xaeac8 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0xaeac8, 0xaeac8 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    eapply implM_evt; [| intros msx Hx; exact (EXK TID HT at_parser 2 _ Q msx Hx)]. unfold MFRAME in FR.
    apply (rw_cells_gagree _ _ _ _ _ AG) in FR; [| intros a Ha; apply OUT; cbn in Ha; lia].
    zstep.
    destruct SSP2 as [GG2 GU2]. unfold got_ssp, ssp_guard in GG2, GU2.
    eapply (main_return sp0 argv TID VSP CEIL 2 stdout_init).
    - exact FR.
    - unfold LO. exact ST2.
    - eapply (EXITC_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold exitc_addr in Ha; lia| exact EX].
    - eapply wr_at_transport; [exact CRT| exact WMc].
    - exact ENV2.
    - eapply globals_shadow_frame; [exact GSH| exact MUc| exact WMc| unfold app_ivs; apply Forall_cons; [apply app_iv_stack; lia| apply Forall_cons; [apply app_iv_low; lia| apply Forall_nil]]].
    - exact GG2.
    - exact GU2.
    - cbn [ps_so ps_init]. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF0].
    - apply stderr_wfile_file. exact SEW.
    - eapply (stdin_file_agree _ _ _ AG); [intros a Ha; apply OUT2; unfold stdin_addr in Ha; lia| exact SI].
    - exact MI2.
  Qed.
  #[using="PZ_agree VSP CEIL VARGV ESF FPR EXK"] Lemma main_usage : forall msr g (Q : at_parser -> ASt -> machine_state -> gst -> Prop),
    rat_mainA FI AI PZ sp0 argv envp uid hw rnd msr g -> Z.of_nat (length argv) <> 2 ->
    djM (drv_preA RSVA (argv_Z argv)) stdout_init Q msr g.
  Proof.
    intros msr g Q AM HARGC.
    eapply djM_mono; [eapply djM_of_implM; [eapply (main_usage_impl msr g (fun _ _ _ => False) AM HARGC) | apply fdtree_drv_preA] |].
    intros x s' ms' g' [[] _].
  Qed.
End A3.

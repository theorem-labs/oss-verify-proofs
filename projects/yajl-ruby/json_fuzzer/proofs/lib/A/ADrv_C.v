(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge ITree Nodes NodesCfg Decode Arr FP InitMem Frame Mem Cells SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages ExecA LazyModel NodesA ImplRzA CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzNodes TrzStdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model R_StartupLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface A_iface5x ADrv_ctx ADrv_A ADrv_B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma shiftr26_zero_iff : forall a, 0 <= a -> (Z.shiftr a 26 = 0 <-> a < 67108864).
Proof.
  intros a Ha. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 26) with 67108864.
  split; intros H; [| apply Z.div_small; lia].
  destruct (Z.lt_ge_cases a 67108864) as [L|G]; [exact L|]. exfalso.
  pose proof (Z.div_le_mono 67108864 a 67108864 ltac:(lia) G) as M. rewrite Z.div_same in M by lia. lia.
Qed.

Lemma rw_cells_CB_join : forall m A n1 n2 (b1 b2 : list byte),
  rw_cells asegs m A [CB n1 b1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells asegs m A [CB (n1 + n2)%nat (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2.
  assert (H : rw_cells asegs m A ([CB n1 b1] ++ [CB n2 b2])).
  { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H2. }
  destruct H as [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
  split; [split|].
  - cbn. rewrite length_app. split; [lia| exact I].
  - cbn [cells_bytes cbytes app] in HB |- *. rewrite !app_nil_r in HB |- *. exact HB.
  - replace (Z.of_nat (cells_size [CB (n1 + n2)%nat (b1 ++ b2)])) with (Z.of_nat (cells_size ([CB n1 b1] ++ [CB n2 b2]))) by (cbn; lia). exact HW.
Qed.

Lemma rw_cells_of_bytes : forall m A bs n, bytes_at asegs m A bs -> wr_at asegs m A (Z.of_nat n) -> length bs = n ->
  rw_cells asegs m A [CB n bs].
Proof.
  intros m A bs n HB HW HL. split; [split|].
  - cbn. split; [exact HL| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma firstn_app_skipn_firstn : forall {A} (l : list A) n k,
  firstn n l ++ firstn k (skipn n l) = firstn (n + k) l.
Proof.
  intros A l n k. revert l. induction n as [|n IH]; intros l; cbn; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma ab_remove_second : forall A' n' A n, A' <> A -> ab_remove A [mkABlock A' n'; mkABlock A n] = [mkABlock A' n'].
Proof. intros A' n' A n NE. cbn [ab_remove ab_addr]. rewrite (proj2 (Z.eqb_neq A' A) NE), Z.eqb_refl. reflexivity. Qed.

Section C.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte)
            (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Variable D : adrv_params.
  Hypothesis DI : a_drv_iface asegs ACONSTS AFMTS D.
  Hypothesis DIx : a_drv_iface5x asegs ACONSTS D.      (* [comment removed for export] *)
  Notation AHK := (p_AHK D).
  Notation SO := (p_SO D).
  Notation AHEAD := (p_AHEAD D).

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 0x5e0b10).
  Notation IMGB := (build_stack_bytes aph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation ABASE' := (ABASE sp0 argv envp uid hw rnd).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).

  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  (* [comment removed for export] *)
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).

  Variable FS0 : Fs.Fs.
  Notation RDCORE' := (RDCORE sp0 argv envp uid hw rnd PAD S4 S5 S6 S7 D FS0).
  Notation RDINV' := (RDINV sp0 argv envp uid hw rnd PAD S4 S5 S6 S7 S8 S9 S10 S11 D FS0).
  Notation RDBRK' := (RDBRK sp0 argv envp uid hw rnd PAD S4 S5 S6 S7 S8 S9 S10 S11 D FS0).
  Let PSTK := PSTK sp0 VSP RCSP.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (P1v : Z) (pathb FILE : list byte).
  (* [comment removed for export] *)
  Variable KDONE : TSet.
  Hypothesis KDONE_nil : KDONE [].
  Hypothesis HBRK : forall cap s mo ms, RDBRK' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length FILE)))) cap FILE s mo ms ->
                    Z.of_nat (length FILE) < cap -> realizes_cfg acfg asegs (mkCfg ms mo) KDONE.

  Definition TREF : TSet := TDIE pieces_too_big stdout_init FS0.
  (* [comment removed for export] *)
  Definition TFIN : TSet := if MAX_INPUT <=? Z.of_nat (length FILE) then TREF else KDONE.
  Lemma TFIN_nil : TFIN []. Proof. unfold TFIN. destruct (MAX_INPUT <=? _); [apply TDIE_nil | apply KDONE_nil]. Qed.

  (* [comment removed for export] *)
  Definition rmeas (cap : Z) (DATA : list byte) : Z := 2 * MAX_INPUT - Z.of_nat (length DATA) - cap.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma az_grow : forall (cap : Z) (DATA : list byte) s mo
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z),
    RDCORE' 3 (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA)))) cap DATA s mo mm fc A ->
    fs_lookup (m_fs mo) pathb = Some FILE -> DATA = firstn (length DATA) FILE ->
    Z.of_nat (length DATA) = cap ->
    (forall cap' s' mo' ms', rmeas cap' DATA < rmeas cap DATA ->
        fs_lookup (m_fs mo') pathb = Some FILE ->
        RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA)))) cap' DATA s' mo' ms' ->
        realizes_cfg acfg asegs (mkCfg ms' mo') TFIN) ->
    realizes_cfg acfg asegs
      (mkCfg (RST 0x81b38 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (Z.of_nat (length DATA)) 3 cap (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm) mo)
      TFIN.
  Proof.
    intros until A. intros RC FSL PRE FULL IH.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    destruct RC as (junk & H & BU & HKx & HD & HB & SO0 & FD & FS & FR & BA & FRM).
    destruct BU as (BLK & [CAPR [k [Kk0 CAPK]]] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    cbn [c_img_hi ACONSTS] in BR5. unfold MAX_INPUT in CAPR.
    pose proof BA as (ST & MI & IMG & (G & E & IB)). unfold LO in ST. unfold MFRAME in FR.
    pose proof (f_equal (@length byte) PRE) as LD. rewrite length_firstn in LD.
    set (LEN := Z.of_nat (length DATA)) in *.
    pose proof (PSTK [mkABlock A cap]) as PS. pose proof (pol_img [mkABlock A cap]) as PI.
    aseg DI HKx.
    zstepA. zstepA. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (GE : 67108864 <= cap).
      { destruct (Z.lt_ge_cases cap 67108864) as [L|G']; [| exact G']. exfalso. apply K0.
        apply (proj2 (shiftr26_zero_iff LEN ltac:(lia))). lia. }
      do 6 zstepA. aleaf. intros moa Haga HKa Efsa Efdsa Hha.
      assert (TLE : TFIN = TREF).
      { unfold TFIN. replace (MAX_INPUT <=? Z.of_nat (length FILE)) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia). reflexivity. }
      rewrite TLE. unfold TREF. rewrite <- FS, <- Efsa.
      eapply (az_fprintf_exit sp0 argv envp uid hw rnd S8 S9 S10 S11 VSP RCSP D DI DIx DTooBig s [mkABlock A cap]);
        [| exact BA | exact HKa | exact SO0 | exact FRM].
      cbn [adiag_args f_too_big AFMTS]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    assert (LTM : cap < 67108864).
    { rewrite <- FULL. apply (proj1 (shiftr26_zero_iff LEN ltac:(lia))). exact K0. }
    assert (CAP2 : cap * 2 <= 67108864).
    { pose proof LTM as LTM'. rewrite CAPK in LTM' |- *. change 67108864 with (2 ^ 26) in LTM' |- *. apply Z.pow_lt_mono_r_iff in LTM'; [| lia| lia].
      replace (2 ^ k * 2) with (2 ^ (k + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
    zstepA. zstepA. zstepA. aleaf. intros moa Haga HKa Efsa Efdsa Hha.
    replace (Z.shiftl LEN 1) with (cap * 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ HD Haga) as HDa.
    assert (Hk26 : 0 <= k <= 26).
    { split; [exact Kk0|]. destruct (Z_lt_le_dec 26 k) as [L|L]; [exfalso | exact L].
      pose proof (Z.pow_lt_mono_r 2 26 k ltac:(lia) ltac:(lia) L). lia. }
    assert (EB : abud cap = S (S (abud (cap * 2)))) by (rewrite CAPK; apply abud_grow; lia). rewrite EB in HDa.
    (* [comment removed for export] *)
    eapply (adi_malloc _ _ _ _ DI) with (lo := usp0 - 8388608) (n := cap * 2); try reflexivity.
    all: rewrite ?(unsigned_lit (usp0 + -128)) by lia.
    - apply TFIN_nil.
    - exact HKa.
    - exact ST.
    - lia.
    - unfold AMALLOC_STACK. lia.
    - clear -SF. Z.div_mod_to_equations. lia.
    - lia.
    - apply (adi_uanchorC _ _ _ _ DI); [in_lits| rewrite unsigned_lit by lia; aceil; lia].
    - exact FRM.
    - lia.
    - eapply (adi_hd_cmalloc _ _ _ _ DI); [exact HDa | lia].
    - apply nbig_small; cbn [length]; lia.
    - (* [comment removed for export] *)
      intros v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 m2 mo2 s2 A' ST2 HPR WM2 FRM2 SOE REL FS2 FDS2 CR2 EA0 BR' HK2 [junk' [JL NBLK]] BSH2.
      subst c0.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0x81b4c)) with (Z_to_bv 64 0x81b4c) by (symmetry; rpc).
      assert (BA2 : ABASE' m2) by (eapply (ABASE_heap_pres sp0 argv envp uid hw rnd VSP RCSP); [exact BA| exact HPR| lia| reflexivity| reflexivity| reflexivity| exact (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK2)| unfold LO; exact ST2]).
      pose proof (aheap_pres_agree _ _ _ _ _ _ HPR) as AG2.
      assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply rw_cells_agree; [exact AG2| exact FR| intros ax Ha; left; cbn in Ha; lia]).
      assert (BLK2 : rw_cells asegs m2 A [CB (length DATA) DATA; CB (Z.to_nat (cap - LEN)) junk]).
      { eapply rw_cells_agree; [exact AG2| exact BLK|]. intros ax Ha. right; left. exists (mkABlock A cap). split; [left; reflexivity|]. cbn [ab_addr ab_size cells_size csize Nat.add] in Ha |- *. lia. }
      clear FR BLK ST MI IMG G E IB AG2.
      pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). cbn [c_img_hi ACONSTS] in BQ5.
      destruct (adi_blocks _ _ _ _ DI _ _ _ _ _ HK2) as (_ & DISJ0 & ND).
      assert (NEQ : A' <> A).
      { cbn [map ab_addr] in ND. inversion ND as [|x l NI ND']; subst. intros EQ. apply NI. rewrite EQ. left. reflexivity. }
      assert (DISJ : A' + cap * 2 <= A \/ A + cap <= A').
      { pose proof (DISJ0 (mkABlock A' (cap * 2)) (mkABlock A cap) ltac:(left; reflexivity) ltac:(right; left; reflexivity) NEQ) as DD.
        cbn [ab_addr ab_size] in DD. exact DD. }
      pose proof BA2 as (ST & MI & IMG & (G & E & IB)). unfold LO in ST.
      pose proof (PSTK [mkABlock A' (cap * 2); mkABlock A cap]) as PS2. pose proof (pol_img [mkABlock A' (cap * 2); mkABlock A cap]) as PI2.
      pose proof (adi_hd_malloc _ _ _ _ DI _ _ (cap * 2) (S (abud (cap * 2))) [(A, cap)] H A' _ _ HDa ltac:(lia) REL) as HD2.
      aseg DI HK2.
      zstepA. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
      zstepA. zstepA. if_cases K2; zify_cond K2; try (exfalso; rewrite ?unsigned_lit in K2 by lia; lia). clear K2.
      zstepA. zstepA. zstepA. zstepA. aleaf. intros mo2a Hag2a HK2a Efs2a Efds2a Hh2a.
      (* [comment removed for export] *)
      pose proof BLK2 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in SRC. destruct SRC as [SRC _].
      pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
      pose proof NBLK as NB0.
      apply (rw_cells_split_CB _ _ _ [] _ _ [] [length DATA; Z.to_nat (cap * 2) - length DATA]%nat) in NB0; [| cbn; lia]. cbn [mk_CB_cells app] in NB0.
      apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) (firstn (length DATA) junk')] _)) in NB0. destruct NB0 as [NB1 NB2]. cbn [cells_size csize Nat.add] in NB2.
      eapply (adi_memcpy _ _ _ _ DI) with (lo := usp0 - 8388608) (bd := mkABlock A' (cap * 2)) (bsr := mkABlock A cap) (dst := A') (src := A) (n := LEN);
        [ apply TFIN_nil | exact HK2a | left; reflexivity | cbn [ab_addr]; lia | cbn [ab_addr ab_size]; lia
        | right; left; reflexivity | cbn [ab_addr]; lia | cbn [ab_addr ab_size]; lia | lia | lia | exact SRCB | lia
        | replace (Z.to_nat LEN) with (length DATA) by lia; exact NB1
        | rewrite unsigned_lit by lia; exact ST | lia
        | rewrite unsigned_lit by lia; unfold AICP_STACK; lia | reflexivity | exact FRM2 | reflexivity | reflexivity | reflexivity | ].
      intros w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F3 fc3 m3 mo3 s3 ST3 NB1' MUc WM3 FRM3 HK3 AS3 SO3 Efs3 Efds3 Hag3.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
      replace (ret_pc (Z_to_bv 64 0x81b68)) with (Z_to_bv 64 0x81b68) by (symmetry; rpc).
      assert (WOKW : Forall (AWOK sp0) [(usp0 - 8388608, usp0 + -128); (A', A' + LEN)]).
      { unfold AWOK, LO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
      pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK3) as MI3.
      assert (BA3 : ABASE' m3) by (eapply (ABASE_munch sp0 argv envp uid hw rnd VSP RCSP VARGV VENVP); [exact BA2| exact WOKW| exact MUc| exact WM3| exact MI3| unfold LO; exact ST3]).
      pose proof (agree_on_of_munch _ _ _ MUc WM3) as AG3.
      assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply rw_cells_agree; [exact AG3 | exact FR2 | intros ax Ha; cbn in Ha |- *; lia]).
      (* [comment removed for export] *)
      assert (NB3 : rw_cells asegs m3 A' [CB (length DATA) DATA; CB (Z.to_nat (cap * 2 - LEN)) (firstn (Z.to_nat (cap * 2) - length DATA)%nat (skipn (length DATA) junk'))]).
      { apply (proj2 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)). split.
        - replace (length DATA) with (Z.to_nat LEN) by lia. exact NB1'.
        - cbn [cells_size csize Nat.add]. replace (Z.to_nat (cap * 2 - LEN)) with (Z.to_nat (cap * 2) - length DATA)%nat by lia.
          eapply rw_cells_agree; [exact AG3| exact NB2|]. intros ax Ha. cbn in Ha |- *. lia. }
      pose proof (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ (adi_hd_aps _ _ _ _ DI _ _ _ _ _ _ (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ HD2 Hag2a) AS3) Hag3) as HD3.
      clear MUc WOKW AG3 BA2 ST MI IMG G E IB NB1 NB2 NBLK NB1'.
      pose proof BA3 as (ST & MI & IMG & (G & E & IB)). unfold LO in ST.
      pose proof (PSTK [mkABlock A' (cap * 2); mkABlock A cap]) as PS3. pose proof (pol_img [mkABlock A' (cap * 2); mkABlock A cap]) as PI3.
      aseg DI HK3.
      (* [comment removed for export] *)
      zstepA. zstepA. aleaf. intros mo3a Hag3a HK3a Efs3a Efds3a Hh3a.
      assert (HD3' : AHEAD (S (abud (cap * 2))) ((A, cap) :: [(A', cap * 2)]) (EvMalloc (cap * 2) (Some A') :: H) s3 mo3a).
      { eapply (adi_hd_perm _ _ _ _ DI); [| apply perm_swap]. eapply (adi_hd_magree _ _ _ _ DI); [exact HD3| exact Hag3a]. }
      eapply (adi_free _ _ _ _ DI) with (lo := usp0 - 8388608) (A := A); try reflexivity.
      all: rewrite ?(unsigned_lit (usp0 + -128)) by lia.
      + apply TFIN_nil.
      + exact HK3a.
      + right; exists (mkABlock A cap); split; [right; left; reflexivity| reflexivity].
      + exact ST.
      + lia.
      + unfold AMALLOC_STACK. lia.
      + clear -SF. Z.div_mod_to_equations. lia.
      + lia.
      + apply (adi_uanchorC _ _ _ _ DI); [in_lits| rewrite unsigned_lit by lia; aceil; lia].
      + exact FRM3.
      + eapply (adi_hd_cfree _ _ _ _ DI); exact HD3'.
      + apply nbig_small; cbn [length]; lia.
      + intros w0' w1' w2' rb0 e1 e2 e3 e4 e5 e6 e7 w3' w4' w5' w6' F4 fc4 m4 mo4 s4 ST4 HPR4 FRM4 SOE4 HK4 REL4 FS4 FDS4 CR4.
        rewrite ?(unsigned_lit (usp0 + -128)) in ST4 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR4 by lia.
        replace (ret_pc (Z_to_bv 64 0x81b70)) with (Z_to_bv 64 0x81b70) by (symmetry; rpc).
        rewrite (ab_remove_second A' (cap * 2) A cap NEQ) in HPR4, HK4.
        assert (BA4 : ABASE' m4) by (eapply (ABASE_heap_pres sp0 argv envp uid hw rnd VSP RCSP); [exact BA3| exact HPR4| lia| reflexivity| reflexivity| reflexivity| exact (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK4)| unfold LO; exact ST4]).
        pose proof (aheap_pres_agree _ _ _ _ _ _ HPR4) as AG4.
        assert (FR4 : FRAME' m4) by (unfold MFRAME; eapply rw_cells_agree; [exact AG4| exact FR3| intros ax Ha; left; cbn in Ha; lia]).
        assert (NB4 : rw_cells asegs m4 A' [CB (length DATA) DATA; CB (Z.to_nat (cap * 2 - LEN)) (firstn (Z.to_nat (cap * 2) - length DATA)%nat (skipn (length DATA) junk'))]).
        { eapply rw_cells_agree; [exact AG4| exact NB3|]. intros ax Ha. right; left. exists (mkABlock A' (cap * 2)). split; [left; reflexivity|].
          cbn [ab_addr ab_size cells_size csize Nat.add] in Ha |- *. lia. }
        pose proof (adi_hd_free _ _ _ _ DI _ _ _ _ _ _ _ _ _ HD3' REL4) as HD4.
        (* [comment removed for export] *)
        apply (IH (cap * 2) s4 mo4); [unfold rmeas; lia | rewrite FS4, Efs3a, Efs3, Efs2a, FS2, Efsa; exact FSL |].
        unfold RDINV. do 17 eexists. exists F4, fc4, m4, A'. split; [reflexivity|]. split; [| lia].
        unfold RDCORE. exists (firstn (Z.to_nat (cap * 2) - length DATA)%nat (skipn (length DATA) junk')), (EvFree A :: EvMalloc (cap * 2) (Some A') :: H).
        split. { unfold BUFC. split; [exact NB4|]. unfold MAX_INPUT. split; [split; [lia| exists (k + 1); split; [lia| rewrite CAPK, Z.pow_add_r by lia; lia]]|]. split; [lia| exact BR']. }
        split; [exact HK4|]. split; [exact HD4|].
        split; [constructor; [exact I| constructor; [cbn; lia| exact HB]]|].
        split; [rewrite SOE4, SO3, SOE; exact SO0|].
        split; [rewrite FDS4, Efds3a, Efds3, Efds2a, FDS2, Efdsa; exact FD|].
        split; [rewrite FS4, Efs3a, Efs3, Efs2a, FS2, Efsa; exact FS|].
        split; [exact FR4|]. split; [exact BA4| exact FRM4].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma az_read_part : forall (cap : Z) (DATA : list byte) s mo
      x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A CNT : Z),
    RDCORE' 3 (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA)))) cap DATA s mo mm fc A ->
    fs_lookup (m_fs mo) pathb = Some FILE -> DATA = firstn (length DATA) FILE ->
    Z.of_nat (length DATA) < cap -> 0 < CNT <= 65536 -> CNT <= cap - Z.of_nat (length DATA) ->
    (forall cap' DATA' s' mo' ms', rmeas cap' DATA' < rmeas cap DATA -> fs_lookup (m_fs mo') pathb = Some FILE -> DATA' = firstn (length DATA') FILE ->
        RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA')))) cap' DATA' s' mo' ms' -> realizes_cfg acfg asegs (mkCfg ms' mo') TFIN) ->
    realizes_cfg acfg asegs
      (mkCfg (GST 0x81b80 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 (Z_to_bv 64 CNT) a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (Z.of_nat (length DATA))) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm) mo)
      TFIN.
  Proof.
    intros until CNT. intros RC FSL PRE LT CNTR CNTC IH.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof STAGE_val as SV.
    destruct RC as (junk & H & BU & HKx & HD & HB & SO0 & FD & FS & FR & BA & FRM).
    destruct BU as (BLK & [CAPR CAPK] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    cbn [c_img_hi ACONSTS] in BR5. unfold MAX_INPUT in CAPR.
    pose proof BA as (ST & MI & IMG & (G & E & IB)). unfold LO in ST. unfold MFRAME in FR.
    set (LEN := Z.of_nat (length DATA)) in *.
    (* [comment removed for export] *)
    destruct (RSTG_any mm) as [stg RSG].
    pose proof RSG as DST0. unfold RSTG in DST0. pose proof (rw_cells_bound _ _ _ _ DST0) as STGB. cbn [cells_size csize Nat.add] in STGB.
    apply (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat CNT; Z.to_nat STAGE - Z.to_nat CNT]%nat) in DST0; [| cbn; lia]. cbn [mk_CB_cells app] in DST0.
    apply (proj1 (rw_cells_app _ _ _ [CB (Z.to_nat CNT) (firstn (Z.to_nat CNT) stg)] _)) in DST0. destruct DST0 as [DST _].
    pose proof (PSTK [mkABlock A cap]) as PS. pose proof (pol_img [mkABlock A cap]) as PI.
    aseg DI HKx. zstepA. zstepA. zstepA. aleaf. intros moa Haga HKa Efsa Efdsa Hha.
    (* [comment removed for export] *)
    set (bs := firstn (Z.to_nat CNT) (skipn (length DATA) FILE)).
    set (mo2 := with_fds (fd_insert (m_fds moa) (Z_to_bv 64 3) (FdFile pathb (Z_to_bv 64 (LEN + Z.of_nat (length bs))))) moa).
    assert (RO : read_out 3 RSTAGE CNT moa = Some (RdData bs, mo2)).
    { rewrite <- Efdsa in FD. unfold read_out. rewrite FD, Efsa, FSL. rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia.
      replace (Z.to_nat LEN) with (length DATA) by lia. subst bs mo2. unfold len_word. rewrite lit_add_lit. reflexivity. }
    eapply (adx_read_s _ _ _ DIx) with (lo := usp0 - 8388608) (buf := RSTAGE) (count := CNT) (fd := 3);
      [ apply TFIN_nil | exact HKa | unfold RSTAGE, A_RSTAGE; lia | unfold RSTAGE, A_RSTAGE, A_RSTAGE_LEN; lia | lia | lia | exact DST | exact RO
      | rewrite unsigned_lit by lia; exact ST | lia
      | rewrite unsigned_lit by lia; unfold AICP_STACK; lia | reflexivity | exact FRM | reflexivity | reflexivity | reflexivity | ].
    intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 mo3 s3 res ST2 RES WM2 FRM2 HK2 AS2 SO2 Efs2 Efds2 Hag2. clear DST.
    cbv iota beta in RES. destruct RES as (-> & BS & MUc).
    rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x81b8c)) with (Z_to_bv 64 0x81b8c) by (symmetry; rpc).
    assert (LBS : (length bs <= Z.to_nat CNT)%nat) by (subst bs; rewrite length_firstn; lia).
    (* [comment removed for export] *)
    assert (WOKW : Forall (AWOK sp0) [(usp0 - 8388608, usp0 + -128); (RSTAGE, RSTAGE + CNT); (0x5e0a6c, 0x5e0a6c + 4)]).
    { unfold AWOK, LO, RSTAGE. cbn [c_errno ACONSTS] in *. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    cbn [c_errno ACONSTS] in MUc.
    pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK2) as MI2.
    assert (BA2 : ABASE' m2) by (eapply (ABASE_munch sp0 argv envp uid hw rnd VSP RCSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WM2| exact MI2| unfold LO; exact ST2]).
    pose proof (agree_on_of_munch _ _ _ MUc WM2) as AG.
    assert (FR2 : FRAME' m2).
    { unfold MFRAME. eapply rw_cells_agree; [exact AG | exact FR | intros ax Ha; cbn in Ha |- *; unfold RSTAGE; lia]. }
    assert (BLK2 : rw_cells asegs m2 A [CB (length DATA) DATA; CB (Z.to_nat (cap - LEN)) junk]).
    { eapply rw_cells_agree; [exact AG | exact BLK | intros ax Ha; cbn [cells_size csize Nat.add] in Ha; cbn; unfold RSTAGE; lia]. }
    assert (HD2 : AHEAD (abud cap) [(A, cap)] H s3 mo3).
    { eapply (adi_hd_aps _ _ _ _ DI); [| exact AS2]. eapply (adi_hd_magree _ _ _ _ DI); [| exact Hag2].
      eapply (adi_hd_vmsame _ _ _ _ DI); [| subst mo2; apply vm_same_with_fds]. eapply (adi_hd_magree _ _ _ _ DI); [exact HD| exact Haga]. }
    assert (PRE' : DATA ++ bs = firstn (length DATA + length bs) FILE).
    { subst bs. rewrite PRE at 1. rewrite firstn_app_skipn_firstn. rewrite length_firstn, length_skipn.
      pose proof (f_equal (@length byte) PRE) as LD. rewrite length_firstn in LD.
      destruct (Nat.le_gt_cases (Z.to_nat CNT) (length FILE - length DATA)) as [LE|GT].
      - rewrite Nat.min_l by lia. reflexivity.
      - rewrite Nat.min_r by lia. rewrite !firstn_all2 by lia. reflexivity. }
    assert (FD3 : fd_lookup (m_fds mo3) (Z_to_bv 64 3) = Some (FdFile pathb (Z_to_bv 64 (Z.of_nat (length (DATA ++ bs)))))).
    { rewrite Efds2. subst mo2. rewrite m_fds_with_fds, fd_lookup_insert_same. rewrite length_app. do 3 f_equal. lia. }
    assert (FS3 : m_fs mo3 = FS0) by (rewrite Efs2, Efsa; exact FS).
    assert (FSL3 : fs_lookup (m_fs mo3) pathb = Some FILE) by (rewrite FS3, <- FS; exact FSL).
    clear MUc WOKW AG BA ST MI IMG G E IB FR BLK RO RSG.
    pose proof BA2 as (ST & MI & IMG & (G & E & IB)). unfold LO in ST.
    pose proof (PSTK [mkABlock A cap]) as PS2. pose proof (pol_img [mkABlock A cap]) as PI2.
    aseg DI HK2.
    zstepA. if_cases K0; zify_cond K0; try (exfalso; revert K0 LBS CNTR; clear; intros; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
    zstepA. zstepA. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (NZ : length bs <> 0%nat) by (intros EE; rewrite EE in K1; apply K1; reflexivity).
      zstepA. zstepA. zstepA. zstepA. aleaf. intros mo3a Hag3a HK3a Efs3a Efds3a Hh3a.
      (* [comment removed for export] *)
      pose proof BLK2 as BLKx. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKx. destruct BLKx as [BLK1 BLKr].
      cbn [cells_size csize Nat.add] in BLKr. replace (length DATA + 0)%nat with (length DATA) in BLKr by lia.
      apply (rw_cells_split_CB _ _ _ [] _ _ [] [length bs; Z.to_nat (cap - LEN) - length bs]%nat) in BLKr; [| cbn; lia]. cbn [mk_CB_cells app] in BLKr.
      apply (proj1 (rw_cells_app _ _ _ [CB (length bs) (firstn (length bs) junk)] _)) in BLKr. destruct BLKr as [DSTB RESTB]. cbn [cells_size csize Nat.add] in RESTB.
      eapply (adx_memcpy_s _ _ _ DIx) with (lo := usp0 - 8388608) (bd := mkABlock A cap) (dst := A + LEN) (src := RSTAGE) (n := Z.of_nat (length bs)) (bs := bs);
        [ apply TFIN_nil | exact HK3a | left; reflexivity | cbn [ab_addr]; lia | cbn [ab_addr ab_size]; lia
        | unfold RSTAGE, A_RSTAGE; lia | unfold RSTAGE, A_RSTAGE, A_RSTAGE_LEN; lia | lia | exact BS | reflexivity
        | replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) by lia; first [exact DSTB | replace (A + LEN) with (A + Z.of_nat (length DATA)) by lia; exact DSTB]
        | rewrite unsigned_lit by lia; exact ST | lia
        | rewrite unsigned_lit by lia; unfold AICP_STACK; lia | reflexivity | exact FRM2 | reflexivity | reflexivity | reflexivity | ].
      intros w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F3 fc3 m3 mo4 s4 ST3 DSTB' MUc WM3 FRM3 HK3 AS3 SO3 Efs3 Efds3 Hag3.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
      replace (ret_pc (Z_to_bv 64 0x81b24)) with (Z_to_bv 64 0x81b24) by (symmetry; rpc).
      assert (WOKW : Forall (AWOK sp0) [(usp0 - 8388608, usp0 + -128); (A + LEN, A + LEN + Z.of_nat (length bs))]).
      { unfold AWOK, LO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
      pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK3) as MI3.
      assert (BA3 : ABASE' m3) by (eapply (ABASE_munch sp0 argv envp uid hw rnd VSP RCSP VARGV VENVP); [exact BA2| exact WOKW| exact MUc| exact WM3| exact MI3| unfold LO; exact ST3]).
      pose proof (agree_on_of_munch _ _ _ MUc WM3) as AG3.
      assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply rw_cells_agree; [exact AG3 | exact FR2 | intros ax Ha; cbn in Ha |- *; lia]).
      assert (BLK1' : rw_cells asegs m3 A [CB (length DATA) DATA]).
      { eapply rw_cells_agree; [exact AG3 | exact BLK1 | intros ax Ha; cbn [cells_size csize Nat.add] in Ha; cbn; lia]. }
      assert (RESTB' : rw_cells asegs m3 (A + LEN + Z.of_nat (length bs + 0)) [CB (Z.to_nat (cap - LEN) - length bs) (firstn (Z.to_nat (cap - LEN) - length bs) (skipn (length bs) junk))]).
      { eapply rw_cells_agree; [exact AG3 | first [exact RESTB | replace (A + LEN) with (A + Z.of_nat (length DATA)) by lia; exact RESTB] | intros ax Ha; cbn [cells_size csize Nat.add] in Ha; cbn; lia]. }
      (* [comment removed for export] *)
      assert (BLK' : rw_cells asegs m3 A [CB (length (DATA ++ bs)) (DATA ++ bs); CB (Z.to_nat (cap - Z.of_nat (length (DATA ++ bs)))) (firstn (Z.to_nat (cap - LEN) - length bs) (skipn (length bs) junk))]).
      { pose proof (rw_cells_CB_join m3 A (length DATA) (length bs) DATA bs BLK1'
                      ltac:(replace (A + Z.of_nat (length DATA)) with (A + LEN) by lia;
                            replace (length bs) with (Z.to_nat (Z.of_nat (length bs))) at 1 by lia; exact DSTB')) as J.
        apply (proj2 (rw_cells_app _ _ _ [CB (length (DATA ++ bs)) (DATA ++ bs)] _)). rewrite length_app. split; [exact J|]. cbn [cells_size csize Nat.add].
        replace (Z.to_nat (cap - Z.of_nat (length DATA + length bs))) with (Z.to_nat (cap - LEN) - length bs)%nat by lia.
        replace (A + Z.of_nat (length DATA + length bs + 0)) with (A + LEN + Z.of_nat (length bs + 0)) by lia. exact RESTB'. }
      pose proof (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ (adi_hd_aps _ _ _ _ DI _ _ _ _ _ _ (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ HD2 Hag3a) AS3) Hag3) as HD3.
      assert (FD4 : fd_lookup (m_fds mo4) (Z_to_bv 64 3) = Some (FdFile pathb (Z_to_bv 64 (Z.of_nat (length (DATA ++ bs)))))) by (rewrite Efds3, Efds3a; exact FD3).
      assert (FS4 : m_fs mo4 = FS0) by (rewrite Efs3, Efs3a; exact FS3).
      assert (SO4 : SO s4 = stdout_init) by (rewrite SO3, SO2; exact SO0).
      clear MUc WOKW AG3 BA2 ST MI IMG G E IB FR2 BLK2 BLK1 DSTB RESTB BLK1' RESTB' DSTB'.
      pose proof BA3 as (ST & MI & IMG & (G & E & IB)). unfold LO in ST.
      pose proof (PSTK [mkABlock A cap]) as PS3. pose proof (pol_img [mkABlock A cap]) as PI3.
      aseg DI HK3.
      (* [comment removed for export] *)
      zstepA. zstepA. zstepA. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        aleaf. intros mo5 Hag5 HK5 Efs5 Efds5 Hh5.
        replace (Z.of_nat (length bs) + LEN) with (Z.of_nat (length (DATA ++ bs))) by (rewrite length_app; lia).
        eapply (az_grow cap (DATA ++ bs) s4 mo5); [| rewrite Efs5, FS4, <- FS; exact FSL | rewrite length_app; exact PRE' | rewrite length_app; lia |].
        * unfold RDCORE. exists (firstn (Z.to_nat (cap - LEN) - length bs) (skipn (length bs) junk)), H.
          split. { unfold BUFC. split; [exact BLK' | unfold MAX_INPUT; split; [split; [lia| exact CAPK]|]; split; [rewrite length_app; lia| exact BR]]. }
          split; [exact HK5|]. split; [eapply (adi_hd_magree _ _ _ _ DI); [exact HD3| exact Hag5]|]. split; [exact HB|]. split; [exact SO4|].
          split; [rewrite Efds5; exact FD4|]. split; [rewrite Efs5; exact FS4|].
          split; [exact FR3|]. split; [exact BA3| exact FRM3].
        * intros cap' s' mo' ms' HM FSL' RI'. apply (IH cap' (DATA ++ bs) s' mo' ms'); [unfold rmeas in *; rewrite length_app in *; lia | exact FSL' | rewrite length_app; exact PRE' | exact RI'].
      + (* [comment removed for export] *)
        zstepA. zstepA. aleaf. intros mo5 Hag5 HK5 Efs5 Efds5 Hh5.
        apply (IH cap (DATA ++ bs) s4 mo5); [unfold rmeas; rewrite length_app; lia | rewrite Efs5, FS4, <- FS; exact FSL | rewrite length_app; exact PRE' |].
        unfold RDINV. do 17 eexists. exists F3, fc3, m3, A.
        split. { rewrite length_app. replace (Z.of_nat (length bs) + LEN) with (Z.of_nat (length DATA + length bs)%nat) by lia. reflexivity. }
        split; [| rewrite length_app; lia].
        unfold RDCORE. exists (firstn (Z.to_nat (cap - LEN) - length bs) (skipn (length bs) junk)), H.
        split. { unfold BUFC. split; [exact BLK' | unfold MAX_INPUT; split; [split; [lia| exact CAPK]|]; split; [rewrite length_app; lia| exact BR]]. }
        split; [exact HK5|]. split; [eapply (adi_hd_magree _ _ _ _ DI); [exact HD3| exact Hag5]|]. split; [exact HB|]. split; [exact SO4|].
        split; [rewrite Efds5; exact FD4|]. split; [rewrite Efs5; exact FS4|].
        split; [exact FR3|]. split; [exact BA3| exact FRM3].
    - (* [comment removed for export] *)
      assert (Ebs : bs = []) by (destruct bs; [reflexivity| cbn [length] in K1; exfalso; rewrite ?unsigned_lit in K1 by lia; lia]).
      assert (LENF : length DATA = length FILE).
      { pose proof (f_equal (@length byte) PRE) as L1. rewrite length_firstn in L1.
        assert (L2 : length bs = 0%nat) by (rewrite Ebs; reflexivity).
        unfold bs in L2. rewrite length_firstn, length_skipn in L2. lia. }
      assert (EDF : DATA = FILE) by (rewrite PRE, LENF, firstn_all; reflexivity).
      aleaf. intros mo4 Hag4 HK4 Efs4 Efds4 Hh4.
      assert (TLF : TFIN = KDONE).
      { unfold TFIN. replace (MAX_INPUT <=? Z.of_nat (length FILE)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia). reflexivity. }
      rewrite TLF. apply (HBRK cap s3 mo4); [| lia].
      rewrite EDF in BLK2.
      unfold RDBRK. do 17 eexists. exists F2, fc2, m2, A. split; [rewrite <- LENF; reflexivity|].
      unfold RDCORE. exists junk, H.
      split. { unfold BUFC. split; [replace (Z.of_nat (length FILE)) with LEN by lia; exact BLK2 | unfold MAX_INPUT; split; [split; [lia| exact CAPK]|]; split; [lia| exact BR]]. }
      split; [exact HK4|]. split; [eapply (adi_hd_magree _ _ _ _ DI); [exact HD2| exact Hag4]|]. split; [exact HB|]. split; [rewrite SO2; exact SO0|].
      split. { rewrite Efds4, FD3. rewrite Ebs, app_nil_r, EDF. reflexivity. } split; [rewrite Efs4; exact FS3|].
      split; [exact FR2|]. split; [exact BA2| exact FRM2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma az_round : forall (cap : Z) (DATA : list byte) s mo ms,
    RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA)))) cap DATA s mo ms ->
    fs_lookup (m_fs mo) pathb = Some FILE -> DATA = firstn (length DATA) FILE ->
    (forall cap' DATA' s' mo' ms', rmeas cap' DATA' < rmeas cap DATA ->
        fs_lookup (m_fs mo') pathb = Some FILE -> DATA' = firstn (length DATA') FILE ->
        RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA')))) cap' DATA' s' mo' ms' ->
        realizes_cfg acfg asegs (mkCfg ms' mo') TFIN) ->
    realizes_cfg acfg asegs (mkCfg ms mo) TFIN.
  Proof.
    intros cap DATA s mo ms RI FSL PRE IH.
    destruct RI as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & A & -> & RC & LT).
    destruct RC as (junk & H & BU & HKx & HD & HB & SO0 & FD & FS & FR & BA & FRM).
    destruct BU as (BLK & [CAPR CAPK] & LENR & BR). unfold MAX_INPUT in CAPR.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & IMG & (G & E & IB)). unfold LO in ST.
    set (LEN := Z.of_nat (length DATA)) in *.
    pose proof (PSTK [mkABlock A cap]) as PS. pose proof (pol_img [mkABlock A cap]) as PI.
    (* [comment removed for export] *)
    assert (RP : forall moa x1' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' x23' t3' t4' t5' t6' CNT,
      magree mo moa -> AHK s [mkABlock A cap] [] mm moa -> m_fs moa = m_fs mo -> m_fds moa = m_fds mo ->
      0 < CNT <= 65536 -> CNT <= cap - LEN ->
      realizes_cfg acfg asegs (mkCfg (GST 0x81b80 x1' t0' t1' t2' (Z_to_bv 64 A) a0' a1' (Z_to_bv 64 CNT) a3' a4' a5' a6' a7' (Z_to_bv 64 P1v) (Z_to_bv 64 LEN) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23' t3' t4' t5' t6' F fc mm) moa) TFIN).
    { intros moa x1' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' x23' t3' t4' t5' t6' CNT Hag HKa Efs Efds C1 C2.
      eapply (az_read_part cap DATA s moa); [| rewrite Efs; exact FSL | exact PRE | lia | lia | lia | exact IH].
      unfold RDCORE. exists junk, H. split; [split; [exact BLK| unfold MAX_INPUT; split; [split; [lia| exact CAPK]|]; split; [lia| exact BR]]|].
      split; [exact HKa|]. split; [eapply (adi_hd_magree _ _ _ _ DI); [exact HD| exact Hag]|]. split; [exact HB|].
      split; [exact SO0|]. split; [rewrite Efds; exact FD|]. split; [rewrite Efs; exact FS|]. split; [exact FR|]. split; [exact BA| exact FRM]. }
    aseg DI HKx.
    (* [comment removed for export] *)
    zstepA. zstepA. zstepA. if_cases K01; zify_cond K01.
    - (* [comment removed for export] *)
      aleaf. intros moa Haga HKa Efsa Efdsa Hha. eapply RP; [exact Haga| exact HKa| exact Efsa| exact Efdsa| lia| lia].
    - zstepA. aleaf. intros moa Haga HKa Efsa Efdsa Hha. eapply RP; [exact Haga| exact HKa| exact Efsa| exact Efdsa| lia| lia].
  Qed.

  Lemma az_loop : forall (fuel : nat) (cap : Z) (DATA : list byte) s mo ms,
    rmeas cap DATA < Z.of_nat fuel ->
    RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length DATA)))) cap DATA s mo ms ->
    fs_lookup (m_fs mo) pathb = Some FILE -> DATA = firstn (length DATA) FILE ->
    realizes_cfg acfg asegs (mkCfg ms mo) TFIN.
  Proof.
    induction fuel as [|fuel IH]; intros cap DATA s mo ms HM RI FSL PRE.
    - exfalso. destruct RI as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & A & _ & RC & LT).
      destruct RC as (junk & H & BU & _). destruct BU as (_ & [CAPR _] & LENR & _). unfold rmeas, MAX_INPUT in *. cbn in HM. lia.
    - eapply az_round; [exact RI | exact FSL | exact PRE |].
      intros cap' DATA' s' mo' ms' HM' FSL' PRE' RI'. apply (IH cap' DATA' s' mo' ms'); [lia | exact RI' | exact FSL' | exact PRE'].
  Qed.

  (* [comment removed for export] *)
  Lemma az_loop0 : forall s mo ms,
    RDINV' 3 P1v (FdFile pathb (Z_to_bv 64 0)) 65536 [] s mo ms ->
    fs_lookup (m_fs mo) pathb = Some FILE ->
    realizes_cfg acfg asegs (mkCfg ms mo) TFIN.
  Proof.
    intros s mo ms RI FSL. apply (az_loop (Z.to_nat (rmeas 65536 []) + 1) 65536 [] s mo ms); [unfold rmeas, MAX_INPUT; cbn; lia | exact RI | exact FSL | reflexivity].
  Qed.
End C.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CDir.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte)
            (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Variable D : adrv_params.
  Hypothesis DI : a_drv_iface asegs ACONSTS AFMTS D.
  Hypothesis DIx : a_drv_iface5x asegs ACONSTS D.
  Notation AHK := (p_AHK D).
  Notation SO := (p_SO D).
  Notation AHEAD := (p_AHEAD D).

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 0x5e0b10).
  Notation IMGB := (build_stack_bytes aph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation ABASE' := (ABASE sp0 argv envp uid hw rnd).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Variable FS0 : Fs.Fs.
  Notation RDINV' := (RDINV sp0 argv envp uid hw rnd PAD S4 S5 S6 S7 S8 S9 S10 S11 D FS0).
  Let PSTK := PSTK sp0 VSP RCSP.

  Variables (P1v : Z).
  Hypothesis HP1 : nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v).
  Hypothesis P1R : 0 <= P1v < 2^64.

  Lemma az_loop_dir : forall s mo ms,
    RDINV' 3 P1v FdDir 65536 [] s mo ms ->
    realizes_cfg acfg asegs (mkCfg ms mo) (TDIE (pieces_read_error (map bv_unsigned arg1)) stdout_init FS0).
  Proof.
    intros s mo ms RI.
    destruct RI as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & A & -> & RC & _).
    destruct RC as (junk & H & BU & HKx & HD & HB & SO0 & FD & FS & FR & BA & FRM).
    destruct BU as (BLK & [CAPR CAPK] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    cbn [c_img_hi ACONSTS] in BR5. unfold MAX_INPUT in CAPR.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. pose proof STAGE_val as SV.
    pose proof BA as (ST & MI & IMG & (G & E & IB)). unfold LO in ST. unfold MFRAME in FR.
    cbn [length Z.of_nat] in *.
    destruct (RSTG_any mm) as [stg RSG].
    pose proof RSG as DST. unfold RSTG in DST.
    apply (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat 65536; Z.to_nat STAGE - Z.to_nat 65536]%nat) in DST; [| cbn; lia]. cbn [mk_CB_cells app] in DST.
    apply (proj1 (rw_cells_app _ _ _ [CB (Z.to_nat 65536) (firstn (Z.to_nat 65536) stg)] _)) in DST. destruct DST as [DST _].
    pose proof (PSTK [mkABlock A 65536]) as PS. pose proof (pol_img [mkABlock A 65536]) as PI.
    aseg DI HKx.
    (* [comment removed for export] *)
    zstepA. zstepA. zstepA. if_cases K01; zify_cond K01; [exfalso; lia|].
    zstepA. zstepA. zstepA. zstepA. rewrite ?Z.sub_0_r.
    aleaf. intros moa Haga HKa Efsa Efdsa Hha.
    (* [comment removed for export] *)
    assert (RO : read_out 3 RSTAGE 65536 moa = Some (RdErr EISDIR, moa)) by (unfold read_out; rewrite Efdsa, FD; reflexivity).
    eapply (adx_read_s _ _ _ DIx) with (lo := usp0 - 8388608) (buf := RSTAGE) (count := 65536) (fd := 3);
      [ apply TDIE_nil | exact HKa | unfold RSTAGE, A_RSTAGE; lia | unfold RSTAGE, A_RSTAGE, A_RSTAGE_LEN; lia | lia | lia | exact DST | exact RO
      | rewrite unsigned_lit by lia; exact ST | lia
      | rewrite unsigned_lit by lia; unfold AICP_STACK; lia | reflexivity | exact FRM | reflexivity | reflexivity | reflexivity | ].
    intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 mo3 s3 res ST2 RES WM2 FRM2 HK2 AS2 SO2 Efs2 Efds2 Hag2.
    cbv iota beta in RES. destruct RES as [-> MUc]. cbn [c_errno ACONSTS] in MUc.
    rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x81b8c)) with (Z_to_bv 64 0x81b8c) by (symmetry; rpc).
    assert (WOKW : Forall (AWOK sp0) [(usp0 - 8388608, usp0 + -128); (RSTAGE, RSTAGE + 65536); (0x5e0a6c, 0x5e0a6c + 4)]).
    { unfold AWOK, LO, RSTAGE. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK2) as MI2.
    assert (BA2 : ABASE' m2) by (eapply (ABASE_munch sp0 argv envp uid hw rnd VSP RCSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WM2| exact MI2| unfold LO; exact ST2]).
    pose proof (agree_on_of_munch _ _ _ MUc WM2) as AG.
    assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply rw_cells_agree; [exact AG | exact FR | intros ax Ha; cbn in Ha |- *; unfold RSTAGE; lia]).
    clear MUc WOKW BA ST MI IMG G E IB FR.
    pose proof BA2 as (ST & MI & IMG & (G & E & IB)). unfold LO in ST.
    (* [comment removed for export] *)
    pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
    destruct (proj2 IMG 1%nat arg1 ltac:(lia) ltac:(rewrite EARGV; reflexivity))
      as (p1 & slack1 & HP1' & P1LO & P1HI & STR1 & SLK1 & TOP1). unfold str_base, struct_size, argc, envc in P1LO.
    assert (EP : p1 = P1v).
    { rewrite HP1 in HP1'. assert (EE : bv_unsigned (Z_to_bv 64 P1v) = bv_unsigned (Z_to_bv 64 p1)) by congruence.
      rewrite !unsigned_lit in EE by lia. lia. }
    subst p1.
    assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
    assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
    pose proof (PSTK [mkABlock A 65536]) as PS2. pose proof (pol_img [mkABlock A 65536]) as PI2.
    aseg DI HK2.
    zstepA. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
    (* [comment removed for export] *)
    do 7 zstepA. aleaf. intros mo4 Hag4 HK4 Efs4 Efds4 Hh4.
    replace FS0 with (m_fs mo4) by (rewrite Efs4, Efs2, Efsa; exact FS).
    eapply (az_fprintf_exit sp0 argv envp uid hw rnd S8 S9 S10 S11 VSP RCSP D DI DIx (DReadError (map bv_unsigned arg1)) s3 [mkABlock A 65536]);
      [| exact BA2 | exact HK4 | rewrite SO2; exact SO0 | exact FRM2].
    cbn [adiag_args f_read_error AFMTS]. split; [reflexivity|].
    rewrite !unsigned_lit by lia. rewrite zb_map_unsigned. unfold zlength. rewrite !length_map.
    split; [exists slack1; split; [exact STR1 | exact SLK1]|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|]. split; lia.
  Qed.
End CDir.
End RC__1.

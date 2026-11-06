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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface ADrv_ctx ADrv_A ADrv_B ADrv_C.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AX_atexit A_iface5x.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SysStepA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
(* [comment removed for export] *)
Ltac fix_lit_store_a :=
  try (lazymatch goal with
       | |- evtA _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evtA _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac zstA := zstepA; fix_lit_store_a.
(* [comment removed for export] *)
Ltac RET0A :=
  lazymatch goal with
  | |- context [Z_to_bv 64 (Z.land ?x 78)] =>
      replace (Z_to_bv 64 (Z.land x 78)) with (Z_to_bv 64 0) by (vm_compute; reflexivity)
  | _ => idtac
  end.
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Ltac aceil_in H := aceil.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition Y_EMPTY : Z := 0x5e01e0.

(* [comment removed for export] *)
Fixpoint emits (n : nat) (so : stdout_st) : list Z * stdout_st :=
  match n with
  | O => ([], so)
  | S k => let e1 := vprintf_pure so (pieces_emit_d 0) in
           let e2 := emits k (snd e1) in
           (fst e1 ++ fst e2, snd e2)
  end.

Lemma vprintf_pure_buf_bound : forall so ps, zlength (so_buf so) <= STDOUT_BUFSIZ -> zlength (so_buf (snd (vprintf_pure so ps))) <= STDOUT_BUFSIZ.
Proof.
  intros so ps Hb. unfold vprintf_pure. apply pieces_pure_buf_bound.
  unfold towrite_pure. destruct (so_active so); [exact Hb|]. unfold zlength, STDOUT_BUFSIZ. cbn. lia.
Qed.
Lemma emits_0 : forall so, fst (emits 0 so) = [] /\ snd (emits 0 so) = so.
Proof. intros so. split; reflexivity. Qed.
Lemma emits_S : forall n so,
  fst (emits (S n) so) = fst (vprintf_pure so (pieces_emit_d 0)) ++ fst (emits n (snd (vprintf_pure so (pieces_emit_d 0))))
  /\ snd (emits (S n) so) = snd (emits n (snd (vprintf_pure so (pieces_emit_d 0)))).
Proof.
  intros n so. change (emits (S n) so) with (let e1 := vprintf_pure so (pieces_emit_d 0) in let e2 := emits n (snd e1) in (fst e1 ++ fst e2, snd e2)).
  cbv zeta. split; reflexivity.
Qed.
Lemma emits_buf_bound : forall n so, zlength (so_buf so) <= STDOUT_BUFSIZ -> zlength (so_buf (snd (emits n so))) <= STDOUT_BUFSIZ.
Proof.
  induction n as [|n IH]; intros so Hb.
  - exact Hb.
  - rewrite (proj2 (emits_S n so)). apply IH. apply vprintf_pure_buf_bound. exact Hb.
Qed.

Lemma In_ab_remove : forall A b LB, In b LB -> ab_addr b <> A -> In b (ab_remove A LB).
Proof.
  intros A b LB. induction LB as [|x LB IH]; [intros [] |].
  intros [-> | H] NE; cbn [ab_remove].
  - destruct (Z.eqb (ab_addr b) A) eqn:E; [apply Z.eqb_eq in E; lia| left; reflexivity].
  - destruct (Z.eqb (ab_addr x) A); [exact H| right; apply IH; assumption].
Qed.

Lemma count_yfuzz_hist : forall H, Forall ev_big_or_free H -> count_yfuzz H = 0%nat.
Proof.
  intros H HF. unfold count_yfuzz. induction HF as [|e H He HF IH]; [reflexivity|].
  cbn [List.filter]. destruct e; cbn in He; [exact IH | exact IH | destruct He].
Qed.


Lemma nbig_le_len : forall LB, nbig LB <= Z.of_nat (length LB).
Proof.
  intros LB. unfold nbig. induction LB as [|b LB IH]; cbn [List.filter length]; [lia|].
  destruct (64512 <? ab_size b); cbn [length]; lia.
Qed.

Section RUN.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte)
            (PAD : list byte) (S4 S5 S6 S7 X7 S8 S9 S10 S11 : word).   (* [comment removed for export] *)
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
  Lemma hd_weaken_le : forall s mo k k' X H, AHEAD k X H s mo -> (k' <= k)%nat -> AHEAD k' X H s mo.
  Proof.
    intros s mo k k' X H HD Hle. induction Hle as [|m Hle IH]; [exact HD|].
    apply IH. eapply (adi_hd_weaken _ _ _ _ DI). exact HD.
  Qed.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 0x5e0b10).
  Notation IMGB := (build_stack_bytes aph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation ABASE' := (ABASE sp0 argv envp uid hw rnd).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Let PSTK := PSTK sp0 VSP RCSP.

  Variable FS0 : Fs.Fs.

  (* [comment removed for export] *)
  Definition TRFRAME (mm : mem) (pad : list byte) (A L PL SB1 : Z) : Prop :=
    rw_cells asegs mm (usp0 + -208)
      [CB 8 pad; C8 X7; C8 (Z_to_bv 64 RSTAGE); C8 (Z_to_bv 64 SB1); C8 (Z_to_bv 64 PL); C8 (Z_to_bv 64 (A + 6 + L)); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 2)); C8 (Z_to_bv 64 0x81c18)].

  (* [comment removed for export] *)
  Definition RBASE (mm : mem) : Prop :=
    stk asegs mm LO' (usp0 + -208) /\ mem_inv asegs mm /\ AIMG sp0 argv envp uid hw rnd mm /\ ASTAT mm.

  Lemma RBASE_heap_pres : forall LB LF m m' SP, RBASE m -> aheap_pres asegs ACONSTS LB LF SP m m' -> SP <= usp0 + -208 ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -208) -> RBASE m'.
  Proof.
    intros LB LF m m' SP (ST & MI & IMG & AS) HP HSP MI' ST'. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    pose proof (aheap_pres_agree _ _ _ _ _ _ HP) as AG.
    split; [exact ST'|]. split; [exact MI'|]. split.
    - eapply AIMG_agree; [exact AG| intros a Ha; left; lia| exact IMG].
    - eapply ASTAT_agree; [exact AG| | exact AS]. intros a Ha. right; right; right. unfold adrv_static, astat_addr in *. cbn [c_seg3_lo c_seg3_hi c_initialized ACONSTS]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma RBASE_reflag : forall (P : Z -> Prop) m m', RBASE m -> agree_on P m m' ->
    (forall a, (usp0 <= a \/ astat_addr a) -> a <> 0x5e01d4 -> P a) ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -208) -> rw_cells asegs m' 0x5e01d4 [C1 (Z_to_bv 8 0)] -> RBASE m'.
  Proof.
    intros P m m' (ST & MI & IMG & AS) AG HP MI' ST' FL. pose proof (sp_facts sp0 VSP RCSP) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|]. split.
    - eapply AIMG_agree; [exact AG| | exact IMG]. intros a Ha. apply HP; [left; lia| lia].
    - eapply ASTAT_reflag; [exact AG| | exact FL| exact AS]. intros a Ha NE. apply HP; [right; exact Ha| exact NE].
  Qed.

  (* [comment removed for export] *)
  Definition RWOK (iv : Z * Z) : Prop :=
    (LO' <= fst iv /\ snd iv <= usp0 + -208) \/ (snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x603000 <= fst iv))
    \/ (fst iv = 0xa9178 /\ snd iv = 0xa9178 + 232) \/ (fst iv = 0x601220 /\ snd iv = 0x601220 + 1024).   (* [comment removed for export] *)

  Lemma RWOK_outside : forall W a, Forall RWOK W ->
    (usp0 + -208 <= a \/ (0x10000 <= a < 0x603000 /\ (a < 0xa9178 \/ 0xa9178 + 232 <= a) /\ (a < 0x601220 \/ 0x601220 + 1024 <= a))) -> outside W a.
  Proof.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold RWOK, LO in H1, SF. aceil. cbn [fst snd] in H1. lia.
  Qed.

  Lemma RBASE_munch : forall W m m', RBASE m -> Forall RWOK W -> munch W m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' LO' (usp0 + -208) -> RBASE m'.
  Proof.
    intros W m m' (ST & MI & IMG & AS) HW MU WM MI' ST'. pose proof (sp_facts sp0 VSP RCSP) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. unfold LO in *.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    split; [exact ST'|]. split; [exact MI'|]. split.
    - eapply AIMG_agree; [exact AG| | exact IMG]. intros a Ha. cbn. apply RWOK_outside; [exact HW| left; lia].
    - eapply ASTAT_agree; [exact AG| | exact AS]. intros a Ha. cbn. apply RWOK_outside; [exact HW| unfold astat_addr in Ha; right; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Loop.
    (* [comment removed for export] *)
    Variables (T PL OWN A L SB1 : Z) (PAY : list byte) (pad : list byte) (REST0 : list ablock).
    (* [comment removed for export] *)
    Variable KEND : stdout_st -> TSet.
    Hypothesis KEND_nil : forall so, KEND so [].
    Hypothesis HLEN0 : Z.of_nat (length REST0) <= 2.     (* [comment removed for export] *)

    Definition RUNINV (n : nat) (so : stdout_st) (s : p_APS D) (mo : Model) (mm : mem) (fc : bv 32) : Prop :=
      exists (H : list aevent),
        (count_yfuzz H + n <= 4)%nat /\
        TRFRAME mm pad A L PL SB1 /\ FRAME' mm /\ RBASE mm /\ SO s = so /\ zlength (so_buf so) <= STDOUT_BUFSIZ
        /\ AHK s REST0 [] mm mo /\ AHEAD n (map (fun b => (ab_addr b, ab_size b)) REST0) H s mo /\ m_fs mo = FS0   (* [comment removed for export] *)
        /\ bytes_at asegs mm T PAY /\ 0 < T /\ T + PL < 2^62 /\ Z.of_nat (length PAY) = PL /\ PL < 2^26
        /\ ((exists bt, In bt REST0 /\ ab_addr bt <= T /\ T + PL <= ab_addr bt + ab_size bt) \/ (PL = 0 /\ T = Y_EMPTY))
        /\ frm0 fc.

    Hypothesis HEND : forall n so s mo mm fc (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 : word) (F : bvmap 5 word),
      RUNINV n so s mo mm fc ->
      realizes_cfg acfg asegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 (Z_to_bv 64 PL) (Z_to_bv 64 T) a0 a1 a2 a3 a4 a5 a6 a7
                                          (Z_to_bv 64 OWN) s3v (Z_to_bv 64 0x5e01d0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
                                  F (Z_to_bv 64 0x81e64) fc None mm (seg_rom asegs)) mo)
                (KEND so).

    Lemma az_run_loop : forall (n : nat) so s mo mm fc (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 : word) (F : bvmap 5 word),
      (1 <= n <= 4)%nat ->
      RUNINV n so s mo mm fc ->
      realizes_cfg acfg asegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 (Z_to_bv 64 PL) (Z_to_bv 64 T) a0 a1 a2 a3 a4 a5 a6 a7
                                          (Z_to_bv 64 OWN) s3v (Z_to_bv 64 0x5e01d0) (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
                                  F (Z_to_bv 64 0x81e2c) fc None mm (seg_rom asegs)) mo)
                (ShapeAlg.t_emit (Wz 1 (fst (emits n so))) (KEND (snd (emits n so)))).
    Proof.
      induction n as [|n IH]; intros so s mo mm fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 F Hn RI; [lia|].
      destruct RI as (H & CNT & TRF & FR & RB & SOE & SOB & HKx & HD & FS & PAYB & T0 & T62 & PLEN & PL26 & PBLK & FRM).
      pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
      pose proof RB as (ST & MI & IMG & AS). unfold LO in ST.
      pose proof (PSTK REST0) as PS. pose proof (pol_img REST0) as PI.
      destruct (adi_blocks _ _ _ _ DI _ _ _ _ _ HKx) as (RNG & _ & _).
      (* [comment removed for export] *)
      assert (PAYOFF : forall a, T <= a < T + Z.of_nat (length PAY) -> in_ablock REST0 a /\ 0x603000 <= a < alloc_ceiling).
      { intros a Ha. destruct PBLK as [(bt & Hin & Hb1 & Hb2)| [Z0 _]]; [| lia].
        pose proof (RNG bt Hin) as BR. unfold ablock_range in BR. cbn [c_img_hi ACONSTS] in BR.
        split; [exists bt; split; [exact Hin| lia]| lia]. }
      (* [comment removed for export] *)
      pose proof (ASTAT_flag _ AS) as FLG.
      pose proof (conj PAYB I) as PAYK. clear PAYB.
      pose proof (munch_refl [(0x5e01d4, 0x5e01d4 + 1)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
      aseg DI HKx. zstepA. zstA. zstepA. zstepA. zstepA. aleaf. intros moa Haga HKa Efsa Efdsa Hha.
      lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => set (mf1 := mx) in * end.
      lazymatch goal with HH : stk _ mf1 _ _ |- _ => rename HH into ST1 end.
      lazymatch goal with HH : mem_inv _ mf1 |- _ => rename HH into MI1 end.
      lazymatch goal with HH : munch _ mm mf1 |- _ => rename HH into MU1 end.
      lazymatch goal with HH : wmono _ mm mf1 |- _ => rename HH into WM1 end.
      lazymatch goal with HH : rw_cells _ mf1 0x5e01d4 _ |- _ => rename HH into FLG1 end.
      pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
      assert (OUT1 : forall a, a <> 0x5e01d4 -> (fun a0 : Z => outside [(0x5e01d4, 0x5e01d4 + 1)] a0) a) by (intros a Ha; cbn; lia).
      assert (HK1 : AHK s REST0 [] mf1 moa).
      { eapply (AHK_after D DI); [exact HKa| exact MU1| exact WM1|]. constructor; [apply wok_flag| constructor]. }
      assert (PAYB1 : bytes_at asegs mf1 T PAY).
      { eapply bytes_at_agree; [exact AG1 | exact (proj1 PAYK) |]. intros a Ha. apply OUT1. destruct (PAYOFF a Ha) as [_ OFF]. lia. }
      (* [comment removed for export] *)
      eapply (adi_yfuzz _ _ _ _ DI) with (lo := usp0 - 8388608) (T := T) (n := PL) (txt := PAY); try reflexivity.
      all: rewrite ?(unsigned_lit (usp0 + -208)) by lia.
      - apply ShapeAlg.t_emit_has_nil.
      - exact HK1.
      - exact PAYB1.
      - exact PLEN.
      - lia.
      - destruct PBLK as [(bt & Hin & Hb1 & Hb2)| [-> ->]]; [left; exists bt; split; [exact Hin| lia] | right; split; reflexivity].
      - pose proof (nbig_le_len REST0). lia.
      - exact ST1.
      - aceil; lia.
      - unfold AYFUZZ_STACK. lia.
      - clear - SF. Z.div_mod_to_equations. lia.
      - lia.
      - apply (adi_uanchorC _ _ _ _ DI); [in_lits| rewrite unsigned_lit by lia; aceil; lia].
      - exact FRM.
      - eapply (adi_hd_cyfuzz _ _ _ _ DI); [eapply (adi_hd_magree _ _ _ _ DI); [exact HD| exact Haga] | lia | lia].
      - intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 mo2 s2 ST2 HPR FRM2 SOE2 HK2 YREL FS2 FDS2 CR2.
        replace (ret_pc (Z_to_bv 64 0x81e40)) with (Z_to_bv 64 0x81e40) by (symmetry; rpc).
        pose proof (aheap_pres_agree _ _ _ _ _ _ HPR) as AG2.
        assert (FLG2 : rw_cells asegs m2 0x5e01d4 [C1 (Z_to_bv 8 1)]).
        { eapply rw_cells_agree; [exact AG2| exact FLG1|]. intros ax Ha. cbn in Ha. right; right; right.
          unfold adrv_static. cbn [c_seg3_lo c_seg3_hi c_initialized c_ystat_lo c_ystat_hi ACONSTS]. lia. }
        pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK2) as MI2.
        pose proof (adi_hd_yfuzz _ _ _ _ DI _ _ _ _ _ _ _ (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ HD Haga) ltac:(clear -CNT; lia) YREL) as HD2.
        try clear ST; try clear MI; try clear ST1; try clear MI1; try clear FLG1.
        pose proof (PSTK REST0) as PS2. pose proof (pol_img REST0) as PI2.
        (* [comment removed for export] *)
        aseg DI HK2.
        pose proof (munch_refl [(usp0 - 288, usp0 - 208); (0x5e01d4, 0x5e01d4 + 1)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
        zstepA. zstA. zstepA. zstepA.
        zstepA. carve_frame 80%nat ST2.
        do 14 zstepA.
        aleaf. intros mo2a Hag2a HK2a Efs2a Efds2a Hh2a.
        lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => set (mf3 := mx) in * end.
        lazymatch goal with HH : stk _ mf3 _ _ |- _ => rename HH into ST3 end.
        lazymatch goal with HH : mem_inv _ mf3 |- _ => rename HH into MI3 end.
        lazymatch goal with HH : munch _ m2 mf3 |- _ => rename HH into MU3 end.
        lazymatch goal with HH : wmono _ m2 mf3 |- _ => rename HH into WM3 end.
        lazymatch goal with HH : rw_cells _ mf3 (usp0 + -288) _ |- _ => rename HH into EFR end.
        lazymatch goal with HH : rw_cells _ mf3 0x5e01d4 _ |- _ => rename HH into FLG3 end.
        assert (HK3 : AHK s2 REST0 [] mf3 mo2a).
        { eapply (AHK_after D DI); [exact HK2a| exact MU3| exact WM3|]. constructor; [| constructor; [apply wok_flag| constructor]]. apply wok_stack.
          aceil; lia. }
        destruct (emits_S n so) as [E1 E2]. rewrite E1, E2, Wz_app.
        eapply rz_conseq_cfg; [| apply t_eq_sym; apply t_eq_emit_app].
        pose proof EFR as EFR'. 
        apply (proj1 (rw_cells_app _ _ _ [C8 (Z_to_bv 64 (usp0 + -264)); C8 (Z_to_bv 64 0x81e50); CB 8 _] _)) in EFR'. destruct EFR' as [_ APC].
        cbn [cells_size csize Nat.add] in APC.
        apply (proj1 (rw_cells_app _ _ _ [C8 (Z_to_bv 64 0)] _)) in APC. destruct APC as [APC _].
        replace (usp0 + -288 + Z.of_nat 24) with (usp0 + -264) in APC by lia.
        rewrite <- SOE, <- SOE2.
        eapply (adi_printf _ _ _ _ DI) with (lo := usp0 - 8388608) (ap := usp0 + -264) (v1 := Z_to_bv 64 0);
          rewrite ?(unsigned_lit (usp0 + -288)) by lia.
        + apply ShapeAlg.t_emit_has_nil.
        + exact HK3.
        + exact APC.
        + rewrite unsigned_lit by lia. reflexivity.
        + lia.
        + lia.
        + clear -SF. Z.div_mod_to_equations. lia.
        + rewrite SOE2, SOE. exact SOB.
        + exact ST3.
        + aceil; lia.
        + unfold AICP_STACK. lia.
        + lia.
        + reflexivity.
        + exact FRM2.
        + reflexivity.
        + zsimp. reflexivity.
        + intros v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 fc4 m4 mo4 s4 ST4 MUc WM4 FRM4 HK4 AS4 SO4 Efs4 Efds4 VS4.
          replace (ret_pc (Z_to_bv 64 0x81f38)) with (Z_to_bv 64 0x81f38) by (symmetry; rpc).
          rewrite ?(unsigned_lit (usp0 + -288)) in MUc by lia. rewrite SOE2, SOE.
          cbn [c_stdout_F c_stdout_buf ACONSTS] in MUc.
          pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK4) as MI4.
          assert (ST4' : stk asegs m4 (usp0 - 8388608) (usp0 + -288)) by exact ST4.
          pose proof (agree_on_of_munch _ _ _ MUc WM4) as AG4.
          pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
          lazymatch type of EFR with rw_cells _ _ _ ?cs =>
            assert (EFR4 : rw_cells asegs m4 (usp0 + -288) cs) by (eapply rw_cells_agree; [exact AG4| exact EFR| intros ax Ha; cbn in Ha |- *; lia]) end.
          assert (FLG4 : rw_cells asegs m4 0x5e01d4 [C1 (Z_to_bv 8 0)]) by (eapply rw_cells_agree; [exact AG4| exact FLG3| intros ax Ha; cbn in Ha |- *; lia]).
          (* [comment removed for export] *)
          assert (AG : agree_on (fun a => aclient_addr ACONSTS REST0 [] (usp0 + -208) a /\ a <> 0x5e01d4
                                          /\ (a < 0xa9178 \/ 0xa9178 + 232 <= a) /\ (a < 0x601220 \/ 0x601220 + 1024 <= a)
                                          /\ (a < usp0 - 8388608 \/ usp0 + -208 <= a)) mm m4).
          { eapply agree_on_trans; [eapply agree_on_trans; [eapply agree_on_trans|]|].
            - eapply agree_on_mono; [exact AG1|]. intros a (_ & Ha & _). apply OUT1. exact Ha.
            - eapply agree_on_mono; [exact AG2|]. intros a (Ha & _). exact Ha.
            - eapply agree_on_mono; [exact AG3|]. intros a (_ & Ha & _ & _ & Hs). cbn. lia.
            - eapply agree_on_mono; [exact AG4|]. intros a (_ & _ & H1 & H2 & Hs). cbn. lia. }
          assert (STAT : forall a, 0x10000 <= a < 0x603000 -> adrv_static ACONSTS a -> a <> 0x5e01d4 ->
                           (a < 0xa9178 \/ 0xa9178 + 232 <= a) -> (a < 0x601220 \/ 0x601220 + 1024 <= a) ->
                           (fun a => aclient_addr ACONSTS REST0 [] (usp0 + -208) a /\ a <> 0x5e01d4
                                          /\ (a < 0xa9178 \/ 0xa9178 + 232 <= a) /\ (a < 0x601220 \/ 0x601220 + 1024 <= a)
                                          /\ (a < usp0 - 8388608 \/ usp0 + -208 <= a)) a).
          { intros a H1 H2 H3 H4 H5. cbv beta. split; [right; right; right; exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5| lia]. }
          assert (TRF4 : TRFRAME m4 pad A L PL SB1).
          { unfold TRFRAME. eapply rw_cells_agree; [exact AG | exact TRF |]. intros ax Ha. cbn in Ha. cbv beta. split; [left; lia| lia]. }
          assert (FR4 : FRAME' m4).
          { unfold MFRAME. eapply rw_cells_agree; [exact AG | exact FR |]. intros ax Ha. cbn in Ha. cbv beta. split; [left; lia| lia]. }
          assert (PAYB4 : bytes_at asegs m4 T PAY).
          { eapply bytes_at_agree; [exact AG | exact (proj1 PAYK) |]. intros ax Ha. destruct (PAYOFF ax Ha) as [INB OFF]. cbv beta. aceil.
            split; [right; left; exact INB| lia]. }
          assert (RB4 : RBASE m4).
          { eapply (RBASE_reflag _ mm m4 RB AG); [| exact MI4| | exact FLG4].
            - intros a [Ha|Ha] NE; [cbv beta; split; [left; lia| lia]|].
              apply STAT; [unfold astat_addr in Ha; lia| | exact NE| unfold astat_addr in Ha; lia| unfold astat_addr in Ha; lia].
              unfold adrv_static, astat_addr in *. cbn [c_seg3_lo c_seg3_hi c_initialized c_ystat_lo c_ystat_hi ACONSTS]. lia.
            - unfold LO. eapply stk_release in EFR4; [| exact ST4'| lia]. cbn [cells_size csize Nat.add] in EFR4.
              replace (usp0 + -288 + Z.of_nat 80) with (usp0 + -208) in EFR4 by lia. exact EFR4. }
          pose proof (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ (adi_hd_aps _ _ _ _ DI _ _ _ _ _ _ (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ HD2 Hag2a) AS4) VS4) as HD4.
          try clear IMG; try clear AS.
          pose proof (PSTK REST0) as PS4. pose proof (pol_img REST0) as PI4.
          aseg DI HK4. zstepA. zstepA. release_frame EFR4 ST4' (usp0 + -208). zstepA.
          replace (ret_pc (Z_to_bv 64 0x81e50)) with (Z_to_bv 64 0x81e50) by (symmetry; rpc).
          (* [comment removed for export] *)
          zstepA. zstepA. if_cases KB; [| exfalso; vm_compute in KB; discriminate KB]. clear KB.
          zstepA.
          rewrite (SysStep.swrap32_small (Z.of_nat (S n) + -1)) by lia.
          replace (Z.of_nat (S n) + -1) with (Z.of_nat n) by lia.
          zstepA. if_cases K1; zify_cond K1.
          * (* [comment removed for export] *)
            aleaf. intros mo5 Hag5 HK5 Efs5 Efds5 Hh5.
            apply (IH (snd (vprintf_pure so (pieces_emit_d 0))) s4 mo5 m4 fc4); [lia|].
            exists (EvYfuzz :: H).
            split; [unfold count_yfuzz in *; cbn [List.filter length] in *; lia|].
            split; [exact TRF4|]. split; [exact FR4|]. split; [exact RB4|]. split; [rewrite SO4, SOE2, SOE; reflexivity|].
            split; [apply vprintf_pure_buf_bound; exact SOB|]. split; [exact HK5|].
            split; [eapply (adi_hd_magree _ _ _ _ DI); [exact HD4| exact Hag5]|].
            split; [rewrite Efs5, Efs4, Efs2a, FS2, Efsa; exact FS|]. split; [exact PAYB4|].
            split; [lia|]. split; [lia|]. split; [exact PLEN|]. split; [exact PL26|]. split; [exact PBLK| exact FRM4].
          * (* [comment removed for export] *)
            assert (n = 0%nat) as -> by lia. destruct (emits_0 (snd (vprintf_pure so (pieces_emit_d 0)))) as [E3 E4]. rewrite E3, E4. rewrite ?app_nil_r. cbn [Wz map to_bytes].
            aleaf. intros mo5 Hag5 HK5 Efs5 Efds5 Hh5.
            eapply rz_conseq_cfg; [apply (HEND 0%nat (snd (vprintf_pure so (pieces_emit_d 0))) s4 mo5 m4 fc4) | apply t_eq_sym; apply t_emit_nil_eq; apply KEND_nil].
            exists (EvYfuzz :: H).
            split; [unfold count_yfuzz in *; cbn [List.filter length] in *; lia|].
            split; [exact TRF4|]. split; [exact FR4|]. split; [exact RB4|]. split; [rewrite SO4, SOE2, SOE; reflexivity|].
            split; [apply vprintf_pure_buf_bound; exact SOB|]. split; [exact HK5|].
            split; [eapply (adi_hd_magree _ _ _ _ DI); [exact HD4| exact Hag5]|].
            split; [rewrite Efs5, Efs4, Efs2a, FS2, Efsa; exact FS|]. split; [exact PAYB4|].
            split; [lia|]. split; [lia|]. split; [exact PLEN|]. split; [exact PL26|]. split; [exact PBLK| exact FRM4].
    Qed.
  End Loop.

  Lemma ab_remove_length : forall A LB, (length (ab_remove A LB) <= length LB)%nat.
  Proof. intros A0 LB. induction LB as [|b LB IH]; cbn [ab_remove length]; [lia|]. destruct (ab_addr b =? A0); cbn [length]; lia. Qed.

  Lemma ab_remove_notin : forall A LB, (forall b, In b LB -> ab_addr b <> A) -> ab_remove A LB = LB.
  Proof.
    intros A0 LB. induction LB as [|b LB IH]; intros HN; [reflexivity|]. cbn [ab_remove].
    destruct (Z.eqb_spec (ab_addr b) A0) as [E|NE]; [exfalso; exact (HN b (or_introl eq_refl) E)|].
    rewrite IH; [reflexivity|]. intros b' Hb'. apply HN. right. exact Hb'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section TargetRun.
    (* [comment removed for export] *)
    Variables (A cap L PL SB1 : Z) (FILE : list byte) (H0 : list aevent) (hk : nat).   (* [comment removed for export] *)
    Hypothesis HL : 0 <= L < 32768.
    Hypothesis HPL : 0 <= PL.
    Hypothesis HLEN : Z.of_nat (length FILE) = 6 + L + PL.
    Hypothesis HCAP : Z.of_nat (length FILE) < cap.
    Hypothesis HCAPM : cap <= 67108864.
    Hypothesis HH0 : Forall ev_big_or_free H0.
    Let PAY : list byte := skipn (Z.to_nat (6 + L)) FILE.
    Let calls : nat := if L =? 0 then 1%nat else S (Z.to_nat (bv_unsigned (nth 2 FILE (Z_to_bv 8 0)) mod 4)).

    (* [comment removed for export] *)
    Variable KR : Z -> stdout_st -> TSet.
    Hypothesis KR_nil : forall st so, KR st so [].

    Definition RETINV (so : stdout_st) (s : p_APS D) (mo : Model) (mm : mem) (fc : bv 32) : Prop :=
      exists (LB : list ablock) (LF : list fblock),
        FRAME' mm /\ ABASE' mm /\ SO s = so /\ zlength (so_buf so) <= STDOUT_BUFSIZ
        /\ AHK s LB LF mm mo /\ In (mkABlock A cap) LB /\ Z.of_nat (length LB) <= 2 /\ m_fs mo = FS0 /\ frm0 fc   (* [comment removed for export] *)
        /\ 1 <= p_acredit D s.                                                                                    (* [comment removed for export] *)

    Hypothesis HRET : forall (status : Z) so s mo mm fc (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word),
      0 <= status < 2^32 -> RETINV so s mo mm fc ->
      realizes_cfg acfg asegs (mkCfg (MS (mkR (Z_to_bv 64 0x81c18) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) (Z_to_bv 64 status) a1 a2 a3 a4 a5 a6 a7
                                          (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 SB1) (Z_to_bv 64 RSTAGE) X7 S8 S9 S10 S11 t3 t4 t5 t6)
                                  F (Z_to_bv 64 0x81c18) fc None mm (seg_rom asegs)) mo)
                (KR status so).

    (* [comment removed for export] *)
    Definition TPR (n : nat) (so : stdout_st) : TSet := ShapeAlg.t_emit (Wz 1 (fst (emits n so))) (KR 0 (snd (emits n so))).

    (* [comment removed for export] *)
    Lemma az_tr_tail : forall (T OWN : Z) (pad : list byte) (REST0 : list ablock),
      REST0 = (if OWN =? 0 then [] else [mkABlock OWN PL]) ++ [mkABlock A cap] ->
      0 <= OWN ->
      forall n so s mo mm fc (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 : word) (F : bvmap 5 word),
      RUNINV T PL A L SB1 PAY pad REST0 n so s mo mm fc ->
      realizes_cfg acfg asegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 (Z_to_bv 64 PL) (Z_to_bv 64 T) a0 a1 a2 a3 a4 a5 a6 a7
                                          (Z_to_bv 64 OWN) s3v (Z_to_bv 64 0x5e01d0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
                                  F (Z_to_bv 64 0x81e64) fc None mm (seg_rom asegs)) mo)
                (KR 0 so).
    Proof.
      intros T OWN pad REST0 ER HO n so s mo mm fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 F RI.
      destruct RI as (H & CNT & TRF & FR & RB & SOE & SOB & HKx & HD & FS & PAYB & T0 & T62 & PLEN & PL26 & PBLK & FRM).
      pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
      pose proof RB as (ST & MI & IMG & AS). unfold LO in ST. unfold TRFRAME in TRF.
      assert (RLEN : Z.of_nat (length REST0) <= 2) by (subst REST0; destruct (OWN =? 0); cbn [length app]; lia).
      pose proof (PSTK REST0) as PS. pose proof (pol_img REST0) as PI.
      aseg DI HKx. zstepA. zstepA. aleaf. intros moa Haga HKa Efsa Efdsa Hha.
      (* [comment removed for export] *)
      eapply (adi_free _ _ _ _ DI) with (lo := usp0 - 8388608) (A := OWN);
        [ apply KR_nil | exact HKa
        | destruct (Z.eqb_spec OWN 0) as [E0|NE0]; [left; exact E0| right; exists (mkABlock OWN PL); split; [subst REST0; left; reflexivity| reflexivity]]
        | rewrite unsigned_lit by lia; exact ST | aceil; lia
        | rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia | clear -SF; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia
        | rewrite unsigned_lit by lia; lia
        | reflexivity | apply (adi_uanchorC _ _ _ _ DI); [in_lits| rewrite unsigned_lit by lia; aceil; lia]
        | exact FRM | reflexivity
        | pose proof (adi_hd_reserve _ _ _ _ DI _ _ _ _ _ HD) as RS2; unfold afree_cost; destruct (OWN =? 0); lia
        | apply nbig_small; lia | ].
      intros w0 w1 w2 rb0 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F4 fc4 m4 mo4 s4 ST4 HPR4 FRM4 SOE4 HK4 REL4 FS4 FDS4 CR4.
      rewrite ?(unsigned_lit (usp0 + -208)) in ST4 by lia. rewrite ?(unsigned_lit (usp0 + -208)) in HPR4 by lia.
      replace (ret_pc (Z_to_bv 64 0x81e6c)) with (Z_to_bv 64 0x81e6c) by (symmetry; rpc).
      assert (CR1 : 1 <= p_acredit D s4).
      { pose proof (adi_hd_reserve _ _ _ _ DI _ _ _ _ _ HD) as RS2.
        assert (RF0 : 0 <= arefund_at (p_arefund D) OWN REST0).
        { unfold arefund_at. destruct (ab_find OWN REST0) as [b|]; [| lia]. pose proof (adi_charge _ _ _ _ DI (ab_size b)). lia. }
        unfold afree_cost in CR4. destruct (OWN =? 0); lia. }
      assert (INB : In (mkABlock A cap) (ab_remove OWN REST0)).
      { destruct (adi_blocks _ _ _ _ DI _ _ _ _ _ HKx) as (RNG & _ & ND).
        apply In_ab_remove; [subst REST0; apply in_or_app; right; left; reflexivity|]. cbn [ab_addr]. intros E. subst OWN.
        destruct (Z.eqb_spec A 0) as [EA|NA].
        - pose proof (RNG (mkABlock A cap) ltac:(subst REST0; apply in_or_app; right; left; reflexivity)) as R0. unfold ablock_range in R0. cbn [ab_addr] in R0. lia.
        - subst REST0. cbn [map ab_addr app] in ND.
          inversion ND as [|x l NI ND']; subst. apply NI. left. reflexivity. }
      pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK4) as MI4.
      assert (RB4 : RBASE m4) by (eapply (RBASE_heap_pres _ _ mm m4 (usp0 + -208)); [exact RB | exact HPR4 | lia | exact MI4 | exact ST4]).
      pose proof (aheap_pres_agree _ _ _ _ _ _ HPR4) as AG4.
      lazymatch type of TRF with rw_cells _ _ _ ?cs =>
        assert (TRF4 : rw_cells asegs m4 (usp0 + -208) cs) by (eapply rw_cells_agree; [exact AG4| exact TRF| intros ax Ha; left; cbn in Ha; lia]) end.
      assert (FR4 : FRAME' m4) by (unfold MFRAME; eapply rw_cells_agree; [exact AG4| exact FR| intros ax Ha; left; cbn in Ha; lia]).
      clear ST MI IMG AS. pose proof RB4 as (ST & MI & IMG & AS). unfold LO in ST.
      pose proof (PSTK (ab_remove OWN REST0)) as PS4. pose proof (pol_img (ab_remove OWN REST0)) as PI4.
      aseg DI HK4. zstepA. zstepA. zstepA. RET0A. do 10 zstepA. release_frame TRF4 ST (usp0 + -128). zstepA.
      replace (ret_pc (Z_to_bv 64 0x81c18)) with (Z_to_bv 64 0x81c18) by (symmetry; rpc).
      aleaf. intros mo5 Hag5 HK5 Efs5 Efds5 Hh5.
      apply (HRET 0 so s4 mo5); [lia|].
      exists (ab_remove OWN REST0), []. split; [exact FR4|].
      split. { split; [unfold LO; exact ST|]. split; [exact MI|]. split; [exact IMG| exact AS]. }
      split; [rewrite SOE4; exact SOE|]. split; [exact SOB|]. split; [exact HK5|]. split; [exact INB|].
      split; [pose proof (ab_remove_length OWN REST0); lia|].
      split; [rewrite Efs5, FS4, Efsa; exact FS|]. split; [exact FRM4| exact CR1].
    Qed.

    Let TPR_nil : forall n so, TPR n so [].
    Proof. intros; unfold TPR; apply ShapeAlg.t_emit_has_nil. Qed.
    Let CALLS : (1 <= calls <= 4)%nat.
    Proof. unfold calls. destruct (L =? 0); [lia|]. pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 FILE (Z_to_bv 8 0))) 4 ltac:(lia)). lia. Qed.

    (* [comment removed for export] *)
    Lemma az_tr_alloc : forall s mo mm fc (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (pad junk : list byte),
      0 < PL ->
      TRFRAME mm pad A L PL SB1 -> FRAME' mm -> RBASE mm -> SO s = stdout_init ->
      AHK s [mkABlock A cap] [] mm mo -> AHEAD hk [(A, cap)] H0 s mo -> (5 <= hk)%nat -> m_fs mo = FS0 ->
      rw_cells asegs mm A [CB (length FILE) FILE; CB (Z.to_nat (cap - Z.of_nat (length FILE))) junk] -> ablock_range ACONSTS A cap ->
      frm0 fc ->
      realizes_cfg acfg asegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 (Z_to_bv 64 PL) (Z_to_bv 64 (A + 6 + L))
                                          a0 a1 a2 a3 a4 a5 a6 a7
                                          (Z_to_bv 64 L) (Z_to_bv 64 (A + 2)) (Z_to_bv 64 0x5e01d0) (Z_to_bv 64 (Z.of_nat calls)) (Z_to_bv 64 RSTAGE) X7 S8 S9 S10 S11 t3 t4 t5 t6)
                                  F (Z_to_bv 64 0x81dd0) fc None mm (seg_rom asegs)) mo)
                (TPR calls stdout_init).
    Proof.
      intros s mo mm fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pad junk PLP TRF FR RB SO0 HKx HD HK5 FS BLK BR FRM.
      destruct hk as [|hk']; [lia|].
      pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
      pose proof RB as (ST & MI & IMG & AS). unfold LO in ST. unfold TRFRAME in TRF. unfold MFRAME in FR.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). aceil_in BR4. cbn [c_img_hi ACONSTS] in BR5.
      pose proof (PSTK [mkABlock A cap]) as PS. pose proof (pol_img [mkABlock A cap]) as PI.
      aseg DI HKx. zstepA. zstepA. aleaf. intros moa Haga HKa Efsa Efdsa Hha.
      pose proof (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ HD Haga) as HDa.
      (* [comment removed for export] *)
      eapply (adi_malloc _ _ _ _ DI) with (lo := usp0 - 8388608) (n := PL); try reflexivity.
      all: rewrite ?(unsigned_lit (usp0 + -208)) by lia.
      - apply TPR_nil.
      - exact HKa.
      - exact ST.
      - aceil; lia.
      - unfold AMALLOC_STACK. lia.
      - clear -SF. Z.div_mod_to_equations. lia.
      - lia.
      - apply (adi_uanchorC _ _ _ _ DI); [in_lits| rewrite unsigned_lit by lia; aceil; lia].
      - exact FRM.
      - lia.
      - eapply (adi_hd_cmalloc _ _ _ _ DI); [exact HDa | lia].
      - apply nbig_small; cbn [length]; lia.
      - (* [comment removed for export] *)
        intros v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 m2 mo2 s2 T ST2 HPR WM2 FRM2 SOE REL FS2 FDS2 CR2 EA0 BR' HK2 [junk' [JL NBLK]] BSH2.
        subst c0.
        rewrite ?(unsigned_lit (usp0 + -208)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -208)) in HPR by lia.
        replace (ret_pc (Z_to_bv 64 0x81dd8)) with (Z_to_bv 64 0x81dd8) by (symmetry; rpc).
        pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK2) as MI2.
        assert (RB2 : RBASE m2) by (eapply (RBASE_heap_pres _ _ mm m2 (usp0 + -208)); [exact RB | exact HPR | lia | exact MI2 | exact ST2]).
        pose proof (aheap_pres_agree _ _ _ _ _ _ HPR) as AG2.
        lazymatch type of TRF with rw_cells _ _ _ ?cs =>
          assert (TRF2 : rw_cells asegs m2 (usp0 + -208) cs) by (eapply rw_cells_agree; [exact AG2| exact TRF| intros ax Ha; left; cbn in Ha; lia]) end.
        assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply rw_cells_agree; [exact AG2| exact FR| intros ax Ha; left; cbn in Ha; lia]).
        assert (BLK2 : rw_cells asegs m2 A [CB (length FILE) FILE; CB (Z.to_nat (cap - Z.of_nat (length FILE))) junk]).
        { eapply rw_cells_agree; [exact AG2| exact BLK|]. intros ax Ha. right; left. exists (mkABlock A cap). split; [left; reflexivity|]. cbn [ab_addr ab_size cells_size csize Nat.add] in Ha |- *. lia. }
        clear ST MI IMG AS. pose proof RB2 as (ST & MI & IMG & AS). unfold LO in ST.
        pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). aceil_in BQ4. cbn [c_img_hi ACONSTS] in BQ5.
        destruct (adi_blocks _ _ _ _ DI _ _ _ _ _ HK2) as (_ & DISJ0 & ND).
        assert (NEQ : T <> A).
        { cbn [map ab_addr] in ND. inversion ND as [|x l NI ND']; subst. intros EQ. apply NI. rewrite EQ. left. reflexivity. }
        assert (DISJ : T + PL <= A \/ A + cap <= T).
        { pose proof (DISJ0 (mkABlock T PL) (mkABlock A cap) ltac:(left; reflexivity) ltac:(right; left; reflexivity) NEQ) as DD. cbn [ab_addr ab_size] in DD. exact DD. }
        (* [comment removed for export] *)
        pose proof BLK2 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length FILE) FILE] _)) in SRC. destruct SRC as [SRC _].
        pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
        rewrite <- (firstn_skipn (Z.to_nat (6 + L)) FILE) in SRCB. apply bytes_at_app in SRCB. destruct SRCB as [_ PAYB].
        rewrite length_firstn in PAYB. replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length FILE))) with (A + 6 + L) in PAYB by lia.
        assert (PLEN : Z.of_nat (length PAY) = PL) by (unfold PAY; rewrite length_skipn; lia).
        pose proof (adi_hd_malloc _ _ _ _ DI _ _ PL hk' [(A, cap)] H0 T _ _ HDa ltac:(lia) REL) as HD2.
        pose proof (PSTK [mkABlock T PL; mkABlock A cap]) as PS2. pose proof (pol_img [mkABlock T PL; mkABlock A cap]) as PI2.
        aseg DI HK2. zstepA. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
        zstepA. zstepA. zstepA. zstepA. aleaf. intros mo2a Hag2a HK2a Efs2a Efds2a Hh2a.
        eapply (adi_memcpy _ _ _ _ DI) with (lo := usp0 - 8388608) (bd := mkABlock T PL) (bsr := mkABlock A cap) (dst := T) (src := A + 6 + L) (n := PL) (bs := PAY);
          [ apply TPR_nil | exact HK2a | left; reflexivity | cbn [ab_addr]; lia | cbn [ab_addr ab_size]; lia
          | right; left; reflexivity | cbn [ab_addr]; lia | cbn [ab_addr ab_size]; lia | lia | lia | exact PAYB | exact PLEN | exact NBLK
          | rewrite unsigned_lit by lia; exact ST | aceil; lia
          | rewrite unsigned_lit by lia; unfold AICP_STACK; lia | reflexivity | exact FRM2 | reflexivity | reflexivity | reflexivity | ].
        intros w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F3 fc3 m3 mo3 s3 ST3 NB3 MUc WM3 FRM3 HK3 AS3 SO3 Efs3 Efds3 Hag3.
        rewrite ?(unsigned_lit (usp0 + -208)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -208)) in MUc by lia.
        replace (ret_pc (Z_to_bv 64 0x81dec)) with (Z_to_bv 64 0x81dec) by (symmetry; rpc).
        assert (WOKW : Forall RWOK [(usp0 - 8388608, usp0 + -208); (T, T + PL)]).
        { unfold RWOK, LO. aceil. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
        pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK3) as MI3.
        assert (RB3 : RBASE m3) by (eapply RBASE_munch; [exact RB2 | exact WOKW | exact MUc | exact WM3 | exact MI3 | unfold LO; exact ST3]).
        pose proof (agree_on_of_munch _ _ _ MUc WM3) as AG3.
        lazymatch type of TRF with rw_cells _ _ _ ?cs =>
          assert (TRF3 : rw_cells asegs m3 (usp0 + -208) cs) by (eapply rw_cells_agree; [exact AG3 | exact TRF2 | intros ax Ha; cbn in Ha |- *; lia]) end.
        assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply rw_cells_agree; [exact AG3 | exact FR2 | intros ax Ha; cbn in Ha |- *; lia]).
        pose proof (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ (adi_hd_aps _ _ _ _ DI _ _ _ _ _ _ (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ HD2 Hag2a) AS3) Hag3) as HD3.
        clear MUc WM3 AG3 ST MI IMG AS. pose proof RB3 as (ST & MI & IMG & AS). unfold LO in ST.
        pose proof (PSTK [mkABlock T PL; mkABlock A cap]) as PS3. pose proof (pol_img [mkABlock T PL; mkABlock A cap]) as PI3.
        aseg DI HK3. zstepA. zstepA. zstepA. zstepA. aleaf. intros mo4 Hag4 HK4 Efs4 Efds4 Hh4.
        unfold TPR.
        eapply (az_run_loop T PL T A L SB1 PAY pad [mkABlock T PL; mkABlock A cap] (fun so => KR 0 so) (fun so => KR_nil 0 so) ltac:(cbn [length]; lia)) with (s := s3).
        + intros n' so s' mo' m' fc' x1' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 s3' u3 u4 u5 u6 F' RI'.
          eapply (az_tr_tail T T pad _); [| lia | exact RI']. replace (T =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
        + exact CALLS.
        + exists (EvMalloc PL (Some T) :: H0). cbn [app map ab_addr ab_size].
          split; [unfold count_yfuzz; cbn [List.filter]; fold (count_yfuzz H0) ; first [rewrite (count_yfuzz_hist H0 HH0); lia | pose proof (count_yfuzz_hist H0 HH0) as CY; unfold count_yfuzz in CY; lia]|].
          split; [exact TRF3|]. split; [exact FR3|]. split; [exact RB3|]. split; [rewrite SO3, SOE; exact SO0|].
          split; [unfold zlength, STDOUT_BUFSIZ; cbn; lia|]. split; [exact HK4|].
          split; [eapply hd_weaken_le; [eapply (adi_hd_magree _ _ _ _ DI); [exact HD3| exact Hag4] | lia]|].
          split; [rewrite Efs4, Efs3, Efs2a, FS2, Efsa; exact FS|].
          split; [pose proof (rw_cells_bytes_at _ _ _ _ NB3) as X; cbn [cells_bytes cbytes app] in X; rewrite app_nil_r in X; exact X|].
          split; [lia|]. split; [lia|]. split; [exact PLEN|]. split; [lia|].
          split; [left; exists (mkABlock T PL); split; [left; reflexivity| cbn [ab_addr ab_size]; lia]| exact FRM3].
    Qed.

    (* [comment removed for export] *)
    Lemma az_tr_empty : forall s mo mm fc (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (pad : list byte),
      PL = 0 ->
      TRFRAME mm pad A L PL SB1 -> FRAME' mm -> RBASE mm -> SO s = stdout_init ->
      AHK s [mkABlock A cap] [] mm mo -> AHEAD hk [(A, cap)] H0 s mo -> (5 <= hk)%nat -> m_fs mo = FS0 -> frm0 fc ->
      realizes_cfg acfg asegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 (Z_to_bv 64 PL) (Z_to_bv 64 (A + 6 + L))
                                          a0 a1 a2 a3 a4 a5 a6 a7
                                          (Z_to_bv 64 L) (Z_to_bv 64 (A + 2)) (Z_to_bv 64 0x5e01d0) (Z_to_bv 64 (Z.of_nat calls)) (Z_to_bv 64 RSTAGE) X7 S8 S9 S10 S11 t3 t4 t5 t6)
                                  F (Z_to_bv 64 0x81e1c) fc None mm (seg_rom asegs)) mo)
                (TPR calls stdout_init).
    Proof.
      intros s mo mm fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pad PL0 TRF FR RB SO0 HKx HD HK5 FS FRM.
      pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
      pose proof RB as (ST & MI & IMG & AS). unfold LO in ST.
      assert (PAY0 : PAY = []) by (unfold PAY; apply skipn_all2; lia).
      pose proof (PSTK [mkABlock A cap]) as PS. pose proof (pol_img [mkABlock A cap]) as PI.
      aseg DI HKx. zstepA. zstepA. zstepA. zstepA. aleaf. intros moa Haga HKa Efsa Efdsa Hha.
      unfold TPR. rewrite PL0.
      eapply (az_run_loop Y_EMPTY 0 0 A L SB1 [] pad [mkABlock A cap] (fun so => KR 0 so) (fun so => KR_nil 0 so) ltac:(cbn [length]; lia)) with (s := s).
      - intros n' so s' mo' m' fc' x1' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 s3' u3 u4 u5 u6 F' RI'.
        pose proof (az_tr_tail Y_EMPTY 0 pad _ eq_refl ltac:(lia) n' so s' mo' m' fc' x1' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 s3' u3 u4 u5 u6 F') as TT.
        rewrite PL0, PAY0 in TT. exact (TT RI').
      - exact CALLS.
      - exists H0. cbn [app map ab_addr ab_size]. rewrite PL0 in TRF.
        split; [pose proof (count_yfuzz_hist H0 HH0) as CY; lia|].
        split; [exact TRF|]. split; [exact FR|]. split; [exact RB|]. split; [exact SO0|].
        split; [unfold zlength, STDOUT_BUFSIZ; cbn; lia|]. split; [exact HKa|].
        split; [eapply hd_weaken_le; [eapply (adi_hd_magree _ _ _ _ DI); [exact HD| exact Haga] | lia]|].
        split; [rewrite Efsa; exact FS|]. split; [apply bytes_at_nil; unfold Y_EMPTY; lia|].
        split; [unfold Y_EMPTY; lia|]. split; [unfold Y_EMPTY; lia|]. split; [reflexivity|]. split; [lia|].
        split; [right; split; reflexivity| exact FRM].
    Qed.

    (* [comment removed for export] *)
    Lemma az_target_run : forall s mo (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (junk : list byte),
      FRAME' mm -> ABASE' mm -> AHK s [mkABlock A cap] [] mm mo -> AHEAD hk [(A, cap)] H0 s mo -> (5 <= hk)%nat -> SO s = stdout_init -> m_fs mo = FS0 ->
      rw_cells asegs mm A [CB (length FILE) FILE; CB (Z.to_nat (cap - Z.of_nat (length FILE))) junk] -> ablock_range ACONSTS A cap ->
      frm0 fc ->
      realizes_cfg acfg asegs (mkCfg (MS (mkR (Z_to_bv 64 0x81c18) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A)
                                          (Z_to_bv 64 (A + 2)) (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) a4 a5 a6 a7
                                          (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 SB1) (Z_to_bv 64 RSTAGE) X7 S8 S9 S10 S11 t3 t4 t5 t6)
                                  F (Z_to_bv 64 0x81d74) fc None mm (seg_rom asegs)) mo)
                (TPR calls stdout_init).
    Proof.
      intros s mo t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc mm junk FR BA HKx HD HK5 SO0 FS BLK BR FRM.
      pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL.
      pose proof BA as (ST & MI & IMG & (G & E & (reg & p3 & p4 & FJ & AJ & ATC & INI & FLG))). unfold LO in ST. pose proof FR as FR0. unfold MFRAME in FR.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). aceil_in BR4. cbn [c_img_hi ACONSTS] in BR5.
      pose proof BLK as BLKF. apply (proj1 (rw_cells_app _ _ _ [CB (length FILE) FILE] _)) in BLKF. destruct BLKF as [BLKF _].
      apply rw_cells_bytes_at in BLKF. cbn [cells_bytes cbytes app] in BLKF. rewrite app_nil_r in BLKF.
      pose proof (PSTK [mkABlock A cap]) as PS. pose proof (pol_img [mkABlock A cap]) as PI.
      pose proof (pol_blk [mkABlock A cap] (mkABlock A cap)) as PB. cbn [ab_addr ab_size] in PB. specialize (fun a n => PB a n (or_introl eq_refl) BR).
      (* [comment removed for export] *)
      assert (BODY : forall mm1 mo1,
        magree mo mo1 -> AHK s [mkABlock A cap] [] mm1 mo1 ->
        (exists pad, TRFRAME mm1 pad A L PL SB1) -> FRAME' mm1 -> RBASE mm1 ->
        rw_cells asegs mm1 A [CB (length FILE) FILE; CB (Z.to_nat (cap - Z.of_nat (length FILE))) junk] ->
        forall (x1 v0 v1 v2 u0 u1 u2 u3 u4 u5 u6 u7 v3 v4 v5 v6 : word),
        realizes_cfg acfg asegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv v0 v1 v2 (Z_to_bv 64 PL) (Z_to_bv 64 (A + 6 + L))
                                            u0 u1 u2 u3 u4 u5 u6 u7
                                            (Z_to_bv 64 L) (Z_to_bv 64 (A + 2)) (Z_to_bv 64 0x5e01d0) (Z_to_bv 64 SB1) (Z_to_bv 64 RSTAGE) X7 S8 S9 S10 S11 v3 v4 v5 v6)
                                    F (Z_to_bv 64 0x81dbc) fc None mm1 (seg_rom asegs)) mo1)
                  (TPR calls stdout_init)).
      { intros mm1 mo1 Hag1 HK1 TRF1 FR1 RB1 BLK1 x1 v0 v1 v2 u0 u1 u2 u3 u4 u5 u6 u7 v3 v4 v5 v6.
        destruct TRF1 as [pad TRF1].
        pose proof (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ HD Hag1) as HD1.
        assert (FS1 : m_fs mo1 = FS0) by (rewrite (proj1 (proj2 (proj2 (proj2 (magree_frame _ _ Hag1))))); exact FS).
        pose proof RB1 as (ST1 & MI1 & IMG1 & AS1). unfold LO in ST1.
        pose proof BLK1 as BLKF1. apply (proj1 (rw_cells_app _ _ _ [CB (length FILE) FILE] _)) in BLKF1. destruct BLKF1 as [BLKF1 _].
        apply rw_cells_bytes_at in BLKF1. cbn [cells_bytes cbytes app] in BLKF1. rewrite app_nil_r in BLKF1.
        aseg DI HK1.
        zstepA. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstepA. zstepA. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
          + aleaf. intros mo2 Hag2 HK2 Efs2 Efds2 Hh2.
            replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat calls)) by (unfold calls; rewrite (proj2 (Z.eqb_eq L 0) K2); reflexivity).
            eapply az_tr_alloc; try eassumption. all: first [lia | eapply (adi_hd_magree _ _ _ _ DI); [exact HD1| exact Hag2] | rewrite Efs2; exact FS1].
          + aleaf. intros mo2 Hag2 HK2 Efs2 Efds2 Hh2.
            replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat calls)) by (unfold calls; rewrite (proj2 (Z.eqb_eq L 0) K2); reflexivity).
            eapply az_tr_empty; try eassumption. all: first [lia | eapply (adi_hd_magree _ _ _ _ DI); [exact HD1| exact Hag2] | rewrite Efs2; exact FS1].
        - (* [comment removed for export] *)
          assert (E2 : exists d2, nth_error FILE 2 = Some d2).
          { destruct (nth_error FILE 2) as [d2|] eqn:EE; [exists d2; reflexivity|]. apply nth_error_None in EE. exfalso. lia. }
          destruct E2 as [d2 E2]. pose proof (byte_range d2) as Rd2.
          pose proof (u8ro_read asegs mm1 _ _ 2 d2 (wa (A + 2)) BLKF1 E2 ltac:(lia) eq_refl) as R2.
          zstepA. clear R2. cbv beta. zstepA. zstepA.
          replace (Z.land (bv_unsigned d2) 3 + 1) with (Z.of_nat calls).
          2:{ unfold calls. replace (L =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
              rewrite (nth_error_nth FILE 2%nat (Z_to_bv 8 0) E2).
              change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. lia. }
          zstepA. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
          + aleaf. intros mo2 Hag2 HK2 Efs2 Efds2 Hh2.
            eapply az_tr_empty; try eassumption. all: first [lia | eapply (adi_hd_magree _ _ _ _ DI); [exact HD1| exact Hag2] | rewrite Efs2; exact FS1].
          + aleaf. intros mo2 Hag2 HK2 Efs2 Efds2 Hh2.
            eapply az_tr_alloc; try eassumption. all: first [lia | eapply (adi_hd_magree _ _ _ _ DI); [exact HD1| exact Hag2] | rewrite Efs2; exact FS1]. }
      (* [comment removed for export] *)
      pose proof (conj BLK I) as BLKK. pose proof (conj BLKF I) as BLKFK. clear BLK BLKF.
      destruct (adx_libc_head _ _ _ DIx _ _ _ _ _ HKx) as (cdt & thr & sec & tm1 & LCH).
      unfold atx_cells in ATC. change (AATXFLAG + 4) with 0x5e01d4 in FLG. change AATXFLAG with 0x5e01d0 in INI.
      (* [comment removed for export] *)
      aseg DI HKx.
      pose proof (munch_refl [(usp0 - 256, usp0 - 128); (0x5e01d0, 0x5e01d1); (0x600b60, 0x600b60 + 544)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
      assert (OUT : forall a, (usp0 - 128 <= a \/ (0x10000 <= a < 0x603000 /\ a <> 0x5e01d0 /\ ~ (0x600b60 <= a < 0x600d80)) \/ (a < usp0 - 256 /\ (a < 0x10000 \/ 0x603000 <= a))) ->
                       (fun a0 : Z => outside [(usp0 - 256, usp0 - 128); (0x5e01d0, 0x5e01d1); (0x600b60, 0x600b60 + 544)] a0) a) by (intros a Ha; cbn; lia).
      assert (WOKW : forall LB, Forall (aclient_write_ok ACONSTS LB) [(usp0 - 256, usp0 - 128); (0x5e01d0, 0x5e01d1); (0x600b60, 0x600b60 + 544)]).
      { intros LB. constructor; [apply wok_stack; aceil; lia|]. constructor; [apply wok_init|]. constructor; [apply wok_atx| constructor]. }
      zstepA. carve_frame 80%nat ST.
      do 9 zstepA. do 5 zstepA.
      destruct reg; cbv iota in ATC, INI.
      - (* [comment removed for export] *)
        zstepA. zstepA. zstepA. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; vm_compute in K0; first [discriminate K0 | lia]|]. clear K0.
        aleaf. intros mo1 Hag1 HK1 Efs1 Efds1 Hh1.
        lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => set (mf1 := mx) in * end.
        lazymatch goal with HH : munch _ mm mf1 |- _ => rename HH into MU1 end.
        lazymatch goal with HH : wmono _ mm mf1 |- _ => rename HH into WM1 end.
        lazymatch goal with HH : stk _ mf1 _ _ |- _ => rename HH into ST1 end.
        lazymatch goal with HH : mem_inv _ mf1 |- _ => rename HH into MI1 end.
        lazymatch goal with HH : rw_cells _ mf1 (usp0 + -208) _ |- _ => rename HH into TRF1 end.
        pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
        assert (HK1' : AHK s [mkABlock A cap] [] mf1 mo1) by (eapply (AHK_after D DI); [exact HK1| exact MU1| exact WM1| apply WOKW]).
        eapply BODY; [exact Hag1| exact HK1'| eexists; unfold TRFRAME; exact TRF1| | |].
        + unfold MFRAME. eapply rw_cells_agree; [exact AG1| exact FR0| intros ax Ha; apply OUT; cbn in Ha; lia].
        + split; [unfold LO; exact ST1|]. split; [exact MI1|]. split.
          * eapply AIMG_agree; [exact AG1| intros a Ha; apply OUT; lia| exact IMG].
          * split; [| split]; [ first [exact G | eapply rw_cells_agree; [exact AG1| exact G| intros a Ha; apply OUT; cbn in Ha; lia]]
                               | first [exact E | eapply rw_cells_agree; [exact AG1| exact E| intros a Ha; apply OUT; cbn in Ha; lia]] |].
            exists true, p3, p4, FJ, AJ. split; [unfold atx_cells; exact ATC|]. split; [exact INI| exact FLG].
        + eapply rw_cells_agree; [exact AG1| exact (proj1 BLKK)| intros ax Ha; apply OUT; cbn [cells_size csize Nat.add] in Ha; lia].
      - (* [comment removed for export] *)
        zstepA. zstepA. zstepA. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
        zstepA. zstA. zstepA. zstepA. zstepA.
        call_spA (aatexit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 8388608) p3 p4 FJ AJ cdt thr sec tm1 (adrv_acc ACONSTS [mkABlock A cap]));
          [ intros a k H1 H2; apply PS; lia | exact PI | exact ST | aceil; lia | lia | exact MI | unfold atx_cells; exact ATC | exact LCH | reflexivity
          | vm_compute; reflexivity | ].
        zstepA. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. clear K1.
        zstepA. zstepA. zstepA. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. clear K1.
        aleaf. intros mo1 Hag1 HK1 Efs1 Efds1 Hh1.
        lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => set (mf1 := mx) in * end.
        lazymatch goal with HH : munch _ mm mf1 |- _ => rename HH into MU1 end.
        lazymatch goal with HH : wmono _ mm mf1 |- _ => rename HH into WM1 end.
        lazymatch goal with HH : stk _ mf1 _ _ |- _ => rename HH into ST1 end.
        lazymatch goal with HH : mem_inv _ mf1 |- _ => rename HH into MI1 end.
        lazymatch goal with HH : rw_cells _ mf1 (usp0 + -208) _ |- _ => rename HH into TRF1 end.
        lazymatch goal with HH : rw_cells _ mf1 0x5e01d0 _ |- _ => rename HH into INI1 end.
        lazymatch goal with HH : rw_cells _ mf1 0x5e01d4 _ |- _ => rename HH into FLG1 end.
        lazymatch goal with HH : rw_cells _ mf1 0x600b60 _ |- _ => rename HH into ATC1 end.
        pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
        assert (HK1' : AHK s [mkABlock A cap] [] mf1 mo1) by (eapply (AHK_after D DI); [exact HK1| exact MU1| exact WM1| apply WOKW]).
        eapply BODY; [exact Hag1| exact HK1'| eexists; unfold TRFRAME; exact TRF1| | |].
        + unfold MFRAME. eapply rw_cells_agree; [exact AG1| exact FR0| intros ax Ha; apply OUT; cbn in Ha; lia].
        + split; [unfold LO; exact ST1|]. split; [exact MI1|]. split.
          * eapply AIMG_agree; [exact AG1| intros a Ha; apply OUT; lia| exact IMG].
          * split; [| split]; [ first [exact G | eapply rw_cells_agree; [exact AG1| exact G| intros a Ha; apply OUT; cbn in Ha; lia]]
                               | first [exact E | eapply rw_cells_agree; [exact AG1| exact E| intros a Ha; apply OUT; cbn in Ha; lia]] |].
            eexists true, _, _, _, _. split; [exact ATC1|]. split; [exact INI1| exact FLG1].
        + eapply rw_cells_agree; [exact AG1| exact (proj1 BLKK)| intros ax Ha; apply OUT; cbn [cells_size csize Nat.add] in Ha; lia].
    Qed.
  End TargetRun.
End RUN.
End RC__1.

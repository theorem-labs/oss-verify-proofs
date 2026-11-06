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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep ITree ITreeCfg Nodes NodesCfg Decode Arr FP InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg TrzNodesCfg TrzStdioCfg TrzLeafCfg ImplSplitCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim STree Malloc Monad StdioBase Stdio FmtFp Driver RawAlloc MSafe MLive.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface U_StartupLib U_Startup U_Exit UF_pad.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RF_stdio_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UStdio_iface UF_printf_iface UStdio_init UF_syscalls UF_memcpy UF_fwritex_gen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UDrv_iface UDrv_ctx UDrv_kio UDrv_A.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import MSuccIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
Definition held (P : Prop) : Prop := P.
(* [comment removed for export] *)
Ltac fix_lit_store_r :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac zst2r := zstep; fix_lit_store_r.

(* [comment removed for export] *)
Definition YFUZZ_PC : Z := 0x139a0.
Definition YDEPTH : Z := 8736.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition Y_EMPTY : Z := 0x355b0.

(* [comment removed for export] *)
Section RC__0.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition yfuzz_rz_stmt (HK : HK_T) : Prop :=
  forall (REST : list block) (T : Z) (txt : list byte) (lo B : Z) (errv : word) (K : TSet)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] -> HK s REST m mo -> YST m ->
  bytes_at usegs m T txt -> 0 < T -> T + Z.of_nat (length txt) < 2^62 -> Z.of_nat (length txt) < 2^26 ->
  ((exists bt, In bt REST /\ blk_addr bt <= T /\ T + Z.of_nat (length txt) <= blk_addr bt + blk_size bt) \/ length txt = 0%nat) ->
  Z.of_nat (length REST) + 8 <= NHELDc ->   (* [comment removed for export] *)
  rauxv_ok m B -> bv_unsigned sp <= B -> stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - YDEPTH ->
  bv_unsigned sp mod 16 = 0 ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = wz RATP ->
  a0 = wz T -> a1 = wz (Z.of_nat (length txt)) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (F' : bvmap 5 word) (LK : list block) (errv' : word),
     mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) -> rw_cells usegs m' (errno_addr tp) [C4 errv'] -> rauxv_ok m' B ->
     rheap_pres REST (bv_unsigned sp) m m' -> a0' = wz 0 -> HK s' (LK ++ REST) m' mo' -> LK = [] -> YST m' ->
     (forall k : reg, reg_get F' k = reg_get F k) -> m_fs mo' = m_fs mo ->
     realizes_cfg acfg usegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc None m' (seg_rom usegs)) mo') K) ->
  realizes_cfg acfg usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz YFUZZ_PC) fc None m (seg_rom usegs)) mo) K.
End RC__0.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

(* [comment removed for export] *)
Fixpoint emits (n : nat) (so : stdout_st) : list Z * stdout_st :=
  match n with
  | O => ([], so)
  | S k => let e1 := vprintf_pure so (pieces_emit_d 0) in
           let e2 := emits k (snd e1) in
           (fst e1 ++ fst e2, snd e2)
  end.

Section RUN.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (PAD : list byte) (S4 S5 S6 S7 X7 S8 S9 S10 S11 : word).   (* [comment removed for export] *)
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.          (* [comment removed for export] *)
  Hypothesis RCS : rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))).   (* [comment removed for export] *)
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Variable HKG : HKG_T.
  Hypothesis DI : drv_iface HKG.
  Variable FS0 : Fs.Fs.
  Notation HK := (HKG (G_fs FS0)).

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).

  Let DIR := di_run HKG DI.
  Hypothesis YF : yfuzz_rz_stmt HK.

  (* [comment removed for export] *)
  Definition TRFRAME (mm : mem) (pad : list byte) (A L PL SB1 : Z) : Prop :=
    rw_cells usegs mm (usp0 + -208)
      [CB 8 pad; C8 X7; C8 (Z_to_bv 64 RSTAGE); C8 (Z_to_bv 64 SB1); C8 (Z_to_bv 64 PL); C8 (Z_to_bv 64 (A + 6 + L)); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 2)); C8 (Z_to_bv 64 0x13674)].

  (* [comment removed for export] *)
  Definition RBASE (mm : mem) : Prop :=
    stk usegs mm LO' (usp0 + -208) /\ mem_inv usegs mm /\ RSTAT TID mm /\ rauxv_ok mm usp0 /\ bytes_at usegs mm usp0 IMGB
    /\ stderr_wfile0 mm /\ YST mm.

  Lemma RBASE_heap_pres : forall LB m m' SP, RBASE m -> rheap_pres LB SP m m' -> SP <= usp0 + -208 ->
    mem_inv usegs m' -> stk usegs m' LO' (usp0 + -208) -> rauxv_ok m' usp0 -> RBASE m'.
  Proof.
    intros LB m m' SP (ST & MI & RS & AUX & IMG & SE & YS) HP HSP MI' ST' AUX'. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    assert (HP' : rheap_pres LB (usp0 + -208) m m') by (eapply rheap_pres_weaken; [exact HP | lia | auto]).
    split; [exact ST'|]. split; [exact MI'|]. split; [eapply RSTAT_heap_pres; [exact HP'| exact RS]|]. split; [exact AUX'|].
    split; [eapply rheap_pres_bytes_at; [exact HP'| exact IMG| left; lia]|].
    split; [eapply stderr_wfile0_heap_pres; [exact HP'| exact SE]|].
    eapply (YST_agree _ _ _ (rheap_pres_agree _ _ _ _ HP')); [| exact YS]. intros a Ha. right; left.
    unfold ytr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma RBASE_reflag : forall (P : Z -> Prop) m m', RBASE m -> agree_on P m m' ->
    (forall a, (usp0 <= a \/ (0x24000 <= a < 0x57000 /\ ~ ralloc_static a)) -> a <> 0x355a4 -> P a) ->
    mem_inv usegs m' -> stk usegs m' LO' (usp0 + -208) -> rauxv_ok m' usp0 -> rw_cells usegs m' 0x355a4 [C1 (Z_to_bv 8 0)] -> RBASE m'.
  Proof.
    intros P m m' (ST & MI & RS & AUX & IMG & SE & YS) AG HP MI' ST' AUX' FL. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL.
    assert (STA : forall a, 0x24000 <= a < 0x57000 -> ~ ralloc_static a -> a <> 0x355a4 -> P a) by (intros a H1 H2 H3; apply HP; [right; split; assumption| exact H3]).
    split; [exact ST'|]. split; [exact MI'|].
    split. { eapply (RSTAT_reflag TID _ _ _ AG); [| exact FL| exact RS]. intros a Ha NE. apply STA; [| | exact NE];
             unfold rstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *; lia. }
    split; [exact AUX'|].
    split. { eapply bytes_at_agree; [exact AG| exact IMG|]. intros a Ha. apply HP; [left; lia| lia]. }
    split. { eapply (stderr_wfile0_agree _ _ _ AG); [| exact SE]. intros a Ha. apply STA;
             unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *; lia. }
    eapply (YST_agree _ _ _ AG); [| exact YS]. intros a Ha. apply STA;
      unfold ytr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *; lia.
  Qed.

  (* [comment removed for export] *)
  Definition RWOK (iv : Z * Z) : Prop :=
    (LO' <= fst iv /\ snd iv <= usp0 + -208) \/ (fst iv = RERRNO /\ snd iv = RERRNO + 4)
    \/ (fst iv = 0x25458 /\ snd iv = 0x25458 + 232) \/ (fst iv = 0x55d78 /\ snd iv = 0x55d78 + 1024)
    \/ (snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x57000 <= fst iv)).

  Lemma RWOK_outside : forall W a, Forall RWOK W ->
    (usp0 + -208 <= a \/ (0x10000 <= a < 0x57000 /\ ~ (RERRNO <= a < RERRNO + 4) /\ ~ stdout_addr a)) -> outside W a.
  Proof.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold RWOK, LO, RERRNO, alloc_ceiling, stdout_addr in H1 |- *. cbn [fst snd] in H1. unfold RERRNO, stdout_addr in Ha. lia.
  Qed.

  (* [comment removed for export] *)

  Lemma RBASE_munch : forall W m m', RBASE m -> Forall RWOK W -> munch W m m' -> wmono usegs m m' ->
    mem_inv usegs m' -> stk usegs m' LO' (usp0 + -208) -> RBASE m'.
  Proof.
    intros W m m' (ST & MI & RS & AUX & IMG & SE & YS) HW MU WM MI' ST'. pose proof (sp_facts sp0 VSP RCSP) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|].
    split; [eapply RSTAT_munch; [exact MU| exact WM| intros a Ha; apply RWOK_outside; [exact HW| unfold rstat_addr, RERRNO, stdout_addr in *; lia]| exact RS]|].
    split.
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      eapply Forall_impl; [| exact HW]. intros [lo1 hi1] H. unfold RWOK, RERRNO, RAUXV_CELL, RLIBC, LO, alloc_ceiling in *. cbn [fst snd] in *. lia. }
    split.
    { eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact IMG|]. intros a Ha. cbn. apply RWOK_outside; [exact HW| left; lia]. }
    split.
    { eapply stderr_wfile0_munch; [exact MU| exact WM| | exact SE]. intros a Ha. apply RWOK_outside; [exact HW| unfold stderr_addr, RERRNO, stdout_addr in *; lia]. }
    eapply (YST_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)); [| exact YS]. intros a Ha. cbn. apply RWOK_outside; [exact HW| unfold ytr_addr, RERRNO, stdout_addr in *; lia].
  Qed.

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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Loop.
    (* [comment removed for export] *)
    Variables (T PL OWN A L SB1 : Z) (PAY : list byte) (pad : list byte) (REST0 : list block) (bufp : bptr) (cap : Z).
    (* [comment removed for export] *)
    Variable KEND : stdout_st -> TSet.
    Hypothesis KEND_nil : forall so, KEND so [].

    Definition RUNINV (so : stdout_st) (s : PState) (mo : Model) (mm : mem) (fc : bv 32) : Prop :=
      exists (LK : list block) (errv : word),
        TRFRAME mm pad A L PL SB1 /\ FRAME' mm /\ RBASE mm /\ stdout_file mm so /\ zlength (so_buf so) <= STDOUT_BUFSIZ
        /\ HK s (LK ++ REST0) mm mo /\ Z.of_nat (length (LK ++ REST0)) + 8 <= NHELDc /\ m_fs mo = FS0
        /\ bytes_at usegs mm T PAY /\ 0 < T /\ T + PL < 2^62 /\ Z.of_nat (length PAY) = PL /\ PL < 2^26
        /\ ((exists bt, In bt REST0 /\ blk_addr bt <= T /\ T + PL <= blk_addr bt + blk_size bt) \/ PL = 0)
        /\ rw_cells usegs mm RERRNO [C4 errv] /\ frm0 fc.

    Hypothesis HEND : forall so s mo mm fc (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 : word) (F : bvmap 5 word),
      RUNINV so s mo mm fc ->
      realizes_cfg acfg usegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 (Z_to_bv 64 PL) (Z_to_bv 64 T) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 OWN) s3v (Z_to_bv 64 0x355a0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x138c0) fc None mm (seg_rom usegs)) mo)
               (KEND so).

    Lemma rz_run_loop : forall (n : nat) so s mo mm fc (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 : word) (F : bvmap 5 word),
      (1 <= n <= 4)%nat ->
      RUNINV so s mo mm fc ->
      realizes_cfg acfg usegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 (Z_to_bv 64 PL) (Z_to_bv 64 T) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 OWN) s3v (Z_to_bv 64 0x355a0) (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x13888) fc None mm (seg_rom usegs)) mo)
               (ShapeAlg.t_emit (Wz 1 (fst (emits n so))) (KEND (snd (emits n so)))).
    Proof.
      induction n as [|n IH]; intros so s mo mm fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 F Hn RI; [lia|].
      destruct RI as (LK & errv & TRF & FR & RB & SOF & SOB & HKx & NBLK & FS & PAYB & T0 & T62 & PLEN & PL26 & PBLK & ERR & FRM).
      pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
      pose proof RB as (ST & MI & RS & AUX & IMG & SE & YS). unfold LO in ST. unfold RERRNO in ERR.
      destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
      destruct (di_blocks HKG DI _ _ _ _ _ HKx) as (RNG & _ & _).
      (* [comment removed for export] *)
      assert (PAYOFF : forall a, T <= a < T + Z.of_nat (length PAY) -> in_block (LK ++ REST0) a /\ (a < 0x10000 \/ 0x57000 <= a)).
      { intros a Ha. destruct PBLK as [(bt & Hin & Hb1 & Hb2)| Z0]; [| lia].
        pose proof (RNG bt ltac:(apply in_or_app; right; exact Hin)) as BR. unfold rblock_range, alloc_ceiling in BR.
        split; [exists bt; split; [apply in_or_app; right; exact Hin| lia] | lia]. }
      (* [comment removed for export] *)
      pose proof (RSTAT_flag TID _ RS) as FLG.
      assert (PAYK : held (bytes_at usegs mm T PAY)) by exact PAYB. clear PAYB.
      assert (IMGK : held (bytes_at usegs mm usp0 IMGB)) by exact IMG. clear IMG.
      pose proof (munch_refl [(0x355a4, 0x355a4 + 1)] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
      rz_seg Hh Hl. zstep. zst2r. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m1 := mx) in * end.
      lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into ST1 end.
      lazymatch goal with H : mem_inv _ m1 |- _ => rename H into MI1 end.
      lazymatch goal with H : munch _ mm m1 |- _ => rename H into MU1 end.
      lazymatch goal with H : wmono _ mm m1 |- _ => rename H into WM1 end.
      lazymatch goal with H : rw_cells _ m1 0x355a4 _ |- _ => rename H into FLG1 end.
      lazymatch goal with H : rw_cells _ m1 0x355fc _ |- _ => rename H into ERR1 end.
      pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
      assert (OUT1 : forall a, a <> 0x355a4 -> (fun a0 : Z => outside [(0x355a4, 0x355a4 + 1)] a0) a) by (intros a Ha; cbn; lia).
      assert (FLOK : Forall (rclient_write_ok (LK ++ REST0)) [(0x355a4, 0x355a4 + 1)]).
      { constructor; [| constructor]. right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
      assert (FLAUX : Forall (fun iv : Z * Z => snd iv <= usp0 /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) [(0x355a4, 0x355a4 + 1)]).
      { constructor; [| constructor]. cbn [fst snd]. unfold RAUXV_CELL, RLIBC. lia. }
      assert (HK1 : HK s (LK ++ REST0) m1 mo) by (eapply (di_frame HKG DI); [exact HKx| exact MU1| exact WM1| exact FLOK]).
      assert (YS1 : YST m1) by (eapply (YST_agree _ _ _ AG1); [intros a Ha; apply OUT1; unfold ytr_addr in Ha; lia| exact YS]).
      assert (AUX1 : rauxv_ok m1 usp0) by (eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1| exact FLAUX]).
      assert (PAYB1 : bytes_at usegs m1 T PAY).
      { eapply bytes_at_agree; [exact AG1 | exact PAYK |]. intros a Ha. apply OUT1. destruct (PAYOFF a Ha) as [_ OFF]. lia. }
      apply evt_done.
      (* [comment removed for export] *)
      eapply (YF (LK ++ REST0) T PAY (usp0 - 8388608) usp0 errv) ; try reflexivity.
      all: unfold RATP; rewrite ?(unsigned_lit 0x356a0) by lia; rewrite ?(unsigned_lit (usp0 + -208)) by lia.
      - apply ShapeAlg.t_emit_has_nil.
      - exact HK1.
      - exact YS1.
      - exact PAYB1.
      - lia.
      - lia.
      - lia.
      - destruct PBLK as [(bt & Hin & Hb1 & Hb2)| ->]; [left; exists bt; split; [apply in_or_app; right; exact Hin| lia] | right; lia].
      - exact NBLK.
      - exact AUX1.
      - lia.
      - exact ST1.
      - lia.
      - unfold YDEPTH. lia.
      - clear - SF. Z.div_mod_to_equations. lia.
      - exact ERR1.
      - exact MI1.
      - unfold wz. f_equal. lia.
      - intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 mo2 s2 F2 LK2 errv2 MI2 ST2 ERR2 AUX2 HPR -> HK2 -> YS2 FEQ FS2. cbn [app] in HK2.
        replace (ret_pc (Z_to_bv 64 0x1389c)) with (Z_to_bv 64 0x1389c) by (symmetry; rpc).
        assert (FLG2 : rw_cells usegs m2 0x355a4 [C1 (Z_to_bv 8 1)]).
        { eapply rheap_pres_rw_cells; [exact HPR| exact FLG1|]. right; left. cbn. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
        unfold RATP in ERR2. rewrite ?(unsigned_lit 0x356a0) in ERR2 by lia. cbn in ERR2.
        clear ST1 MI1 ERR1 FLG1.
        (* [comment removed for export] *)
        destruct (DIR _ _ _ _ _ HK2) as (Hmi2 & Hh2 & Hl2).
        pose proof (munch_refl [(0x355a4, 0x355a4 + 1)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
        rz_seg Hh2 Hl2. unfold wz. zstep. zst2r.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m3 := mx) in * end.
        lazymatch goal with H : stk _ m3 _ _ |- _ => rename H into ST3 end.
        lazymatch goal with H : mem_inv _ m3 |- _ => rename H into MI3 end.
        lazymatch goal with H : munch _ m2 m3 |- _ => rename H into MU3 end.
        lazymatch goal with H : wmono _ m2 m3 |- _ => rename H into WM3 end.
        lazymatch goal with H : rw_cells _ m3 0x355a4 _ |- _ => rename H into FLG3 end.
        rename ERR2 into ERR3.
        (* [comment removed for export] *)
        pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
        assert (AG : agree_on (fun a => rclient_addr (LK ++ REST0) (usp0 + -208) a /\ a <> 0x355a4) mm m3).
        { eapply agree_on_trans; [eapply agree_on_trans|].
          - eapply agree_on_mono; [exact AG1|]. intros a [_ Ha]. apply OUT1. exact Ha.
          - eapply agree_on_mono; [exact (rheap_pres_agree _ _ _ _ HPR)|]. intros a [Ha _]. exact Ha.
          - eapply agree_on_mono; [exact AG3|]. intros a [_ Ha]. apply OUT1. exact Ha. }
        assert (HK3 : HK s2 (LK ++ REST0) m3 mo2) by (eapply (di_frame HKG DI); [exact HK2| exact MU3| exact WM3| exact FLOK]).
        assert (AUX3 : rauxv_ok m3 usp0) by (eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3| exact FLAUX]).
        assert (RB2 : RBASE m3).
        { eapply (RBASE_reflag _ mm m3 RB AG); [| exact MI3| unfold LO; exact ST3| exact AUX3| exact FLG3].
          intros a Ha NE. split; [destruct Ha as [Ha|Ha]; [left; lia| right; left; exact Ha]| exact NE]. }
        assert (TRF2 : TRFRAME m3 pad A L PL SB1).
        { unfold TRFRAME. eapply rw_cells_agree; [exact AG | exact TRF |]. intros ax Ha. cbn in Ha. split; [left; lia| lia]. }
        assert (FR2 : FRAME' m3).
        { unfold MFRAME. eapply rw_cells_agree; [exact AG | exact FR |]. intros ax Ha. cbn in Ha. split; [left; lia| lia]. }
        assert (SOF2 : stdout_file m3 so).
        { eapply (stdout_file_agree _ _ _ _ AG); [| exact SOF]. intros a Ha. unfold stdout_addr in Ha.
          split; [right; left; split; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia]| lia]. }
        assert (PAYB2 : bytes_at usegs m3 T PAY).
        { eapply bytes_at_agree; [exact AG | exact PAYK |]. intros a Ha. destruct (PAYOFF a Ha) as [INB OFF]. split; [right; right; exact INB| lia]. }
        try clear ST; try clear MI; try clear RS; try clear AUX; try clear SE; try clear YS; try clear AG; try clear AG1; try clear AG3;
        try clear MU1; try clear WM1; try clear MU3; try clear WM3; try clear FLG2; try clear IMGK; try clear PAYK.
        try clearbody m1. try clearbody m3.
        pose proof RB2 as (ST & MI & RS & AUX & IMG & SE & YS). unfold LO in ST.
        destruct (di_ssp HKG DI _ _ _ _ _ HK3) as [G1 G2]. unfold RGOT_SSP, RSSP_GUARD in G1, G2.
        zstep. zstep. apply evt_done.
        (* [comment removed for export] *)
        destruct (emits_S n so) as [E1 E2]. rewrite E1, E2, Wz_app.
        eapply rz_conseq_cfg; [| apply t_eq_sym; apply t_eq_emit_app].
        eapply (rz_emit_printf) with (lo := usp0 - 8388608) (canary := rc_guard) (rc := 0) (st := set_so_ps so s2);
          rewrite ?ps_get_set; rewrite ?(unsigned_lit (usp0 + -208)) by lia.
        + apply ShapeAlg.t_emit_has_nil.
        + exact Hmi2.
        + exact Hh2.
        + exact SOF2.
        + lia.
        + rewrite unsigned_lit by lia. reflexivity.
        + exact ST.
        + unfold EMIT_DEPTH. lia.
        + unfold GLOBALS_TOP. lia.
        + lia.
        + split; [exact G1 | exact G2].
        + exact MI.
        + exact FRM.
        + exact SOB.
        + intros v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 Ft fc3 m4 MUc WMc MI4 FRM3 FEQ3 ST4 SOF3 SSP3.
          rewrite ?ps_set_set, ?ps_get_set in SOF3.
          replace (ret_pc (Z_to_bv 64 0x138ac)) with (Z_to_bv 64 0x138ac) by (symmetry; rpc).
          rewrite ?(unsigned_lit (usp0 + -208)) in MUc by lia.
          assert (WOKW : Forall RWOK [(usp0 - 8388608, usp0 + -208); (0x25458, 0x25458 + 232); (0x55d78, 0x55d78 + 1024)]).
          { unfold RWOK, LO. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
          assert (RB3 : RBASE m4) by (eapply RBASE_munch; [exact RB2 | exact WOKW | exact MUc | exact WMc | exact MI4 | unfold LO; exact ST4]).
          pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG4.
          assert (TRF3 : TRFRAME m4 pad A L PL SB1).
          { unfold TRFRAME. eapply rw_cells_agree; [exact AG4 | exact TRF2 | intros ax Ha; apply RWOK_outside; [exact WOKW | cbn in Ha; left; lia]]. }
          assert (FR3 : FRAME' m4).
          { unfold MFRAME. eapply rw_cells_agree; [exact AG4 | exact FR2 | intros ax Ha; apply RWOK_outside; [exact WOKW | cbn in Ha; left; lia]]. }
          assert (HK4 : HK s2 (LK ++ REST0) m4 mo2).
          { eapply (di_frame HKG DI); [exact HK3| exact MUc| exact WMc|].
            constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|].
            constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia|].
            constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP; lia| constructor]. }
          assert (PAYB3 : bytes_at usegs m4 T PAY).
          { eapply bytes_at_agree; [exact AG4 | exact PAYB2 |]. intros ax Ha. destruct (PAYOFF ax Ha) as [_ OFF].
            destruct PBLK as [(bt & Hin & Hb1 & Hb2)| Z0]; [| lia].
            pose proof (RNG bt ltac:(apply in_or_app; right; exact Hin)) as BR.
            unfold rblock_range, alloc_ceiling in BR. cbn. lia. }
          assert (ERR4 : rw_cells usegs m4 RERRNO [C4 errv2]).
          { unfold RERRNO. eapply rw_cells_agree; [exact AG4 | exact ERR3 | intros ax Ha; cbn in Ha |- *; lia]. }
          destruct (DIR _ _ _ _ _ HK4) as (_ & Hh4 & Hl4).
          rz_seg Hh4 Hl4.
          (* [comment removed for export] *)
          zstep. zstep. if_cases KB; [| exfalso; vm_compute in KB; discriminate KB]. clear KB.
          zstep.
          rewrite (SysStep.swrap32_small (Z.of_nat (S n) + -1)) by lia.
          replace (Z.of_nat (S n) + -1) with (Z.of_nat n) by lia.
          zstep. if_cases K1; zify_cond K1.
          * (* [comment removed for export] *)
            apply evt_done. apply (IH (snd (vprintf_pure so (pieces_emit_d 0))) s2 mo2 m4 fc3); [lia|].
            exists LK, errv2. repeat (split; [assumption|]).
            split; [apply vprintf_pure_buf_bound; exact SOB|]. split; [exact HK4|]. split; [exact NBLK|]. split; [rewrite FS2; exact FS|]. split; [exact PAYB3|].
            split; [lia|]. split; [lia|]. split; [exact PLEN|]. split; [exact PL26|]. split; [exact PBLK|].
            split; [exact ERR4| exact FRM3].
          * (* [comment removed for export] *)
            assert (n = 0%nat) as -> by lia. destruct (emits_0 (snd (vprintf_pure so (pieces_emit_d 0)))) as [E3 E4]. rewrite E3, E4. rewrite ?app_nil_r. cbn [Wz map to_bytes].
            apply evt_done. eapply rz_conseq_cfg; [apply (HEND (snd (vprintf_pure so (pieces_emit_d 0))) s2 mo2 m4 fc3) | apply t_eq_sym; apply t_emit_nil_eq; apply KEND_nil].
            exists LK, errv2. repeat (split; [assumption|]).
            split; [apply vprintf_pure_buf_bound; exact SOB|]. split; [exact HK4|]. split; [exact NBLK|]. split; [rewrite FS2; exact FS|]. split; [exact PAYB3|].
            split; [lia|]. split; [lia|]. split; [exact PLEN|]. split; [exact PL26|]. split; [exact PBLK|].
            split; [exact ERR4| exact FRM3].
    Qed.
  End Loop.

End RUN.

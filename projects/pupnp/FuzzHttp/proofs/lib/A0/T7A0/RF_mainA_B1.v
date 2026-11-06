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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog AssembleA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_exit RF_mainA_A.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Definition S_OOM_A : Z := 0x14927.   Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition S_SHORT_A : Z := 0x1fc46. Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition S_OVER_A : Z := 0x159d5.  Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
Lemma s_short_ro : ro_bytes_b asegs S_SHORT_A (zb s_short) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_over_ro : ro_bytes_b asegs S_OVER_A (zb s_over) = true. Proof. vm_compute. reflexivity. Qed.
Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
  intros s. unfold str. induction (list_ascii_of_string s) as [|a l IH]; cbn; constructor; [| exact IH].
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.

Lemma implM_get_bind : forall {A} (f : ASt -> M ASt A) s Q ms,
  implM asegs (f s) s Q ms -> implM asegs (x <- mget ;; f x) s Q ms.
Proof. intros. exact H. Qed.
Lemma implM_mret_bind : forall {A B} (a : A) (f : A -> M ASt B) s Q ms,
  implM asegs (f a) s Q ms -> implM asegs (x <- mret a ;; f x) s Q ms.
Proof. intros. exact H. Qed.

Section B.
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

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE_A PZ sp0 argv envp uid hw rnd TID stdout_init).
  Notation FRAME' mm := (MFRAME sp0 argv mm MPAD S7 S6 S5 S4).
  Local Notation K := (am_K FI AI).
  Local Notation BL := (list (AllocIF.block K)).

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition HEAP (mm : mem) (g : gst) (LB : BL) : Prop :=
    exists (s : aps FI AI) (st : fsstate FI), RHEAP_A FI AI s LB mm /\ RFAKE FI st mm /\ g = gh FI AI s
      /\ fs_live FI st = [] /\ am_nsec FI AI s * 65536 <= lb_bytes FI AI LB.

  Definition BUF_A (mm : mem) (g : gst) (bufk : K) (A cap : Z) (DATA junk : list byte) : Prop :=
    HEAP mm g [(bufk, A, cap)]
    /\ rw_cells asegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
    /\ rw_cells asegs mm (sh A) (shadow_cells (block_shadow cap))
    /\ (65536 <= cap <= 67108864 /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap
    /\ 0x609000 <= A /\ A + cap + 16 <= alloc_ceiling /\ A mod 16 = 0 /\ win_ok A (cap + 16).

  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSVA) (Z_to_bv 64 x23) t3 t4 t5 t6 F fc mm).

  Definition rd_pc (st : rd_st (ptr:=unit)) : Z := if zlength (rd_content st) =? rd_cap st then 0x86108 else 0x86100.

  Definition RDINV (fd P1v : Z) (st : rd_st) (so : ASt) (ms : machine_state) (g : gst) : Prop :=
    exists (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A : Z) (DATA junk : list byte) (errv : word) (kb : K),
      ms = RST (rd_pc st) x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength (rd_content st)) fd (rd_cap st) A t3 t4 t5 t6 F fc mm
      /\ rd_content st = map bv_unsigned DATA /\ so = stdout_init
      /\ BUF_A mm g kb A (rd_cap st) DATA junk
      /\ FRAME' mm /\ BASE' mm /\ CJ0 mm /\ rw_cells asegs mm RERRNOA [C4 errv] /\ frm0 fc.

  Definition RDBRK (fd P1v : Z) (b : unit) (content : list Z) (so : ASt) (ms : machine_state) (g : gst) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap : Z) (DATA junk : list byte) (errv : word) (kb : K),
      ms = RST 0x86168 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap 0 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA /\ so = stdout_init
      /\ BUF_A mm g kb A cap DATA junk
      /\ FRAME' mm /\ BASE' mm /\ CJ0 mm /\ rw_cells asegs mm RERRNOA [C4 errv] /\ frm0 fc.

  Definition POSTBODY (fd P1v : Z) (r : rd_st + rd_result) (so : ASt) (ms : machine_state) (g : gst) : Prop :=
    match r with
    | inl st' => RDINV fd P1v st' so ms g
    | inr RdExit => rat_exitA TID 2 so ms
    | inr (RdDone b c) => RDBRK fd P1v b c so ms g
    end.

  Definition rd_read_part (fd : Z) (path : list Z) (st1 : rd_st (ptr:=unit)) : M ASt (rd_st + rd_result) :=
    let len := zlength (rd_content st1) in
    let cnt := Z.min (rd_cap st1 - len) READ_CHUNK in
    a <- msys (NRead fd RSVA cnt) (dec_read RSVA cnt) ;;
    match a with
    | RdErr _ => io_diag ioA (DReadError path) ;;; mret (inr RdExit)
    | RdData bs =>
        if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
        else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
    end.

  Definition diag_of_pdiag (d : pdiag) : diag_msg :=
    match d with PDUsage a => DUsage a | PDCannotOpen p => DCannotOpen p | PDReadError p => DReadError p | PDTooBig => DTooBig end.
  #[using="Type"] Lemma s_diag_pdiag : forall d, io_diag ioA (diag_of_pdiag d) = stderr_fprintf (pdiag_pieces d).
  Proof. intros []; reflexivity. Qed.

  #[using="VSP CEIL ESF FPR"] Lemma fprintf_exit : forall (d : pdiag) {R} (Kp : M ASt R) (Q : R -> ASt -> machine_state -> Prop) (so : ASt)
      x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    diag_args d mm a1v a2v (usp0 - 8388608) (usp0 - 128) ->
    BASE' mm -> so = stdout_init -> frm0 fc ->
    (forall ms', rat_exitA TID 2 so ms' -> implM asegs Kp so Q ms') ->
    implM asegs (io_diag ioA (diag_of_pdiag d) ;;; Kp) so Q
      (GST 0x862d4 x1 t0 t1 t2 x9 (Z_to_bv 64 RSTDERR) a1v a2v x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros DA BA SO FRM HK. rewrite s_diag_pdiag.
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'. unfold LO in SF.
    pose proof BA as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST.
    destruct MC as (G28 & GSE & SSP).
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM asegs tm so Q msx) end.
    eapply implM_bind.
    { eapply (FPR d) with (lo := usp0 - 8388608) (canary := guard_word); rewrite ?unsigned_lit by lia;
        first [ apply stderr_wfile0_wfile; exact SE| reflexivity
              | replace (usp0 + -128) with (usp0 - 128) by lia; exact DA
              | exact ST | unfold FPRINTF_DEPTH; lia | unfold GLOBALS_TOP; lia | lia | exact SSP | exact MI | exact FRM | exact ENV
              | unfold RO_LO, RO_SZ; apply (SHZ_ro sp0 argv envp uid hw rnd); exact SZ
              | apply (SHZ_stack sp0 argv envp uid hw rnd); [exact SZ | lia | pose proof (build_stack_bytes_length rph sp0 argv envp uid hw rnd); lia | lia | lia] ]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ENV2 & ->).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x862d8)) with (Z_to_bv 64 0x862d8) by (symmetry; rpc).
    pose proof (gagree_on_of_munch _ _ _ MUc WMc) as AG.
    assert (OUT2 : forall a, (a < 0x10008000000 /\ ~ (0xaeac8 <= a < 0xaeac8 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0xaeac8, 0xaeac8 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    eapply implM_evt; [| intros ms'' H; apply HK; exact H].
    zstep.
    destruct SSP2 as [GG2 GU2]. unfold got_ssp, ssp_guard in GG2, GU2.
    eapply (exit2_tail sp0 TID VSP CEIL).
    - unfold LO. exact ST2.
    - eapply (EXITC_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold exitc_addr in Ha; lia| exact EX].
    - eapply wr_at_transport; [exact CRT| exact WMc].
    - exact ENV2.
    - eapply globals_shadow_frame; [exact GSH| exact MUc| exact WMc| unfold app_ivs; apply Forall_cons; [apply app_iv_stack; lia| apply Forall_cons; [apply app_iv_low; lia| apply Forall_nil]]].
    - exact GG2.
    - exact GU2.
    - rewrite SO. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF].
    - apply stderr_wfile_file. exact SEW.
    - eapply (stdin_file_agree _ _ _ AG); [intros a Ha; apply OUT2; unfold stdin_addr in Ha; lia| exact SI].
    - exact MI2.
  Qed.
End B.

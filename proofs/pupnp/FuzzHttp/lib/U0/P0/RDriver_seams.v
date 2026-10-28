(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Keeps Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl Stdio_iface RDriver_kit RDriver_ctx RDriver_iface RF_main_post.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require RF_main_A RF_main_T F_printf_diag F_printf_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_fuzz_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Record dlay := mkDL {
  d_A : Z;
  d_cap : Z;
  d_L : Z;
  d_sc : Z;
  d_AL : Z;
  d_OW : Z;
  d_DATA : list byte;
  d_junk : list byte;
  d_mpad : list byte;
  d_pad : list byte
}.

Definition drv_status (d : dlay) (fl : bool) : Z := if d_sc d <? 0 then 0 else if fl then 78 else 0.

Section SEAMS.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv : list (list byte)) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).

  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).

  Notation TST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).
  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 RSV) (Z_to_bv 64 0) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Definition DLAY_ok (ap : at_parser (ptr:=bptr)) (d : dlay) : Prop :=
    ap_content ap = map bv_unsigned (d_DATA d) /\ ap_config_len ap = d_L d /\ ap_count ap = (d_sc d <? 0)
    /\ 1 <= ap_calls ap <= 4
    /\ 6 + d_L d <= Z.of_nat (length (d_DATA d)) <= d_cap d /\ d_cap d <= MAX_INPUT /\ 0 <= d_L d < 32768 /\ -128 <= d_sc d < 128
    /\ rblock_range (d_A d) (d_cap d)
    /\ match ap_owned ap with
       | None => ap_payload_len ap = 0 /\ d_AL d = 0x3b6e0 /\ d_OW d = 0
       | Some p => 0 < ap_payload_len ap /\ d_OW d = d_AL d /\ rblock_range (d_AL d) (ap_payload_len ap)
       end.

  Definition DBLOCKS (own : bool) (ap : at_parser (ptr:=bptr)) (d : dlay) (LB : list block) : Prop :=
    In (ap_buf ap, d_A d, d_cap d) LB
    /\ (own = true -> match ap_owned ap with Some p => In (p, d_AL d, ap_payload_len ap) LB | None => True end).

  Definition DBYTES (own : bool) (ap : at_parser (ptr:=bptr)) (d : dlay) (m : mem) : Prop :=
    rw_cells rsegs m (d_A d) [CB (length (d_DATA d)) (d_DATA d); CB (Z.to_nat (d_cap d - Z.of_nat (length (d_DATA d)))) (d_junk d)]
    /\ (own = true -> match ap_owned ap with
                      | Some p => rw_cells rsegs m (d_AL d) [CB (Z.to_nat (ap_payload_len ap)) (skipn (Z.to_nat (6 + d_L d)) (d_DATA d))]
                      | None => True end).

  Definition RSTAT_cb (cb : bool) (mm : mem) : Prop :=
    if cb then exists m0 : mem, RSTAT TID m0 /\ agree_on rsegs (fun a => rstat_addr a /\ ~ (0x3b6d4 <= a < 0x3b6d5)) m0 mm
                                /\ rw_cells rsegs mm 0x3b6d4 [C1 (Z_to_bv 8 1)]
    else RSTAT TID mm.

  Definition DMEM (cb : bool) (ap : at_parser (ptr:=bptr)) (d : dlay) (m : mem) : Prop :=
    TRFRAME sp0 m (d_pad d) (d_sc d) (ap_payload_len ap) (d_A d) (d_L d)
    /\ MFRAME sp0 argv m (d_mpad d) S7 S6 S5 S4
    /\ mem_inv rsegs m /\ RSTAT_cb cb m /\ rauxv_ok m usp0 /\ stderr_wfile0 m /\ CJ1 m.

  Definition dmem_addr (a : Z) : Prop :=
    usp0 - 208 <= a \/ rstat_addr a \/ stderr_addr a \/ RF_main_A.cj0_addr a.

  Definition SEAM (cb own : bool) (ap : at_parser (ptr:=bptr)) (d : dlay) (s : PState) (LB : list block) (m : mem) : Prop :=
    DLAY_ok ap d /\ DMEM cb ap d m /\ DBYTES own ap d m /\ DBLOCKS own ap d LB /\ RHEAP s LB m
    /\ stdout_file m (ps_so s) /\ (exists errv : word, rw_cells rsegs m RERRNO [C4 errv])
    /\ stk rsegs m (usp0 - 8388608) (usp0 + -208).

  Definition rat_head (k : Z) (fl : bool) (ap : at_parser (ptr:=bptr)) (d : dlay) (s : PState) (LB : list block) (m : mem) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      ms = TST 0x13ea4 x1 t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) x19 (Z_to_bv 64 0x3b6d0) (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ 1 <= k <= ap_calls ap /\ SEAM false true ap d s LB m.

  Definition rat_call (k : Z) (fl : bool) (ap : at_parser (ptr:=bptr)) (d : dlay) (s : PState) (LB : list block) (m : mem) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      ms = TST 0x13fbc (Z_to_bv 64 0x13eb8) t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               (Z_to_bv 64 (d_AL d)) (Z_to_bv 64 (ap_payload_len ap)) a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) x19 (Z_to_bv 64 0x3b6d0) (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ 1 <= k <= ap_calls ap /\ SEAM true true ap d s LB m.

  Definition rat_ret (k rc : Z) (fl : bool) (ap : at_parser (ptr:=bptr)) (d : dlay) (s : PState) (LB : list block) (m : mem) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      ms = TST 0x13eb8 x1 t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) x19 (Z_to_bv 64 0x3b6d0) (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ 1 <= k <= ap_calls ap /\ 0 <= rc < 2^31 /\ SEAM true true ap d s LB m.

  Definition rat_emit (k rc : Z) (fl : bool) (ap : at_parser (ptr:=bptr)) (d : dlay) (s : PState) (LB : list block) (m : mem) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      ms = TST 0x13f74 (Z_to_bv 64 0x13ec8) t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               (Z_to_bv 64 rc) (Z_to_bv 64 rc) a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) (Z_to_bv 64 rc) (Z_to_bv 64 0x3b6d0) (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ 1 <= k <= ap_calls ap /\ 0 <= rc < 2^31 /\ SEAM false true ap d s LB m.

  Definition rat_emit_ret (k rc : Z) (fl : bool) (ap : at_parser (ptr:=bptr)) (d : dlay) (s : PState) (LB : list block) (m : mem) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      ms = TST 0x13ec8 x1 t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) (Z_to_bv 64 rc) (Z_to_bv 64 0x3b6d0) (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ 1 <= k <= ap_calls ap /\ 0 <= rc < 2^31 /\ SEAM false true ap d s LB m.

  Definition rat_free_owned (fl : bool) (ap : at_parser (ptr:=bptr)) (d : dlay) (s : PState) (LB : list block) (m : mem) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      ms = TST 0x17fb0 (Z_to_bv 64 0x13ee4) t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               (Z_to_bv 64 (d_OW d)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) x19 (Z_to_bv 64 0x3b6d0) (Z_to_bv 64 0) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ SEAM false true ap d s LB m.

  Definition rat_owned_ret (fl : bool) (ap : at_parser (ptr:=bptr)) (d : dlay) (s : PState) (LB : list block) (m : mem) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      ms = TST 0x13ee4 x1 t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) x19 (Z_to_bv 64 0x3b6d0) (Z_to_bv 64 0) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ SEAM false false ap d s LB m.

  Definition rat_free_buf (st : Z) (ap : at_parser (ptr:=bptr)) (d : dlay) (s : PState) (LB : list block) (m : mem) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      ms = GST 0x17fb0 (Z_to_bv 64 0x13d18) t0 t1 t2 (Z_to_bv 64 st) (Z_to_bv 64 (d_A d))
               (Z_to_bv 64 (d_A d)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_L d)) (Z_to_bv 64 (d_A d + 6 + d_L d)) (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_sc d)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ 0 <= st < 256
      /\ DLAY_ok ap d /\ MFRAME sp0 argv m (d_mpad d) S7 S6 S5 S4 /\ mem_inv rsegs m /\ RSTAT TID m /\ rauxv_ok m usp0 /\ stderr_wfile0 m /\ CJ1 m
      /\ DBYTES false ap d m /\ DBLOCKS false ap d LB /\ RHEAP s LB m
      /\ stdout_file m (ps_so s) /\ (exists errv : word, rw_cells rsegs m RERRNO [C4 errv])
      /\ stk rsegs m (usp0 - 8388608) (usp0 + -128).

  Definition rat_main_ret (st : Z) (s : PState) (LB : list block) (m : mem) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mpad : list byte),
      ms = GST 0x13d18 x1 t0 t1 t2 (Z_to_bv 64 st) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 F fc m
      /\ 0 <= st < 256
      /\ MFRAME sp0 argv m mpad S7 S6 S5 S4 /\ mem_inv rsegs m /\ RSTAT TID m /\ RHEAP s LB m
      /\ stdout_file m (ps_so s) /\ stderr_wfile0 m
      /\ stk rsegs m (usp0 - 8388608) (usp0 + -128).

  #[using="Type"] Lemma valid_sp_facts : valid_sp sp0 -> 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0.
  Proof. intros (A & B & C). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

  #[using="Type"] Lemma RSTAT_cb_agree : forall (P : Z -> Prop) cb m m', agree_on rsegs P m m' -> (forall a, rstat_addr a -> P a) ->
    RSTAT_cb cb m -> RSTAT_cb cb m'.
  Proof.
    intros P [] m m' AG HP RS; cbv beta iota delta [RSTAT_cb] in RS |- *.
    - destruct RS as (m0 & RS0 & AG0 & CB). exists m0. split; [exact RS0|]. split.
      + eapply agree_on_trans; [exact AG0|]. eapply agree_on_mono; [exact AG|]. intros a Ha. apply HP. exact (proj1 Ha).
      + eapply rw_cells_agree; [exact AG| exact CB|]. intros a Ha. apply HP. unfold rstat_addr. cbn in Ha. lia.
    - eapply (RSTAT_agree TID _ _ _ AG); [exact HP| exact RS].
  Qed.

  #[using="Type"] Lemma RSTAT_cb_heap_pres : forall LB SP cb m m', rheap_pres LB SP m m' -> RSTAT_cb cb m -> RSTAT_cb cb m'.
  Proof.
    intros LB SP cb m m' HP. apply (RSTAT_cb_agree _ cb _ _ HP). intros a Ha. right; left.
    unfold rstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
  Qed.

  #[using="Type"] Lemma RSTAT_cb_set : forall cb cb' m m', RSTAT_cb cb m ->
    agree_on rsegs (fun a => rstat_addr a /\ ~ (0x3b6d4 <= a < 0x3b6d5)) m m' ->
    rw_cells rsegs m' 0x3b6d4 [C1 (Z_to_bv 8 (Z.b2z cb'))] -> RSTAT_cb cb' m'.
  Proof.
    intros [] [] m m' RS AG CB; cbv beta iota delta [RSTAT_cb] in RS |- *.
    - destruct RS as (m0 & RS0 & AG0 & _). exists m0. split; [exact RS0|]. split; [eapply agree_on_trans; [exact AG0| exact AG]| exact CB].
    - destruct RS as (m0 & RS0 & AG0 & _). eapply RSTAT_incb; [exact RS0| eapply agree_on_trans; [exact AG0| exact AG]| exact CB].
    - exists m. split; [exact RS|]. split; [exact AG| exact CB].
    - eapply RSTAT_incb; [exact RS| exact AG| exact CB].
  Qed.

  #[using="Type"] Lemma RSTAT_cb_cell : forall cb m, RSTAT_cb cb m -> rw_cells rsegs m 0x3b6d4 [C1 (Z_to_bv 8 (Z.b2z cb))].
  Proof.
    intros [] m RS; cbv beta iota delta [RSTAT_cb] in RS.
    - destruct RS as (_ & _ & _ & CB). exact CB.
    - destruct RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [reg [_ CB]]). exact CB.
  Qed.

  #[using="Type"] Lemma DMEM_agree : forall (P : Z -> Prop) cb ap d m m',
    agree_on rsegs P m m' -> (forall a, dmem_addr a -> P a) -> mem_inv rsegs m' -> rauxv_ok m' usp0 ->
    DMEM cb ap d m -> DMEM cb ap d m'.
  Proof.
    intros P cb ap d m m' AG HP MI' AUX' (TF & FR & MI & RS & AUX & SE & CJ). unfold DMEM.
    split. { unfold TRFRAME in *. eapply rw_cells_agree; [exact AG| exact TF|]. intros a Ha. apply HP. left. cbn in Ha. lia. }
    split. { unfold MFRAME in *. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. apply HP. left. cbn in Ha. lia. }
    split; [exact MI'|].
    split. { eapply (RSTAT_cb_agree _ cb _ _ AG); [| exact RS]. intros a Ha. apply HP. right; left. exact Ha. }
    split; [exact AUX'|].
    split. { eapply (stderr_wfile0_agree _ _ _ AG); [| exact SE]. intros a Ha. apply HP. right; right; left. exact Ha. }
    eapply (RF_main_T.CJ1_agree _ _ _ AG); [| exact CJ]. intros a Ha. apply HP. right; right; right. exact Ha.
  Qed.

  #[using="Type"] Lemma DMEM_heap_pres : forall cb LB SP ap d m m', rheap_pres LB SP m m' -> SP <= usp0 - 208 -> mem_inv rsegs m' -> rauxv_ok m' usp0 ->
    DMEM cb ap d m -> DMEM cb ap d m'.
  Proof.
    intros cb LB SP ap d m m' HP HSP MI' AUX' (TF & FR & MI & RS & AUX & SE & CJ). unfold DMEM.
    split. { unfold TRFRAME in *. eapply rheap_pres_rw_cells; [exact HP| exact TF| left; cbn; lia]. }
    split. { unfold MFRAME in *. eapply rheap_pres_rw_cells; [exact HP| exact FR| left; cbn; lia]. }
    split; [exact MI'|]. split; [eapply RSTAT_cb_heap_pres; [exact HP| exact RS]|]. split; [exact AUX'|].
    split; [eapply stderr_wfile0_heap_pres; [exact HP| exact SE]| eapply RF_main_T.CJ1_heap_pres; [exact HP| exact CJ]].
  Qed.

  #[using="Type"] Lemma DMEM_munch : forall W cb ap d m m', valid_sp sp0 -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    Forall (fun iv => (0x5d000 <= fst iv /\ snd iv <= usp0 - 208) \/ (fst iv = RERRNO /\ snd iv = RERRNO + 4)
                      \/ (fst iv = RSTDOUT /\ snd iv = RSTDOUT + 232) \/ (fst iv = RSTDOUT_BUF /\ snd iv = RSTDOUT_BUF + 1024)) W ->
    DMEM cb ap d m -> DMEM cb ap d m'.
  Proof.
    intros W cb ap d m m' VSP MU WM MI' HW DM. pose proof (valid_sp_facts VSP) as SF.
    apply (DMEM_agree _ _ _ _ _ _ (agree_on_of_munch rsegs _ _ _ MU WM)); [| exact MI'| | exact DM].
    2:{ destruct DM as (_ & _ & _ & _ & AUX & _). eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
        eapply Forall_impl; [| exact HW]. intros [lo hi] H1. cbn [fst snd] in H1 |- *. unfold RAUXV_CELL, RERRNO in *. lia. }
    intros a Ha. cbn. clear MU WM MI' DM. induction W as [|[lo hi] W IH]; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; exact H2]. cbn [fst snd] in H1.
    unfold dmem_addr, rstat_addr, stderr_addr, RF_main_A.cj0_addr, RERRNO in *. lia.
  Qed.

  #[using="Type"] Lemma DMEM_cb : forall cb cb' ap d m m', valid_sp sp0 -> munch [(0x3b6d4, 0x3b6d5)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    rw_cells rsegs m' 0x3b6d4 [C1 (Z_to_bv 8 (Z.b2z cb'))] -> DMEM cb ap d m -> DMEM cb' ap d m'.
  Proof.
    intros cb cb' ap d m m' VSP MU WM MI' CB (TF & FR & MI & RS & AUX & SE & CJ). pose proof (valid_sp_facts VSP) as SF.
    pose proof (agree_on_of_munch rsegs _ _ _ MU WM) as AG. unfold DMEM.
    split. { unfold TRFRAME in *. eapply rw_cells_agree; [exact AG| exact TF|]. intros a Ha. cbn in Ha |- *. lia. }
    split. { unfold MFRAME in *. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. cbn in Ha |- *. lia. }
    split; [exact MI'|].
    split. { eapply RSTAT_cb_set; [exact RS| | exact CB]. eapply agree_on_mono; [exact AG|]. intros a [_ Hn]. cbn. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn [fst snd]; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply (stderr_wfile0_agree _ _ _ AG); [| exact SE]. intros a Ha. cbn. unfold stderr_addr in Ha. lia. }
    eapply (RF_main_T.CJ1_agree _ _ _ AG); [| exact CJ]. intros a Ha. cbn. unfold RF_main_A.cj0_addr in Ha. lia.
  Qed.

  #[using="Type"] Lemma DBYTES_agree : forall (P : Z -> Prop) own ap d m m',
    agree_on rsegs P m m' -> DLAY_ok ap d ->
    (forall a, d_A d <= a < d_A d + d_cap d -> P a) ->
    (own = true -> forall a, d_AL d <= a < d_AL d + ap_payload_len ap -> P a) ->
    DBYTES own ap d m -> DBYTES own ap d m'.
  Proof.
    intros P own ap d m m' AG OK HP HP2 [B1 B2]. pose proof OK as (_ & _ & _ & _ & LEN & _ & _ & _ & BR & OWN). split.
    - eapply rw_cells_agree; [exact AG| exact B1|]. intros a Ha. apply HP. cbn [cells_size csize Nat.add] in Ha. lia.
    - intros Ho. specialize (B2 Ho). specialize (HP2 Ho). destruct (ap_owned ap) as [p|]; [| exact I].
      destruct OWN as (PL & _ & BR2). pose proof BR2 as (_ & _ & Q3 & _).
      eapply rw_cells_agree; [exact AG| exact B2|]. intros a Ha. apply HP2. cbn [cells_size csize Nat.add] in Ha. lia.
  Qed.

  #[using="Type"] Lemma DBYTES_drop : forall ap d m, DBYTES true ap d m -> DBYTES false ap d m.
  Proof. intros ap d m [B1 _]. split; [exact B1| intros X; discriminate X]. Qed.
  #[using="Type"] Lemma DBLOCKS_drop : forall ap d LB, DBLOCKS true ap d LB -> DBLOCKS false ap d LB.
  Proof. intros ap d LB [B1 _]. split; [exact B1| intros X; discriminate X]. Qed.

  #[using="Type"] Lemma SEAM_cb : forall cb cb' own ap d s LB m m', valid_sp sp0 -> munch [(0x3b6d4, 0x3b6d5)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    rw_cells rsegs m' 0x3b6d4 [C1 (Z_to_bv 8 (Z.b2z cb'))] -> SEAM cb own ap d s LB m -> SEAM cb' own ap d s LB m'.
  Proof.
    intros cb cb' own ap d s LB m m' VSP MU WM MI' CB (OK & DM & DB & DBL & HP & SOF & [errv ERR] & ST).
    pose proof (valid_sp_facts VSP) as SF. pose proof (agree_on_of_munch rsegs _ _ _ MU WM) as AG.
    pose proof OK as (_ & _ & _ & _ & LEN & _ & _ & _ & BR & OWN).
    split; [exact OK|].
    split; [eapply DMEM_cb; [exact VSP| exact MU| exact WM| exact MI'| exact CB| exact DM]|].
    split. { eapply (DBYTES_agree _ own ap d m m' AG OK); [| | exact DB].
             - intros a Ha. cbn. pose proof BR as (_ & _ & _ & _ & B5 & B6). lia.
             - intros _ a Ha. cbn. destruct (ap_owned ap) as [p|]; [| destruct OWN as (PL0 & _); lia].
               destruct OWN as (_ & _ & Q). pose proof Q as (_ & _ & _ & _ & Q5 & Q6). lia. }
    split; [exact DBL|].
    split. { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
             constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia| constructor]. }
    split. { eapply (stdout_file_agree _ _ _ _ AG); [| exact SOF]. intros a Ha. cbn. unfold stdout_addr in Ha. lia. }
    split. { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha |- *. unfold RERRNO in Ha. lia. }
    eapply stk_agree; [exact AG| exact ST|]. intros a Ha. cbn. lia.
  Qed.

  #[using="Type"] Lemma head_to_call : forall k fl ap d s LB m ms, valid_sp sp0 -> rat_head k fl ap d s LB m ms ->
    evt rsegs (fun ms' => exists m', rat_call k fl ap d s LB m' ms') ms.
  Proof.
    intros k fl ap d s LB m ms VSP (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & -> & FRM & HK & SM).
    pose proof SM as (_ & (_ & _ & MI & RS & _) & _).
    pose proof (RSTAT_cb_cell false m RS) as CB. change (Z_to_bv 8 (Z.b2z false)) with (Z_to_bv 8 0) in CB.
    pose proof (munch_refl [(0x3b6d4, 0x3b6d5)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zst. zstep. zstep. zstep.
    apply evt_done. cbv beta. eexists. unfold rat_call. do 16 eexists. split; [reflexivity|].
    split; [exact FRM|]. split; [exact HK|].
    eapply SEAM_cb; [exact VSP| exact MU| exact WM| exact MI| exact CB| exact SM].
  Qed.

  #[using="Type"] Lemma rat_parser_call : forall ap s ms, valid_sp sp0 -> rat_parser sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 ap s ms ->
    exists d LB, evt rsegs (fun ms' => exists m, rat_call (ap_calls ap) false ap d s LB m ms') ms
                 /\ ps_so s = stdout_init /\ ps_fa s = (0, 0)
                 /\ LB = match ap_owned ap with Some p => [(p, d_AL d, ap_payload_len ap); (ap_buf ap, d_A d, d_cap d)]
                         | None => [(ap_buf ap, d_A d, d_cap d)] end.
  Proof.
    intros ap s ms VSP (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & A & cap & L & sc & AL & OW & DATA & junk & mpad & pad & errv & LB
                     & -> & FRM & HC & HL & HCNT & HK & LEN & CAPM & LR & SCR & BR & OWN & HP & SO & FA & BLK & TFR & FR & ST & MI & RS & AUX & SE & SOF & ERR & CJ).
    exists (mkDL A cap L sc AL OW DATA junk mpad pad), LB. cbn [d_A d_cap d_L d_sc d_AL d_OW d_DATA d_junk d_mpad d_pad].
    split; [| split; [exact SO| split; [exact FA| destruct (ap_owned ap) as [p|]; [destruct OWN as (_ & _ & E & _)| destruct OWN as (_ & _ & _ & E)]; exact E]]].
    eapply head_to_call; [exact VSP|].
    unfold rat_head. exists x1, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, (Z_to_bv 64 (A + 2)), t3, t4, t5, t6, F, fc.
    cbn [d_A d_cap d_L d_sc d_AL d_OW d_DATA d_junk d_mpad d_pad].
    split; [reflexivity|]. split; [exact FRM|]. split; [lia|].
    split. { unfold DLAY_ok. cbn [d_A d_cap d_L d_sc d_AL d_OW d_DATA].
             repeat (split; [first [assumption| lia]|]).
             destruct (ap_owned ap) as [p|]; [destruct OWN as (Q1 & Q2 & Q3 & Q4 & Q5); auto| destruct OWN as (Q1 & Q2 & Q3 & Q4); auto]. }
    split. { unfold DMEM. cbn [d_pad d_mpad d_sc d_A d_L].
             split; [exact TFR|]. split; [exact FR|]. split; [exact MI|]. split; [exact RS|]. split; [exact AUX|]. split; [exact SE| exact CJ]. }
    split. { unfold DBYTES. cbn [d_A d_cap d_DATA d_junk d_AL d_L]. split; [exact BLK|]. intros _.
             destruct (ap_owned ap) as [p|]; [destruct OWN as (Q1 & Q2 & Q3 & Q4 & Q5); exact Q5| exact I]. }
    split. { unfold DBLOCKS. cbn [d_A d_cap d_AL]. destruct (ap_owned ap) as [p|].
             - destruct OWN as (Q1 & Q2 & -> & Q4 & Q5). split; [right; left; reflexivity| intros _; left; reflexivity].
             - destruct OWN as (Q1 & Q2 & Q3 & ->). split; [left; reflexivity| intros _; exact I]. }
    split; [exact HP|]. split; [rewrite SO; exact SOF|]. split; [exists errv; exact ERR| exact ST].
  Qed.

  #[using="Type"] Lemma ret_to_emit : forall k rc fl ap d s LB m ms, valid_sp sp0 -> rat_ret k rc fl ap d s LB m ms ->
    evt rsegs (fun ms' => exists m', rat_emit k rc fl ap d s LB m' ms') ms.
  Proof.
    intros k rc fl ap d s LB m ms VSP (x1 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & -> & FRM & HK & HRC & SM).
    pose proof SM as (_ & (_ & _ & MI & RS & _) & _).
    eapply post_to_emit; [exact (RSTAT_cb_cell true m RS)| exact MI|].
    intros m' MU WM MI' CB. apply evt_done. cbv beta. eexists. unfold rat_emit. do 15 eexists. split; [reflexivity|].
    split; [exact FRM|]. split; [exact HK|]. split; [exact HRC|].
    eapply SEAM_cb; [exact VSP| exact MU| exact WM| exact MI'| exact CB| exact SM].
  Qed.

  #[using="Type"] Lemma ps_get_set : forall (x : PState) so, ps_so (set_so_ps so x) = so.
  Proof. intros [] so. reflexivity. Qed.
  #[using="Type"] Lemma ps_set_set : forall (x : PState) so so', set_so_ps so' (set_so_ps so x) = set_so_ps so' x.
  Proof. intros [] so so'. reflexivity. Qed.

  #[using="CEIL"] Lemma emit_step : forall k fl ap d s LB m ms, valid_sp sp0 -> rat_emit k 0 fl ap d s LB m ms ->
    implM rsegs (stdout_vprintf ps_so set_so_ps pieces_emit) s
          (fun _ s' ms' => exists m' so', rat_emit_ret k 0 fl ap d s' LB m' ms' /\ s' = set_so_ps so' s) ms.
  Proof.
    intros k fl ap d s LB m ms VSP (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & -> & FRM & HK & HRC & SM).
    pose proof (valid_sp_facts VSP) as SF.
    destruct SM as (OK & DM & DB & DBL & HP & SOF & [errv ERR] & ST).
    pose proof DM as (TF & FR & MI & RS & AUX & SE & CJ).
    pose proof (F_printf_diag.emit_printf_proof ps_so set_so_ps ps_get_set ps_set_set) as EP. unfold F_printf_diag.emit_printf_stmt in EP.
    eapply implM_mono.
    { eapply (implM_keepsf rsegs (fun x => set_so_ps stdout_init x)).
      - eapply EP with (lo := usp0 - 8388608) (canary := guard_word);
          [exact SOF| rewrite unsigned_lit by lia; reflexivity| rewrite unsigned_lit by lia; exact ST
          | rewrite unsigned_lit by lia; unfold F_printf_iface.EMIT_DEPTH; lia| unfold F_printf_iface.GLOBALS_TOP; lia
          | rewrite unsigned_lit by lia; lia| apply (RHEAP_ssp _ _ _ HP)| exact MI| exact FRM].
      - apply (stdout_vprintf_keeps ps_so set_so_ps). intros so [x1 x2 x3 x4]. reflexivity. }
    cbv beta. intros [] s' ms' [PO ES].
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FEQ & ST' & SOF' & SSP').
    rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit in ST' by lia.
    assert (Es : s' = set_so_ps (ps_so s') s).
    { destruct s as [q1 q2 q3 q4], s' as [r1 r2 r3 r4]. cbn in ES |- *. unfold set_so_ps in ES |- *. cbn in ES |- *. injection ES. intros -> -> ->. reflexivity. }
    exists m', (ps_so s'). split; [| exact Es].
    pose proof (agree_on_of_munch rsegs _ _ _ MU WM) as AG.
    pose proof OK as (_ & _ & _ & _ & LEN & _ & _ & _ & BR & OWN). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). rewrite CEIL in BR4. unfold LO in BR4.
    assert (OUT : forall a, ((a < usp0 - 8388608 \/ usp0 - 208 <= a) /\ ~ (RSTDOUT <= a < RSTDOUT + 232) /\ ~ (RSTDOUT_BUF <= a < RSTDOUT_BUF + 1024)) ->
                            (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -208); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] a0) a).
    { intros a Ha. cbn. lia. }
    unfold rat_emit_ret. do 18 eexists. split; [replace (ret_pc (Z_to_bv 64 0x13ec8)) with (Z_to_bv 64 0x13ec8) by (symmetry; rpc); reflexivity|].
    split; [exact FRM'|]. split; [exact HK|]. split; [exact HRC|].
    split; [exact OK|].
    split. { eapply (DMEM_munch _ _ ap d m m' VSP MU WM MI'); [| exact DM]. unfold RERRNO.
             constructor; [cbn [fst snd]; left; lia|]. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    split. { eapply (DBYTES_agree _ true ap d m m' AG OK); [| | exact DB].
             - intros a Ha. apply OUT. lia.
             - intros _ a Ha. apply OUT. destruct (ap_owned ap) as [p|]; [| destruct OWN as (PL0 & _); lia].
               destruct OWN as (_ & _ & Q). pose proof Q as (Q1 & Q2 & Q3 & Q4 & Q5). rewrite CEIL in Q4. unfold LO in Q4. lia. }
    split; [exact DBL|].
    split. { rewrite Es. eapply RHEAP_ext; [| reflexivity| reflexivity].
             eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
             constructor; [left; cbn [fst snd]; rewrite CEIL; unfold LO; lia|].
             constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia|].
             constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia| constructor]. }
    split; [exact SOF'|].
    split. { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. apply OUT. cbn in Ha. unfold RERRNO in Ha. lia. }
    replace (usp0 - 8388608) with (usp0 - 8388608) in ST' by lia. exact ST'.
  Qed.

  #[using="Type"] Lemma emit_ret_call : forall k rc fl ap d s LB m ms, valid_sp sp0 -> rat_emit_ret k rc fl ap d s LB m ms -> 1 < k ->
    evt rsegs (fun ms' => exists m', rat_call (k - 1) (fl || (0 <? rc)) ap d s LB m' ms') ms.
  Proof.
    intros k rc fl ap d s LB m ms VSP (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & -> & FRM & HK & HRC & SM) H1.
    pose proof SM as ((_ & _ & _ & HC4 & _) & _).
    eapply (emit_ret_next sp0 S8 S9 S10 S11 _ k rc fl); [lia| exact HRC| | intros X; exfalso; lia].
    intros _. apply (head_to_call (k - 1) (fl || (0 <? rc)) ap d s LB m _ VSP).
    unfold rat_head. do 19 eexists. split; [reflexivity|]. split; [exact FRM|]. split; [lia| exact SM].
  Qed.

  #[using="Type"] Lemma emit_ret_free : forall k rc fl ap d s LB m ms, rat_emit_ret k rc fl ap d s LB m ms -> k = 1 ->
    evt rsegs (rat_free_owned (fl || (0 <? rc)) ap d s LB m) ms.
  Proof.
    intros k rc fl ap d s LB m ms (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & -> & FRM & HK & HRC & SM) H1.
    pose proof SM as ((_ & _ & _ & HC4 & _) & _).
    eapply (emit_ret_next sp0 S8 S9 S10 S11 _ k rc fl); [lia| exact HRC| intros X; exfalso; lia|].
    intros _. apply evt_done. unfold rat_free_owned. do 17 eexists. split; [reflexivity|]. split; [exact FRM| exact SM].
  Qed.

  #[using="Type"] Lemma owned_ret_to_free_buf : forall fl ap d s LB m ms, valid_sp sp0 -> rat_owned_ret fl ap d s LB m ms ->
    evt rsegs (rat_free_buf (drv_status d fl) ap d s LB m) ms.
  Proof.
    intros fl ap d s LB m ms VSP (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & -> & FRM & SM).
    pose proof (valid_sp_facts VSP) as SF.
    destruct SM as (OK & DM & DB & DBL & HP & SOF & ERR & ST). pose proof OK as (_ & _ & _ & _ & _ & _ & _ & SCR & _).
    destruct DM as (TF & FR & MI & RS & AUX & SE & CJ).
    eapply (free_ret_to_main sp0 S8 S9 S10 S11 VSP _ fl (d_sc d) (ap_payload_len ap) (d_A d) (d_L d) (d_pad d));
      [exact TF| exact ST| lia| exact SCR|].
    intros a0' ST'. apply evt_done. unfold rat_free_buf. do 16 eexists. split; [reflexivity|]. split; [exact FRM|].
    split; [unfold drv_status; destruct (d_sc d <? 0); [cbn; lia| destruct fl; cbn; lia]|].
    split; [exact OK|]. split; [exact FR|]. split; [exact MI|]. split; [exact RS|]. split; [exact AUX|]. split; [exact SE|]. split; [exact CJ|].
    split; [exact DB|]. split; [exact DBL|]. split; [exact HP|]. split; [exact SOF|]. split; [exact ERR| exact ST'].
  Qed.

  #[using="CEIL"] Lemma main_ret_exit : forall st s LB m ms, valid_sp sp0 -> 0 < TID < 4194304 -> rat_main_ret st s LB m ms ->
    evt rsegs (rat_exit st s) ms.
  Proof.
    intros st s LB m ms VSP HT (x1 & t0 & t1 & t2 & x9 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x18 & x19 & x20 & x21 & t3 & t4 & t5 & t6 & F & fc & mpad
                              & -> & HST & FR & MI & RS & HP & SOF & SE & ST).
    eapply (main_return sp0 argv TID VSP CEIL HT st s LB); [exact FR| unfold LO; replace (usp0 - 8388608) with (usp0 + -8388608) in ST by lia; first [exact ST| replace (usp0 + -8388608) with (usp0 - 8388608) in ST by lia; exact ST]
      | exact RS| exact HP| exact SOF| apply stderr_wfile0_file; exact SE| exact MI].
  Qed.
End SEAMS.

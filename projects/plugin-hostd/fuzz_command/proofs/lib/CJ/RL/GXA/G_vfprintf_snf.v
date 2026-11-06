(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/CJ/RL/GXA/G_vsnprintf.v, with its module paths, addresses and numbers changed; 341 of its 414 lines of code are new or changed and 293 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied unchanged from plugin-hostd/fuzz_reply lib/CJ/RL/GXA at 568db058c1d; only the module path prefix is rewritten to this harness. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require Import SFModel Arr ITree Nodes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require Import G_towrite G_vfprintf_snf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA Require Import AsanFacts CopyCall VfprintfCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA Require G_printf_core_common.
Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require Import RProgNotJ.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require Import RProgNot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require Import StoreCache.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GXI := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.

Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition VFA_DEPTH : Z := 368 + PC_DEPTH.

Section Img.
  Context {IMG : RImg}.

Definition vfprintf_snf_a_post (INV : mem -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp CK D N : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
                    (fjunk : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom img_segs)
    /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells img_segs m' D [CB dn (zb (firstn (Z.to_nat N) o) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (Z.min (zlength o) N))) junkd)]
    /\ rw_cells img_segs m' CK [C8 (Z_to_bv 64 (D + Z.min (zlength o) N)); C8 (Z_to_bv 64 (N - Z.min (zlength o) N))]
    /\ rw_cells img_segs m' Fp [CB 232 fjunk]
    /\ INV m'.

Lemma vfprintf_snf_a_post_plain : forall (INV : mem -> Prop) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
    Fp CK D N dn junkd r o lo canary m ms',
  vfprintf_snf_a_post INV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary m ms' ->
  vfprintf_snf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary m ms'.
Proof.
  intros until ms'.
  intros (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & fc' & fjunk & m' &
          E & MU & WM & MI & FRM & FOK & ST & SSP & DC & CKC & FC & _).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, Ft, fc', fjunk, m'.
  repeat (split; [assumption|]). assumption.
Qed.

Fixpoint args_pf (m : mem) (slots : list word) (args : list parg) : Prop :=
  match args with
  | [] => True
  | a :: args' => match slots with
                  | [] => True
                  | w :: slots' => match a with PA_s s => pf_rng m (bv_unsigned w) (zlength s + 1) | _ => True end
                                   /\ args_pf m slots' args'
                  end
  end.

Lemma args_ok_pf : forall (Fp B BS RC RCS RE RES : Z) (m : mem) (lo sp ap : Z) (ws : list word) (args : list parg),
  GXI.args_ok Fp B BS RC RCS RE RES m lo sp ap ws args -> args_pf m ws args ->
  args_ok Fp B BS RC RCS RE RES m lo sp ap ws args.
Proof.
  intros Fp B BS RC RCS RE RES m lo sp ap ws args. revert ws.
  induction args as [|a args IH]; intros ws H P; [destruct ws; exact I|].
  destruct ws as [|w ws]; [exact H|].
  destruct H as [H1 H2]. destruct P as [P1 P2].
  split; [|exact (IH ws H2 P2)].
  destruct a as [s|i|u|d|l]; try exact H1.
  destruct H1 as (slack & BY & HS & PAD & NZ & D1 & D2 & D3 & D4 & D5 & D6).
  exists slack. repeat (split; [assumption|]). exact P1.
Qed.

Lemma pc_guard_weaken : forall orR sR stR (Iv : mem -> Prop) (m : mem) (lo q q' : Z) (W W' : list (Z * Z)),
  pc_guard orR sR stR Iv m lo q W' -> q' = q -> sub_fp W W' -> pc_guard orR sR stR Iv m lo q' W.
Proof.
  intros orR sR stR Iv m lo q q' W W' G -> S m' MU WM.
  exact (G m' (munch_weaken W W' m m' S MU) WM).
Qed.

Lemma fpcall_snf_a : forall (Fp B BS RC RCS RE RES : Z) (SINK : mem -> list Z -> Prop) (TOPOK : Z -> Prop) c,
  fpcall_stmt Fp B BS RC RCS RE RES SINK TOPOK OUTFP_snf c.
Proof.
  intros Fp B BS RC RCS RE RES SINK TOPOK [[[[y w] p] fl] t]. cbn.
  intros. unfold implM. cbn. apply evt_done. exact I.
Qed.

Lemma fpcalls_snf_a : forall (Fp B BS RC RCS RE RES : Z) (SINK : mem -> list Z -> Prop) (TOPOK : Z -> Prop) cs,
  Forall (fpcall_stmt Fp B BS RC RCS RE RES SINK TOPOK OUTFP_snf) cs.
Proof. intros. apply Forall_forall. intros c _. apply fpcall_snf_a. Qed.

Lemma topok_snf_a : forall TOP, topok_stmt (TOPOK_snf TOP).
Proof. intros TOP a b H1 H2. unfold TOPOK_snf in *. lia. Qed.

Section SnfFlushA.
  Variable copy_ready : mem -> Z -> Z -> Z -> Z -> Prop.
  Variables (Fp : Z) (fl0 : byte) (j1 jm jr js jt jx jy : list byte) (lbfw : word)
            (B CK D : Z) (dn : nat) (junkd : list byte) (N TOP OM : Z).

  Definition snf_flush_a_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (o : list Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (bj : list byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom img_segs)
      /\ munch [(bv_unsigned sp - SN_WRITE_DEPTH, bv_unsigned sp); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (CK, CK + 16);
                (D, D + Z.of_nat dn)] m m'
      /\ wmono img_segs m m' /\ mem_inv img_segs m'
      /\ stk img_segs m' (bv_unsigned sp - SN_WRITE_DEPTH) (bv_unsigned sp)
      /\ length bj = 80%nat
      /\ wfile m' Fp fl0 j1 (snf_j2 jm jr js jt B) lbfw B [] bj
      /\ rw_cells img_segs m' (Fp + 148) [CB 4 jx; C8 (Z_to_bv 64 CK); CB 72 jy]
      /\ rw_cells img_segs m' CK [C8 (Z_to_bv 64 (D + Z.min (zlength o) N)); C8 (Z_to_bv 64 (N - Z.min (zlength o) N))]
      /\ rw_cells img_segs m' D [CB dn (zb (firstn (Z.to_nat N) o) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (Z.min (zlength o) N))) junkd)].

  Definition snf_flush_a_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (o : list Z),
      SINK_snf Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM m o ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 0 ->
      stk img_segs m (bv_unsigned sp - SN_WRITE_DEPTH) (bv_unsigned sp) -> SN_WRITE_DEPTH <= bv_unsigned sp ->
      bv_unsigned sp <= TOP ->
      (D + Z.of_nat dn <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= D) ->
      mem_inv img_segs m ->
      sn_write_ready copy_ready m (bv_unsigned sp) Fp CK D (Z.of_nat dn) B SNF_CAP 0 0 ->
      evt img_segs (snf_flush_a_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (sym K_SN_WRITE)) fc None m (seg_rom img_segs)).
End SnfFlushA.

Definition printf_core_a_all (set_ready : mem -> Z -> Z -> Z -> Prop) (strn_ready : mem -> Z -> Z -> Z -> list byte -> Prop) : Prop :=
  forall (St : Type) (Fp B BS RC RCS RE RES : Z) (SINK : mem -> St -> Prop) (TOPOK : Z -> Prop)
         (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z) (out_ready : mem -> Z -> Z -> Z -> Prop)
         (INV : mem -> Prop),
    sink_frame_stmt Fp B BS RC RCS RE RES SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK ->
    out_a_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT out_ready ->
    printf_core_a_stmt Fp B BS RC RCS RE RES SINK TOPOK OUT OUTFP out_ready set_ready strn_ready INV.

Definition vf_snf_fp (lo q Fp CK D : Z) (dn : nat) : list (Z * Z) :=
  [(lo, q); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)].

  Variable out_ready : Z -> Z -> Z -> Z -> nat -> mem -> Z -> Z -> Z -> Prop.
  Variable set_ready : mem -> Z -> Z -> Z -> Prop.
  Variable strn_ready : mem -> Z -> Z -> Z -> list byte -> Prop.
  Variable copy_ready : mem -> Z -> Z -> Z -> Z -> Prop.
  Variable INV : mem -> Prop.

Definition vf_snf_guard (m : mem) (q lo Fp CK D : Z) (dn : nat) (A : Z) (fmt : list Z) (slots : list word)
    (args : list parg) : Prop :=
  forall m1, munch (vf_snf_fp lo q Fp CK D dn) m m1 -> wmono img_segs m m1 ->
    pf_rng m1 A (zlength fmt) /\ musl_prefix_addressable m1 /\ args_pf m1 slots args
    /\ pc_guard (out_ready Fp (q - 352) CK D dn) set_ready strn_ready INV m1 lo (q - 368) (vf_snf_fp lo q Fp CK D dn)
    /\ sn_write_ready copy_ready m1 (q - 368) Fp CK D (Z.of_nat dn) (q - 352) SNF_CAP 0 0.

Definition vfprintf_snf_a_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (Fp CK D N OM bufp A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells img_segs m Fp (snf_file bufp CK) ->
    rw_cells img_segs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 N)] ->
    rw_cells img_segs m D [CB dn (Z_to_bv 8 0 :: skipn 1 junkd)] -> length junkd = dn ->
    bytes_at img_segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> GXI.args_ok Fp lo 0 CK 16 D (Z.of_nat dn) m lo q lo slots args ->
    printf_model (OUT_snf OM) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, o)) ->
    0 <= N < 2^63 -> 0 <= OM -> Z.min N OM < Z.of_nat dn -> 0 < bufp < 2^64 ->
    stk img_segs m lo q -> lo <= q - VFA_DEPTH -> GLOBALS_TOP <= lo -> q < 2^63 ->
    ssp_cells m canary -> mem_inv img_segs m -> frm0 fc ->
    A + zlength fmt <= sym 0x22e18 -> 65536 <= A ->
    q <= Fp -> Fp + 232 <= CK -> CK + 16 <= VA -> CK + 16 < 2^63 -> VA + 8 * zlength slots <= 2^64 ->
    0 < D -> D + Z.of_nat dn < 2^63 ->
    (D + Z.of_nat dn <= lo \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    vf_snf_guard m q lo Fp CK D dn A fmt slots args ->
    evt img_segs (vfprintf_snf_a_post INV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x7f000400)) fc None m (seg_rom img_segs)).

Definition vf_ready_a : vf_guard :=
  fun m q lo Fp CK D dn N bufp A VA fmt slots args =>
    A + zlength fmt <= sym 0x22e18 /\ vf_snf_guard m q lo Fp CK D dn A fmt slots args.

  Context {CODE_vfprintf : CodeAtT img_segs (sym 0x7f000400) (PROGAT_CODE_vfprintf IMG)}.
  Context {RB_vfprintf : RelCode (sym 0x7f000400) 432}.
  Context {RN_printf_core : RelNear (sym 0x7f000400) (sym 0x18704)}.
  Context {RN_lockfile : RelNear (sym 0x7f000400) (sym 0x7f000700)}.
  Context {RN_towrite : RelNear (sym 0x7f000400) (sym 0x17f40)}.
  Context {RN_unlockfile : RelNear (sym 0x7f000400) (sym 0x7f000800)}.
  Context {RN_stack_chk_fail : RelNear (sym 0x7f000400) (sym 0x15f04)}.
  Context {CODE_towrite : CodeAtT img_segs (sym 0x17f40) (PROGAT_CODE_towrite IMG)}.
  Context {RB_towrite : RelCode (sym 0x17f40) 84}.
  Context {RS_got_ssp : RelSym (sym 0x22e18)}.
  Context {RS_snw : RelSym (sym K_SN_WRITE)}.
  Context {RB_snw : RelCode (sym K_SN_WRITE) 220}.
  Context {RS_34288 : RelSym (sym 0x34288)}.
  Context {RS_35000 : RelSym (sym 0x35000)}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)}.
  Context {RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000)}.
  Let rp_22e18 : 0 <= sym 0x22e18 < 2^30 := @rel_sym_pf _ RS_got_ssp.
  Let rp_snw : 0 <= sym K_SN_WRITE < 2^30 := @rel_sym_pf _ RS_snw.
  Let rp_34288 : 0 <= sym 0x34288 < 2^30 := @rel_sym_pf _ RS_34288.
  Let rp_35000 : 0 <= sym 0x35000 < 2^30 := @rel_sym_pf _ RS_35000.
  Let rl0_0 : sym 0x22e18 + 8 <= sym 0x34288 := @zfact_pf _ RL0_0.
  Let rl0_1 : sym 0x34288 + 8 <= sym 0x35000 := @zfact_pf _ RL0_1.
  Context (PC : printf_core_a_all set_ready strn_ready).
  Context (PC1 : forall INV' : mem -> Prop, printf_core1_a_stmt INV').
  Context (SNF_FRAME : forall Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM,
            sink_frame_stmt Fp B 80 CK 16 D (Z.of_nat dn) (SINK_snf Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM)).
  Context (SNF_FLAGS : forall Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM,
            sink_flags_stmt Fp (SINK_snf Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM)).
  Context (SNF_OUT : forall Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM,
            out_a_stmt Fp B 80 CK 16 D (Z.of_nat dn) (SINK_snf Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM)
                       (TOPOK_snf TOP) (OUT_snf OM) (out_ready Fp B CK D dn)).
  Context (SNF_FLUSH : forall Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM,
            snf_flush_a_stmt copy_ready Fp fl0 j1 jm jr js jt jx jy lbfw B CK D dn junkd N TOP OM).

Theorem vfprintf_snf_a_proof : vfprintf_snf_a_stmt.
Proof.
  unfold vfprintf_snf_a_stmt. intros until o. cbv zeta.
  intros -> -> -> FH CKC DST LJ BY HF P1 VAA AOK MODEL HN HOM HDN HBP ST LO GLO QHI SSP MI FRM HA HA0 QF FCK CKV CKHI VAHI D0 DHI DD1 DD2 GRD.
  unfold VFA_DEPTH, PC_DEPTH, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. unfold zb in AB. rewrite length_map in AB.
  pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  pose proof rp_22e18. pose proof rp_snw. pose proof rp_34288. pose proof rp_35000. pose proof rl0_0. pose proof rl0_1.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU2.
  stash BY. stash VAA. stash AOK. stash MODEL. stash DST. stash CKC. stash GRD.
  unfold snf_file in FH.
  carve_frame 368%nat ST.
  do 25 zs.
  assert (BY0 : bytes_at img_segs m0 A (zb fmt)).
  { unfold hideP in BY. eapply bytes_at_transport; [exact BY | exact MU |]. cbn [disjoint_from]. unfold zb. rewrite length_map. lia. }
  zs.
  eapply evt_cut.
  { eapply (PC1 (fun _ => True)); rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, zlength;
      [ exact BY0 | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
      | split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia | intros ? ? ?; exact I ]. }
  cbv beta. intros ms' P. clear BY0. unfold printf_core1_a_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 21%nat; intros x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m1 -> MUc WMc MIc STc SSPc).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m1 MUc WMc; clear MUc WMc; try clear MI end.
  aret_pc.
  clear SSP1 SSP2. destruct SSPc as [[SSP1 SSP2] _]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  zs. if_lit. zs. zs. if_lit. zs. do 4 zs. zs. if_lit.
  do 9 zs. zs.
  replace (Z.land (bv_unsigned (sx32 (Z_to_bv 64 0))) 18446744073709551583) with 0 in * by (vm_compute; reflexivity).
  assert (FH2 : rw_cells img_segs m1 Fp (snf_file2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                         (bv_unsigned sp + -352) 80 (Z_to_bv 64 0) CK)) by exact FH.
  clear FH. apply file_to_tw in FH2.
  eapply evt_cut.
  { eapply towrite_x_proof; rewrite ?unsigned_lit by lia; [exact FH2 | vm_compute; reflexivity | lia | lia | lia | assumption]. }
  cbv beta. intros ms' P. clear FH2. rewrite !unsigned_lit in P by lia.
  (nelim P 21%nat; intros x5' x6' x7' c1 c2 c3 c4 c5 c6 c7 x28' x29' x30' x31' mode' m2 -> MUc WMc MIt FHt).
  apply tw_to_file in FHt.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m2 MUc WMc; clear MUc WMc; try clear MIc end.
  aret_pc.
  zs. if_lit. do 5 zs. zs.
  set (B := bv_unsigned sp + -352) in *.
  apply (rw_cells_split_CB img_segs _ _ [_; _] 248 _ _ [80; 168]%nat) in FR; [|reflexivity]. cbn [app mk_CB_cells] in FR.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in FR. destruct FR as [AP2 FR]. cbn [cells_size csize Nat.add app] in FR.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in FR. destruct FR as [BUFc FR]. cbn [cells_size csize Nat.add app] in FR.
  replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8) with B in BUFc by (unfold B; lia).
  replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80) with (bv_unsigned sp + -272) in FR by (unfold B; lia).
  replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in AP2 by lia.
  match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
  pose proof (OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX.G_printf_core_common.rw_CB_length _ _ _ _ BUFc) as LJB.
  apply (rw_cells_split_CB img_segs _ _ [] 80 _ [] [0; 80]%nat) in BUFc; [|reflexivity]. cbn [app mk_CB_cells] in BUFc.
  change (firstn 0 jb) with (@nil byte) in BUFc. change (skipn 0 jb) with jb in BUFc.
  rewrite (firstn_all2 (n := 80%nat) jb) in BUFc by (rewrite LJB; apply Nat.le_refl).
  apply file_to_sink in FHt. destruct FHt as [FILE1 R148].
  unfold hideP in BY, VAA, AOK, MODEL, DST, CKC.
  unfold hideP in GRD. destruct (GRD _ MU WM) as (PF2 & MP2 & APF2 & PGm & _). stash GRD.
  replace (bv_unsigned sp - 352) with B in PGm by (unfold B; lia).
  assert (BY2 : bytes_at img_segs m2 A (zb fmt)).
  { eapply bytes_at_transport; [exact BY | exact MU2 |]. cbn [disjoint_from]. unfold zb. rewrite length_map. lia. }
  assert (VAA2 : bytes_at img_segs m2 VA (u64s slots)).
  { eapply bytes_at_transport; [exact VAA | exact MU2 |]. cbn [disjoint_from]. rewrite LU. lia. }
  assert (CKC2 : rw_cells img_segs m2 CK [C8 (Z_to_bv 64 (D + Z.min (zlength (@nil Z)) N)); C8 (Z_to_bv 64 (N - Z.min (zlength (@nil Z)) N))]).
  { replace (Z.min (zlength (@nil Z)) N) with 0 by (unfold zlength; cbn; lia). rewrite Z.add_0_r, Z.sub_0_r.
    eapply rw_cells_transport; [exact CKC | exact MU2 | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  assert (DST2 : rw_cells img_segs m2 D [CB dn (zb (firstn (Z.to_nat N) (@nil Z)) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (Z.min (zlength (@nil Z)) N))) junkd)]).
  { replace (Z.min (zlength (@nil Z)) N) with 0 by (unfold zlength; cbn; lia). rewrite firstn_nil. cbn [zb map app Z.to_nat].
    eapply rw_cells_transport; [exact DST | exact MU2 | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  assert (AOK1 : GXI.args_ok Fp B 80 CK 16 D (Z.of_nat dn) m2 lo (bv_unsigned sp + -368) (bv_unsigned sp + -368) slots args).
  { eapply args_ok_rebase; [exact AOK | exact MU | lia | right; reflexivity | left; unfold B; lia | right; split; reflexivity | left; lia]. }
  pose proof (args_ok_pf _ _ _ _ _ _ _ _ _ _ _ _ _ AOK1 APF2) as AOK2.
  clear MU2 BY VAA AOK CKC DST AOK1 APF2.
  assert (WF : wfile m2 Fp (Z_to_bv 8 0) snf_j1 (snf_j2 snf_jz snf_jz snf_jz (snf_jt mode') B) (Z_to_bv 64 (-1)) B (zb []) jb).
  { unfold wfile. cbn [zb map length Z.of_nat]. rewrite LJB.
    replace (B + Z.of_nat 0 + Z.of_nat 80) with (B + 80) by lia. replace (B + Z.of_nat 0) with B by lia.
    split; [exact FILE1|]. split; [exact BUFc|]. split; [vm_compute; reflexivity|].
    split; [apply Z.leb_le; vm_compute; reflexivity|]. unfold B. lia. }
  assert (SNK : SINK_snf Fp (Z_to_bv 8 0) snf_j1 snf_jz snf_jz snf_jz (snf_jt mode') snf_jx snf_jy (Z_to_bv 64 (-1))
                         B CK D dn junkd N (bv_unsigned sp + -368) OM m2 []).
  { exists [], [], jb. cbv zeta.
    split; [reflexivity|].
    split; [unfold SNF_CAP, zlength; rewrite LJB; reflexivity|].
    split; [apply length_le8|]. split; [apply length_le8|]. split; [apply length_le8|].
    split; [unfold snf_jt; rewrite ?length_app, ?length_le4, ?length_le8; reflexivity|].
    split; [apply length_le4|]. split; [unfold snf_jy; rewrite ?length_app, ?length_le8; reflexivity|].
    split; [exact WF|]. split; [exact R148|]. split; [exact CKC2|]. split; [exact DST2|].
    split; [exact LJ|].
    unfold SNF_CAP, B. repeat split; unfold zlength in *; cbn [length] in *; lia. }
  assert (PCALL : forall Q ms, implM img_segs (printf_model (OUT_snf OM) OUTFP_snf fmt args) [] Q ms -> evt img_segs (Q r o) ms).
  { intros Q ms HQ. unfold implM in HQ. rewrite MODEL in HQ. exact HQ. }
  pose proof (SNF_FRAME Fp (Z_to_bv 8 0) snf_j1 snf_jz snf_jz snf_jz (snf_jt mode') snf_jx snf_jy (Z_to_bv 64 (-1)) B CK D dn junkd N (bv_unsigned sp + -368) OM) as SFR.
  pose proof (SNF_FLAGS Fp (Z_to_bv 8 0) snf_j1 snf_jz snf_jz snf_jz (snf_jt mode') snf_jx snf_jy (Z_to_bv 64 (-1)) B CK D dn junkd N (bv_unsigned sp + -368) OM) as SFL.
  pose proof (SNF_OUT Fp (Z_to_bv 8 0) snf_j1 snf_jz snf_jz snf_jz (snf_jt mode') snf_jx snf_jy (Z_to_bv 64 (-1)) B CK D dn junkd N (bv_unsigned sp + -368) OM) as SOUT.
  pose proof (PC (list Z) Fp B 80 CK 16 D (Z.of_nat dn) _ _ (OUT_snf OM) OUTFP_snf (out_ready Fp B CK D dn) INV
                 SFR SFL (topok_snf_a (bv_unsigned sp + -368)) SOUT) as PC2.
  unfold printf_core_a_stmt in PC2.
  eapply evt_cut.
  { apply PCALL. destruct DD1 as [DD1 | DD1]; [destruct DD2 as [DD2 | DD2] |];
    eapply PC2 with (st := []) (VA := VA) (i := 0) (slots := slots) (args := args) (lo := lo) (canary := canary);
    rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, TOPOK_snf, zlength;
    first [ exact SNK | exact BY2 | exact HF | reflexivity | (replace (VA + 8 * 0) with VA by lia; exact APC)
          | exact VAA2 | (cbn [Z.to_nat skipn]; exact AOK2) | apply fpcalls_snf_a | exact STc
          | (split; [exact SSP1 | exact SSP2]) | exact PF2 | exact MP2
          | (eapply pc_guard_weaken; [exact PGm | lia | unfold vf_snf_fp, SR, sub_fp; cbn [outside]; intros; unfold B; lia])
          | assumption | exact FRM | lia
          | (left; split; lia) | (right; left; repeat split; lia) | (right; right; repeat split; lia)
          | (right; repeat split; lia) | (repeat split; lia) ]. }
  cbv beta. intros ms' P. clear PC2 PCALL PF2 MP2 PGm.
  unfold printf_core_a_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 29%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' apv m3 -> MUc WMc MI3 FRM' FOK ST3 SNK3 SSP3 APC3 Hr).
  destruct Hr as [Hr _].
  unfold SR in MUc. cbn [app] in MUc.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m3 MUc WMc; clear MUc WMc; try clear MIt end.
  aret_pc.
  zs. zs. zs. if_cases Kb; zify_cond Kb. { exfalso. rewrite ?unsigned_lit in Kb by lia. lia. }
  pose proof (sink_write_cell _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SNK3) as W72.
  zs. zs. zs. zs. zs. aret_pc.
  unfold hideP in GRD. destruct (GRD _ MU WM) as (_ & _ & _ & _ & SW3). stash GRD.
  replace (bv_unsigned sp - 368) with (bv_unsigned sp + -368) in SW3 by lia.
  replace (bv_unsigned sp - 352) with B in SW3 by (unfold B; lia).
  destruct (stk_split _ _ _ (bv_unsigned sp + -368 - SN_WRITE_DEPTH) _ ST3 ltac:(unfold SN_WRITE_DEPTH, COPY_DEPTH; lia)) as [ST4a ST4b].
  clear ST3.
  pose proof (SNF_FLUSH Fp (Z_to_bv 8 0) snf_j1 snf_jz snf_jz snf_jz (snf_jt mode') snf_jx snf_jy (Z_to_bv 64 (-1))
              B CK D dn junkd N (bv_unsigned sp + -368) OM) as FLU.
  unfold snf_flush_a_stmt in FLU. unfold SN_WRITE_DEPTH, COPY_DEPTH in *.
  eapply evt_cut.
  { eapply FLU; clear FLU; rewrite ?unsigned_lit by lia;
      [ exact SNK3 | reflexivity | reflexivity | reflexivity | exact ST4b | lia | lia | lia | assumption | exact SW3 ]. }
  clear FLU SW3.
  cbv beta. intros ms' P. unfold snf_flush_a_post in P. unfold SN_WRITE_DEPTH, COPY_DEPTH in P. rewrite !unsigned_lit in P by lia.
  (nelim P 26%nat; intros z5 z6 z7 e1 e2 e3 e4 e5 e6 e7 z28 z29 z30 z31 m4 bj4 -> MUc WMc MI4 ST4b' Lbj4 WF4 R148' CK4 D4).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call img_segs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
  aret_pc.
  destruct WF4 as (FC4 & BUF4 & _).
  match type of FC4 with rw_cells _ _ _ (FILE_cells _ _ ?we ?wp _ _) =>
    replace we with (B + 80) in FC4 by (rewrite ?Lbj4; cbn; lia); replace wp with B in FC4 by (cbn; lia) end.
  pose proof (sink_to_file _ _ _ _ _ FC4 R148') as FH5. clear FC4 R148'. unfold snf_file2 in FH5.
  do 16 zs.
  try replace (0 <? B) with true by (symmetry; apply Z.ltb_lt; unfold B; lia).
  try replace (Z.land (bv_unsigned (sx32 (Z_to_bv 64 0))) 32) with 0 by (vm_compute; reflexivity).
  try replace (bv_unsigned (sx32 (Z_to_bv 64 0))) with 0 by (vm_compute; reflexivity).
  try replace (Z.land (bv_swrap 32 (Z.b2z true + -1)) 18446744073709551615) with 0 by (vm_compute; reflexivity).
  try replace (Z.land (bv_swrap 32 (Z.b2z (0 <? 1) + -1)) 18446744073709551615) with 0 by (vm_compute; reflexivity).
  rewrite ?Z.lor_0_l.
  zs. if_lit.
  zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
  do 9 zs.
  replace (Z.land r 18446744073709551615) with r
    by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; unfold INT_MAX in Hr; lia).
  unfold B in *.
  pose proof (stk_merge _ _ _ _ _ ST4a ST4b' ltac:(lia)) as ST5. clear ST4a ST4b'.
  cbn [length] in BUF4. rewrite Lbj4 in BUF4.
  release_frame APC3 ST5 (bv_unsigned sp + -360).
  release_frame AP2 ST5 (bv_unsigned sp + -352).
  release_frame BUF4 ST5 (bv_unsigned sp + -272).
  release_frame FR ST5 (bv_unsigned sp).
  destruct (rw_cells_forget _ _ _ _ FH5) as [fjunk FJ]. cbn [cells_size csize Nat.add] in FJ.
  unfold hideP in GRD. destruct (GRD _ MU WM) as (_ & _ & _ & PGf & _).
  pose proof (proj1 (PGf _ (munch_refl _ _) (wmono_refl _ _))) as INVf.
  apply evt_done. unfold vfprintf_snf_a_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI4|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST5|]. split; [split; [exact SSP1 | exact SSP2]|].
  split; [exact D4|]. split; [exact CK4|]. split; [exact FJ|]. exact INVf.
Qed.

Lemma vfprintf_snf_a_guarded : vfprintf_guarded_stmt vf_ready_a.
Proof.
  unfold vfprintf_guarded_stmt. intros until o. cbv zeta.
  intros E0 E1 E2 FH CKC DST LJ BY HF P1 VAA AOK MODEL HN HOM HDN HBP ST LO GLO QHI SSP MI FRM [HA GRD] HAG HA0
         QF FCK CKV CKHI VAHI D0 DHI DD1 DD2.
  pose proof vfprintf_snf_a_proof as V. unfold vfprintf_snf_a_stmt in V. cbv zeta in V.
  eapply evt_mono.
  { refine (V ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              Fp CK D N OM bufp A VA dn junkd fmt slots args lo canary r o
              E0 E1 E2 FH CKC DST LJ BY HF P1 VAA AOK MODEL HN HOM HDN HBP ST _ _ QHI SSP MI FRM HA HA0
              QF FCK CKV CKHI VAHI D0 DHI DD1 _ GRD);
      unfold VFA_DEPTH, PC_DEPTH, GLOBALS_TOP, GXI.VF_DEPTH, GXI.GLOBALS_TOP in *; lia. }
  intros ms' P. eapply vfprintf_snf_a_post_plain. exact P.
Qed.

End Img.

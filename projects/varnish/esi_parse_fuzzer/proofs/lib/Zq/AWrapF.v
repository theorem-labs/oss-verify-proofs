(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac AMallocI AMallocA AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt2gfb ARt22fz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt2gfb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeH0 AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB1 AFreeB2 ATransp AFreeB3 AFreeB4 AFreeB5 ACoresk AWrapKit AIaShell.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx.ARt27j4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2gfb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt22fz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2gfb.AFreeM0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT.AFreeN OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AWrapKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIaShell.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac mem_side := cbn; first [ (let E := fresh "E" in intros E; discriminate E) | solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ exact I | reflexivity ] ] | solve [ repeat first [ left; reflexivity | right ] ] | tauto ].
Local Ltac mem_hyp Hr := cbn in Hr; first [ solve [ repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); first [ discriminate Hr | destruct Hr ] ] | intuition discriminate ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
Section OBLV.
Context {Clg : Ceiling}.
Definition pa_free_obligationV : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (p n0 : Z) (T : TSet),
      let v := aview_of (pa_hull A) m in
      @pa_ainv _ DepotRepL A m md -> mem_inv (cl_segs LPA) v ->
      a0 = wz p -> ((p = 0 /\ n0 = 0) \/ as_live A p = Some n0) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites LPA) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AState) (m' : mem) (md' : Model),
          let v' := aview_of (pa_hull A') m' in
          @pa_ainv _ DepotRepL A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          hull_le (pa_hull A) (pa_hull A') \/ True ->
          (forall ff, as_fframe A' ff = as_fframe A ff) ->
          as_live A' p = None -> (forall q, q <> p -> as_live A' q = as_live A q) ->
          as_livebytes A' = as_livebytes A - n0 -> as_tinycred A' = as_tinycred A -> as_seccred A' = as_seccred A -> as_primcred A' = as_primcred A (* [comment removed for export] *) ->
          as_nlive A' = as_nlive A - (if Z.eqb p 0 then 0 else 1) ->
          (forall c, c <> kQuarantineBatchClass -> a_virgin A c -> a_virgin A' c) ->
          (forall i, 0 <= i < 4 -> mrd (cl_segs LPA) v' (wz (cl_errno LPA + i)) = mrd (cl_segs LPA) v (wz (cl_errno LPA + i))) ->
          frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK (newblk p n0) nowhere
                   (aview_of (pa_hull A) m) v' ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' (seg_rom (cl_segs LPA))) md') T) ->
      srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_free_pc LPA) fc None m (seg_rom (cl_segs LPA))) md) T.

Lemma pa_free_of_V : pa_free_obligationV -> @pa_free_obligation _ DepotRepL.
Proof.
  intros V. unfold pa_free_obligation.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 T.
  cbv zeta. intros AI MI A0 LV TP SPA RA4 SITE S0C CEIL SM KK0.
  eapply (V ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 T
            AI MI A0 LV TP SPA RA4 SITE S0C CEIL SM).
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' v' X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 XPC X11 VG X12 X13.   (* [comment removed for export] *)
  exact (KK0 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 XPC X11 X12 X13).
Qed.
End OBLV.

Lemma pa_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma set_ia_same : forall A b, a_ia_inited A = b -> set_ia A b = A.
Proof. intros A b E. destruct A; cbn in E |- *. subst b. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fshell1_W (ia0 : bool) (fp thr : Z) : list (Z * Z) :=
  [(fp - 2128 - 224, fp); (thr + off_th_unwinding, thr + off_th_unwinding + 1)] ++ ia_Wk ia0.

Section Shell1.
Context {Clg : Ceiling}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo p tsd ctx thr top bot : Z) (ia0 : bool).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 2688.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis RA0 : 4096 <= bv_unsigned ra.
  Hypothesis RANE : bv_unsigned ra <> 0x58994.
  Hypothesis VLE : bv_unsigned s0 <= bv_unsigned sp.
  Hypothesis TOPR : 0 <= top < 2^64.
  Hypothesis BOTR : 0 <= bot < 2^64.
  Hypothesis TPE : tp = Z_to_bv 64 TP.
  Hypothesis FCo : free_consts m.
  Hypothesis PCo : poison_consts m.
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TTB : rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)].
  Hypothesis TDT : ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)].
  Hypothesis TUNW : rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  (* [comment removed for export] *)
  Hypothesis PZ : (p = 0 /\ ro_cells rsegs m 0xb5dc8 [C8 (wz 0)])
                  \/ (0 < p /\ aobj (p + -16) 16 /\ p < alloc_ceiling /\ ro_cells rsegs m (0xb5dc8 + 8 * Z.shiftr p 32) [C8 (wz 0)]).
  (* [comment removed for export] *)
  Hypothesis IA : ia_pre ia0 m.

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).

  #[using="IA PZ TUNW TDT TTB TSDL TC PCo FCo TPE BOTR TOPR VLE RANE RA0 SPH SPA LO ST MI ctx tsd Clg"] Lemma free_shell1 : forall (Q : machine_state -> Prop),
    (forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (pad jb1 jrest : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (fp + -2128) [C8 (wz (fp + -2128 + 16))] ->
        rw_cells rsegs m' (fp + -2128 + 32) [CB 2024 jrest] ->
        rw_cells rsegs m' (fp + -2128 + 2056) [C8 (wz fp)] ->
        rw_cells rsegs m' (fp + -2128 + 8) [C4 (wz (dep_w8 top bot fp))] ->
        rw_cells rsegs m' (fp + -2128 + 16) [C8 (wz 0x58994); CB 8 (dep_b16 top bot fp ra jb1)] ->
        rw_cells rsegs m' (fp + -2128 + 12) [C4 (wz 0)] ->
        rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        ia_post ia0 m' ->
        munch (fshell1_W ia0 fp thr) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (fp - 2128) ->
        evt rsegs Q (MS (mkR (wz 0x58a04) (wz (fp + -2128)) gp tp t0' t1' t2' (wz fp) (wz p)
                         (wz 0xb1558) (wz p) (wz 0) (wz 0) (wz (fp + -2128)) (wz 1) a6' a7'
                         (wz 0x58994) (wz 1) (wz (fp + -2128)) (wz (fp + -81)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz dealloc_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x5884c) fc None m (seg_rom rsegs)).
  Proof.
    intros Q K.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof FCo as FC'. (first [ dand9 FC' as Fini Fmcs Fgotcf Ffu Fhook Fgotfl Fffs Fqmax Fcmax | destruct FC' as (Fini & Fmcs & Fgotcf & Ffu & Fhook & Fgotfl & Fffs & Fqmax & Fcmax) ]).
    unfold QINST, kHighMemBeg, off_th_unwinding in *.
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    rewrite TPL in *. change (6192088 - 88) with 6192000 in Ctsd.
    clear Ccan Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Fhook Fgotfl Fffs Fqmax Fcmax.
    (* [comment removed for export] *)
    amz.
    (* [comment removed for export] *)
    eapply free_pro_ok; [exact MI| exact ST| lia|].
    intros junk pad m1 FRO SAV MU1 WM1 MI1 ST1.
    rewrite ?unsigned_lit in FRO, SAV, MU1, ST1 by lia.
    xfer Cini MU1 WM1. xfer Ckey MU1 WM1. xfer Ctsd MU1 WM1. xfer Cctx MU1 WM1. xfer Cthr2 MU1 WM1.
    xfer Cgotcf MU1 WM1. xfer Cgotps MU1 WM1. xfer Cps MU1 WM1.
    xfer Fini MU1 WM1. xfer Fmcs MU1 WM1. xfer Fgotcf MU1 WM1. xfer Ffu MU1 WM1.
    xfer TTB MU1 WM1. xfer TDT MU1 WM1. xfer TUNW MU1 WM1.
    assert (PZ1 : (p = 0 /\ ro_cells rsegs m1 0xb5dc8 [C8 (wz 0)])
                  \/ (0 < p /\ aobj (p + -16) 16 /\ p < alloc_ceiling /\ ro_cells rsegs m1 (0xb5dc8 + 8 * Z.shiftr p 32) [C8 (wz 0)])).
    { destruct PZ as [[P0 IAM]|(P1 & P2 & P3 & IAM)].
      - left. split; [exact P0|]. xfer IAM MU1 WM1. exact IAM.
      - right. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
        assert (IAMR : 0 <= Z.shiftr p 32 < 2^15).
        { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2^32 * 2^15) with (2^47). lia. }
        xfer IAM MU1 WM1. exact IAM. }
    assert (IA1 : ia_pre ia0 m1).
    { destruct ia0; cbn [ia_pre] in IA |- *.
      - xfer IA MU1 WM1. exact IA.
      - destruct IA as (I1 & I2 & I3 & I4 & I5 & I6). unfold ia_pre0, IAB in *.
        xfer I1 MU1 WM1. xfer I2 MU1 WM1. xferb I3 MU1 WM1. xferb I4 MU1 WM1. xferb I5 MU1 WM1. xferb I6 MU1 WM1.
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }
    clear PZ IA MI ST.
    assert (MU : munch [(fp - 2128 - 224, fp); (thr + 3168, thr + 3168 + 1)] m m1).
    { eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    pose proof WM1 as WM. clear MU1 WM1.
    (* [comment removed for export] *)
    assert (IAC : evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR (wz 0x58890) (wz (fp + -2128)) gp tp t0' t1' t2' sp (wz p) (wz 0xb5dc0) a1' a2' a3' a4' a5' a6' a7'
                              ra s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc (wz 0x58890)) fc None m' (seg_rom rsegs)
                 /\ munch ((fp - 2128 - 48, fp - 2128) :: ia_Wk ia0) m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo (fp - 2128) /\ ia_post ia0 m')
        (MS (mkR (wz 0x58890) (wz (fp + -2128)) gp tp t0 t1 t2 sp (wz p) (wz p) a1 a2 a3 a4 a5 a6 a7
                            ra s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz ia_entry) fc None m1 (seg_rom rsegs))).
    { destruct ia0; cbn [ia_pre ia_post ia_Wk] in IA1 |- *.
      - eapply evt_cut; [eapply (ia_fast_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo)|];
          [exact MI1| rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; lia| lia| exact IA1| reflexivity|].
        intros ms' PO. destruct_exs PO. (first [ dand5 PO as E MUc WMc MI2 ST2 | destruct PO as (E & MUc & WMc & MI2 & ST2) ]). subst ms'. rewrite ?unsigned_lit in MUc, ST2 by lia.
        apply evt_done. hot_eexists_all. split; [reflexivity|].
        unfold IAB. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [exact MUc| exact WMc| exact MI2| exact ST2| exact I].
      - (first [ dand6 IA1 as I1 I2 I3 I4 I5 I6 | destruct IA1 as (I1 & I2 & I3 & I4 & I5 & I6) ]). unfold IAB in *.
        eapply evt_cut; [eapply (ia_init_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 0 lo
                                   (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) (Z.to_nat 262144)) (repeat (Z_to_bv 8 0) (Z.to_nat 262728)) (repeat (Z_to_bv 8 0) 40) (repeat (wz 0) 432))|];
          [exact MI1| rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; lia| lia| lia| exact I1| exact Cgotps| exact Cps
          | exact I2| exact I3| exact I4| apply repeat_length| exact I5| exact I6| reflexivity|].
        intros ms' PO. destruct_exs PO. (first [ dand11 PO as E MUc WMc MI2 ST2 P1 P2 P3 P4 P5 P6 | destruct PO as (E & MUc & WMc & MI2 & ST2 & P1 & P2 & P3 & P4 & P5 & P6) ]). subst ms'.
        rewrite ?unsigned_lit in MUc, ST2 by lia. unfold IAB in *.
        apply evt_done. hot_eexists_all. split; [reflexivity|].
        unfold ia_W, ia_post0, IAB. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [exact MUc| exact WMc| exact MI2| exact ST2| kcell]. }
    clear IA1. eapply evt_cut; [exact IAC|]. clear IAC.
    intros ms' PO. destruct_exs PO. (first [ dand6 PO as E MUc WMc MI2 ST2 IAP2 | destruct PO as (E & MUc & WMc & MI2 & ST2 & IAP2) ]). subst ms'.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
    assert (MUs : munch [(fp - 2128 - 48, fp - 2128); (0xb5dc0, 0x136df0); (0x144648, 0x14464c)] m1 m2).
    { eapply munch_weaken; [| exact MUc]. unfold sub_fp, ia_Wk, ia_W, IAB. destruct ia0; cbn [outside app]; intros y Hy; lia. }
    xfer Cini MUs WMc. xfer Ckey MUs WMc. xfer Ctsd MUs WMc. xfer Cctx MUs WMc. xfer Cthr2 MUs WMc.
    xfer Cgotcf MUs WMc. xfer Cgotps MUs WMc. xfer Cps MUs WMc.
    xfer Fini MUs WMc. xfer Fmcs MUs WMc. xfer Fgotcf MUs WMc. xfer Ffu MUs WMc.
    xfer TTB MUs WMc. xfer TDT MUs WMc. xfer TUNW MUs WMc. xferb FRO MUs WMc. xfer SAV MUs WMc.
    assert (PZ2 : (p = 0 /\ ro_cells rsegs m2 0xb5dc8 [C8 (wz 0)])
                  \/ (0 < p /\ aobj (p + -16) 16 /\ p < alloc_ceiling /\ ro_cells rsegs m2 (0xb5dc8 + 8 * Z.shiftr p 32) [C8 (wz 0)])).
    { destruct PZ1 as [[P0 IAM]|(P1 & P2 & P3 & IAM)].
      - left. split; [exact P0|]. destruct ia0; cbn [ia_post ia_Wk] in IAP2, MUc.
        + xfer IAM MUc WMc. exact IAM.
        + (first [ dand4 IAP2 as _ _ Q3 _ | destruct IAP2 as (_ & _ & Q3 & _) ]). unfold IAB in Q3. replace 0xb5dc8 with (0xb5dc0 + 8 + 0) by reflexivity. exact (zeros_word_at m2 _ _ 0 Q3 ltac:(lia) ltac:(lia)).
      - right. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
        assert (IAMR : 0 <= Z.shiftr p 32 < 2^15).
        { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2^32 * 2^15) with (2^47). lia. }
        destruct ia0; cbn [ia_post ia_Wk] in IAP2, MUc.
        + xfer IAM MUc WMc. exact IAM.
        + (first [ dand4 IAP2 as _ _ Q3 _ | destruct IAP2 as (_ & _ & Q3 & _) ]). unfold IAB in Q3.
          replace (0xb5dc8 + 8 * Z.shiftr p 32) with (0xb5dc0 + 8 + 8 * Z.shiftr p 32) by lia. exact (zeros_word_at m2 _ _ (8 * Z.shiftr p 32) Q3 ltac:(lia) ltac:(lia)). }
    clear PZ1.
    assert (MU2 : munch (fshell1_W ia0 fp thr) m m2).
    { unfold fshell1_W, off_th_unwinding.
      eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp, ia_Wk, ia_W, IAB; destruct ia0; cbn [outside app]; intros y Hy; lia. }
    pose proof (wmono_trans _ _ _ _ WM WMc) as WM2. clear MU MUc MUs WM WMc MI1 ST1 m1.
    replace (ret_pc (wz 0x58890)) with (Z_to_bv 64 0x58890) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    (first [ pose proof ((obj_reshape m2 _ _ FRO)) as dR_11; dex4 dR_11 as j0 j3 j12 jb; rename dR_11 into OBJ | pose proof ((obj_reshape m2 _ _ FRO)) as dR_11; dand5 dR_11 as j0 j3 j12 jb OBJ | destruct (obj_reshape m2 _ _ FRO) as (j0 & j3 & j12 & jb & OBJ) ]). clear FRO.
    assert (TC2 : thread_cells m2 tp tsd ctx thr) by tcells TPL.
    rewrite <- (Z_to_bv_bv_unsigned sp). rewrite !(unsigned_lit fp) by lia.
    assert (KONT : forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (jb1 jrest : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (fp + -2128) [C8 (wz (fp + -2128 + 16))] ->
        rw_cells rsegs m' (fp + -2128 + 32) [CB 2024 jrest] ->
        rw_cells rsegs m' (fp + -2128 + 2056) [C8 (wz fp)] ->
        (if unwind_depth2 top bot fp
         then rw_cells rsegs m' (fp + -2128 + 8) [C4 (wz 2)] /\ rw_cells rsegs m' (fp + -2128 + 16) [C8 (wz 0x58994); C8 ra]
         else rw_cells rsegs m' (fp + -2128 + 8) [C4 (wz 1)] /\ rw_cells rsegs m' (fp + -2128 + 16) [C8 (wz 0x58994); CB 8 jb1]) ->
        rw_cells rsegs m' (fp + -2128 + 12) [C4 (wz 0)] ->
        rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        munch [(fp - 2128 - 224, fp - 2128); (fp + -2128, fp + -2128 + 32); (fp + -2128 + 2056, fp + -2128 + 2064);
               (thr + off_th_unwinding, thr + off_th_unwinding + 1)] m2 m' ->
        wmono rsegs m2 m' -> mem_inv rsegs m' -> stk rsegs m' lo (fp - 2128) ->
        evt rsegs Q (MS (mkR (wz 0x58a04) (wz (fp + -2128)) gp tp t0' t1' t2' (wz fp) (wz p)
                         (wz 0xb1558) (wz p) (wz 0) (wz 0) (wz (fp + -2128)) (wz 1) a6' a7'
                         (wz 0x58994) (wz 1) (wz (fp + -2128)) (wz (fp + -81)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz dealloc_entry) fc None m' (seg_rom rsegs))).
    { intros t0b t1b t2b a6b a7b t3b t4b t5b t6b jb1 jrest m3 O0 O32 PFP DEP O12 TUNW3 SAV3 MU3 WM3 MI3 ST3.
      unfold off_th_unwinding in TUNW3, MU3.
      apply fdep_cells in DEP. destruct DEP as [D8 D16].
      assert (IAP3 : ia_post ia0 m3).
      { destruct ia0; [exact I|]. cbn [ia_post] in IAP2 |- *.
        eapply (ia_post_xfer false _ m2 m3 IAP2 MU3 WM3); cbn [disjoint_from]; unfold IAB; lia. }
      eapply K; try eassumption.
      - unfold fshell1_W, off_th_unwinding. intros y Hy. apply outside_app in Hy. destruct Hy as [Hy1 Hy2].
        rewrite (MU3 y); [apply MU2; unfold fshell1_W, off_th_unwinding; apply outside_app; split; [exact Hy1| exact Hy2]|].
        cbn [outside] in Hy1 |- *. clear -Hy1. lia.
      - exact (wmono_trans _ _ _ _ WM2 WM3). }
    destruct PZ2 as [[P0 IAM]|(P1 & P2 & P3 & IAM)].
    - rewrite P0 in KONT |- *.
      eapply (free_mid0_ok _ gp tp _ _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 fp tsd ctx thr top bot lo ra s0 s5 s4 s3 s2 s1 j0 j3 pad j12 jb);
        [> try (fside CV) .. | idtac].
      exact KONT.
    - eapply (free_mid_ok _ gp tp _ _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 fp p tsd ctx thr top bot lo ra s0 s5 s4 s3 s2 s1 j0 j3 pad j12 jb);
        [> try (fside CV) .. | idtac].
      exact KONT.
  Qed.
End Shell1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WrapF.
Context {Clg : Ceiling}.
  Hypothesis DCORE : dealloc_core_cps.

  #[using="DCORE"] Theorem pa_freeV_of_core : pa_free_obligationV.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 T.
    cbv zeta. intros AI MI Ha0 LV TPE SPA RA4 SITE S0C CEIL SM KK.
    cbn [cl_segs cl_free_pc LPA] in MI |- *.
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0.
    pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A (aview_of (pa_hull A) m)) as AR.
    pose proof (hit_stk A m sp CEIL SM) as ST. pose proof (hit_sp47 A m md sp AI CEIL SM) as SPH. unfold ASTK in *.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
    (first [ pose proof ((hit_place A m md AI)) as dR_12; dand7 dR_12 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]). pose proof (aobj_facts _ _ TH1) as THF.
    pose proof (hit_TC A m md AI) as TC. pose proof (hit_tsd A m md AI) as [TSD1 TSD2].
    assert (TSDL : 0x5e7b28 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia).
    pose proof (free_FCo A m md AI) as FCo. pose proof (hit_PCo A m md AI) as PCo.
    pose proof (hit_TTB A m md AI) as TTB. pose proof (hit_TDT A m md AI) as TDT. pose proof (hit_TUNW A m md AI) as TUNW.
    subst a0 tp.
    assert (LO : alloc_ceiling <= bv_unsigned sp - 8192 /\ bv_unsigned sp - 8192 <= bv_unsigned sp - 2688) by lia.
    pose proof (proj1 (Forall_forall _ _) pa_sites_range _ SITE) as RAr. cbv beta in RAr. assert (RA0 : 4096 <= bv_unsigned ra) by lia.
    assert (RANE : bv_unsigned ra <> 0x58994) by (intros E; apply (pa_pcs_not_sites 0x58994 ltac:(mem_side)); rewrite <- E; exact SITE).
    assert (VLE : bv_unsigned s0 <= bv_unsigned sp) by lia.
    assert (TPE : cl_tp LPA = wz TP) by reflexivity.
    destruct (asI_minv A m md AI) as [HMI HH].
    set (fp := bv_unsigned sp) in *. set (thr := p_thr (a_pl A)) in *. set (v := aview_of (pa_hull A) m) in *.
    set (top := p_stk_top (a_pl A)) in *. set (bot := p_stk_bot (a_pl A)) in *.
    (* [comment removed for export] *)
    assert (NL0 : forall li, a_livemap A !! 0 = Some li -> False).
    { intros li E. destruct (wfV A WF0) as (V1 & _). (first [ pose proof ((V1 0 li E)) as dR_13; dand3 dR_13 as N U _ | pose proof (V1 0 li E) as (N & U & _) ]). cbv zeta in U.
      pose proof (ATransp.user_in A _ _ (ATransp.known_live A v AR 0 li E)) as [U1 _].
      pose proof (ATransp.known_range A v AR _ _ (ATransp.known_live A v AR 0 li E)) as [R1 _].
      rewrite <- U in U1. unfold kHighMemBeg in *. clear -R1 U1. lia. }
    assert (PZ : (p = 0 /\ ro_cells rsegs v 0xb5dc8 [C8 (wz 0)])
                 \/ (0 < p /\ aobj (p + -16) 16 /\ p < alloc_ceiling /\ ro_cells rsegs v (0xb5dc8 + 8 * Z.shiftr p 32) [C8 (wz 0)])).
    { destruct (Z.eq_dec p 0) as [->|PNZ].
      - left. split; [reflexivity|].
        destruct (ar_ia _ _ _ _ _ (proj2 AR)) as [MAP1 _]. specialize (MAP1 0 ltac:(unfold kDepotNodesL1; lia)).
        change (al_internal_allocator_inst AL_pboth) with 0xb5dc0 in MAP1. replace (0xb5dc0 + 8 + 8 * 0) with 0xb5dc8 in MAP1 by reflexivity. exact (u64_ro _ _ _ MAP1).
      - assert (HL : as_live A p = Some n0) by (destruct LV as [[E _]|LV]; [exfalso; exact (PNZ E)| exact LV]).
        (first [ pose proof ((free_geom A m md p n0 AI HL)) as dR_14; dand4 dR_14 as PAL PLO PCE PHI | destruct (free_geom A m md p n0 AI HL) as (PAL & PLO & PCE & PHI) ]). destruct (free_n0 A m md p n0 AI HL) as [NR _]. unfold REQ_MAX in NR.
        pose proof (aobj_facts _ _ PLO) as PF. pose proof (Z_div_mod_eq_full (n0 + 7) 8) as NDE. pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)) as ER.
        right. split; [clear -PF NR NDE ER; lia|]. split; [apply (aobj_sub _ _ _ _ PLO); clear -NR NDE ER; lia|]. split; [clear -PCE NR; lia|].
        exact (free_IAM A m md p n0 AI HL). }
    assert (N00 : p = 0 -> n0 = 0).
    { intros ->. destruct LV as [[_ E]|LV]; [exact E|]. exfalso. unfold as_live, as_live_ in LV. destruct (a_livemap A !! 0) as [li|] eqn:E; [eapply NL0; first [exact E| reflexivity]| discriminate]. }
    pose proof (ia_pre_of A v AR) as IAX.
    (* [comment removed for export] *)
    pose (Q1 := fun ms' : machine_state => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (pad jb1 jrest : list byte) (m1 : mem),
        ms' = MS (mkR (wz 0x58a04) (wz (fp + -2128)) gp (cl_tp LPA) t0' t1' t2' (wz fp) (wz p)
                     (wz 0xb1558) (wz p) (wz 0) (wz 0) (wz (fp + -2128)) (wz 1) a6' a7'
                     (wz 0x58994) (wz 1) (wz (fp + -2128)) (wz (fp + -81)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz dealloc_entry) fc None m1 (seg_rom rsegs)
        /\ rw_cells rsegs m1 (fp + -2128) [C8 (wz (fp + -2128 + 16))]
        /\ rw_cells rsegs m1 (fp + -2128 + 32) [CB 2024 jrest]
        /\ rw_cells rsegs m1 (fp + -2128 + 2056) [C8 (wz fp)]
        /\ rw_cells rsegs m1 (fp + -2128 + 8) [C4 (wz (dep_w8 top bot fp))]
        /\ rw_cells rsegs m1 (fp + -2128 + 16) [C8 (wz 0x58994); CB 8 (dep_b16 top bot fp ra jb1)]
        /\ rw_cells rsegs m1 (fp + -2128 + 12) [C4 (wz 0)]
        /\ rw_cells rsegs m1 (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
        /\ rw_cells rsegs m1 (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ ia_post (a_ia_inited A) m1
        /\ munch (fshell1_W (a_ia_inited A) fp thr) v m1 /\ wmono rsegs v m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 (fp - 8192) (fp - 2128)).
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) pa_wx _ (pa_eager A) Q1 _ md T HMI HH).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      eapply (free_shell1 ra sp gp (cl_tp LPA) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc v
                (fp - 8192) p pa_tsd (p_ctx (a_pl A)) thr top bot (a_ia_inited A) MI ST LO SPA SPH RA0 RANE VLE TOPR BOTR TPE FCo PCo TC TSDL TTB TDT TUNW PZ IAX).
      intros t0' t1' t2' a6' a7' t3' t4' t5' t6' pad jb1 jrest m1 O0 O32 PFP D8 D16 O12 TUNW1 SAV IAP1 MU1 WM1 MI1 ST1.
      apply evt_done. unfold Q1. first [ hotw_ex13 t0' t1' t2' a6' a7' t3' t4' t5' t6' pad jb1 jrest m1 | exists t0', t1', t2', a6', a7', t3', t4', t5', t6', pad, jb1, jrest, m1 ].
      split; [reflexivity|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }
    intros msr1 md1 HQ1 HI1 SB1 CL1.
    (first [ dex13 HQ1 as t0' t1' t2' a6' a7' t3' t4' t5' t6' pad jb1 jrest m1; dand14 HQ1 as -> O0 O32 PFP D8 D16 O12 TUNW1 SAV IAP1 MU1 WM1 MI1 ST1 | dand27 HQ1 as t0' t1' t2' a6' a7' t3' t4' t5' t6' pad jb1 jrest m1 -> O0 O32 PFP D8 D16 O12 TUNW1 SAV IAP1 MU1 WM1 MI1 ST1 | destruct HQ1 as (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & pad & jb1 & jrest & m1 & -> & O0 & O32 & PFP & D8 & D16 & O12 & TUNW1 & SAV & IAP1 & MU1 & WM1 & MI1 & ST1) ]).
    rewrite unrestrict_MS. cbn [ms_mem] in CL1.
    lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
    idtac "seg1 done".
    (* [comment removed for export] *)
    assert (AGc : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> thr + 3168 -> ~ ia_blk a -> m1 (wz a) = v (wz a)).
    { intros a Ha NW NT NI. unfold ASTK in NW. apply MU1. rewrite unsigned_lit by lia. unfold fshell1_W, off_th_unwinding, ia_blk in *.
      rewrite outside_app. split.
      - cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; first [apply NW; clear -X; lia| apply NT; clear -X; lia].
      - destruct (a_ia_inited A); cbn [ia_Wk ia_W outside]; [exact I|]. unfold IAB. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; apply NI; clear -X; lia. }
    assert (AI1 : @pa_ainv _ DepotRepL (set_ia A true) (munrestrict (hidc (pa_hull A)) m m1) md1).
    { destruct (a_ia_inited A) eqn:EIA.
      - rewrite (set_ia_same A true EIA).
        apply (shell_ainv A m md md1 fp m1 nowhere AI CEIL SM); [| intros a []| exact TUNW1| exact WM1| exact CL1| exact HI1| exact SB1].
        intros a Ha NW NT NE _. unfold ASTK in NW. apply MU1. rewrite unsigned_lit by lia. unfold fshell1_W, off_th_unwinding. cbn [ia_Wk app outside].
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; first [apply NW; clear -X; lia| apply NT; clear -X; lia].
      - cbn [ia_post] in IAP1. exact (ia_shell_ainv A m md md1 fp m1 AI CEIL AGc TUNW1 IAP1 WM1 CL1 HI1 SB1). }
    pose proof (shell_view A m m1 CL1) as VIEW1. fold v in VIEW1.
    set (m1r := munrestrict (hidc (pa_hull A)) m m1) in *. set (A1 := set_ia A true) in *.
    set (KEY := free_key top bot fp ra).
    pose proof (free_key_len top bot fp ra) as KL. pose proof (free_key_range top bot fp ra) as KR. fold KEY in KL, KR.
    destruct (ftrc_cells m1 top bot fp ra jb1 (fp + -2128) O0 D8 O12 D16) as [TRC TRB]. fold KEY in TRC, TRB.
    idtac "AI1 done".
    (* [comment removed for export] *)
    pose proof DCORE as DC. unfold dealloc_core_cps in DC.
    eapply (DC (wz 0x58a04) (wz (fp + -2128)) gp (cl_tp LPA) t0' t1' t2' (wz fp) (wz p) (wz 0) (wz 0) a6' a7' (wz 0x58994) (wz 1) (wz (fp + -2128)) (wz (fp + -81))
               s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1r md1 A1 p n0 (fp + -2128) (fp - 8192) fp KEY T); clear DC.
    - (* [comment removed for export] *)
      unfold dealloc_core_pre. subst A1. change (pa_hull (set_ia A true)) with (pa_hull A). rewrite VIEW1. cbn [cl_segs LPA].
      rewrite !unsigned_lit by lia.
      split; [exact AI1|]. split; [exact MI1|].
      split; [exact LV|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact CEIL|]. split; [clear -CE CEIL; lia|]. split; [clear -SPR; lia|]. split; [exact SPH|].
      split; [clear -SPA SPR; Z.div_mod_to_equations; lia|]. split; [reflexivity|].
      split; [exact ST1|].
      split. { eapply (mapped_mono _ m1); [eapply (ALogic2.mapped_sub _ _ _ _ _ SM); lia|].
               intros i Hi Hv. apply (wmono_NN _ _ _ WM1); [clear -Hi CE CEIL; lia| clear -Hi SPR CE CEIL; lia| exact Hv]. }
      split; [lia|]. split; [lia|].
      split; [exact TRC|]. split; [exact TRB|].
      split. { unfold KEY, free_key. (first [ pose proof ((place_extra A m md AI)) as dR_16; dand6 dR_16 as _ _ _ _ SK _ | destruct (place_extra A m md AI) as (_ & _ & _ & _ & SK & _) ]).
               destruct (SK 0x58994 (bv_unsigned ra) ltac:(mem_side) SITE) as [K2 K1]. destruct (unwind_depth2 top bot fp); [exact K2| exact K1]. }
      exact KR.
    - (* [comment removed for export] *)
      unfold dealloc_core_K. cbv zeta. subst A1. change (pa_hull (set_ia A true)) with (pa_hull A). rewrite VIEW1.
      intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c A' m' md' AI' MI' AMD FFR PLE HL' HLQ LB TCR SCR PCR NLV VG ERRK FRK CFI STK'.
      cbn [cl_segs cl_errno LPA] in MI', FRK, ERRK, CFI, STK' |- *.
      set (v' := aview_of (pa_hull A') m') in *.
      replace (ret_pc (wz 0x58a04)) with (wz 0x58a04 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite !unsigned_lit in CFI, STK' by lia. replace (fp - (fp - 8192)) with 8192 in FRK by lia.
      destruct (asI_minv A' m' md' AI') as [HMI' HH'].
      (first [ pose proof ((hit_place A' m' md' AI')) as dR_17; dand3 dR_17 as TH1' TH2' _ | pose proof (hit_place A' m' md' AI') as (TH1' & TH2' & _) ]). pose proof (aobj_facts _ _ TH1') as THF'.
      pose proof (hit_TUNW A' m' md' AI') as TUNW'. fold v' in TUNW'. unfold off_th_unwinding in TUNW'.
      idtac "K entered".
      (* [comment removed for export] *)
      assert (CF : forall a cs, rw_cells rsegs m1 a cs -> fp - 2128 <= a -> a + Z.of_nat (cells_size cs) <= fp -> rw_cells rsegs v' a cs).
      { intros a cs H Ha Hb. apply (rw_cells_agree m1 v' a cs H). intros i Hi. apply CFI. lia. }
      pose proof (CF _ _ O0 ltac:(lia) ltac:(cbn; lia)) as O0'. pose proof (CF _ _ O12 ltac:(lia) ltac:(cbn; lia)) as O12'.
      pose proof (CF _ _ O32 ltac:(lia) ltac:(cbn; lia)) as O32'. pose proof (CF _ _ PFP ltac:(lia) ltac:(cbn; lia)) as PFP'.
      pose proof (CF _ _ D8 ltac:(lia) ltac:(cbn; lia)) as D8'. pose proof (CF _ _ SAV ltac:(lia) ltac:(cbn; lia)) as SAV'.
      assert (D16' : rw_cells rsegs v' (fp + -2128 + 16) [C8 (wz 0x58994); CB 8 (dep_b16 top bot fp ra jb1)]).
      { apply (CF _ _ D16 ltac:(lia)). destruct D16 as [[[_ WFj] _] _]. cbn in WFj |- *. lia. }
      destruct (obj_rejoin v' (fp + -2128) _ _ _ _ _ _ O0' D8' O12' D16' O32' PFP') as [junk OBJ].
      (* [comment removed for export] *)
      pose (Q2 := fun ms2 : machine_state =>
          ms2 = MS (mkR ra (wz fp) gp (cl_tp LPA) t0c t1c t2c s0 s1 a0c a1c a2c a3c a4c a5c a6c a7c s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                   F (ret_pc ra) fc None v' (seg_rom rsegs)
          /\ stk rsegs v' (fp - 8192) fp).
      eapply (srz_evt_restrict rsegs (pa_hull A') (asI_hull_segs A' m' md' AI') pa_wx _ (pa_eager A') Q2 _ md' T HMI' HH').
      { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A')) m') with v'.
        pose proof free_epi_ok as EPI. unfold free_epi_stmt in EPI.
        eapply (EPI _ _ gp (cl_tp LPA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc v' fp (fp - 8192) s5 s4 s3 s2 s1 s0 ra junk pad); clear EPI.
        all: try eassumption. all: try reflexivity. all: try (clear KK; lia).
        intros ST2. apply evt_done. unfold Q2. split; [reflexivity| exact ST2]. }
      intros msr2 md2 HQ2 HI2 SB2 CL2. destruct HQ2 as [-> ST2].
      rewrite unrestrict_MS.
      lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
      cbn [ms_mem] in CL2.
      idtac "seg3 done".
      assert (SM' : mapped v' (fp - ASTK) ASTK) by ((first [ dand4 FRK as _ _ F3 _ | destruct FRK as (_ & _ & F3 & _) ]); unfold ASTK; exact F3).
      pose proof (shell_ainv A' m' md' md2 fp v' nowhere AI' CEIL SM' ltac:(intros; reflexivity) ltac:(intros a []) TUNW' (wmono_refl rsegs v') CL2 HI2 SB2) as AI2.
      pose proof (shell_view A' m' v' CL2) as VIEW2.
      replace (ret_pc ra) with ra by (rewrite <- (Z_to_bv_bv_unsigned ra); symmetry; apply ret_pc_even; [clear -RAR; lia| clear -RA4; Z.div_mod_to_equations; lia]).
      replace (Z_to_bv 64 fp) with sp by (subst fp; symmetry; apply Z_to_bv_bv_unsigned).
      assert (OWW : forall a, pa_owned A a -> ~ (fp - 8192 <= a < fp) /\ ~ (6191924 <= a < 6191924 + 4)).
      { intros a OW. destruct (asI_owned_where A m md a AI OW) as [ST0|HZ].
        - cbn [cl_static LPA] in ST0. unfold pa_static in ST0. clear -ST0 CE CEIL. lia.
        - unfold heap_zone, in_image in HZ. cbn [cl_image_lo cl_image_hi LPA] in HZ. clear -HZ CEIL. lia. }
      eapply (KK t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c A' (munrestrict (hidc (pa_hull A')) m' v') md2).
      + exact AI2.
      + cbn [cl_segs LPA]. rewrite VIEW2. exact MI'.
      + eapply (wamd_sbm_l md md1); [exact SB1| exact HH|]. eapply wamd_sbm_r; [exact AMD| exact SB2].
      + right. exact I.
      + intros ff. rewrite FFR. reflexivity.
      + exact HL'.
      + intros q Hq. rewrite (HLQ q Hq). reflexivity.
      + exact LB.
      + exact TCR.
      + exact SCR.
      + exact PCR.   (* [comment removed for export] *)
      + exact NLV.
      + intros c Hc Vc. apply (VG c Hc). exact Vc.
      + intros i Hi. rewrite VIEW2. cbn [cl_segs cl_errno LPA]. rewrite (ERRK i Hi). unfold mrd.
        rewrite (AGc (6191924 + i)); [reflexivity| clear -Hi; lia| clear -Hi CEIL CE; unfold ASTK; lia| clear -Hi THF; lia| unfold ia_blk; clear -Hi; lia].
      + rewrite VIEW2. cbn [cl_errno LPA] in OWW.
        apply (frame_ok_shell (pa_owned A) (pa_owned A') (newblk p n0) nowhere fp 8192 v m1 v' v' FRK).
        * intros a Ha NW NO. destruct (Z.eq_dec a (thr + 3168)) as [->|NT]; [exact (shell_unw A m md m1 AI TUNW1 WM1)|].
          apply AGc; [exact Ha| unfold ASTK; exact NW| exact NT|].
          intros IB. apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. unfold ia_blk in IB. clear -IB. lia.
        * intros a H1 H2. exact (wmono_NN _ _ a WM1 H1 H2).
        * intros; reflexivity.
        * intros a _ _ H. exact H.
        * eapply stk_mapped_pa; [exact ST2| exact CEIL| lia| lia].
        * exact OWW.
        * intros a NB. unfold newblk, blk in NB. destruct (Z.eq_dec p 0) as [->|PNZ]; [exfalso; clear -NB; lia|].
          assert (HL : as_live A p = Some n0) by (destruct LV as [[E _]|LV]; [exfalso; exact (PNZ E)| exact LV]).
          (first [ pose proof ((free_geom A m md p n0 AI HL)) as dR_19; dand4 dR_19 as _ PLO PCE _ | destruct (free_geom A m md p n0 AI HL) as (_ & PLO & PCE & _) ]). destruct (free_n0 A m md p n0 AI HL) as [NR _]. unfold REQ_MAX in NR.
          (first [ pose proof ((free_li A p n0 HL)) as dR_20; dex1 dR_20 as li; destruct dR_20 as [LU LN] | pose proof ((free_li A p n0 HL)) as dR_20; dand3 dR_20 as li LU LN | destruct (free_li A p n0 HL) as (li & LU & LN) ]).
          pose proof (GEO A v p n0 li sp AR LU LN) as Gx. pose proof (aobj_facts _ _ PLO) as PF.
          pose proof (Z_div_mod_eq_full (n0 + 7) 8) as NDE. pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)) as ER.
          clear -NB PCE NR Gx PF CEIL CE NDE ER. unfold kHighMemBeg, REQ_MAX in Gx. cbn [cl_errno LPA]. unfold kLowShadowMapBeg, kHighMemBeg in PF. lia.
  Qed.

  #[using="DCORE"] Theorem pa_free_of_core : @pa_free_obligation _ DepotRepL.
  Proof. exact (pa_free_of_V pa_freeV_of_core). Qed.
End WrapF.

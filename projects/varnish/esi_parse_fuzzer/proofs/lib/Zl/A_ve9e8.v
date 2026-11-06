(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_vemo8.

Module A_veqnt.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_vemo8.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vemo8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, vep_default_cb_post, CB_STACK, CRC_STACK, C64_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@VEPC]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (H : henv) (p mark n : Z) (seg : list byte) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis HEC : vep_emit_common_stmt.
  Hypothesis HCRC : crc32_stmt.
  Hypothesis HC64 : crc32_combine_stmt2.   (* [comment removed for export] *)
  Hypothesis HCB : vep_default_cb_stmt.
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs (aview A m).
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 p.
  Hypothesis A2 : a2 = Z_to_bv 64 mark.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LPA A (aview A m) VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LPA VIA H A (aview A m).
  Hypothesis HLM : bool01 (v Flast_mark).
  Hypothesis CNT : vep_cnt v n.
  Hypothesis N0 : 0 <= n.
  Hypothesis NMX : n + (p - v Fver_p) < NMAX.
  Hypothesis SOBJ : vsb_obj LPA A (aview A m) (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis EM : vb_size vv + 9 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A + vsb_extendsize (vb_size vv + 9) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A.
  Hypothesis PCM : PRIM_ROOM <= a_primcred A.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A 2 0.
  Hypothesis BSEG : bytes_at rsegs (aview A m) (v Fver_p) seg.
  Hypothesis LSEG : Z.of_nat (length seg) = p - v Fver_p.
  Hypothesis VPLO : 4096 <= v Fver_p.
  Hypothesis PHI : p <= alloc_ceiling.
  Hypothesis SHSEG : shadowed LPA (aview A m) (v Fver_p) (p - v Fver_p).
  Hypothesis SEGH : (v Fver_p = vi_empty VIA /\ seg = []) \/
                    (exists d k, a_live A d = Some k /\ 0 < k /\ d <= v Fver_p /\ p <= d + k /\ d <> VEP /\ d <> v Fvsb /\ d <> vb_buf vv).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST : stk rsegs (aview A m) lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + MARK_STACK <= bv_unsigned sp.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          let w' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs w' -> amd_frame md md' ->
          stk rsegs w' lo (bv_unsigned sp) ->
          vep_obj LPA A' w' VEP v' tag q -> vkeep v v' MARK_FIELDS ->
          v' Fver_p = p -> v' Flast_mark = mark -> v' Fo_pending = 0 -> vep_cnt v' (n + (p - v Fver_p)) ->
          0 <= v' Fcrc < 2^64 -> 0 <= v' Fcrcp < 2^64 ->
          vsb_obj LPA A' w' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + Z.min 9 (3 * (v' Fo_last - v Fo_last)) ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> a_live A' r = a_live A r) ->
          frames_aged A A' 2 0 ->
          a_livebytes A' = a_livebytes A + vb_size vv' - vb_size vv ->
          a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A ->
          a_seccred A - (vsb_pot vv' - vsb_pot vv) <= a_seccred A' <= a_seccred A ->
          a_primcred A - (vsb_ppot vv' - vsb_ppot vv) <= a_primcred A' <= a_primcred A ->   (* [comment removed for export] *)
          henv_ok LPA VIA H A' w' -> bytes_at rsegs w' (v Fver_p) seg ->
          cframe LPA (owned A) (owned A') (bv_unsigned sp) MARK_STACK
                 (fun a => blk VEP 312 a \/ newblk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40))
                 (newblk (vb_buf vv') (vb_size vv')) (aview A m) w' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Let Vmc : Z -> Prop := fun a => blk VEP 312 a \/ newblk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40).
  Let l : Z := p - v Fver_p.

  (* [comment removed for export] *)
  #[using="l SEGH LSEG NEB NES SOBJ VOBJ AINV A md m sp p q tag AI Clg"] Lemma seg_ranges :
       (v Fver_p + Z.of_nat (length seg) <= VEP \/ VEP + 312 <= v Fver_p)
    /\ (v Fver_p + Z.of_nat (length seg) <= v Fvsb \/ v Fvsb + 40 <= v Fver_p)
    /\ (v Fver_p + Z.of_nat (length seg) <= vb_buf vv \/ vb_buf vv + vb_size vv <= v Fver_p).
  Proof.
    destruct VOBJ as (VLV & _ & _ & _).
    (first [ pose proof ((live_geomP LPA A m md VEP _ AINV VLV)) as dR_1; dand4 dR_1 as _ _ Vlo _ | pose proof (live_geomP LPA A m md VEP _ AINV VLV) as (_ & _ & Vlo & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA A m md (v Fvsb) vv false AINV SOBJ)) as dR_2; dand7 dR_2 as _ Slo _ _ _ Blo _ | pose proof (vsb_obj_geom LPA A m md (v Fvsb) vv false AINV SOBJ) as (_ & Slo & _ & _ & _ & Blo & _) ]).
    destruct SOBJ as (_ & _ & VLS & VLB & _ & _). unfold kHighMemBeg in *. all_app_facts. unhide_app.
    destruct SEGH as [[EV ES] | (d & k & LD & K0 & D0 & D1 & N1 & N2 & N3)].
    - rewrite ES. rewrite EV. cbn [vi_empty VIA length Z.of_nat]. lia.
    - pose proof (as_live_disjoint LPA A m md d k VEP 312 AINV LD VLV N1).
      pose proof (as_live_disjoint LPA A m md d k (v Fvsb) 40 AINV LD VLS N2).
      pose proof (as_live_disjoint LPA A m md d k (vb_buf vv) (vb_size vv) AINV LD VLB N3).
      lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj HEC (conj HCRC (conj HC64 (conj HCB (conj AINV (conj MI (conj A0 (conj A1 (conj A2 (conj HMK (conj VOBJ
      (conj VBASE (conj HENV (conj HLM (conj CNT (conj N0 (conj NMX (conj SOBJ (conj NES (conj NEB (conj EM (conj LBM (conj NLV (conj SCM (conj PCM
      (conj FY (conj BSEG (conj LSEG (conj VPLO (conj PHI (conj SHSEG (conj SEGH (conj TP (conj SP16 (conj ST (conj CEIL
      (conj LO K))))))))))))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A m md H AINV (proj1 HENV)) as HG;
    pose proof HG as (G1 & G2 & G3); unfold HFSIZE in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VIA] in ECB, EURL;
    pose proof CNT as (CN1 & CN2 & CN3 & CN4 & CN5 & CN6 & CN7);
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    unfold_stacks; unfold NMAX in *.

  (* [comment removed for export] *)
  Local Ltac seg_prelims AINVx VLVx SOBJx NEBx BSEGx :=
    prelims;
    pose proof (live_geomP LPA _ _ _ VEP _ AINVx VLVx) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    pose proof (mod8_of_mod16 VEP V16) as V8;
    pose proof VOBJ as (_ & _ & TAG & PADS); (first [ pose proof (PADS) as dR_4; dand7 dR_4 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    pose proof (bytes_at_bound _ _ _ _ BSEGx) as SEGBD;
    (first [ pose proof ((vsb_obj_geom LPA _ _ _ (v Fvsb) _ false AINVx SOBJx)) as dR_5; dand11 dR_5 as S16 Slo Shi Simg B16 Blo Bhi Bimg _ Smap Bmap | pose proof (vsb_obj_geom LPA _ _ _ (v Fvsb) _ false AINVx SOBJx) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & _ & Smap & Bmap) ]);
    pose proof (proj1 (proj2 SOBJx)) as VINVx; (first [ pose proof (VINVx) as dR_6; dand3 dR_6 as Vsz Vlen _ | pose proof VINVx as (Vsz & Vlen & _) ]);
    pose proof (proj1 (proj2 (proj2 (proj2 SOBJx)))) as VLBx;
    pose proof (as_live_disjoint LPA _ _ _ VEP 312 (v Fvsb) 40 AINVx VLVx (proj1 (proj2 (proj2 SOBJx))) NES) as DVS;
    pose proof (as_live_disjoint LPA _ _ _ VEP 312 _ _ AINVx VLVx VLBx NEBx) as DVB;
    unfold kHighMemBeg in *; all_app_facts;
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact Vhi)) as SHVB; rewrite SHMAX_val in SHVB;
    change ((312 + 7) / 8) with 39 in SHVB;
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINVx VLVx) as SHV0; fold_cl_segs; fold_aview;
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0;
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0;
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity);
    pose proof BSEGx as BSEG0; hide BSEG0; hide DVS; hide DVB.

  Local Definition mc_stepB' := mc_stepB (* [comment removed for export] *) VEP v tag q vv H p mark n seg lo ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A T
                     HEC HCRC HC64 HCB AINV MI A0 A1 A2 HMK VOBJ VBASE HENV HLM CNT N0 NMX SOBJ NES NEB EM LBM NLV SCM PCM FY BSEG LSEG VPLO PHI SHSEG SEGH TP SP16 ST CEIL LO K.

  (* [comment removed for export] *)
  #[using="l SEGH AINV A md m sp vv VEP AI Clg"] Lemma seg_high : Z.of_nat (length seg) = 0 \/ (17594333495296 <= v Fver_p \/ p <= 2147446784).
  Proof.
    destruct SEGH as [[EV ES] | (d & k & LD & K0 & D0 & D1 & N1 & N2 & N3)].
    - left. rewrite ES. reflexivity.
    - right. (first [ pose proof ((live_geomP LPA A m md d k AINV LD)) as dR_7; dand4 dR_7 as _ _ DLO _ | destruct (live_geomP LPA A m md d k AINV LD) as (_ & _ & DLO & _) ]). unfold kHighMemBeg in DLO. all_app_facts. unhide_app. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="l K LO CEIL ST SP16 TP SEGH SHSEG PHI VPLO LSEG BSEG FY SCM PCM NLV LBM EM NEB NES SOBJ NMX N0 CNT HLM HENV VBASE VOBJ HMK A2 A1 A0 MI AINV HCB HC64 HCRC HEC a2 a1 a0 seg n H vv"] Lemma mc_stepE :
    forall (xra xs5 xs7 xs10 xt0 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (j0 : list byte) (v1 : mem),
      mem_inv rsegs v1 -> stk rsegs v1 lo (bv_unsigned sp + -160) ->
      rw_cells rsegs v1 (bv_unsigned sp + -160)
        [CB 24 j0; C8 (Z_to_bv 64 (VEP + 160)); C8 (Z_to_bv 64 ((VEP + 304) / 8 + 2147450880));
         C8 (Z_to_bv 64 (VEP + 40)); C8 (Z_to_bv 64 p);
         C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs v1 VEP (vep_cells v tag q) ->
      munch [(bv_unsigned sp - 8800, bv_unsigned sp); (VEP, VEP + 312)] (aview A m) v1 -> wmono rsegs (aview A m) v1 ->
      evt rsegs (EvtAcct.srz_at_r rsegs (ahull A) (alhull A) (aeager A) m md T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp xt0 xt1 xt2
                 (Z_to_bv 64 VEP) (Z_to_bv 64 mark) xa0 xa1 xa2 (Z_to_bv 64 (VEP + 40)) (Z_to_bv 64 (VEP + 160)) xa5 xa6 xa7
                 (Z_to_bv 64 (VEP + 24)) (Z_to_bv 64 ((VEP + 96) / 8 + 2147450880)) (Z_to_bv 64 2147450880) xs5
                 (Z_to_bv 64 (VEP + 96)) xs7 (Z_to_bv 64 (VEP + 48)) (Z_to_bv 64 (VEP + 104)) xs10
                 (Z_to_bv 64 (VEP + 304)) xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x8e238) fc None v1 (seg_rom rsegs)).
  Proof.
    touch_all.
    intros until v1. intros MI1 ST1 FR VEPC MU WM.
    pose proof VOBJ as (VLV & _ & _ & _).
    (first [ pose proof (seg_ranges) as dR_8; dand3 dR_8 as SEGV SEGS SEGB | pose proof seg_ranges as (SEGV & SEGS & SEGB) ]). pose proof seg_high as SEGHI.
    seg_prelims AINV VLV SOBJ NEB BSEG. hide HMK.
    pose proof CNT as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
    pose proof (cenv_intro A m md AINV) as CEx.
    pose proof (proj1 HENV) as [agex HFRx].
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS agex VEP 312 AINV HFRx VLV) as DJv.
    change (fsize HCLASS) with 8192 in DJv.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(unfold HFSIZE in G3; lia)) as SHF.
    rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vv) (vb_size vv) ltac:(lia) ltac:(lia) ltac:(exact Bhi)) as SHB. rewrite SHMAX_val in SHB.
    (* [comment removed for export] *)
    apply (bytes_at_transport rsegs [(bv_unsigned sp - 8800, bv_unsigned sp); (VEP, VEP + 312)] (aview A m) v1 _ _) in SHV0;
      [| exact MU | cbn [disjoint_from]; lia ].
    assert (WMAPx : mapped (aview A m) (bv_unsigned sp - 8800) 8800).
    { eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8800, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8800)) with 8800 by lia; exact WMAPx |].
      split; [right; left; exists VEP, 312; split; [exact VLV|lia]| exact I]. }
    unfold vep_cells in VEPC.
    hide SEGV. hide SEGS. hide SEGB. hide SEGHI. hide_slow. unhide V8.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 8 0.
    zstep. zstep. zstep. zstep. zstep. zstep. rewrite EVC, ECB, EPRIV. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (HENVq : henv_ok LPA VIA H A mq)
        by (eapply henv_ok_munch; [exact HENV| exact MU| exact WM| exact HG|];
            intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
            change (8192 / 8) with 1024 in Ha__; cbn; lia);
      (first [ pose proof (HENVq) as dR_9; dand4 dR_9 as _ _ HOBJq HSHq | pose proof HENVq as (_ & _ & HOBJq & HSHq) ])
    end.
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
    icall (HCB VEP v tag q H 0 lo) by
      (rewrite ?unsigned_lit by lia;
       lazymatch goal with
       | |- @eq (bv _) _ _ => first [reflexivity | unhide HMK; destruct HMK as [-> | ->]; reflexivity]
       | |- rw_cells _ _ _ _ => exact VEPC
       | |- length _ = _ => exact TAG
       | |- vep_pads_wf _ => exact PADS
       | |- hobj_ok _ _ _ _ => exact HOBJq
       | |- hshadow _ _ _ => exact HSHq
       | |- henv_geom LPA _ => exact HG
       | |- cenv _ => eapply cenv_munch; [exact CEx| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia]
       | |- shadowed _ _ _ _ => exists VEP, 312; split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|]; lia
       | |- stk _ _ _ _ => exact STq
       | |- mem_inv _ _ => assumption
       | |- _ => unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; unfold kHighMemBeg, HFSIZE, CB_STACK; lia
       end).
    clear HENVq HOBJq HSHq. try clear STq.
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
    lazymatch goal with X : rw_cells _ ?mq VEP (vep_cells _ tag q) |- evt _ _ (MS _ _ _ _ _ ?mq _) => pose proof X as VEPC; rename X into VEPCF end.
    unfold vep_cells in VEPC. cbn [fupd vf_beq vf_index N.eqb Pos.eqb] in VEPC. hide VEPCF.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. clear - D1 D2 D3 D4 D5 D6 D7 NMX N0 LSEG. dead_b2z. } clear KU.
    (* [comment removed for export] *)
    zstep. vrechk SHV0 EzsV (VEP + 304) 4 0.
    (* [comment removed for export] *)
    zstep. unhide HLM. rewrite (sx32_small (v Flast_mark)) by (clear -HLM; try pose proof alloc_ceiling_val as ACV__; destruct HLM as [-> | ->]; lia). hide HLM.
    zstep. zstep.
    (* [comment removed for export] *)
    astop AINV MU WM CFP.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH].
    unhide VEPCF. unhide DVS. unhide DVB. unhide NES. unhide NEB. unhide HLM.
    eapply (HEC VEP (fupd v Fcb_x (v Fcb_x + 0)) tag q vv (v Fcb_x - v Fo_last) (v Flast_mark) lo);
      [ exact AINV0 | assumption | reflexivity | reflexivity | reflexivity
      | lia
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; lia
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; lia
      | exact HLM
      | split; [exact VLV|]; split; [exact VEPCF|]; split; [exact TAG| exact PADS]
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact EDZ
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM| intros a__ Ha__; cbn; lia]
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact NES
      | exact NEB | exact EM | exact LBM | exact NLV | exact SCM | exact PCM (* [comment removed for export] *) | exact FY | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; exact STq
      | exact CEIL
      | rewrite unsigned_lit by lia; unfold_stacks; lia
      | ].
    clear VEPCF VEPC. hide NES. hide HLM.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' vv' vr'. cbv zeta.
    intros AINV' MI' MDF' ST' VOBJ' CASES SOBJ' LEN SZ REL LIVEq FA' LB' TC' NL' SC' PC' CF'.   (* [comment removed for export] *)
    cbn [fupd vf_beq vf_index N.eqb Pos.eqb] in VOBJ', CASES, SOBJ', CF'.
    rewrite unsigned_lit in ST', CF' by lia. unfold_stacks.
    (first [ pose proof ((vsb_obj_geom LPA A' m' md' (v Fvsb) vr' false AINV' SOBJ')) as dR_10; dand9 dR_10 as _ _ _ _ B16' Blo' Bhi' Bimg' _ | pose proof (vsb_obj_geom LPA A' m' md' (v Fvsb) vr' false AINV' SOBJ') as (_ & _ & _ & _ & B16' & Blo' & Bhi' & Bimg' & _) ]).
    unfold kHighMemBeg in Blo'. all_app_facts.
    pose proof (proj1 (proj1 (proj2 SOBJ'))) as Vsz'.
    (* [comment removed for export] *)
    assert (VF : vkeep v vv' MARK_FIELDS /\ vv' Fver_p = v Fver_p /\ vv' Flast_mark = v Flast_mark /\ vv' Fo_pending = v Fo_pending
                 /\ vv' Fcb_x = v Fcb_x + 0 /\ 0 <= vv' Fo_total <= v Fcb_x /\ vv' Fo_crc = 0 /\ vv' Fvc = v Fvc /\ vv' Fcb = v Fcb
                 /\ vv' Fcb_priv = v Fcb_priv /\ vv' Fvsb = v Fvsb
                 /\ vb_len vv <= vb_len vr' <= vb_len vv + Z.min 9 (3 * (v Fcb_x - v Fo_last))
                 /\ vb_size vv <= vb_size vr' <= Z.max (vb_size vv) (vb_len vr' + 4096)).
    { clear - CASES LEN SZ D1 D2 D3 D4 D5 D6 D7 N0; try pose proof alloc_ceiling_val as ACV__.
      destruct CASES as [(L0 & -> & ->) | (L1 & c & ->)]; cbn [fupd vf_beq vf_index N.eqb Pos.eqb].
      - split; [apply vkeep_fupd; [apply vkeep_refl | in_tac] |]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
      - split; [repeat (apply vkeep_fupd; [| in_tac]); apply vkeep_refl |]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    clear CASES LEN SZ.
    (first [ dand13 VF as VK' EVP' ELM' EPD' ECX' ETOT' ECRC' EVC' ECB' EPR' EVSB' RL' RS' | destruct VF as (VK' & EVP' & ELM' & EPD' & ECX' & ETOT' & ECRC' & EVC' & ECB' & EPR' & EVSB' & RL' & RS') ]).
    assert (NEB2 : VEP <> vb_buf vr').
    { destruct REL as [E | [FRESH _]]; [rewrite E; unhide NEB; exact NEB | intros X; rewrite <- X in FRESH; rewrite FRESH in VLV; discriminate]. }
    assert (VLV' : a_live A' VEP = Some 312) by (rewrite (LIVEq VEP ltac:(unhide NEB; exact NEB) NEB2); exact VLV).
    assert (VLS' : a_live A' (v Fvsb) = Some 40) by exact (proj1 (proj2 (proj2 SOBJ'))).
    assert (VLB' : a_live A' (vb_buf vr') = Some (vb_size vr')) by exact (proj1 (proj2 (proj2 (proj2 SOBJ')))).
    assert (SEGB2 : v Fver_p + Z.of_nat (length seg) <= vb_buf vr' \/ vb_buf vr' + vb_size vr' <= v Fver_p).
    { unhide_app_of (vb_buf vr'). destruct SEGH as [[EV ES] | (d & k & LD & K0 & Dlo & Dhi & N1 & N2 & N3)].
      - rewrite EV, ES. cbn [vi_empty VIA length Z.of_nat]. lia.
      - assert (N4 : d <> vb_buf vr')
          by (destruct REL as [E | [FRESH _]]; [rewrite E; exact N3 | intros X; rewrite <- X in FRESH; rewrite FRESH in LD; discriminate]).
        pose proof (LIVEq d N3 N4) as LD'. rewrite LD in LD'.
        pose proof (as_live_disjoint LPA A' m' md' d k (vb_buf vr') (vb_size vr') AINV' LD' VLB' N4) as X3. lia. }
    (* [comment removed for export] *)
    assert (HENV1 : henv_ok LPA VIA H A' (aview A' m')).
    { lazymatch type of CF' with cframe _ _ _ _ _ _ _ (aview A ?m1) _ =>
        eapply (henv_ok_acall_gen H A A' m1); [exact AINV0| exact CF'| | unfold_stacks; lia| |] end.
      - eapply henv_ok_munch; [exact HENV| exact MU| exact WM| exact HG|].
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
        change (8192 / 8) with 1024 in Ha__; cbn; lia.
      - intros ff k age HF. (first [ pose proof ((proj1 FA' ff k age HF)) as dR_12; dex1 dR_12 as d; destruct dR_12 as [E _] | pose proof ((proj1 FA' ff k age HF)) as dR_12; dand3 dR_12 as d E _ | destruct (proj1 FA' ff k age HF) as (d & E & _) ]). exists (age + d)%nat. exact E.
      - intros a [X|[X|X]].
        + exists VEP, 312. split; [exact VLV|]. left. unfold blk in X. lia.
        + exists (vb_buf vv), (vb_size vv). split; [exact VLBx|]. unfold newblk, blk in X. lia.
        + exists (v Fvsb), 40. split; [exact (proj1 (proj2 (proj2 SOBJ)))|]. left. lia. }
    (* [comment removed for export] *)
    unhide BSEG0. unhide SEGV. unhide SEGS. unhide SEGB. unhide SEGHI.
    lazymatch type of CF' with cframe _ _ _ _ _ _ _ (aview A ?m1) _ =>
      apply (bytes_at_transport rsegs [(bv_unsigned sp - 8800, bv_unsigned sp); (VEP, VEP + 312)] (aview A m) (aview A m1) _ seg) in BSEG0;
        [| exact MU | cbn [disjoint_from]; clear - LSEG PHI CEIL LO SEGV; lia ];   (* [comment removed for export] *)
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ (aview A m1) (bv_unsigned sp - 160) 160 AINV0 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CRfr;
      assert (CRseg : crange A (aview A m1) (v Fver_p) (Z.of_nat (length seg)))
        by (destruct SEGH as [[EV ES] | (d & k & LD & K0 & D0 & D1' & _)];
            [ rewrite ES; cbn; split; [lia|]; split; [lia|]; intros i Hi; lia
            | eapply (crange_block (L:=LPA)); [exact AINV0 | exact LD | lia | lia | lia] ])
    end.
    (* [comment removed for export] *)
    lazymatch type of CF' with cframe _ (owned _) (owned _) ?xsp ?win ?V ?N ?m0 ?m1' =>
      lazymatch type of FR with rw_cells _ _ ?fa ?fcs =>
        apply (rw_cells_ccall LPA A A' xsp win V N m0 m1' CF' fa fcs) in FR;
        [ | exact CRfr
          | cbn [Cells.cells_size Cells.csize Nat.add length app]; try (generalize alloc_ceiling_val); clear - ACV CEIL LO Vhi Bhi Shi SHB SPR Vlo Blo Slo; try pose proof alloc_ceiling_val as ACV__;
            split; [lia|]; intros i Hi X; unfold newblk, blk, nowhere in X; cbn beta in X; lia ] end;
      lazymatch type of BSEG0 with bytes_at _ _ ?ba ?bs =>
        apply (bytes_at_ccall LPA A A' xsp win V N m0 m1' CF' ba bs) in BSEG0;
        [ | exact CRseg
          | try (generalize alloc_ceiling_val); clear - ACV CEIL LO PHI LSEG SEGV SEGS SEGB SEGHI SHB SPR SEGBD Vlo Blo Slo; try pose proof alloc_ceiling_val as ACV__;
            split; [lia|]; intros i Hi X; unfold newblk, blk, nowhere in X; cbn beta in X; lia ] end;
      apply (stk_ccall LPA A A' _ _ m0 m1' xsp win V N lo _ AINV0 CF') in STq;
        [ | exact CEIL | lia | lia
          | clear - ACV CEIL LO Vhi Bhi Shi SHB Vlo Blo Slo; try pose proof alloc_ceiling_val as ACV__; intros a Ha X; unfold newblk, blk, nowhere in X; cbn beta in X; lia ];
      repeat match goal with H : crange _ m0 _ _ |- _ => clear H | H : mem_inv _ m0 |- _ => clear H
                           | H : bytes_at _ m0 _ _ |- _ => clear H | H : ro_cells _ m0 _ _ |- _ => clear H end
    end.
    hide SEGV. hide SEGS. hide SEGB. hide SEGHI. hide BSEG0.
    (* [comment removed for export] *)
    (first [ pose proof (VOBJ') as dR_13; dand3 dR_13 as _ VEPC' _ | pose proof VOBJ' as (_ & VEPC' & _) ]). unfold vep_cells in VEPC'.
    pose proof (as_live_shadow LPA A' m' md' VEP 312 AINV' VLV') as SHV1. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV1. rewrite <- EzsV in SHV1.
    pose proof (as_live_disjoint (Clg:=Clg) LPA A' m' md' VEP 312 (v Fvsb) 40 AINV' VLV' VLS' ltac:(unhide NES; exact NES)) as DVS'.
    pose proof (as_live_disjoint LPA A' m' md' VEP 312 (vb_buf vr') (vb_size vr') AINV' VLV' VLB' NEB2) as DVB'.
    pose proof (munch_refl [(bv_unsigned sp - 8800, bv_unsigned sp); (VEP, VEP + 312)] (aview A' m')) as MU2.
    pose proof (wmono_refl rsegs (aview A' m')) as WM2.
    assert (WMAP2 : mapped (aview A' m') (bv_unsigned sp - 8800) 8800).
    { eapply (window_mapped LPA _ lo); [exact ST' | exact FR | cbn; lia | exact CEIL | lia | lia]. }
    assert (CFP2 : client_fp LPA A' (aview A' m') [(bv_unsigned sp - 8800, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8800)) with 8800 by lia; exact WMAP2 |].
      split; [right; left; exists VEP, 312; split; [exact VLV'|lia]| exact I]. }
    pose proof (cenv_intro A' m' md' AINV') as CE2.
    hide DVS'. hide DVB'. hide NEB2.
    ago AINV'. fold_cl_segs. fix_ret_pc.
    (* [comment removed for export] *)
    vrechk SHV1 EzsV (VEP + 144) 8 0. zstep. vrechk SHV1 EzsV (VEP + 96) 8 1. zstep. zstep.
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq2 end.
    astop AINV' MU2 WM2 CFP2.
    (* [comment removed for export] *)
    unhide DVS'. unhide DVB'. unhide NEB2. unhide BSEG0. unhide SEGV.
    set (vx2 := fupd (fupd vv' Fo_last (v Fcb_x)) Fo_wait 0).
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mf _) ?mdf) _ =>
      assert (VEPC2 : rw_cells rsegs (aview A' mf) VEP (vep_cells vx2 tag q))
        by (unfold vep_cells, vx2; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact VEPC');
      clear VEPC';
      assert (MP2 : mapped (aview A' mf) (bv_unsigned sp - 8800) 8800)
        by (eapply (window_mapped LPA _ lo); [exact STq2 | exact FR | cbn; lia | exact CEIL | lia | lia]);
      eapply (mc_stepB' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' mf mdf vx2 vr');
      [ assumption | assumption
      | eapply amd_frame_sbm_l; [exact SBM | exact MH | eapply amd_frame_sbm_r; [exact MDF' | exact SBM0]]
      | exact STq2 | exact FR | exact VEPC2 | exact VLV'
      | unfold vx2; repeat (apply vkeep_fupd; [| in_tac]); exact VK'
      | unfold vx2, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact EVP'
      | unfold vep_cnt, vx2, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; lia
      | eapply vsb_obj_munch; [exact SOBJ'| exact MU2| exact WM2| intros a__ Ha__; cbn; lia]
      | unfold vx2, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact RL'
      | exact RS'
      | exact NEB2 | exact REL | exact LIVEq | exact FA' | exact LB' | exact TC' | exact NL' | exact SC' | exact PC' (* [comment removed for export] *)
      | eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
        change (8192 / 8) with 1024 in Ha__; cbn; lia
      | eapply (bytes_at_munch LPA); [exact BSEG0| exact MU2| intros a__ Ha__; cbn; lia]
      | exact SEGV
      | lazymatch type of CF' with cframe _ _ _ _ _ _ _ (aview A ?m1) _ =>
          unfold_stacks;
          eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) (aview A m1) (aview A' m') (aview A' mf) _ _);
          [ exact MU | | exact CF' | lia | lia | intros a X; exact X | intros a X; left; exact X | exact MU2 | | exact MP2 ];
          intros a Ha NO; cbn [outside] in NO; unfold Vmc, blk; lia
        end ]
    end.
  Qed.
End S.
End A_veqnt.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vemo8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve9e8.A_veqnt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, vep_default_cb_post, CB_STACK, CRC_STACK, C64_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@Vlo; @TAG; @P36; @P124; @P140; @P196; @P236; @P268; @P308; @Vsz; @LO; @LSEG; @ACV; @Ha__; @CEIL; @Vlo_l; @SPR; @NMX; @D3; @D1; @D6; @Blo; @Vhi; @D4; @PHI; @KQ; @G2; @KS; @Shi; @DVS; @DVB; @DJv; @NO; @Y; @X; @NEB; @CN1; @NES; @KB; @D5; @SEGV; @VPLO; @SEGBD; @D2; @Slo; @K0; @D0; @H0; @H1; @H2; @G3; @KP; @CNT; @CN2; @CN4; @CN5; @D7])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (H : henv) (p mark n : Z) (seg : list byte) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis HEC : vep_emit_common_stmt.
  Hypothesis HCRC : crc32_stmt.
  Hypothesis HC64 : crc32_combine_stmt2.   (* [comment removed for export] *)
  Hypothesis HCB : vep_default_cb_stmt.
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs (aview A m).
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 p.
  Hypothesis A2 : a2 = Z_to_bv 64 mark.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LPA A (aview A m) VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LPA VIA H A (aview A m).
  Hypothesis HLM : bool01 (v Flast_mark).
  Hypothesis CNT : vep_cnt v n.
  Hypothesis N0 : 0 <= n.
  Hypothesis NMX : n + (p - v Fver_p) < NMAX.
  Hypothesis SOBJ : vsb_obj LPA A (aview A m) (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis EM : vb_size vv + 9 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A + vsb_extendsize (vb_size vv + 9) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A.
  Hypothesis PCM : PRIM_ROOM <= a_primcred A.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A 2 0.
  Hypothesis BSEG : bytes_at rsegs (aview A m) (v Fver_p) seg.
  Hypothesis LSEG : Z.of_nat (length seg) = p - v Fver_p.
  Hypothesis VPLO : 4096 <= v Fver_p.
  Hypothesis PHI : p <= alloc_ceiling.
  Hypothesis SHSEG : shadowed LPA (aview A m) (v Fver_p) (p - v Fver_p).
  Hypothesis SEGH : (v Fver_p = vi_empty VIA /\ seg = []) \/
                    (exists d k, a_live A d = Some k /\ 0 < k /\ d <= v Fver_p /\ p <= d + k /\ d <> VEP /\ d <> v Fvsb /\ d <> vb_buf vv).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST : stk rsegs (aview A m) lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + MARK_STACK <= bv_unsigned sp.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          let w' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs w' -> amd_frame md md' ->
          stk rsegs w' lo (bv_unsigned sp) ->
          vep_obj LPA A' w' VEP v' tag q -> vkeep v v' MARK_FIELDS ->
          v' Fver_p = p -> v' Flast_mark = mark -> v' Fo_pending = 0 -> vep_cnt v' (n + (p - v Fver_p)) ->
          0 <= v' Fcrc < 2^64 -> 0 <= v' Fcrcp < 2^64 ->
          vsb_obj LPA A' w' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + Z.min 9 (3 * (v' Fo_last - v Fo_last)) ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> a_live A' r = a_live A r) ->
          frames_aged A A' 2 0 ->
          a_livebytes A' = a_livebytes A + vb_size vv' - vb_size vv ->
          a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A ->
          a_seccred A - (vsb_pot vv' - vsb_pot vv) <= a_seccred A' <= a_seccred A ->
          a_primcred A - (vsb_ppot vv' - vsb_ppot vv) <= a_primcred A' <= a_primcred A ->   (* [comment removed for export] *)
          henv_ok LPA VIA H A' w' -> bytes_at rsegs w' (v Fver_p) seg ->
          cframe LPA (owned A) (owned A') (bv_unsigned sp) MARK_STACK
                 (fun a => blk VEP 312 a \/ newblk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40))
                 (newblk (vb_buf vv') (vb_size vv')) (aview A m) w' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Let Vmc : Z -> Prop := fun a => blk VEP 312 a \/ newblk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40).
  Let l : Z := p - v Fver_p.

  (* [comment removed for export] *)
  #[using="l SEGH LSEG NEB NES SOBJ VOBJ AINV A md m sp p q tag AI Clg"] Lemma seg_ranges :
       (v Fver_p + Z.of_nat (length seg) <= VEP \/ VEP + 312 <= v Fver_p)
    /\ (v Fver_p + Z.of_nat (length seg) <= v Fvsb \/ v Fvsb + 40 <= v Fver_p)
    /\ (v Fver_p + Z.of_nat (length seg) <= vb_buf vv \/ vb_buf vv + vb_size vv <= v Fver_p).
  Proof.
    destruct VOBJ as (VLV & _ & _ & _).
    pose proof (live_geomP LPA A m md VEP _ AINV VLV) as (_ & _ & Vlo & _).
    pose proof (vsb_obj_geom LPA A m md (v Fvsb) vv false AINV SOBJ) as (_ & Slo & _ & _ & _ & Blo & _).
    destruct SOBJ as (_ & _ & VLS & VLB & _ & _). unfold kHighMemBeg in *. all_app_facts. unhide_app.
    destruct SEGH as [[EV ES] | (d & k & LD & K0 & D0 & D1 & N1 & N2 & N3)].
    - rewrite ES. rewrite EV. cbn [vi_empty VIA length Z.of_nat]. lia.
    - pose proof (as_live_disjoint LPA A m md d k VEP 312 AINV LD VLV N1).
      pose proof (as_live_disjoint LPA A m md d k (v Fvsb) 40 AINV LD VLS N2).
      pose proof (as_live_disjoint LPA A m md d k (vb_buf vv) (vb_size vv) AINV LD VLB N3).
      lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj HEC (conj HCRC (conj HC64 (conj HCB (conj AINV (conj MI (conj A0 (conj A1 (conj A2 (conj HMK (conj VOBJ
      (conj VBASE (conj HENV (conj HLM (conj CNT (conj N0 (conj NMX (conj SOBJ (conj NES (conj NEB (conj EM (conj LBM (conj NLV (conj SCM (conj PCM
      (conj FY (conj BSEG (conj LSEG (conj VPLO (conj PHI (conj SHSEG (conj SEGH (conj TP (conj SP16 (conj ST (conj CEIL
      (conj LO K))))))))))))))))))))))))))))))))))))) as ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A m md H AINV (proj1 HENV)) as HG;
    pose proof HG as (G1 & G2 & G3); unfold HFSIZE in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VIA] in ECB, EURL;
    pose proof CNT as (CN1 & CN2 & CN3 & CN4 & CN5 & CN6 & CN7);
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    unfold_stacks; unfold NMAX in *.

  (* [comment removed for export] *)
  Local Ltac seg_prelims AINVx VLVx SOBJx NEBx BSEGx :=
    prelims;
    pose proof (live_geomP LPA _ _ _ VEP _ AINVx VLVx) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    pose proof (mod8_of_mod16 VEP V16) as V8;
    pose proof VOBJ as (_ & _ & TAG & PADS); pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308);
    pose proof (bytes_at_bound _ _ _ _ BSEGx) as SEGBD;
    pose proof (vsb_obj_geom LPA _ _ _ (v Fvsb) _ false AINVx SOBJx) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & _ & Smap & Bmap);
    pose proof (proj1 (proj2 SOBJx)) as VINVx; pose proof VINVx as (Vsz & Vlen & _);
    pose proof (proj1 (proj2 (proj2 (proj2 SOBJx)))) as VLBx;
    pose proof (as_live_disjoint LPA _ _ _ VEP 312 (v Fvsb) 40 AINVx VLVx (proj1 (proj2 (proj2 SOBJx))) NES) as DVS;
    pose proof (as_live_disjoint LPA _ _ _ VEP 312 _ _ AINVx VLVx VLBx NEBx) as DVB;
    unfold kHighMemBeg in *; all_app_facts;
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact Vhi)) as SHVB; rewrite SHMAX_val in SHVB;
    change ((312 + 7) / 8) with 39 in SHVB;
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINVx VLVx) as SHV0; fold_cl_segs; fold_aview;
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0;
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0;
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity);
    pose proof BSEGx as BSEG0; hide BSEG0; hide DVS; hide DVB.

  Local Definition mc_stepB' := mc_stepB (* [comment removed for export] *) VEP v tag q vv H p mark n seg lo ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A T
                     HEC HCRC HC64 HCB AINV MI A0 A1 A2 HMK VOBJ VBASE HENV HLM CNT N0 NMX SOBJ NES NEB EM LBM NLV SCM PCM FY BSEG LSEG VPLO PHI SHSEG SEGH TP SP16 ST CEIL LO K.
  Local Definition mc_stepE' := mc_stepE (* [comment removed for export] *) VEP v tag q vv H p mark n seg lo ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A T
                     HEC HCRC HC64 HCB AINV MI A0 A1 A2 HMK VOBJ VBASE HENV HLM CNT N0 NMX SOBJ NES NEB EM LBM NLV SCM PCM FY BSEG LSEG VPLO PHI SHSEG SEGH TP SP16 ST CEIL LO K.

  (* [comment removed for export] *)
  Local Ltac to_stepE :=
    lazymatch goal with
    | VEPC : rw_cells _ ?mq VEP _, MU : munch _ (aview A m) ?mq, WM : wmono _ (aview A m) ?mq,
      FR : rw_cells _ ?mq (bv_unsigned sp + -160) (CB 24 ?j0 :: _), STq : stk _ ?mq lo _, MIq : mem_inv _ ?mq
      |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply (mc_stepE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 mq); [exact MIq | exact STq | exact FR | exact VEPC | exact MU | exact WM]
    end.

  (* [comment removed for export] *)
  Local Ltac to_stepB AINV MU WM CFP MH HG :=
    lazymatch goal with STq : stk _ ?mq lo _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
    astop AINV MU WM CFP;
    lazymatch goal with
    | AINV1 : ainv A ?m1 ?md1, SBM : same_but_materialized md ?md1,
      VEPC : rw_cells _ (aview A ?m1) VEP _, FR : rw_cells _ (aview A ?m1) (bv_unsigned sp + -160) (CB 24 ?j0 :: _),
      B0 : kept (bytes_at _ (aview A m) (v Fver_p) seg),
      SV : kept ((v Fver_p + _ <= VEP \/ _)%Z), DS : kept ((VEP + 312 <= v Fvsb \/ _)%Z), DB : kept ((VEP + 312 <= vb_buf _ \/ _)%Z)
      |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
      assert (MP : mapped (aview A m1) (bv_unsigned sp - 8800) 8800)
        by (eapply (window_mapped LPA _ lo); [exact STq | exact FR | cbn; lia | exact CEIL | lia | lia]);
      unhide B0; unhide SV; unhide DS; unhide DB;
      eapply (mc_stepB' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 A m1 md1 v vv);
      [ exact AINV1 | assumption
      | apply amd_frame_sbm; [exact SBM | exact MH]
      | exact STq | exact FR | exact VEPC | exact (proj1 VOBJ)
      | apply vkeep_refl | reflexivity | exact CNT
      | eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM| intros a__ Ha__; cbn; lia]
      | lia | lia | unhide NEB; exact NEB | left; reflexivity | intros r _ _; reflexivity
      | apply frames_same_aged; intros ff; reflexivity
      | lia | reflexivity | reflexivity | lia | lia (* [comment removed for export] *)
      | eapply henv_ok_munch; [exact HENV| exact MU| exact WM| exact HG|];
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
        change (8192 / 8) with 1024 in Ha__; cbn; lia
      | eapply (bytes_at_munch LPA); [exact B0| exact MU| intros a__ Ha__; cbn; lia]
      | exact SV
      | unfold_stacks; eapply (cframe_noalloc LPA); [exact MU | | exact MP | intros a X; right; left; exact X];
        intros a Ha NO; cbn [outside] in NO; unfold Vmc, blk; lia ]
    end end.

  #[using="l K LO CEIL ST SP16 TP SEGH SHSEG PHI VPLO LSEG BSEG FY SCM PCM NLV LBM EM NEB NES SOBJ NMX N0 CNT HLM HENV VBASE VOBJ HMK A2 A1 A0 MI AINV HCB HC64 HCRC HEC A lo seg n mark p H vv q tag v VEP AI Clg"] Lemma mc_main :
    srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 vep_mark_common_entry) fc None m (seg_rom rsegs)) md) T.
  Proof.
    rewrite A0, A1, A2. unfold vep_mark_common_entry.
    pose proof VOBJ as (VLV & VEPC & _ & _).
    pose proof seg_ranges as (SEGV & SEGS & SEGB). clear SEGS SEGB.
    seg_prelims AINV VLV SOBJ NEB BSEG. hide HMK. hide BSEG.
    pose proof CNT as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
    pose proof (as_minv LPA A _ _ AINV) as [_ MH].
    pose proof (proj1 HENV) as [agex HFRx].
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS agex VEP 312 AINV HFRx VLV) as DJv.
    change (fsize HCLASS) with 8192 in DJv.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(unfold HFSIZE in G3; lia)) as SHF.
    rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    pose proof (cenv_intro A m md AINV) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC. fold_aview. open_map_cells MC.
    unfold vep_cells in VEPC.
    hide SEGV. hide_slow. unhide V8.
    pose proof (munch_refl [(bv_unsigned sp - 8800, bv_unsigned sp); (VEP, VEP + 312)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WMAPx : mapped (aview A m) (bv_unsigned sp - 8800) 8800).
    { eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8800, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8800)) with 8800 by lia; exact WMAPx |].
      split; [right; left; exists VEP, 312; split; [exact VLV|lia]| exact I]. }
    (* [comment removed for export] *)
    pose proof MI as MIw. pose proof ST as STw. hide MI. hide ST.
    ago AINV. fold_cl_segs.
    carve_frame 160%nat STw.
    (* [comment removed for export] *)
    do 14 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KB; zify_cond KB. { exfalso. unhide HMK. clear - KB HMK; try pose proof alloc_ceiling_val as ACV__. destruct HMK as [-> | ->]; klia KB. } clear KB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KA; zify_cond KA. { exfalso. apply KA. apply land7_of_mod8; [lia | exact V8]. } clear KA. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep.
    pose proof SHV0 as SHT. rewrite EzsV in SHT. zstep. zstep. shadow_addr SHT 4. clear SHT. shadow_cleanup.
    zstep. vrechk SHV0 EzsV (VEP + 304) 4 0.
    (* [comment removed for export] *)
    zstep. unhide HLM. rewrite (sx32_small (v Flast_mark)) by (clear - HLM; try pose proof alloc_ceiling_val as ACV__; destruct HLM as [-> | ->]; lia). hide HLM.
    do 6 zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KM; zify_cond KM.
    - (* [comment removed for export] *)
      vchk SHV0 EzsV 8 0. zstep. zstep. if_cases KW; zify_cond KW.
      + (* [comment removed for export] *)
        to_stepE.
      + (* [comment removed for export] *)
        zstep. vchk SHV0 EzsV 4 0. zstep. zstep. if_cases KS; zify_cond KS.
        * to_stepB AINV MU WM CFP MH HG.
        * to_stepE.
    - (* [comment removed for export] *)
      vchk SHV0 EzsV 8 0. zstep. zstep. zstep. if_cases KQ; zify_cond KQ.
      + to_stepB AINV MU WM CFP MH HG.
      + (* [comment removed for export] *)
        vchk SHV0 EzsV 8 0. zstep. zstep. if_cases KP; zify_cond KP.
        * to_stepB AINV MU WM CFP MH HG.
        * (* [comment removed for export] *)
          do 15 zstep.
          try replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
          release_frame FR STw (bv_unsigned sp).
          astop AINV MU WM CFP.
          unhide DVS. unhide DVB. unhide SEGV. unhide BSEG0. unhide HMK. unhide HLM. unhide NEB.
          lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mf _) ?mdf) _ =>
            assert (MP : mapped (aview A mf) (bv_unsigned sp - 8800) 8800) by (eapply (stk_mapped (L:=LPA)); [exact STw | exact CEIL | lia | lia]);
            eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A mf mdf (fupd (fupd v Fcrc ((v Fcrc) mod 2^64)) Fcrcp ((v Fcrcp) mod 2^64)) vv);
            [ assumption | assumption | apply amd_frame_sbm; [exact SBM | exact MH] | exact STw
            | split; [exact VLV|]; split; [unfold vep_cells, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; rewrite !Z_to_bv_mod64; exact VEPC|];
              exact (proj2 (proj2 VOBJ))
            | repeat (apply vkeep_fupd; [| in_tac]); apply vkeep_refl
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; klia KQ
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; clear - KM HMK HLM; try pose proof alloc_ceiling_val as ACV__;
              rewrite !Z.mod_small in KM by (clear KM; destruct HMK as [X|X]; destruct HLM as [Y|Y]; lia); exact KM
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; klia KP
            | unfold vep_cnt, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; unfold vep_cnt in CNT; klia KQ
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; apply Z.mod_pos_bound; lia
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; apply Z.mod_pos_bound; lia
            | eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM| intros a__ Ha__; cbn; lia]
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; lia
            | lia
            | left; reflexivity | intros r _ _; reflexivity
            | apply frames_same_aged; intros ff; reflexivity
            | lia | reflexivity | reflexivity | lia | lia (* [comment removed for export] *)
            | eapply henv_ok_munch; [exact HENV| exact MU| exact WM| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
              change (8192 / 8) with 1024 in Ha__; cbn; lia
            | eapply (bytes_at_munch LPA); [exact BSEG0| exact MU| intros a__ Ha__; cbn; lia]
            | unfold_stacks; eapply (cframe_noalloc LPA); [exact MU | | exact MP | intros a X; right; left; exact X];
              intros a Ha NO; cbn [outside] in NO; unfold blk; lia ]
          end.
  Qed.
End S.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vep_mark_common_ok {AI : AsanAlloc LPA} {AI16 : AsanAlloc16} :
  vep_emit_common_stmt -> crc32_stmt -> crc32_combine_stmt2 -> vep_default_cb_stmt -> vep_mark_common_stmt.
Proof. intros HEC HCRC HC64 HCB. unfold vep_mark_common_stmt. intros. eapply mc_main; eassumption. Qed.

End CEIL.

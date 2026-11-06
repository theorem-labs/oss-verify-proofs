(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World U_Img ImgU U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_VS58t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_vegk2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_ve2lq.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_VS58t OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cromo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cr6ux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_vegk2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve2lq.U_veyab.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_ve2lq.

Module U_vejdy.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World U_Img ImgU U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_VS58t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_vegk2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_ve2lq.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_VS58t OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cromo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cr6ux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_vegk2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve2lq.U_veyab.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import U_ve2lq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold CRC_FRAME_U, C64_FRAME in H.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (H : henv) (p mark n : Z) (seg : list byte) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 p.
  Hypothesis A2 : a2 = Z_to_bv 64 mark.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LayoutPU A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutPU VIU H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_okU m.
  Hypothesis HLM : bool01 (v Flast_mark).
  Hypothesis CNT : vep_cnt v n.
  Hypothesis N0 : 0 <= n.
  Hypothesis NMX : n + (p - v Fver_p) < NMAX.
  Hypothesis SOBJ : vsb_obj LayoutPU A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis EM : vb_size vv + 9 <= EXT_MAX.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vsb_extendsize (vb_size vv + 9) <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis BSEG : bytes_at rsegs m (v Fver_p) seg.
  Hypothesis LSEG : Z.of_nat (length seg) = p - v Fver_p.
  Hypothesis VPLO : 4096 <= v Fver_p.
  Hypothesis PHI : p <= alloc_ceiling.
  Hypothesis SEGH : (v Fver_p = vi_empty VIU /\ seg = []) \/
                    (exists d k, a_live A d = Some k /\ 0 < k /\ d <= v Fver_p /\ p <= d + k /\ d <> VEP /\ d <> v Fvsb /\ d <> vb_buf vv).
  Hypothesis TP : tp = al_tp LayoutPU.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + MARK_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          vep_obj LayoutPU A' m' VEP v' tag q -> vkeep v v' MARK_FIELDS ->
          v' Fver_p = p -> v' Flast_mark = mark -> v' Fo_pending = 0 -> vep_cnt v' (n + (p - v Fver_p)) ->
          0 <= v' Fcrc < 2^64 -> 0 <= v' Fcrcp < 2^64 ->
          vsb_obj LayoutPU A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + 3 * (v' Fo_last - v Fo_last) ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> a_live A' r = a_live A r) ->
          a_livebytes A' = a_livebytes A + vb_size vv' - vb_size vv -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
          henv_ok LayoutPU VIU H m' -> bytes_at rsegs m' (v Fver_p) seg ->
          cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) MARK_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  Let Vmc : Z -> Prop := fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40).
  Let l : Z := p - v Fver_p.

  (* [comment removed for export] *)
  Local Definition henv_ok_ccall0' := @henv_ok_ccall0 _ AI v H p seg ra sp HG.
  Local Definition henv_ok_munch0' := @henv_ok_munch0 _ AI VEP v H p seg lo ra sp HG SP16 CEIL LO SPH.
  Local Definition seg_ranges' := @seg_ranges _ AI VEP v tag q vv p seg ra sp m md A AINV VOBJ SOBJ NES NEB LSEG SEGH.
  Local Definition mc_step4' := @mc_step4 _ AI VEP v tag q vv H p mark n seg lo ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T
                     AINV MI A0 A1 A2 HMK VOBJ VBASE HENV HG IMG HLM CNT N0 NMX SOBJ NES NEB EM LBUD NBUD BSEG LSEG VPLO PHI SEGH TP SP16 RA2 ST CEIL LO SPH K.

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj A2 (conj HMK (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG
      (conj HLM (conj CNT (conj N0 (conj NMX (conj SOBJ (conj NES (conj NEB (conj EM (conj LBUD (conj NBUD (conj BSEG (conj LSEG (conj VPLO (conj PHI
      (conj SEGH (conj TP (conj SP16 (conj RA2 (conj ST (conj CEIL (conj LO (conj SPH K))))))))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutPU)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VIU] in ECB, EURL;
    pose proof CNT as (CN1 & CN2 & CN3 & CN4 & CN5 & CN6 & CN7);
    unfold MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK, NMAX in *.

  (* [comment removed for export] *)
  Local Ltac leaf_side :=
    lazymatch goal with
    | |- mem_inv _ _ => assumption
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
    | |- @eq (bv _) _ _ => first [reflexivity | rewrite ?unsigned_lit by lia; reflexivity]
    | |- rw_cells _ _ _ _ => eassumption
    | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
    | |- length _ = _ => assumption
    | |- vep_pads_wf _ => assumption
    | |- (_ mod 8 = 0)%Z => first [apply mod8_of_mod16; assumption | unfold h_vc; apply align_mod8_of16; [match goal with G : (h_sp H mod 16 = 0)%Z |- _ => exact G | G : kept (h_sp H mod 16 = 0)%Z |- _ => exact G end| reflexivity]]
    | |- _ => rewrite ?unsigned_lit by lia;
            repeat match goal with H : (_ <= _ \/ _ <= _)%Z |- _ => clear H end;
            first [ lia | rewrite Z.mod_small by lia; lia | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; lia ]
    end.

  (* [comment removed for export] *)
  Local Ltac seg_prelims AINVx VLVx SOBJx NEBx BSEGx :=
    prelims;
    (first [ pose proof ((as_live_ok _ _ _ VEP _ AINVx VLVx)) as dR_1; dand7 dR_1 as _ V16 Vlo Vhi Vimg Vmap Vown | pose proof (as_live_ok _ _ _ VEP _ AINVx VLVx) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown) ]);
    pose proof VOBJ as (_ & _ & TAG & PADS); (first [ pose proof (PADS) as dR_2; dand7 dR_2 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    pose proof (bytes_at_bound _ _ _ _ BSEGx) as SEGBD;
    assert (Ehvc : h_vc H = h_sp H + 1304) by reflexivity;
    (first [ pose proof ((vsb_obj_geom LayoutPU _ _ _ (v Fvsb) _ false AINVx SOBJx)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg _ Smap Bmap | pose proof (vsb_obj_geom LayoutPU _ _ _ (v Fvsb) _ false AINVx SOBJx) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & _ & Smap & Bmap) ]);
    pose proof (proj1 (proj2 SOBJx)) as VINVx; (first [ pose proof (VINVx) as dR_4; dand3 dR_4 as Vsz Vlen _ | pose proof VINVx as (Vsz & Vlen & _) ]);
    pose proof (proj1 (proj2 (proj2 (proj2 SOBJx)))) as VLBx;
    pose proof (as_live_disjoint _ _ _ VEP 312 (v Fvsb) 40 AINVx VLVx (proj1 (proj2 (proj2 SOBJx))) NES) as DVS;
    pose proof (as_live_disjoint _ _ _ VEP 312 _ _ AINVx VLVx VLBx NEBx) as DVB;
    pose proof BSEGx as BSEG0; hide BSEG0; hide DVS; hide DVB.

  (* [comment removed for export] *)
  Local Ltac to_step4 AINVx VLVx VK EVP SOBJx LENx SZx NEBx RELx LIVEx HENVx CFx :=
    lazymatch goal with
    | VEPC : rw_cells _ ?mq VEP ?cs, MU : munch ?W ?mx ?mq, WM : wmono _ ?mx ?mq, CFP : client_fp _ ?Ax ?W,
      FR : rw_cells _ ?mq (bv_unsigned sp + -48) _, STq : stk _ ?mq lo _,
      B0 : kept (bytes_at _ ?mx (v Fver_p) seg), SV : kept ((v Fver_p + _ <= VEP \/ _)%Z),
      DS : kept ((VEP + 312 <= v Fvsb \/ _)%Z), DB : kept ((VEP + 312 <= vb_buf _ \/ _)%Z),
      ACV' : (_ <= alloc_ceiling <= _)%Z, SEGBD' : (0 <= v Fver_p /\ _)%Z, Shi' : (v Fvsb + 40 <= alloc_ceiling)%Z,
      Bhi' : (vb_buf _ + vb_size _ <= alloc_ceiling)%Z, Vlo' : (4096 <= VEP)%Z, Vhi' : (VEP + 312 <= alloc_ceiling)%Z
      |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      lazymatch cs with context [C8 (Z_to_bv 64 (?vx Fcb_x + ?pend)) :: C8 (Z_to_bv 64 (?vx Fstate)) :: _] =>
      lazymatch cs with context [C8 (Z_to_bv 64 ?ow) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 (vx Fo_total)) :: C4 ?cw :: CB 4 (p124 q) :: C8 (Z_to_bv 64 ?oc) :: C4 ?pw :: _] =>
      set (v3 := fupd (fupd (fupd (fupd (fupd (fupd vx Fcb_x (vx Fcb_x + pend)) Fcrc (bv_unsigned cw)) Fo_crc oc)
                       Fo_wait ow) Fo_pending 0) Fcrcp (bv_unsigned pw));
      assert (VEPC3 : rw_cells rsegs mq VEP (vep_cells v3 tag q))
        by (unfold vep_cells, v3; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; rewrite ?Z_to_bv_bv_unsigned; exact VEPC);
      clear VEPC;
      pose proof (ainv_munch LayoutPU Ax mx mq _ _ AINVx MU WM CFP) as AINV3;
      unhide B0; unhide SV;
      apply (bytes_at_transport rsegs W mx mq _ seg) in B0; [| exact MU | clear - SV LSEG PHI CEIL LO ACV' SEGBD'; cbn [disjoint_from]; lia ];
      unhide DS;
      assert (D40 : disjoint_from W (v Fvsb) 40) by (clear - DS Shi' CEIL LO ACV'; cbn [disjoint_from]; lia);
      hide DS; unhide DB;
      assert (SOBJ3 : vsb_obj LayoutPU Ax mq (v Fvsb) _ false)
        by (eapply (vsb_obj_munch LayoutPU); [exact SOBJx | exact MU | exact WM | exact D40 | clear - DB Bhi' CEIL LO ACV'; cbn [disjoint_from]; lia]);
      assert (HENV3 : henv_ok LayoutPU VIU H mq) by (eapply henv_ok_munch0'; [exact HENVx | exact MU | exact WM | exact Vhi' | assumption]);
      assert (MP : mapped mq (bv_unsigned sp - 8480) 8480)
        by (eapply (window_mapped LayoutPU _ lo); [exact STq | exact FR | cbn; lia | exact CEIL | lia | lia]);
      assert (CF2 : cframe LayoutPU (owned Ax) (owned Ax) (bv_unsigned sp) 8480 Vmc nowhere mx mq)
        by (eapply (cframe_noalloc LayoutPU); [exact MU | | exact MP | intros a X; destruct X];
            intros a Ha NO; cbn [outside] in NO; clear - Ha NO Vlo'; unfold Vmc, blk; lia);
      eapply (mc_step4' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ax mq _ v3 _);
      [ eassumption | eassumption | exact AINV3 | assumption | eassumption | exact STq | exact FR | exact VEPC3 | exact VLVx
      | unfold v3; vkeep_tac VK
      | unfold v3, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact EVP
      | reflexivity
      | unfold vep_cnt, v3, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; unfold vep_cnt in *; lia
      | exact SOBJ3
      | unfold v3, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact LENx
      | exact SZx
      | exact NEBx | exact RELx | exact LIVEx | eassumption | eassumption | exact HENV3 | exact B0 | exact SV
      | unfold MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK;
        eapply (cframe_seq LayoutPU _ _ _ _ _ _ _ _ _ _ _ _ _ m mx mq CFx CF2);
        [ lia | lia | exact MP | intros a X; exact X | intros a X; right; exact X | intros a X; left; exact X ] ]
      end end
    end.

  (* [comment removed for export] *)
  Local Ltac ovf64 KO :=
    lazymatch type of KO with context [Z.b2z ?c] => idtac end;
    repeat match goal with H : _ |- _ => lazymatch type of H with
      | vep_cnt _ _ => fail | (0 <= n)%Z => fail | (n + _ < _)%Z => fail | (_ = p - v Fver_p)%Z => fail
      | _ => lazymatch H with KO => fail | _ => clear H end end end;
    unfold vep_cnt in *; unsign KO;
    repeat match type of KO with context [?a <? ?b] => destruct (Z.ltb_spec a b); cbn in KO end; lia.

  (* [comment removed for export] *)
  Local Ltac step3_tail :=
    zstep; zstep; zstep; zstep; zstep;
    call_fr (crc32_null_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) _ lo) by (idtac; leaf_side);
    zstep; zstep; zstep; zstep; zstep; zstep;
    let KO := fresh "KO" in
    zstep; if_cases KO; zify_cond KO; [ exfalso; ovf64 KO |]; clear KO;
    zstep; zstep;
    lazymatch goal with AINVx : ainv ?Ax ?mx _, CFx : cframe _ (owned A) (owned ?Ax) _ _ _ _ m ?mx,
                        VLVx : a_live ?Ax VEP = Some 312, VK : vkeep v ?vx MARK_FIELDS, EVP : ?vx Fver_p = v Fver_p,
                        SOBJx : vsb_obj _ ?Ax ?mx (v Fvsb) ?vvx false,
                        LENx : (vb_len vv <= vb_len ?vvx <= vb_len vv + 3 * (?vx Fo_last - v Fo_last))%Z,
                        SZx : (vb_size vv <= vb_size ?vvx <= _)%Z,
                        NEBx : kept (VEP <> vb_buf ?vvx), RELx : (vb_buf ?vvx = vb_buf vv \/ _),
                        LIVEx : (forall r, r <> vb_buf vv -> r <> vb_buf ?vvx -> a_live ?Ax r = a_live A r),
                        HENVx : henv_ok _ _ H ?mx |- _ =>
      to_step4 AINVx VLVx VK EVP SOBJx LENx SZx NEBx RELx LIVEx HENVx CFx
    end.

  (* [comment removed for export] *)
  #[using="l K SPH LO CEIL ST RA2 SP16 TP SEGH PHI VPLO LSEG BSEG EM LBUD NBUD NEB NES SOBJ NMX N0 CNT HLM IMG HG HENV VBASE VOBJ HMK A2 A1 A0 MI AINV a2 a1 a0"] Lemma mc_step3 :
    forall (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word) (j8 : list byte)
           (Ax : AS) (mx : mem) (mdx : Model) (vx : vep) (vvx : vsb_rec),
      m_halted mdx = None -> m_vm_lazy mdx = [] ->
      ainv Ax mx mdx -> mem_inv rsegs mx -> md_frame md mdx ->
      stk rsegs mx lo (bv_unsigned sp + -48) ->
      rw_cells rsegs mx (bv_unsigned sp + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs mx VEP (vep_cells vx tag q) -> a_live Ax VEP = Some 312 ->
      vkeep v vx MARK_FIELDS -> vx Fver_p = v Fver_p -> vep_cnt vx n ->
      vsb_obj LayoutPU Ax mx (v Fvsb) vvx false ->
      vb_len vv <= vb_len vvx <= vb_len vv + 3 * (vx Fo_last - v Fo_last) ->
      vb_size vv <= vb_size vvx <= Z.max (vb_size vv) (vb_len vvx + 4096) -> VEP <> vb_buf vvx ->
      (vb_buf vvx = vb_buf vv \/ (a_live A (vb_buf vvx) = None /\ a_live Ax (vb_buf vv) = None)) ->
      (forall r, r <> vb_buf vv -> r <> vb_buf vvx -> a_live Ax r = a_live A r) ->
      a_livebytes Ax = a_livebytes A + vb_size vvx - vb_size vv -> a_nlive Ax = a_nlive A ->   (* [comment removed for export] *)
      henv_ok LayoutPU VIU H mx -> bytes_at rsegs mx (v Fver_p) seg ->
      (v Fver_p + Z.of_nat (length seg) <= VEP \/ VEP + 312 <= v Fver_p) ->
      cframe LayoutPU (owned A) (owned Ax) (bv_unsigned sp) MARK_STACK Vmc (blk (vb_buf vvx) (vb_size vvx)) m mx ->
      evt rsegs (rz_at rsegs mdx T)
          (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 mark) (Z_to_bv 64 VEP)
                   xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 p) xs3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              bvmap_empty (Z_to_bv 64 0x1b1ac) (Z_to_bv 32 0) None mx (seg_rom rsegs)).
  Proof.
    touch_all.
    intros until vvx. intros MDHx MDLx AINVx MIx MDFx STx FR VEPC VLVx VK EVP CNTx SOBJx LENx SZx NEBx RELx LIVEx LBx NLx HENVx BSEGx SEGV CFx.
    seg_prelims AINVx VLVx SOBJx NEBx BSEGx. hide HMK. hide HLM. hide SEGV. clear BSEGx. hide_slow.
    (first [ pose proof (CNTx) as dR_5; dand7 dR_5 as D1 D2 D3 D4 D5 D6 D7 | pose proof CNTx as (D1 & D2 & D3 & D4 & D5 & D6 & D7) ]).
    assert (EVCx : vx Fvc = h_vc H) by (rewrite (VK Fvc ltac:(notin_tac)); exact EVC).
    assert (ECBx : vx Fcb = 114388) by (rewrite (VK Fcb ltac:(notin_tac)); exact ECB).
    assert (EPRx : vx Fcb_priv = VEP + 56) by (rewrite (VK Fcb_priv ltac:(notin_tac)); exact EPRIV).
    pose proof VEPC as VEPCF. hide VEPCF. unfold vep_cells in VEPC.
    pose proof (munch_refl [(bv_unsigned sp - 8480, bv_unsigned sp); (VEP, VEP + 312)] mx) as MU.
    pose proof (wmono_refl rsegs mx) as WM.
    assert (CFP : client_fp LayoutPU Ax [(bv_unsigned sp - 8480, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLVx|lia]| exact I]. }
    (* [comment removed for export] *)
    zstep. zstep. if_cases KP; zify_cond KP.
    { (* [comment removed for export] *)
      unhide BSEG0. unhide SEGV. unhide DVS. unhide DVB. unhide VEPCF. clear VEPC MU WM CFP.
      eapply (mc_step4' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j8 Ax mx mdx vx vvx); try eassumption; klia KP. }
    (* [comment removed for export] *)
    unhide VEPCF.
    zstep. zstep. zstep. zstep. rewrite EVCx, ECBx, EPRx. zstep.
    (first [ pose proof ((proj1 (proj2 HENVx))) as dR_6; dex2 dR_6 as vcpad vcrest; dand3 dR_6 as LP1 LR1 VCX | pose proof ((proj1 (proj2 HENVx))) as dR_6; dand5 dR_6 as vcpad vcrest LP1 LR1 VCX | pose proof (proj1 (proj2 HENVx)) as (vcpad & vcrest & LP1 & LR1 & VCX) ]). cbn [al_segs LayoutPU] in VCX.
    clear VEPC.
    call_fr (vep_default_cb_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) _
               (h_vc H) VEP vx tag q (vx Fo_pending) vcpad (h_resp H) (h_wrk H) vcrest) by (idtac; leaf_side).
    (* [comment removed for export] *)
    lazymatch goal with P : rw_cells _ _ VEP (vep_cells _ tag q) |- _ => rename P into VEPC end.
    unfold vep_cells in VEPC. cbn [fupd vf_beq vf_index N.eqb Pos.eqb] in VEPC.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      step3_tail.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      call_fr (crc32_combine_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) _ lo) by (idtac; leaf_side).
      zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases KO; zify_cond KO; [| exfalso; ovf64 KO]. clear KO.
      step3_tail.
  Qed.

End S.
End U_vejdy.


Module U_veshp.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World U_Img ImgU U_Cov8m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_VS58t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_crc32.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_vegk2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_ve2lq.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_VS58t OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cromo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_crc32.U_cr6ux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_vegk2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve2lq.U_veyab.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_ve2lq.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve2lq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve3w7.U_vejdy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold CRC_FRAME_U, C64_FRAME in H.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (H : henv) (p mark n : Z) (seg : list byte) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 p.
  Hypothesis A2 : a2 = Z_to_bv 64 mark.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LayoutPU A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutPU VIU H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_okU m.
  Hypothesis HLM : bool01 (v Flast_mark).
  Hypothesis CNT : vep_cnt v n.
  Hypothesis N0 : 0 <= n.
  Hypothesis NMX : n + (p - v Fver_p) < NMAX.
  Hypothesis SOBJ : vsb_obj LayoutPU A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis EM : vb_size vv + 9 <= EXT_MAX.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vsb_extendsize (vb_size vv + 9) <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis BSEG : bytes_at rsegs m (v Fver_p) seg.
  Hypothesis LSEG : Z.of_nat (length seg) = p - v Fver_p.
  Hypothesis VPLO : 4096 <= v Fver_p.
  Hypothesis PHI : p <= alloc_ceiling.
  Hypothesis SEGH : (v Fver_p = vi_empty VIU /\ seg = []) \/
                    (exists d k, a_live A d = Some k /\ 0 < k /\ d <= v Fver_p /\ p <= d + k /\ d <> VEP /\ d <> v Fvsb /\ d <> vb_buf vv).
  Hypothesis TP : tp = al_tp LayoutPU.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + MARK_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          vep_obj LayoutPU A' m' VEP v' tag q -> vkeep v v' MARK_FIELDS ->
          v' Fver_p = p -> v' Flast_mark = mark -> v' Fo_pending = 0 -> vep_cnt v' (n + (p - v Fver_p)) ->
          0 <= v' Fcrc < 2^64 -> 0 <= v' Fcrcp < 2^64 ->
          vsb_obj LayoutPU A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + 3 * (v' Fo_last - v Fo_last) ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> a_live A' r = a_live A r) ->
          a_livebytes A' = a_livebytes A + vb_size vv' - vb_size vv -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
          henv_ok LayoutPU VIU H m' -> bytes_at rsegs m' (v Fver_p) seg ->
          cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) MARK_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  Let Vmc : Z -> Prop := fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40).
  Let l : Z := p - v Fver_p.

  (* [comment removed for export] *)
  Local Definition henv_ok_ccall0' := @henv_ok_ccall0 _ AI v H p seg ra sp HG.
  Local Definition henv_ok_munch0' := @henv_ok_munch0 _ AI VEP v H p seg lo ra sp HG SP16 CEIL LO SPH.
  Local Definition seg_ranges' := @seg_ranges _ AI VEP v tag q vv p seg ra sp m md A AINV VOBJ SOBJ NES NEB LSEG SEGH.
  Local Definition mc_step4' := @mc_step4 _ AI VEP v tag q vv H p mark n seg lo ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T
                     AINV MI A0 A1 A2 HMK VOBJ VBASE HENV HG IMG HLM CNT N0 NMX SOBJ NES NEB EM LBUD NBUD BSEG LSEG VPLO PHI SEGH TP SP16 RA2 ST CEIL LO SPH K.

  Local Definition mc_step3' := @mc_step3 _ AI VEP v tag q vv H p mark n seg lo ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T
                     AINV MI A0 A1 A2 HMK VOBJ VBASE HENV HG IMG HLM CNT N0 NMX SOBJ NES NEB EM LBUD NBUD BSEG LSEG VPLO PHI SEGH TP SP16 RA2 ST CEIL LO SPH K.
  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj A2 (conj HMK (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG
      (conj HLM (conj CNT (conj N0 (conj NMX (conj SOBJ (conj NES (conj NEB (conj EM (conj LBUD (conj NBUD (conj BSEG (conj LSEG (conj VPLO (conj PHI
      (conj SEGH (conj TP (conj SP16 (conj RA2 (conj ST (conj CEIL (conj LO (conj SPH K))))))))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutPU)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VIU] in ECB, EURL;
    pose proof CNT as (CN1 & CN2 & CN3 & CN4 & CN5 & CN6 & CN7);
    unfold MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK, NMAX in *.

  (* [comment removed for export] *)
  Local Ltac leaf_side :=
    lazymatch goal with
    | |- mem_inv _ _ => assumption
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
    | |- @eq (bv _) _ _ => first [reflexivity | rewrite ?unsigned_lit by lia; reflexivity]
    | |- rw_cells _ _ _ _ => eassumption
    | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
    | |- length _ = _ => assumption
    | |- vep_pads_wf _ => assumption
    | |- (_ mod 8 = 0)%Z => first [apply mod8_of_mod16; assumption | unfold h_vc; apply align_mod8_of16; [match goal with G : (h_sp H mod 16 = 0)%Z |- _ => exact G | G : kept (h_sp H mod 16 = 0)%Z |- _ => exact G end| reflexivity]]
    | |- _ => rewrite ?unsigned_lit by lia;
            repeat match goal with H : (_ <= _ \/ _ <= _)%Z |- _ => clear H end;
            first [ lia | rewrite Z.mod_small by lia; lia | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; lia ]
    end.

  (* [comment removed for export] *)
  Local Ltac seg_prelims AINVx VLVx SOBJx NEBx BSEGx :=
    prelims;
    (first [ pose proof ((as_live_ok _ _ _ VEP _ AINVx VLVx)) as dR_1; dand7 dR_1 as _ V16 Vlo Vhi Vimg Vmap Vown | pose proof (as_live_ok _ _ _ VEP _ AINVx VLVx) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown) ]);
    pose proof VOBJ as (_ & _ & TAG & PADS); (first [ pose proof (PADS) as dR_2; dand7 dR_2 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    pose proof (bytes_at_bound _ _ _ _ BSEGx) as SEGBD;
    assert (Ehvc : h_vc H = h_sp H + 1304) by reflexivity;
    (first [ pose proof ((vsb_obj_geom LayoutPU _ _ _ (v Fvsb) _ false AINVx SOBJx)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg _ Smap Bmap | pose proof (vsb_obj_geom LayoutPU _ _ _ (v Fvsb) _ false AINVx SOBJx) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & _ & Smap & Bmap) ]);
    pose proof (proj1 (proj2 SOBJx)) as VINVx; (first [ pose proof (VINVx) as dR_4; dand3 dR_4 as Vsz Vlen _ | pose proof VINVx as (Vsz & Vlen & _) ]);
    pose proof (proj1 (proj2 (proj2 (proj2 SOBJx)))) as VLBx;
    pose proof (as_live_disjoint _ _ _ VEP 312 (v Fvsb) 40 AINVx VLVx (proj1 (proj2 (proj2 SOBJx))) NES) as DVS;
    pose proof (as_live_disjoint _ _ _ VEP 312 _ _ AINVx VLVx VLBx NEBx) as DVB;
    pose proof BSEGx as BSEG0; hide BSEG0; hide DVS; hide DVB.

  (* [comment removed for export] *)
  Local Ltac mc_xfer FRK FR B0 CRfr CRseg SEGV SEGS SEGB :=
    acall_consts;
    lazymatch type of FRK with cframe ?L (owned ?A0) (owned ?A1) ?xsp ?win ?V ?N ?m0 ?m1 =>
      lazymatch type of FR with Step.rw_cells _ _ ?a ?cs =>
        apply (rw_cells_ccall L A0 A1 xsp win V N m0 m1 FRK a cs) in FR;
        [ | exact CRfr
          | cbn [Cells.cells_size Cells.csize Nat.add length app]; clear SEGV SEGS SEGB; split; [lia|];
            intros i Hi X; unfold blk, nowhere in X; cbn beta in X; lia ] end;
      lazymatch type of B0 with bytes_at _ _ ?a ?bs =>
        apply (bytes_at_ccall L A0 A1 xsp win V N m0 m1 FRK a bs) in B0;
        [ | exact CRseg
          | split; [clear SEGV SEGS SEGB; lia|];
            intros i Hi [X|[X|X]]; unfold blk, nowhere in X; cbn beta in X;
            [clear SEGS SEGB | clear SEGV SEGS | clear SEGV SEGB]; lia ] end;
      repeat match goal with H : crange _ m0 _ _ |- _ => clear H | H : mem_inv _ m0 |- _ => clear H | H : stk _ m0 _ _ |- _ => clear H end
    end.

  (* [comment removed for export] *)
  Local Ltac ovf64 KO :=
    lazymatch type of KO with context [Z.b2z ?c] => idtac end;
    repeat match goal with H : _ |- _ => lazymatch type of H with
      | vep_cnt _ _ => fail | (0 <= n)%Z => fail | (n + _ < _)%Z => fail | (_ = p - v Fver_p)%Z => fail
      | _ => lazymatch H with KO => fail | _ => clear H end end end;
    unfold vep_cnt in *; unsign KO;
    repeat match type of KO with context [?a <? ?b] => destruct (Z.ltb_spec a b); cbn in KO end; lia.

  (* [comment removed for export] *)
  #[using="l Vmc K SPH LO CEIL ST RA2 SP16 TP SEGH PHI VPLO LSEG BSEG EM LBUD NBUD NEB NES SOBJ NMX N0 CNT HLM IMG HG HENV VBASE VOBJ HMK A2 A1 A0 MI AINV A a2 a1 a0 seg n H vv AI Clg"] Lemma mc_step2 :
    forall (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (j8 : list byte) (m1 : mem),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -48) ->
      rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs m1 VEP (vep_cells v tag q) ->
      munch [(bv_unsigned sp - MARK_STACK, bv_unsigned sp); (VEP, VEP + 312)] m m1 -> wmono rsegs m m1 ->
      evt rsegs (rz_at rsegs md T)
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 mark) (Z_to_bv 64 VEP)
                   xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              bvmap_empty (Z_to_bv 64 0x1b164) (Z_to_bv 32 0) None m1 (seg_rom rsegs)).
  Proof.
    touch_all.
    intros until m1. intros MI1 ST1 FR VEPC MU WM.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    pose proof VOBJ as (VLV & _ & _ & _).
    (first [ pose proof (seg_ranges') as dR_5; dand3 dR_5 as SEGV SEGS SEGB | pose proof seg_ranges' as (SEGV & SEGS & SEGB) ]).
    seg_prelims AINV VLV SOBJ NEB BSEG. hide SEGV. hide SEGS. hide SEGB. hide_slow.
    pose proof CNT as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8480, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLV|lia]| exact I]. }
    unfold vep_cells in VEPC.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. rewrite EVC, ECB, EPRIV. zstep.
    (first [ pose proof ((proj1 (proj2 HENV))) as dR_6; dex2 dR_6 as vcpad vcrest; dand3 dR_6 as LP1 LR1 VCX | pose proof ((proj1 (proj2 HENV))) as dR_6; dand5 dR_6 as vcpad vcrest LP1 LR1 VCX | pose proof (proj1 (proj2 HENV)) as (vcpad & vcrest & LP1 & LR1 & VCX) ]). cbn [al_segs LayoutPU] in VCX.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport rsegs W m m1 _ _) in VCX; [| exact MU | exact WM | cbn [disjoint_from cells_size csize vc_cells Nat.add length]; lia ] end.
    call_fr (vep_default_cb_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) _
               (h_vc H) VEP v tag q 0 vcpad (h_resp H) (h_wrk H) vcrest) by (idtac; leaf_side).
    clear VCX.
    lazymatch goal with P : rw_cells _ _ VEP (vep_cells _ tag q) |- _ => pose proof P as VEPC; rename P into VEPCF end.
    unfold vep_cells in VEPC. cbn [fupd vf_beq vf_index N.eqb Pos.eqb] in VEPC. hide VEPCF.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KO; zify_cond KO. { exfalso. ovf64 KO. } clear KO.
    (* [comment removed for export] *)
    zstep. rewrite (sx32_small (v Flast_mark)) by (clear -HLM; destruct HLM; lia).
    zstep. zstep.
    apply rz_stop.
    (* [comment removed for export] *)
    unhide BSEG0.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ => lazymatch type of MU with munch ?W _ _ =>
      apply (bytes_at_transport rsegs W m mq _ seg) in BSEG0; [| exact MU | unhide SEGV; cbn [disjoint_from]; lia ];
      pose proof (ainv_munch LayoutPU A m mq md _ AINV MU WM CFP) as AINV1;
      unhide VEPCF; pose_cranges LayoutPU A mq AINV1;
      assert (CRS : crange A mq (v Fver_p) (Z.of_nat (length seg)))
        by (destruct SEGH as [[EV ES] | (d & k & LD & K0 & D0 & D1' & _)];
            [ rewrite ES; cbn; split; [lia|]; split; [lia|]; intros i Hi; lia
            | eapply (crange_block (L:=LayoutPU)); [exact AINV1 | exact LD | lia | lia | lia] ])
    end end.
    clear VEPC.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
    eapply (vep_emit_common_ok VEP (fupd v Fcb_x (v Fcb_x + 0)) tag q vv (v Fcb_x - v Fo_last) (v Flast_mark) lo
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq md A T);
      [ exact AINV1 | assumption | reflexivity | reflexivity | reflexivity
      | lia | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; lia | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; lia | exact HLM
      | split; [exact VLV|]; split; [exact VEPCF|]; split; assumption
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact EDZ
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; eapply (vsb_obj_munch LayoutPU); [exact SOBJ | exact MU | exact WM | unhide DVS; cbn [disjoint_from]; lia | unhide DVB; cbn [disjoint_from]; lia]
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact NES
      | exact NEB
      | exact EM | exact LBUD | exact NBUD
      | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; eassumption | exact CEIL
      | rewrite unsigned_lit by lia; unfold EMITC_STACK, EMITLEN_STACK, REALLOC_STACK; lia
      | rewrite unsigned_lit by lia; lia | ] end.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' v' vv' AINV' MI' MDF' ST' VOBJ' CASES SOBJ' LEN SZ REL LIVEq LBp NLp FRK.
    cbn [fupd vf_beq vf_index N.eqb Pos.eqb] in SOBJ', CASES, FRK.
    pose proof (as_lazy_nil A' m' md' AINV') as [MDL' MDH'].
    rewrite unsigned_lit in ST', FRK by lia. unfold EMITC_STACK, EMITLEN_STACK, REALLOC_STACK in FRK.
    (first [ pose proof ((vsb_obj_geom LayoutPU A' m' md' (v Fvsb) vv' false AINV' SOBJ')) as dR_7; dand9 dR_7 as _ _ _ _ _ Blo' Bhi' Bimg' _ | pose proof (vsb_obj_geom LayoutPU A' m' md' (v Fvsb) vv' false AINV' SOBJ') as (_ & _ & _ & _ & _ & Blo' & Bhi' & Bimg' & _) ]).
    pose proof (proj1 (proj1 (proj2 SOBJ'))) as Vsz'.
    (* [comment removed for export] *)
    assert (VF : vkeep v v' MARK_FIELDS /\ v' Fver_p = v Fver_p /\ v' Flast_mark = v Flast_mark /\ v' Fo_pending = v Fo_pending
                 /\ v' Fcb_x = v Fcb_x + 0 /\ 0 <= v' Fo_total <= v Fcb_x /\ v' Fo_crc = 0
                 /\ vb_len vv <= vb_len vv' <= vb_len vv + 3 * (v Fcb_x - v Fo_last)
                 /\ vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096)).
    { clear - CASES LEN SZ D1 D2 D3 D4 D5 D6 D7 N0.
      destruct CASES as [(L0 & -> & ->) | (L1 & c & ->)]; cbn [fupd vf_beq vf_index N.eqb Pos.eqb].
      - split; [apply vkeep_fupd; [apply vkeep_refl | in_tac] |]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
      - split; [repeat (apply vkeep_fupd; [| in_tac]); apply vkeep_refl |]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    clear CASES LEN SZ.
    (first [ dand9 VF as VK' EVP' ELM' EPD' ECX' ETOT' ECRC' RL' RS' | destruct VF as (VK' & EVP' & ELM' & EPD' & ECX' & ETOT' & ECRC' & RL' & RS') ]).
    assert (NEB2 : VEP <> vb_buf vv').
    { destruct REL as [E | [FRESH _]]; [rewrite E; exact NEB | intros X; rewrite <- X in FRESH; rewrite FRESH in VLV; discriminate]. }
    assert (SEGB2 : v Fver_p + Z.of_nat (length seg) <= vb_buf vv' \/ vb_buf vv' + vb_size vv' <= v Fver_p).
    { destruct SEGH as [[EV ES] | (d & k & LD & K0 & Dlo & Dhi & N1 & N2 & N3)].
      - rewrite EV, ES. cbn [vi_empty VIU length Z.of_nat]. unfold off_image in Bimg'. cbn [al_image_lo al_image_hi LayoutPU] in Bimg'. lia.
      - assert (N4 : d <> vb_buf vv')
          by (destruct REL as [E | [FRESH _]]; [rewrite E; exact N3 | intros X; rewrite <- X in FRESH; rewrite FRESH in LD; discriminate]).
        pose proof (LIVEq d N3 N4) as LD'. rewrite LD in LD'.
        pose proof (as_live_disjoint A' m' md' d k (vb_buf vv') (vb_size vv') AINV' LD' (proj1 (proj2 (proj2 (proj2 SOBJ')))) N4) as X3.
        lia. }
    (* [comment removed for export] *)
    clear VEPCF. hide HMK. hide HLM. hide RS'. hide RL'. hide SEGB2. hide ETOT'. hide_slow.
    unhide SEGV. unhide SEGS. unhide SEGB.
    lazymatch goal with CRfr : crange A _ (bv_unsigned sp + -48) _ |- _ =>
      mc_xfer FRK FR BSEG0 CRfr CRS SEGV SEGS SEGB end.
    hide SEGV. hide SEGS. hide SEGB. hide BSEG0. unhide RS'. unhide RL'. unhide SEGB2. unhide ETOT'.
    lazymatch type of FRK with cframe _ _ _ _ _ _ _ _ ?mc =>
      pose proof (munch_refl [(bv_unsigned sp - 8480, bv_unsigned sp); (VEP, VEP + 312)] mc) as MU2;
      pose proof (wmono_refl rsegs mc) as WM2 end.
    assert (VLV' : a_live A' VEP = Some 312) by (rewrite (LIVEq VEP NEB NEB2); exact VLV).
    assert (CFP2 : client_fp LayoutPU A' [(bv_unsigned sp - 8480, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLV'|lia]| exact I]. }
    (first [ pose proof (VOBJ') as dR_9; dand3 dR_9 as _ VEPC' _ | pose proof VOBJ' as (_ & VEPC' & _) ]). cbn [al_segs LayoutPU] in VEPC'. unfold vep_cells in VEPC'.
    rz_resume MDH' MDL'.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    set (vx2 := fupd (fupd v' Fo_wait 0) Fo_last (v Fcb_x)).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => lazymatch type of FRK with cframe _ _ _ _ _ _ _ ?mpre ?mc =>
      pose proof (ainv_munch LayoutPU A' mc mq md' _ AINV' MU2 WM2 CFP2) as AINV2;
      assert (VEPC2 : rw_cells rsegs mq VEP (vep_cells vx2 tag q))
        by (unfold vep_cells, vx2; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact VEPC');
      clear VEPC';
      (* [comment removed for export] *)
      unhide BSEG0; unhide SEGV;
      apply (bytes_at_transport rsegs [(bv_unsigned sp - 8480, bv_unsigned sp); (VEP, VEP + 312)] mc mq _ seg) in BSEG0; [| exact MU2 | cbn [disjoint_from]; lia ];
      pose proof (as_live_disjoint A' mc md' VEP 312 (v Fvsb) 40 AINV' VLV' (proj1 (proj2 (proj2 SOBJ'))) NES) as DVS';
      pose proof (as_live_disjoint A' mc md' VEP 312 (vb_buf vv') (vb_size vv') AINV' VLV' (proj1 (proj2 (proj2 (proj2 SOBJ')))) NEB2) as DVB';
      assert (SOBJ2 : vsb_obj LayoutPU A' mq (v Fvsb) vv' false)
        by (eapply (vsb_obj_munch LayoutPU); [exact SOBJ' | exact MU2 | exact WM2
            | clear - DVS' Shi CEIL LO ACV; cbn [disjoint_from]; lia | clear - DVB' Bhi' CEIL LO ACV; cbn [disjoint_from]; lia]);
      clear DVS' DVB';
      assert (HENV2 : henv_ok LayoutPU VIU H mq)
        by (eapply henv_ok_munch0'; [| exact MU2 | exact WM2 | lia | assumption];
            eapply (henv_ok_ccall0' A A' mpre md mc); [exact AINV1 | exact FRK | | lia | lia | ];
            [ eapply henv_ok_munch0'; [exact HENV | exact MU | exact WM | lia | assumption]
            | intros a [X|[X|X]]; unfold blk in X; [clear - X Vimg Vhi ACV | clear - X Bimg Bhi ACV | clear - X Simg Shi ACV];
              unfold off_image in *; cbn [al_image_lo al_image_hi LayoutPU] in *; lia ]);
      assert (MP2 : mapped mq (bv_unsigned sp - 8480) 8480)
        by (eapply (window_mapped LayoutPU _ lo); [eassumption | exact FR | cbn; lia | exact CEIL | lia | lia]);
      assert (CF2 : cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) 8480 Vmc (blk (vb_buf vv') (vb_size vv')) m mq)
        by (eapply (cframe_extend LayoutPU _ _ _ _ _ _ _ _ _ _ m mpre mc mq _ _);
            [ exact MU | | exact FRK | lia | lia | intros a X; exact X | intros a X; left; exact X | exact MU2 | | exact MP2 ];
            intros a Ha NO; cbn [outside] in NO; clear - Ha NO Vlo; unfold Vmc, blk; lia);
      eapply (mc_step3' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' mq md' vx2 vv');
      [ exact MDH' | exact MDL' | exact AINV2 | assumption | exact MDF' | eassumption | exact FR | exact VEPC2 | exact VLV'
      | unfold vx2; repeat (apply vkeep_fupd; [| in_tac]); exact VK'
      | unfold vx2, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact EVP'
      | unfold vep_cnt, vx2, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; lia
      | exact SOBJ2
      | unfold vx2, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact RL'
      | exact RS'
      | exact NEB2 | exact REL | exact LIVEq | exact LBp | exact NLp | exact HENV2 | exact BSEG0 | exact SEGV
      | unfold MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK; exact CF2 ]
    end end.
  Qed.

End S.
End U_veshp.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve2lq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve3w7.U_vejdy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve3w7.U_veshp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold CRC_FRAME_U, C64_FRAME in H.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (H : henv) (p mark n : Z) (seg : list byte) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 p.
  Hypothesis A2 : a2 = Z_to_bv 64 mark.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LayoutPU A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutPU VIU H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_okU m.
  Hypothesis HLM : bool01 (v Flast_mark).
  Hypothesis CNT : vep_cnt v n.
  Hypothesis N0 : 0 <= n.
  Hypothesis NMX : n + (p - v Fver_p) < NMAX.
  Hypothesis SOBJ : vsb_obj LayoutPU A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis EM : vb_size vv + 9 <= EXT_MAX.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vsb_extendsize (vb_size vv + 9) <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis BSEG : bytes_at rsegs m (v Fver_p) seg.
  Hypothesis LSEG : Z.of_nat (length seg) = p - v Fver_p.
  Hypothesis VPLO : 4096 <= v Fver_p.
  Hypothesis PHI : p <= alloc_ceiling.
  Hypothesis SEGH : (v Fver_p = vi_empty VIU /\ seg = []) \/
                    (exists d k, a_live A d = Some k /\ 0 < k /\ d <= v Fver_p /\ p <= d + k /\ d <> VEP /\ d <> v Fvsb /\ d <> vb_buf vv).
  Hypothesis TP : tp = al_tp LayoutPU.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + MARK_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          vep_obj LayoutPU A' m' VEP v' tag q -> vkeep v v' MARK_FIELDS ->
          v' Fver_p = p -> v' Flast_mark = mark -> v' Fo_pending = 0 -> vep_cnt v' (n + (p - v Fver_p)) ->
          0 <= v' Fcrc < 2^64 -> 0 <= v' Fcrcp < 2^64 ->
          vsb_obj LayoutPU A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + 3 * (v' Fo_last - v Fo_last) ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> a_live A' r = a_live A r) ->
          a_livebytes A' = a_livebytes A + vb_size vv' - vb_size vv -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
          henv_ok LayoutPU VIU H m' -> bytes_at rsegs m' (v Fver_p) seg ->
          cframe LayoutPU (owned A) (owned A') (bv_unsigned sp) MARK_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  Let Vmc : Z -> Prop := fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40).
  Let l : Z := p - v Fver_p.

  (* [comment removed for export] *)
  Local Definition henv_ok_ccall0' := @henv_ok_ccall0 _ AI v H p seg ra sp HG.
  Local Definition henv_ok_munch0' := @henv_ok_munch0 _ AI VEP v H p seg lo ra sp HG SP16 CEIL LO SPH.
  Local Definition seg_ranges' := @seg_ranges _ AI VEP v tag q vv p seg ra sp m md A AINV VOBJ SOBJ NES NEB LSEG SEGH.
  Local Definition mc_step4' := @mc_step4 _ AI VEP v tag q vv H p mark n seg lo ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T
                     AINV MI A0 A1 A2 HMK VOBJ VBASE HENV HG IMG HLM CNT N0 NMX SOBJ NES NEB EM LBUD NBUD BSEG LSEG VPLO PHI SEGH TP SP16 RA2 ST CEIL LO SPH K.

  Local Definition mc_step3' := @mc_step3 _ AI VEP v tag q vv H p mark n seg lo ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T
                     AINV MI A0 A1 A2 HMK VOBJ VBASE HENV HG IMG HLM CNT N0 NMX SOBJ NES NEB EM LBUD NBUD BSEG LSEG VPLO PHI SEGH TP SP16 RA2 ST CEIL LO SPH K.
  Local Definition mc_step2' := @mc_step2 _ AI VEP v tag q vv H p mark n seg lo ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T
                     AINV MI A0 A1 A2 HMK VOBJ VBASE HENV HG IMG HLM CNT N0 NMX SOBJ NES NEB EM LBUD NBUD BSEG LSEG VPLO PHI SEGH TP SP16 RA2 ST CEIL LO SPH K.
  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutPU)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutPU] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VIU] in ECB, EURL;
    pose proof CNT as (CN1 & CN2 & CN3 & CN4 & CN5 & CN6 & CN7);
    unfold MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK, NMAX in *.

  (* [comment removed for export] *)
  Local Ltac leaf_side :=
    lazymatch goal with
    | |- mem_inv _ _ => assumption
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
    | |- @eq (bv _) _ _ => first [reflexivity | rewrite ?unsigned_lit by lia; reflexivity]
    | |- rw_cells _ _ _ _ => eassumption
    | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
    | |- length _ = _ => assumption
    | |- vep_pads_wf _ => assumption
    | |- _ => rewrite ?unsigned_lit by lia;
            repeat match goal with H : (_ <= _ \/ _ <= _)%Z |- _ => clear H end;
            first [ lia | rewrite Z.mod_small by lia; lia | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; lia ]
    end.

  (* [comment removed for export] *)
  Local Ltac to_step3_entry :=
    lazymatch goal with
    | VEPC : rw_cells _ ?mq VEP _, MU : munch ?W m ?mq, WM : wmono _ m ?mq, CFP : client_fp _ A ?W,
      FR : rw_cells _ ?mq (bv_unsigned sp + -48) [CB 8 ?j8; _; _; _; _; _], STq : stk _ ?mq lo _,
      SEGV : (v Fver_p + _ <= VEP \/ _)%Z, DVS : (VEP + 312 <= v Fvsb \/ _)%Z, DVB : (VEP + 312 <= vb_buf vv \/ _)%Z,
      ACV' : (_ <= alloc_ceiling <= _)%Z, SEGBD' : (0 <= v Fver_p /\ _)%Z, Shi' : (v Fvsb + 40 <= alloc_ceiling)%Z,
      Bhi' : (vb_buf vv + vb_size vv <= alloc_ceiling)%Z, Vlo' : (4096 <= VEP)%Z, Vhi' : (VEP + 312 <= alloc_ceiling)%Z, Blo' : (4096 <= vb_buf vv)%Z
      |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (ainv_munch LayoutPU A m mq md _ AINV MU WM CFP) as AINV3;
      pose proof BSEG as BSEG3; unhide BSEG3;
      apply (bytes_at_transport rsegs W m mq _ seg) in BSEG3; [| exact MU | clear - SEGV LSEG PHI CEIL LO ACV' SEGBD'; cbn [disjoint_from]; lia ];
      assert (SOBJ3 : vsb_obj LayoutPU A mq (v Fvsb) vv false)
        by (eapply (vsb_obj_munch LayoutPU); [exact SOBJ | exact MU | exact WM | clear - DVS Shi' CEIL LO ACV'; cbn [disjoint_from]; lia | clear - DVB Bhi' CEIL LO ACV'; cbn [disjoint_from]; lia]);
      assert (HENV3 : henv_ok LayoutPU VIU H mq) by (eapply henv_ok_munch0'; [exact HENV | exact MU | exact WM | exact Vhi' | assumption]);
      assert (MP : mapped mq (bv_unsigned sp - 8480) 8480)
        by (eapply (window_mapped LayoutPU _ lo); [exact STq | exact FR | cbn; lia | exact CEIL | lia | lia]);
      assert (CF3 : cframe LayoutPU (owned A) (owned A) (bv_unsigned sp) 8480 Vmc (blk (vb_buf vv) (vb_size vv)) m mq)
        by (eapply (cframe_noalloc LayoutPU); [exact MU | | exact MP | intros a X; right; left; exact X];
            intros a Ha NO; cbn [outside] in NO; clear - Ha NO Vlo' Blo'; unfold Vmc, blk; lia);
      eapply (mc_step3' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j8 A mq md v vv);
      [ eassumption | eassumption | exact AINV3 | assumption | eapply md_frame_refl; eassumption | exact STq | exact FR | exact VEPC | eassumption
      | apply vkeep_refl | reflexivity | exact CNT | exact SOBJ3 | lia | lia | exact NEB | left; reflexivity | intros r _ _; reflexivity
      | lia | reflexivity
      | exact HENV3 | exact BSEG3 | exact SEGV
      | unfold MARK_STACK, EMITC_STACK, EMITLEN_STACK, REALLOC_STACK; exact CF3 ]
    end.

  Local Ltac to_step2_entry :=
    lazymatch goal with
    | VEPC : rw_cells _ ?mq VEP _, MU : munch _ m ?mq, WM : wmono _ m ?mq,
      FR : rw_cells _ ?mq (bv_unsigned sp + -48) [CB 8 ?j8; _; _; _; _; _], STq : stk _ ?mq lo _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply (mc_step2' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j8 mq); [assumption | exact STq | exact FR | exact VEPC | exact MU | exact WM]
    end.

  #[using="l Vmc K SPH LO CEIL ST RA2 SP16 TP SEGH PHI VPLO LSEG BSEG EM LBUD NBUD NEB NES SOBJ NMX N0 CNT HLM IMG HG HENV VBASE VOBJ HMK A2 A1 A0 MI AINV A lo seg n mark p H vv q tag v VEP AI Clg"] Lemma mc_main :
    realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 vep_mark_common_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    rewrite A0, A1, A2. unfold vep_mark_common_entry.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    prelims.
    pose proof VOBJ as (VLV & VEPC & TAG & PADS). cbn [al_segs LayoutPU] in VEPC.
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown).
    pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308).
    pose proof (vsb_obj_geom LayoutPU A m md (v Fvsb) vv false AINV SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & _ & Smap & Bmap).
    pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as VLB.
    pose proof (as_live_disjoint A m md VEP 312 (v Fvsb) 40 AINV VLV (proj1 (proj2 (proj2 SOBJ))) NES) as DVS.
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf vv) (vb_size vv) AINV VLV VLB NEB) as DVB.
    pose proof seg_ranges' as (SEGV & SEGS & SEGB).
    pose proof (bytes_at_bound _ _ _ _ BSEG) as SEGBD.
    hide DVS. hide DVB. hide SEGV. clear SEGS SEGB. hide BSEG. hide_slow.
    unfold vep_cells in VEPC.
    pose proof (munch_refl [(bv_unsigned sp - 8480, bv_unsigned sp); (VEP, VEP + 312)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutPU A [(bv_unsigned sp - 8480, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLV|lia]| exact I]. }
    (* [comment removed for export] *)
    pose proof MI as MIw. pose proof ST as STw. hide MI. hide ST.
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 48%nat STw.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KB; zify_cond KB. { exfalso. clear - KB HMK. destruct HMK as [-> | ->]; klia KB. } clear KB.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (land7_of_mod8 VEP) by (first [lia | apply mod8_of_mod16; exact V16]).
    zstep. if_cases KT; zify_cond KT. { exfalso. klia KT. } clear KT.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (sx32_small (v Flast_mark)) by (clear - HLM; destruct HLM; lia).
    hide HMK. hide HLM.
    zstep. if_cases KM; zify_cond KM.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases KW; zify_cond KW.
      + (* [comment removed for export] *)
        unhide DVS. unhide DVB. unhide SEGV. to_step2_entry.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases KS; zify_cond KS.
        * unhide DVS. unhide DVB. unhide SEGV. to_step3_entry.
        * unhide DVS. unhide DVB. unhide SEGV. to_step2_entry.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases KQ; zify_cond KQ.
      + unhide DVS. unhide DVB. unhide SEGV. to_step3_entry.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases KP; zify_cond KP.
        * unhide DVS. unhide DVB. unhide SEGV. to_step3_entry.
        * (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep. zstep. zstep.
          try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
          release_frame FR STw (bv_unsigned sp).
          cps_done.
          unhide DVS. unhide DVB. unhide SEGV.
          lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ => lazymatch type of MU with munch ?W _ _ =>
            pose proof (ainv_munch LayoutPU A m mf md _ AINV MU WM CFP) as AINV9;
            pose proof BSEG as BSEG9; unhide BSEG9;
            apply (bytes_at_transport rsegs W m mf _ seg) in BSEG9; [| exact MU | clear - SEGV LSEG PHI CEIL LO ACV SEGBD; cbn [disjoint_from]; lia ];
            assert (SOBJ9 : vsb_obj LayoutPU A mf (v Fvsb) vv false)
              by (eapply (vsb_obj_munch LayoutPU); [exact SOBJ | exact MU | exact WM | clear - DVS Shi CEIL LO ACV; cbn [disjoint_from]; lia | clear - DVB Bhi CEIL LO ACV; cbn [disjoint_from]; lia]);
            assert (MP : mapped mf (bv_unsigned sp - 8480) 8480) by (eapply (stk_mapped (L:=LayoutPU)); [exact STw | exact CEIL | lia | lia]);
            eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A mf md (fupd (fupd v Fcrc ((v Fcrc) mod 2^64)) Fcrcp ((v Fcrcp) mod 2^64)) vv);
            [ exact AINV9 | assumption | apply md_frame_refl; assumption | exact STw
            | split; [exact VLV|]; split; [unfold vep_cells, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; rewrite !Z_to_bv_mod64; exact VEPC|];
              split; [exact TAG| exact PADS]
            | repeat (apply vkeep_fupd; [| in_tac]); apply vkeep_refl
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; klia KQ
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; unhide HMK; unhide HLM; clear - KM HMK HLM;
              rewrite !Z.mod_small in KM by (destruct HMK; destruct HLM; lia); lia
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; klia KP
            | unfold vep_cnt, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; unfold vep_cnt in CNT; klia KQ
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; apply Z.mod_pos_bound; lia
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; apply Z.mod_pos_bound; lia
            | exact SOBJ9
            | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; lia
            | lia
            | left; reflexivity | intros r _ _; reflexivity
            | lia | reflexivity
            | eapply henv_ok_munch0'; [exact HENV | exact MU | exact WM | exact Vhi | exact Vimg]
            | exact BSEG9
            | eapply (cframe_noalloc LayoutPU); [exact MU | | exact MP | intros a X; right; left; exact X];
              intros a Ha NO; cbn [outside] in NO; clear - Ha NO Vlo; unfold blk; lia ]
          end end.
  Qed.
End S.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vep_mark_common_ok {AI : AllocSpec LayoutPU} : vep_mark_common_stmt.
Proof. unfold vep_mark_common_stmt. intros. eapply mc_main; eassumption. Qed.

End CEIL.

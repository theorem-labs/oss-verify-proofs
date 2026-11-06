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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r R_strcmp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_veobg.

Module V_ve72d.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r R_strcmp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_veobg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (ya : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 0.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HMH : v Fmatch_hit = vi_tbl_attr_include VI0 \/ v Fmatch_hit = vi_tbl_attr_include VI0 + 16.
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis ANZ : v Fattr_vsb <> 0.
  Hypothesis AOBJ : vsb_obj LayoutP0 A m (v Fattr_vsb) ya true.
  Hypothesis AERR : vb_error ya = 0.
  Hypothesis NAS : v Fattr_vsb <> VEP.
  Hypothesis NAB : vb_buf ya <> VEP.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fattr_vsb /\ v Finclude_src <> vb_buf ya /\
                   vb_buf yi <> v Fattr_vsb /\ vb_buf yi <> vb_buf ya
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vi' : option vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q ->
          (  (* [comment removed for export] *) (vi = None /\ v' = fupd (fupd v Finclude_src (v Fattr_vsb)) Fattr_vsb 0 /\ vi' = Some ya /\
                        (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A)
          \/ (* [comment removed for export] *) (vi <> None /\ v' = fupd (fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0) Finclude_src 0 /\ vi' = None /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        (match vi with Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                                                  a_livebytes A' = a_livebytes A - 80 - vb_size ya - vb_size yi /\ a_nlive A' = a_nlive A - 4
                                     | None => False end) /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> r <> v Finclude_src ->
                                   r <> match vi with Some yi => vb_buf yi | None => 0 end -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (vi = None /\ v' = fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0 /\ vi' = None /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (exists ic, bool01 ic /\ v' = fupd (fupd v Finclude_continue ic) Fattr_vsb 0 /\ vi' = vi /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))) ->
          match vi' with
          | None => v' Finclude_src = 0
          | Some yi => v' Finclude_src <> 0 /\ vsb_obj LayoutP0 A' m' (v' Finclude_src) yi true /\ vb_error yi = 0
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ vsb_blocks (v Fattr_vsb) ya a
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  (* [comment removed for export] *)
  Let FRAME (j : list byte) : list cell :=
    [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_1; dand7 dR_1 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fattr_vsb) ya true AINV AOBJ)) as dR_2; dand11 dR_2 as SA16 SAlo SAhi SAimg BA16 BAlo BAhi BAimg DSBA SAmap BAmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fattr_vsb) ya true AINV AOBJ) as (SA16 & SAlo & SAhi & SAimg & BA16 & BAlo & BAhi & BAimg & DSBA & SAmap & BAmap) ]);
    pose proof (proj1 (proj2 (proj2 AOBJ))) as LSA; pose proof (proj1 (proj2 (proj2 (proj2 AOBJ)))) as LBA;
    pose proof (as_live_disjoint A m md VEP 312 (v Fattr_vsb) 40 AINV VLV LSA (not_eq_sym NAS)) as DVSA;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf ya) (vb_size ya) AINV VLV LBA (not_eq_sym NAB)) as DVBA;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HMH (conj HIC
      (conj ANZ (conj AOBJ (conj AERR (conj NAS (conj NAB (conj HVI (conj TP (conj SP16 (conj RA2 (conj ST (conj CEIL (conj LO
      (conj SPH K)))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac env_at mq MU WM :=
    lazymatch goal with GLOB : glob_ok _ _ H m, HOBJ : hobj_ok _ _ H m, IMG : img_ok0 m |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in
      (first [ pose proof (GLOB) as dR_3; dand4 dR_3 as EBSS BSS CP _ | pose proof GLOB as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      eapply (rw_cells_transport rsegs _ m mq) in BSS; [| exact MU | exact WM | cbn; geo_lia];
      eapply (rw_cells_transport rsegs _ m mq) in CP; [| exact MU | exact WM | cbn; unfold h_cp; geo_lia];
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_4; dand3 dR_4 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      eapply (rw_cells_transport rsegs _ m mq) in VC; [| exact MU | exact WM | cbn; revert L1 L2; geo_lia];
      eapply (rw_cells_transport rsegs _ m mq) in WK; [| exact MU | exact WM | cbn; revert L3 L4; geo_lia];
      let GV := fresh "GVSC" in
      pose proof IMG as (_ & _ & GV & _); unfold GOT_vsc in GV;
      eapply (ro_cells_transport rsegs _ m mq) in GV; [| exact MU | cbn; geo_lia]
    end.

  (* [comment removed for export] *)
  Local Ltac henv_at mx MU WM CNT HENV0 :=
    lazymatch goal with GLOB : glob_ok _ _ H m, HOBJ : hobj_ok _ _ H m |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT" in
      (first [ pose proof (GLOB) as dR_7; dand4 dR_7 as EBSS BSS CP _ | pose proof GLOB as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP;
      destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
      assert (HENV0 : henv_ok LayoutP0 VI0 H mx);
      [ split;
        [ eapply (glob_ok_intro LayoutP0); [exact EBSS | | | exact C];
          [ eapply rw_cells_transport; [exact BSS | exact MU | exact WM | rewrite EBSS; cbn; geo_lia]
          | eapply rw_cells_transport; [exact CP | exact MU | exact WM | cbn; unfold h_cp; geo_lia] ]
        | eapply (hobj_ok_munch LayoutP0); [exact HOBJ | exact MU | exact WM |];
          let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; revert Ha; geo_lia ]
      | clear BSS CP C c EBSS ]
    end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  (* [comment removed for export] *)
  Local Ltac err_block STq :=
    do 15 zstep;
    (* [comment removed for export] *)
    zstep; carve_frame 48%nat STq; do 8 zstep;
    lazymatch goal with FR2 : rw_cells _ _ (bv_unsigned sp + -160)%Z _ |- _ =>
      release_frame FR2 STq (bv_unsigned sp + -112)%Z end.

  #[using="SPH LO CEIL NAB NAS AOBJ ANZ HG VBASE VOBJ AINV md m ra lo ya q tag v"] Lemma CFP : client_fp LayoutP0 A W.
  Proof.
    prelims. cbn. split; [left; lia|]. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLV| lia]| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="NAB NAS AOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ vsb_blocks (v Fattr_vsb) ya a \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)
  Local Ltac accept_tail EVI :=
    do 19 zstep;
    try replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp);
    cps_done;
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
    lazymatch goal with FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MU : munch _ m mx, WM : wmono _ m mx,
                        VEPC : rw_cells _ mx VEP _, CNT : rw_cells _ mx (h_vsc H + 1304)%Z _,
                        MDL : m_vm_lazy md = [], MDH : m_halted md = None,
                        VLV : a_live A VEP = Some 312, TAG : length tag = 8%nat, PADS : vep_pads_wf q, EVC : v Fvc = h_vc H |- _ =>
      release_frame FR STq (bv_unsigned sp);
      let AINVf := fresh "AINVf" in let HENVf := fresh "HENVf" in
      pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINVf;
      henv_at mx MU WM CNT HENVf;
      unhide_neqs;
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A mx md (fupd (fupd v Finclude_src (v Fattr_vsb)) Fattr_vsb 0) (Some ya));
      [ exact AINVf | assumption | apply md_frame_refl; [exact MDL| exact MDH] | exact STq | exact HENVf
      | split; [exact VLV|]; split; [| split; [exact TAG| exact PADS]];
        cbn [al_segs LayoutP0]; unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; rewrite EVC; exact VEPC
      | left; split; [exact EVI|]; split; [reflexivity|]; split; [reflexivity|]; split; [intros r; reflexivity| split; reflexivity]
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; split; [exact ANZ|]; split; [| exact AERR];
        eapply (vsb_obj_munch LayoutP0); [exact AOBJ | exact MU | exact WM | | ];
        [ cbn; lazymatch goal with D : kept (VEP + 312 <= v Fattr_vsb \/ _)%Z, B : (v Fattr_vsb + 40 <= alloc_ceiling)%Z |- _ => unhide D; revert D B; geo_lia end
        | cbn; lazymatch goal with D : kept (VEP + 312 <= vb_buf ya \/ _)%Z, B : (vb_buf ya + vb_size ya <= alloc_ceiling)%Z |- _ => unhide D; revert D B; geo_lia end ]
      | rewrite EVI; eapply (cframe_stores LayoutP0 _ _ _ _ m mx); [exact MU | apply W_cover | eapply (stk_mapped (L:=LayoutP0)); [exact STq | exact CEIL | clear -LO; lia | clear; lia]] ]
    end end.

  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH IMG HG HENV VBASE VOBJ A1 A0 MI AINV A a1 a0 ya AI Clg"] Lemma seg_src2 : forall (yi : vsb_rec) (xra xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 : word) (mq : mem) (junk cnt : list byte),
    vi = Some yi ->
    mem_inv rsegs mq -> stk rsegs mq lo (bv_unsigned sp + -112) ->
    rw_cells rsegs mq (bv_unsigned sp + -112) (FRAME junk) ->
    rw_cells rsegs mq VEP (vep_cells v tag q) ->
    rw_cells rsegs mq (h_vsc H + 1304) [CB 16 cnt] ->
    munch W m mq -> wmono rsegs m mq ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b290) (Z_to_bv 32 0) None mq (seg_rom rsegs)) md) T.
  Proof.
    touch_all.
    intros until cnt. intros EVI MIq STq FR VEPC CNT MU WM.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH]. prelims. clear VEPC0. cbv delta [W] in MU. cbv delta [FRAME] in FR.
    unfold vep_cells in VEPC. rewrite EVC in VEPC.
    rewrite EVI in HVI. destruct HVI as (INZ & IOBJ & IERR & NIS & NIB & NISA & NISB & NIBA & NIBB).
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Finclude_src) yi true AINV IOBJ)) as dR_8; dand8 dR_8 as _ SIlo SIhi _ _ BIlo BIhi _ | pose proof (vsb_obj_geom LayoutP0 A m md (v Finclude_src) yi true AINV IOBJ) as (_ & SIlo & SIhi & _ & _ & BIlo & BIhi & _) ]).
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI. pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI.
    pose proof (as_live_disjoint A m md VEP 312 (v Finclude_src) 40 AINV VLV LSI (not_eq_sym NIS)) as DVSI.
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf yi) (vb_size yi) AINV VLV LBI (not_eq_sym NIB)) as DVBI.
    destruct HENV as [GLOB HOBJ]. env_at mq MU WM.
    hide MI. hide ST. clear HMH. hide_disj. hide_slow.
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KT; zify_cond KT. { exfalso. unhide INZ. clear - KT INZ SIlo SIhi ACV. lia. } clear KT.
    (* [comment removed for export] *)
    err_block STq.
    clear GVSC BSS CP VC WK.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m0 end.
    pose proof (ainv_munch LayoutP0 A m m0 md _ AINV MU WM CFP) as AINV0.
    assert (AOBJ0 : vsb_obj LayoutP0 A m0 (v Fattr_vsb) ya true)
      by (eapply (vsb_obj_munch LayoutP0); [exact AOBJ | exact MU | exact WM | cbn; clear - DVSA SAhi CEIL LO ACV G2 SPH Evsc; try unhide DVSA; lia | cbn; clear - DVBA BAhi CEIL LO ACV G2 SPH Evsc; try unhide DVBA; lia]).
    assert (IOBJ0 : vsb_obj LayoutP0 A m0 (v Finclude_src) yi true)
      by (eapply (vsb_obj_munch LayoutP0); [exact IOBJ | exact MU | exact WM | cbn; clear - DVSI SIhi CEIL LO ACV G2 SPH Evsc; try unhide DVSI; lia | cbn; clear - DVBI BIhi CEIL LO ACV G2 SPH Evsc; try unhide DVBI; lia]).
    henv_at m0 MU WM CNT HENV0.
    vep_split3 VEPC 36%nat VEPa VEPp VEPb.
    pose proof (crange_block (L:=LayoutP0) A m0 md VEP 312 VEP 224 AINV0 VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRa.
    pose proof (crange_block (L:=LayoutP0) A m0 md VEP 312 (VEP + 232) 80 AINV0 VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRb.
    unfold VSB_destroy_entry.
    eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 md A (VEP + 224) (v Fattr_vsb) ya true lo);
      [ exact AINV0 | assumption | reflexivity | cbn [w64]; exact VEPp
      | right; exists VEP, 312; split; [exact VLV|]; split; [unhide NAS; unhide NAB; intros [X|[X|[]]]; [exact (NAS X)| exact (NAB X)] | clear; lia]
      | exact AOBJ0 | exact TP
      | rewrite unsigned_lit by lia; unhide SP16; clear - SP16; lia
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact STq | exact CEIL
      | unfold DESTROY_STACK, FREE_STACK; rewrite unsigned_lit by lia; clear - LO; lia
      | rewrite unsigned_lit by lia; clear - SPH G3; lia | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A_1 m1 md1 AINV1 MI1 MDF1 ST1 PSC1 LVS1 LVB1 LIVE1 LB1 NL1 CF1.
    rewrite unsigned_lit in ST1, CF1 by lia. unfold DESTROY_STACK, FREE_STACK in CF1.
    pose proof (as_lazy_nil _ _ _ AINV1) as [MDL1 MDH1].
    assert (HC0 : hcover A [] (fun a => blk (v Fattr_vsb) 40 a \/ blk (vb_buf ya) (vb_size ya) a \/ VEP + 224 <= a < VEP + 224 + 8))
      by (hcover_destroy LSA LBA VLV).
    pose proof (henv_call H A A_1 m0 m1 md (bv_unsigned sp + -112) _ _ _ [] AINV0 CF1 HG ltac:(clear - CEIL LO; lia) ltac:(clear - SPH; lia) HC0 HENV0) as HENV1.
    pose proof (rw_cells_call_stack H A A_1 m0 m1 md _ _ _ _ [] AINV0 CF1 ltac:(clear - CEIL LO; lia) ltac:(clear; lia) _ _ (hcover_vcover H A [] _ HC0) FR
                  ltac:(clear; lia) ltac:(cbn; clear - SPH Evsc; lia)) as FR1.
    assert (LVV1 : a_live A_1 VEP = Some 312) by (unhide NAS; unhide NAB; rewrite (LIVE1 VEP (not_eq_sym NAS) (not_eq_sym NAB)); exact VLV).
    assert (LSI1 : a_live A_1 (v Finclude_src) = Some 40) by (unhide NISA; unhide NISB; rewrite (LIVE1 _ NISA NISB); exact LSI).
    assert (LBI1 : a_live A_1 (vb_buf yi) = Some (vb_size yi)) by (unhide NIBA; unhide NIBB; rewrite (LIVE1 _ NIBA NIBB); exact LBI).
    assert (IOBJ1 : vsb_obj LayoutP0 A_1 m1 (v Finclude_src) yi true).
    { eapply (vsb_obj_call H A A_1 m0 m1 md (bv_unsigned sp + -112) _ _ _ [v Finclude_src; vb_buf yi] AINV0 CF1 HG ltac:(clear - CEIL LO; lia));
        [ | left; reflexivity | right; left; reflexivity | exact LSI1 | exact LBI1 | exact IOBJ0 ].
      intros a Ha. left. revert a Ha. hcover_destroy LSA LBA VLV. }
    xfer_piece CF1 VEPa CRa. xfer_piece CF1 VEPb CRb.
    clear FR STq MIq AOBJ0 IOBJ0 CRa CRb.
    rz_resume MDH1 MDL1.
    (* [comment removed for export] *)
    do 16 zstep.
    try replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    apply rz_stop.
    release_frame FR1 ST1 (bv_unsigned sp).
    vep_split3 VEPb 8%nat VEPb1 VEPq VEPb2.
    pose proof (crange_block (L:=LayoutP0) A_1 m1 md1 VEP 312 VEP 224 AINV1 LVV1 ltac:(lia) ltac:(lia) ltac:(lia)) as CR1a.
    pose proof (crange_block (L:=LayoutP0) A_1 m1 md1 VEP 312 (VEP + 224) 8 AINV1 LVV1 ltac:(lia) ltac:(lia) ltac:(lia)) as CR1p.
    pose proof (crange_block (L:=LayoutP0) A_1 m1 md1 VEP 312 (VEP + 232) 48 AINV1 LVV1 ltac:(lia) ltac:(lia) ltac:(lia)) as CR1b1.
    pose proof (crange_block (L:=LayoutP0) A_1 m1 md1 VEP 312 (VEP + 288) 24 AINV1 LVV1 ltac:(lia) ltac:(lia) ltac:(lia)) as CR1b2.
    eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md1 A_1 (VEP + 280) (v Finclude_src) yi true lo);
      [ exact AINV1 | exact MI1 | reflexivity | cbn [w64]; exact VEPq
      | right; exists VEP, 312; split; [exact LVV1|]; split; [unhide NIS; unhide NIB; intros [X|[X|[]]]; [exact (NIS X)| exact (NIB X)] | clear; lia]
      | exact IOBJ1 | exact TP | unhide SP16; exact SP16 | unhide RA2; exact RA2 | exact ST1 | exact CEIL
      | unfold DESTROY_STACK, FREE_STACK; clear - LO; lia | clear - SPH G3; lia | ].
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A_2 m2 md2 AINV2 MI2 MDF2 ST2 PSC2 LVS2 LVB2 LIVE2 LB2 NL2 CF2.
    unfold DESTROY_STACK, FREE_STACK in CF2.
    assert (HC1 : hcover A_1 [] (fun a => blk (v Finclude_src) 40 a \/ blk (vb_buf yi) (vb_size yi) a \/ VEP + 280 <= a < VEP + 280 + 8))
      by (hcover_destroy LSI1 LBI1 LVV1).
    pose proof (henv_call H A_1 A_2 m1 m2 md1 (bv_unsigned sp) _ _ _ [] AINV1 CF2 HG ltac:(clear - CEIL LO; lia) SPH HC1 HENV1) as HENV2.
    xfer_piece CF2 VEPa CR1a. xfer_piece CF2 PSC1 CR1p. xfer_piece CF2 VEPb1 CR1b1. xfer_piece CF2 VEPb2 CR1b2.
    cbn [w64] in PSC1, PSC2.
    vep_join3 VEPb1 PSC2 VEPb2 VEPb'. vep_join3 VEPa PSC1 VEPb' VEPC2.
    unhide_neqs.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A_2 m2 md2 (fupd (fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0) Finclude_src 0) None);
      [ exact AINV2 | exact MI2 | exact (md_frame_trans _ _ _ MDF1 MDF2) | exact ST2 | exact HENV2 | | | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; reflexivity | ].
    - (* [comment removed for export] *)
      split; [rewrite (LIVE2 VEP (not_eq_sym NIS) (not_eq_sym NIB)); exact LVV1|].
      split; [| split; [exact TAG| exact PADS]].
      cbn [al_segs LayoutP0]. unfold vep_cells. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VI0 st0]. rewrite EVC. exact VEPC2.
    - (* [comment removed for export] *)
      right; left. rewrite EVI. split; [discriminate|]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite (LIVE2 _ (not_eq_sym NISA) (not_eq_sym NIBA)); exact LVS1|].
      split; [rewrite (LIVE2 _ (not_eq_sym NISB) (not_eq_sym NIBB)); exact LVB1|].
      split; [split; [exact LVS2| split; [exact LVB2| split; [rewrite LB2, LB1; lia| rewrite NL2, NL1; lia]]]|].
      intros r R1 R2 R3 R4. rewrite (LIVE2 r R3 R4). exact (LIVE1 r R1 R2).
    - (* [comment removed for export] *)
      rewrite EVI.
      lazymatch type of CF1 with cframe _ _ _ _ _ ?V1 _ _ _ =>
      lazymatch goal with |- cframe _ _ _ _ _ ?VF _ _ _ =>
        assert (CFA : cframe LayoutP0 (owned A) (owned A_1) (bv_unsigned sp) 8544 VF nowhere m m1)
      end end.
      { eapply (cframe_extend LayoutP0 _ _ (bv_unsigned sp + -112) _ (bv_unsigned sp) _ _ _ _ _ m m0 m1 m1 _ []);
          [ exact MU | | exact CF1 | clear; lia | clear; lia | | intros a X; left; exact X | apply munch_refl
          | intros a _ X; exfalso; apply X; exact I
          | eapply (stk_mapped (L:=LayoutP0)); [exact ST1 | exact CEIL | clear -LO; lia | clear; lia] ].
        + apply W_cover.
        + intros a [X|[X|X]]; [right; left; left; exact X | right; left; right; exact X | left; split; [clear -Vlo; lia| clear -X; lia]]. }
      eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8208 8544 _ _ _ _ _ _ m m1 m2);
        [ exact CFA | exact CF2 | clear; lia | clear; lia
        | eapply (stk_mapped (L:=LayoutP0)); [exact ST2 | exact CEIL | clear -LO; lia | clear; lia]
        | intros a X; exact X
        | intros a [X|[X|X]]; right; [right; right; left; left; exact X | right; right; left; right; exact X | left; split; [clear -Vlo; lia| clear -X; lia]]
        | intros a X; destruct X ].
  Qed.

End S.
End V_ve72d.


Module V_vev75.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r R_strcmp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_veobg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (ya : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 0.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HMH : v Fmatch_hit = vi_tbl_attr_include VI0 \/ v Fmatch_hit = vi_tbl_attr_include VI0 + 16.
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis ANZ : v Fattr_vsb <> 0.
  Hypothesis AOBJ : vsb_obj LayoutP0 A m (v Fattr_vsb) ya true.
  Hypothesis AERR : vb_error ya = 0.
  Hypothesis NAS : v Fattr_vsb <> VEP.
  Hypothesis NAB : vb_buf ya <> VEP.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fattr_vsb /\ v Finclude_src <> vb_buf ya /\
                   vb_buf yi <> v Fattr_vsb /\ vb_buf yi <> vb_buf ya
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vi' : option vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q ->
          (  (* [comment removed for export] *) (vi = None /\ v' = fupd (fupd v Finclude_src (v Fattr_vsb)) Fattr_vsb 0 /\ vi' = Some ya /\
                        (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A)
          \/ (* [comment removed for export] *) (vi <> None /\ v' = fupd (fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0) Finclude_src 0 /\ vi' = None /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        (match vi with Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                                                  a_livebytes A' = a_livebytes A - 80 - vb_size ya - vb_size yi /\ a_nlive A' = a_nlive A - 4
                                     | None => False end) /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> r <> v Finclude_src ->
                                   r <> match vi with Some yi => vb_buf yi | None => 0 end -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (vi = None /\ v' = fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0 /\ vi' = None /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (exists ic, bool01 ic /\ v' = fupd (fupd v Finclude_continue ic) Fattr_vsb 0 /\ vi' = vi /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))) ->
          match vi' with
          | None => v' Finclude_src = 0
          | Some yi => v' Finclude_src <> 0 /\ vsb_obj LayoutP0 A' m' (v' Finclude_src) yi true /\ vb_error yi = 0
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ vsb_blocks (v Fattr_vsb) ya a
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  (* [comment removed for export] *)
  Let FRAME (j : list byte) : list cell :=
    [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_1; dand7 dR_1 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fattr_vsb) ya true AINV AOBJ)) as dR_2; dand11 dR_2 as SA16 SAlo SAhi SAimg BA16 BAlo BAhi BAimg DSBA SAmap BAmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fattr_vsb) ya true AINV AOBJ) as (SA16 & SAlo & SAhi & SAimg & BA16 & BAlo & BAhi & BAimg & DSBA & SAmap & BAmap) ]);
    pose proof (proj1 (proj2 (proj2 AOBJ))) as LSA; pose proof (proj1 (proj2 (proj2 (proj2 AOBJ)))) as LBA;
    pose proof (as_live_disjoint A m md VEP 312 (v Fattr_vsb) 40 AINV VLV LSA (not_eq_sym NAS)) as DVSA;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf ya) (vb_size ya) AINV VLV LBA (not_eq_sym NAB)) as DVBA;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HMH (conj HIC
      (conj ANZ (conj AOBJ (conj AERR (conj NAS (conj NAB (conj HVI (conj TP (conj SP16 (conj RA2 (conj ST (conj CEIL (conj LO
      (conj SPH K)))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac env_at mq MU WM :=
    lazymatch goal with GLOB : glob_ok _ _ H m, HOBJ : hobj_ok _ _ H m, IMG : img_ok0 m |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in
      (first [ pose proof (GLOB) as dR_3; dand4 dR_3 as EBSS BSS CP _ | pose proof GLOB as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      eapply (rw_cells_transport rsegs _ m mq) in BSS; [| exact MU | exact WM | cbn; geo_lia];
      eapply (rw_cells_transport rsegs _ m mq) in CP; [| exact MU | exact WM | cbn; unfold h_cp; geo_lia];
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_4; dand3 dR_4 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      eapply (rw_cells_transport rsegs _ m mq) in VC; [| exact MU | exact WM | cbn; revert L1 L2; geo_lia];
      eapply (rw_cells_transport rsegs _ m mq) in WK; [| exact MU | exact WM | cbn; revert L3 L4; geo_lia];
      let GV := fresh "GVSC" in
      pose proof IMG as (_ & _ & GV & _); unfold GOT_vsc in GV;
      eapply (ro_cells_transport rsegs _ m mq) in GV; [| exact MU | cbn; geo_lia]
    end.

  (* [comment removed for export] *)
  Local Ltac henv_at mx MU WM CNT HENV0 :=
    lazymatch goal with GLOB : glob_ok _ _ H m, HOBJ : hobj_ok _ _ H m |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT" in
      (first [ pose proof (GLOB) as dR_7; dand4 dR_7 as EBSS BSS CP _ | pose proof GLOB as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP;
      destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
      assert (HENV0 : henv_ok LayoutP0 VI0 H mx);
      [ split;
        [ eapply (glob_ok_intro LayoutP0); [exact EBSS | | | exact C];
          [ eapply rw_cells_transport; [exact BSS | exact MU | exact WM | rewrite EBSS; cbn; geo_lia]
          | eapply rw_cells_transport; [exact CP | exact MU | exact WM | cbn; unfold h_cp; geo_lia] ]
        | eapply (hobj_ok_munch LayoutP0); [exact HOBJ | exact MU | exact WM |];
          let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; revert Ha; geo_lia ]
      | clear BSS CP C c EBSS ]
    end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  (* [comment removed for export] *)
  Local Ltac err_block STq :=
    do 15 zstep;
    (* [comment removed for export] *)
    zstep; carve_frame 48%nat STq; do 8 zstep;
    lazymatch goal with FR2 : rw_cells _ _ (bv_unsigned sp + -160)%Z _ |- _ =>
      release_frame FR2 STq (bv_unsigned sp + -112)%Z end.

  #[using="SPH LO CEIL NAB NAS AOBJ ANZ HG VBASE VOBJ AINV md m ra lo ya q tag v"] Lemma CFP : client_fp LayoutP0 A W.
  Proof.
    prelims. cbn. split; [left; lia|]. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLV| lia]| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="NAB NAS AOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ vsb_blocks (v Fattr_vsb) ya a \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)
  Local Ltac accept_tail EVI :=
    do 19 zstep;
    try replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp);
    cps_done;
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
    lazymatch goal with FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MU : munch _ m mx, WM : wmono _ m mx,
                        VEPC : rw_cells _ mx VEP _, CNT : rw_cells _ mx (h_vsc H + 1304)%Z _,
                        MDL : m_vm_lazy md = [], MDH : m_halted md = None,
                        VLV : a_live A VEP = Some 312, TAG : length tag = 8%nat, PADS : vep_pads_wf q, EVC : v Fvc = h_vc H |- _ =>
      release_frame FR STq (bv_unsigned sp);
      let AINVf := fresh "AINVf" in let HENVf := fresh "HENVf" in
      pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINVf;
      henv_at mx MU WM CNT HENVf;
      unhide_neqs;
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A mx md (fupd (fupd v Finclude_src (v Fattr_vsb)) Fattr_vsb 0) (Some ya));
      [ exact AINVf | assumption | apply md_frame_refl; [exact MDL| exact MDH] | exact STq | exact HENVf
      | split; [exact VLV|]; split; [| split; [exact TAG| exact PADS]];
        cbn [al_segs LayoutP0]; unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; rewrite EVC; exact VEPC
      | left; split; [exact EVI|]; split; [reflexivity|]; split; [reflexivity|]; split; [intros r; reflexivity| split; reflexivity]
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; split; [exact ANZ|]; split; [| exact AERR];
        eapply (vsb_obj_munch LayoutP0); [exact AOBJ | exact MU | exact WM | | ];
        [ cbn; lazymatch goal with D : kept (VEP + 312 <= v Fattr_vsb \/ _)%Z, B : (v Fattr_vsb + 40 <= alloc_ceiling)%Z |- _ => unhide D; revert D B; geo_lia end
        | cbn; lazymatch goal with D : kept (VEP + 312 <= vb_buf ya \/ _)%Z, B : (vb_buf ya + vb_size ya <= alloc_ceiling)%Z |- _ => unhide D; revert D B; geo_lia end ]
      | rewrite EVI; eapply (cframe_stores LayoutP0 _ _ _ _ m mx); [exact MU | apply W_cover | eapply (stk_mapped (L:=LayoutP0)); [exact STq | exact CEIL | clear -LO; lia | clear; lia]] ]
    end end.

  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH IMG HG HENV VBASE VOBJ A1 A0 MI AINV A a1 a0 ya AI Clg"] Lemma seg_src0 : forall (xra xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 : word) (mq : mem) (junk cnt : list byte),
    vi = None ->
    mem_inv rsegs mq -> stk rsegs mq lo (bv_unsigned sp + -112) ->
    rw_cells rsegs mq (bv_unsigned sp + -112) (FRAME junk) ->
    rw_cells rsegs mq VEP (vep_cells v tag q) ->
    rw_cells rsegs mq (h_vsc H + 1304) [CB 16 cnt] ->
    munch W m mq -> wmono rsegs m mq ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b290) (Z_to_bv 32 0) None mq (seg_rom rsegs)) md) T.
  Proof.
    touch_all.
    intros until cnt. intros EVI MIq STq FR VEPC CNT MU WM.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH]. prelims. clear VEPC0. cbv delta [W] in MU. cbv delta [FRAME] in FR.
    unfold vep_cells in VEPC. rewrite EVC in VEPC.
    rewrite EVI in HVI. rewrite HVI in VEPC.
    (* [comment removed for export] *)
    assert (AOBJq : vsb_obj LayoutP0 A mq (v Fattr_vsb) ya true)
      by (eapply (vsb_obj_munch LayoutP0); [exact AOBJ | exact MU | exact WM | cbn; clear - DVSA SAhi CEIL LO ACV G2 SPH Evsc; lia | cbn; clear - DVBA BAhi CEIL LO ACV G2 SPH Evsc; lia]).
    pose proof AOBJq as AO. vsb_open AO. (first [ dex1 VBUF as bs; dand3 VBUF as U8 LBS NUL | dand4 VBUF as bs U8 LBS NUL | destruct VBUF as (bs & U8 & LBS & NUL) ]). cbn [al_segs LayoutP0] in U8. specialize (NUL eq_refl).
    (first [ pose proof (VINV) as dR_9; dand8 dR_9 as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | pose proof VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    (* [comment removed for export] *)
    pose proof IMG as (GVCT & _). unfold GOT_vct, VCT_TYPTAB in GVCT.
    eapply (ro_cells_transport rsegs _ m mq) in GVCT; [| exact MU | cbn; geo_lia].
    destruct HENV as [GLOB HOBJ].
    hide MI. hide ST. clear HMH Verr. hide_disj. hide_slow.
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KT; zify_cond KT. 2:{ exfalso. apply KT. reflexivity. } clear KT.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    call_fr (VSB_data_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq (v Fattr_vsb) ya lo) by
      (idtac; [> reflexivity | exact VSBC | exact VINV | exact SAlo | exact SAhi
              | rewrite unsigned_lit by lia; exact STq | rewrite unsigned_lit by lia; lia | exact CEIL
              | rewrite unsigned_lit by lia; lia | exact MIq ]).
    lazymatch goal with S : stk _ ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename S into STq; rename mx into m0 end.
    clear VSBC VLS VLB VNE.
    (* [comment removed for export] *)
    destruct (nth_error bs 0) as [b0|] eqn:Hn0; [| apply nth_error_None in Hn0; exfalso; clear - Hn0 LBS Vsz; lia].
    pose proof (byte_range b0) as RB0.
    pose proof (u8arr_read rsegs m0 (vb_buf ya) bs 0 b0 (Z_to_bv 64 (vb_buf ya)) U8 Hn0 ltac:(clear; lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      clear U8 GVCT. accept_tail EVI.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. clear GVCT.
      assert (LNZ : vb_len ya <> 0).
      { intros E. rewrite E in NUL. change (Z.to_nat 0) with 0%nat in NUL. rewrite Hn0 in NUL. injection NUL as E0. rewrite E0 in KZ. apply KZ. reflexivity. }
      replace (vb_buf ya + 1) with (vb_buf ya + 0 + 1) by lia.
      eapply evt_cut; [eapply (lws_loop (Z.to_nat (vb_len ya))) with (i := 0) (z := vb_len ya);
        [ exact U8 | assumption | exact Hn0 | clear; lia | exact KZ | exact NUL | clear - LNZ Vlen; lia | clear - Vlen; lia ] |].
      cbv beta. (intros ms'; (first [ intro dR_10; dex3 dR_10 as xa0' xa2' pc'; destruct dR_10 as [-> [-> | ->]] | intro dR_10; dand5 dR_10 as xa0' xa2' pc' -> [-> | ->] | intros (xa0' & xa2' & pc' & -> & [-> | ->]) ])).
      + (* [comment removed for export] *)
        clear U8.
        env_at m0 MU WM.
        err_block STq.
        clear GVSC BSS CP VC WK.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        apply rz_stop.
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m9 end.
        pose proof (ainv_munch LayoutP0 A m m9 md _ AINV MU WM CFP) as AINV0.
        assert (AOBJ0 : vsb_obj LayoutP0 A m9 (v Fattr_vsb) ya true)
          by (eapply (vsb_obj_munch LayoutP0); [exact AOBJ | exact MU | exact WM | cbn; clear - DVSA SAhi CEIL LO ACV G2 SPH Evsc; try unhide DVSA; lia | cbn; clear - DVBA BAhi CEIL LO ACV G2 SPH Evsc; try unhide DVBA; lia]).
        henv_at m9 MU WM CNT HENV0.
        vep_split3 VEPC 36%nat VEPa VEPp VEPb.
        pose proof (crange_block (L:=LayoutP0) A m9 md VEP 312 VEP 224 AINV0 VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRa.
        pose proof (crange_block (L:=LayoutP0) A m9 md VEP 312 (VEP + 232) 80 AINV0 VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRb.
        unfold VSB_destroy_entry.
        eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 md A (VEP + 224) (v Fattr_vsb) ya true lo);
          [ exact AINV0 | assumption | reflexivity | cbn [w64]; exact VEPp
          | right; exists VEP, 312; split; [exact VLV|]; split; [unhide NAS; unhide NAB; intros [X|[X|[]]]; [exact (NAS X)| exact (NAB X)] | clear; lia]
          | exact AOBJ0 | exact TP
          | rewrite unsigned_lit by lia; unhide SP16; clear - SP16; lia
          | rewrite unsigned_lit by lia; reflexivity
          | rewrite unsigned_lit by lia; exact STq | exact CEIL
          | unfold DESTROY_STACK, FREE_STACK; rewrite unsigned_lit by lia; clear - LO; lia
          | rewrite unsigned_lit by lia; clear - SPH G3; lia | ].
        intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A_1 m1 md1 AINV1 MI1 MDF1 ST1 PSC1 LVS1 LVB1 LIVE1 LB1 NL1 CF1.
        rewrite unsigned_lit in ST1, CF1 by lia. unfold DESTROY_STACK, FREE_STACK in CF1.
        pose proof (as_lazy_nil _ _ _ AINV1) as [MDL1 MDH1].
        assert (HC0 : hcover A [] (fun a => blk (v Fattr_vsb) 40 a \/ blk (vb_buf ya) (vb_size ya) a \/ VEP + 224 <= a < VEP + 224 + 8))
          by (hcover_destroy LSA LBA VLV).
        pose proof (henv_call H A A_1 m9 m1 md (bv_unsigned sp + -112) _ _ _ [] AINV0 CF1 HG ltac:(clear - CEIL LO; lia) ltac:(clear - SPH; lia) HC0 HENV0) as HENV1.
        pose proof (rw_cells_call_stack H A A_1 m9 m1 md _ _ _ _ [] AINV0 CF1 ltac:(clear - CEIL LO; lia) ltac:(clear; lia) _ _ (hcover_vcover H A [] _ HC0) FR
                      ltac:(clear; lia) ltac:(cbn; clear - SPH Evsc; lia)) as FR1.
        assert (LVV1 : a_live A_1 VEP = Some 312) by (unhide NAS; unhide NAB; rewrite (LIVE1 VEP (not_eq_sym NAS) (not_eq_sym NAB)); exact VLV).
        xfer_piece CF1 VEPa CRa. xfer_piece CF1 VEPb CRb.
        clear FR STq AOBJ0 CRa CRb.
        rz_resume MDH1 MDL1.
        (* [comment removed for export] *)
        zstep. zstep. if_cases KT; zify_cond KT. { exfalso. apply KT. reflexivity. } clear KT.
        do 16 zstep.
        try replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        cps_done.
        release_frame FR1 ST1 (bv_unsigned sp).
        cbn [w64] in PSC1. vep_join3 VEPa PSC1 VEPb VEPC1.
        unhide_neqs.
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A_1 m1 md1 (fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0) None);
          [ exact AINV1 | assumption | exact MDF1 | exact ST1 | exact HENV1 | | | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact HVI | ].
        * split; [exact LVV1|]. split; [| split; [exact TAG| exact PADS]].
          cbn [al_segs LayoutP0]. unfold vep_cells. cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VI0 st0]. rewrite EVC, HVI. exact VEPC1.
        * right; right; left. split; [exact EVI|]. split; [reflexivity|]. split; [reflexivity|].
          split; [exact LVS1|]. split; [exact LVB1|]. split; [exact LB1|]. split; [exact NL1|]. exact LIVE1.
        * rewrite EVI.
          eapply (cframe_extend LayoutP0 _ _ (bv_unsigned sp + -112) _ (bv_unsigned sp) _ _ _ _ _ m m9 m1 m1 _ []);
            [ exact MU | | exact CF1 | clear; lia | clear; lia | | intros a X; left; exact X | apply munch_refl
            | intros a _ X; exfalso; apply X; exact I
            | eapply (stk_mapped (L:=LayoutP0)); [exact ST1 | exact CEIL | clear -LO; lia | clear; lia] ].
          -- apply W_cover.
          -- intros a [X|[X|X]]; [right; left; left; exact X | right; left; right; exact X | left; split; [clear -Vlo; lia| clear -X; lia]].
      + (* [comment removed for export] *)
        clear U8. accept_tail EVI.
  Qed.

End S.
End V_vev75.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veobg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vezwa.V_ve72d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vezwa.V_vev75.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (ya : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 0.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HMH : v Fmatch_hit = vi_tbl_attr_include VI0 \/ v Fmatch_hit = vi_tbl_attr_include VI0 + 16.
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis ANZ : v Fattr_vsb <> 0.
  Hypothesis AOBJ : vsb_obj LayoutP0 A m (v Fattr_vsb) ya true.
  Hypothesis AERR : vb_error ya = 0.
  Hypothesis NAS : v Fattr_vsb <> VEP.
  Hypothesis NAB : vb_buf ya <> VEP.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fattr_vsb /\ v Finclude_src <> vb_buf ya /\
                   vb_buf yi <> v Fattr_vsb /\ vb_buf yi <> vb_buf ya
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vi' : option vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q ->
          (  (* [comment removed for export] *) (vi = None /\ v' = fupd (fupd v Finclude_src (v Fattr_vsb)) Fattr_vsb 0 /\ vi' = Some ya /\
                        (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A)
          \/ (* [comment removed for export] *) (vi <> None /\ v' = fupd (fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0) Finclude_src 0 /\ vi' = None /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        (match vi with Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                                                  a_livebytes A' = a_livebytes A - 80 - vb_size ya - vb_size yi /\ a_nlive A' = a_nlive A - 4
                                     | None => False end) /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> r <> v Finclude_src ->
                                   r <> match vi with Some yi => vb_buf yi | None => 0 end -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (vi = None /\ v' = fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0 /\ vi' = None /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (exists ic, bool01 ic /\ v' = fupd (fupd v Finclude_continue ic) Fattr_vsb 0 /\ vi' = vi /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))) ->
          match vi' with
          | None => v' Finclude_src = 0
          | Some yi => v' Finclude_src <> 0 /\ vsb_obj LayoutP0 A' m' (v' Finclude_src) yi true /\ vb_error yi = 0
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ vsb_blocks (v Fattr_vsb) ya a
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  (* [comment removed for export] *)
  Let FRAME (j : list byte) : list cell :=
    [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_1; dand7 dR_1 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fattr_vsb) ya true AINV AOBJ)) as dR_2; dand11 dR_2 as SA16 SAlo SAhi SAimg BA16 BAlo BAhi BAimg DSBA SAmap BAmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fattr_vsb) ya true AINV AOBJ) as (SA16 & SAlo & SAhi & SAimg & BA16 & BAlo & BAhi & BAimg & DSBA & SAmap & BAmap) ]);
    pose proof (proj1 (proj2 (proj2 AOBJ))) as LSA; pose proof (proj1 (proj2 (proj2 (proj2 AOBJ)))) as LBA;
    pose proof (as_live_disjoint A m md VEP 312 (v Fattr_vsb) 40 AINV VLV LSA (not_eq_sym NAS)) as DVSA;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf ya) (vb_size ya) AINV VLV LBA (not_eq_sym NAB)) as DVBA;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HMH (conj HIC
      (conj ANZ (conj AOBJ (conj AERR (conj NAS (conj NAB (conj HVI (conj TP (conj SP16 (conj RA2 (conj ST (conj CEIL (conj LO
      (conj SPH K)))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac env_at mq MU WM :=
    lazymatch goal with GLOB : glob_ok _ _ H m, HOBJ : hobj_ok _ _ H m, IMG : img_ok0 m |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in
      (first [ pose proof (GLOB) as dR_3; dand4 dR_3 as EBSS BSS CP _ | pose proof GLOB as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      eapply (rw_cells_transport rsegs _ m mq) in BSS; [| exact MU | exact WM | cbn; geo_lia];
      eapply (rw_cells_transport rsegs _ m mq) in CP; [| exact MU | exact WM | cbn; unfold h_cp; geo_lia];
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_4; dand3 dR_4 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      eapply (rw_cells_transport rsegs _ m mq) in VC; [| exact MU | exact WM | cbn; revert L1 L2; geo_lia];
      eapply (rw_cells_transport rsegs _ m mq) in WK; [| exact MU | exact WM | cbn; revert L3 L4; geo_lia];
      let GV := fresh "GVSC" in
      pose proof IMG as (_ & _ & GV & _); unfold GOT_vsc in GV;
      eapply (ro_cells_transport rsegs _ m mq) in GV; [| exact MU | cbn; geo_lia]
    end.

  (* [comment removed for export] *)
  Local Ltac henv_at mx MU WM CNT HENV0 :=
    lazymatch goal with GLOB : glob_ok _ _ H m, HOBJ : hobj_ok _ _ H m |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT" in
      (first [ pose proof (GLOB) as dR_7; dand4 dR_7 as EBSS BSS CP _ | pose proof GLOB as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP;
      destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
      assert (HENV0 : henv_ok LayoutP0 VI0 H mx);
      [ split;
        [ eapply (glob_ok_intro LayoutP0); [exact EBSS | | | exact C];
          [ eapply rw_cells_transport; [exact BSS | exact MU | exact WM | rewrite EBSS; cbn; geo_lia]
          | eapply rw_cells_transport; [exact CP | exact MU | exact WM | cbn; unfold h_cp; geo_lia] ]
        | eapply (hobj_ok_munch LayoutP0); [exact HOBJ | exact MU | exact WM |];
          let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; revert Ha; geo_lia ]
      | clear BSS CP C c EBSS ]
    end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  (* [comment removed for export] *)
  Local Ltac err_block STq :=
    do 15 zstep;
    (* [comment removed for export] *)
    zstep; carve_frame 48%nat STq; do 8 zstep;
    lazymatch goal with FR2 : rw_cells _ _ (bv_unsigned sp + -160)%Z _ |- _ =>
      release_frame FR2 STq (bv_unsigned sp + -112)%Z end.

  #[using="SPH LO CEIL NAB NAS AOBJ ANZ HG VBASE VOBJ AINV md m ra lo ya q tag v"] Lemma CFP : client_fp LayoutP0 A W.
  Proof.
    prelims. cbn. split; [left; lia|]. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLV| lia]| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="NAB NAS AOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ vsb_blocks (v Fattr_vsb) ya a \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)
  Local Ltac accept_tail EVI :=
    do 19 zstep;
    try replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp);
    cps_done;
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
    lazymatch goal with FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MU : munch _ m mx, WM : wmono _ m mx,
                        VEPC : rw_cells _ mx VEP _, CNT : rw_cells _ mx (h_vsc H + 1304)%Z _,
                        MDL : m_vm_lazy md = [], MDH : m_halted md = None,
                        VLV : a_live A VEP = Some 312, TAG : length tag = 8%nat, PADS : vep_pads_wf q, EVC : v Fvc = h_vc H |- _ =>
      release_frame FR STq (bv_unsigned sp);
      let AINVf := fresh "AINVf" in let HENVf := fresh "HENVf" in
      pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINVf;
      henv_at mx MU WM CNT HENVf;
      unhide_neqs;
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A mx md (fupd (fupd v Finclude_src (v Fattr_vsb)) Fattr_vsb 0) (Some ya));
      [ exact AINVf | assumption | apply md_frame_refl; [exact MDL| exact MDH] | exact STq | exact HENVf
      | split; [exact VLV|]; split; [| split; [exact TAG| exact PADS]];
        cbn [al_segs LayoutP0]; unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; rewrite EVC; exact VEPC
      | left; split; [exact EVI|]; split; [reflexivity|]; split; [reflexivity|]; split; [intros r; reflexivity| split; reflexivity]
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; split; [exact ANZ|]; split; [| exact AERR];
        eapply (vsb_obj_munch LayoutP0); [exact AOBJ | exact MU | exact WM | | ];
        [ cbn; lazymatch goal with D : kept (VEP + 312 <= v Fattr_vsb \/ _)%Z, B : (v Fattr_vsb + 40 <= alloc_ceiling)%Z |- _ => unhide D; revert D B; geo_lia end
        | cbn; lazymatch goal with D : kept (VEP + 312 <= vb_buf ya \/ _)%Z, B : (vb_buf ya + vb_size ya <= alloc_ceiling)%Z |- _ => unhide D; revert D B; geo_lia end ]
      | rewrite EVI; eapply (cframe_stores LayoutP0 _ _ _ _ m mx); [exact MU | apply W_cover | eapply (stk_mapped (L:=LayoutP0)); [exact STq | exact CEIL | clear -LO; lia | clear; lia]] ]
    end end.

  (* [comment removed for export] *)
  #[using="W K SPH LO CEIL ST RA2 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH IMG HG HENV VBASE VOBJ A1 A0 MI AINV A lo H vi ya q tag v VEP AI Clg"] Lemma main :
    realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 vep_do_include_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    rewrite A0, A1. unfold vep_do_include_entry.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    prelims.
    pose proof VEPC0 as VEPC. clear VEPC0. unfold vep_cells in VEPC.
    (* [comment removed for export] *)
    destruct HENV as [GLOB HOBJ]. (first [ pose proof (GLOB) as dR_8; dand4 dR_8 as EBSS _ _ [cnt CNT] | pose proof GLOB as (EBSS & _ & _ & [cnt CNT]) ]). cbn [al_segs LayoutP0] in CNT.
    pose proof IMG as (_ & _ & _ & _ & _ & _ & _ & TBL & _). cbn [mtab_cells tbl_attr_include me_ptr me_svar] in TBL. unfold TBL_attr_include in TBL.
    cbn [vi_tbl_attr_include VI0] in HMH. unfold TBL_attr_include in HMH.
    pose proof (munch_refl W m) as MU. cbv delta [W] in MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof MI as MIw. pose proof ST as STw. hide MI. hide ST.
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 112%nat STw.
    (* [comment removed for export] *)
    do 14 zstep.
    zstep. zstep. zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT. lia. } clear KT.
    zstep. if_cases KT; zify_cond KT. { exfalso. apply KT. reflexivity. } clear KT.
    (* [comment removed for export] *)
    zstep. destruct HMH as [EMH|EMH]; rewrite EMH.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        eapply evt_cut; [eapply strcmp_spec with (ls := STR_src) (rs := STR_src) (v := 0);
          [ rewrite unsigned_lit by lia; apply str_src_at; assumption
          | rewrite unsigned_lit by lia; apply str_src_at; assumption
          | reflexivity | assumption ]
        | post_call_fr rsegs mq ] end.
      repeat match goal with Hb : bytes_at _ _ _ STR_src |- _ => clear Hb end.
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT. 2:{ exfalso. apply KT. reflexivity. } clear KT.
      apply rz_stop.
      lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -112) _ |- _ =>
        let EV := fresh "EV" in
        assert (EV : (exists yi, vi = Some yi) \/ vi = None) by (clear; destruct vi; [left; eexists; reflexivity | right; reflexivity]);
        destruct EV as [[yi EVI]|EVI];
        [ eapply (@seg_src2 _ AI VEP v tag q ya vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HMH HIC ANZ AOBJ AERR NAS NAB HVI TP SP16 RA2 ST CEIL LO SPH K yi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq _ cnt); [exact EVI | assumption | exact STw | exact FRq | unfold vep_cells; eassumption | eassumption | exact MU | exact WM]
        | eapply (@seg_src0 _ AI VEP v tag q ya vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HMH HIC ANZ AOBJ AERR NAS NAB HVI TP SP16 RA2 ST CEIL LO SPH K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq _ cnt); [exact EVI | assumption | exact STw | exact FRq | unfold vep_cells; eassumption | eassumption | exact MU | exact WM] ] end.
    - (* [comment removed for export] *)
      replace (201888 + 16) with 201904 by reflexivity.
      zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        eapply evt_cut; [eapply strcmp_spec with (ls := STR_src) (rs := STR_onerror) (v := 4);
          [ rewrite unsigned_lit by lia; apply str_src_at; assumption
          | rewrite unsigned_lit by lia; apply str_onerror_at; assumption
          | reflexivity | assumption ]
        | post_call_fr rsegs mq ] end.
      repeat match goal with Hb : bytes_at _ _ _ _ |- _ => clear Hb end.
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT. lia. } clear KT.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        eapply evt_cut; [eapply strcmp_spec with (ls := STR_onerror) (rs := STR_onerror) (v := 0);
          [ rewrite unsigned_lit by lia; apply str_onerror_at; assumption
          | rewrite unsigned_lit by lia; apply str_onerror_at; assumption
          | reflexivity | assumption ]
        | post_call_fr rsegs mq ] end.
      repeat match goal with Hb : bytes_at _ _ _ _ |- _ => clear Hb end.
      (* [comment removed for export] *)
      zstep. if_cases KT; zify_cond KT. { exfalso. apply KT. reflexivity. } clear KT.
      apply rz_stop.
      lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -112) _ |- _ =>
        eapply (@seg_onerr _ AI VEP v tag q ya vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HMH HIC ANZ AOBJ AERR NAS NAB HVI TP SP16 RA2 ST CEIL LO SPH K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq _ cnt); [assumption | exact STw | exact FRq | unfold vep_cells; eassumption | eassumption | exact MU | exact WM] end.
  Qed.
End S.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem vep_do_include_attr_ok {AI : AllocSpec LayoutP0} : vep_do_include_attr_stmt.
Proof.
  unfold vep_do_include_attr_stmt. intros until T.
  intros AINV MI A0 A1 VOBJ VBASE HENV HG IMG HMH HIC ANZ AOBJ AERR NAS NAB HVI TP SP16 RA2 ST CEIL LO SPH K.
  eapply main; eassumption.
Qed.

End CEIL.

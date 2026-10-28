(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX Image Statics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_oidv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_oid LxConv_getlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxA_sums LxAOid.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_oid_ec_grp () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_lookup1v_postA"; "OID_EC_GRP_VALS"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "A_OID_GET_EC_GRP"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_rt_hyps"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_lookup1v_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_lookup1_stmtA"].


Definition A_OID_GET_EC_GRP : Z := 0x0a86c8.
Definition A_OID_EC_GRP_TBL : Z := 0x0f1aa0.
Notation OID_EC_GRP_STACK_A := 64 (only parsing).
(* [comment removed for export] *)
Definition OID_EC_GRP_VALS : list Z := [1; 2; 3; 4; 5; 10; 11; 12; 6; 7; 8].

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  (* [comment removed for export] *)
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GSB : al_gsb AL = AGSB.
  Hypothesis MCI : arl_memcmp_i R = A_WRAP_BCMP.
  Hypothesis RTC : forall m, arl_rtc R m -> asan_rtc m.
  Hypothesis NEEDB : 0 <= arl_need_bcmp R.
  Hypothesis ISH : forall h LB LF m, HM asegs R HIA h LB LF m -> img_shadow_ok asegs AL m.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (OID EXT P LEN lo : Z) (tg pd v0 : word) (xs : list byte).
  Hypothesis HLEN : Z.of_nat (length xs) = LEN.
  Hypothesis D1 : EXT + 4 <= OID \/ OID + 24 <= EXT.
  Hypothesis D2 : EXT + 4 <= P \/ P + LEN <= EXT.
  Hypothesis AL1 : OID mod 8 = 0.
  Hypothesis AL2 : EXT mod 4 = 0.
  Hypothesis NZ1 : 0 < OID.
  Hypothesis NZ2 : 0 < EXT.
  Hypothesis NZ3 : 0 < P.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 64 - arl_need_bcmp R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : OID + 24 <= lo \/ bv_unsigned sp <= OID.
  Hypothesis DS2 : EXT + 4 <= lo \/ bv_unsigned sp <= EXT.
  Hypothesis DS3 : P + LEN <= lo \/ bv_unsigned sp <= P.
  Hypothesis P47 : P + LEN + 8 <= 2^47.
  Hypothesis CW : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) EXT 4.
  Hypothesis EXTB : EXT + 4 <= 2^64.
  Hypothesis PB : P + LEN <= 2^64.
  Hypothesis OIDB : OID + 24 <= 2^64.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (hcs_img_cs R HIA h IMG GSB) as ICS;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    match goal with HH : HM _ _ _ h LB LF _ |- _ =>
      pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia])
    end.

  Notation W := [(EXT, EXT + 4); (lo, bv_unsigned sp)].
  Notation POST := (oid_lookup1v_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc EXT lo v0 OID_EC_GRP_VALS m).
  Notation TBLC := A_OID_EC_GRP_TBL (only parsing).
  Notation SB := (Z_to_bv 64 (al_sb AL)).

  Definition offsets : list Z := [0; 40; 80; 120; 160; 200; 240; 280; 320; 360; 400].

  Definition seg_stmt (pc : Z) : Prop :=
    forall (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word) (jk : list byte) (mm : mem),
    HM asegs R HIA h LB LF mm ->
    rw_cells asegs mm OID (buf_cells tg pd LEN P) ->
    bytes_at asegs mm P xs ->
    rw_cells asegs mm EXT [C4 v0] ->
    rw_cells asegs mm (bv_unsigned sp + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -64) ->
    mem_inv asegs mm ->
    aobj asegs AL CS mm OID 24 -> aobj asegs AL CS mm P LEN -> aobj asegs AL CS mm EXT 4 ->
    munch W m mm -> wmono asegs m mm ->
    evtA asegs AL CS POST
      (MS (mkR rra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp rt0 rt1 rt2 (Z_to_bv 64 EXT) (Z_to_bv 64 (-46))
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (OID + 8)) (Z_to_bv 64 (OID + 16)) (Z_to_bv 64 (al_sb AL))
               (Z_to_bv 64 (Z.shiftr (OID + 8) 3 + al_sb AL)) s6 s7 s8 s9 s10 s11 rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac seg_ret := lxr_leaf; try lx_rejoin; lx_leaf.
  Ltac seg_next NEXT :=
    lxr_leaf; let LW := fresh "LW" in pose proof NEXT as LW; unfold seg_stmt in LW; lx_apply LW.
  Ltac seg_attr k :=
    let b := eval cbv delta [A_OID_EC_GRP_TBL] in A_OID_EC_GRP_TBL in let a := eval cbv in (b + 40 * k + 32) in lx_tbl_attr1 a.
  Ltac seg_intro :=
    unfold seg_stmt;
    intros rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 jk mm
      HH HOID HXS HEXT FR ST MI OOID OP OEXT MU WM;
    rt_facts;
    pose proof (hm_abase asegs R HIA h LB LF mm HH) as AB;
    pose proof (artA_bcmp asegs R HIA) as SPB; rewrite MCI in SPB; unfold A_WRAP_BCMP in SPB;
    unfold buf_cells in HOID;
    let H := fresh "OTBL" in img_aobj A_OID_EC_GRP_TBL 440 as H; unfold A_OID_EC_GRP_TBL in H.

  Lemma seg_walk_10 : seg_stmt 0xa8970.
  Proof.
    seg_intro.
    seg_attr 10.
    lx_pre. lxr_pose. lxa_auto [SUM_bcmp0A 0x25f00 9 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
    lx_pre. lx_run_tac (PLANS [] [(0xa8a50, DJoin); (0xa8a64, DJoin)] 150%N [SUM_bcmp0A 0x25f00 9 1 4 5 6]).
    lx_tree. all: lxa_unglob.
    all: lazymatch goal with
         | |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => seg_ret
         | |- _ => idtac
         end.
  Qed.

  Lemma seg_walk_9 : seg_stmt 0xa8934.
  Proof.
    seg_intro.
    seg_attr 9.
    lx_pre. lxr_pose. lxa_auto [SUM_bcmp0A 0x25ea0 9 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
    lx_pre. lx_run_tac (PLANS [0xa8970] [(0xa8a50, DJoin); (0xa8a64, DJoin)] 150%N [SUM_bcmp0A 0x25ea0 9 1 4 5 6]).
    lx_tree. all: lxa_unglob.
    all: lazymatch goal with
         | |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => seg_ret
         | |- context [MS _ _ (Z_to_bv 64 0xa8970) _ _ _ (seg_rom _)] => seg_next seg_walk_10
         | |- _ => idtac
         end.
  Qed.

  Lemma seg_walk_8 : seg_stmt 0xa88f8.
  Proof.
    seg_intro.
    seg_attr 8.
    lx_pre. lxr_pose. lxa_auto [SUM_bcmp0A 0x25e40 9 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
    lx_pre. lx_run_tac (PLANS [0xa8934] [(0xa8a50, DJoin); (0xa8a64, DJoin)] 150%N [SUM_bcmp0A 0x25e40 9 1 4 5 6]).
    lx_tree. all: lxa_unglob.
    all: lazymatch goal with
         | |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => seg_ret
         | |- context [MS _ _ (Z_to_bv 64 0xa8934) _ _ _ (seg_rom _)] => seg_next seg_walk_9
         | |- _ => idtac
         end.
  Qed.

  Lemma seg_walk_7 : seg_stmt 0xa88bc.
  Proof.
    seg_intro.
    seg_attr 7.
    lx_pre. lxr_pose. lxa_auto [SUM_bcmp0A 0x25e00 5 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
    lx_pre. lx_run_tac (PLANS [0xa88f8] [(0xa8a50, DJoin); (0xa8a64, DJoin)] 150%N [SUM_bcmp0A 0x25e00 5 1 4 5 6]).
    lx_tree. all: lxa_unglob.
    all: lazymatch goal with
         | |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => seg_ret
         | |- context [MS _ _ (Z_to_bv 64 0xa88f8) _ _ _ (seg_rom _)] => seg_next seg_walk_8
         | |- _ => idtac
         end.
  Qed.

  Lemma seg_walk_6 : seg_stmt 0xa8880.
  Proof.
    seg_intro.
    seg_attr 6.
    lx_pre. lxr_pose. lxa_auto [SUM_bcmp0A 0x25dc0 5 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
    lx_pre. lx_run_tac (PLANS [0xa88bc] [(0xa8a50, DJoin); (0xa8a64, DJoin)] 150%N [SUM_bcmp0A 0x25dc0 5 1 4 5 6]).
    lx_tree. all: lxa_unglob.
    all: lazymatch goal with
         | |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => seg_ret
         | |- context [MS _ _ (Z_to_bv 64 0xa88bc) _ _ _ (seg_rom _)] => seg_next seg_walk_7
         | |- _ => idtac
         end.
  Qed.

  Lemma seg_walk_5 : seg_stmt 0xa8844.
  Proof.
    seg_intro.
    seg_attr 5.
    lx_pre. lxr_pose. lxa_auto [SUM_bcmp0A 0x25d80 5 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
    lx_pre. lx_run_tac (PLANS [0xa8880] [(0xa8a50, DJoin); (0xa8a64, DJoin)] 150%N [SUM_bcmp0A 0x25d80 5 1 4 5 6]).
    lx_tree. all: lxa_unglob.
    all: lazymatch goal with
         | |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => seg_ret
         | |- context [MS _ _ (Z_to_bv 64 0xa8880) _ _ _ (seg_rom _)] => seg_next seg_walk_6
         | |- _ => idtac
         end.
  Qed.

  Lemma seg_walk_4 : seg_stmt 0xa8808.
  Proof.
    seg_intro.
    seg_attr 4.
    lx_pre. lxr_pose. lxa_auto [SUM_bcmp0A 0x25d40 5 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
    lx_pre. lx_run_tac (PLANS [0xa8844] [(0xa8a50, DJoin); (0xa8a64, DJoin)] 150%N [SUM_bcmp0A 0x25d40 5 1 4 5 6]).
    lx_tree. all: lxa_unglob.
    all: lazymatch goal with
         | |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => seg_ret
         | |- context [MS _ _ (Z_to_bv 64 0xa8844) _ _ _ (seg_rom _)] => seg_next seg_walk_5
         | |- _ => idtac
         end.
  Qed.

  Lemma seg_walk_3 : seg_stmt 0xa87cc.
  Proof.
    seg_intro.
    seg_attr 3.
    lx_pre. lxr_pose. lxa_auto [SUM_bcmp0A 0x25d00 5 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
    lx_pre. lx_run_tac (PLANS [0xa8808] [(0xa8a50, DJoin); (0xa8a64, DJoin)] 150%N [SUM_bcmp0A 0x25d00 5 1 4 5 6]).
    lx_tree. all: lxa_unglob.
    all: lazymatch goal with
         | |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => seg_ret
         | |- context [MS _ _ (Z_to_bv 64 0xa8808) _ _ _ (seg_rom _)] => seg_next seg_walk_4
         | |- _ => idtac
         end.
  Qed.

  Lemma seg_walk_2 : seg_stmt 0xa8790.
  Proof.
    seg_intro.
    seg_attr 2.
    lx_pre. lxr_pose. lxa_auto [SUM_bcmp0A 0x25cc0 8 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
    lx_pre. lx_run_tac (PLANS [0xa87cc] [(0xa8a50, DJoin); (0xa8a64, DJoin)] 150%N [SUM_bcmp0A 0x25cc0 8 1 4 5 6]).
    lx_tree. all: lxa_unglob.
    all: lazymatch goal with
         | |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => seg_ret
         | |- context [MS _ _ (Z_to_bv 64 0xa87cc) _ _ _ (seg_rom _)] => seg_next seg_walk_3
         | |- _ => idtac
         end.
  Qed.

  Lemma seg_walk_1 : seg_stmt 0xa8754.
  Proof.
    seg_intro.
    seg_attr 1.
    lx_pre. lxr_pose. lxa_auto [SUM_bcmp0A 0x25c80 5 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
    lx_pre. lx_run_tac (PLANS [0xa8790] [(0xa8a50, DJoin); (0xa8a64, DJoin)] 150%N [SUM_bcmp0A 0x25c80 5 1 4 5 6]).
    lx_tree. all: lxa_unglob.
    all: lazymatch goal with
         | |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => seg_ret
         | |- context [MS _ _ (Z_to_bv 64 0xa8790) _ _ _ (seg_rom _)] => seg_next seg_walk_2
         | |- _ => idtac
         end.
  Qed.




  Local Ltac2 Set LiaOrc.tbl := fun () => "02M0@D1321268744.117 D55386061505.117D563007111.118  D62022258533.118L11196619170.180L11818975218.182L12351228705.0  L1236133506.198 L12797248770.184L1289004050.164 L13421714258.198L13706168263.84 L13706168263.85 L13706168263.86 L13706168263.87 L13706178068.84 L13706178068.85 L13706178068.86 L13706178068.87 L13706178455.84 L13706178455.85 L13706178455.86 L13706178455.87 L15039373650.212L15471961447.124L1550667292.124 L15629820850.244L16098824082.166L1703206428.124 L17470411553.0  L17829562994.182L18013285419.124L1874603548.124 L18772075036.124L1884170098.244 L18926711324.124L19096011292.124L19388666619.124L20496473106.180L20667467707.124L21101600626.212L22655999393.0  L22704339666.228L23326693602.166L23840176722.166L24904065170.212L25580706365.125L26006424866.198L26542899778.228L26897839035.124L27607066754.182L28742641666.198L29315528524.124L29337807714.166L29428324939.5  L29913304631.124L30195726845.125L31115876057.2  L3126340958.124 L31378308326.102L31506485805.125L32016776450.196L32614037602.228L34216778690.212L34811668002.244L34882647402.130L34882647402.147L34882647402.200L34882647402.90 L35323053970.198L35348421442.182L35653441506.7  L35995059740.124L36147598876.124L36408115586.228L36588325665.0  L37497119229.125L37625111090.166L38162114386.228L38179144178.198L39067712573.125L39227854226.182L39941904941.125L40228188091.124L40387014578.228L4109263074.198 L41229852833.0  L41272565821.113L41272565821.114L41272565821.115L41272565821.128L41272565821.129L41272565821.130L41272565821.143L41272565821.144L41272565821.158L41272565821.173L41272565821.188L43061431611.100L4354443041.0   L43652758706.166L44123854994.244L44195295649.0  L45067427193.2  L45249206290.182L46398999037.125L46979947250.180L48044097842.198L48813779005.125L49145938722.182L50277581474.244L50748681858.166L51302190658.244L51862563212.124L51899451554.212L53047159324.124L53216475676.124L53558549435.124L5491307771.124 L55156809122.182L55299785966.155L55299785966.194L55299785966.211L55299785966.266L55299799889.130L55299799889.147L55299799889.200L55299799889.90 L55787951613.125L56759286018.166L57356534882.198L58127621921.0  L58488191970.196L58999301458.182L59131364238.124L59314873579.2  L59314873579.3  L59314873579.4  L59381307131.124L59590018322.244L60087256107.124L60098763854.3  L60197645006.124L61952791329.0  L62042275325.125L62074852380.124L62726766523.124L63370311324.124L63409269202.196L65420710397.125L66664791762.198L66888906683.124L67800628818.184L68395268274.196L68432392609.0  L7709701537.0   L8927552119.124 00000?00N00e01601701801901:01;01<01=01>01?01@01A01a02502G02H02Y02m03?03@03A03P03_03`03a04004104204A04P04_04`04o05>05M05N05]05^05_05`05a05b05c06606706806G06H06I06X06Y06k07:07M07N07]07l08?08@08A08B08C08D08E08F08G08H08I08a09009?09@09A09T09U09V09W09j09k0:>0:M0:N0:O0:P0:_0:n0;=0;L0;[0;j0<90<H0<W0<f0=50><0>=0>>0>?0>@0>A0>B0>U0>V0>W0>j0>k0>l0>m0>n0?=0?>0?M0?\0?k0@:0@;0@<0@=0@>0@?0@@0@A0@B0@C0@V0@W0@X0@Y0@Z0@[0@j0@k0@l0@m0A<0A=0AL0AV0Ae0Af0B90BH0BW0Bf0Bg0C:0C;0CJ0CK0CL0CM0CN0C]S2sp3OID3EXT2xsS2sp3OID3EXT2xsS1R3HIA1h2sp3OID3EXT2xsS1R2sp3OID3EXT2xsFFSFFFFFFFFS1R5NEEDB2sp1P2lo2xs3SLO1a2Ha2H1S2sp1P2lo2xs1a2Ha2H1S3EXT1P2xs1a2Ha2H1FS2sp1P2xs1a2Ha2H1S2sp1P2lo2xs1a2Ha2H1S3EXT1P2xs1a2Ha2H1FFS2sp3OID3EXT2xsS2sp3OID3EXT2xsFFS2sp3OID3EXT2xsSFS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsFS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsFS2sp3OID3EXT2xsFSFFFFS1R2sp3OID3EXT2xs1HFFS2sp3OID3EXT2xsFFS2sp3OID3EXT2xsFS1R2lo3LOS3ALO3ACPS2sp3OID3EXT2xsS1R2sp3OID3EXT2xs1HFS2sp3OID3EXT2xsS2sp3OID3EXT2xsS1R2sp3OID3EXT2xs1HFFFFFFFFFFS1R3HIA1h2sp2lo3TOP4HTOPS2sp3OID3EXT2xsS2sp3OID3EXT2xsFSS1R2sp3OID3EXT2xs1HFFFS1R2sp3OID3EXT2xs1HFS1R2sp3OID3EXT2xs1HS2sp3OID3EXT2xsFFSS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsS1R5NEEDB2sp3OID3EXT1P3LEN2lo2xs4HLEN2D12D23NZ13NZ23SLO3DS13DS23DS33SPRSFFSFFS1R2sp3OID3EXT2xs1HFFS1R2sp3OID3EXT2xs1HFFFFS2sp3OID3EXT2xsFS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsFFFFFFFFFS1R2sp3OID3EXT2xs1HFFSFFS2sp3OID3EXT2xsFFFS2sp3OID3EXT2xsFS2sp3OID3EXT2xsS1R2lo3LOSS2sp3OID3EXT2xsSS1R2sp3OID3EXT2xs1HS2sp3OID3EXT2xsS2sp3OID3EXT2xsS2sp3OID3EXT2xsFS1R2sp3OID3EXT2xs1HFS2sp3OID3EXT2xsFFSSS2sp3OID3EXT2xs". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_oid_ec_grp ()) "Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)P,(1.$2.VR,VHIA,Vh,VLB,VLF,Vm,)P,(3.$2.Vm,VOID,(4.Vtg,Vpd,VLEN,VP,))P,(5.$2.Vm,VP,Vxs,)P,(3.$2.Vm,VEXT,(6.$7.(8.Vv0,)(9.$7.)))P,(:.$2.Vm,Vlo,(;.&40.Vsp,))P,(<.$2.Vm,)P,(=.$2.(>.VR,)(?.$2.VR,VHIA,Vh,)Vm,VOID,+18.)P,(=.$2.(>.VR,)(?.$2.VR,VHIA,Vh,)Vm,VP,VLEN,)P,(=.$2.(>.VR,)(?.$2.VR,VHIA,Vh,)Vm,VEXT,+4.)(10.$2.(>.VR,)(?.$2.VR,VHIA,Vh,)(11.$2.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VEXT,Vlo,Vv0,$12.Vm,)(13.(14.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(15.&40.VOID,)(15.&40.VEXT,)R?.R>.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(15.&40.$16.)Vfc,(17.(0.&40.))Vm,(18.$2.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros x5 x6 x7 x12 x13 x14 x15 x16 x17 HH HOID HXS HEXT ST MI OOID OP OEXT.
  rt_facts.
  unfold A_OID_GET_EC_GRP.
  pose proof (munch_refl W m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
  pose proof (artA_bcmp asegs R HIA) as SPB.
  rewrite MCI in SPB.
  unfold A_WRAP_BCMP in SPB.
  unfold buf_cells in HOID.
  carve_frame 64%nat ST.
  img_aobj A_OID_EC_GRP_TBL 440 as OTBL. unfold A_OID_EC_GRP_TBL in OTBL.   (* [comment removed for export] *)
  lx_tbl_attrs A_OID_EC_GRP_TBL offsets 32.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  lx_pre. lxr_pose. lxa_auto [SUM_bcmp0A 0x25c40 8 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
  lx_pre. lx_run_tac (PLANS [0xa8754] [(0xa8a50, DJoin); (0xa8a64, DJoin)] 150%N [SUM_bcmp0A 0x25c40 8 1 4 5 6]).
  lx_tree. all: lxa_unglob.
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => seg_ret | |- context [MS _ _ (Z_to_bv 64 0xa8754) _ _ _ (seg_rom _)] => seg_next seg_walk_1 | |- _ => idtac end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L13667526808.81L36071685254.81L58646921526.8100000I00]011S2sp3OID3EXT1P3LEN2xs3P47S2sp3OID3EXT2xs4OIDBS2sp3OID3EXT2xs4EXTB". (* [comment removed for export] *)
Lemma A_oid_get_ec_grp_v_spec : ltac2:(CDefT.buildp (gd_tbl_A_oid_ec_grp ()) "PR,$19.PHIA,(1:.$2.R1.)P,(1;.R2.R1.)(1<.$2.R3.R2.$16.+40.$12.)")
(* [comment removed for export] *).
Proof.
  intros R HIA (IMG & GSB & MCI & RTC & NEEDB & ISH).
  unfold oid_lookup1v_stmtA. intros until xs.
  intros HH HOID HXS HLEN HEXT D1 D2 AL1 AL2 NZ1 NZ2 NZ3 ST LOS SLO TOP SPA DS1 DS2 DS3 P47 CW MI OOID OP OEXT -> ->.
  pose proof (rw_cells_bound _ _ _ _ HEXT) as EXTB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in EXTB.
  change (Z.of_nat 4) with 4 in EXTB.
  pose proof (rw_cells_bound _ _ _ _ HOID) as OIDB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ buf_cells] in OIDB.
  change (Z.of_nat 24) with 24 in OIDB.
  pose proof (bytes_at_bound _ _ _ _ HXS) as PB. rewrite HLEN in PB.
  eapply main_walk; try eassumption; try lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma A_oid_get_ec_grp_spec : ltac2:(CDefT.buildp (gd_tbl_A_oid_ec_grp ()) "PR,$19.PHIA,(1:.$2.R1.)P,(1;.R2.R1.)(1=.$2.R3.R2.$16.+40.)")
(* [comment removed for export] *).
Proof. intros R HIA H. eapply oid_lookup1v_weakenA. apply A_oid_get_ec_grp_v_spec. exact H. Qed.

(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_cmp_int P_mpi_add_int.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_cmp_mpi A_frame_lib A_frame_kit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
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
Ltac2 gd_tbl_A_mpi_cmp_int () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_mpi.mpi_cmp_postA"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.abs"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_cmp.SIGF"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"].


Definition A_MPI_CMP_INT_E : Z := 0x9dd64.   (* [comment removed for export] *)
Notation MPI_CMP_INT_STACK_A := 128 (only parsing).
Definition A_SMALLOC_0_CI : Z := 0x52ef8.
Definition A_UAR_GOT_CI : Z := 0xf5ea8.

Definition mpi_cmp_int_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r lo : Z) (m : mem) (ms' : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (h' : HST segs R HIA),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ presA segs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi segs R HIA h) [] m m'
    /\ hcs segs R HIA h' = hcs segs R HIA h /\ htop segs R HIA h' = htop segs R HIA h
    /\ hstkhi segs R HIA h' = hstkhi segs R HIA h /\ hflag segs R HIA h' = hflag segs R HIA h
    /\ havol segs R HIA h' = havol segs R HIA h /\ hfr segs R HIA h' = hfr segs R HIA h
    /\ (forall mo, HK segs R HIA h' mo <-> HK segs R HIA h mo)
    /\ HM segs R HIA h' LB LF m'.

Definition mpi_cmp_int_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop :=
  forall (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (dX : mpd) (z lo slo : Z),
    HM segs R HIA h LB LF m ->
    (length LF < 512)%nat ->
    mpd_at segs m LB dX ->
    (md_own dX = LHeap -> 0 < md_p dX) ->
    -2^31 <= z < 2^31 ->
    mem_inv segs m ->
    aobj segs (arl_AL R) (hcs segs R HIA h) m (md_addr dX) 16 ->
    (1 <= md_n dX -> aobj segs (arl_AL R) (hcs segs R HIA h) m (md_p dX) (4 * md_n dX)) ->
    client_range (arl_L R) (LB ++ fdata LF) lo (md_addr dX) 16 ->
    (md_own dX = LStatic -> img_norz (md_p dX) (4 * md_n dX) = true) ->
    stk segs m lo (bv_unsigned sp) ->
    arl_stklo R <= lo ->
    lo <= bv_unsigned sp - MPI_CMP_INT_STACK_A ->
    lo <= bv_unsigned sp - 112 - arl_need_smalloc R ->
    bv_unsigned sp <= htop segs R HIA h ->
    bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 (arl_tp R) ->
    sshad segs (arl_AL R) m slo (bv_unsigned sp) ->
    arl_stklo R <= slo ->
    slo <= bv_unsigned sp - 96 ->
    (md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX) ->
    (1 <= md_n dX -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX) ->
    a0 = Z_to_bv 64 (md_addr dX) ->
    a1 = Z_to_bv 64 z ->
    evtA segs (arl_AL R) (hcs segs R HIA h)
      (mpi_cmp_int_postA segs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (Z.sgn (mpd_val dX - z)) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.

Lemma lx_abs_limb_ci : forall b : Z, -2^31 <= b < 2^31 ->
  zswrap 32 (zlow 32 (Z.lxor b (Z.shiftr b 31) + - Z.shiftr b 31)) = abs_limb_expr b.
Proof.
  intros b Hb. unfold zswrap, zlow, abs_limb_expr.
  change 18446744073709551616%Z with (2^64)%Z.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N N.sub].
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
  replace (2 ^ 32 `div` 2)%Z with (2^31)%Z by reflexivity.
  change (2 ^ (32 - 1))%Z with (2^31)%Z.
  rewrite !Z.shiftr_div_pow2 by lia.
  destruct (Z.ltb_spec b 0) as [NEG|POS].
  - assert (D : (b / 2 ^ 31 = -1)%Z).
    { symmetry. apply (Z.div_unique b (2^31) (-1) (b + 2^31)); lia. }
    rewrite D. rewrite Z.lxor_m1_r. unfold Z.lnot.
    assert (E1 : (b mod 2^64 = 2^64 + b)%Z) by (rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small; lia).
    rewrite E1.
    assert (E2 : ((2^64 + b + 2^31) mod 2^32 - 2^31 = b)%Z).
    { replace (2^64 + b + 2^31)%Z with ((b + 2^31) + 2^32 * 2^32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small; lia. }
    rewrite E2. rewrite D.
    replace (((-1 + 2^31) mod 2^32 - 2^31))%Z with (-1)%Z by reflexivity.
    replace ((-1) mod 2^64)%Z with (2^64 - 1)%Z by reflexivity.
    change (2^64 - 1)%Z with 18446744073709551615%Z. rewrite OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MpiWalkAux.lxor_allones64 by lia.
    replace (Z.pred (- b) + - (-1))%Z with (-b)%Z by lia.
    rewrite (Z.mod_small (-b) (2^32)) by lia.
    replace (18446744073709551615 - (2 ^ 64 + b) - 18446744073709551615 + 2^31)%Z with ((- b + 2^31) + (- 2^32) * 2^32)%Z by lia.
    rewrite Z.mod_add by lia.
    reflexivity.
  - rewrite (Z.div_small b) by lia.
    rewrite Z.lxor_0_r. rewrite (Z.mod_small b (2^64)) by lia.
    replace (b + - 0)%Z with b by lia. rewrite (Z.mod_small b (2^32)) by lia.
    assert (E2 : ((b + 2^31) mod 2^32 - 2^31 = b)%Z) by (rewrite Z.mod_small; lia). rewrite !E2.
    rewrite (Z.div_small b) by lia.
    replace ((0 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31)%Z with 0%Z by reflexivity. change (0 mod 2^64)%Z with 0%Z.
    rewrite Z.lxor_0_r. rewrite Z.sub_0_r. rewrite !E2. reflexivity.
Qed.

Lemma aobj_of_partial_ci : forall (segs : list Segment) (AL : asan_layout) (CS : Z -> Prop) (m : mem) (B : Z)
    (cs : list cell) (A : Z) (g0 : nat) (k : Z),
  cs_ok AL CS -> rw_cells segs m (Z.shiftr B 3 + al_sb AL) cs -> crange CS A k -> B mod 8 = 0 -> 0 <= B ->
  A = B + 8 * Z.of_nat g0 -> 1 <= k <= 7 -> cell_at cs g0 = Some (C1 (Z_to_bv 8 k)) -> aobj segs AL CS m A k.
Proof.
  intros segs AL CS m B cs A g0 k OK H HC HB H0 HA Hk HZ.
  replace (Z.shiftr B 3 + al_sb AL) with (shadow_of AL B) in H
    by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
  split; [exact HC|].
  intros a Ha. exists (Z_to_bv 8 k). split.
  - flat constr:(OK) 2%nat. flclear OK. intros C1' _. flat constr:((C1' a (HC a Ha))) 4%nat. intros R0 R1 R2 _.
    pose proof (rw_cells_read segs m _ cs g0 _ H HZ) as RD. cbn [csize cbytes] in RD.
    assert (E : shadow_of AL a = shadow_of AL B + Z.of_nat g0).
    { unfold shadow_of. subst A.
      assert (E8 : a / 8 = B / 8 + Z.of_nat g0); [| rewrite E8; lia].
      pose proof (Z.div_mod B 8 ltac:(lia)) as DB. rewrite HB in DB.
      symmetry. apply (Z.div_unique a 8 (B / 8 + Z.of_nat g0) (a - B - 8 * Z.of_nat g0)); lia. }
    rewrite E. apply (bytes_at_of_read1 segs); [lia| lia| exact RD].
  - right. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow Z.of_N Pos.pow]. rewrite (Z.mod_small k) by lia.
    subst A. pose proof (Z.div_mod B 8 ltac:(lia)) as DB. rewrite HB in DB.
    assert (EM : a mod 8 = a - B - 8 * Z.of_nat g0).
    { symmetry. apply (Z.mod_unique a 8 (B / 8 + Z.of_nat g0) (a - B - 8 * Z.of_nat g0)); lia. }
    rewrite EM. lia.
Qed.

Lemma aobj_of_sshad_ci : forall (AL : asan_layout) (CS : Z -> Prop) mX slo' shi B (k : nat),
  cs_ok AL CS -> sshad asegs AL mX slo' shi -> slo' <= B -> B + 8 * Z.of_nat (S k) <= shi -> B mod 8 = 0 -> 0 <= B ->
  crange CS B (8 * Z.of_nat (S k)) -> aobj asegs AL CS mX B (8 * Z.of_nat (S k)).
Proof.
  intros AL CS mX slo' shi B k OK SS H1 H2 HB H0 HC.
  pose proof (sshad_chunk asegs AL mX slo' shi k B SS H1 H2 HB) as SH.
  replace (shadow_of AL B) with (Z.shiftr B 3 + al_sb AL) in SH
    by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
  eapply (aobj_of_zero_shadow_sh asegs AL CS mX B (zcells (S k)) B 0 (S k) OK SH HC HB H0 ltac:(lia)).
  intros i Hi. apply cell_at_zcells. exact Hi.
Qed.

Definition A_CI_RET : Z := 0x9de98.

Section WalkC.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_CI.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0_CI.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis CMP : mpi_cmp_mpi_stmtA asegs AL A_MPI_CMP_MPI_E.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (z lo : Z).
  Hypothesis BZ : -2^31 <= z < 2^31.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 128.
  Hypothesis SLOS : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_CI in UARG; unfold A_SMALLOC_0_CI in SM0;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation FSHL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 4);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition S1P (a0v : Z) (ms : machine_state) : Prop :=
    exists (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem)
           (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w0 w1 w2 padw : word),
      ms = MS (mkR (Z_to_bv 64 A_CI_RET) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1)
                   (Z_to_bv 64 a0v) (Z_to_bv 64 (sp1 + 16)) a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 FB) (Z_to_bv 64 z) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB)
                   (Z_to_bv 64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 A_MPI_CMP_MPI_E) fc None m1 (seg_rom asegs)
      /\ bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96
      /\ sp1 mod 32 = 0
      /\ HM asegs R HIA h1 LB ((FB, 64) :: LF) m1
      /\ hcs asegs R HIA h1 = hcs asegs R HIA h
      /\ htop asegs R HIA h1 = htop asegs R HIA h
      /\ hstkhi asegs R HIA h1 = hstkhi asegs R HIA h
      /\ hflag asegs R HIA h1 = hflag asegs R HIA h
      /\ havol asegs R HIA h1 = havol asegs R HIA h
      /\ hfr asegs R HIA h1 = hfr asegs R HIA h
      /\ (forall mo, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo)
      /\ FB mod 64 = 0
      /\ fresh_apart R LB LF FB 64
      /\ rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2]
      /\ rw_cells asegs m1 (FB + 32) [C4 (Z_to_bv 64 (abs_limb_expr z))]
      /\ rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) FSHL
      /\ rw_cells asegs m1 (bv_unsigned sp + -64) SAVEL
      /\ rw_cells asegs m1 (sp1 + 8) [C8 (Z_to_bv 64 FB)]
      /\ rw_cells asegs m1 (sp1 + 16) [C8 (Z_to_bv 64 (FB + 32)); C2 (Z_to_bv 64 (sgn_of z)); C2 (Z_to_bv 64 1); C4 padw]
      /\ stk asegs m1 sp1 (sp1 + 8)
      /\ stk asegs m1 (sp1 + 32) (bv_unsigned sp + -64)
      /\ stk asegs m1 lo sp1
      /\ mem_inv asegs m1
      /\ presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1.

  #[local] Ltac lx_pins_hook ::= try lx_pin1 CMP.
  Lemma pro_walk : forall (a0v : Z) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      HM asegs R HIA h LB LF m -> stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      evtA asegs AL CS (S1P a0v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 z) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_MPI_CMP_INT_E) fc None m (seg_rom asegs)).
  Proof.
  intros a0v t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH ST MI.
  unfold A_MPI_CMP_INT_E.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
  flat constr:(IMG') 3%nat. flclear IMG'. intros EGOT ELO EHI.
  carve_frame 96%nat ST.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
  lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
  pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
  pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
  (flat constr:((hm_auar asegs R HIA h LB LF mc HHc)) 2%nat; intros UGOT UFLAG);
  pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
  end end.
  rewrite EGOT in GOT.
  rewrite UARG in UGOT.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 160%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV; lia | lx_side_lia ]).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(first [ clear - SP1 SLOS NS1; lia | lx_side_lia ])) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 0x52ef8) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - SLOS SP1 TOP NS1; lia | lx_side_lia ]
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      try clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      try clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        (flat constr:(H) 9%nat; flclear H; intros h1 Ehcs Ehtop Estk Eflag Evol Efr HKI SMC) end.
      flat constr:(SMC) 8%nat. flclear SMC. intros FB junkf Ea0 F64 FRSH HH1 FRM FSH. lazymatch type of Ea0 with ?x = _ => subst x end.
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      zstep. zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. flat constr:(FRSH) 3%nat. flclear FRSH. intros F0 F1 _.
          try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      try clear Kb.
      try (change (64 * 2 ^ 0) with 64 in * ).
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS).
      change (64 / 8) with 8 in SBND, APS. change (64 - 40) with 24 in IND.
      pose proof (art_stk_high asegs R HIA) as STKH.
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -96 + 32) with (bv_unsigned sp + -64) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa STx (bv_unsigned sp + -64); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 32) (bv_unsigned sp + -64) STJ ltac:(first [ clear - SP1; lia | lx_side_lia ])) as [STlo SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 32) 4 STlo ltac:(clear; lia)) as [STa [jpad YPAD]].
      replace (sp1 + 32 - Z.of_nat 4) with (sp1 + 28) in STa, YPAD by (clear; lia). clear STlo.
      destruct (stk_split asegs m3 sp1 (sp1 + 16) (sp1 + 28) STa ltac:(clear; lia)) as [STb STY]. clear STa.
      destruct (stk_carve asegs m3 sp1 (sp1 + 16) 8 STb ltac:(clear; lia)) as [STlo [jslot SLOT]].
      replace (sp1 + 16 - Z.of_nat 8) with (sp1 + 8) in STlo, SLOT by (clear; lia). clear STb.
      cb8_to_c8 SLOT (@nil cell).
      apply (rw_cells_split_CB asegs m3 FB [] 64 junkf [] [8; 8; 8; 8; 4; 28]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat LMB FREST.
      lazymatch type of LMB with rw_cells _ _ ?a _ => replace a with (FB + 32) in LMB by (clear; lia) end.
      try clear FLNK. try clear FREST.
      cb8_to_c8 FHD (@nil cell).
      cbn [zcells] in FSH.
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0x9d9a4] [] 200%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (match goal with H : context [zswrap 32 (zlow 32 (Z.lxor ?bb (Z.shiftr ?bb 31) + - Z.shiftr ?bb 31))] |- _ =>
         rewrite (lx_abs_limb_ci bb) in H by (first [ assumption | lx_side_lia ]) end).
  try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  lazymatch goal with H : rw_cells _ m9 (sp1 + 8) (C8 _ :: C8 _ :: _) |- _ => rename H into SLOTY end.
  chunk_split SLOTY 1%nat SLOT1 YST.
  lazymatch type of YST with rw_cells _ _ ?a _ => replace a with (sp1 + 16) in YST by (clear; lia) end.
  lazymatch type of YST with rw_cells _ _ _ [C8 ?pp; C2 (Z_to_bv 64 ?sw); C2 ?one] =>
    pose proof (rw_cells_C2_congr asegs m9 (sp1 + 16) [C8 pp] sw (sgn_of z) [C2 one] YST (sign_half_val z BZ)) as YST';
    cbn [app] in YST'; clear YST end.
  assert (YCELLS : rw_cells asegs m9 (sp1 + 16)
                    [C8 (Z_to_bv 64 (FB + 32)); C2 (Z_to_bv 64 (sgn_of z)); C2 (Z_to_bv 64 1); C4 (le_bytes_to_word jpad)]).
  { change [C8 (Z_to_bv 64 (FB + 32)); C2 (Z_to_bv 64 (sgn_of z)); C2 (Z_to_bv 64 1); C4 (le_bytes_to_word jpad)]
      with ([C8 (Z_to_bv 64 (FB + 32)); C2 (Z_to_bv 64 (sgn_of z)); C2 (Z_to_bv 64 1)] ++ [C4 (le_bytes_to_word jpad)]).
    apply (proj2 (rw_cells_app asegs m9 _ _ _)). split; [exact YST'|].
    lazymatch goal with |- rw_cells _ _ ?a _ => replace a with (sp1 + 28) by (cbn; clear; lia) end.
    exact (cells_CB4_C4 asegs m9 _ jpad YPAD). }
  apply evtA_done. unfold S1P.
  exists FB, sp1, h1, m9.
  do 17 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [exact SP1|]. split; [exact SP1M|].
  split; [exact HH1|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|].
  split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
  split; [exact F64|]. split; [exact FRSH|].
  split; [exact FHD|]. split; [exact LMB|]. split; [exact FSHX|].
  split; [exact SAVE|]. split; [exact SLOT1|]. split; [exact YCELLS|].
  split; [exact STlo|]. split; [exact SThi|].
  split; [assumption|]. split; [assumption|].
  exact PRES.
  Qed.

  Definition EPOST (h3 : HST asegs R HIA) (m0 : mem) (r : Z) (ms : machine_state) : Prop :=
    exists (m' : mem) (h4 : HST asegs R HIA) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                   t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ presW asegs R HIA h3 LB LF (bv_unsigned sp) (arl_stklo R) [] m0 m'
      /\ hcs asegs R HIA h4 = hcs asegs R HIA h3 /\ htop asegs R HIA h4 = htop asegs R HIA h3
      /\ hstkhi asegs R HIA h4 = hstkhi asegs R HIA h3 /\ hflag asegs R HIA h4 = hflag asegs R HIA h3
      /\ havol asegs R HIA h4 = havol asegs R HIA h3 /\ hfr asegs R HIA h4 = hfr asegs R HIA h3
      /\ (forall mo, HK asegs R HIA h4 mo <-> HK asegs R HIA h3 mo)
      /\ HM asegs R HIA h4 LB LF m'.

  #[local] Ltac lx_pins_hook ::= try lx_pin1 CMP; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 SLOS; try lx_pin1 BZ.
  Lemma epi_walk : forall (h3 : HST asegs R HIA) (m0 mm : mem) (FB sp1 : Z)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w0 w1 w2 : word) (r : Z),
      HM asegs R HIA h3 LB ((FB, 64) :: LF) mm ->
      hcs asegs R HIA h3 = CS ->
      htop asegs R HIA h3 = htop asegs R HIA h ->
      hstkhi asegs R HIA h3 = hstkhi asegs R HIA h ->
      bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96 ->
      sp1 mod 32 = 0 ->
      FB mod 64 = 0 ->
      fresh_apart R LB LF FB 64 ->
      rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2] ->
      rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) FSHL ->
      rw_cells asegs mm (bv_unsigned sp + -64) SAVEL ->
      rw_cells asegs mm (sp1 + 8) [C8 (Z_to_bv 64 FB)] ->
      stk asegs mm sp1 (sp1 + 8) ->
      stk asegs mm (sp1 + 16) (bv_unsigned sp + -64) ->
      stk asegs mm lo sp1 ->
      mem_inv asegs mm ->
      presW asegs R HIA h3 LB LF (bv_unsigned sp) (arl_stklo R) [] m0 mm ->
      evtA asegs AL (hcs asegs R HIA h3) (EPOST h3 m0 r)
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 FB) (Z_to_bv 64 z) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB)
                 (Z_to_bv 64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_CI_RET) fc None mm (seg_rom asegs)).
  Proof.
  intros h3 m0 mm FB sp1 xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w0 w1 w2 r
         HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FHD FSH SAVE SLOT STA STB STlo MI PRES.
  unfold A_CI_RET.
  rt_facts.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV; lia | lx_side_lia ]).
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LB LF mm FB 64 lo HH3 eq_refl FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
    as (CFB & INF & INH & IND & AP & _ & F8 & FBLO & SBND & APS).
  change (64 / 8) with 8 in SBND, APS.
  assert (SCS : crange CS lo (bv_unsigned sp - lo))
    by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (rewrite HCS3; exact SCS).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (rewrite HCS3; exact SCS0).
  pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
  flat constr:(FRSH') 4%nat. flclear FRSH'. intros F0 F1 F2 F3.
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x9ded0] [] 160%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 LB ((FB, 64) :: LF) me FB 64 HHe ltac:(left; reflexivity))
    as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 64 - 8) with (FB + 56) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b', In b' (LB ++ fdata LF) -> In b' (LB ++ fdata ((FB, 64) :: LF)))
    by (intros b' Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -64 + 64 <= p \/ p + 1 <= bv_unsigned sp + -64).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 8 + 8 <= p \/ p + 1 <= sp1 + 8).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS SP1; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp : wcover R LB LF (bv_unsigned sp) [] p 1)
    by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO; lia | lx_side_lia ]]).
  clear HHe NCp NSp.
  repeat match goal with H : rw_cells _ me FB _ |- _ => clear H end.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f). subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 14 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  { lazymatch goal with H : rw_cells _ mf (sp1 + 8) _ |- _ => rename H into SLOTf end.
    lazymatch goal with H : rw_cells _ mf (bv_unsigned sp + -64) _ |- _ => rename H into SAVEf end.
    chunk_to_stk SLOTf. chunk_to_stk SAVEf.
    lazymatch goal with ST0 : stk _ mf lo sp1, STa : stk _ mf sp1 (sp1 + 8), STb : stk _ mf (sp1 + 16) _ |- _ =>
      stk_merge_into ST0 STa; stk_merge_into ST0 SLOTf; stk_merge_into ST0 STb; stk_merge_into ST0 SAVEf;
      replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in ST0 by (clear; lia); exact ST0 end. }
  split; [assumption|].
  split; [exact E4cs|]. split; [exact E4top|]. split; [exact E4stk|]. split; [exact E4flag|].
  split; [exact E4vol|]. split; [exact E4fr|]. split; [exact HKI4|].
  exact HM4.
  Qed.

  Variable slo : Z.
  Hypothesis SSH : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis SLOL : arl_stklo R <= slo.
  Hypothesis SLOH : slo <= bv_unsigned sp - 96.

  #[using="IMG"] Lemma hcs_img_cs_ci : forall hc, img_cs (hcs asegs R HIA hc).
  Proof.
    intros hc. ddestruct IMG as (G & LO & HI & GSB). eapply img_cs_of; [exact LO | exact HI | exact G | exact GSB |].
    intros a n H1 H2 H3 H4. eapply (hcs_img asegs R HIA hc); assumption.
  Qed.

  #[local] Ltac lx_pins_hook ::= idtac.
  Section MX.
  Variable dX : mpd.
  Hypothesis MX : mpd_at asegs m LB dX.
  Hypothesis XP0 : md_own dX = LHeap -> 0 < md_p dX.
  Hypothesis OX : aobj asegs AL CS m (md_addr dX) 16.
  Hypothesis OP : 1 <= md_n dX -> aobj asegs AL CS m (md_p dX) (4 * md_n dX).
  Hypothesis CRX : client_range L (LB ++ fdata LF) lo (md_addr dX) 16.
  Hypothesis INZ : md_own dX = LStatic -> img_norz (md_p dX) (4 * md_n dX) = true.
  Hypothesis XS : md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX.
  Hypothesis PS : 1 <= md_n dX -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX.

  Lemma ci_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      HM asegs R HIA h LB LF m -> stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      evtA asegs AL CS
        (mpi_cmp_int_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
           (Z.sgn (mpd_val dX - z)) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 z) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_MPI_CMP_INT_E) fc None m (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH ST MI.
    pose proof CMP as CMPc.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO TOP HTOP; lia]).
    eapply evtA_cut.
    { eapply pro_walk; eassumption. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & y0 & y1 & y2 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & w0 & w1 & w2 & padw
                    & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & LMB & FSHX
                    & SAVE & SLOT & YC & STA & STB & STlo & MI1 & PRES0).
    subst ms1.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV; lia).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS).
    change (64 / 8) with 8 in SBND, APS.
    pose proof (art_stk_high asegs R HIA) as STKH.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0) as HP01.
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HP01) as HPX01.
    assert (TOPCS : forall x, CS x -> x < hstkhi asegs R HIA h) by (intros x Hx; eapply hcs_below_top; exact Hx).
    pose proof (presA_sshad asegs R _ _ _ _ _ _ m m1 slo (bv_unsigned sp) HP01 SSH SLOL ltac:(clear - TOP HTOP; lia)) as SSH1.
    assert (OY1 : aobj asegs AL CS m1 (sp1 + 16) 16).
    { refine (aobj_of_sshad_ci AL CS m1 slo (bv_unsigned sp) (sp1 + 16) 1 CSOK SSH1 _ _ _ _ _).
      - clear - SLOH SP1. lia.
      - cbn. clear - SP1. lia.
      - clear - SP1M. Z.div_mod_to_equations. lia.
      - clear - SP1R. lia.
      - eapply crange_sub; [exact SCS0| clear - SP1 SLO LOS; lia| cbn; clear - SP1 TOP HTOP; lia]. }
    assert (OQ1 : aobj asegs AL CS m1 (FB + 32) 4).
    { eapply (aobj_of_partial_ci asegs AL CS m1 FB _ (FB + 32) 4%nat 4);
        [exact CSOK| exact FSHX| eapply crange_sub; [exact CFB| clear; lia| clear; lia]| exact F8| clear - F0; lia| clear; lia| clear; lia| reflexivity]. }
    pose proof MX as MX0.
    flat constr:(MX0) 2%nat. intros FLt1 SGX. flat constr:(FLt1) 6%nat. flclear FLt1. intros CX0 XAL X0 LENX NRX OWNX.
    pose proof (rw_cells_bound _ _ _ _ CX0) as XB. unfold mpi_cells in XB. cbn [cells_size csize Nat.add] in XB.
    assert (CRXs : client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_addr dX) 16).
    { intros a Ha. destruct (CRX a Ha) as [C|[C|C]]; [| right; left; exact C| right; right; exact C]. left. clear - C Ha XS. lia. }
    assert (CRXL : md_own dX = LHeap -> client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_p dX) (4 * md_n dX)).
    { intros EO. rewrite EO in OWNX. flat constr:(OWNX) 3%nat. flclear OWNX. intros N1 XIN _.
      eapply client_range_block; [apply in_app_iff; left; exact XIN| clear; lia| clear - N1; lia]. }
    set (LBy := (FB + 32, 4) :: LB).
    assert (MX1 : mpd_at asegs m1 LBy dX).
    { eapply (mpd_at_heap_presx asegs L); [exact MX| exact HPX01| exact MI| exact MI1| exact CRXs| exact CRXL| exact I| intros _; exact I| ].
      intros b' Hb. unfold mpd_blk in Hb. destruct (md_own dX) eqn:EO; try (destruct Hb; fail).
      destruct Hb as [<-|[]]. right. try rewrite EO in OWNX. flat constr:(OWNX) 3%nat. flclear OWNX. intros _ XIN _. exact XIN. }
    set (dY := mkMPD (sp1 + 16) (sgn_of z) 1 (FB + 32) [Z_to_bv 64 (abs_limb_expr z)] padw LHeap).
    assert (MY1 : mpd_at asegs m1 LBy dY).
    { unfold mpd_at, mpi_at, dY. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own length].
      split; [| apply sgn_of_cases].
      split; [unfold mpi_cells; exact YC|].
      split; [clear - SP1M; Z.div_mod_to_equations; lia|].
      split; [clear - SP1 SB64 SLO LOS STKH; lia|].
      split; [reflexivity|].
      split; [unfold MPI_MAX_LIMBS; clear; lia|].
      split; [clear; lia|]. split; [left; reflexivity|]. split; [clear - F64; Z.div_mod_to_equations; lia|].
      eapply (u32arr_of_cells _ _ _ 4 (le4 (Z_to_bv 64 (abs_limb_expr z)))); [eapply rw_cells_reshape; [exact LMB| cbn; split; [apply (length_le4 (Z_to_bv 64 (abs_limb_expr z)))| exact I]| cbn; rewrite ?app_nil_r; reflexivity]| cbn; rewrite ?app_nil_r; reflexivity].
    }
    assert (OX1 : aobj asegs AL CS m1 (md_addr dX) 16)
      by (eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OX| exact CRXs| clear - LOS SLO; lia| exact TOPCS]).
    assert (OP1 : 1 <= md_n dX -> aobj asegs AL CS m1 (md_p dX) (4 * md_n dX)).
    { intros N1. destruct (md_own dX) eqn:EO.
      - try rewrite EO in OWNX. destruct OWNX as [_ N0]. exfalso. clear - N0 N1. lia.
      - rewrite <- Ehcs. eapply (hm_aobj_block asegs R HIA h1 LB ((FB, 64) :: LF) m1); [exact HH1|].
        try rewrite EO in OWNX. flat constr:(OWNX) 3%nat. flclear OWNX. intros _ XIN _. exact XIN.
      - eapply (aobj_img asegs AL); [apply hcs_img_cs_ci| eapply (hm_img_shadow asegs R HIA); exact HH1| apply INZ; first [exact EO | reflexivity]]. }
    assert (EVY : mpd_val dY = z).
    { unfold mpd_val, dY. cbn [md_sg md_limbs limbs_val].
      pose proof (abs_limb_val z BZ) as AV. unfold w32 in AV.
      rewrite Z.mul_0_r, Z.add_0_r, AV. apply sgn_of_abs. }
    eapply evtA_cut.
    { unfold mpi_cmp_mpi_stmtA in CMPc.
      eapply (CMPc CS) with (LB := LBy) (dX := dX) (dY := dY) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact MX1 | exact MY1 | exact XP0 | exact MI1 | exact CSOK | exact OX1 | exact OP1 | exact STlo | reflexivity
              | exact (art_alwf asegs R HIA)
              | exact (hm_abase asegs R HIA h1 LB _ m1 HH1)
              | exact OY1
              | (intros _; exact OQ1)
              | (intros _; unfold dY; cbn [md_p]; clear - F0; lia)
              | (clear - LOS ALO ACP; lia)
              | (clear - SLO SP1; lia)
              | (clear - SP1M; Z.div_mod_to_equations; lia)
              | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
              | (destruct XS as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (right; unfold dY; cbn [md_addr]; clear; lia)
              | (intros N1; destruct (PS N1) as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (intros _; left; unfold dY; cbn [md_p md_n]; clear - FBLO; lia)
              | match goal with |- ?g => idtac "CMPPRE-LEFT:" g end ]. }
    rewrite EVY. clear MX1 MY1 OX1 OP1.
    cbv beta. intros ms2 PO. unfold mpi_cmp_postA in PO.
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 A_CI_RET)) with (Z_to_bv 64 A_CI_RET : word)
      by (symmetry; apply ret_pc_even; [unfold A_CI_RET; clear; lia| reflexivity]).
    assert (HH2 : HM asegs R HIA h1 LB ((FB, 64) :: LF) m2).
    { eapply hm_munch; [exact HH1| exact MU2| exact WM2|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite Ehtop. clear - Ha LOS SP1 TOP. lia. }
    assert (PRES2 : presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m2).
    { eapply presW_munch; [exact PRES0| exact MU2| exact WM2| |].
      - unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]| apply Forall_nil].
      - apply Forall_cons; [cbn [fst snd]; eapply wcover_of_wlow; [exact WL| clear - ALO LOS; lia| clear - SP1; lia]| apply Forall_nil]. }
    pose proof (presW_hmono R HIA h h1 LB LF _ _ _ m m2 PRES2 ltac:(intros x Hx; rewrite Ehcs; exact Hx) Estk) as PRES2h.
    clear HH1 PRES0 HP01 HPX01 OY1 OQ1 SSH1 STlo.
    chunk_to_stk YC. stk_merge_into YC STB.
    transport_after_call asegs m1 m2 MU2 WM2.
    eapply evtA_cut.
    { eapply (evtA_cs_mono asegs AL (hcs asegs R HIA h1)); [| intros x Hx; rewrite Ehcs in Hx; exact Hx].
      eapply (epi_walk h1 m m2 FB sp1);
        first [ exact HH2 | exact Ehcs | exact Ehtop | exact Estk | exact SP1 | exact SP1M | exact F64 | exact FRSH
              | exact FHD | exact FSHX | exact SAVE | exact SLOT | exact STA | exact YC | exact ST2 | exact MI2 | exact PRES2h
              | match goal with |- ?g => idtac "EPIPRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply evtA_done. unfold mpi_cmp_int_postA.
    do 14 eexists. exists m9, h4.
    split; [reflexivity|].
    split; [exact MI9|]. split; [exact ST9|].
    split; [pose proof (presW_presA asegs R HIA h1 _ LF _ _ _ _ _ PRES9) as HPF; rewrite Estk in HPF; exact HPF|].
    split; [rewrite E4cs; exact Ehcs|]. split; [rewrite E4top; exact Ehtop|]. split; [rewrite E4stk; exact Estk|].
    split; [rewrite E4flag; exact Eflag|]. split; [rewrite E4vol; exact Evol|]. split; [rewrite E4fr; exact Efr|].
    split; [intros mo; rewrite HKI4; apply HKI|].
    exact HH4.
  Qed.
  End MX.

  Section MZ.
  Variables (X P : Z) (sw pad : word).
  Hypothesis CXz : rw_cells asegs m X [C8 (Z_to_bv 64 P); C2 sw; C2 (Z_to_bv 64 0); C4 pad].
  Hypothesis XALz : X mod 8 = 0.
  Hypothesis X0z : 0 < X.
  Hypothesis OXz : aobj asegs AL CS m X 16.
  Hypothesis CRXz : client_range L (LB ++ fdata LF) lo X 16.
  Hypothesis XSz : X + 16 <= lo \/ bv_unsigned sp <= X.
  Hypothesis Z0 : z = 0.
  Hypothesis CMPZ : mpi_cmp_mpi_zz_stmtA asegs AL A_MPI_CMP_MPI_E.

  Lemma ci_main_z0 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      HM asegs R HIA h LB LF m -> stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      evtA asegs AL CS
        (mpi_cmp_int_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 z) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_MPI_CMP_INT_E) fc None m (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH ST MI.
    pose proof CMPZ as CMPc.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO TOP HTOP; lia]).
    eapply evtA_cut.
    { eapply pro_walk; eassumption. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & y0 & y1 & y2 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & w0 & w1 & w2 & padw
                    & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & LMB & FSHX
                    & SAVE & SLOT & YC & STA & STB & STlo & MI1 & PRES0).
    subst ms1.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV; lia).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS).
    change (64 / 8) with 8 in SBND, APS.
    pose proof (art_stk_high asegs R HIA) as STKH.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0) as HP01.
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HP01) as HPX01.
    assert (TOPCS : forall x, CS x -> x < hstkhi asegs R HIA h) by (intros x Hx; eapply hcs_below_top; exact Hx).
    pose proof (presA_sshad asegs R _ _ _ _ _ _ m m1 slo (bv_unsigned sp) HP01 SSH SLOL ltac:(clear - TOP HTOP; lia)) as SSH1.
    assert (OY1 : aobj asegs AL CS m1 (sp1 + 16) 16).
    { refine (aobj_of_sshad_ci AL CS m1 slo (bv_unsigned sp) (sp1 + 16) 1 CSOK SSH1 _ _ _ _ _).
      - clear - SLOH SP1. lia.
      - cbn. clear - SP1. lia.
      - clear - SP1M. Z.div_mod_to_equations. lia.
      - clear - SP1R. lia.
      - eapply crange_sub; [exact SCS0| clear - SP1 SLO LOS; lia| cbn; clear - SP1 TOP HTOP; lia]. }
    assert (OQ1 : aobj asegs AL CS m1 (FB + 32) 4).
    { eapply (aobj_of_partial_ci asegs AL CS m1 FB _ (FB + 32) 4%nat 4);
        [exact CSOK| exact FSHX| eapply crange_sub; [exact CFB| clear; lia| clear; lia]| exact F8| clear - F0; lia| clear; lia| clear; lia| reflexivity]. }
    pose proof (rw_cells_bound _ _ _ _ CXz) as XB. cbn [cells_size csize Nat.add] in XB.
    assert (CRXs : client_range L (LB ++ fdata LF) (bv_unsigned sp) X 16).
    { intros a Ha. destruct (CRXz a Ha) as [C|[C|C]]; [| right; left; exact C| right; right; exact C]. left. clear - C Ha XSz. lia. }
    assert (CX1 : rw_cells asegs m1 X [C8 (Z_to_bv 64 P); C2 sw; C2 (Z_to_bv 64 0); C4 pad]).
    { eapply (presA_rw_cells asegs R); [exact HP01| exact CXz| first [exact CRXs | (cbn; exact CRXs)]| exact I]. }
    assert (OX1 : aobj asegs AL CS m1 X 16)
      by (eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OXz| exact CRXs| clear - LOS SLO; lia| exact TOPCS]).
    assert (BQ : bytes_at asegs m1 (FB + 32) (u32s [Z_to_bv 64 (abs_limb_expr z)])).
    { assert (UQ : u32arr asegs m1 (FB + 32) [Z_to_bv 64 (abs_limb_expr z)]).
      {
      eapply (u32arr_of_cells _ _ _ 4 (le4 (Z_to_bv 64 (abs_limb_expr z)))); [eapply rw_cells_reshape; [exact LMB| cbn; split; [apply (length_le4 (Z_to_bv 64 (abs_limb_expr z)))| exact I]| cbn; rewrite ?app_nil_r; reflexivity]| cbn; rewrite ?app_nil_r; reflexivity].
      }
      exact (proj1 UQ). }
    assert (LV : lval [Z_to_bv 64 (abs_limb_expr z)] 1 = 0).
    { unfold lval. change (Z.to_nat 1) with 1%nat. cbn [firstn limbs_val].
      pose proof (abs_limb_val z BZ) as AV. unfold w32 in AV.
      rewrite Z.mul_0_r, Z.add_0_r, AV, Z0. reflexivity. }
    eapply evtA_cut.
    { unfold mpi_cmp_mpi_zz_stmtA in CMPc.
      eapply (CMPc CS) with (X := X) (P := P) (sw := sw) (pad := pad) (Y := sp1 + 16) (Q := FB + 32) (n' := 1)
        (sg' := sgn_of z) (ys := [Z_to_bv 64 (abs_limb_expr z)]) (pad' := padw) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact CX1 | exact XALz | exact X0z | exact YC | exact BQ | reflexivity | exact LV | exact MI1 | exact CSOK
              | exact OX1 | exact OY1 | exact STlo
              | exact (art_alwf asegs R HIA)
              | exact (hm_abase asegs R HIA h1 LB _ m1 HH1)
              | (intros _; exact OQ1)
              | (clear; lia)
              | (right; split; [clear - F0; lia| clear - F8; Z.div_mod_to_equations; lia])
              | (clear - SP1M; Z.div_mod_to_equations; lia)
              | (clear - SP1 SB64 SLO LOS STKH; lia)
              | (clear - LOS ALO ACP; lia)
              | (clear - SLO SP1; lia)
              | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
              | (destruct XSz as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (right; clear; lia)
              | (intros _; left; clear - FBLO; lia)
              | match goal with |- ?g => idtac "CMPZPRE-LEFT:" g end ]. }
    clear CX1 OX1 BQ LV.
    cbv beta. intros ms2 PO. unfold mpi_cmp_postA in PO.
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    rewrite ?(unsigned_lit sp1) in MU2, ST2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 A_CI_RET)) with (Z_to_bv 64 A_CI_RET : word)
      by (symmetry; apply ret_pc_even; [unfold A_CI_RET; clear; lia| reflexivity]).
    assert (HH2 : HM asegs R HIA h1 LB ((FB, 64) :: LF) m2).
    { eapply hm_munch; [exact HH1| exact MU2| exact WM2|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite Ehtop. clear - Ha LOS SP1 TOP. lia. }
    assert (PRES2 : presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m2).
    { eapply presW_munch; [exact PRES0| exact MU2| exact WM2| |].
      - unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]| apply Forall_nil].
      - apply Forall_cons; [cbn [fst snd]; eapply wcover_of_wlow; [exact WL| clear - ALO LOS; lia| clear - SP1; lia]| apply Forall_nil]. }
    pose proof (presW_hmono R HIA h h1 LB LF _ _ _ m m2 PRES2 ltac:(intros x Hx; rewrite Ehcs; exact Hx) Estk) as PRES2h.
    clear HH1 PRES0 HP01 HPX01 OY1 OQ1 SSH1 STlo.
    chunk_to_stk YC. stk_merge_into YC STB.
    transport_after_call asegs m1 m2 MU2 WM2.
    eapply evtA_cut.
    { eapply (evtA_cs_mono asegs AL (hcs asegs R HIA h1)); [| intros x Hx; rewrite Ehcs in Hx; exact Hx].
      eapply (epi_walk h1 m m2 FB sp1);
        first [ exact HH2 | exact Ehcs | exact Ehtop | exact Estk | exact SP1 | exact SP1M | exact F64 | exact FRSH
              | exact FHD | exact FSHX | exact SAVE | exact SLOT | exact STA | exact YC | exact ST2 | exact MI2 | exact PRES2h
              | match goal with |- ?g => idtac "EPIPRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply evtA_done. unfold mpi_cmp_int_postA.
    do 14 eexists. exists m9, h4.
    split; [reflexivity|].
    split; [exact MI9|]. split; [exact ST9|].
    split; [pose proof (presW_presA asegs R HIA h1 _ LF _ _ _ _ _ PRES9) as HPF; rewrite Estk in HPF; exact HPF|].
    split; [rewrite E4cs; exact Ehcs|]. split; [rewrite E4top; exact Ehtop|]. split; [rewrite E4stk; exact Estk|].
    split; [rewrite E4flag; exact Eflag|]. split; [rewrite E4vol; exact Evol|]. split; [rewrite E4fr; exact Efr|].
    split; [intros mo; rewrite HKI4; apply HKI|].
    exact HH4.
  Qed.
  End MZ.

  End Call.
End WalkC.

Theorem A_mpi_cmp_int_spec : forall (R : art_layout) (HIA : artA asegs R),
    asan_img_ok (arl_AL R) -> arl_uar_got R = A_UAR_GOT_CI -> arl_smalloc R 0 = A_SMALLOC_0_CI ->
    0 <= arl_need_smalloc R ->
    mpi_cmp_int_stmtA asegs R HIA A_MPI_CMP_INT_E.
Proof.
  intros R HIA IMG UARG SM0 NS. unfold mpi_cmp_int_stmtA.
  intros h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    dX z lo slo HH LFB MX XP0 BZ MI OX OP CRX INZ ST LOS SLO SLOS TOP SPA TPV SSH SLOL SLOH XS PS -> ->.
  pose proof (A_mpi_cmp_mpi_spec (arl_AL R) IMG) as CMP.
  eapply ci_main; eassumption.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Qed.

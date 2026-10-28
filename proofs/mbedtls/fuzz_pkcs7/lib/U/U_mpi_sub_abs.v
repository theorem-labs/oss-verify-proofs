(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout U_string U_platform_zeroize U_mpi_addsub U_mpi_sub_abs_C U_mpi_sub_abs_B U_mpi_free U_mpi_cmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_sub_abs () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_sub_abs_C.sub_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_cmp.SIGF"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_NEGATIVE_VALUE"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.U.U_layout.U_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"].

Local Ltac no_vars z := match z with | context [?v] => is_var v; fail 1 | _ => idtac end.
Local Ltac chk_lia K :=
  exfalso;
  repeat match type of K with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in K by lia end;
  revert K;
  repeat match goal with
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
    end;
  cbn [Z.b2z]; intros K;
  repeat match type of K with context [bv_unsigned (Z_to_bv 64 ?z)] =>
    no_vars z; let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in change (bv_unsigned (Z_to_bv 64 z)) with v in K end;
  repeat match type of K with context [Z.lxor ?x ?y] =>
    no_vars x; no_vars y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v in K end;
  lia.
Local Ltac chk K := first [ chk_lia K | (rewrite ?unsigned_lit in K by lia; lxu_pnull K) ].
Local Ltac unlit_goal :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.
Local Ltac land_chk H :=
  lazymatch goal with
  | |- context [Z.land ?p 7] => let E := fresh "E" in
      assert (E : Z.land p 7 = 0) by (rewrite lxu_land7; unlit_goal; clear - H; Z.div_mod_to_equations; lia);
      rewrite E; clear E
  | |- context [Z.land ?p 3] => let E := fresh "E" in
      assert (E : Z.land p 3 = 0) by (rewrite lxu_land3; unlit_goal; clear - H; Z.div_mod_to_equations; lia);
      rewrite E; clear E
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sub_front_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (X Aa Ba nA nB lo : Z) (zs : list word) : machine_state -> Prop := fun ms' : machine_state => exists (m1 : mem) (n : Z),
    munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\
    rw_cells usegs m1 (bv_unsigned sp - 64) (sub_frame ra s0 s1 s2 s3 s4 s5 s6) /\
    stk usegs m1 lo (bv_unsigned sp - 64) /\ SIGF zs nB n /\
    ((exists raj t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word, n <= nA /\
        ms' = MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 n) a0
                   (Z_to_bv 64 Aa) (Z_to_bv 64 Ba) a3 a4 a5 a6 a7 (Z_to_bv 64 nA) s3 (Z_to_bv 64 (4 * n)) s5 s6
                   s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20830) fc None m1 (seg_rom usegs))
     \/ (exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word, nA < n /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 MBEDTLS_ERR_MPI_NEGATIVE_VALUE) a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m1 (seg_rom usegs)))
(* [comment removed for export] *).

Section Front.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (X Aa Ba pA pB nA nB lo : Z) (sAw sBw padA padB : word) (zs : list word).
  Hypothesis CA : rw_cells usegs m Aa [C8 (Z_to_bv 64 pA); C2 sAw; C2 (Z_to_bv 64 nA); C4 padA].
  Hypothesis CB : rw_cells usegs m Ba [C8 (Z_to_bv 64 pB); C2 sBw; C2 (Z_to_bv 64 nB); C4 padB].
  Hypothesis BV : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs ()) "P,(15.+1.VnB,)(5.(20.$>.Vm,VpB,(21.Vzs,))(5.(1=.=VpB,)(5.(16.$4.(22.VpB,+4.)=)(14.(15.(1:.VpB,(23.+4.VnB,))Vlo,)(15.(;.&40.Vsp,)VpB,)))))")
(* [comment removed for export] *).
  Hypothesis LENB : Z.of_nat (length zs) = nB.
  Hypothesis NRA : 0 <= nA <= 10000.
  Hypothesis NRB : 0 <= nB <= 10000.
  Hypothesis AB : 0 < Aa /\ Aa + 16 <= 2^64.
  Hypothesis BB : 0 < Ba /\ Ba + 16 <= 2^64.
  Hypothesis AAL : Aa mod 8 = 0.
  Hypothesis BAL : Ba mod 8 = 0.
  Hypothesis AS : Aa + 16 <= lo \/ bv_unsigned sp <= Aa.
  Hypothesis BS : Ba + 16 <= lo \/ bv_unsigned sp <= Ba.
  Hypothesis ST : stk usegs m lo (bv_unsigned sp).
  Hypothesis SLO : lo <= bv_unsigned sp - 64.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis MI : mem_inv usegs m.

  Let FQ := sub_front_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m X Aa Ba nA nB lo zs.

  (* [comment removed for export] *)
  #[using="pB BV AB BB AAL NRA NRB SLO LO0"] Lemma front_tail : forall (mz : mem) (n : Z) (t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    munch [(bv_unsigned sp - 64, bv_unsigned sp)] m mz -> wmono usegs m mz -> mem_inv usegs mz ->
    rw_cells usegs mz (bv_unsigned sp - 64) (sub_frame ra s0 s1 s2 s3 s4 s5 s6) ->
    stk usegs mz lo (bv_unsigned sp - 64) ->
    rw_cells usegs mz Aa [C8 (Z_to_bv 64 pA); C2 sAw; C2 (Z_to_bv 64 nA); C4 padA] ->
    SIGF zs nB n ->
    evt usegs FQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 n) a0
                        (Z_to_bv 64 Aa) (Z_to_bv 64 Ba) a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (4 * n)) s5 s6
                        s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20818) fc None mz (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros MU WM MIz FRz STz CAz SB. dpose SB as (SB1 & SB2 & SB3).
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    zstep; if_cases KA; zify_cond KA; [clear - KA AB; chk KA|].
    zstep. land_chk AAL. zstep. if_false.
    zstep. rewrite zx16_small by (clear - NRA; lia). zstep.
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - SB1 NRA NRB; lia).
    - (* [comment removed for export] *)
      unfold sub_frame in FRz.
      call sub_epilogue; [exact FRz| exact MIz| clear - SLO LO0; lia|].
      apply evt_done. unfold FQ, sub_front_post. dexists mz, n.
      split; [exact MU|]. split; [exact WM|]. split; [exact MIz|]. split; [exact FRz|]. split; [exact STz|]. split; [exact SB|].
      right. deexists 14. split; [clear - K0; lia| reflexivity].
    - apply evt_done. unfold FQ, sub_front_post. dexists mz, n.
      split; [exact MU|]. split; [exact WM|]. split; [exact MIz|]. split; [exact FRz|]. split; [exact STz|]. split; [exact SB|].
      left. deexists 14. split; [clear - K0; lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="pB BV AB BB AAL LENB NRA NRB SLO LO0"] Lemma front_loop : forall (mz : mem) (k : nat) (r : Z) (w9 w20 wa0 wa3 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    munch [(bv_unsigned sp - 64, bv_unsigned sp)] m mz -> wmono usegs m mz -> mem_inv usegs mz ->
    rw_cells usegs mz (bv_unsigned sp - 64) (sub_frame ra s0 s1 s2 s3 s4 s5 s6) ->
    stk usegs mz lo (bv_unsigned sp - 64) ->
    rw_cells usegs mz Aa [C8 (Z_to_bv 64 pA); C2 sAw; C2 (Z_to_bv 64 nA); C4 padA] ->
    rw_cells usegs mz Ba [C8 (Z_to_bv 64 pB); C2 sBw; C2 (Z_to_bv 64 nB); C4 padB] ->
    (1 <= nB -> bytes_at usegs mz pB (u32s zs) /\ 0 < pB /\ pB mod 4 = 0) ->
    Z.to_nat r = k -> 0 <= r <= nB -> lval zs nB = lval zs r ->
    wa0 = Z_to_bv 64 (4 * r) -> wa3 = Z_to_bv 64 r ->
    evt usegs FQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 X) w9 wa0
                        (Z_to_bv 64 Aa) (Z_to_bv 64 Ba) wa3 a4 a5 a6 a7 s2 s3 w20 s5 s6
                        s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x207c8) fc None mz (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros mz k. induction k as [|k IH]; intros r w9 w20 wa0 wa3 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 MU WM MIz FRz STz CAz CBz BZI Hk Hr INV -> ->.
    all: pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB.
    all: zstep; zstep; zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - Hr NRB; lia).
    - eapply (front_tail mz r); try eassumption. split; [clear - Hr; lia|]. split; [exact INV| left; clear - K0; lia].
    - exfalso. clear - Hk Hr K0. lia.
    - eapply (front_tail mz r); try eassumption. split; [clear - Hr; lia|]. split; [exact INV| left; clear - K0; lia].
    - assert (R1 : 1 <= r) by (clear - Hr K0; lia).
      destruct (BZI ltac:(clear - Hr R1; lia)) as (BZ & PB0 & PBAL).
      pose proof (u32ro_bound _ _ _ _ BZ) as PBB. rewrite LENB in PBB.
      pose proof (rw_cells_bound _ _ _ _ CAz) as ABND. cbn [cells_size csize Nat.add] in ABND.
      destruct (nth_error zs (Z.to_nat (r - 1))) as [wz|] eqn:NZ; [| apply nth_error_None in NZ; exfalso; clear - NZ Hr R1 LENB; lia].
      zstep. zstep. zstep.
      zstep; if_cases K1; zify_cond K1; [clear - K1 PB0 PBB Hr R1; chk K1|].
      zstep. zstep. zstep. zstep; if_cases K2; zify_cond K2; [clear - K2 PB0 PBB Hr R1; chk K2|].
      zstep; if_cases K3; zify_cond K3; [clear - K3 PB0 PBB; chk K3|].
      zstep. zstep. zstep. land_chk PBAL. zstep. if_false.
      pose proof (u32ro_read usegs mz pB zs (r - 1) wz _ BZ NZ ltac:(clear - R1; lia) eq_refl) as RDZ.
      zstep. clear RDZ. pose proof (limb32_of_read zs r wz NZ) as LZr.
      pose proof (Z.mod_pos_bound (bv_unsigned wz) (2^32) ltac:(clear; lia)) as Bz.
      zstep. zstep. zstep. if_cases K4; zify_cond K4; rewrite ?bv_unsigned_sx32 in K4.
      + apply (proj1 (sxz_zero_iff _ Bz)) in K4.
        eapply (IH (r - 1)); try eassumption.
        all: first [ (clear - Hk; lia) | (clear - Hr R1; lia) | (f_equal; clear; lia)
                   | (rewrite INV; apply lval_drop_zero; [clear - R1; lia| rewrite LZr; exact K4]) ].
      + (* [comment removed for export] *)
        assert (NZL : limb32 zs (Z.to_nat (r - 1)) <> 0) by (rewrite LZr; intros E; apply K4; rewrite E; reflexivity).
        eapply (front_tail mz r); try eassumption. split; [clear - Hr; lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [clear - R1; lia| exact NZL].
  Qed.

  #[using="pA pB sAw sBw padA padB CA CB BV LENB NRA NRB AB BB AAL BAL AS BS ST SLO LO0 MI"] Lemma sub_front_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)(28.$>.VFQ,(17.(18.Vra,Vsp,Vgp,Vtp,R<.R;.R:.Vs0,Vs1,(19.&40.VX,)(19.&40.VAa,)(19.&40.VBa,)R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(19.&40.+2078<.)Vfc,(1;.(2.&40.))Vm,(1<.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (rw_cells_bound _ _ _ _ CB) as BBND. cbn [cells_size csize Nat.add] in BBND.
    destruct (Z.le_gt_cases 1 nB) as [NB1|NB1]; [ddestruct (BV NB1) as (BZ & PB0 & PBAL & PBS)|].
    all: carve_frame 64%nat ST.
    all: do 9 zstep.
    all: replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in * by (clear; lia).
    all: zstep; if_cases K0; zify_cond K0; [clear - K0 BB; chk K0|].
    all: zstep; zstep; land_chk BAL; zstep; if_false.
    all: zstep; rewrite zx16_small by (clear - NRB; lia); zstep.
    all: rewrite ?Z.shiftl_mul_pow2 by (clear; lia); try change (2 ^ 2) with 4.
    all: eapply (front_loop _ (Z.to_nat nB) nB); try eassumption; try reflexivity.
    all: first [ (clear - NRB; lia) | (f_equal; clear; lia)
               | (intros _; split; [eassumption| split; assumption])
               | (intros H1; exfalso; clear - H1 NB1; lia) ].
  Qed.
End Front.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma U_layout_roimg : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs ()) "Psp0,(2.&40.)Pa,$4.P,(16.$2<.(2=.$>.(2>.R1.))$2?.)P,(5.(15.=R2.)(1=.R2.(30.+2.+40.)))(5.(15.(31.(32.R4.))R3.)(1=.R3.(33.(32.R4.))))")
(* [comment removed for export] *).
Proof.
  intros sp0 a H Ha. unfold ro_addr in H. unfold wa in H. rewrite unsigned_lit in H by lia.
  cbn -[Z.leb Z.add andb negb] in H.
  repeat match type of H with context [if ?c then _ else _] => destruct c eqn:?E end;
    rewrite ?Bool.andb_true_iff, ?Bool.andb_false_iff, ?Z.leb_le, ?Z.leb_gt in *; cbn in *; try discriminate; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Spec.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem U_mpi_sub_abs_spec_o : forall MSF, MSF = U_MEMSET_FUNC -> mpi_sub_abs_stmt' usegs L HI U_MPI_SUB_ABS MSF.
  Proof.
    intros MSF MSFE. unfold mpi_sub_abs_stmt', mpi_binop_stmt', U_MPI_SUB_ABS. intros until lo.
    intros HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    destruct (opnd_raw _ _ _ _ _ MA ltac:(intros EO; pose proof (opnd_view _ _ _ _ _ MA) as [(_ & _ & _ & _ & _ & OW) _]; rewrite EO in OW; ddestruct OW as (_ & IN & _);
               pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (R0 & _); exact R0)) as (CA0 & ABY & LENA & NRA & SGA & ABA & PBA).
    destruct (opnd_raw _ _ _ _ _ MB ltac:(intros EO; pose proof (opnd_view _ _ _ _ _ MB) as [(_ & _ & _ & _ & _ & OW) _]; rewrite EO in OW; ddestruct OW as (_ & IN & _);
               pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (R0 & _); exact R0)) as (CB0 & BBY & LENB & NRB & SGB & ABB & PBB).
    pose proof (opnd_view _ _ _ _ _ MA) as [(_ & AAL & A0 & _) _]. pose proof (opnd_view _ _ _ _ _ MB) as [(_ & BAL & B0 & _) _].
    pose proof (conj A0 (proj2 ABA)) as ABx. pose proof (conj B0 (proj2 ABB)) as BBx.
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    dpose XW as (XCW & XD & XP).
    pose proof (client_wrange_where L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as XS.
    eapply aevtM_cut_evt; [exact MK| |].
    { eapply (sub_front_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (md_addr dX) (md_addr dA) (md_addr dB)
                (md_p dA) (md_p dB) (md_n dA) (md_n dB) lo (Z_to_bv 64 (md_sg dA)) (Z_to_bv 64 (md_sg dB)) (md_pad dA) (md_pad dB) (md_limbs dB));
        try eassumption.
      - intros H1. split; [exact BBY|]. destruct PBB as [Z0|[P0 PAL]]; [exfalso; clear - Z0 H1; lia|]. split; [exact P0|]. split; [exact PAL|].
        apply OB5. pose proof (opnd_view _ _ _ _ _ MB) as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dB); [destruct OW; exfalso; clear - H1 H0; lia| discriminate| discriminate].
      - clear - SLO HLS. lia.
      - clear - ACL ACP. lia. }
    cbv beta. intros ms' FQ. unfold sub_front_post in FQ.
    ddestruct FQ as (m1 & n & MU1 & WM1 & MI1 & FR1 & ST1 & SB & CASES).
    (* [comment removed for export] *)
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact ACL| exact MU1| exact WM1|].
      intros a Ha NO. cbn in NO. left. clear - NO HTOP SLO HLS. lia. }
    assert (SOK1 : statics_ok usegs L m1).
    { eapply statics_ok_munch; [exact SOK| exact MU1|]. intros a Hd NW. cbn. split; [clear - Hd DHI ACL SLO HLS; lia| exact I]. }
    assert (HPX1 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m1).
    { eapply heap_presx_of_munch; [exact MU1| exact WM1|]. intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [C|[[C1 C2]|([q k] & Hq & R)]]; [clear - C; lia| clear - C1 DHI ACL SLO HLS; lia|]. cbn in R.
      pose proof (proj1 (Forall_forall _ _) HBR _ Hq) as (_ & _ & _ & R3 & _). cbn in R3. clear - R R3 ACL SLO HLS. lia. }
    assert (OPM : forall d, mpd_at usegs m LB d -> (md_addr d + 16 <= lo \/ bv_unsigned sp <= md_addr d) ->
                  (md_own d <> LNull -> md_p d + 4 * md_n d <= lo \/ bv_unsigned sp <= md_p d) -> mpd_at usegs m1 LB d).
    { intros d Md D1 D2. eapply mpd_at_munch_any; [exact Md| exact MU1| exact WM1| cbn; split; [clear - D1 SLO HLS; lia| exact I]|].
      intros ON. cbn. split; [destruct (D2 ON); clear - H SLO HLS; lia| exact I]. }
    pose proof (OPM _ MX XS XLS) as MX1.
    assert (OPM' : forall d, opnd_at usegs m LB (bv_unsigned sp) d -> (md_addr d + 16 <= lo \/ bv_unsigned sp <= md_addr d) ->
                  (md_own d <> LNull -> md_p d + 4 * md_n d <= lo \/ bv_unsigned sp <= md_p d) -> opnd_at usegs m1 LB (bv_unsigned sp) d).
    { intros d Md D1 D2. eapply opnd_at_munch_any; [exact Md| exact MU1| exact WM1| cbn; split; [clear - D1 SLO HLS; lia| exact I]|].
      intros ON. cbn. split; [destruct (D2 ON); clear - H SLO HLS; lia| exact I]. }
    pose proof (OPM' _ MA OA4 OA5) as MA1. pose proof (OPM' _ MB OB4 OB5) as MB1.
    destruct CASES as [(raj & t0' & t1' & t2' & a0' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & NLE & ->)
                      |(t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & NGT & ->)].
    - (* [comment removed for export] *)
      eapply (sub_J1_proof L HI); try eassumption.
      intros n'. eapply (sub_C1_proof L HI); eassumption.
    - (* [comment removed for export] *)
      apply aevtM_done. unfold mpi_binop_post. deexists 14. dexists m1, mo, h, LB, dX, MBEDTLS_ERR_MPI_NEGATIVE_VALUE.
      split; [reflexivity|]. split; [exact MI1|].
      split; [unfold sub_frame in FR1; release_frame FR1 ST1 (bv_unsigned sp); exact ST1|].
      split; [apply mo_frame_refl|]. split; [reflexivity|]. split; [exact HH1|]. split; [exact MX1|].
      split; [apply mpd_out_refl; exact NST|]. split; [exact HPX1|]. split; [exact SOK1|].
      split; [| split; [reflexivity| split; [reflexivity| split; [intros b Hb; left; exact Hb| reflexivity]]]].
      right; right. split; [reflexivity|].
      dpose SB as (SB1 & SB2 & SB3). destruct SB3 as [Z0|LOW]; [exfalso; clear - Z0 NGT NRA; lia|].
      rewrite !mpd_abs_lval by assumption. rewrite SB2.
      pose proof (lval_range (md_limbs dA) (md_n dA) ltac:(clear - NRA; lia)) as RA. pose proof (pow32_le (md_n dA) (n - 1) ltac:(clear - NRA NGT; lia)) as PW.
      clear - RA PW LOW. lia.
  Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem U_mpi_sub_abs_spec : forall MSF, MSF = U_MEMSET_FUNC -> mpi_sub_abs_stmt usegs L HI U_MPI_SUB_ABS MSF.
  Proof. intros MSF E. apply mpi_binop_stmt_of_prime. exact (U_mpi_sub_abs_spec_o MSF E). Qed.
End Spec.

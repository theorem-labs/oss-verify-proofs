(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import StrFun.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STRW_memset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HA_F_memset () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.Heap.StrFun.filled"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "memset_post"; "RocqVerifyHarness.AgentSubmission.Heap.StrFun.BC8"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"].

Definition rsegs := asegs.

Definition memset_entry := 0x0eadc4%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac with_arr tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
  end.

(* [comment removed for export] *)
Ltac brute256 c Rc :=
  first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
  repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
  revert c Rc; apply brute256_ok; vm_compute; reflexivity.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
  intros x Hx H4.
  transitivity (Z.land (x mod 8) 4).
  { change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
    rewrite <- Z.land_assoc. reflexivity. }
  assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
  destruct R as [R|R]; rewrite R; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HA_F_memset ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1',(2.&40.)(1.(2.&40.)La2',(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O16.O15.O14.O13.R?.R>.R=.O12.O11.O4.R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(8.O16.)O5.(9.(2.&40.))R1.(:.$;.)))(4.(<.(=.(>.$?.$?.)(10.$?.$?.(11.&40.O4.)(12.(11.&40.O4.)(11.&40.O2.)))(13.(>.$?.$?.)))O1.R1.)(4.(14.$;.O1.R1.)(4.(15.$;.R1.)(16.$;.R1.(11.&40.O4.)(=.$17.(18.(19.(11.&40.O2.))(1:.(2.&8.)(1;.&8.(1<.(11.&40.O3.)+100.))(19.(11.&40.O2.))))(13.$17.))))))))))))))))))))))")
(* [comment removed for export] *).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).
  (* [comment removed for export] *)
  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  (* [comment removed for export] *)
  Ltac fin_with cover :=
    zstep;
    with_arr ltac:(fun segs ARR FIL LEN A cb =>
      let E := fresh "E" in
      pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
      rewrite LEN in E; rewrite E in ARR;
      apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
    finish; subst; assumption.
  Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
  Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

  (* [comment removed for export] *)
  Lemma memset_loop : ltac2:(CDefT.buildp (gd_tbl_HA_F_memset ()) "PK,$1=.Pc,$?.Pp,$?.Pr,$?.Pe,$?.Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1>.(2.&8.))PQ,P,$?.SpPx15,(2.&40.)Px16,(2.&40.)P,(5.$1=.(19.R7.)R:.)P,(5.$?.R:.(1<.(11.&40.Va1,)+100.))P,(1?.$;.R7.(11.&40.Va0,)R6.)P,(20.(1;.&8.R<.)R7.R6.)P,(5.$1=.(21.(2.&8.)R8.)(19.(11.&40.Va2,)))P,(15.$;.R:.)P,(<.(=.(>.$?.$?.)(10.$?.$?.(11.&40.Va0,)(12.(11.&40.Va0,)(11.&40.Va2,)))(13.(>.$?.$?.)))Vm,R;.)P,(14.$;.Vm,R<.)P,Pj,$?.P,(22.(4.(23.=R1.)(24.R1.R11.))(4.(23.R?.R1.)(24.R1.(11.&40.Va2,))))A1.R=.R2.P,(23.=R11.)P,(23.+20.R11.)P,(1.$?.Lq,$?.(5.$?.R13.(25.+4.R1.)))P,(23.(12.R14.R13.)(11.&40.Va2,))P,(23.(12.R13.+1<.)(12.R15.R14.))(26.$;.(27.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,Va0,(1;.&40.(12.(11.&40.Va0,)R16.))(1;.&40.(25.R17.$28.))(1;.&40.+1?.)(1;.&40.R15.)R10.R?.Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(1;.&40.+>:>9<.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB.
    induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
      assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    zstep. zstep. zstep.
    if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
      replace (r + -32)%Z with (r - 32)%Z by lia.
      eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
      2:{ exists (q4 - 8)%Z. lia. }
      intros j Hj.
      destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
      destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
      assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
      destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
    - fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
                      destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
  Qed.

  Lemma memset_body : ltac2:(CDefT.buildp (gd_tbl_HA_F_memset ()) "Pjunk,(1>.(2.&8.))P,(16.$;.Vm,(11.&40.Va0,)(=.$17.(18.(19.(11.&40.Va2,))R1.)(13.$17.)))(26.$;.(27.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,Va0,Va1,Va2,Va3,Va4,Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(1;.&40.+>:=<4.)Vfc,(9.(2.&40.))Vm,(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB MI0.
    intros junk DST. pose proof MI0 as MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (zr_word a1) as R1. unfold inr64 in R1.
    remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
    assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { fin. }
    assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
    pose proof (ms_store_ok rsegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
    zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K3; zify_cond K3. { fin. }
    mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K7; zify_cond K7. { fin. }
    mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K9; zify_cond K9. { fin. }
    (* [comment removed for export] *)
    zstep. zstep.
    setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
    zstep. zstep.
    remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
    assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
    { subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
      unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
      change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
      Z.div_mod_to_equations. lia. }
    clear Hk.
    zstep. zstep. zstep. zstep. zstep.
    change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
    remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
    assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
    { split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
    clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
    zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).
    (* [comment removed for export] *)
    mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K9'; zify_cond K9'. { fin. }
    mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep.
    mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K25; zify_cond K25. { fin. }
    mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    (* [comment removed for export] *)
    zstep.
    remember (Z.land (A + k) 4) as k4 eqn:Hk4.
    assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
    { subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
    clear Hk4.
    zstep. zstep. zstep.
    mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K32; zify_cond K32. { fin. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
    zstep.
    replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
    eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
    exists (q4 - Z.div k4 4 - 6)%Z. lia.
  Qed.
End Proofs.

Lemma memset_spec : ltac2:(CDefT.buildp (gd_tbl_HA_F_memset ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(29.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pjunk,(1>.(2.&8.))P,(16.$;.R2.(11.&40.R1:.)(=.$17.(18.(19.(11.&40.R18.))R1.)(13.$17.)))P,(15.$;.R3.)(26.$;.(27.R25.R24.R23.R22.R1>.R1=.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R6.R5.R1<.R1;.R1:.R4.)(6.(7.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R6.(1;.&40.+>:=<4.)R5.(9.(2.&40.))R4.(:.$;.)))")
(* [comment removed for export] *).
Proof.
  intros until junk. intros DST MI.
  eapply memset_body; [exact MI | | exact DST].
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.

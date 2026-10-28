(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge Mem Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_amem_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
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
Ltac2 gd_tbl_A_imsetv () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "vfill"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.repeat"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.shiftl"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Stdlib.ZArith.BinInt.Z.to_nat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.imsv_post"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.zxb"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"].


(* [comment removed for export] *)
Definition vfill (m : mem) (P i n : Z) (b : byte) : Prop :=
  bytes_at asegs m P (repeat b (Z.to_nat i)) /\ wr_at asegs m P n /\ 0 <= i <= n.

Lemma vfill_start : forall m P bs b, u8arr asegs m P bs -> vfill m P 0 (Z.of_nat (length bs)) b.
Proof.
  intros m P bs b [HB HW]. unfold vfill. split; [|split; [exact HW| lia]].
  cbn [Z.to_nat repeat]. apply bytes_at_nil. ddestruct HW as (H1 & H2 & _). lia.
Qed.

Lemma vfill_store_ok : ltac2:(CDefT.buildp (gd_tbl_A_imsetv ()) "Pm,P,(0.&40.)(1.(0.&8.))PP,$2.Pi,$2.Pn,$2.Pb,(0.&8.)Pk,$3.P,(4.R6.R5.R4.R3.R2.)P,(5.(6.R5.(7.R2.))R4.)(8.$9.(:.$;.R8.(<.(6.R7.R6.))R3.)$=.)")
(* [comment removed for export] *).
Proof. (intros m P i n b k dd_H; ddestruct dd_H as (HB & HW & HI); intros Hk). eapply wr_at_store_ok; [exact HW| lia| lia]. Qed.

Lemma repeat_app_nat : forall {X} (x : X) a c, repeat x (a + c) = repeat x a ++ repeat x c.
Proof. intros X x a c. rewrite repeat_app. reflexivity. Qed.

Lemma vfill_write : ltac2:(CDefT.buildp (gd_tbl_A_imsetv ()) "Pm,P,(0.&40.)(1.(0.&8.))PP,$2.Pi,$2.Pn,$2.Pb,(0.&8.)Pbs,(>.(0.&8.))P,(4.R6.R5.R4.R3.R2.)P,(5.(6.R5.(7.(?.(0.&8.)R2.)))R4.)P,(8.(>.(0.&8.))R3.(10.(0.&8.)R4.(?.(0.&8.)R3.)))(4.(11.R9.(<.(6.R8.R7.))R4.)R8.(6.R7.(7.(?.(0.&8.)R4.)))R6.R5.)")
(* [comment removed for export] *).
Proof.
  (intros m P i n b bs dd_H; ddestruct dd_H as (HB & HW & HI); intros Hn E). unfold vfill.
  dpose HW as (W0 & W1 & _).
  split; [| split; [apply wr_at_write; exact HW| lia]].
  replace (Z.to_nat (i + Z.of_nat (length bs))) with (Z.to_nat i + length bs)%nat by lia.
  rewrite repeat_app_nat. apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HB| lia| lia|]. left. rewrite repeat_length. lia.
  - rewrite repeat_length. replace (P + Z.of_nat (Z.to_nat i)) with (P + i) by lia.
    rewrite <- E. apply bytes_at_write_same; lia.
Qed.

Lemma vfill_done : forall m P n b, vfill m P n n b -> u8arr asegs m P (repeat b (Z.to_nat n)).
Proof.
  (intros m P n b dd_H; ddestruct dd_H as (HB & HW & HI)). split; [exact HB|]. rewrite repeat_length. replace (Z.of_nat (Z.to_nat n)) with n by lia. exact HW.
Qed.

Lemma list_bv_eq : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Definition pat8 (b : byte) : word := ltac2:(CDefT.buildp (gd_tbl_A_imsetv ()) "(12.&40.(13.(14.(15.(13.(14.(15.(13.(14.(15.(16.&8.O1.)+8.)+10000000000000000.)(16.&8.O1.))+10.)+10000000000000000.)(13.(14.(15.(16.&8.O1.)+8.)+10000000000000000.)(16.&8.O1.)))+20.)+10000000000000000.)(13.(14.(15.(13.(14.(15.(16.&8.O1.)+8.)+10000000000000000.)(16.&8.O1.))+10.)+10000000000000000.)(13.(14.(15.(16.&8.O1.)+8.)+10000000000000000.)(16.&8.O1.)))))")
(* [comment removed for export] *).

Lemma le8_pat8 : forall b : byte, le8 (pat8 b) = repeat b 8.
Proof.
  intros b. unfold pat8.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8)%Z with 256%Z in R.
  rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b).
  rewrite !(definitions.Z_to_bv_small 8) by (unfold bv_modulus; change (2 ^ Z.of_N 8)%Z with 256%Z; lia).
  set (z := bv_unsigned b) in *. clearbody z.
  assert (E : exists k : nat, z = Z.of_nat k /\ (k < 256)%nat) by (exists (Z.to_nat z); lia).
  ddestruct E as (k & -> & Hk).
  do 256 (destruct k as [|k]; [apply list_bv_eq; vm_compute; reflexivity|]). lia.
Qed.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition imsv_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word)
      (PC : word) (fc : bv 32) (P n : Z) (b : byte) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_imsetv ()) "Lms',$17.(18.(0.&40.)La3',(0.&40.)(18.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(19.(8.$17.R3.(1:.(1;.O24.O23.O22.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.(12.&40.(6.O4.O3.))R2.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.)O7.O6.O5.(1<.(0.&40.))R1.(1=.$;.)))(19.(1>.(1?.(20.$2.$2.)(21.$2.$2.O4.(6.O4.O3.))(22.(20.$2.$2.)))O1.R1.)(19.(23.$;.O1.R1.)(19.(24.$;.R1.)(25.$;.R1.O4.(10.(0.&8.)O2.(26.O3.)))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma imsv_bloop : ltac2:(CDefT.buildp (gd_tbl_A_imsetv ()) "Pk,$3.Pi,$2.Pn,$2.PP,$2.Pcd,$2.Pb,(0.&8.)Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(27.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(1.(0.&8.))Pm,P,(0.&40.)(1.(0.&8.))P,(8.$2.R22.(6.R23.R25.))P,(8.$2.R26.(28.R25.(7.R27.)))P,(19.(5.=R27.)(29.R27.R26.))P,(29.(6.R26.R27.)(2:.+2.+3?.))P,(29.=R27.)P,(4.R6.R28.R2:.R29.R26.)P,(2;.VCS,R29.R2:.)P,(1>.(1?.(20.$2.$2.)(21.$2.$2.R2:.(6.R2:.R2;.))(22.(20.$2.$2.)))R9.R8.)P,(23.$;.R:.R9.)P,(24.$;.R:.)(2<.$;.VAL,VCS,(2=.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.(2>.R2;.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.(12.&40.+7::;4.)R=.R2=.R2>.R2;.R<.)(1:.(1;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.(2>.R2;.)(12.&40.(6.R2=.R2>.))(12.&40.R2<.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(12.&40.+7::70.)R=.(1<.(0.&40.))R;.(1=.$;.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until m; intros -> Hi Hin N63 P0 VF CR MU WM MI; [lia|]. al_facts.
    assert (SOK : store_ok asegs m (Z_to_bv 64 (P + i)) 1 = true).
    { change (Z_to_bv 64 (P + i)) with (wa (P + i)). eapply (vfill_store_ok m P i n b 1); [exact VF | cbn; lia]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
    pose proof (vfill_write m P i n b [b] VF ltac:(cbn; lia) eq_refl) as VF1. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in VF1.
    change (Z.of_nat 1) with 1 in VF1.
    set (m1 := write_to_mem m (wa (P + i)) [b]) in *.
    change (write_to_mem m (Z_to_bv 64 (P + i)) [b]) with m1.
    assert (MU1 : munch [(P, P + n)] m0 m1).
    { subst m1. eapply munch_trans; [exact MU|]. apply munch_write; [apply munch_refl | lia | cbn; lia | cbn; left; lia]. }
    assert (WM1 : wmono asegs m0 m1) by (subst m1; eapply wmono_trans; [exact WM | apply wmono_write; apply wmono_refl]).
    assert (MI1 : mem_inv asegs m1) by (subst m1; apply mem_inv_store; [exact MI | exact SOK]).
    destruct (Z.eq_dec (i + 1) n) as [EQ|NE].
    - if_falseU. (* [comment removed for export] *) zstep. apply evtA_done. eexists _, m1. split; [replace (P + i + 1) with (P + n) by lia; reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
      apply vfill_done. rewrite <- EQ at 1. exact VF1.
    - if_trueU. eapply (IH (i + 1) n P (P + i + 1) b); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma imsv_wloop : ltac2:(CDefT.buildp (gd_tbl_A_imsetv ()) "Pk,$3.Pi,$2.Pn,$2.PP,$2.Pcd,$2.Pb,(0.&8.)Ppat,(0.&40.)Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(27.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(1.(0.&8.))Pm,P,(0.&40.)(1.(0.&8.))P,(8.(>.(0.&8.))(2?.R21.)(10.(0.&8.)R22.#8.))P,(8.$2.R24.(6.R25.R27.))P,(8.$2.R28.(28.R27.(30.+10.(7.R29.))))P,(19.(5.=R29.)(29.R29.R28.))P,(29.(6.R28.R29.)(2:.+2.+3?.))P,(29.=R29.)P,(4.R7.R2:.R2<.R2;.R28.)P,(2;.VCS,R2;.R2<.)P,(1>.(1?.(20.$2.$2.)(21.$2.$2.R2<.(6.R2<.R2=.))(22.(20.$2.$2.)))R:.R9.)P,(23.$;.R;.R:.)P,(24.$;.R;.)(2<.$;.VAL,VCS,(2=.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R2<.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.(12.&40.+7::;4.)R>.R2?.R30.R2=.R=.)(1:.(1;.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R2<.(12.&40.(6.R2?.R30.))(12.&40.R2>.)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(12.&40.+7:::4.)R>.(1<.(0.&40.))R<.(1=.$;.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until m; intros PAT -> Hi Hin N63 P0 VF CR MU WM MI; [lia|]. al_facts.
    assert (I16 : i + 16 <= n) by lia.
    (* [comment removed for export] *)
    assert (SOK : store_ok asegs m (Z_to_bv 64 (P + i)) 8 = true).
    { change (Z_to_bv 64 (P + i)) with (wa (P + i)). eapply (vfill_store_ok m P i n b 8); [exact VF | cbn; lia]. }
    zstep. rewrite PAT.
    pose proof (vfill_write m P i n b (repeat b 8) VF ltac:(cbn; lia) ltac:(reflexivity)) as VF1.
    change (Z.of_nat (length (repeat b 8))) with 8 in VF1.
    set (m1 := write_to_mem m (wa (P + i)) (repeat b 8)) in *.
    change (write_to_mem m (Z_to_bv 64 (P + i)) (repeat b 8)) with m1.
    assert (MU1 : munch [(P, P + n)] m0 m1).
    { subst m1. eapply munch_trans; [exact MU|]. apply munch_write; [apply munch_refl | lia | cbn; lia | cbn; left; lia]. }
    assert (WM1 : wmono asegs m0 m1) by (subst m1; eapply wmono_trans; [exact WM | apply wmono_write; apply wmono_refl]).
    assert (MI1 : mem_inv asegs m1) by (subst m1; apply mem_inv_store; [exact MI | exact SOK]).
    clear SOK. clearbody m1.
    (* [comment removed for export] *)
    assert (SOK : store_ok asegs m1 (Z_to_bv 64 (P + i + 8)) 8 = true).
    { change (Z_to_bv 64 (P + i + 8)) with (wa (P + i + 8)). replace (P + i + 8) with (P + (i + 8)) by lia.
      eapply (vfill_store_ok m1 P (i + 8) n b 8); [exact VF1 | cbn; lia]. }
    zstep. rewrite PAT.
    pose proof (vfill_write m1 P (i + 8) n b (repeat b 8) VF1 ltac:(cbn; lia) ltac:(reflexivity)) as VF2.
    change (Z.of_nat (length (repeat b 8))) with 8 in VF2.
    replace (wa (P + (i + 8))) with (Z_to_bv 64 (P + i + 8) : word) in VF2 by (unfold wa; f_equal; lia).
    set (m2 := write_to_mem m1 (Z_to_bv 64 (P + i + 8)) (repeat b 8)) in *.
    assert (MU2 : munch [(P, P + n)] m0 m2).
    { subst m2. eapply munch_trans; [exact MU1|]. change (Z_to_bv 64 (P + i + 8)) with (wa (P + i + 8)).
      apply munch_write; [apply munch_refl | lia | cbn; lia | cbn; left; lia]. }
    assert (WM2 : wmono asegs m0 m2) by (subst m2; eapply wmono_trans; [exact WM1 | apply wmono_write; apply wmono_refl]).
    assert (MI2 : mem_inv asegs m2) by (subst m2; apply mem_inv_store; [exact MI1 | exact SOK]).
    clear SOK. clearbody m2.
    (* [comment removed for export] *)
    zstep. zstep.
    destruct (Z_lt_le_dec (i + 16) n) as [LT|GE].
    - if_trueU. eapply (IH (i + 16) n P (P + i + 16) b pat); try eassumption; try lia. replace (i + 16) with (i + 8 + 8) by lia. exact VF2.
    - if_falseU. apply evtA_done. eexists _, m2. split; [replace (P + i + 16) with (P + n) by lia; reflexivity|].
      split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|].
      apply vfill_done. replace n with (i + 8 + 8) at 1 by lia. exact VF2.
  Qed.

  #[using="Type"] Lemma land15_lor_zero : forall a c, 0 <= a -> 0 <= c -> Z.land (Z.lor a c) 15 = 0 -> a mod 16 = 0 /\ c mod 16 = 0.
  Proof.
    intros a c Ha Hc H. rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H. destruct H as [H1 H2].
    change 15 with (Z.ones 4) in H1, H2. rewrite Z.land_ones in H1, H2 by lia. change (2^4) with 16 in H1, H2. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Theorem imsetv_spec : ltac2:(CDefT.buildp (gd_tbl_A_imsetv ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(27.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))PP,$2.Pn,$2.Pb,(0.&8.)Pds,(>.(0.&8.))P,(25.$;.R5.R4.R1.)P,(8.$2.(7.(?.(0.&8.)R2.))R4.)P,(29.=R5.)P,(2;.VCS,R7.R6.)P,(29.=R8.)P,(29.(6.R9.R8.)(2:.+2.+3?.))P,(24.$;.R;.)P,(8.(0.&40.)R24.(12.&40.R;.))P,(8.(0.&40.)R24.(2>.R:.))P,(8.(0.&40.)R24.(12.&40.R<.))(2<.$;.VAL,VCS,Lms',$17.(18.(0.&40.)La1',(0.&40.)(18.(0.&40.)La3',(0.&40.)(18.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(19.(8.$17.R4.(1:.(1;.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R3.(12.&40.(6.R12.R11.))R2.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(31.R34.)R14.(1<.(0.&40.))R1.(1=.$;.)))(19.(1>.(1?.(20.$2.$2.)(21.$2.$2.R12.(6.R12.R11.))(22.(20.$2.$2.)))R13.R1.)(19.(23.$;.R13.R1.)(19.(24.$;.R1.)(25.$;.R1.R12.(10.(0.&8.)R10.(26.R11.))))))))))(1:.(1;.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(12.&40.+7::58.)R10.(1<.(0.&40.))R?.(1=.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros until ds. intros ARR LEN N1 CR P0 PH MI -> -> ->. al_facts.
    pose proof (vfill_start m P ds b ARR) as VF. rewrite LEN in VF.
    pose proof (munch_refl [(P, P + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (B15 : 0 <= Z.land (Z.lor n P) 15 < 16).
    { change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2^4) with 16. apply Z.mod_pos_bound. lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    destruct (Z.eq_dec (Z.land (Z.lor n P) 15) 0) as [AL16|NA].
    - (* [comment removed for export] *)
      destruct (land15_lor_zero n P ltac:(lia) ltac:(lia) AL16) as [Mn Mp].
      if_trueU. zstep. if_falseU. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      eapply (evtA_cut asegs AL CS).
      { eapply (imsv_wloop (Z.to_nat (n / 16)) 0 n P P b (pat8 b)); [exact (le8_pat8 b) | ..]; try eassumption; try lia. }
      cbn beta. (intros ms' dd_H; ddestruct dd_H as (a3' & m' & -> & MU' & WM' & MI' & ARR')). zstep. apply evtA_done.
      eexists _, _, m'. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'| exact ARR'].
    - (* [comment removed for export] *)
      if_falseU. zstep. if_falseU. zstep. zstep.
      eapply (evtA_cut asegs AL CS).
      { eapply (imsv_bloop (Z.to_nat n) 0 n P P b); try eassumption; try lia. }
      cbn beta. (intros ms' dd_H; ddestruct dd_H as (a3' & m' & -> & MU' & WM' & MI' & ARR')). zstep. apply evtA_done.
      eexists _, _, m'. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'| exact ARR'].
  Qed.
End Walk.

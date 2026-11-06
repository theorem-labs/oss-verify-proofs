(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanNodesAux AsanStartLoops AsanNodesStartX.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanNodesStartXInit () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.false"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.ABoot.AsanInit.argH0"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.None"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.uE"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.e_envp"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ev"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.V_ENVC"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.e_str0"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.ABoot.PropExec.wrap_mem"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.x_stmt"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.NX0"; "OSSVerify.KrLib.ABoot.AsanInit.LIMIT"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.XEnvScan"].


Section GenericInit.
  (* [comment removed for export] *)
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis HULL_cov : APS.hull_cov segs A.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
  Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
  Hypothesis Fe1 : fetch_word segs (Z_to_bv 64 (x_envscan A)) = Some we1.
  Hypothesis Fe2 : fetch_word segs (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
  Hypothesis Fe3 : fetch_word segs (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
  Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
  Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
  Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
  Hypothesis Fp0 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
  Hypothesis Fp1 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
  Hypothesis Fp2 : fetch_word segs (Z_to_bv 64 (x_pnscan A)) = Some wp2.
  Hypothesis Fp3 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
  Hypothesis Fp4 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
  Hypothesis Ep : ltac2:(CDefT.buildp (gd_tbl_AsanNodesStartXInit ()) "(0.(1.$2.(3.Vwp0,)$4.)(0.(1.$2.(3.Vwp1,)$4.)(0.(1.$2.(3.Vwp2,)$4.)(0.(1.$2.(3.Vwp3,)$4.)(1.$2.(3.Vwp4,)$4.)))))")
(* [comment removed for export] *).
  Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 ph sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : ltac2:(CDefT.buildp (gd_tbl_AsanNodesStartXInit ()) "PE,$5.PM,Px,(6.&40.)(7.(6.&8.))PM',Px,(6.&40.)(7.(6.&8.))P,Pa,(6.&40.)P,(1.$2.(8.Vph,Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,R4.R1.)$9.)(1.(7.(6.&8.))A1.R3.R2.A1.R4.R2.)P,Pa,(6.&40.)P,(:.(;.&40.Vsp,)(;.&40.R1.))P,(<.(1.(7.(6.&8.))A1.R5.R2.(=.(6.&8.))))(<.(1.(7.(6.&8.))A1.R5.R3.(=.(6.&8.))))P,A2.VSINV,R5.R4.A2.VSINV,R6.R4.")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].

  #[using="Hsp"] Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  #[using="Hsp"] Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  (* [comment removed for export] *)
  #[using="ph rdraw brk0 Hsp Hva Hve uid hw Hfit SINV_SINV0"] Lemma SINV0_vals : ltac2:(CDefT.buildp (gd_tbl_AsanNodesStartXInit ()) "PE,$5.PM,P,(6.&40.)(7.(6.&8.))P,A2.VSINV,R2.R1.(0.(1.$>.(?.R3.$10.)(11.(11.Vusp,(12.+8.Vargc,))+10.))(0.(1.(6.&40.)(13.R3.$14.)(15.&40.Venvc,))(1.$>.(?.R3.$16.)(11.(11.(11.Vusp,(12.+8.Vargc,))(12.+8.Venvc,))+;8.))))")
(* [comment removed for export] *).
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (u_e_envp ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U1.
    pose proof (u_e_str0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U3.
    pose proof (uE0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & _ & U2 & _).
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *.
    rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_envp eq_refl Hev7).
    rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_str0 eq_refl Hev7).
    split; [exact U1|]. split; [|exact U3].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) (EVar V_ENVC) eq_refl Hev7).
    apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
  Qed.

  #[using="brk0 SINV_SINV0"] Lemma SINV0_envp : ltac2:(CDefT.buildp (gd_tbl_AsanNodesStartXInit ()) "PE,$5.PM,P,(6.&40.)(7.(6.&8.))Pa,(6.&40.)P,A2.VSINV,R3.R2.P,(0.(:.(11.(11.Vusp,(12.+8.Vargc,))+10.)(;.&40.R2.))(17.(;.&40.R2.)(11.(11.(11.(11.Vusp,(12.+8.Vargc,))+10.)(12.+8.Venvc,))+8.)))(1.(7.(6.&8.))A1.R4.R3.(18.Vph,Vsp,Vargv,Venvp,Vuid,Vhw,Vrdraw,R3.))")
(* [comment removed for export] *).
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. left.
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  #[using="ph sp rdraw brk0 envp Hva uid hw Hfit SINV SINV_SINV0 SINV_frame usp envc"] Lemma s0_fits : Z.of_nat (length s0) + 1 <= total_arg_bytes argv.
  Proof.
    unfold s0. rewrite total_arg_bytes_Z. destruct argv as [|a r]; [destruct Hva as [H _]; cbn in H; lia|].
    cbn [nth]. rewrite total_arg_bytes_cons. lia.
  Qed.

  #[using="brk0 Hva Hve Hfit SINV_SINV0 SINV_frame"] Lemma SINV0_str0 : ltac2:(CDefT.buildp (gd_tbl_AsanNodesStartXInit ()) "PE,$5.PM,P,(6.&40.)(7.(6.&8.))Pa,(6.&40.)P,A2.VSINV,R3.R2.P,(0.(:.(11.(11.(11.Vusp,(12.+8.Vargc,))(12.+8.Venvc,))+;8.)(;.&40.R2.))(:.(;.&40.R2.)(11.(11.(11.(11.Vusp,(12.+8.Vargc,))(12.+8.Venvc,))+;8.)(19.(1:.(6.&8.)Vs0,)))))(1.(7.(6.&8.))A1.R4.R3.(18.Vph,Vsp,Vargv,Venvp,Vuid,Vhw,Vrdraw,R3.))")
(* [comment removed for export] *).
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. right.
    pose proof (W_range ph sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
    pose proof (length_bsb_eq ph sp rdraw argv envp uid hw) as L. pose proof s0_fits as F.
    pose proof (total_arg_bytes_Z envp) as TE.
    unfold stack_image_size in L.
    assert (Hpd : 0 <= (8 - (8 + (Z.of_nat (length argv) + 1) * 8 + (Z.of_nat (length envp) + 1) * 8 + 160
                              + total_arg_bytes argv + total_arg_bytes envp) mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS_wx SEGS_in_hull HULL_ok we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3 brk0 Hsp Hva Hve Hfit SINV_SINV0 SINV_frame usp argc envc"] Theorem init_x_sound_envscan : ltac2:(CDefT.buildp (gd_tbl_AsanNodesStartXInit ()) "(1;.Vsegs,VA,$1<.$1=.(;.&40.Vsp,)VSINV,(8.Vph,Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,)VFS0,$1>.)")
(* [comment removed for export] *).
  Proof.
    exact (x_sound_envscan segs A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0
              SEGS_wx SEGS_in_hull HULL_ok (bv_unsigned sp) SINV_frame
              we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
              ph sp rdraw argv envp uid hw Hva Hve sp_lo sp_hi eq_refl SINV0_vals SINV0_envp).
  Qed.

  #[using="SEGS_wx SEGS_in_hull HULL_ok wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4 brk0 Hsp Hva Hve Hfit SINV_SINV0 SINV_frame SINV_agree usp argc envc s0"] Theorem init_x_sound_pnscan :
    x_stmt segs A NX0 LIMIT (bv_unsigned sp) SINV (argH0 ph sp rdraw argv envp uid hw) FS0 XPnScan.
  Proof.
    exact (x_sound_pnscan segs A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0
              SEGS_wx SEGS_in_hull HULL_ok (bv_unsigned sp)
              (argH0_high ph sp rdraw argv envp uid hw Hva) (argH0_agree ph sp rdraw argv envp uid hw)
              SINV_frame SINV_agree
              wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
              ph sp rdraw argv envp uid hw Hva Hve sp_lo sp_hi eq_refl SINV0_vals SINV0_str0).
  Qed.
  #[using="Type"] Theorem init_x_sound_layout :
    x_stmt segs A NX0 LIMIT (bv_unsigned sp) SINV (argH0 ph sp rdraw argv envp uid hw) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.

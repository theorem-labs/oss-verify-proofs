(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame LibTail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow Restrict RestrictLib RestrictRun NodesA SymDriveA SymDriveAX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_base A_exit_lib A_exit_defs A_unreg_globals A_stdio_defs A_stdio_write A_stdio_call A_rip A_fwrite_oom.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tailkit_defs A_tailkit_exit A_refused_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxAKnD.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_refused () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_LO"; "ShadowArith.SHW"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_HI"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.env"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "kread_bytes"; "Corelib.Init.Datatypes.Some"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.lor"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "RocqVerifyHarness.AgentSubmission.LibA.SymDriveA.DcovZ"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.Env"; "RocqVerifyHarness.AgentSubmission.BB.SymDrive.blobs_ev"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "SHW"; "RocqVerifyHarness.AgentSubmission.LibA.Restrict.restrict"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "Stdlib.ZArith.BinInt.Z.eqb"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "Stdlib.ZArith.BinInt.Z.lxor"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_refused"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"].

#[local] Existing Instance Lib.PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ShadowArith.
  Open Scope Z_scope.
  (* [comment removed for export] *)
  Definition SHW (sp0 : word) (k : Z) : Z :=
    let q := (bv_unsigned sp0 + k) / 8 + 0x7fff8000 in q - q mod 8.

  Lemma SHW_range : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "Psp0,(0.&40.)Pk,$1.P,(2.(3.(4.+7???7?000000.+1000.)(5.&40.R2.))(3.(5.&40.R2.)+800000000000.))P,(6.$1.(7.(5.&40.R3.)+10.)=)P,(2.(3.-?<0.R3.)(3.R3.-40.))(2.(3.(8.R5.)(9.R5.R4.))(2.(3.(4.(9.R5.R4.)+8.)(:.R5.))(2.(6.$1.(7.(9.R5.R4.)+8.)=)(2.(3.+7???8000.(9.R5.R4.))(2.(3.(4.(9.R5.R4.)+8.)(;.+2.+2>.))(2.(3.=(8.R5.))(3.(:.R5.)(;.+2.+2>.))))))))")
(* [comment removed for export] *).
  Proof. intros sp0 k H1 H2 H3. unfold SHW, SSH_LO, SSH_HI. lia. Qed.

  Lemma mod4_of_sp : forall s k r, s mod 16 = 0 -> 0 <= s + k -> (k mod 4 =? 0) = r -> ((s + k) mod 4 =? 0) = r.
  Proof. intros s k r H1 H2 H3. replace ((s + k) mod 4) with (k mod 4); [exact H3|]. lia. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41415985948.2000001S".
  Lemma land3_mod4 : forall x, 0 <= x -> Z.land x 3 = x mod 4.
  Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ssh_app : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "Psp0,(0.&40.)Pz,$1.P,(2.(3.(4.+7???7?000000.+1000.)(5.&40.R2.))(3.(5.&40.R2.)+800000000000.))P,(6.$1.(7.(5.&40.R3.)+10.)=)P,(2.(3.(8.R4.)R3.)(<.R3.(:.R4.)))(2.(2.(3.(=.(5.&40.R5.)+1000.)(>.+8.(=.R4.+7???8000.)))(<.(>.+8.(=.R4.+7???8000.))(5.&40.R5.)))(6.$1.R4.(4.+7???8000.(?.(>.+8.(=.R4.+7???8000.))+8.))))")
(* [comment removed for export] *).
  Proof. intros sp0 z H1 H2 H3. unfold SSH_LO, SSH_HI in H3. lia. Qed.
End ShadowArith.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint kread_bytes (kn : list kentry) (b : expr) (k : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match kread RSEGS kn b k 1 with
            | Some (ELit v) => match kread_bytes kn b (k + 1) n' with Some vs => Some (v :: vs) | None => None end
            | _ => None
            end
  end.

Lemma kread_bytes_rdn : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "PE,$10.PM,P,(0.&40.)(11.(0.&8.))Pkn,(12.$13.)Pb,$14.Pn,$15.Pk,$1.Pvs,(12.$1.)P,(16.$17.R7.R6.R5.)P,(6.(11.(12.$1.))(18.R6.R5.R3.R4.)(19.(12.$1.)R2.))P,(1:.$1.Lv,$1.(2.(3.=R1.)(<.R1.+100.))R3.)P,(3.=(4.(5.&40.(1;.R:.R7.))R5.))P,(<.(4.(4.(5.&40.(1;.R;.R8.))R6.)(1<.R7.))(;.+2.+40.))(6.(11.(12.(0.&8.)))(1=.$17.R;.(1>.&40.(4.(5.&40.(1;.R<.R9.))R7.))R8.)(19.(12.(0.&8.))(1?.$1.(0.&8.)Lv,$1.(1>.&8.R1.)R6.)))")
(* [comment removed for export] *).
Proof.
  intros E M kn b n. induction n as [|n IH]; intros k vs HK Hr Hvs Hlo Hhi.
  - cbn in Hr. inversion Hr. reflexivity.
  - cbn [kread_bytes] in Hr. destruct (kread RSEGS kn b k 1) as [[v| | | | | | |]|] eqn:E1; try discriminate.
    destruct (kread_bytes kn b (k + 1) n) as [vs'|] eqn:E2; [|discriminate]. inversion Hr; subst vs. clear Hr.
    apply Forall_cons_iff in Hvs as [Hv Hvs'].
    pose proof (kread_rdn RSEGS E M kn b k 1 (ELit v) HK E1 ltac:(lia) ltac:(lia)
                  ltac:(unfold flat, estart; cbn [a_base a_off]; lia)) as R1.
    unfold adenot, v_addi in R1. cbn [a_base a_off edenot] in R1.
    change (S n) with (1 + n)%nat. cbn [map]. change (Z_to_bv 8 v :: map (fun v0 => Z_to_bv 8 v0) vs') with ([Z_to_bv 8 v] ++ map (fun v0 => Z_to_bv 8 v0) vs').
    apply rdn_app_Z; [ | | lia | lia].
    + rewrite R1. f_equal. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite bv_wrap8_mod, bv_wrap64_mod.
      rewrite (Z.mod_small v) by lia. reflexivity.
    + replace (bv_unsigned (edenot E b) + k + Z.of_nat 1)%Z with (bv_unsigned (edenot E b) + (k + 1))%Z by lia.
      apply IH; [exact HK | exact E2 | exact Hvs' | lia | lia].
Qed.

(* [comment removed for export] *)
Definition msgZ : list Z := Eval vm_compute in match kread_bytes knA (EVar 0) (-464) 38 with Some vs => vs | None => [] end.
Lemma msgZ_eq : kread_bytes knA (EVar 0) (-464) 38 = Some msgZ.
Proof. vm_compute. reflexivity. Qed.
Lemma msgZ_msg : map (fun v => Z_to_bv 8 v) msgZ = msg_refused.
Proof. vm_compute. reflexivity. Qed.
Lemma msgZ_range : Forall (fun v => 0 <= v < 256)%Z msgZ.
Proof. unfold msgZ. repeat (constructor; [lia|]). constructor. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rf_lor40_mod16 : forall x, (0 <= x)%Z -> ((Z.lor 40 x) mod 16 <> 0)%Z.
Proof.
  intros x Hx EQ.
  assert (T : Z.testbit (Z.lor 40 x) 3 = true) by (rewrite Z.lor_spec; reflexivity).
  apply Z.testbit_true in T; [|lia]. change (2 ^ 3)%Z with 8%Z in T.
  pose proof (Z.lor_nonneg 40 x) as NN.
  pose proof (Z.div_mod (Z.lor 40 x) 16 ltac:(lia)) as DM. rewrite EQ, Z.add_0_r in DM.
  rewrite DM in T. replace (16 * (Z.lor 40 x / 16) / 8)%Z with (2 * (Z.lor 40 x / 16))%Z in T.
  2:{ symmetry. replace (16 * (Z.lor 40 x / 16))%Z with ((2 * (Z.lor 40 x / 16)) * 8)%Z by lia. apply Z.div_mul. lia. }
  rewrite Z.mul_comm, Z_mod_mult in T. lia.
Qed.
Lemma rf_memset_align_false : forall x, (0 <= x)%Z ->
  bv_eqb (Z_to_bv 64 (Z.land (Z.lor 40 x) 15)) (Z_to_bv 64 0) = false.
Proof.
  intros x Hx. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4)%Z with 16%Z.
  pose proof (Z.mod_pos_bound (Z.lor 40 x) 16 ltac:(lia)) as B. pose proof (rf_lor40_mod16 x Hx) as NZ.
  unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact NZ.
Qed.

Lemma rf_lor40_bound : forall x, (0 <= x < 2^64)%Z -> (0 <= Z.lor 40 x < 2^64)%Z.
Proof.
  intros x Hx. split; [apply Z.lor_nonneg; lia|].
  apply Z.log2_lt_pow2. { assert (0 <= Z.lor 40 x)%Z by (apply Z.lor_nonneg; lia). destruct (Z.eq_dec (Z.lor 40 x) 0) as [E0|]; [|lia]. exfalso. pose proof (rf_lor40_mod16 x ltac:(lia)) as MZ. rewrite E0 in MZ. apply MZ. reflexivity. }
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; [reflexivity|].
  destruct (Z.eq_dec x 0) as [->|NZ]; [reflexivity|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma rf_memset_align_false' : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "Px,$1.P,(2.(3.=R1.)(<.R1.(;.+2.+40.)))(6.$20.(21.&40.(1>.&40.(22.(5.&40.(1>.&40.(23.(5.&40.(1>.&40.+28.))(5.&40.(1>.&40.R2.)))))(5.&40.(1>.&40.+?.))))(1>.&40.=))$24.)")
(* [comment removed for export] *).
Proof.
  intros x Hx. rewrite (unsigned_lit 40), (unsigned_lit 15), (unsigned_lit x) by lia.
  rewrite unsigned_lit by (apply rf_lor40_bound; lia). apply rf_memset_align_false. lia.
Qed.

(* [comment removed for export] *)
Definition entry_in2_b (spi : nat) (flo fhi ilo ihi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => Nat.eqb i spi && Z.leb flo k && Z.leb (k + Z.of_nat w) fhi && Z.ltb 0 (Z.of_nat w)
  | SE (SA (ELit z) k) w _ => Z.eqb z 0 && Z.leb ilo k && Z.leb (k + Z.of_nat w) ihi && Z.ltb 0 (Z.of_nat w)
  | _ => false
  end.
Lemma log_out_in2 : forall E spi flo fhi ilo ihi log (x : word),
  forallb (entry_in2_b spi flo fhi ilo ihi) log = true ->
  (0 <= bv_unsigned (ev E spi) + flo)%Z -> (bv_unsigned (ev E spi) + fhi <= 2 ^ 64)%Z ->
  (0 <= ilo)%Z -> (ihi <= 2 ^ 64)%Z ->
  ~ (bv_unsigned (ev E spi) + flo <= bv_unsigned x < bv_unsigned (ev E spi) + fhi)%Z ->
  ~ (ilo <= bv_unsigned x < ihi)%Z ->
  log_out E x log.
Proof.
  intros E spi flo fhi ilo ihi log x Hb S1 S2 I1 I2 N1 N2.
  induction log as [|[[b k] w v] rest IH]; [exact I|].
  cbn [forallb] in Hb. apply andb_prop in Hb. destruct Hb as [He Hr].
  cbn [log_out]. unfold adenot, v_addi. cbn [a_base a_off].
  destruct b as [z|i| | | | | |]; cbn [entry_in2_b] in He; try discriminate.
  - repeat (apply andb_prop in He; destruct He as [He ?]).
    apply Z.eqb_eq in He. subst z.
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H | H : (_ <? _)%Z = true |- _ => apply Z.ltb_lt in H end.
    cbn [edenot]. rewrite (u_small 0) by lia. rewrite u_small by lia.
    split; [lia | split; [lia | exact (IH Hr)]].
  - repeat (apply andb_prop in He; destruct He as [He ?]).
    apply Nat.eqb_eq in He. subst i.
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H | H : (_ <? _)%Z = true |- _ => apply Z.ltb_lt in H end.
    cbn [edenot]. rewrite u_small by lia.
    split; [lia | split; [lia | exact (IH Hr)]].
Qed.

Section RF.
  (* [comment removed for export] *)
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable KI : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000%Z.
  Hypothesis GSB : al_gsb AL = 0x1099f8%Z.
  Hypothesis IMGCS : A_unreg_globals.img_cs AL CS.
  Hypothesis K_halted : forall mo, KI mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "Pmo,$25.Pacc,(12.(26.(0.&40.)$15.))P,A1.VKI,R2.P,(27.VAL,VCS,R2.)(28.$25.Lmo',$25.(2.(6.(11.$25.)(29.R5.R4.)(19.$25.R1.))(2.A1.VKI,R1.(2:.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "Pmo,$25.Pmo',$25.P,A1.VKI,R2.P,(6.$2;.(2<.R2.)(2<.R3.))P,(6.(12.(26.(0.&40.)(0.&40.)))(2=.R3.)(2=.R4.))P,(6.(12.(0.&40.))(2>.R4.)(2>.R5.))P,(6.(11.(0.&40.))(2?.R5.)(2?.R6.))A1.VKI,R6.")
(* [comment removed for export] *).

  Variable sp0 : word.
  Variable model : Model.
  Hypothesis SPlo : (0x7fff7f000000 + 4096 <= bv_unsigned sp0)%Z.
  Hypothesis SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis SPal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Hypothesis HKI : KI model.
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  (* [comment removed for export] *)
  Hypothesis WCS : crange CS (bv_unsigned sp0 - 4096) 4096.
  Hypothesis FCS : crange CS 0x1b900 128.

  Variables (R : bvmap 5 word) (M : word -> option byte) (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Hypothesis G2 : getr R 2 = sp0.
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x63ca90.
  Hypothesis TM : tail_memA sp0 M can tid wp0 rp0 wp1 rp1.

  (* [comment removed for export] *)
  Let D : word -> bool := Dimg [(bv_unsigned sp0 - 4096, bv_unsigned sp0)%Z; (0x7fffb720, 0x7fffb730)%Z; (SSH_LO sp0, SSH_HI sp0)].

  Lemma SSH_facts : (0x7fff8000 <= SSH_LO sp0)%Z /\ (SSH_HI sp0 <= 2^46)%Z /\ (SSH_LO sp0 < SSH_HI sp0)%Z.
  Proof. pose proof (SHW_range sp0 (-64) ltac:(lia) SPal ltac:(lia)). unfold SSH_LO, SSH_HI in *. lia. Qed.

  Lemma D_Dseg : forall a : word, segcov RSEGS (bv_unsigned a) = true -> D a = true.
  Proof. intros a H. unfold D. apply Dimg_Dseg. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L6097392651.3100000;S3sp03SSW1c".
  Lemma shadow_aok : forall c x, CS c -> (x = 0x7fff8000 + c / 8)%Z -> aok_addr AL CS x.
  Proof. intros c x Hc ->. right; left. exists c. split; [exact Hc|]. unfold shadow_of. rewrite ASB. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L19627418368.38L24890867569.42L3515141888.38 L5268879960.38 L60692804685.43L61028780023.40L61028787006.38L63368316460.41L63368316718.39L67812584585.3800000F00O00e01001Y01b01k02402=02KS3sp04SPlo3SSW2S41z2HzS3sp03SSWS3sp04SPlo3SSW2S41z2HzS3sp03SSW1zS3sp04SPlo3SSW2S12S22S41z2Hz2H02H12H23D16S3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSWS3sp03SSW1z2Hz".
  Lemma D_DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
  Proof.
    intros a H. unfold D in H. eapply (Dimg_DOK_aok AL CS IMG); [|exact H].
    repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
    - intros z Hz. left. apply WCS. lia.
    - intros z Hz. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply FCS; lia|]. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - intros z Hz. destruct (ssh_app sp0 z ltac:(lia) SPal Hz) as [A1 A2]. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply WCS; lia| exact A2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L22864299158.35L24994215446.35L3891981915.35 L60918251839.3500000900B00N00\S3sp03SSWS3sp03SSWS3sp03SSW2S4S3sp04SPlo3SSW".
  Lemma D_D0 : D (Z_to_bv 64 0) = false.
  Proof. pose proof SSH_facts. pose proof SPlo. unfold D. apply Dimg_D0. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.

  Definition RRUN := rz_runA RSEGS D AL CS KI K_halted K_mat D_Dseg asegs_top D_DOK D_D0.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L30901545954.35L46534914516.35L60924549197.3500000Q00_00mS3sp04SPlo3SSW2lo2hi3Hlo3Hhi1z2HzS3sp04SPhi3SSWS3sp04SPlo3SSW".
  Lemma D_frame : forall lo hi, (bv_unsigned sp0 - 4096 <= lo)%Z -> (hi <= bv_unsigned sp0)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply (Dimg_cov _ (bv_unsigned sp0 - 4096) (bv_unsigned sp0)); [left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40646207469.3500000QS3sp04SPlo3SSW2lo2hi3Hlo3Hhi1z2Hz".
  Lemma D_img : forall lo hi, (0x10000 <= lo)%Z -> (hi <= 0x65f000)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply Dimg_img. unfold AIMG_LO, AIMG_HI. lia. Qed.
  Lemma D_fsh : DcovZ D 0x7fffb720 0x7fffb730.
  Proof. intros z Hz. unfold D. eapply Dimg_cov; [right; left; reflexivity | lia | lia | lia]. Qed.
  Lemma D_ssh : DcovZ D (SSH_LO sp0) (SSH_HI sp0).
  Proof. pose proof SSH_facts. intros z Hz. unfold D. eapply Dimg_cov; [right; right; left; reflexivity | lia | lia | lia]. Qed.

  (* [comment removed for export] *)
  Definition valsRF : list word := [sp0] ++ junk_vals R ++ [can] ++ repeat (Z_to_bv 64 0) 8.
  Let E : env := Env (vals_ev valsRF) (blobs_ev []).

  Lemma valsRF_len : length valsRF = 42%nat.
  Proof. unfold valsRF. rewrite !length_app, junk_vals_length. reflexivity. Qed.
  Lemma vP0 : vals_ev valsRF 0 = sp0. Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Definition LITS_KND : list (Z * Z) := [(0x10000, 0x65f000)%Z; (0x7fffb720, 0x7fffb730)%Z].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L43821501577.34L51855111613.30L59283940997.3400000@00I00YS3sp03SSW2hi3HhiS3sp03SSWS3sp03SSW2lo3Hlo".
  Lemma KND : forall kn, Forall (kentry_inD D E) (knd_residual (-4096) LITS_KND kn) -> kn_inD D E kn.
  Proof.
    apply (kn_inD_residual D E sp0 (-4096) LITS_KND).
    - exact vP0.
    - intros lo hi Hlo Hhi. apply D_frame; lia.
    - repeat (apply Forall_cons; [cbn [fst snd] |]); [apply D_img; lia | exact D_fsh | apply Forall_nil].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18267881737.34L5599869189.34 00000A00RS3sp03SSW3qhi3HhiS3sp03SSW3qlo3Hlo".
  Lemma D_frameS : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "Pqlo,$1.Pqhi,$1.P,(3.(4.(5.&40.Vsp0,)-1000.)R2.)P,(3.R2.(5.&40.Vsp0,))(30.VD,R4.R3.)")
(* [comment removed for export] *).
  Proof. intros qlo qhi Hlo Hhi. apply D_frame; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L38995425597.30L4957445309.30 L51855111613.30L54869566397.30L58753121597.3000000100:00C00D00MFS3sp03SSWS3sp03SSWFS3sp03SSW".
  Lemma HLITS_KND : Forall (fun iv => DcovZ D (fst iv) (snd iv)) LITS_KND.
  Proof. unfold LITS_KND. repeat (apply Forall_cons; [cbn [fst snd] |]); [ .. | apply Forall_nil]; first [ apply D_img; lia | exact D_fsh ]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54434931423.30000009S3sp03SSW".
  Lemma vP33 : vals_ev valsRF 33 = can.
  Proof. unfold valsRF, vals_ev. change ([sp0] ++ junk_vals R ++ [can] ++ repeat (Z_to_bv 64 0) 8) with (([sp0] ++ junk_vals R) ++ ([can] ++ repeat (Z_to_bv 64 0) 8)).
    rewrite app_nth2; [|rewrite length_app, junk_vals_length; cbn; lia].
    rewrite length_app, junk_vals_length. reflexivity. Qed.
  Lemma vPz : forall n, (34 <= n)%nat -> vals_ev valsRF n = Z_to_bv 64 0.
  Proof.
    intros n Hn. unfold valsRF, vals_ev.
    change ([sp0] ++ junk_vals R ++ [can] ++ repeat (Z_to_bv 64 0) 8) with (([sp0] ++ junk_vals R ++ [can]) ++ repeat (Z_to_bv 64 0) 8).
    rewrite app_nth2 by (rewrite !length_app, junk_vals_length; cbn; lia).
    rewrite !length_app, junk_vals_length. cbn [length Nat.add].
    destruct (Nat.lt_ge_cases (n - 34) 8) as [Hl|Hg]; [apply nth_repeat | rewrite nth_overflow by (rewrite repeat_length; lia); reflexivity].
  Qed.
  Lemma vPz_app : forall extra n, (34 <= n < 42)%nat -> vals_ev (valsRF ++ extra) n = Z_to_bv 64 0.
  Proof. intros extra n Hn. rewrite vals_ev_app_l by (rewrite valsRF_len; lia). apply vPz. lia. Qed.
  Ltac evs := unfold E; cbn [ev eb]; rewrite ?vals_ev_app_l by (rewrite valsRF_len; lia); rewrite ?vP0, ?vP33, ?vPz by lia.

  Lemma evP1_junk : forall i, (i < 32)%nat -> ev E (1 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E. cbn [ev]. unfold valsRF.
    change (1 + i)%nat with (length [sp0] + i)%nat.
    unfold vals_ev. cbn [app length Nat.add]. change (S i) with (length [sp0] + i)%nat.
    change (sp0 :: junk_vals R ++ can :: repeat (Z_to_bv 64 0) 8) with ([sp0] ++ (junk_vals R ++ (can :: repeat (Z_to_bv 64 0) 8))). rewrite app_nth2_plus. rewrite app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma regs_okRF : regs_ok E sr_RF R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_RF all_regs];
      first [ (cbn [edenot]; first [ reflexivity | exact G3 | exact G4 | (evs; exact G2) ])
            | (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                 change (edenot E (EVar n)) with (ev E n); rewrite (evP1_junk (n - 1)) by lia; reflexivity end) ].
  Qed.

  (* [comment removed for export] *)
  Lemma shw_denot : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "Pvals,(12.(0.&40.))Pk,$1.P,(6.(0.&40.)(31.R2.#0.)Vsp0,)P,(2.(3.-1000.R2.)(3.R2.=))(6.$1.(5.&40.(1;.(32.(31.R4.)(33.(34.(12.(0.&8.)))))(35.$36.(35.$37.(35.$38.(35.$37.(39.#0.)(3:.R3.))(3:.+3.))(3:.+7???8000.))(3:.-8.))))(3;.Vsp0,R3.))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo. pose proof SPhi.
    intros vals k V0 Hk. cbn [edenot ev]. rewrite V0.
    rewrite alu_and. rewrite alu_add. rewrite alu_srl. rewrite (alu_add sp0).
    unfold v_and, v_add, v_srl.
    replace (bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + bv_unsigned (Z_to_bv 64 k))))%Z with (bv_unsigned sp0 + k)%Z.
    2:{ rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
        rewrite Zplus_mod_idemp_r. symmetry. apply Z.mod_small. lia. }
    rewrite (unsigned_lit 3) by lia. change (3 mod 64)%Z with 3%Z. rewrite Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
    pose proof (Z.div_pos (bv_unsigned sp0 + k) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (bv_unsigned sp0 + k) 8 (2^45) ltac:(lia) ltac:(lia)).
    rewrite (unsigned_lit ((bv_unsigned sp0 + k) / 8)) by lia. rewrite (unsigned_lit 2147450880) by lia.
    rewrite (unsigned_lit ((bv_unsigned sp0 + k) / 8 + 2147450880)) by lia.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with 18446744073709551608%Z by reflexivity.
    rewrite A_rip.land_m8 by lia. rewrite unsigned_lit.
    2:{ pose proof (Z.mod_pos_bound ((bv_unsigned sp0 + k) / 8 + 2147450880) 8 ltac:(lia)). lia. }
    unfold SHW. lia.
  Qed.
  Lemma shw_denotE : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "Pk,$1.P,(2.(3.-1000.R1.)(3.R1.=))(6.$1.(5.&40.(1;.VE,(35.$36.(35.$37.(35.$38.(35.$37.(39.#0.)(3:.R2.))(3:.+3.))(3:.+7???8000.))(3:.-8.))))(3;.Vsp0,R2.))")
(* [comment removed for export] *).
  Proof. intros k Hk. unfold E. apply shw_denot; [reflexivity | exact Hk]. Qed.

  Lemma adenot_of_estart : forall a, flat E a 8 -> adenot E a = Z_to_bv 64 (estart E a).
  Proof. intros a Hf. rewrite <- (flat_u E a 8 Hf). symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Lemma know_okRF : know_ok RSEGS E M kn_RF.
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal.
    pose proof TM as TM'. destruct TM' as [WIN RO ERR CAN RTC ZI ZS _ _ _ _ _ _ _ _ _ _ _ _].
    assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
    { intros off n A B C. apply flat_abs0; lia. }
    unfold know_ok, kn_RF.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    all: try (split; [lia|]; split; [apply FL; lia|]; rewrite adenot_lit0; cbn [edenot];
              first [ exact CAN
                    | (apply (rtc_rdn1 _ _ _ RTC); rtc_in)
                    | (apply (rtc_rdn8 _ _ _ RTC); rtc_in)
                    | (eapply (zrun_rdn8 _ _ _ _ ZI); cbv -[Z.le]; lia) ]).
    all: first
      [ (* [comment removed for export] *) split; [lia|]; cbn [edenot]; evs; assumption
      | (* [comment removed for export] *) cbn [edenot]; evs; lia
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot]; evs; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off]; cbn [edenot]; evs;
        apply store_ok_of_all; rewrite u_small by lia; [lia|]; intros x Hx; apply WIN; lia
      | (* [comment removed for export] *) split; [lia|]; split; [lia|]; intros i Hi; first [apply RO; lia | apply ERR; lia]
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia;
        apply store_ok_data; rewrite u_small by lia; lia
      | match goal with |- ?g => idtac "KNOWN-GOAL-LEFT:" g end ].
  Qed.

  (* [comment removed for export] *)
  Ltac covtac :=
    try (unfold estart, elenZ; cbn [a_base a_off]);
    first [ exact I
          | cbn [edenot]; evs; rewrite ?(u_small 0) by lia; intros z Hz;
            first [ apply (D_img z (z + 1)); lia | apply (D_frame z (z + 1)); lia | apply D_fsh; lia ] ].

  (* [comment removed for export] *)
  Lemma rdn_of_rst : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "PMM,P,(0.&40.)(11.(0.&8.))Pa,(0.&40.)Pn,$15.Pbs,(12.(0.&8.))P,(6.(11.(12.(0.&8.)))(1=.$17.(3<.VD,R4.)R3.R2.)(19.(12.(0.&8.))R1.))P,(3.(4.(5.&40.R4.)(1<.R3.))(;.+2.+40.))P,(30.VD,(5.&40.R5.)(4.(5.&40.R5.)(1<.R4.)))(6.(11.(12.(0.&8.)))(1=.$17.R7.R6.R5.)(19.(12.(0.&8.))R4.))")
(* [comment removed for export] *).
  Proof. intros MM a n bs H Hnw HD. rewrite <- (rdn_restrict_in RSEGS D MM a n Hnw HD). exact H. Qed.

  Lemma alu_add_zlit : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "Px,(0.&40.)Pk,$1.P,(2.(3.=(4.(5.&40.R2.)R1.))(<.(4.(5.&40.R2.)R1.)(;.+2.+40.)))(6.(0.&40.)(3=.$37.R3.(1>.&40.R2.))(1>.&40.(4.(5.&40.R3.)R2.)))")
(* [comment removed for export] *).
  Proof.
    intros x k Hk. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma and3_lit : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "Pk,$1.P,(2.(3.-1000.R1.)(3.R1.=))(6.$20.(21.&40.(3=.$36.(1>.&40.(4.(5.&40.Vsp0,)R2.))(1>.&40.+3.))(1>.&40.=))(3>.(7.R2.+4.)=))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo. pose proof SPhi.
    intros k Hk. rewrite alu_and. unfold v_and. rewrite (unsigned_lit 3), (unsigned_lit (bv_unsigned sp0 + k)) by lia.
    rewrite land3_mod4 by lia. pose proof (Z.mod_pos_bound (bv_unsigned sp0 + k) 4 ltac:(lia)).
    unfold bv_eqb. rewrite !unsigned_lit by lia. apply (mod4_of_sp (bv_unsigned sp0) k); [exact SPal | lia | reflexivity].
  Qed.
  (* [comment removed for export] *)
  Lemma not_ltu_small : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "Px,$1.Pn,$1.P,(2.(3.=R2.)(<.R2.(;.+2.+30.)))P,(2.(3.=R2.)(<.R2.(;.+2.+10.)))(6.$20.(3?.&40.(1>.&40.(40.(5.&40.(1>.&40.R4.))(5.&40.(1>.&40.-1.))))(1>.&40.R3.))$24.)")
(* [comment removed for export] *).
  Proof.
    intros x n Hx Hn. rewrite (unsigned_lit x) by lia. replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z by reflexivity.
    rewrite zb_lxor_ones by lia. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac solve_sc :=
    cbn [sc_denot branch_taken];
    first
      [ (* [comment removed for export] *)
        lazymatch goal with |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off];
          rewrite !shw_denotE by lia;
          lazymatch goal with |- context [SHW sp0 ?k] =>
            pose proof (SHW_range sp0 k ltac:(lia) SPal ltac:(lia)); pose proof SSH_facts end;
          cbn [edenot]; rewrite ?(u_small 8), ?(u_small 4), ?(u_small 0) by lia; lia end
      | (* [comment removed for export] *)
        lazymatch goal with |- exists bs, rdn _ _ _ _ = Some bs /\ _ =>
          exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
          [ lazymatch goal with |- rdn _ _ (adenot _ (SA ?e 0)) 8 = _ =>
              unfold adenot, v_addi; cbn [a_base a_off]; rewrite Z.add_0_r;
              lazymatch e with context [ELit ?k] =>
                rewrite (shw_denotE k) by lia;
                pose proof (SHW_range sp0 k ltac:(lia) SPal ltac:(lia)); pose proof SSH_facts;
                apply (RestrictRun.rdn_restrictD RSEGS D);
                [ eapply (zrun_rdn8 _ _ _ _ (tm_zstk _ _ _ _ _ _ _ _ TM)); lia
                | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                | rewrite u_small by lia; intros z Hz; apply D_ssh; cbn in Hz; lia ] end end
          | cbn [edenot]; evs; vm_compute; reflexivity ] end
      | cbn [edenot]; evs; rewrite ?alu_add_zlit by lia;
        first
          [ (* [comment removed for export] *) apply Bool.negb_true_iff; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia
          | (* [comment removed for export] *)
            unfold bv_eqb, bv_ltu; rewrite !unsigned_lit by lia; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Bool.negb_false_iff; apply Z.ltb_lt]; lia
          | (* [comment removed for export] *) rewrite and3_lit by lia; reflexivity
          | (* [comment removed for export] *) rewrite alu_or; unfold v_or; rewrite !unsigned_lit by lia; reflexivity
          | (* [comment removed for export] *) rewrite alu_and, alu_or; unfold v_and, v_or; apply rf_memset_align_false'; lia
          | (* [comment removed for export] *) rewrite alu_xor; unfold v_xor; apply not_ltu_small; lia ]
      | match goal with |- ?g => idtac "SC-LEFT:" g end ].

  Theorem refused_tailA : ltac2:(CDefT.buildp (gd_tbl_A_refused ()) "(41.$17.(42.(43.$44.VR,(1>.&40.+97328.)VM,(45.$17.))Vmodel,)(46.$47.(48.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SSH_facts as SSF.
    pose proof regs_okRF as HR. pose proof know_okRF as HK.
    unfold t_die.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try clear KNDc.
    lazymatch goal with HRx : regs_ok ?EE _ _ |- _ => let EE2 := eval unfold E in EE in lazymatch EE2 with Env (vals_ev ?Vx) ?bb => pose proof (kn_inD_residual D (Env (vals_ev Vx) bb) sp0 (-4096) LITS_KND ltac:(cbn [ev]; first [ exact vP0 | rewrite ?vals_ev_app_l by (rewrite ?length_app, ?junk_vals_length, ?valsRF_len; cbn; lia); exact vP0 ]) D_frameS HLITS_KND) as KNDc end end.
    run_blockA3 RRUN KNDc FUEL_RF STOPS_RF scrRA 34%nat true covtac.
    all: try solve_sc.
    rename EQM into EQMA. rename OUT into OUTA. rename R0 into RA. rename M0 into MA0. rename HKmo into HKA. rename MM into MMA.
    (* [comment removed for export] *)
    unfold W.
    change (map (WriteEv (Z_to_bv 64 2)) msg_refused) with (map (WriteEv (Z_to_bv 64 (sc_fd resC))) (msg_refused ++ [])).
    assert (FdA : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
    { unfold m_fds in *. destruct MMA as (E1 & _). rewrite E1. exact Hfd2. }
    pose proof itinerary_rf as (_ & SC & _ & _).
    eapply (stdio_call_sound_frA AL CS KI IMG K_halted K_mat K_vmonly valsRF (blobs_ev []) srA knA RA MA0 mo resC msg_refused []
              (t_exit (exit_code 2) (m_fs model)) HR HK);
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resC edenot];
      change (@length byte msg_refused) with 38%nat; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
    + rewrite valsRF_len. exact SC.
    + evs. rewrite !alu_add_zlit by lia. rewrite !u_small by lia. lia.
    + evs. rewrite !alu_add_zlit by lia. rewrite !u_small by lia. lia.
    + reflexivity.
    + cbn. lia.                                                    (* [comment removed for export] *)
    + right. evs. rewrite !alu_add_zlit by lia. rewrite !u_small by lia. lia.
    + left. evs. rewrite !alu_add_zlit by lia. rewrite !u_small by lia. lia.
    + rewrite !u_small by lia. lia.
    + evs. rewrite !alu_add_zlit by lia. rewrite !u_small by lia. lia.   (* [comment removed for export] *)
    + rewrite !u_small by lia. lia.                                      (* [comment removed for export] *)
    + (* [comment removed for export] *)
      evs. rewrite alu_add_zlit by lia. rewrite u_small by lia.
      rewrite <- msgZ_msg.
      pose proof (kread_bytes_rdn _ MA0 knA (EVar 0) 38 (-464) msgZ HK msgZ_eq msgZ_range) as RD.
      cbn [edenot] in RD. change (ev E 0) with sp0 in RD. apply RD; lia.
    + reflexivity.
    + exact FdA.
    + exact HKA.
    + intros z Hz. revert Hz. evs. rewrite alu_add_zlit by lia. rewrite !u_small by lia. intros Hz. apply WCS. lia.
    + intros z Hz. revert Hz. evs. rewrite !alu_add_zlit by lia. rewrite !u_small by lia. intros Hz. left. apply WCS. lia.
    + intros z Hz. rewrite !u_small in Hz by lia. lia.
    + unfold t_exit. apply t_emit_has_nil.
    + (* [comment removed for export] *)
      intros Rm MC moC HPOST HRm HKm HKC MMC. clear HR HK. rename HRm into HR. rename HKm into HK.
      (* [comment removed for export] *)
      try clear KNDc.
      lazymatch goal with HRx : regs_ok ?EE _ _ |- _ => let EE2 := eval unfold E in EE in lazymatch EE2 with Env (vals_ev ?Vx) ?bb => pose proof (kn_inD_residual D (Env (vals_ev Vx) bb) sp0 (-4096) LITS_KND ltac:(cbn [ev]; first [ exact vP0 | rewrite ?vals_ev_app_l by (rewrite ?length_app, ?junk_vals_length, ?valsRF_len; cbn; lia); exact vP0 ]) D_frameS HLITS_KND) as KNDc end end.
      run_blockA3 RRUN KNDc FUEL_RF STOPS_RF scrC 74%nat true covtac.
      all: try solve_sc.
      lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into RC; rename Mn into MD end.
      rename EQM into EQMC. rename OUT into OUTC. rename HKmo into HKD. rename MM into MMD.
      (* [comment removed for export] *)
      apply (srzJ_getr_ext RSEGS
               (mkR (getr RC (Z_to_bv 5 1)) sp0 (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90)
                    (getr RC (Z_to_bv 5 5)) (getr RC (Z_to_bv 5 6)) (getr RC (Z_to_bv 5 7)) (getr RC (Z_to_bv 5 8)) (getr RC (Z_to_bv 5 9))
                    (getr RC (Z_to_bv 5 10)) (getr RC (Z_to_bv 5 11)) (getr RC (Z_to_bv 5 12)) (getr RC (Z_to_bv 5 13))
                    (getr RC (Z_to_bv 5 14)) (getr RC (Z_to_bv 5 15)) (getr RC (Z_to_bv 5 16)) (getr RC (Z_to_bv 5 17))
                    (getr RC (Z_to_bv 5 18)) (getr RC (Z_to_bv 5 19)) (getr RC (Z_to_bv 5 20)) (getr RC (Z_to_bv 5 21))
                    (getr RC (Z_to_bv 5 22)) (getr RC (Z_to_bv 5 23)) (getr RC (Z_to_bv 5 24)) (getr RC (Z_to_bv 5 25))
                    (getr RC (Z_to_bv 5 26)) (getr RC (Z_to_bv 5 27))
                    (getr RC (Z_to_bv 5 28)) (getr RC (Z_to_bv 5 29)) (getr RC (Z_to_bv 5 30)) (getr RC (Z_to_bv 5 31))) RC).
      { intros r. pose proof (ridx_range r) as Hi.
        rewrite <- (ridx_roundtrip r). set (i := ridx r) in *. clearbody i.
        destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
          [ .. | lia];
          lazymatch goal with |- _ = getr RC (Z_to_bv 5 (Z.of_nat ?k)) =>
            first
              [ (transitivity (getr RC (Z_to_bv 5 (Z.of_nat k))); [reflexivity|reflexivity])
              | rewrite (HR (Z_to_bv 5 (Z.of_nat k)));
                lazymatch goal with |- _ = edenot _ (sr_get ?L ?rr) =>
                  let e := eval vm_compute in (sr_get L rr) in change (sr_get L rr) with e end;
                cbn [edenot];
                first [ reflexivity
                      | (lazymatch goal with |- _ = ev _ ?n =>
                           change (ev _ n) with (vals_ev (valsRF ++ junk_vals Rm) n);
                           rewrite vals_ev_app_l by (rewrite valsRF_len; lia);
                           change (vals_ev valsRF n) with sp0; reflexivity end) ] ]
          end. }
      change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
      lazymatch goal with |- srealizesJ _ (mkCfg _ ?mox) _ => rewrite <- (mo_mat_fs model mox) end.
      2:{ eapply mo_mat_trans; [exact MMA|]. eapply mo_mat_trans; [exact MMC|]. exact MMD. }
      apply (die2_at_96e04 AL CS KI IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly sp0 SPlo SPhi SPal WCS
               M can tid wp0 rp0 wp1 rp1 TM); [| exact HKD].
      (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      cbn [sc_sp sc_f sc_bufp sc_bufsz resC edenot] in Pagree, Pwend, Pwpos, Pwbase.
      unfold E in Pagree. cbn [ev] in Pagree. rewrite vP0 in Pagree. rewrite alu_add_zlit in Pagree by lia. rewrite !u_small in Pagree by lia.
      assert (AG : forall x : word,
                 ~ (bv_unsigned sp0 - 4096 <= bv_unsigned x < bv_unsigned sp0)%Z ->
                 ~ (0x0fa488 <= bv_unsigned x < 0x0fa570)%Z -> MD x = M x).
      { intros x N1 N2. pose proof (u64_range x).
        destruct (D x) eqn:Dx.
        - rewrite <- (restrict_in D MD x Dx). rewrite EQMC. rewrite mem_denot_out.
          2:{ apply (log_out_in2 _ 0 (-4096) 0 0x0fa488 0x0fa570); [vm_compute; reflexivity | evs; lia | evs; lia | lia | lia | evs; intros ?; apply N1; lia | exact N2]. } (* [comment removed for export] *)
          rewrite (restrict_in D MC x Dx). rewrite Pagree by lia.
          rewrite <- (restrict_in D MA0 x Dx). rewrite EQMA. rewrite mem_denot_out.
          2:{ apply (log_out_in2 _ 0 (-4096) 0 0x0fa488 0x0fa570); [vm_compute; reflexivity | evs; lia | evs; lia | lia | lia | evs; intros ?; apply N1; lia | exact N2]. } (* [comment removed for export] *)
          apply (restrict_in D M x Dx).
        - assert (ND : forall lo hi, DcovZ D lo hi -> ~ (lo <= bv_unsigned x < hi)%Z).
          { intros lo hi Hc Hin. specialize (Hc (bv_unsigned x) Hin). rewrite Z_to_bv_bv_unsigned in Hc. congruence. }
          rewrite (OUTC x Dx). rewrite Pagree.
          2:{ apply (ND _ _ (D_frame (bv_unsigned sp0 - 480 - 112) (bv_unsigned sp0 - 480) ltac:(lia) ltac:(lia))). }
          2:{ apply (ND _ _ (D_img (0x0fa488 + 32) (0x0fa488 + 48) ltac:(lia) ltac:(lia))). }
          2:{ apply (ND _ _ (D_img (0x0fa488 + 56) (0x0fa488 + 64) ltac:(lia) ltac:(lia))). }
          apply (OUTA x Dx). }
      assert (GR : mem_grows M MD).
      { eapply mem_grows_trans; [eapply (grows_of_rst D); [exact EQMA | exact OUTA]|].
        eapply mem_grows_trans; [exact Pgrows|]. eapply (grows_of_rst D); [exact EQMC | exact OUTC]. }
      split.
      * exact AG.
      * intros x Hout. cbn [outside] in Hout. destruct Hout as (O1 & O2 & _). apply AG; lia.
      * exact GR.
      * apply mem_grows_wmono. exact GR.
      * (* [comment removed for export] *)
        krd HK (0x0fa488 + 140)%Z 4%nat F140. krd HK (0x0fa488 + 40)%Z 8%nat F40. krd HK (0x0fa488 + 56)%Z 8%nat F56.
        krd HK (0x0fa488 + 8)%Z 8%nat F8. krd HK (0x0fa488 + 16)%Z 8%nat F16.
        eexists. eexists. unfold file_clean. repeat split.
        -- exact F140.
        -- rewrite F40. reflexivity.
        -- rewrite F56. reflexivity.
        -- rewrite F8. reflexivity.
        -- rewrite F16. reflexivity.
  Qed.
End RF.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

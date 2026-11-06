(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed g6.

(* [comment removed for export] *)
Module DrvRGlue.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "SLit"; "eval"; "rm"; "cell"; "rl"; "rw"; "ss_objs"; "mkObj"; "obj_holds"; "ss_facts"; "SAlu"; "holds"; "obj_hi_of"; "obj_lo_of"; "sv_eqb"; "DList"; "DUnknown"; "c_off"; "c_val"; "c_width"; "ob_base"; "ob_cells"; "obj_range"; "soff"; "SPBranch"; "SPNot"; "SVar"; "ob_dflt"; "odefault"; "sprop"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Corelib.Init.Datatypes"; "list"; "andb"; "bool"; "true"; "option"; "prod"; "pair"; "Some"; "cons"; "nil"; "nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "SHADOW_OFF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "modulo"; "pow"; "sub"; "eqb"; "leb"; "ltb"; "div"; "mul"; "land"; "lor"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vTP"; "clen_of"; "flags_of"; "hdr_word"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "Forall2"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "obj_clear_litb2"; "tv_bandfree"; "obj_clear_litb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states"; "errL"; "errL_okb"; "clen_x"; "errL0"; "errL0_okb"; "errV"; "errV0"; "errV0_okb"; "errV_okb"; "flg_x"; "has_tpfact"; "ob_shape0b"; "plen_x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.ErrnoA"; "errno_blind"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "JA"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "errno_addrA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "ALU_OR"; "ALU_SRL"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g7.DrvRGlue"; "pub_lit_okb"; "pub_lit_okb2"; "pub_sym_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates"; "ms16_at"; "x4_okb"; "x4d_okb"; "x4set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bxt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code DrvJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.DrvJRe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.ErrnoA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvErrno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma ob_shape0b_sound : ltac2:(tb__ "0|0|
S9S7S7S7S0S2dS6dR4R3R2R1A4S2eA3S0S9R5S11R4R3R2S34SdA1S1aA5A3F_;Fhi;Flo;Fb;Fo;").
Proof.
  intros [ob ol oh oc od] b lo hi H. unfold ob_shape0b in H. cbn in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3. subst.
  destruct oc; [|discriminate]. destruct od; try discriminate. reflexivity.
Qed.

Lemma has_tpfact_holds : ltac2:(tb__ "0|0|
S39S8S0S2dS6cR2A1S2eA3S76S27S15R2A1S13S3aR3A1A1A3S0S4S37Q40SbR3S53A2A2S5eA3F_;F_;Frho;FE;").
Proof.
  intros E rho H HF. unfold has_tpfact in H. pose proof (holds_mem _ _ _ HF H) as X. cbn [holds] in X.
  unfold vTP in X |- *. rewrite X. rewrite U_lit. reflexivity.
Qed.

Lemma SPA_errV0 : ltac2:(tb__ "0|0|
S2aS8S39S2bS36Q40A1A1S4eS0S2dS69R3A1S2eA3S29S6R6R4R5R3R2A6S29S6R7S68R5A1R6R4R3A6F_;F_;Fw;Ftp;FE;Frho;FJ;").
Proof.
  intros J rho E tp w H HS. unfold errV0_okb in H. apply andb_prop in H as [H Htp]. apply andb_prop in H as [Hn Hsame].
  destruct (nth_error (ss_objs (ax_S E)) (ierrL E)) as [o|] eqn:En; [|discriminate].
  apply ob_shape0b_sound in Hn. subst o.
  pose proof (has_tpfact_holds E rho Htp (smatchA_facts segs _ _ _ _ (proj1 HS))) as HTP.
  unfold errV0. apply (SPA_reslice segs J rho E (ierrL E) _ O_errnoV tp w En); try reflexivity.
  - exact Hsame.
  - unfold O_errnoV, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small; unfold TP; try lia.
    rewrite HTP. cbn [eval]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. unfold TP. f_equal; lia.
  - unfold O_errnoV, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi]; rewrite !soff_lit_small; lia.
  - exact HS.
Qed.

Lemma SPA_errV : ltac2:(tb__ "0|0|
S2aS8S39S2bS36Q40A1A1S4eS0S2dS6aR3A1S2eA3S29S6R6R4R5R3R2A6S29S6R7S67R5A1R6R4R3A6F_;F_;Fw;Ftp;FE;Frho;FJ;").
Proof.
  intros J rho E tp w H HS. unfold errV_okb in H. apply andb_prop in H as [HC HV]. unfold errV.
  exact (SPA_errV0 J rho (errC E) tp w HV (SPA_errC J rho E tp w HC HS)).
Qed.

Lemma SPA_errL0 : ltac2:(tb__ "0|0|
S2aS8S39S2bS36Q40A1A1S4eS0S2dS66R3A1S2eA3S29S6R6R4R5R3R2A6S29S6R7S65R5A1R6R4R3A6F_;F_;Fw;Ftp;FE;Frho;FJ;").
Proof.
  intros J rho E tp w H HS. unfold errL0_okb in H. apply andb_prop in H as [H Htp]. apply andb_prop in H as [Hn Hsame].
  destruct (nth_error (ss_objs (ax_S E)) (ierrV E)) as [o|] eqn:En; [|discriminate].
  apply ob_shape0b_sound in Hn. subst o.
  pose proof (has_tpfact_holds E rho Htp (smatchA_facts segs _ _ _ _ (proj1 HS))) as HTP.
  unfold errL0. apply (SPA_reslice segs J rho E (ierrV E) _ O_errno tp w En); try reflexivity.
  - exact Hsame.
  - unfold O_errno, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small; unfold TP; try lia.
    rewrite HTP. cbn [eval]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. unfold TP. f_equal; lia.
  - unfold O_errno, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi]; rewrite !soff_lit_small; unfold TP; lia.
  - exact HS.
Qed.

Lemma errL_Ts : ltac2:(tb__ "0|3|
S4eOF_;S2aS39S4fS8S2bS36Q40M0A1M1A1S0S2dS63R4A1S2eA3S70R6A1S8S0S5G1F_;SfR1A1SfR5A1A3S0S5S2bS36Q8A1M2A1F_;SeR2A1SeR6A1A3G1S2S74S37G0R1A2A1A1S0S2fG2A1ScR5R2A2ScR9R2A2A3F_;Fa;S51S6RcS29S6RbS62RaA1R4R7A5R9A4F_;F_;F_;Frho1;S51S6R9S29S6R8R7R5R4A5R6A4F_;F_;F_;Ftp;Frho;FQ;FE;FJ;Fok;").
Proof.
  intros ok J E Q rho tp H HJ HT. unfold errL_okb in H. apply andb_prop in H as [HL HR].
  eapply triple_conseq; [intros w HS; exact (SPA_errL0 J rho E tp w HL HS) | intros w Hw; exact Hw |].
  apply (errR_T (triple segs ok) (fun P P' Q0 HP HTq => ltac:(eapply triple_conseq; [exact HP | intros w0 Hw0; exact Hw0 | exact HTq])) (fun A P Q0 => @triple_ex segs ok A P Q0) (fun X P Q0 => @triple_pure segs ok X P Q0) J (errL0 E) Q rho tp HR HJ).
  exact HT.
Qed.
Lemma errL_Te : ltac2:(tb__ "0|3|
S2aS39S4fS8S2bS36Q40M0A1M1A1S0S2dS63R4A1S2eA3S70R6A1S8S0S5G1F_;SfR1A1SfR5A1A3S0S5S2bS36Q8A1M2A1F_;SeR2A1SeR6A1A3G1S2S74S37G0R1A2A1A1S0S2fG2A1ScR5R2A2ScR9R2A2A3F_;Fa;S50S6S29S6RbS62RaA1R4R7A5R9A3F_;F_;F_;Frho1;S50S6S29S6R8R7R5R4A5R6A3F_;F_;F_;Ftp;Frho;FQ;FE;FJ;").
Proof.
  intros J E Q rho tp H HJ HT. unfold errL_okb in H. apply andb_prop in H as [HL HR].
  eapply etriple_conseq; [intros w HS; exact (SPA_errL0 J rho E tp w HL HS) | intros w Hw; exact Hw |].
  apply (errR_T (etriple segs) (fun P P' Q0 HP HTq => ltac:(eapply etriple_conseq; [exact HP | intros w0 Hw0; exact Hw0 | exact HTq])) (fun A P Q0 => @etriple_ex segs A P Q0) (fun X P Q0 => @etriple_pure segs X P Q0) J (errL0 E) Q rho tp HR HJ).
  exact HT.
Qed.

Lemma x4d_okb_sound : ltac2:(tb__ "0|4|
S2bS30S7S7A2M0A1M1S0S2dS80R1A1S2eA3S3S0G1R2S34G0A1M2A3S3S0G1R2S33G0S31S7S7S53SaS5eA1M3A4G2A3A3S0G1R2S33G0S31S7S7G3S53A4G2A3A3A2A2F_;Fd;").
Proof.
  intros [|[a b] [|]] H; try discriminate; [left; reflexivity|]. cbn in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2];
  apply sv_eqb_sound in H1; apply sv_eqb_sound in H2; subst; auto.
Qed.

Lemma SPA_x4set : ltac2:(tb__ "0|0|
S2aS8S39S7S2bS36Q40A1A1S4eS0S2dS7fR4R3A2S2eA3S29S6R7R5R6R3R2A6S29S6R8S81R5R6A2R7R4R3A6F_;F_;Fw;Ftp;Fe;FA;Frho;FJ;").
Proof.
  intros J rho A e tp w H HS. unfold x4_okb in H. apply andb_prop in H as [H Htp]. apply andb_prop in H as [Hwf Hd].
  destruct (state_diff (ax_S A) (ax_S (x4set e A))) as [[d [|]]|] eqn:E; try discriminate.
  pose proof (has_tpfact_holds A rho Htp (smatchA_facts segs _ _ _ _ (proj1 HS))) as HTP.
  assert (Htpe : eval rho vTP = eval rho (SLit TP)).
  { apply bv_eq. rewrite HTP. cbn [eval]. rewrite Z_to_bv_unsigned. reflexivity. }
  unfold x4set. apply (SPA_restate segs J rho A _ tp w d [] Hwf E).
  - reflexivity.
  - destruct (x4d_okb_sound d Hd) as [-> |[-> | ->]]; [constructor| |];
      (constructor; [cbn [fst snd] | constructor]); [exact Htpe | symmetry; exact Htpe].
  - constructor.
  - exact HS.
Qed.

Lemma ms16_shape_holds : ltac2:(tb__ "0|0|
S8S7S15R2S23S22S7aS14S77S14S78SaZ28A1R1A3SaZfA1A3SaZ0A1A3A1A2Fx;Frho;").
Proof.
  intros rho x. cbn [holds eval branch_taken]. intros HB.
  unfold bv_eqb in HB. apply Z.eqb_eq in HB.
  assert (U0 : bv_unsigned (alu64 ALU_AND (alu64 ALU_OR (Z_to_bv 64 40) (eval rho x)) (Z_to_bv 64 15)) = 0).
  { rewrite HB. rewrite lit_unsigned. reflexivity. }
  rewrite and_val, or_val_A, !lit_unsigned in U0. change (40 mod 2 ^ 64) with 40 in U0. change (15 mod 2 ^ 64) with 15 in U0.
  assert (T : Z.testbit (Z.land (Z.lor 40 (bv_unsigned (eval rho x))) 15) 3 = true).
  { rewrite Z.land_spec, Z.lor_spec. reflexivity. }
  rewrite U0 in T. cbn in T. discriminate.
Qed.
Lemma ms16_at_holds : ltac2:(tb__ "0|0|
S8S7S4S15R3S7eR2R1A2A2Fd;Fb;Frho;").
Proof. intros rho b d. exact (ms16_shape_holds rho (SAlu ALU_ADD b (SLit (- d)))). Qed.

Definition pub_lit_okb (A : axst) (B L : Z) : bool := ltac2:(tb__ "0|4|
S2cS2cS2cS2cS2cS2cS48Z0M0VB;A2S47S44VB;Z40M1A2G0A2A2S49G0VL;A2A2S47S44VL;G1A2G0A2A2S48S43VB;VL;A2M2S45Z2Z28A2A2A2S18S3cVA;A1SaS40A1A2A2S58S9S61S13S3aVA;A1M3A1S3fVB;A1S3fG2A1A3S10G3A1A3A2").

Lemma SPA_publish_lit : ltac2:(tb__ "0|3|
S2aS8S39S2bS36Q40M0A1A1S4eS4S4S0S2dS7bR5R2R1A3S2eA3S4S1S41S3fR4A1R1A2S42R1S3fS43R4R3A2A1A2A2S0S2fS36Q8M1A1M2A1ScR9S38G0R2A2A2S32G2S38G1Z0A2A2A3F_;Fz;S29S6R9R7R8R6R5A6S29S6RaS57R8S33S30S7S7A2S31S7S7SaR5A1SaR4A1A4S3bR8A1A3A2R9R7R6A6F_;F_;F_;FL;FB;Fw;Ftp;FA;Frho;FJ;").
Proof.
  intros J rho A tp w B L Hok Hz HS.
  unfold pub_lit_okb in Hok. apply andb_prop in Hok as [Hok HO]. apply andb_prop in Hok as [Hok Hb]. apply andb_prop in Hok as [Hok H5].
  apply andb_prop in Hok as [Hok H4]. apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2].
  apply Z.leb_le in H1. apply Z.eqb_eq in H2. apply Z.ltb_lt in H3. apply Z.eqb_eq in H4. apply Z.leb_le in H5. apply sv_eqb_sound in Hb.
  pose proof HS as [(Hsm & _) _].
  assert (HF : Forall (holds rho) (ss_facts (ax_S A))) by exact (smatch_facts_hold _ _ _ _ Hsm).
  assert (Hall : Forall (obj_holds segs rho (cfg_ms (snd (virt tp w)))) (ss_objs (ax_S A))).
  { destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
  assert (SHB : Sh B = SHADOW_OFF + B / 8) by (unfold Sh; lia).
  assert (SHE : Sh (B + L) = SHADOW_OFF + (B + L) / 8) by (unfold Sh; lia).
  assert (OUT : forall z, Sh B <= z < Sh (B + L) -> outside_all rho (ss_objs (ax_S A)) (Z_to_bv 64 z)).
  { intros z Hzr. apply (ranges_disjoint_outside rho _ (Sh B) (Sh (B + L))).
    - apply Forall_forall. intros o Ho.
      apply (obj_clear_litb_sound rho _ (ss_facts (ax_S A)) (Sh B) (Sh (B + L)) o (proj1 (Forall_forall _ _) Hall o Ho) HF);
        [unfold Sh, SHADOW_OFF; split; [lia | apply Z.add_le_mono_r; apply Z.div_le_mono; lia] | unfold Sh, SHADOW_OFF; pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5); lia |].
      exact (proj1 (forallb_forall _ _) HO o Ho).
    - rewrite lit_unsigned.
      rewrite Z.mod_small; [exact Hzr|]. unfold Sh, SHADOW_OFF in Hzr |- *. pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5). pose proof (Z.div_pos B 8). lia. }
  apply (SPA_x_publish segs J rho A (SLit B, SLit L) tp w); [reflexivity | | exact HS].
  rewrite Hb. unfold xr_ok. cbn [eval fst snd]. rewrite !lit_unsigned.
  rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia). rewrite (Z.mod_small B) by lia. rewrite (Z.mod_small L) by lia.
  split; [pose proof (Z.div_mod B 64 ltac:(lia)) as DB0; rewrite H2 in DB0; replace B with ((8 * (B / 64)) * 8) by lia; apply Z_mod_mult|].
  split; [lia|].
  intros a Ha.

  assert (W : forall j, 0 <= j < 8 -> Sh B <= (SHADOW_OFF + a / 8) / 8 * 8 + j < Sh (B + L)).
  { intros j Hj. rewrite SHB, SHE.
    pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
    assert (HB8 : B / 8 = 8 * (B / 64)) by (rewrite H2 in DB; nia).
    assert (HBL8 : (B + L) / 8 = 8 * (B / 64) + 8 * (L / 64)) by (rewrite H2 in DB; rewrite H4 in DL; nia).
    assert (LO : 8 * (B / 64) <= a / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HI : a / 8 < 8 * (B / 64) + 8 * (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_mod (a / 8) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (a / 8) 8 ltac:(lia)) as M3.
    assert (E8 : (SHADOW_OFF + a / 8) / 8 * 8 = SHADOW_OFF + (a / 8) / 8 * 8).
    { replace (SHADOW_OFF + a / 8) with ((268431360 + (a / 8) / 8) * 8 + (a / 8) mod 8) by (unfold SHADOW_OFF; lia).
      rewrite Z.div_add_l by lia. rewrite (Z.div_small ((a / 8) mod 8) 8) by lia. unfold SHADOW_OFF. lia. }
    rewrite E8.
    assert (LO2 : B / 64 <= (a / 8) / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HI2 : (a / 8) / 8 < (B / 64) + (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  assert (INa : Sh B <= SHADOW_OFF + a / 8 < Sh (B + L)).
  { rewrite SHB, SHE. split; [apply Z.add_le_mono_l; apply Z.div_le_mono; lia|].
    apply Z.add_lt_mono_l. pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    rewrite H2 in DB. rewrite H4 in DL. apply Z.div_lt_upper_bound; [lia|]. nia. }
  split; [unfold Sh, SHADOW_OFF in INa |- *; pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5); lia|].
  split; [unfold shadow_addr; apply OUT; exact INa|].
  split.
  - intros j Hj. unfold word_byte. split; [apply OUT; apply W; exact Hj|]. rewrite (Hz _ (W j Hj)). discriminate.
  - exists (Z_to_bv 8 0). split; [unfold shadow_addr; apply Hz; exact INa|]. left. reflexivity.
Qed.

Definition pub_lit_okb2 (A : axst) (tv : list (sv * sv)) (B L : Z) : bool := ltac2:(tb__ "0|4|
S2cS2cS2cS2cS2cS2cS48Z0M0VB;A2S47S44VB;Z40M1A2G0A2A2S49G0VL;A2A2S47S44VL;G1A2G0A2A2S48S43VB;VL;A2M2S45Z2Z28A2A2A2S18S3cVA;A1SaS40A1A2A2S58S9S5fS13S3aVA;A1M3A1Vtv;S3fVB;A1S3fG2A1A4S10G3A1A3A2").

Lemma SPA_publish_lit2 : ltac2:(tb__ "0|4|
S2aS8S39S2bS30S7S7A2M0A1S2bS36Q40M1A1A1S4eS4S4S0S2dS7cR6R5R2R1A4S2eA3S60R8R6A2S4S1S41S3fR5A1R1A2S42R1S3fS43R5R4A2A1A2A2S0S2fS36Q8M2A1M3A1ScRbS38G1R2A2A2S32G3S38G2Z0A2A2A3F_;Fz;S29S6RbR9RaR7R6A6S29S6RcS57RaS33G0S31S7S7SaR6A1SaR5A1A4S3bRaA1A3A2RbR8R7A6F_;F_;F_;F_;FL;FB;Fw;Ftp;Ftv;FA;Frho;FJ;").
Proof.
  intros J rho A tv tp w B L Hok HTV Hz HS.
  unfold pub_lit_okb2 in Hok. apply andb_prop in Hok as [Hok HO]. apply andb_prop in Hok as [Hok Hb]. apply andb_prop in Hok as [Hok H5].
  apply andb_prop in Hok as [Hok H4]. apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2].
  apply Z.leb_le in H1. apply Z.eqb_eq in H2. apply Z.ltb_lt in H3. apply Z.eqb_eq in H4. apply Z.leb_le in H5. apply sv_eqb_sound in Hb.
  pose proof HS as [(Hsm & _) _].
  assert (HF : Forall (holds rho) (ss_facts (ax_S A))) by exact (smatch_facts_hold _ _ _ _ Hsm).
  assert (Hall : Forall (obj_holds segs rho (cfg_ms (snd (virt tp w)))) (ss_objs (ax_S A))).
  { destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
  assert (SHB : Sh B = SHADOW_OFF + B / 8) by (unfold Sh; lia).
  assert (SHE : Sh (B + L) = SHADOW_OFF + (B + L) / 8) by (unfold Sh; lia).
  assert (OUT : forall z, Sh B <= z < Sh (B + L) -> outside_all rho (ss_objs (ax_S A)) (Z_to_bv 64 z)).
  { intros z Hzr. apply (ranges_disjoint_outside rho _ (Sh B) (Sh (B + L))).
    - apply Forall_forall. intros o Ho.
      apply (obj_clear_litb2_sound rho _ (ss_facts (ax_S A)) tv (Sh B) (Sh (B + L)) o (proj1 (Forall_forall _ _) Hall o Ho) HF);
        [unfold Sh, SHADOW_OFF; split; [lia | apply Z.add_le_mono_r; apply Z.div_le_mono; lia] | unfold Sh, SHADOW_OFF; pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5); lia | exact HTV |].
      exact (proj1 (forallb_forall _ _) HO o Ho).
    - rewrite lit_unsigned.
      rewrite Z.mod_small; [exact Hzr|]. unfold Sh, SHADOW_OFF in Hzr |- *. pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5). pose proof (Z.div_pos B 8). lia. }
  apply (SPA_x_publish segs J rho A (SLit B, SLit L) tp w); [reflexivity | | exact HS].
  rewrite Hb. unfold xr_ok. cbn [eval fst snd]. rewrite !lit_unsigned.
  rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia). rewrite (Z.mod_small B) by lia. rewrite (Z.mod_small L) by lia.
  split; [pose proof (Z.div_mod B 64 ltac:(lia)) as DB0; rewrite H2 in DB0; replace B with ((8 * (B / 64)) * 8) by lia; apply Z_mod_mult|].
  split; [lia|].
  intros a Ha.

  assert (W : forall j, 0 <= j < 8 -> Sh B <= (SHADOW_OFF + a / 8) / 8 * 8 + j < Sh (B + L)).
  { intros j Hj. rewrite SHB, SHE.
    pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
    assert (HB8 : B / 8 = 8 * (B / 64)) by (rewrite H2 in DB; nia).
    assert (HBL8 : (B + L) / 8 = 8 * (B / 64) + 8 * (L / 64)) by (rewrite H2 in DB; rewrite H4 in DL; nia).
    assert (LO : 8 * (B / 64) <= a / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HI : a / 8 < 8 * (B / 64) + 8 * (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_mod (a / 8) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (a / 8) 8 ltac:(lia)) as M3.
    assert (E8 : (SHADOW_OFF + a / 8) / 8 * 8 = SHADOW_OFF + (a / 8) / 8 * 8).
    { replace (SHADOW_OFF + a / 8) with ((268431360 + (a / 8) / 8) * 8 + (a / 8) mod 8) by (unfold SHADOW_OFF; lia).
      rewrite Z.div_add_l by lia. rewrite (Z.div_small ((a / 8) mod 8) 8) by lia. unfold SHADOW_OFF. lia. }
    rewrite E8.
    assert (LO2 : B / 64 <= (a / 8) / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HI2 : (a / 8) / 8 < (B / 64) + (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  assert (INa : Sh B <= SHADOW_OFF + a / 8 < Sh (B + L)).
  { rewrite SHB, SHE. split; [apply Z.add_le_mono_l; apply Z.div_le_mono; lia|].
    apply Z.add_lt_mono_l. pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    rewrite H2 in DB. rewrite H4 in DL. apply Z.div_lt_upper_bound; [lia|]. nia. }
  split; [unfold Sh, SHADOW_OFF in INa |- *; pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5); lia|].
  split; [unfold shadow_addr; apply OUT; exact INa|].
  split.
  - intros j Hj. unfold word_byte. split; [apply OUT; apply W; exact Hj|]. rewrite (Hz _ (W j Hj)). discriminate.
  - exists (Z_to_bv 8 0). split; [unfold shadow_addr; apply Hz; exact INa|]. left. reflexivity.
Qed.

Definition pub_sym_okb (A : axst) (tv : list (sv * sv)) (eB eL : sv) (LO HI : Z) : bool := ltac2:(tb__ "0|3|
S2cS2cS2cS2cS2cS2cS48Z0M0VLO;A2S47S44VLO;Z40M1A2G0A2A2S47S44VHI;G1A2G0A2A2S48VHI;S45Z2Z2fA2A2A2S18S3cVA;A1SaS40A1A2A2S3eS28S3aVA;A1M2A1S31S7S7VeB;VeL;A4A2A2S58S9S5fS13G2A1Vtv;S3fVLO;A1S3fVHI;A1A4S10G2A1A3A2").

Lemma SPA_publish_sym : ltac2:(tb__ "0|6|
S2aS8S39S2bS30S7S7A2M0A1S2bS36Q40M1A1A1S4eS7S7S4S4S0S2dS7dR8R7R4R3R2R1A6S2eA3S60RaR8A2S37G1SbRbR6A2A2S4S37G1SbRcR6A2A2S4S41R6R2A2S41S43R3R2A2R6A2S0S4S44R4Z40A2Z0M2A3M3G3S42G2R5A2S4S1S41S3fR8A1R1A2S42R1S3fS43R8R7A2A1A2A2S0S2fS36Q8M4A1M5A1ScR14S38G1R2A2A2S32G5S38G4G2A2A2A3F_;Fz;S29S6R14R12R13R10RfA6S29S6R15S57R13S33G0S31S7S7RfReA4S3bR13A1A3A2R14R11R10A6F_;F_;F_;F_;F_;F_;F_;TL;TB;F_;F_;FHI;FLO;FeL;FeB;Fw;Ftp;Ftv;FA;Frho;FJ;").
Proof.
  intros J rho A tv tp w eB eL LO HI Hok HTV B L HLB HBH H2 H4 H3 Hz HS.
  unfold pub_sym_okb in Hok. apply andb_prop in Hok as [Hok HO]. apply andb_prop in Hok as [Hok Hxb]. apply andb_prop in Hok as [Hok Hb].
  apply andb_prop in Hok as [Hok H5]. apply andb_prop in Hok as [Hok HH64]. apply andb_prop in Hok as [H1 HL64].
  apply Z.leb_le in H1. apply Z.eqb_eq in HL64. apply Z.eqb_eq in HH64. apply Z.leb_le in H5. apply sv_eqb_sound in Hb.
  pose proof HS as [(Hsm & _) _].
  assert (HF : Forall (holds rho) (ss_facts (ax_S A))) by exact (smatch_facts_hold _ _ _ _ Hsm).
  assert (Hall : Forall (obj_holds segs rho (cfg_ms (snd (virt tp w)))) (ss_objs (ax_S A))).
  { destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
  assert (SHB : Sh B = SHADOW_OFF + B / 8) by (unfold Sh; lia).
  assert (SHE : Sh (B + L) = SHADOW_OFF + (B + L) / 8) by (unfold Sh; lia).
  assert (OUT : forall z, Sh B <= z < Sh (B + L) -> outside_all rho (ss_objs (ax_S A)) (Z_to_bv 64 z)).
  { intros z Hzr. apply (ranges_disjoint_outside rho _ (Sh LO) (Sh HI)).
    - apply Forall_forall. intros o Ho.
      apply (obj_clear_litb2_sound rho _ (ss_facts (ax_S A)) tv (Sh LO) (Sh HI) o (proj1 (Forall_forall _ _) Hall o Ho) HF);
        [unfold Sh, SHADOW_OFF; split; [lia | apply Z.add_le_mono_r; apply Z.div_le_mono; lia] | unfold Sh, SHADOW_OFF; pose proof (Z.div_le_mono HI (2 ^ 47) 8 ltac:(lia) H5); lia | exact HTV |].
      exact (proj1 (forallb_forall _ _) HO o Ho).
    - rewrite lit_unsigned.
      assert (R1 : Sh LO <= Sh B) by (unfold Sh; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
      assert (R2 : Sh (B + L) <= Sh HI) by (unfold Sh; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
      rewrite Z.mod_small; [lia|]. unfold Sh, SHADOW_OFF in Hzr, R1, R2 |- *. pose proof (Z.div_le_mono HI (2 ^ 47) 8 ltac:(lia) H5). pose proof (Z.div_pos LO 8). lia. }
  apply (SPA_x_publish segs J rho A (eB, eL) tp w); [exact Hxb | | exact HS].
  rewrite Hb. unfold xr_ok. cbn [fst snd]. change (eval rho (SLit SHADOW_OFF)) with (Z_to_bv 64 SHADOW_OFF). rewrite lit_unsigned. fold B L.
  rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  split; [pose proof (Z.div_mod B 64 ltac:(lia)) as DB0; rewrite H2 in DB0; replace B with ((8 * (B / 64)) * 8) by lia; apply Z_mod_mult|].
  pose proof (urange (eval rho eB)). pose proof (urange (eval rho eL)).
  split; [lia|].
  intros a Ha.

  assert (W : forall j, 0 <= j < 8 -> Sh B <= (SHADOW_OFF + a / 8) / 8 * 8 + j < Sh (B + L)).
  { intros j Hj. rewrite SHB, SHE.
    pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
    assert (HB8 : B / 8 = 8 * (B / 64)) by (rewrite H2 in DB; nia).
    assert (HBL8 : (B + L) / 8 = 8 * (B / 64) + 8 * (L / 64)) by (rewrite H2 in DB; rewrite H4 in DL; nia).
    assert (LOa : 8 * (B / 64) <= a / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HIa : a / 8 < 8 * (B / 64) + 8 * (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_mod (a / 8) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (a / 8) 8 ltac:(lia)) as M3.
    assert (E8 : (SHADOW_OFF + a / 8) / 8 * 8 = SHADOW_OFF + (a / 8) / 8 * 8).
    { replace (SHADOW_OFF + a / 8) with ((268431360 + (a / 8) / 8) * 8 + (a / 8) mod 8) by (unfold SHADOW_OFF; lia).
      rewrite Z.div_add_l by lia. rewrite (Z.div_small ((a / 8) mod 8) 8) by lia. unfold SHADOW_OFF. lia. }
    rewrite E8.
    assert (LO2 : B / 64 <= (a / 8) / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HI2 : (a / 8) / 8 < (B / 64) + (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  assert (INa : Sh B <= SHADOW_OFF + a / 8 < Sh (B + L)).
  { rewrite SHB, SHE. split; [apply Z.add_le_mono_l; apply Z.div_le_mono; lia|].
    apply Z.add_lt_mono_l. pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    rewrite H2 in DB. rewrite H4 in DL. apply Z.div_lt_upper_bound; [lia|]. nia. }
  split; [unfold Sh, SHADOW_OFF in INa |- *; pose proof (Z.div_le_mono HI (2 ^ 47) 8 ltac:(lia) H5); pose proof (Z.div_le_mono (B + L) HI 8 ltac:(lia) HBH); lia|].
  split; [unfold shadow_addr; apply OUT; exact INa|].
  split.
  - intros j Hj. unfold word_byte. split; [apply OUT; apply W; exact Hj|]. rewrite (Hz _ (W j Hj)). discriminate.
  - exists (Z_to_bv 8 0). split; [unfold shadow_addr; apply Hz; exact INa|]. left. reflexivity.
Qed.

Lemma SPA_reobj_same_range : ltac2:(tb__ "0|1|
S2aS8S39S35S9S9S2bS36Q40A1A1S4eS0S2fS9A1S59S9S10S3aR6A1A1R5A3S32S9R4A2A3S0S2dS6fS3aR7A1M0S52G0R6R4A3A2S2eA3S0S30S4S4A2S20R9R5A2S20R9R6A2A3S5bS12S6RbR1R8A4S12S6RcR2R8A4F_;Fms;S29S6RcRaRbR6R5A6S29S6RdS3dRbS52S3aRbA1RaR8A3A2RcR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fo';Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o o' tp w Hn Hsame Hr HO HS.
  pose proof HS as [(Hsm & HMI & Haw & Hsh & Hhz) Hk].
  pose proof (nth_error_split3 (ss_objs (ax_S A)) i o Hn) as EO.
  assert (Hin : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).
  apply (SPA_reobj segs J rho A (set_obj_at (ax_S A) i o') tp w).
  - exact Hsame.
  - reflexivity.
  - exact HS.
  - destruct w as [tr [ms md]]. unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg].
    unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
    pose proof (smatch_mm segs _ _ _ _ _ Hsm) as Hmm. cbn [ss_objs set_obj_at set_objs].
    rewrite EO in Hmm.
    change (firstn i (ss_objs (ax_S A)) ++ o' :: skipn (S i) (ss_objs (ax_S A)))
      with (firstn i (ss_objs (ax_S A)) ++ [o'] ++ skipn (S i) (ss_objs (ax_S A))).
    apply (mem_match_replace segs rho _ (firstn i (ss_objs (ax_S A))) o (skipn (S i) (ss_objs (ax_S A))) [o'] Hmm).
    + constructor; [|constructor]. destruct Hmm as (Hall & _ & _).
      apply HO. exact (proj1 (Forall_forall _ _) Hall o ltac:(apply in_or_app; right; left; reflexivity)).
    + destruct Hmm as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
      rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite Hr. exact Hpd.
    + intros x. split.
      * intros Hx. exists o'. split; [left; reflexivity|]. rewrite Hr. exact Hx.
      * intros (o2 & [<-|[]] & Hx). rewrite Hr in Hx. exact Hx.
  - apply xshadow_outside_cover; [exact Hsh|]. cbn [ss_objs set_obj_at set_objs].
    intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|[<-|Ho2]].
    + exists o2. split; [eapply In_firstn_In; exact Ho2 | exact Hx].
    + exists o. split; [exact Hin|]. rewrite <- Hr. exact Hx.
    + exists o2. split; [eapply In_skipn_In; exact Ho2 | exact Hx].
Qed.

Lemma obj_holds_shift : ltac2:(tb__ "0|2|
S8S5bS9S9S4S0S26S25R3A1S1aA3M0G0S0S4S37Q40M1SbR7S1eR4A1A2A2S43S37G1SbR7S1eR5A1A2A2R3A2A3S0S4S17R8R5A2S46S17R8R6A2R4A2A3S0S4S16R9R6A2S46S16R9R7A2R5A2A3S42S46S16RaR7A2S17RaR7A2A2S45Z2Z3fA2A2S5aSdSdSdSdS1S0S4S1dR1A1S1dR2A1A3S1S0S7S1cR1A1S1cR2A1A3S0S4S21RdS1bR1A1A2S46S21RdS1bR2A1A2R9A2A3A2A2Lc';Lc;S1fR9A1S1fR8A1A5S12S6RcRbRaA4S12S6RdRcRaA4F_;F_;F_;F_;F_;F_;F_;F_;Fd;Fo';Fo;Fms;Frho;").
Proof.
  intros rho ms o o' d Hd Hd' Hb Hlo Hhi Hsz HC (HB & Hw & Hcells & Hdf & Hinv).
  unfold obj_holds. cbv zeta. rewrite Hd'. rewrite Hd in Hw, Hdf, Hinv. cbn [dflt_writable dflt_holds dflt_inv] in Hw, Hdf, Hinv |- *.
  rewrite Hb, Hlo, Hhi.
  split; [lia|]. split.
  - intros off Hoff _. replace (bv_unsigned (eval rho (ob_base o)) + d + off) with (bv_unsigned (eval rho (ob_base o)) + (off + d)) by lia.
    apply Hw; [lia | reflexivity].
  - split.
    + clear Hw Hdf Hinv. revert HC Hcells. generalize (ob_cells o') as cs'. generalize (ob_cells o) as cs.
      induction 1 as [|c c' cs cs' (Ew & Ev & Eo) HC2 IH]; intros Hcs; [constructor|].
      inversion Hcs as [|? ? Hc Hcs']; subst. constructor; [|exact (IH Hcs')].
      destruct Hc as (C1 & C2 & C3). unfold cell_holds. rewrite Ew, Ev, Eo. split; [lia|]. split; [lia|].
      unfold oaddr in C3 |- *. rewrite Hb. replace (bv_unsigned (eval rho (ob_base o)) + d + (soff rho (c_off c) - d)) with (bv_unsigned (eval rho (ob_base o)) + soff rho (c_off c)) by lia.
      exact C3.
    + split; [|exact I]. intros off Hoff Hnc.
      replace (bv_unsigned (eval rho (ob_base o)) + d + off) with (bv_unsigned (eval rho (ob_base o)) + (off + d)) by lia.
      apply Hdf; [lia|]. intros HCov. apply Hnc. unfold covered in HCov |- *.
      apply Exists_exists in HCov as (c & Hinc & Hic). clear Hw Hdf Hinv Hcells.
      revert HC Hinc. generalize (ob_cells o') as cs'. generalize (ob_cells o) as cs.
      induction 1 as [|c0 c0' cs cs' (Ew & Ev & Eo) HC2 IH]; intros Hinc; [destruct Hinc|].
      destruct Hinc as [<-|Hinc].
      * apply Exists_cons_hd. unfold in_cell in Hic |- *. rewrite Eo, Ew. lia.
      * apply Exists_cons_tl. exact (IH Hinc).
Qed.

Lemma SPA_relist : ltac2:(tb__ "0|3|
S2aS8S39S35S7S7S7S5S5S2bS36Q40A1A1S4eS0S2fS9A1S59S9S10S3aR9A1A1R8A3S32S9S11R7R6R5S34SdA1M0S19R4A1M1A5A2A3S0S2dS6fS3aRaA1M2S52G2R9S11R8R7R6G0G1A5A3A2S2eA3S0S2bS36Q8A1A1SeRcR5A2SeRcR6A2A3S29S6ReRcRdR5R4A6S29S6RfS3dRdS52S3aRdA1RcS11RbRaR9G0S19R7A1A5A3A2ReR6R5A6F_;F_;F_;F_;Fw;Ftp;Fl';Fl;Fhi;Flo;Fb;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i b lo hi l l' tp w Hn Hsame Hrl HS.
  apply (SPA_reobj_same_range J rho A i (mkObj b lo hi [] (DList l)) (mkObj b lo hi [] (DList l')) tp w Hn Hsame eq_refl); [|exact HS].
  intros ms (HB & Hw & Hc & Hd & Hinv). unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact HB|]. split; [exact Hw|]. split; [exact Hc|]. split.
  - intros off Hoff Hnc. cbn [dflt_holds]. rewrite Hrl. exact (Hd off Hoff Hnc).
  - cbn [dflt_inv] in Hinv |- *. rewrite Hrl. exact Hinv.
Qed.

Section HdrArith.
Variable F : list byte.
Variable rho : valuation.
Let b := bv_unsigned (rw rho 45%positive).
Let b0 := bv_unsigned (nth 0 F (Z_to_bv 8 0)).
Let b1 := bv_unsigned (nth 1 F (Z_to_bv 8 0)).
Let b2 := bv_unsigned (nth 2 F (Z_to_bv 8 0)).
Let b3 := bv_unsigned (nth 3 F (Z_to_bv 8 0)).
Hypothesis Hh : ltac2:(tb__ "0|0|
S0S4S44Vb;S45Z2Z20A2A2S56VF;A1A3").

Lemma hdr_bytes_rng : ltac2:(tb__ "0|2|
S1S1S41Z0M0Vb0;A2S42Vb0;Z100M1A2A2S1S1S41G0Vb1;A2S42Vb1;G1A2A2S1S1S41G0Vb2;A2S42Vb2;G1A2A2S1S41G0Vb3;A2S42Vb3;G1A2A2A2A2A2").
Proof.
  pose proof (bv_unsigned_in_range 8 (nth 0 F (Z_to_bv 8 0))). pose proof (bv_unsigned_in_range 8 (nth 1 F (Z_to_bv 8 0))).
  pose proof (bv_unsigned_in_range 8 (nth 2 F (Z_to_bv 8 0))). pose proof (bv_unsigned_in_range 8 (nth 3 F (Z_to_bv 8 0))).
  change (bv_modulus 8) with 256 in *. subst b0 b1 b2 b3. lia.
Qed.

Lemma hdr_low8 : b mod 256 = b0.
Proof.
  pose proof hdr_bytes_rng as (R0 & R1 & R2 & R3).
  assert (E : b mod 256 = (b mod 2 ^ 32) mod 256).
  { pose proof (Z.div_mod b (2 ^ 32) ltac:(lia)) as Hd. rewrite Hd at 1.
    replace (2 ^ 32 * (b / 2 ^ 32) + b mod 2 ^ 32) with (b mod 2 ^ 32 + (16777216 * (b / 2 ^ 32)) * 256) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite E, Hh. unfold hdr_word. fold b0 b1 b2 b3.
  replace (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) with (b0 + (b1 + 256 * b2 + 65536 * b3) * 256) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma hdr_byte1 : ltac2:(tb__ "0|1|
S0S4S44S4aVb;Z100M0A2G0A2Vb1;A3").
Proof.
  pose proof hdr_bytes_rng as (R0 & R1 & R2 & R3).
  pose proof (Z.div_mod b (2 ^ 32) ltac:(lia)) as Hd. rewrite Hh in Hd. unfold hdr_word in Hd. fold b0 b1 b2 b3 in Hd.
  rewrite Hd at 1. change (2 ^ 32) with (256 * 16777216).
  replace (256 * 16777216 * (b / (256 * 16777216)) + (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3))
    with (b0 + (16777216 * (b / (256 * 16777216)) + b1 + 256 * b2 + 65536 * b3) * 256) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small b0 256) by lia. rewrite Z.add_0_l.
  replace (16777216 * (b / (256 * 16777216)) + b1 + 256 * b2 + 65536 * b3) with (b1 + (65536 * (b / (256 * 16777216)) + b2 + 256 * b3) * 256) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma U_srl8 : ltac2:(tb__ "0|0|
S0S4S37Q40SbVrho;S14S79S24P2dA1SaZ8A1A3A2A2S4aVb;Z100A2A3").
Proof. cbn [eval]. rewrite srl_val. change (8 mod 64) with 8. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma land_shift8_small : ltac2:(tb__ "0|3|
S4S4S41Z0M0R2A2M1S1G1S42R2Z100M2A2A2S0S4S4cS4bR4G2A2R3A2G0A3F_;F_;Fc;Fm;").
Proof.
  intros m c Hm Hc. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hlt|Hge].
  - change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 c i); [apply andb_false_r | lia |].
    destruct (Z.eq_dec c 0) as [->|Hne]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2 ^ 8)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma lor_shift8_small : ltac2:(tb__ "0|3|
S4S4S41Z0R2A2M0S1G0S42R2Z100M1A2A2S0S4S4dS4bR4G1A2M2R3A2S43G2R3A2A3F_;F_;Fc;Fm;").
Proof.
  intros m c Hm Hc. rewrite <- Z.lxor_lor by (apply land_shift8_small; lia). symmetry. apply Z.add_nocarry_lxor. apply land_shift8_small; lia.
Qed.

Lemma U_flg_x : ltac2:(tb__ "0|1|
S0S4S37Q40SbVrho;S6bA2A2S2dS4L_;S49S55VF;A1M0Z80A2G0S46S43G0S45Z2Z40A2A2Z100A2X2dx2A3").
Proof.
  pose proof hdr_bytes_rng as (R0 & R1 & R2 & R3).
  unfold flg_x. cbn [eval].
  change (alu64 ALU_SRL (rw rho 45%positive) (Z_to_bv 64 8)) with (eval rho (SAlu ALU_SRL (SVar 45) (SLit 8))).
  rewrite (U_sext_w 8); [| reflexivity | cbv; discriminate]. rewrite U_srl8. change (Z.of_N 8) with 8. change (2 ^ 8) with 256. rewrite hdr_byte1.
  unfold zsext, flags_of. fold b1. change (2 ^ (8 - 1)) with 128. unfold M64v. destruct (b1 <? 128); lia.
Qed.

Lemma U_clen_x : ltac2:(tb__ "0|0|
S0S4S37Q40SbVrho;S64A2A2S54VF;A1A3").
Proof.
  pose proof hdr_bytes_rng as (R0 & R1 & R2 & R3). pose proof (urange (rw rho 45%positive)) as Rb. fold b in Rb.
  unfold clen_x. cbn [eval].
  change (alu64 ALU_SRL (rw rho 45%positive) (Z_to_bv 64 8)) with (eval rho (SAlu ALU_SRL (SVar 45) (SLit 8))).
  rewrite or_val_A, srl_val, sll_val. change (57 mod 64) with 57. change (49 mod 64) with 49.
  rewrite (U_sext_w 8); [| reflexivity | cbv; discriminate]. rewrite U_srl8. change (Z.of_N 8) with 8. change (2 ^ 8) with 256. rewrite hdr_byte1.
  rewrite (U_zext_w 8) by (cbv; discriminate). change (Z.of_N 8) with 8. change (2 ^ 8) with 256. fold b. rewrite hdr_low8.
  set (z := zsext 8 b1).
  assert (Hz : z mod 128 = b1 mod 128 /\ 0 <= z).
  { subst z. unfold zsext. change (2 ^ (8 - 1)) with 128. change (2 ^ 8) with 256. unfold M64v.
    destruct (Z.ltb_spec b1 128); split; try lia.
    all: replace (b1 + 18446744073709551616 - 256) with (b1 + (144115188075855871) * 128) by lia; rewrite Z_mod_plus_full; reflexivity. }
  destruct Hz as [Hzm Hz0].
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 64) with (128 * 2 ^ 57) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia. rewrite Hzm.
  replace (2 ^ 57) with (2 ^ 8 * 2 ^ 49) by reflexivity. rewrite Z.mul_assoc, Z.div_mul by lia.
  change (2 ^ 8) with 256. pose proof (Z.mod_pos_bound b1 128 ltac:(lia)).
  rewrite lor_shift8_small by lia. unfold clen_of. fold b0 b1.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128. lia.
Qed.

Lemma clen_of_range : 0 <= clen_of F <= 32767.
Proof.
  pose proof hdr_bytes_rng as (R0 & R1 & R2 & R3). unfold clen_of. fold b0 b1.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128. pose proof (Z.mod_pos_bound b1 128 ltac:(lia)). lia.
Qed.

Lemma U_plen_x : ltac2:(tb__ "0|3|
S4S0S4S37Q40M0SfVrho;P65A2A2Z0A3S0S4S37G0SfVrho;P2aA2A2R2A3S41S43S54VF;A1M1Z6M2A2R3A2S42R4S45Z2Z3eA2A2S0S4S37G0SbVrho;S6eA2A2S46S46R5G2A2G1A2A3F_;F_;F_;F_;Flen;").
Proof.
  intros len H101 H32 Hcl Hlen. pose proof clen_of_range as HC.
  unfold plen_x. fold clen_x. rewrite U_add, U_sub, U_clen_x, !U_lit. cbn [eval]. rewrite H32. unfold M64v.
  rewrite (Z.mod_small (len - clen_of F)) by lia.
  replace ((-6) mod 18446744073709551616) with (18446744073709551616 - 6) by reflexivity.
  replace (len - clen_of F + (18446744073709551616 - 6)) with ((len - 6 - clen_of F) + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
End HdrArith.

Lemma SPA_JA_Kc : ltac2:(tb__ "0|3|
S75S8S2bS36Q40A1A1M0S5cOF_;F_;F_;F_;S2bS30S4S4A2M1A1M2G2S5S73S73S8S8OF_;G2S2bS30G1S4A2A1S82S75OF_;S72S39S8G0S4eS2bS5dA1S5cRfR2R1A2RfR3R2A2F_;Fmd;Ftr;S29S6S71R12R11R10RfReRcRbRaR9R8R7R6AcR5R4R3R2A6S29S6S71R13R12R11R10ReRdRcRbRaR9R8R7AcR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fnd;FPA;FBX;FFF;FFB;FP0f;Frho0;FKc';FKc;FNP;FXGL;FCST;FAInv;").
Proof.
  intros AInv CST XGL NP Kc Kc' rho0 P0f FB FF BX PA nd A rho tp w HK [Hsm (Ai & kc & Hav & Hk & REST)].
  split; [exact Hsm|]. exists Ai, kc. split; [exact Hav|]. split; [apply HK; exact Hk | exact REST].
Qed.
End DrvRGlue.

(* [comment removed for export] *)
Module DrvTLXi_f3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "Some"; "nil"; "list"; "option"; "false"; "nat"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "ss_facts"; "ss_next"; "SPUle"; "SVar"; "sobj"; "sprop"; "sprop_eqb"; "ss_lenient"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "mkLeafA"; "ax_X"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX"; "bd_J"; "keptX"; "CP"; "backedge_okb"; "bd_L"; "exitc_b"; "ndJX"; "ndLX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "PreF"; "PostF"; "CUTS_X"; "FUEL_X"; "vB"; "vCap"; "vPlen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states"; "R_fp_Pc0"; "R_fp_Pc1"; "T_fp_Pc0"; "T_fp_Pc1"; "J_E"; "LJa_Pc0"; "LJa_Pc1"; "LJb_Pc0"; "LJb_Pc1"; "LX_Pc0"; "LX_Pc1"; "s_fp"; "vP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "drv_xrb"; "robjs_checkD"; "sp0_factsb"; "xrs_checkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "KU"; "bd_below"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvTLXi_h.

Lemma XPc0_facts : ltac2:(tb__ "0|12|
S1S0S8S7S13A1M0A1S45S20S37A1M1S26S39G1A1M2A3S5G0S2eA2A3S1S0S2S44G1S26G2S2eS4S18S27S6S18A1M3A3A5S3A3S1S0S2S4aS2dG2A2S3A3S1S0S2S3eS2dS10S1aS37A1M4A1M5A2S3A3S1S1S0S2S3dG5S25S22Z1M6A1M7A1A2S3A3S0S2S47G5S1eA2S3A3A2S1S1S0SdS3bG2PcA2S12S3aA1M8A3S0SdS3bG2PdA2S2cA3A2S1S0S2S48SfS1aG1A1M9A1MaSeZ0MbA1McS46G7S1eA5S3A3S1S0S2S42GaA1S3A3S1S0S2S41GaS1fS5SaU0A2MdS2eA4S3A3S1S0S2S43GaS1fGdS17G9A1S40S1cG1A1A6S3A3S1S0S2S4bS14S15S11SeZ1000A1G8A2A1GaA3S3A3S1S0S18S49S26G1G2S2eS27A5S30A3S1S1S0S2S3eS2dS10S1aS30A1MeA1MfA2S3A3S1S0S2S16GeA1S9A3S0S2S3dGfS24S1eA1A2S3A3A2A2S1S0S8S7S19A1M10A1S1dS3fS29S28S30S3A5S5G10S4S19S1bS33S3cA2S4S19S1bS35S3cA2S6S19A1A3A3A2A3S1S0S2S4cS18S21S32S4dGbG6A2GcA2S4ScSdSdA2M11SbSdSdS2aS2bA4S6G11A1A3S1eA3S4S18S33S4S18S35G3A3A3A3S3A3S0S2S23GbSfG4A1A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Lemma XPc1_facts : ltac2:(tb__ "0|11|
S1S0S8S7S13A1M0A1S45S20S38A1M1S26S39G1A1M2A3S5G0S2fA2A3S1S0S2S44G1S26G2S2fS4S18S27S6S18A1M3A3A5S3A3S1S0S2S4aS2dG2A2S3A3S1S0S2S3eS2dS10S1aS38A1M4A1M5A2S3A3S1S1S0S2S3dG5S25S22Z2A1M6A1A2S3A3S0S2S47G5S1eA2S3A3A2S1S1S0SdS3bG2PcA2S12S3aA1M7A3S0SdS3bG2PdA2S2cA3A2S1S0S2S48SfS1aG1A1M8A1M9SeZ0A1MaS46G6S1eA5S3A3S1S0S2S42G9A1S3A3S1S0S2S41G9S1fS5SaU0A2MbS2fA4S3A3S1S0S2S43G9S1fGbS17G8A1S40S1cG1A1A6S3A3S1S0S2S4bS14S15S11SeZ1000A1G7A2A1G9A3S3A3S1S0S18S49S26G1G2S2fS27A5S31A3S1S1S0S2S3eS2dS10S1aS31A1McA1MdA2S3A3S1S0S2S16GcA1S9A3S0S2S3dGdS24S1eA1A2S3A3A2A2S1S0S8S7S19A1MeA1S1dS3fS29S28S31S3A5S5GeS4S19S1bS34S3cA2S4S19S1bS36S3cA2S6S19A1A3A3A2A3S1S0S2S4cS18S21S32S4dZ1MfGfA2GaA2S4ScSdSdA2M10SbSdSdS2aS2bA4S6G10A1A3S1eA3S4S18S34S4S18S36G3A3A3A3S3A3S0S2S23GfSfG4A1A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.
End DrvTLXi_f3.

(* [comment removed for export] *)
Module DrvTLXi_f2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "Some"; "list"; "option"; "prod"; "false"; "nat"; "None"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_next"; "ss_facts"; "sobj"; "ss_lenient"; "ss_objs"; "SLit"; "SVar"; "sv_below"; "SPUle"; "sprop"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "mkLeafA"; "ax_X"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states"; "PreM"; "E_mP1"; "E_mPc"; "LX_E10"; "R_mP1"; "R_mPc"; "R_fn_E10"; "R_fp_Pc2"; "PreFN"; "T_fn_E10"; "T_fp_Pc2"; "T_mnull1"; "T_mnullc"; "vP"; "J_E"; "LJEa_E10"; "LJEb_E10"; "LJa_Pc2"; "LJb_Pc2"; "LX_Pc2"; "PostFN"; "PostsM"; "s_m"; "LN1a"; "LN1b"; "LNca"; "LNcb"; "T_mok1"; "T_mokc"; "s_fn"; "s_fp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX"; "bd_J"; "bd_M"; "backedge_okb"; "keptX"; "plen_factsb"; "CP"; "bd_E"; "bd_L"; "exit1_b"; "exitc_b"; "ndEX"; "ndJE"; "ndJX"; "ndLX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "ANone"; "NDA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vPlen"; "tv_T"; "CUTS_X"; "FUEL_X"; "PreF"; "PostF"; "bd_T"; "nd_T"; "vB"; "vCap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "drv_xrb"; "robjs_checkD"; "sp0_factsb"; "xrs_checkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_below"; "bud_pay"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "L_malloc_null"; "L_malloc_ok"; "V_RES"; "ulink"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "pos_add_nat"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvTLXi_h.

Lemma XPc2_facts : ltac2:(tb__ "0|11|
S1S0S8S7S11A1M0A1S66S45S34A1M1S57S3fG1A1M2A3S6G0S28A2A3S1S0S2S65G1S57G2S28S4S1aS58S5S1aA1M3A3A5S3A3S1S0S2S5fS20G2A2S3A3S1S0S2S52S20SfS1cS34A1M4A1M5A2S3A3S1S1S0S2S4fG5S4dS47Z3A1M6A1A2S3A3S0S2S68G5S40A2S3A3A2S1S1S0SeS5dG2PcA2S15S2eA1M7A3S0SeS5dG2PdA2S53A3A2S1S0S2S69S10S1cG1A1M8A1M9S14Z0A1MaS6aG6S40A5S3A3S1S0S2S63G9A1S3A3S1S0S2S62G9S43S6SbU0A2MbS28A4S3A3S1S0S2S64G9S43GbS13G8A1S61S1eG1A1A6S3A3S1S0S2S75S18S19S17S14Z1000A1G7A2A1G9A3S3A3S1S0S1aS5eS57G1G2S28S58A5S2bA3S1S1S0S2S52S20SfS1cS2bA1McA1MdA2S3A3S1S0S2S12GcA1SaA3S0S2S4fGdS4cS40A1A2S3A3A2A2S1S0S8S7S1bA1MeA1S1fS60S56S55S2bS3A5S6GeS4S1bS1dS32S4eA2S4S1bS1dS33S4eA2S5S1bA1A3A3A2A3S1S0S2S74S1aS42S2fS76Z2MfZ1A2GaA2S4S9SeSeA2M10SdSeSeS5bS5cA4S5G10A1A3S40A3S4S1aS32S4S1aS33G3A3A3A3S3A3S0S2S49GfS10G4A1A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Lemma XE10_facts : ltac2:(tb__ "0|10|
S1S0S8S7S11A1M0A1S66S24S29S3eS24A1M1A3S6G0S27A2A3S1S0S2S65S24S29G1S27S4S1aS35S5S1aA1M2A3A5S3A3S1S0S2S5fS20G1A2S3A3S1S0S2S52S20SfS1cS24A1M3A1M4A2S3A3S1S1S0S2S4fG4S4aS46Z1M5A1M6A1A2S3A3S0S2S68G4S40A2S3A3A2S1S0S2S69S10G3A1M7S14Z0M8A1M9G8G6S40A5S3A3S1S0S2S63G7A1S3A3S1S0S2S62G7S4S9SeSeA2MaSdSeSeS5bS5cA4S5GaA1A3MbScSbA1McS27A4S3A3S1S0S2S64G7GbGcS13G3A1S61S1eS24A1A6S3A3S1S0S1aS5eS29S24G1S27S35A5S2aA3S1S1S0S2S52S20SfS1cS2aA1MdA1MeA2S3A3S1S0S2S12GdA1SaA3S0S2S4fGeS4bS40A1A2S3A3A2A2S1S0S8S7S1bA1MfA1S1fS60S56S55S2aS3A5S6GfS4S1bS1dS30S4eA2S4S1bS1dS31S4eA2S5S1bA1A3A3A2A3S1S0S2S74S1aS42S2fS76G8G5A2G9A2GbS40A3S4S1aS30S4S1aS31G2A3A3A3S3A3S0S2S48G7A1S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Lemma MS1_facts : ltac2:(tb__ "0|c|
S1S0S8S7S11A1M0A1S66S22S21S37S22A1M1A3S6G0S25A2A3S1S0S2S65S22S21G1S25S36A5S3A3S1S0S2S5fS20G1A2S3A3S1S0S2S52S20SfS1cS22A1M2A1M3A2S3A3S1S1S0S2S4fG3S5aA2S3A3S0S2S68G3S41A2S3A3A2S1S0SeS5dG1PcA2S53A3S1S0S2S16G3S53A2S3A3S1S1S0SeS5dS67G1S21S6eS6bS5S70A1M4S6cA3M5S22A4S6fA2S15S73G3UaA2M6A1A3S0S72G6S2eA3A2S1S0S2S69S10G2A1M7S53S6aS59S41A5S3A3S1S0S2S63G7A1S3A3S1S0S2S62G7S54ScSbA1M8S25A4S3A3S1S0S2S64G7S54G8S13G2A1S61S1eS22A1A6S3A3S1S0S2S44G7A1S3A3S1S0S1aS5eS21S22G1S25S6dS6bG4S6cA3A5S2cA3S1S0S1aS5eS21S22G1S25G5A5S3cA3S1S1S0S2S52S20SfS1cS2cA1M9A1MaA2S3A3S1S0S2S12G9A1SaA3S0S2S4fGaS51S54S5S9S9SeS71A2SeA2A1S41S50A4A2S3A3A2A2S0S8S7S1bA1MbA1S1fS60S56S55S2cS3A5S6GbS4S1bS1dS38S4eA2S4S1bS1dS39S4eA2S5S1bA1A3A3A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Lemma MSc_facts : ltac2:(tb__ "0|c|
S1S0S8S7S11A1M0A1S66S23S21S37S23A1M1A3S6G0S26A2A3S1S0S2S65S23S21G1S26S36A5S3A3S1S0S2S5fS20G1A2S3A3S1S0S2S52S20SfS1cS23A1M2A1M3A2S3A3S1S1S0S2S4fG3S5aA2S3A3S0S2S68G3S41A2S3A3A2S1S0SeS5dG1PcA2S53A3S1S0S2S16G3S53A2S3A3S1S1S0SeS5dS67G1S21S6eS6bS5S70A1M4S6cA3M5S23A4S6fA2S15S73G3UaA2M6A1A3S0S72G6S2eA3A2S1S0S2S69S10G2A1M7S53S6aS59S41A5S3A3S1S0S2S63G7A1S3A3S1S0S2S62G7S54ScSbA1M8S26A4S3A3S1S0S2S64G7S54G8S13G2A1S61S1eS23A1A6S3A3S1S0S2S44G7A1S3A3S1S0S1aS5eS21S23G1S26S6dS6bG4S6cA3A5S2dA3S1S0S1aS5eS21S23G1S26G5A5S3dA3S1S1S0S2S52S20SfS1cS2dA1M9A1MaA2S3A3S1S0S2S12G9A1SaA3S0S2S4fGaS51S54S5S9S9SeS71A2SeA2A1S41S50A4A2S3A3A2A2S0S8S7S1bA1MbA1S1fS60S56S55S2dS3A5S6GbS4S1bS1dS3aS4eA2S4S1bS1dS3bS4eA2S5S1bA1A3A3A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.
End DrvTLXi_f2.

(* [comment removed for export] *)
Module DrvTLXi_f5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "Some"; "cons"; "option"; "nil"; "list"; "false"; "length"; "app"; "None"; "nat"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sobj"; "ss_next"; "SLit"; "ss_objs"; "ss_facts"; "sv"; "sprop"; "ss_lenient"; "sprop_below"; "DUnknown"; "SPUle"; "cell"; "mkObj"; "sprop_eqb"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "mkLeafA"; "ax_X"; "sym_runA"; "ax_base"; "entailsA"; "la_state"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "nd_tv"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX"; "bd_J"; "N_mc"; "kept"; "O_srcM"; "mc_needb"; "backedge_okb"; "bd_E"; "exitc_b"; "ndEX"; "ndJE"; "B3c"; "B3h"; "Cmc"; "bd_L"; "ndM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states"; "PreFN"; "LX_Ec1"; "LX_Ec2"; "LX_Ec3"; "PostFN"; "E_mc1"; "E_mcc"; "CUTS_T"; "O_srcT"; "R_fn_Ec1"; "R_fn_Ec2"; "R_fn_Ec3"; "T_mc1"; "T_mcc"; "J_E"; "L_P1"; "L_Pc"; "R_mc1"; "R_mcc"; "T_fn_Ec1"; "T_fn_Ec2"; "T_fn_Ec3"; "U_mc1"; "U_mcc"; "s_fn"; "FUEL_T1"; "FUEL_T2"; "LJEa_Ec1"; "LJEa_Ec2"; "LJEa_Ec3"; "LJEb_Ec1"; "LJEb_Ec2"; "LJEb_Ec3"; "L_P"; "O_cstkB"; "T_mok1"; "T_mokc"; "mc_hints"; "s_mc"; "sel_buf"; "sel_rtc_last"; "sel_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g7.DrvTLXi_f5"; "MC1_V3"; "MCc_V3"; "MC1_B3"; "MC1_V2"; "MCc_B3"; "MCc_V2"; "MC1_RS"; "MC1_V1"; "MC1_V4"; "MC1_s"; "MCc_RS"; "MCc_V1"; "MCc_V4"; "MCc_s"; "MC1_V7"; "MC1_i2"; "MCc_V7"; "MCc_i2"; "MC1_B1"; "MC1_B2"; "MC1_V10"; "MC1_V11"; "MC1_V5"; "MC1_V6"; "MC1_V8"; "MC1_V9"; "MC1_W1"; "MC1_W2"; "MCc_B1"; "MCc_B2"; "MCc_V10"; "MCc_V11"; "MCc_V5"; "MCc_V6"; "MCc_V8"; "MCc_V9"; "MCc_W1"; "MCc_W2"; "MC1_i0"; "MC1_i1"; "MCc_i0"; "MCc_i1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "Pre_mc0"; "P_icpt"; "Posts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vB"; "CUTS_X"; "FUEL_X"; "vCap"; "sp0"; "vClen"; "vLen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "sp0_factsb"; "drv_xrb"; "robjs_checkD"; "xrs_checkD"; "kept_nzb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "KV_T"; "KP_T";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_below"; "bud_pay"; "bd_subst"; "bud_le"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "carve_okb"; "lc_obj"; "lcarve"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvTLXi_h.

Lemma XEc1_facts : ltac2:(tb__ "0|10|
S1S0S6S8S11A1M0A1SacS42S41S59S42A1M1A3S4G0S4aA2A3S1S0S3SadS42S41G1S4aS5S20S45S7S20A1M2A3A5S2A3S1S0S3Sb0S2aG1A2S2A3S1S0S3S2dS2aS12S22S42A1M3A1M4A2S2A3S1S1S0S3S2bG4S36S34Z2A1M5A1A2S2A3S0S3Sb7G4S2eA2S2A3A2S1S0S3Sb8S15G3A1M6S13Z0M7A1M8G7G5S2eA5S2A3S1S0S3Sa7G6A1S2A3S1S0S3Sa9G6S5SfS16S16A2M9SeS16S16Sa0Sa3A4S7G9A1A3MaScSdA1MbS4aA4S2A3S1S0S3SaaG6GaGbS14G3A1Sa8S24S42A1A6S2A3S1S0S20SafS41S42G1S4aS45A5S54A3S1S1S0S3S2dS2aS12S22S54A1McA1MdA2S2A3S1S0S3S18GcA1S9A3S0S3S2bGdS37S2eA1A2S2A3A2A2S1S0S6S8S21A1MeA1S25S6bSa2Sa1S54S2A5S4GeS5S21S23S5cS3fA2S5S21S23S5fS3fA2S7S21A1A3A3A2A3S1S0S3S6cS20S33S4fSbbZ1MfGfA2G8A2GaS2eA3S5S20S5cS5S20S5fG2A3A3A3S2A3S0S3S35GfG6A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Lemma XEc2_facts : ltac2:(tb__ "0|10|
S1S0S6S8S11A1M0A1SacS43S41S59S43A1M1A3S4G0S4bA2A3S1S0S3SadS43S41G1S4bS5S20S45S7S20A1M2A3A5S2A3S1S0S3Sb0S2aG1A2S2A3S1S0S3S2dS2aS12S22S43A1M3A1M4A2S2A3S1S1S0S3S2bG4S36S34Z3A1M5A1A2S2A3S0S3Sb7G4S2eA2S2A3A2S1S0S3Sb8S15G3A1M6S13Z0M7A1M8G7G5S2eA5S2A3S1S0S3Sa7G6A1S2A3S1S0S3Sa9G6S5SfS16S16A2M9SeS16S16Sa0Sa3A4S7G9A1A3MaScSdA1MbS4bA4S2A3S1S0S3SaaG6GaGbS14G3A1Sa8S24S43A1A6S2A3S1S0S20SafS41S43G1S4bS45A5S55A3S1S1S0S3S2dS2aS12S22S55A1McA1MdA2S2A3S1S0S3S18GcA1S9A3S0S3S2bGdS37S2eA1A2S2A3A2A2S1S0S6S8S21A1MeA1S25S6bSa2Sa1S55S2A5S4GeS5S21S23S5dS3fA2S5S21S23S60S3fA2S7S21A1A3A3A2A3S1S0S3S6cS20S33S4fSbbZ2MfZ1A2G8A2GaS2eA3S5S20S5dS5S20S60G2A3A3A3S2A3S0S3S35GfG6A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Lemma XEc3_facts : ltac2:(tb__ "0|10|
S1S0S6S8S11A1M0A1SacS44S41S59S44A1M1A3S4G0S4cA2A3S1S0S3SadS44S41G1S4cS5S20S45S7S20A1M2A3A5S2A3S1S0S3Sb0S2aG1A2S2A3S1S0S3S2dS2aS12S22S44A1M3A1M4A2S2A3S1S1S0S3S2bG4S36S34Z4A1M5A1A2S2A3S0S3Sb7G4S2eA2S2A3A2S1S0S3Sb8S15G3A1M6S13Z0M7A1M8G7G5S2eA5S2A3S1S0S3Sa7G6A1S2A3S1S0S3Sa9G6S5SfS16S16A2M9SeS16S16Sa0Sa3A4S7G9A1A3MaScSdA1MbS4cA4S2A3S1S0S3SaaG6GaGbS14G3A1Sa8S24S44A1A6S2A3S1S0S20SafS41S44G1S4cS45A5S56A3S1S1S0S3S2dS2aS12S22S56A1McA1MdA2S2A3S1S0S3S18GcA1S9A3S0S3S2bGdS37S2eA1A2S2A3A2A2S1S0S6S8S21A1MeA1S25S6bSa2Sa1S56S2A5S4GeS5S21S23S5eS3fA2S5S21S23S61S3fA2S7S21A1A3A3A2A3S1S0S3S6cS20S33S4fSbbZ3MfZ1A2G8A2GaS2eA3S5S20S5eS5S20S61G2A3A3A3S2A3S0S3S35GfG6A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition MC1_W1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_mc1) 0 (SLit (-2160))) (ax_S E_mc1).
Definition MC1_W2 : sstate := Eval vm_compute in optS' (split_obj_at MC1_W1 0 (SLit (-2240))) MC1_W1.
Definition MC1_i0 : nat := Eval vm_compute in locate (ss_objs MC1_W2) vB (SLit 0).
Definition MC1_B1 : sstate := Eval vm_compute in optS' (split_obj_at MC1_W2 MC1_i0 (SLit 6)) MC1_W2.
Definition MC1_i1 : nat := Eval vm_compute in locate (ss_objs MC1_B1) vB (SLit 6).
Definition MC1_B2 : sstate := Eval vm_compute in optS' (split_obj_at MC1_B1 MC1_i1 (add vClen (SLit 6))) MC1_B1.
Definition MC1_i2 : nat := Eval vm_compute in locate (ss_objs MC1_B2) vB (add vClen (SLit 6)).
Definition MC1_B3 : sstate := Eval vm_compute in optS' (split_obj_at MC1_B2 MC1_i2 vLen) MC1_B2.
Definition MC1_RS : sstate := Eval vm_compute in set_obj_at (B3c MC1_B3) MC1_i2 O_srcT.
Definition MC1_V1 : sstate := Eval vm_compute in set_objs (ax_S T_mc1) (select (ss_objs (ax_S T_mc1)) (sel_rtc_last (length (ss_objs (ax_S T_mc1))))).
Definition MC1_V2 : sstate := Eval vm_compute in set_objs MC1_V1 (firstn (length (ss_objs MC1_V1) - 3) (ss_objs MC1_V1)).
Definition MC1_V3 : sstate := Eval vm_compute in set_obj_at MC1_V2 3 O_srcM.
Definition MC1_V4 : sstate := Eval vm_compute in set_obj_at MC1_V3 1 O_cstkB.
Definition MC1_V5 : sstate := Eval vm_compute in set_objs MC1_V4 (select (ss_objs MC1_V4) (sel_win (length (ss_objs MC1_V4)))).
Definition MC1_V6 : sstate := Eval vm_compute in optS' (merge_objs_at MC1_V5 0) MC1_V5.
Definition MC1_V7 : sstate := Eval vm_compute in optS' (merge_objs_at MC1_V6 0) MC1_V6.
Definition MC1_V8 : sstate := Eval vm_compute in set_objs MC1_V7 (select (ss_objs MC1_V7) (sel_buf (ss_objs MC1_V7))).
Definition MC1_V9 : sstate := Eval vm_compute in optS' (merge_objs_at MC1_V8 0) MC1_V8.
Definition MC1_V10 : sstate := Eval vm_compute in optS' (merge_objs_at MC1_V9 0) MC1_V9.
Definition MC1_V11 : sstate := Eval vm_compute in optS' (merge_objs_at MC1_V10 0) MC1_V10.
Definition MC1_s : wsub := Eval vm_compute in infer_sub NF (ax_S L_P1) (ax_S (L_P false 0)).
Lemma MC1_facts : ltac2:(tb__ "0|2a|
S1S1S0S3S2dS2aS12S22S64A1M0A1M1A2S2A3S1S0S3S18G0A1S9A3S0S3S2bG1S3cS3bZ0M2A1M3A1M4A2S2A3A2A2S1S0S6S8S21A1M5A1M6S25S6bS5aS48S64S2A5S4G5S5S21S23S46S3fA2S7S21A1M7A3A2A3S1S0S6S10A1M8S3eS22S46A1M9U0MaS13N870A1A3S4S10S89A2A3S1S0G8S3eS89GaS13N8c0A1A3S4S10S8aA2A3S1S0G8S3eS8aS95S13Z6A1MbA3S4S10S81A2A3S1S0G8S3eS81S96Sb6Sa5GbA2A3S4S10S82A2A3S1S0G8S3eS82S7eSa6A3S4S10S71A2A3S1S0S3S6cS17S19S12S71A1McA1SbS17S66S15S71A1MdA3A3S2A3S1S0S3SabGdS30A2S2A3S1S0S3S1fS38S71A1MeA1S2A3S1S0S3SbdS15S39S71A1MfA1S14GfA1S24S46A1Sb4Sb5S2cG4A1S2fA7S2A3S1S1S0Sb3GcS12G9A1M10A3S0S8S17A1GdS15G9A1M11A3A2S1S0S16S26S46A1S13Sc3A1A3S1S0S6S11A1M12S6dS11S14GeA1S7eA3S4S11S31A2A3S1S0S10S9fGeS7eS49A3S75A3S1S0S3S9cGeS75A2S2A3S1S1S0S3S32G11A1S2A3S0Sb3S12S75A1G10A3A2S1S0S6S8S11A1M13A1SacS3aS46S75A2M14S99S67G14A1M15A3S4G13S52A2A3S1S0S3SaeG14S99G15S52Sb1S21S20S28S9bA4A5S2A3S1S0S3S2dS2aS12S22G14A1M16A1M17A2S2A3S1S0S3S2bG17G4A2S2A3S1S0S3S6cS17S19G17A1S15G16A1M18A3S2A3S1S0S3S6eS17S1eS1bS13Z1000A1Sa0A2A1G18A3S2A3S1S0S20SafS99G14G15S52S9aA5S4dA3S1S1S0S3S9eSaS11S14S22S4dA1M19A1M1aA2M1bS69G1bA1M1cA2S2A3S0S10S40G19S9dG1aG1cA2A2S76A3A2S1S1S0G13S14S76A1M1dSbS11Sb2S11SbcSaS11G1dA2U3M1eA2G1dA3M1fSb1SbfS11SbeS2fA4A3A3S1S0S10S40S76G1fA2S72A3S1S0S3Sc0Sb4S2fA2S2A3S0S3S2bS12S76A1G4A2S2A3A2A2A2S1S1S0G12S6dS11S14S72A1G1eA3S4S11S49A2A3S1S0S10S9fS72G1eS31A3S6fA3S1S0S3S9cS72S6fA2S2A3S0S3S32S15S72A1A1S2A3A2A2A2S1S1S0G12S6dS11S14S6fA1U1M20A3S4S11S1dSb6Sa4S13N940A1A2S13N50A1S13G2A1S7S1cA1S1aA5A2A3S1S0S10S9fS6fG20S63A3S77A3S1S0S3S9cS6fS77A2S2A3S0S3Sa7S15S6fA1A1S2A3A2A2A2S1S1S0S3S9eSaS11S14S77A1M21A2M22S6aG22A1M23A2S2A3S0S10S40S77S9dG21G23A2A2S85A3A2S1S0G8S3dS85GaA2S4S10S86A2A3S1S0G8S3dS86GaA2S4S10S7dA2A3S1S1S0S3S9eSaS11S14S7dA1M24A2S68G24A1M25A2S2A3S0S10S40S7dS9dG24G25A2A2S87A3A2S1S1S0G8S3dS87GaA2S4S10S88A2A3S1S0G8S3dS88GaA2S4S10S83A2A3S0G8S3dS83GaA2S4S10S84A2A3A2A2S1S0S20S29S84S24S4dA1S26S4dA1A3S57A3S1S1S0S3S2dS2aS12S22S57A1M26A1M27A2S2A3S1S0S3S18G26A1S9A3S0S3S2bG27G4A2S2A3A2A2S1S0G6S25S6bS5bS48S57S2A5S4G5S5S21S23S50S3fA2G7A3A2A3S1S0S3S27S50S62S9G2A2S78A3S2A3S1S0S3Sc1S78S2aA2S2A3S1S0S3S2dS2aS12S22S50A1M28A1M29A2S2A3S1S0S3S2bG29G4A2S2A3S1S0S3Sc2S78S30S30A3S2A3S0S3SbaS15G28A1Sb9S78G3A2G3A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition MCc_W1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_mcc) 0 (SLit (-2160))) (ax_S E_mcc).
Definition MCc_W2 : sstate := Eval vm_compute in optS' (split_obj_at MCc_W1 0 (SLit (-2240))) MCc_W1.
Definition MCc_i0 : nat := Eval vm_compute in locate (ss_objs MCc_W2) vB (SLit 0).
Definition MCc_B1 : sstate := Eval vm_compute in optS' (split_obj_at MCc_W2 MCc_i0 (SLit 6)) MCc_W2.
Definition MCc_i1 : nat := Eval vm_compute in locate (ss_objs MCc_B1) vB (SLit 6).
Definition MCc_B2 : sstate := Eval vm_compute in optS' (split_obj_at MCc_B1 MCc_i1 (add vClen (SLit 6))) MCc_B1.
Definition MCc_i2 : nat := Eval vm_compute in locate (ss_objs MCc_B2) vB (add vClen (SLit 6)).
Definition MCc_B3 : sstate := Eval vm_compute in optS' (split_obj_at MCc_B2 MCc_i2 vLen) MCc_B2.
Definition MCc_RS : sstate := Eval vm_compute in set_obj_at (B3c MCc_B3) MCc_i2 O_srcT.
Definition MCc_V1 : sstate := Eval vm_compute in set_objs (ax_S T_mcc) (select (ss_objs (ax_S T_mcc)) (sel_rtc_last (length (ss_objs (ax_S T_mcc))))).
Definition MCc_V2 : sstate := Eval vm_compute in set_objs MCc_V1 (firstn (length (ss_objs MCc_V1) - 3) (ss_objs MCc_V1)).
Definition MCc_V3 : sstate := Eval vm_compute in set_obj_at MCc_V2 3 O_srcM.
Definition MCc_V4 : sstate := Eval vm_compute in set_obj_at MCc_V3 1 O_cstkB.
Definition MCc_V5 : sstate := Eval vm_compute in set_objs MCc_V4 (select (ss_objs MCc_V4) (sel_win (length (ss_objs MCc_V4)))).
Definition MCc_V6 : sstate := Eval vm_compute in optS' (merge_objs_at MCc_V5 0) MCc_V5.
Definition MCc_V7 : sstate := Eval vm_compute in optS' (merge_objs_at MCc_V6 0) MCc_V6.
Definition MCc_V8 : sstate := Eval vm_compute in set_objs MCc_V7 (select (ss_objs MCc_V7) (sel_buf (ss_objs MCc_V7))).
Definition MCc_V9 : sstate := Eval vm_compute in optS' (merge_objs_at MCc_V8 0) MCc_V8.
Definition MCc_V10 : sstate := Eval vm_compute in optS' (merge_objs_at MCc_V9 0) MCc_V9.
Definition MCc_V11 : sstate := Eval vm_compute in optS' (merge_objs_at MCc_V10 0) MCc_V10.
Definition MCc_s : wsub := Eval vm_compute in infer_sub NF (ax_S L_Pc) (ax_S (L_P true 0)).
Lemma MCc_facts : ltac2:(tb__ "0|2a|
S1S1S0S3S2dS2aS12S22S65A1M0A1M1A2S2A3S1S0S3S18G0A1S9A3S0S3S2bG1S3cS3bZ0M2A1M3A1M4A2S2A3A2A2S1S0S6S8S21A1M5A1M6S25S6bS5aS48S65S2A5S4G5S5S21S23S47S3fA2S7S21A1M7A3A2A3S1S0S6S10A1M8S3eS22S47A1M9U0MaS13N870A1A3S4S10S93A2A3S1S0G8S3eS93GaS13N8c0A1A3S4S10S94A2A3S1S0G8S3eS94S97S13Z6A1MbA3S4S10S8bA2A3S1S0G8S3eS8bS98Sb6Sa5GbA2A3S4S10S8cA2A3S1S0G8S3eS8cS80Sa6A3S4S10S73A2A3S1S0S3S6cS17S19S12S73A1McA1SbS17S66S15S73A1MdA3A3S2A3S1S0S3SabGdS30A2S2A3S1S0S3S1fS38S73A1MeA1S2A3S1S0S3SbdS15S39S73A1MfA1S14GfA1S24S47A1Sb4Sb5S2cG4A1S2fA7S2A3S1S1S0Sb3GcS12G9A1M10A3S0S8S17A1GdS15G9A1M11A3A2S1S0S16S26S47A1S13Sc3A1A3S1S0S6S11A1M12S6dS11S14GeA1S80A3S4S11S31A2A3S1S0S10S9fGeS80S49A3S79A3S1S0S3S9cGeS79A2S2A3S1S1S0S3S32G11A1S2A3S0Sb3S12S79A1G10A3A2S1S0S6S8S11A1M13A1SacS3aS47S79A2M14S99S67G14A1M15A3S4G13S53A2A3S1S0S3SaeG14S99G15S53Sb1S21S20S28S9bA4A5S2A3S1S0S3S2dS2aS12S22G14A1M16A1M17A2S2A3S1S0S3S2bG17G4A2S2A3S1S0S3S6cS17S19G17A1S15G16A1M18A3S2A3S1S0S3S6eS17S1eS1bS13Z1000A1Sa0A2A1G18A3S2A3S1S0S20SafS99G14G15S53S9aA5S4eA3S1S1S0S3S9eSaS11S14S22S4eA1M19A1M1aA2M1bS69G1bA1M1cA2S2A3S0S10S40G19S9dG1aG1cA2A2S7aA3A2S1S1S0G13S14S7aA1M1dSbS11Sb2S11SbcSaS11G1dA2U3M1eA2G1dA3M1fSb1SbfS11SbeS2fA4A3A3S1S0S10S40S7aG1fA2S74A3S1S0S3Sc0Sb4S2fA2S2A3S0S3S2bS12S7aA1G4A2S2A3A2A2A2S1S1S0G12S6dS11S14S74A1G1eA3S4S11S49A2A3S1S0S10S9fS74G1eS31A3S70A3S1S0S3S9cS74S70A2S2A3S0S3S32S15S74A1A1S2A3A2A2A2S1S1S0G12S6dS11S14S70A1U1M20A3S4S11S1dSb6Sa4S13N940A1A2S13N50A1S13G2A1S7S1cA1S1aA5A2A3S1S0S10S9fS70G20S63A3S7bA3S1S0S3S9cS70S7bA2S2A3S0S3Sa7S15S70A1A1S2A3A2A2A2S1S1S0S3S9eSaS11S14S7bA1M21A2M22S6aG22A1M23A2S2A3S0S10S40S7bS9dG21G23A2A2S8fA3A2S1S0G8S3dS8fGaA2S4S10S90A2A3S1S0G8S3dS90GaA2S4S10S7fA2A3S1S1S0S3S9eSaS11S14S7fA1M24A2S68G24A1M25A2S2A3S0S10S40S7fS9dG24G25A2A2S91A3A2S1S1S0G8S3dS91GaA2S4S10S92A2A3S1S0G8S3dS92GaA2S4S10S8dA2A3S0G8S3dS8dGaA2S4S10S8eA2A3A2A2S1S0S20S29S8eS24S4eA1S26S4eA1A3S58A3S1S1S0S3S2dS2aS12S22S58A1M26A1M27A2S2A3S1S0S3S18G26A1S9A3S0S3S2bG27G4A2S2A3A2A2S1S0G6S25S6bS5bS48S58S2A5S4G5S5S21S23S51S3fA2G7A3A2A3S1S0S3S27S51S62S2G2A2S7cA3S2A3S1S0S3Sc1S7cS2aA2S2A3S1S0S3S2dS2aS12S22S51A1M28A1M29A2S2A3S1S0S3S2bG29G4A2S2A3S1S0S3Sc2S7cS30S30A3S2A3S0S3SbaS15G28A1Sb9S7cG3A2G3A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.
End DrvTLXi_f5.


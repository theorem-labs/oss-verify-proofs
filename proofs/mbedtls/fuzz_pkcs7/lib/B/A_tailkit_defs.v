(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame SysStep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import MemcpyLib StoreOk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import MemSplit SpecConsts SymExec2 SymExec2Sound.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_base A_exit_lib A_exit_defs A_exit_front1 A_stdio_defs A_fwrite_oom A_fwrite_err1 A_fwrite_err2 A_oomtail.
Import ListNotations. Import SX2. Import SX2S.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_A_tailkit_defs () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.rtc_cells"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "tail_memA"; "RocqVerifyHarness.AgentSubmission.B.A_fwrite_oom.fw_memA"; "RocqVerifyHarness.AgentSubmission.B.A_fwrite_err1.fw_memA"; "RocqVerifyHarness.AgentSubmission.B.A_fwrite_err2.fw_memA"; "RocqVerifyHarness.AgentSubmission.B.A_oomtail.oom_memA"].


Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition ZIMG_LO : Z := 0x7fffa000.
Definition ZIMG_HI : Z := 0x7fffc9a5.
(* [comment removed for export] *)
Definition SSH_LO (sp0 : word) : Z := 0x7fff8000 + (bv_unsigned sp0 - 4096) / 8.
Definition SSH_HI (sp0 : word) : Z := 0x7fff8000 + bv_unsigned sp0 / 8.

Record tail_memA (sp0 : word) (M : word -> option byte) (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word) : Prop := TAIL_MEM {
  tm_win   : forall a : word, bv_unsigned sp0 - 4096 <= bv_unsigned a < bv_unsigned sp0 -> wview RSEGS M a <> None;
  tm_ro    : forall a : Z, 0x10000 <= a < 0x0f1000 -> M (Z_to_bv 64 a) = None;
  tm_err   : forall a : Z, 0x0fa488 <= a < 0x0fa578 -> M (Z_to_bv 64 a) = None;   (* [comment removed for export] *)
  tm_can   : rdn RSEGS M (Z_to_bv 64 0x65cad0) 8 = Some (word_to_le_bytes 8 can);
  tm_rtc   : asan_rtc M;
  tm_zimg  : forall a : Z, ZIMG_LO <= a < ZIMG_HI -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 0);
  tm_zstk  : forall a : Z, SSH_LO sp0 <= a < SSH_HI sp0 -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 0);
  tm_stk   : stk RSEGS M (bv_unsigned sp0 - 4096) (bv_unsigned sp0);
  tm_mi    : mem_inv RSEGS M;
  tm_tid   : 0 < tid < 2^31;
  tm_lock  : rw_cells RSEGS M 0x65cd00 [C4 (Z_to_bv 64 0)];
  tm_mtid  : rw_cells RSEGS M 0x63c9e8 [C4 (Z_to_bv 64 tid)];
  tm_atexit : exists jp jq jf, atexit_cells false M (Z_to_bv 8 0) jp jq jf;   (* [comment removed for export] *)
  tm_nl    : ro_cells RSEGS M 0x65cd23 [C1 (Z_to_bv 8 0)];
  tm_comp  : rw_cells RSEGS M 0x106390 [C1 (Z_to_bv 8 0)];
  tm_mapped : mapped M 0x7fffa000 0x800d3000;
  tm_glob  : stdio_globals M;
  tm_in    : file_clean M 0x0fa668 wp0 rp0;
  tm_out   : file_clean M 0x0fa578 wp1 rp1;
  (* [comment removed for export] *)
  tm_flag  : rw_cells RSEGS M 0x63c050 [C1 (Z_to_bv 8 0)];                           (* [comment removed for export] *)
  tm_incb  : rw_cells RSEGS M 0x63c054 [C1 (Z_to_bv 8 0)]                            (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record tail_postA (sp0 : word) (M M' : word -> option byte) : Prop := TAIL_POSTA {
  tp_agree : forall x : word,
      ~ (bv_unsigned sp0 - 4096 <= bv_unsigned x < bv_unsigned sp0) ->
      ~ (0x0fa488 <= bv_unsigned x < 0x0fa570) -> M' x = M x;
  tp_munch : munch [((bv_unsigned sp0 - 4096)%Z, (bv_unsigned sp0)%Z); (0x0fa488%Z, 0x0fa570%Z)] M M';
  tp_grows : mem_grows M M';
  tp_wmono : wmono RSEGS M M';
  tp_clean : exists wp rp, file_clean M' 0x0fa488 wp rp
}.


(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L38880010350.8L48481168584.8L64915117556.900000500:00AS1v1LS1v1LS1n1v1L". (* [comment removed for export] *)
Lemma rtc_rdn : ltac2:(CDefT.buildp (gd_tbl_A_tailkit_defs ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pn,$3.Pv,$2.P,(4.R4.)P,(5.(6.(6.$2.$3.)$2.)(7.(6.$2.$3.)$2.(7.$2.$3.R4.R3.)R2.)$8.)P,(9.(:.$3.R4.#1.)(9.(:.$3.R4.#4.)(:.$3.R4.#8.)))(:.(1.(;.(0.&8.)))(<.$=.R7.(>.&40.R6.)R5.)(?.(;.(0.&8.))(10.R5.(>.&40.R4.))))")
(* [comment removed for export] *).
Proof.
  intros m a n v RTC Hin Hn.
  pose proof (asan_rtc_cell m a n v RTC Hin) as RO.
  apply ro_cells_bytes_at in RO.
  assert (L : length (cells_bytes [rtc_mkcell n v]) = n).
  { destruct Hn as [-> | [-> | ->]]; reflexivity. }
  pose proof (bytes_at_rdn RSEGS m a _ 0 n RO ltac:(rewrite L; lia)) as RD.
  rewrite Z.add_0_r in RD. unfold wa in RD. rewrite RD. f_equal. cbn [skipn]. rewrite <- L at 1. rewrite firstn_all.
  destruct Hn as [-> | [-> | ->]]; cbn [cells_bytes rtc_mkcell cbytes]; rewrite app_nil_r; try reflexivity.
  unfold word_to_le_bytes. cbn -[Z_to_bv bv_unsigned Z.modulo]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  rewrite !bv_wrap8_mod, bv_wrap64_mod. change (2^64) with (2^8 * 2^56). rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm (2^8)). rewrite Z_mod_plus_full. rewrite Zmod_mod. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Ltac rtc_in := solve [unfold rtc_cells; cbn [In]; repeat (first [left; reflexivity | right])].

Lemma rtc_rdn8 : ltac2:(CDefT.buildp (gd_tbl_A_tailkit_defs ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pv,$2.P,(4.R3.)P,(5.(6.(6.$2.$3.)$2.)(7.(6.$2.$3.)$2.(7.$2.$3.R3.#8.)R2.)$8.)(:.(1.(;.(0.&8.)))(<.$=.R5.(>.&40.R4.)#8.)(?.(;.(0.&8.))(10.#8.(>.&40.R3.))))")
(* [comment removed for export] *).
Proof. intros. apply rtc_rdn; auto. Qed.
Lemma rtc_rdn1 : ltac2:(CDefT.buildp (gd_tbl_A_tailkit_defs ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pv,$2.P,(4.R3.)P,(5.(6.(6.$2.$3.)$2.)(7.(6.$2.$3.)$2.(7.$2.$3.R3.#1.)R2.)$8.)(:.(1.(;.(0.&8.)))(<.$=.R5.(>.&40.R4.)#1.)(?.(;.(0.&8.))(10.#1.(>.&40.R3.))))")
(* [comment removed for export] *).
Proof. intros. apply rtc_rdn; auto. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12501202450.11L2383574145.9  L5744825782.9  00000D00P00eS2lo2hi1x2H12H21y2HyS2hi1x2H22H4S2lo2hi1x2H12H22H32H4". (* [comment removed for export] *)
Lemma zrun_rdn8 : ltac2:(CDefT.buildp (gd_tbl_A_tailkit_defs ()) "Pm,Px,(0.&40.)(1.(0.&8.))Plo,$2.Phi,$2.Px,$2.P,Pa,$2.P,(11.(12.R4.R1.)(13.R1.R3.))(:.(1.(0.&8.))A1.R6.(>.&40.R2.)(?.(0.&8.)(>.&8.=)))P,(12.R4.R2.)P,(12.(14.R3.+8.)R4.)P,(12.=R6.)P,(12.R6.(15.+2.+40.))(:.(1.(;.(0.&8.)))(<.$=.R9.(>.&40.R6.)#8.)(?.(;.(0.&8.))(10.#8.(>.&40.=))))")
(* [comment removed for export] *).
Proof.
  intros m lo hi x Z0 H1 H2 H3 H4.
  change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8).
  apply rdn_const; rewrite u_small by lia; [cbn; lia|].
  intros y Hy. cbn in Hy. rewrite <- (Z_to_bv_bv_unsigned y). apply Z0. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fw_of_tail TM :=
  destruct TM as [WIN RO ERR CAN RTC ZI ZS _ _ _ _ _ _ _ _ _ _ _ _];
  split;
  first [ exact WIN | exact RO | exact ERR | exact CAN
        | (apply (rtc_rdn1 _ _ _ RTC); rtc_in)
        | (apply (rtc_rdn8 _ _ _ RTC); rtc_in)
        | (eapply (zrun_rdn8 _ _ _ _ ZI); cbv -[Z.le]; lia) ].

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L18948844718.17L34590402394.17L54237428666.17L9366979338.17 000001002003004SSSS". (* [comment removed for export] *)
Lemma tail_fw_oom : ltac2:(CDefT.buildp (gd_tbl_A_tailkit_defs ()) "Psp0,(0.&40.)PM,P,(0.&40.)(1.(0.&8.))Pcan,(0.&40.)Ptid,$2.Pwp0,(0.&40.)Prp0,(0.&40.)Pwp1,(0.&40.)Prp1,(0.&40.)P,(16.R8.R7.R6.R5.R4.R3.R2.R1.)(17.R9.R8.R7.)")
(* [comment removed for export] *).
Proof. intros * TM. fw_of_tail TM. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L18948844718.17L34590402394.17L47870102330.17L50038174602.17000001002003004SSSS". (* [comment removed for export] *)
Lemma tail_fw_err1 : ltac2:(CDefT.buildp (gd_tbl_A_tailkit_defs ()) "Psp0,(0.&40.)PM,P,(0.&40.)(1.(0.&8.))Pcan,(0.&40.)Ptid,$2.Pwp0,(0.&40.)Prp0,(0.&40.)Pwp1,(0.&40.)Prp1,(0.&40.)P,(16.R8.R7.R6.R5.R4.R3.R2.R1.)(18.R9.R8.R7.)")
(* [comment removed for export] *).
Proof. intros * TM. fw_of_tail TM. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L18948844718.17L21695513610.17L34590402394.17L37636343610.17L57501814458.17L66799800202.17000001002003004005006SSSSSS". (* [comment removed for export] *)
Lemma tail_fw_err2 : ltac2:(CDefT.buildp (gd_tbl_A_tailkit_defs ()) "Psp0,(0.&40.)PM,P,(0.&40.)(1.(0.&8.))Pcan,(0.&40.)Ptid,$2.Pwp0,(0.&40.)Prp0,(0.&40.)Pwp1,(0.&40.)Prp1,(0.&40.)P,(16.R8.R7.R6.R5.R4.R3.R2.R1.)(19.R9.R8.R7.)")
(* [comment removed for export] *).
Proof. intros * TM. fw_of_tail TM. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma tail_oom : ltac2:(CDefT.buildp (gd_tbl_A_tailkit_defs ()) "Psp0,(0.&40.)PM,P,(0.&40.)(1.(0.&8.))Pcan,(0.&40.)Ptid,$2.Pwp0,(0.&40.)Prp0,(0.&40.)Pwp1,(0.&40.)Prp1,(0.&40.)P,(16.R8.R7.R6.R5.R4.R3.R2.R1.)(1:.R9.R8.R7.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros * TM. split; [exact (tail_fw_oom _ _ _ _ _ _ _ _ TM) | destruct TM; assumption ..].
Qed.

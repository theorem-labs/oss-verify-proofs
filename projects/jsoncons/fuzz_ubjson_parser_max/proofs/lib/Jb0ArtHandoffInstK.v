(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Jb0DefsK Jb0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
Jb0HandoffK Jb0ArtCellsK Jb0ArtHandoffK Jb0HSK_0 Jb0HSK_1 Jb0MainTableK Jb0HandoffInstK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA ArtRuns ArtBridge JbtInv JbtFsInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0ArtHandoffInstK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffRolesK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0ArtCellsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0ArtHandoffInstK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0ArtHandoffK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HSK_0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HSK_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HandoffInstK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0BUDGET"; "1bool"; "1nat"; "1option"; "1true"; "2and"; "2eq"; "3lt"; "4Z"; "0E"; "0FULL"; "5segments_reserved"; "6Model"; "6m_vmmaps"; "6vm_maps"; "6vm_noaccess"]; ["7bvmap"; "0R"; "8LIMIT"; "8SINV0"; "8argH0"; "9am_base"; "9e_sp0"; ":cs_ok"; ":uE"; ";env"; ";expr"; "<rbase"; "<role"; "=vml_of"; ">art_lits_chk"; "?E_BK"]; ["?E_BOT"; "?E_KB"; "?E_TOP"; "?geo_chk"; "@I_KSPACE"; "@K0D"; "@art_lazy_chk"; "@art_sym_chk"; "@as0_A0x"; "@as0_BASEx"; "@as0_rn"; "@bK"; "@botE"; "@topE"; "AAPH0"; "AASAN0"]; ["AASEGS0"; "BHS_0"; "CHS_1"; "DHSA"; "Eart_fsg"; "Eart_fsg0"; "Eart_fsinv"; "FKMAX"; "FLENMAX"; "Fart_handoff_target"; "Gadd"; "Gle"; "Glt"; "Gmodulo"; "Gpow"; "Gsub"]; ["0argv"; "0brk0"; "0cs"; "0envp"; "0fs"; "0h"; "0hw"; "0model"; "0rdraw"; "0sp"; "Hbv"; "0uid"]]).
Local Ltac lia := L5FastLiaT.plia2.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition E_KB : expr := EMd M_MUL (ELit 4096) (EVar 224).
Definition E_BK : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 224)) (EMd M_MUL (ELit (-4096)) (EVar 225)).
Definition E_AND : expr := EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 225)) (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 224)) (ELit 65535)).
Definition E_PG : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EVar 10)).
Definition E_TOP : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 10)) (EMd M_MUL (ELit 4096) (EVar 376))).
Definition E_BOT : expr := eaddz E_TOP (-8388608).
Definition E_R : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 376))) (ELit 3935).
Definition geo_chk (cs : acs) : bool :=
let k := kn cs in
(expr_eqb (am_base (role cs I_KSPACE)) E_KB && expr_eqb (bK cs) E_BK && expr_eqb (topE cs) E_TOP && expr_eqb (botE cs) E_BOT
&& existsb (kentry_eqb (KRange (EVar 225) 0 15)) k && existsb (kentry_eqb (KRange E_AND 0 0)) k
&& existsb (kentry_eqb (KRange (EVar 224) 4295491576 34326181871)) k
&& existsb (kentry_eqb (KRange (EVar 376) 0 1)) k && existsb (kentry_eqb (KRange (EVar 6) 0 255)) k
&& existsb (kentry_eqb (KRange E_R 0 4095)) k
&& existsb (kentry_eqb (KRange E_PG 140735340871680 140737488351232)) k
&& lin_nowrapR k E_KB && lin_nowrapR k E_BK && lin_nowrapR k E_TOP && lin_nowrapR k E_BOT && lin_nowrapR k E_PG && lin_nowrapR k E_R
&& lin_nowrapR k e_sp0)%bool.
Section Geo.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Variable cs : acs.
Hypothesis GCHK : geo_chk cs = true.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : CSOK E cs R FULL model.
Ltac LINEQ e H :=
let Hn := fresh in
assert (Hn : lin_nowrapR (kn cs) e = true)
by (let G := fresh in pose proof GCHK as G; unfold geo_chk in G; repeat (let X := fresh in apply andb_prop in G as [G X]); assumption);
pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H; clear Hn;
unfold LZ in H;
match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
rewrite ?Z.add_0_r in H.
Ltac RANGE K H :=
let Hi := fresh in
assert (Hi : In K (kn cs))
by (apply hb_knb_In; let G := fresh in pose proof GCHK as G; unfold geo_chk in G; repeat (let X := fresh in apply andb_prop in G as [G X]); assumption);
pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model K HC Hi) as H; clear Hi; cbn [kentry_ok] in H.
#[using="GCHK"] Lemma geo_syn : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "J'5'6'J&E&LvR2&Q4%3221%511&Q1%93821&Q;%117&O%=3<21&Q=%11;&Q2%A3@21&Q<%11?&Q0%E3D21%G251%H2:1%I2?1").
Proof.
pose proof GCHK as G. unfold geo_chk in G. repeat (let X := fresh in apply andb_prop in G as [G X]).
repeat split; apply expr_eqb_eq; assumption.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs GCHK R FULL model HC"] Lemma geo_spb : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "J'5&QL&Kv9vR2&Q4%43321&QJ&H&Q;%116%3281+RPP0%6221%=281&QK%92:4%2241%B241'6'8&QM%129:z%53421%I271").
Proof.
destruct geo_syn as (S1 & S2 & _ & _). unfold rbase. rewrite S1, S2. unfold uE.
remember (bv_unsigned (edenot E E_KB)) as kb eqn:Ekb. remember (bv_unsigned (edenot E E_BK)) as bk eqn:Ebk.
LINEQ E_KB L1. rewrite <- Ekb in L1. LINEQ E_BK L2. rewrite <- Ebk in L2.
RANGE (KRange (EVar 225) 0 15) R1. RANGE (KRange (EVar 224) 4295491576 34326181871) R2. RANGE (KRange E_AND 0 0) R3.
cbn [edenot] in R1, R2. change (bv_unsigned (ev E 225)) with (VZ E 225) in R1. change (bv_unsigned (ev E 224)) with (VZ E 224) in R2.
unfold E_AND in R3. cbn [edenot] in R3. rewrite u_add64, u_and64, !u_mul64 in R3.
rewrite (u64_lit 65535), (u64_lit 4096) in R3 by lia.
replace (bv_unsigned (Z_to_bv 64 (-4096))) with 18446744073709547520 in R3 by (vm_compute; reflexivity).
change (bv_unsigned (ev E 225)) with (VZ E 225) in R3. change (bv_unsigned (ev E 224)) with (VZ E 224) in R3.
change 65535 with (Z.ones 16) in R3. rewrite Z.land_ones in R3 by lia. change (2 ^ 16) with 65536 in R3.
rewrite (Z.mod_small (4096 * VZ E 224) (2 ^ 64)) in R3 by lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (HA : (4096 * VZ E 224) mod 65536 = 4096 * VZ E 225) by lia.
subst kb bk. rewrite L1, L2. split; [|]; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs GCHK R FULL model HC"] Lemma geo_stk : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "Q7'5'6'8&Hv9&Q=vR2%211%5241&QJ&Q<%115%9281+XPPP0%5221%>3=71&QM+TP0%2261z%C3B21&QK&QO&F%E2D1%321<%A2>9%6221%C23;%82A1&QN+2+Q?%3221%=2J1%Q3261%Q4291%Q52A1%Q62G1").
Proof.
destruct geo_syn as (_ & _ & S3 & S4). rewrite S3, S4. unfold uE.
remember (bv_unsigned (edenot E E_TOP)) as top eqn:Et. remember (bv_unsigned (edenot E E_BOT)) as bot eqn:Eb.
remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. remember (bv_unsigned (edenot E E_PG)) as pg eqn:Ep.
remember (bv_unsigned (edenot E E_R)) as rr eqn:Er.
LINEQ E_TOP L1. rewrite <- Et in L1. LINEQ E_BOT L2. rewrite <- Eb in L2. LINEQ e_sp0 L3. rewrite <- Es in L3.
LINEQ E_PG L4. rewrite <- Ep in L4. LINEQ E_R L5. rewrite <- Er in L5.
RANGE (KRange (EVar 376) 0 1) R1. RANGE (KRange (EVar 6) 0 255) R2. RANGE (KRange E_R 0 4095) R3. RANGE (KRange E_PG 140735340871680 140737488351232) R4.
cbn [edenot] in R1, R2. change (bv_unsigned (ev E 376)) with (VZ E 376) in R1. change (bv_unsigned (ev E 6)) with (VZ E 6) in R2.
rewrite <- Er in R3. rewrite <- Ep in R4.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
repeat split; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs cs GCHK R FULL model HC"] Lemma geo_spa : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK ";'6'8&QM&Hv9&F%3221+@%6221z%:3921").
Proof.
unfold uE. remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. LINEQ e_sp0 L3. rewrite <- Es in L3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs GCHK R FULL model HC Hve Hfit"] Lemma geo_sp16 : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "=&QK&QJ&Hv9&F%3221+@%6221&QN+2+Q?%3221%<251").
Proof.
unfold uE. remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. LINEQ e_sp0 L3. rewrite <- Es in L3.
pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC) as U0.
pose proof (build_stack_bytes_within_span APH0 sp argv envp uid hw rdraw) as SPAN.
destruct (bsb_ge APH0 sp rdraw argv envp uid hw) as [GE _].
unfold entry_stack_fits, sp_window_hi in Hfit. lia.
Qed.
End Geo.
Lemma geo_chk_0 : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "7'6'1&Q3&QA%211(4%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma geo_chk_1 : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "7'6'1&Q3&QB%211(4%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma art_lits_chk_0 : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "7'6'1&N&QA%211(4%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma art_lits_chk_1 : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "7'6'1&N&QB%211(4%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma art_sym_chk_0 : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "7'6'1&Q7&QA%211(4%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma art_sym_chk_1 : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "7'6'1&Q7&QB%211(4%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma art_lazy_chk_0 : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "7'6'1&Q6&QA%211(4%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma art_lazy_chk_1 : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "7'6'1&Q6&QB%211(4%63521"). Proof. vm_compute. reflexivity. Qed.
Section Inst.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Variable BUDGET : Z.
Hypothesis BUD_ge : 2 ^ 34 <= BUDGET.
Hypothesis BUD_hi : BUDGET <= 2 ^ 39 - 2 ^ 35.
Let FSH : art_fsinv_handoff := art_fsinv_handoff_proved.
#[using="BUD_ge"] Lemma inst_bud : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "B'5&QKzv0%3221&QG%5241&QH%7261&QL&QN+2+QN%3221%5271%?271%@2:1%A2=1").
Proof. unfold JbtInv.KMAX, JbtInv.LENMAX. lia. Qed.
#[using="Hsp Hva Hve Hfit BUD_ge BUD_hi FSH"] Theorem as0_art_handoff_h : ltac2:(TCodec.tc2 tcn__Jb0ArtHandoffInstK "R@'2&7r1u2%3221'I&@y5'R:yR0%211%5241'3y8%611%311p061'<'G&Q@&Q?&B&C&Q>vR9vR8vR1vR0vR3vR;vR6%9887654321&D%17:986543vR4r4&QCr6%211r3r2%G;FED:876321Q7&QI'QD&>&=%116%311&;%11N&?%115&Q9r7%B11r5%4221v0&QF&Q:%1256&QE&Q5+XP0&QN+2+Q2%3221&Q8%12?>&M%11O%N?MIGE@?><;:953Q11p0Q01pT@QI1pFQK1pQ4R11pDR81p0R:1pT<R?1").
Proof.
intros h Hh E R FULL model HC.
assert (CH : as0_chk (HSA h) = true /\ art_lits_chk (HSA h) = true /\ art_sym_chk (HSA h) = true /\ geo_chk (HSA h) = true /\ art_lazy_chk (HSA h) = true).
{ destruct h as [|[|h]]; [| |lia].
- exact (conj as0_chk_0 (conj art_lits_chk_0 (conj art_sym_chk_0 (conj geo_chk_0 art_lazy_chk_0)))).
- exact (conj as0_chk_1 (conj art_lits_chk_1 (conj art_sym_chk_1 (conj geo_chk_1 art_lazy_chk_1)))). }
destruct CH as (C0 & CL & CS & CG & CZ).
destruct (HSA_numbers h Hh) as (N1 & N2 & N3 & N4).
pose proof (geo_spb sp brk0 rdraw argv envp uid hw fs (HSA h) CG E R FULL model HC) as GS.
pose proof (geo_stk sp brk0 rdraw argv envp uid hw fs (HSA h) CG E R FULL model HC) as GT.
pose proof (geo_sp16 sp brk0 rdraw argv envp uid hw fs Hsp Hva (HSA h) CG E R FULL model HC Hve Hfit) as G16.
pose proof (geo_spa sp brk0 rdraw argv envp uid hw fs (HSA h) CG E R FULL model HC) as GA.
assert (BL : a_eager (HSA h) + a_abytes (HSA h) + 2 ^ 34 + BUDGET <= AsanInitK.LIMIT) by (unfold AsanInitK.LIMIT, target_alloc_limit; lia).
assert (GP : AsanCeil.bottomup_floor + JbtInv.LENMAX + (a_totsz (HSA h) + BUDGET)
+ (Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps (HSA h))) + JbtInv.KMAX) * (JbtInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling).
{ rewrite N4, asan0_res_eq. cbn [length Nat.add]. change (Z.of_nat 21) with 21. unfold JbtInv.KMAX, JbtInv.LENMAX, AsanCeil.bottomup_floor, AsanCeil.alloc_ceiling. lia. }
eapply (as0_art_handoff sp brk0 rdraw argv envp uid hw fs Hsp Hva (HSA h)); try eassumption; first [exact inst_bud | exact FSH].
Qed.
End Inst.

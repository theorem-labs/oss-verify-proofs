(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ja0DefsK Ja0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
Ja0HandoffK Ja0HSK_0 Ja0HSK_1 Ja0MainTableK Ja0HandoffInstK Ja0ArtHandoffK Ja0ArtHandoffInstK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0StkShK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0ArtHandoffK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0HSK_0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0HSK_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0HandoffInstK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0StkShK."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nat"; "1option"; "1true"; "2eq"; "3lt"; "4Z"; "0E"; "0FULL"; "5Fs"; "6entry_stack_fits"; "6valid_argv"; "6valid_envp"; "6valid_sp"; "7EntryDraw"]; ["8Model"; "9bvmap"; "0R"; ":LIMIT"; ":SINV0"; ":argH0"; ";cs_ok"; ";uE"; "<env"; "=byte_at"; "=in_shadow_of"; ">topE"; "?APH0"; "?ASAN0"; "?ASEGS0"; "@HS_0"]; ["AHS_1"; "BHSA"; "Cstksh_chk"; "Dmax"; "Dpow"; "Dsub"; "0argv"; "0brk0"; "0cs"; "0envp"; "0fs"; "0h"; "0hw"; "0model"; "0rdraw"; "0sp"]; ["Ebv"; "Ebv_unsigned"; "0uid"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia2.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition E_SHB : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EVar 10)).
Definition E_SHL : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EVar 10))) (ELit 17592187092992).
Definition K_STKSH : kentry := KZero (SA E_SHB 2146402304) E_SHL.
Definition stksh_chk (cs : acs) : bool :=
let k := kn cs in (existsb (kentry_eqb K_STKSH) k && lin_nowrapR k E_SHB && lin_nowrapR k E_SHL)%bool.
Lemma stksh_chk_0 : ltac2:(TCodec.tc2 tcn__Ja0StkShK "7'5'0&Q2&O%211(4%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma stksh_chk_1 : ltac2:(TCodec.tc2 tcn__Ja0StkShK "7'5'0&Q2&Q0%211(4%63521"). Proof. vm_compute. reflexivity. Qed.
Section StkSh.
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
#[local] Notation usp := (bv_unsigned sp).
Variable cs : acs.
Hypothesis SCHK : stksh_chk cs = true.
Hypothesis GCHK : geo_chk cs = true.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : CSOK E cs R FULL model.
Ltac LINEQS e H :=
let Hn := fresh in
assert (Hn : lin_nowrapR (kn cs) e = true)
by (let G := fresh in pose proof SCHK as G; unfold stksh_chk in G; repeat (let X := fresh in apply andb_prop in G as [G X]); assumption);
pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H; clear Hn;
unfold LZ in H;
match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
rewrite ?Z.add_0_r in H.
#[using="brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit SCHK GCHK R model HC"] Theorem stksh_main : ltac2:(TCodec.tc2 tcn__Ja0StkShK "K'7&J&Q5&QAyR0vQ?%3221+XPPP0%6221&Q3&Gv8&KvQ8%211%5241%72:1%?219r1%B3;21&Iv9r2z%43321p061pS8J1").
Proof.
intros x Hx.
assert (Hin : In K_STKSH (kn cs)).
{ apply hb_knb_In. pose proof SCHK as G. unfold stksh_chk in G. repeat (let X := fresh in apply andb_prop in G as [G X]). assumption. }
destruct (hb_zero_k ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ _ HC Hin) as [Hf Hz].
unfold estart, elenZ in Hz. cbn [a_base a_off] in Hz.
remember (bv_unsigned (edenot E E_SHB)) as shb eqn:Eb. remember (bv_unsigned (edenot E E_SHL)) as shl eqn:El.
LINEQS E_SHB L1. rewrite <- Eb in L1. LINEQS E_SHL L2. rewrite <- El in L2.
pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC) as U0.
destruct (geo_stk sp brk0 rdraw argv envp uid hw fs cs GCHK E R FULL model HC) as (_ & _ & _ & _ & TOP).
assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
pose proof (Z.ge_le _ _ (Z.le_ge _ _ (proj1 (u64_range (ev E 6))))) as V6. change (bv_unsigned (ev E 6)) with (VZ E 6) in V6.
unfold in_shadow_of, S, SB in Hx.
set (mx := Z.max usp (uE E (topE cs))) in *.
replace (usp - 8388608 + (mx - (usp - 8388608)) - 1) with (mx - 1) in Hx by ring.
assert (D1 : shb - 1048576 <= (usp - 8388608) / 8).
{ replace (shb - 1048576) with ((8 * shb - 8388608) / 8) by (replace (8 * shb - 8388608) with ((shb - 1048576) * 8) by ring; apply Z.div_mul; lia).
apply Z.div_le_mono; lia. }
assert (D2 : (mx - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
unfold byte_at. replace x with (shb + 2146402304 + (x - (shb + 2146402304))) by ring. apply Hz. lia.
Qed.
#[using="brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit cs SCHK GCHK E R model HC"] Theorem stksh_main_hi : ltac2:(TCodec.tc2 tcn__Ja0StkShK "G'7&J&Q5&QAyR0vQ?%3221+XPPP0%6221&Q4+2+Q?%3221%;215r1%>3721&Iv9r2z%43321p061pS8F1").
Proof.
intros x Hx.
assert (Hin : In K_STKSH (kn cs)).
{ apply hb_knb_In. pose proof SCHK as G. unfold stksh_chk in G. repeat (let X := fresh in apply andb_prop in G as [G X]). assumption. }
destruct (hb_zero_k ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ _ HC Hin) as [Hf Hz].
unfold estart, elenZ in Hz. cbn [a_base a_off] in Hz.
remember (bv_unsigned (edenot E E_SHB)) as shb eqn:Eb. remember (bv_unsigned (edenot E E_SHL)) as shl eqn:El.
LINEQS E_SHB L1. rewrite <- Eb in L1. LINEQS E_SHL L2. rewrite <- El in L2.
pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC) as U0.
destruct (geo_stk sp brk0 rdraw argv envp uid hw fs cs GCHK E R FULL model HC) as (_ & _ & _ & _ & TOP).
assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
pose proof (Z.ge_le _ _ (Z.le_ge _ _ (proj1 (u64_range (ev E 6))))) as V6. change (bv_unsigned (ev E 6)) with (VZ E 6) in V6.
unfold in_shadow_of, S, SB in Hx.
set (mx := 2 ^ 47) in *.
replace (usp - 8388608 + (mx - (usp - 8388608)) - 1) with (mx - 1) in Hx by ring.
assert (D1 : shb - 1048576 <= (usp - 8388608) / 8).
{ replace (shb - 1048576) with ((8 * shb - 8388608) / 8) by (replace (8 * shb - 8388608) with ((shb - 1048576) * 8) by ring; apply Z.div_mul; lia).
apply Z.div_le_mono; lia. }
assert (D2 : (mx - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
unfold byte_at. replace x with (shb + 2146402304 + (x - (shb + 2146402304))) by ring. apply Hz. lia.
Qed.
End StkSh.
Theorem as0_stksh_main : ltac2:(TCodec.tc2 tcn__Ja0StkShK "S3'Q@yR0%211'?'1y8%611%311%411&:&>r8%211&<r6%211&=%113&;r;r7%332:1'2&6r1u2%3221'H&Ay5%221L'3%11Jp0O1'@'F&N&M&C&D&LrBr@rAr?r>r=r<%9887654321&E%17:986543r4&Q1%11Q7r3r2%E;DCB86Q55321Q0'7&J&Q5&QArD%22QM1+XPPP0%5221&Q3&G&K%@1QI%211%42QH1%6291%=218%?391QA&Ir5z%332F1p051pS8F1p0H1pRLQ?1pDQA1pQ6QE1pBQI1p0QK1pRHR01p0R21p0R71p0R:1p0R>1pRFRB1pRJRJ1pS6RK1pRDRF1pR>RG1pRNRM1pR@RO1pS0S01").
Proof.
intros sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit h Hh E R FULL model HC.
destruct h as [|[|h]]; [| |lia].
- exact (stksh_main sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit HS_0 stksh_chk_0 geo_chk_0 E R FULL model HC).
- exact (stksh_main sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit HS_1 stksh_chk_1 geo_chk_1 E R FULL model HC).
Qed.
Theorem as0_stksh_main_hi : ltac2:(TCodec.tc2 tcn__Ja0StkShK "S0'Q@yR0%211'?'1y8%611%311%411&:&>r8%211&<r6%211&=%113&;r;r7%332:1'2&6r1u2%3221'H&Ay5%221L'3%11Jp0O1'@'F&N&M&C&D&LrBr@rAr?r>r=r<%9887654321&E%17:986543r4&Q1%11Q7r3r2%E;DCB86Q55321Q0'7&J&Q5&QArD%22QM1+XPPP0%5221&Q4+2+Q?%3221%:215%<361Q>&Ir5z%332C1p051pS8C1p0E1pRLQ<1pDQ>1pQ6QB1pBQF1p0QH1pRHQM1p0QO1p0R41p0R71p0R;1pRFR?1pRJRG1pS6RH1pRDRC1pR>RD1pRNRJ1pR@RL1pS0RM1").
Proof.
intros sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit h Hh E R FULL model HC.
destruct h as [|[|h]]; [| |lia].
- exact (stksh_main_hi sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit HS_0 stksh_chk_0 geo_chk_0 E R FULL model HC).
- exact (stksh_main_hi sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit HS_1 stksh_chk_1 geo_chk_1 E R FULL model HC).
Qed.

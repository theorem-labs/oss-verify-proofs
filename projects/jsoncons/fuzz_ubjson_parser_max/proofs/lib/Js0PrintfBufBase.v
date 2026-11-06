(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2 SymExec2Sound SymRun SymDrive
RefMemcpyLib AgentLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SymAux RefPrintfLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0PrintfBufBase () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Decimal."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Number."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0PrintfBufBase.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1O"; "1bool"; "1list"; "1nat"; "1option"; "1true"; "2D0"; "2D1"; "2D2"; "2D8"; "2D9"; "2Nil"; "3I"; "3and"; "3eq"; "4of_num_uint"]; ["4sub"; "5UIntDecimal"; "6le"; "6lt"; "7nth"; "8Z"; "0E"; "9store_ok"; ":bvmap"; "0R"; ";allregs32"; ";pf_kn"; ";pf_sr"; "<getr"; "=wseg_ok"; ">ELit"]; [">edenot"; ">env"; ">ev"; ">expr"; "?know_ok"; "?regs_ok"; "@loaded_segments"; "Aadd"; "Ale"; "Aof_nat"; "0a"; "0can"; "0i"; "0m"; "0mem"; "0n"]; ["0regs"; "0sp"; "0sr"; "BBV"; "BZ_to_bv"; "Bbv"; "0w"]]).
Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition PF_FR : Z := 1056.
Record pfH (mem : word -> option byte) (sp : word) (w can : Z) : Prop := PFH {
Psp16 : bv_unsigned sp mod 16 = 0;
PspLo : 0xe9420 <= bv_unsigned sp;
PspHi : bv_unsigned sp <= 0x7fffffffffff;
Pstk : stk_ok RSEGS mem sp PF_FR;
Pimg : forall i, 0x10000 <= i < 0xb5000 -> mem (Z_to_bv 64 i) = None;
Pflags : rdn RSEGS mem (Z_to_bv 64 0xb60d0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
Pwend : rdn RSEGS mem (Z_to_bv 64 0xb60f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe8850));
Pwpos : rdn RSEGS mem (Z_to_bv 64 0xb60f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 w));
Pw : 0xe8450 <= w <= 0xe884e;
Pbsz : rdn RSEGS mem (Z_to_bv 64 0xb6130) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
Plock : rdn RSEGS mem (Z_to_bv 64 0xb615c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
Plbf : rdn RSEGS mem (Z_to_bv 64 0xb6160) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
Pcan : rdn RSEGS mem (Z_to_bv 64 0xe7ed0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
Pcan64 : 0 <= can < 2 ^ 64 }.
Definition pf_vals (regs : bvmap 5 word) (sp : word) (w can : Z) : list word :=
[sp; Z_to_bv 64 w; Z_to_bv 64 can] ++ junk_vals regs.
Definition pfE (regs : bvmap 5 word) (sp : word) (w can : Z) : env :=
Env (vals_ev (pf_vals regs sp w can)) (blobs_ev []).
Definition pf_sr : list expr :=
Eval cbv in (map (fun i => match i with
| 0 => ELit 0 | 1 => ELit 0x33f58 | 2 => EVar 0 | 11 => ELit 0
| _ => EVar (3 + i) end)%nat (seq 0 32)).
Definition pf_kn : list kentry :=
[KAlign (EVar 0) 16; KRange (EVar 0) 0xe9420 0x7fffffffffff;
KWr (SA (EVar 0) (-1056)) 1056;
KImg 0x10000 0xb5000;
KWord (SA (ELit 0) 0xb60d0) 4 (ELit 5);
KWord (SA (ELit 0) 0xb60f0) 8 (ELit 0xe8850);
KWord (SA (ELit 0) 0xb60f8) 8 (EVar 1);
KRange (EVar 1) 0xe8450 0xe884e;
KWord (SA (ELit 0) 0xb6130) 8 (ELit 1024);
KWord (SA (ELit 0) 0xb615c) 4 (ELit 4294967295);
KWord (SA (ELit 0) 0xb6160) 4 (ELit 4294967295);
KWord (SA (ELit 0) 0xe7ed0) 8 (EVar 2);
KWr (SA (ELit 0) 0xb5000) 0x34000;
KWr (SA (EVar 1) 0) 2].
Definition allregs32 : list reg :=
[0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma nth_allregs32 : ltac2:(TCodec.tc2 tcn__Js0PrintfBufBase "H'3&Cr1uQ0%3221'>'QEy5%211&Dr2&J(QCz(<%33821%748651&QD&Q9%119%32=1%@3=51p0B1pS0G1").
Proof.
intros n Hn.
destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
Lemma regs_ok_by_idx : ltac2:(TCodec.tc2 tcn__Js0PrintfBufBase "Q<'Q1'2'Q3%211&Hy5'QEyR0%211%5241'3&Cr1uQ0%3221'>&Mr3&D%=1>r2&J(QCz(<%33D21%847651%;2:1&Q0r5r4(O%119%?4O=31%6251%D3K81p0F1pRJK1&Q5%139FCp031pQDQ01pS6Q71pQ>Q;1").
Proof.
intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
reflexivity.
- pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_allregs32 in Hx by apply ridx_range.
rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
Section Entry.
Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (w can : Z).
Hypothesis PH : pfH mem sp w can.
Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x33f58.
Hypothesis R2 : getr regs 2 = sp.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.
Let E := pfE regs sp w can.
Lemma ev_junk : ltac2:(TCodec.tc2 tcn__Js0PrintfBufBase "O'3'='Bu3r1%3221&CuQ3%2241%8241'>'QEyR0%211&Q2vFr2%3221&MvQ@&QDy5&Q9&@%128E%311%6251%9281%B3?;1p0D1pRJN1").
Proof.
intros i Hi. unfold E, pfE, pf_vals. cbn [ev]. unfold vals_ev.
replace i with (length [sp; Z_to_bv 64 w; Z_to_bv 64 can] + (i - 3))%nat at 1 by (cbn; lia).
rewrite app_nth2_plus. unfold junk_vals.
rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
Qed.
Lemma ev0 : ltac2:(TCodec.tc2 tcn__Js0PrintfBufBase ":'>'QEyR0%211&Q2vF(0%3221vQA%93621"). Proof. reflexivity. Qed.
Lemma ev1 : ltac2:(TCodec.tc2 tcn__Js0PrintfBufBase "<'>'QEyR0%211&Q2vFu1%3221&QDvQF%2281%;3841"). Proof. reflexivity. Qed.
Lemma ev2 : ltac2:(TCodec.tc2 tcn__Js0PrintfBufBase "<'>'QEyR0%211&Q2vFu2%3221&QDvQ;%2281%;3841"). Proof. reflexivity. Qed.
Lemma pf_regs_ok : ltac2:(TCodec.tc2 tcn__Js0PrintfBufBase "5&Q5vF&LvQ@%43321").
Proof.
apply regs_ok_by_idx. intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
cbn [nth pf_sr allregs32 edenot].
1: apply getr_zero.
1: exact R1.
1: exact R2.
9: exact R11.
all: rewrite ev_junk by lia; f_equal; apply bv_eq; reflexivity.
Qed.
Lemma wseg_data : OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim.wseg_ok Plain.M.loaded_segments (Z_to_bv 64 0xb5000) 212992 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma data_store_ok : ltac2:(TCodec.tc2 tcn__Js0PrintfBufBase "Q5'QEyR0%211'4y8%511%311p051'E'3&Q8+fdP0r2%3221&Q7r3&Q9%115%4231+mTP0%:221'>'1&G&Q6r5&QDr4%22K1%64541>(5%:3921p0<1p0D1pS0I1pRFK1pRLM1").
Proof.
intros m a n Ha Hn.
eapply (store_ok_window RSEGS m (Z_to_bv 64 0xb5000) (Z_to_bv 64 a) 212992 n 0xb5000 0xe9000);
[ apply u64_lit; lia | reflexivity | cbn; lia | apply wseg_data
| rewrite u64_lit by lia; lia | rewrite u64_lit by lia; lia ].
Qed.
Lemma pf_know_ok : ltac2:(TCodec.tc2 tcn__Js0PrintfBufBase "6&Q4&Q6vFvQ>&K%544321").
Proof.
destruct PH. pose proof (u64_range sp) as Hsp.
assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
unfold pf_kn. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
- apply kalign_intro; [lia|]. cbn [edenot]. rewrite ev0. assumption.
- apply krange_intro. cbn [edenot]. rewrite ev0. lia.
- apply (kwr_of_stk_ok RSEGS E mem (EVar 0) sp 1056); [apply ev0 | exact Pstk0 | unfold PF_FR; lia].
- apply kimg_intro; [lia | lia | exact Pimg0].
- eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pflags0].
- eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pwend0].
- eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev1 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pwpos0].
- apply krange_intro. cbn [edenot]. rewrite ev1, u64_lit by lia. lia.
- eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pbsz0].
- eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Plock0].
- eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Plbf0].
- eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev2 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pcan0].
- cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
- cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite ev1, u64_lit by lia.
split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
Qed.
End Entry.
End FPX_1.

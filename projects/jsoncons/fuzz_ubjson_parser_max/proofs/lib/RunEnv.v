(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__RunEnv () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RunEnv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RunEnv.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RunEnv.FPX_1.WithEnv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RunEnv.FPX_2."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1false"; "1list"; "1nil"; "1option"; "1prod"; "2eq"; "3Z"; "4Fs"; "5Creds"; "5FdEntry"; "5InputStream"; "5Model"; "5NetQueue"]; ["5PipeBuf"; "5ProcInput"; "5VmMaps"; "5in_fs"; "5in_stdin"; "5init_model"; "5m_abort_terminal"; "5m_conn_ix"; "5m_creds"; "5m_fds"; "5m_fs"; "5m_halted"; "5m_killed"; "5m_net"; "5m_nofile"; "5m_pipes"]; ["5m_rlimit_core"; "5m_sigabrt_pending"; "5m_sigmask"; "5m_stdin"; "5m_tid"; "5m_vm_lazy"; "5m_vm_materialized"; "5m_vmmaps"; "5mkVmMapsFull"; "5with_fds"; "5with_fs"; "5with_halted"; "5with_stdin"; "5with_tid"; "5with_vmmaps"; "0RE"]; ["8mkModelE"; "7re_abort"; "7re_creds"; "7re_net"; "7re_nofile"; "7re_sigmask"; "9fds_init"; "6mkModelE"; "6run_env_of"; "0brk0"; "0c"; "0fds"; "0fds'"; "0fs"; "0fs'"; "0halted"]; ["0inp"; "0lim"; "0mbase"; "0reserved"; "0rlim"; "0s"; "0sp"; "0stdin"; ":Z_to_bv"; ":bv"; "0t"; "0tid"; "0vm"; "0vm'"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Class RunEnv := mkRunEnv {
re_creds : Creds;
re_net : NetQueue;
re_nofile : word;
re_sigmask : word;
re_abort : bool;
re_urandom : InputStream
}.
Definition run_env_of (inp : ProcInput) : RunEnv :=
{| re_creds := mkCreds (in_uid inp) (in_uid inp) (in_uid inp)
(in_gid inp) (in_gid inp) (in_gid inp) (in_groups inp);
re_net := in_net inp;
re_nofile := in_nofile inp;
re_sigmask := in_sigmask inp;
re_abort := in_abort_terminal inp;
re_urandom := in_urandom inp |}.
Section WithEnv.
Context {RE : RunEnv}.
Definition mkModelE (fds : list (word * FdEntry)) (vm : VmMaps)
(stdin : InputStream) (fs : Fs.Fs) (halted : option word)
(tid : option word) (rlim : option (list byte)) : Model :=
with_abort_terminal re_abort
(with_sigmask re_sigmask
(with_nofile re_nofile
(with_net re_net (with_urandom re_urandom (with_creds re_creds (mkModel fds vm stdin fs halted tid rlim)))))).
Lemma m_fds_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q5'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&I&Q@r7r6r5r4r3r2r1%877654321%:11%<3F19pT:>1pTHC1pT0D1pSLG1pT@I1pTJK1pSHM1").
Proof. reflexivity. Qed.
Lemma m_vmmaps_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q5'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&Q7&Q@r7r6r5r4r3r2r1%877654321%:11%<3E18pT:>1pTHC1pT0D1pSLG1pT@I1pTJK1pSHM1").
Proof. reflexivity. Qed.
Lemma m_stdin_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q5'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&Q3&Q@r7r6r5r4r3r2r1%877654321%:11%<3D17pT:>1pTHC1pT0D1pSLG1pT@I1pTJK1pSHM1").
Proof. reflexivity. Qed.
Lemma m_fs_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q5'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&J&Q@r7r6r5r4r3r2r1%877654321%:11%<3C16pT:>1pTHC1pT0D1pSLG1pT@I1pTJK1pSHM1").
Proof. reflexivity. Qed.
Lemma m_halted_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q5'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&K&Q@r7r6r5r4r3r2r1%877654321%:11%<3A15pT:>1pTHC1pT0D1pSLG1pT@I1pTJK1pSHM1").
Proof. reflexivity. Qed.
Lemma m_tid_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q5'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&Q4&Q@r7r6r5r4r3r2r1%877654321%:11%<3A14pT:>1pTHC1pT0D1pSLG1pT@I1pTJK1pSHM1").
Proof. reflexivity. Qed.
Lemma m_rlimit_core_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q5'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&Q0&Q@r7r6r5r4r3r2r1%877654321%:11%<3=13pT:>1pTHC1pT0D1pSLG1pT@I1pTJK1pSHM1").
Proof. reflexivity. Qed.
Lemma m_vm_lazy_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q9'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8%A2>>%C11&Q5&Q@r7r6r5r4r3r2r1%877654321%:11(5%11>%@3>31pT:B1pTHG1pT0H1pSLK1pT@M1pTJO1pSHQ11").
Proof. reflexivity. Qed.
Lemma m_vm_materialized_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q8'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8%B1>&Q6&Q@r7r6r5r4r3r2r1%877654321%:11(5%11K%?3>31pT:A1pTHF1pT0G1pSLJ1pT@L1pTJN1pSHQ01").
Proof. reflexivity. Qed.
Lemma m_pipes_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q:'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&@%B2?1%D11&O&Q@r7r6r5r4r3r2r1%877654321%:11(5%11>%A3>31pT:C1pTHH1pT0I1pSLL1pT@N1pTJQ01pSHQ21").
Proof. reflexivity. Qed.
Lemma m_creds_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q9'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8';&H&Q@r7r6r5r4r3r2r1%877654321%:11&QBvQ?%211%@3?41pT:B1pTHG1pT0H1pSLK1pT@M1pTJO1pSHQ11").
Proof. reflexivity. Qed.
Lemma m_net_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q9'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8'?&M&Q@r7r6r5r4r3r2r1%877654321%:11&QCvQ?%211%@3?41pT:B1pTHG1pT0H1pSLK1pT@M1pTJO1pSHQ11").
Proof. reflexivity. Qed.
Lemma m_nofile_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q8'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&N&Q@r7r6r5r4r3r2r1%877654321%:11&QDvQ?%211%?3L41pT:A1pTHF1pT0G1pSLJ1pT@L1pTJN1pSHQ01").
Proof. reflexivity. Qed.
Lemma m_sigmask_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q8'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&Q2&Q@r7r6r5r4r3r2r1%877654321%:11&QEvQ?%211%?3L41pT:A1pTHF1pT0G1pSLJ1pT@L1pTJN1pSHQ01").
Proof. reflexivity. Qed.
Lemma m_abort_terminal_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q9'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8'2&F&Q@r7r6r5r4r3r2r1%877654321%:11&QAvQ?%211%@3?41pT:B1pTHG1pT0H1pSLK1pT@M1pTJO1pSHQ11").
Proof. reflexivity. Qed.
Lemma m_killed_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q7'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&L&Q@r7r6r5r4r3r2r1%877654321%:11(0%11J%>3C31pT:@1pTHE1pT0F1pSLI1pT@K1pTJM1pSHO1").
Proof. reflexivity. Qed.
Lemma m_sigabrt_pending_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q7'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8'2&Q1&Q@r7r6r5r4r3r2r1%877654321%:11(3%>3=21pT:@1pTHE1pT0F1pSLI1pT@K1pTJM1pSHO1").
Proof. reflexivity. Qed.
Lemma m_conn_ix_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q8'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8&G&Q@r7r6r5r4r3r2r1%877654321%:11&R8z%22L1%?3L41pT:A1pTHF1pT0G1pSLJ1pT@L1pTJN1pSHQ01").
Proof. reflexivity. Qed.
Lemma with_fds_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q9'4'7'R9yR0%211'<%5221%711'B'=&:'6%118y8%<11%?11%511'8'>&Q9r8&Q@r7r6r5r4r3r2r1%877654321%;2:1%:7;876543%?3>21pT:A1pTHF1pT0G1pSLJ1pT@L1pTJN1pSHQ01pSJQ11").
Proof. reflexivity. Qed.
Lemma with_vmmaps_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q9'B'4'7'R9yR0%211'<%5221%711'=&:'6%117y8%;11%>11%511'8'>&Q>r8&Q@r7r6r5r4r3r2r1%877654321%;2:1%:79;76543%?3>21pT:A1pTHF1pT0G1pSLJ1pT@L1pTJQ61pSHO1pTLQ81").
Proof. reflexivity. Qed.
Lemma with_tid_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q;'R9yR0%211'4'7'<%2241%411'B'=&:'6%11:y8%>11%<11%511'8'>&Q=r8&Q@r7r6r5r4r3r2r1%877654321%;2:1(1%12N<%<7;:98715%A3@41pT:C1pTHH1pT0I1pSLL1pT@N1pTJQ01pSHQ21pTFQ81").
Proof. reflexivity. Qed.
Lemma with_halted_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q;'R9yR0%211'4'7'<%2241%411'B'=&:'6%11:y8%>11%<11%511'8'>&Q;r8&Q@r7r6r5r4r3r2r1%877654321%;2:1(1%12N<%<7;:98165%A3@41pT:C1pTHH1pT0I1pSLL1pT@N1pTJQ01pSHQ21pSFQ81").
Proof. reflexivity. Qed.
Lemma with_fs_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q9&:'4'7'R9yR0%211'<%5221%711'B'='6%117y8%;11%>11%511'8'>&Q:r8&Q@r7r6r5r4r3r2r1%877654321%;2:1%:7987;543%?3>21pT:A1pTHF1pT0G1pSLQ41pT@K1pTJM1pSHO1pSNQ81").
Proof. reflexivity. Qed.
Lemma with_stdin_mkModelE : ltac2:(TCodec.tc2 tcn__RunEnv "Q9'='4'7'R9yR0%211'<%5221%711'B&:'6%117y8%;11%>11%511'8'>&Q<r8&Q@r7r6r5r4r3r2r1%877654321%;2:1%:798;6543%?3>21pT:A1pTHF1pT0G1pSLJ1pT@Q51pTJM1pSHO1pT<Q81").
Proof. reflexivity. Qed.
End WithEnv.
End FPX_1.
#[export] Hint Rewrite @m_fds_mkModelE @m_vmmaps_mkModelE @m_stdin_mkModelE @m_fs_mkModelE
@m_halted_mkModelE @m_tid_mkModelE @m_rlimit_core_mkModelE @m_vm_lazy_mkModelE
@m_vm_materialized_mkModelE @m_pipes_mkModelE @m_creds_mkModelE @m_net_mkModelE
@m_nofile_mkModelE @m_sigmask_mkModelE @m_abort_terminal_mkModelE @m_killed_mkModelE
@m_sigabrt_pending_mkModelE @m_conn_ix_mkModelE
@with_fds_mkModelE @with_vmmaps_mkModelE @with_tid_mkModelE @with_halted_mkModelE
@with_fs_mkModelE @with_stdin_mkModelE : model.
Section FPX_2. Context {fx : PropExec.FPState}.
Definition fds_init : list (word * FdEntry) :=
[ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
(Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
(Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].
Lemma init_model_E : ltac2:(TCodec.tc2 tcn__RunEnv "Q='4'7'R9yR0%211%4211%611'9'A'8'>&Er6r5r4r3r2r1%76654321&QG&QH%114&QF(Q8(5%11D%38>11==:<;&D%11;&C%11=(0%11Ly8%Q011%Q311%511%B8@?;97551%M3LD1pT2O1pT4Q11pT>Q51pT6Q61pSDQ71pT8Q61").
Proof. reflexivity. Qed.
Lemma with_tid_init_model_E : ltac2:(TCodec.tc2 tcn__RunEnv "QC'R9yR0%211'4'7%1233%311'9'A'8'>&Q=r7&Er6r5r4r3r2r1%76654321%:291&QG&QH%115&QF(Q8(5%11G%38?11>>;=<&D%11<&C%11>(0%11Q1(1%12Q3Iy8%Q711%Q511%711%D8BA=;9751%Q23Q1F1pT2Q41pT4Q61pT>Q<1pT6Q=1pSDQ>1pT8Q;1pTHQ@1").
Proof. reflexivity. Qed.
End FPX_2.

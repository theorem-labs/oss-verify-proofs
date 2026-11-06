(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec StreamExec WallSim StreamSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__DrainSim () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrainSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrainSim.Drain."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ExitSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.WallSim."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"]; ["2and"; "2eq"; "2ex"; "2not"; "2or"; "3map"; "4Z"; "5len_word"; "6check_read"; "7CheckOk"; "7check_result"; "8Ok"; "8Unmodeled"; "9machine_state"; "9ms_gpr"; "9ms_svc_pending"]; ["9ms_writable_byte"; "9set_gpr0"; ":SError"; ":SNext"; ":advance_past_svc"; ":apply_effect"; ":config"; ":is_prefix"; ":mkCfg"; ":sstep"; ":star"; ":step_to"; ":sys_input"; ";syscall_spec"; "<ExitEv"; "<FdChannel"]; ["<FdEntry"; "<IEof"; "<InputStream"; "<MemCopy"; "<Model"; "<ReadEv"; "<SyscallEffect"; "<WriteEv"; "<access_okb"; "<event"; "<fd_lookup"; "<m_fds"; "<m_fs"; "<m_halted"; "<m_stdin"; "<m_vm_lazy"]; ["<mkEffectU"; "<read_bytes_map"; "<stream_take"; "<with_stdin"; "=fd32"; ">buf_modeled"; ">fd1chan"; ">msteps"; "@dinv"; "@to_out"; "?reads"; "?reads_ch"; "Ato_exit"; "BM_loop"; "Cto_wall_tail"; "Dle"]; ["Dof_nat"; "0blocks"; "0bs"; "0buf"; "0c"; "0c'"; "0cnt"; "0eff"; "0evs"; "0m"; "0model"; "0model'"; "0ms"; "0ms'"; "0rch"; "0rest"]; ["0s"; "0segs"; "0st"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0tr"; "0w"; "0x8"]]).
Section Proc.
Context {A : Type}.
Variable f : A -> byte -> option A.
Fixpoint procs (a : A) (bs : list byte) : option A :=
match bs with
| [] => Some a
| b :: rest => match f a b with Some a' => procs a' rest | None => None end
end.
Lemma procs_app : forall bs1 bs2 a,
procs a (bs1 ++ bs2) =
match procs a bs1 with Some a' => procs a' bs2 | None => None end.
Proof.
induction bs1 as [|b bs1 IH]; intros bs2 a; [reflexivity|].
cbn [procs app]. destruct (f a b); [apply IH | reflexivity].
Qed.
End Proc.
Definition block_ok (cnt : word) (bs : list byte) : Prop :=
(1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z.
Definition reads_ch (rch : word) (blocks : list (list byte)) : list event :=
flat_map (fun bs => map (ReadEv rch) bs) blocks.
Lemma reads_ch_cons : ltac2:(TCodec.tc2 tcn__DrainSim "M'S4yR0%211'8y8%511%311%411'A'QI%711&R;r3(5r2r1%33:21%6251&3&E(QE%119%34A=18%<2;8%63?21%A3?81pU4C1pU6E1pUNJ1").
Proof. reflexivity. Qed.
Definition reads (blocks : list (list byte)) : list event :=
reads_ch (Z_to_bv 64 0) blocks.
Lemma reads_cons : ltac2:(TCodec.tc2 tcn__DrainSim "M'8'S4y8%211%411%511'A'QI%811&R:(5r2r1%33921%511&3&E(QE&S3yR0z%3221%511%74D@1<%?1<%:3B21%D3B<1pU4F1pU6H1").
Proof. exact (reads_ch_cons (Z_to_bv 64 0)). Qed.
Section Traces.
Context {A : Type}.
Variable cnt : word.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.
Definition out_tail (s : InputStream) (a : A) (fs : Fs.Fs) : list event :=
match s with
| IEof => map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]
| ICons _ _ => []
end.
Definition drain_from_ch (rch : word) (a : A) (fs : Fs.Fs) (s : InputStream)
(tr : list event) : Prop :=
(exists blocks s' a',
chunks cnt s blocks s' /\
procs f a (concat blocks) = Some a' /\
is_prefix tr (reads_ch rch blocks ++ out_tail s' a' fs))
\/ (exists blocks bs s' a',
chunks cnt s (blocks ++ [bs]) s' /\
procs f a (concat blocks) = Some a' /\
procs f a' bs = None /\
is_prefix tr (reads_ch rch (blocks ++ [bs]) ++ [ExitEv ec fs])).
Definition drain_from (a : A) (fs : Fs.Fs) (s : InputStream)
(tr : list event) : Prop :=
drain_from_ch (Z_to_bv 64 0) a fs s tr.
Lemma drain_from_ch_prefix : forall rch a fs s tr tr',
drain_from_ch rch a fs s tr -> is_prefix tr' tr -> drain_from_ch rch a fs s tr'.
Proof.
intros rch a fs s tr tr' [ (blocks & s' & a' & HC & Hp & Hpref)
| (blocks & bs & s' & a' & HC & Hp & Hn & Hpref) ] Hp'.
- left. exists blocks, s', a'.
split; [exact HC | split; [exact Hp | eapply is_prefix_trans; eauto]].
- right. exists blocks, bs, s', a'.
split; [exact HC | split; [exact Hp |
split; [exact Hn | eapply is_prefix_trans; eauto]]].
Qed.
Lemma drain_from_prefix : forall a fs s tr tr',
drain_from a fs s tr -> is_prefix tr' tr -> drain_from a fs s tr'.
Proof. exact (drain_from_ch_prefix (Z_to_bv 64 0)). Qed.
Lemma drain_from_ch_nil : forall rch a fs s, drain_from_ch rch a fs s [].
Proof.
intros rch a fs s. left. exists [], s, a.
split; [constructor | split; [reflexivity | apply is_prefix_nil]].
Qed.
Lemma drain_from_nil : forall a fs s, drain_from a fs s [].
Proof. exact (drain_from_ch_nil (Z_to_bv 64 0)). Qed.
Lemma drain_from_ch_out : forall rch a fs tr,
is_prefix tr (map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]) ->
drain_from_ch rch a fs IEof tr.
Proof.
intros rch a fs tr Hp. left. exists [], IEof, a.
split; [constructor | split; [reflexivity | exact Hp]].
Qed.
Lemma drain_from_out : forall a fs tr,
is_prefix tr (map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]) ->
drain_from a fs IEof tr.
Proof. exact (drain_from_ch_out (Z_to_bv 64 0)). Qed.
Lemma drain_from_ch_block : forall rch a a1 fs s bs tr,
(1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take s (length bs)) = bs ->
procs f a bs = Some a1 ->
drain_from_ch rch a1 fs (snd (stream_take s (length bs))) tr ->
drain_from_ch rch a fs s (map (ReadEv rch) bs ++ tr).
Proof.
intros rch a a1 fs s bs tr Hlo Hhi Hpre Hs
[ (blocks & s' & a' & HC & Hp & Hpref)
| (blocks & bsE & s' & a' & HC & Hp & Hn & Hpref) ].
- left. exists (bs :: blocks), s', a'.
split; [eapply chunks_cons; eassumption |].
split; [cbn [concat]; rewrite procs_app, Hs; exact Hp |].
rewrite reads_ch_cons, <- app_assoc.
apply is_prefix_app_mono. exact Hpref.
- right. exists (bs :: blocks), bsE, s', a'.
split; [change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE]));
eapply chunks_cons; eassumption |].
split; [cbn [concat]; rewrite procs_app, Hs; exact Hp |].
split; [exact Hn |].
change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE])).
rewrite reads_ch_cons, <- app_assoc.
apply is_prefix_app_mono. exact Hpref.
Qed.
Lemma drain_from_block : forall a a1 fs s bs tr,
(1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take s (length bs)) = bs ->
procs f a bs = Some a1 ->
drain_from a1 fs (snd (stream_take s (length bs))) tr ->
drain_from a fs s (map (ReadEv (Z_to_bv 64 0)) bs ++ tr).
Proof. exact (drain_from_ch_block (Z_to_bv 64 0)). Qed.
Lemma drain_from_ch_err : forall rch a fs s bs tr,
(1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take s (length bs)) = bs ->
procs f a bs = None ->
is_prefix tr [ExitEv ec fs] ->
drain_from_ch rch a fs s (map (ReadEv rch) bs ++ tr).
Proof.
intros rch a fs s bs tr Hlo Hhi Hpre Hn Hp. right.
exists [], bs, (snd (stream_take s (length bs))), a.
split; [cbn [app]; eapply chunks_cons;
try eassumption; constructor |].
split; [reflexivity |].
split; [exact Hn |].
cbn [app]. unfold reads_ch. cbn [flat_map]. rewrite app_nil_r.
apply is_prefix_app_mono. exact Hp.
Qed.
Lemma drain_from_err : forall a fs s bs tr,
(1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take s (length bs)) = bs ->
procs f a bs = None ->
is_prefix tr [ExitEv ec fs] ->
drain_from a fs s (map (ReadEv (Z_to_bv 64 0)) bs ++ tr).
Proof. exact (drain_from_ch_err (Z_to_bv 64 0)). Qed.
End Traces.
Lemma fd1chan_with_stdin : ltac2:(TCodec.tc2 tcn__DrainSim "='QB'QD&R6r1%211&R3r3r2%3221%711p061pUD:1pV2<1").
Proof. intros s m H. exact H. Qed.
Lemma m_fds_with_stdin : ltac2:(TCodec.tc2 tcn__DrainSim "E'QB'QD'A'8'='S4yR0%211'Q@%5221%711&QK&R3r2r1%3221%511%613%@3821pUDB1pV2D1").
Proof. reflexivity. Qed.
Section Drain.
Context {A : Type}.
Variable segs : list Segment.
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.
Hypothesis Hec : (bv_unsigned ec < 256)%Z.
Variable LH : A -> machine_state -> Prop.
Definition lh_next (a : A) (ms : machine_state) : Prop :=
exists ms', msteps segs ms ms' /\ LH a ms'.
Definition WrFin (bs : list byte) (ms : machine_state) : Prop :=
(1 <= length bs)%nat /\
to_wall segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).
Inductive to_out : list byte -> machine_state -> Prop :=
| tout_exit : forall ms, to_exit segs (Z_to_bv 64 0) ms -> to_out [] ms
| tout_wr : forall bs ms, WrFin bs ms -> to_out bs ms
| tout_step : forall bs ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_out bs ms' -> to_out bs ms.
Definition ReadPend (a : A) (ms : machine_state) : Prop :=
exists buf x8,
ms_svc_pending ms = Some x8 /\
bv_unsigned x8 = 63%Z /\
ms_gpr ms 0 = Z_to_bv 64 0 /\
ms_gpr ms 1 = buf /\
ms_gpr ms 2 = cnt /\
(exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt
= Some w) /\
access_okb buf (bv_unsigned cnt) = true /\
to_out (out a) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
buf_modeled (out a) /\
(forall bs,
(1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
match procs f a bs with
| Some a' => lh_next a'
(advance_past_svc (apply_effect ms
(mkEffect (len_word bs) [(buf, bs)] [])))
| None => to_exit segs ec
(advance_past_svc (apply_effect ms
(mkEffect (len_word bs) [(buf, bs)] [])))
end).
Inductive to_rd : A -> machine_state -> Prop :=
| trd_here : forall a ms, ReadPend a ms -> to_rd a ms
| trd_step : forall a ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_rd a ms' -> to_rd a ms.
Lemma msteps_to_rd : forall a ms ms',
msteps segs ms ms' -> to_rd a ms' -> to_rd a ms.
Proof.
intros a ms ms' H; induction H; [auto|].
intro Hrd. eapply trd_step; eauto.
Qed.
Lemma msteps_to_out : ltac2:(TCodec.tc2 tcn__DrainSim "E'8'S4y8%211%411'M'R7vS1r2r1%43321'R9r4%2215r5%4213p031p071pUL=1pUJ>1pU6@1").
Proof.
intros bs ms ms' H; induction H; [auto|].
intro Ho. eapply tout_step; eauto.
Qed.
Lemma to_out_wall_tail : ltac2:(TCodec.tc2 tcn__DrainSim "I'8'S4y8%211%411'M'R9r2r1%3221'R>vS1&S3yR0+1%3221r3'R<z%7261%3291%;5:6>51p0=1pUJB1pU6D1").
Proof.
intros bs ms H;
induction H as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH].
- apply twt_done. exact Hte.
- destruct HWF as [Hnb Hwl]. apply twt_more; assumption.
- eapply twt_step; eauto.
Qed.
Variable H_LH : forall a ms, LH a ms -> to_rd a ms.
Lemma lh_next_to_rd : forall a ms, lh_next a ms -> to_rd a ms.
Proof.
intros a ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.
Lemma to_rd_star : forall a ms model,
m_halted model = None -> m_vm_lazy model = [] -> to_rd a ms ->
exists msR, ReadPend a msR /\
star segs (mkCfg ms model) [] (mkCfg msR model).
Proof.
intros a ms model Hh Hlazy Hrd.
induction Hrd as [a ms HRP | a ms ms' Hsvc Hstep Hrd IH].
- exists ms. split; [exact HRP | apply star_refl].
- destruct IH as (msR & HRP & Hstar).
exists msR. split; [exact HRP|].
change ([] : list event) with (([] : list event) ++ []).
eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
try assumption.
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma msteps_star : ltac2:(TCodec.tc2 tcn__DrainSim "Q;'M'QD'A';'S4yR0%211%411&QMr1%211(0%116%;3631'8'=%12::%311&QOr2%211(:%116%E3631'R7vS1r5r4%43321'Q:(Q8r6%2215'QI%=11%5298%74;421p091p0?1p0J1pUFQ71pULQ91pUJQ:1").
Proof.
intros ms ms' model Hh Hlazy H. induction H as [ms | ms ms1 ms2 Hsvc Hstep H IH].
- apply star_refl.
- change ([] : list event) with (([] : list event) ++ []).
eapply star_step; [apply (sstep_instr segs ms model ms1 model) | exact IH];
try assumption.
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma to_out_star_admits : ltac2:(TCodec.tc2 tcn__DrainSim "R;'8'S4y8%211%411'M'QD&R6r1%211'A';yR0%<11%311&QMr2%211(0%116%:3631'=%1299%G11&QOr3%211(:%116%C3631'R9r6r5%3221&R5r7%211'B'Q6'Q:vS1(Q8r8%2218&3'QI&E(QG&S3+1%22Q61%411r9%74QB821(5(Q>z%92Q=1&QL%11H%5231%Q21@%83A21%C3B:1%I4HE1QHqU:K1%M2L1p0O1p0Q31p0Q81p0QB1p0QN1pUFR21pUJR41pU6R61").
Proof.
intros bs ms model Hfd1 Hh Hlazy Ho Hbm. revert Hbm.
induction Ho as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH]; intro Hbm.
- cbn [map app].
destruct (to_exit_star_admits segs (Z_to_bv 64 0) ms model Hh Hlazy Hte) as [c Hstar].
exists c. rewrite band0_255 in Hstar. exact Hstar.
- destruct HWF as (Hnb & Hwl).
eapply (to_wall_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
ms bs _ Hwl Hbm model);
[exact Hh | exact Hlazy | apply fd1chan_fdchan; exact Hfd1 |].
intros ms' Hex.
destruct (to_exit_star_admits segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex)
as [c Hstar].
exists c. rewrite band0_255 in Hstar. exact Hstar.
- destruct (IH Hbm) as [c Hstar]. exists c.
replace (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])
with ([] ++ (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]))
by reflexivity.
eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
try assumption.
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma to_out_star_only : ltac2:(TCodec.tc2 tcn__DrainSim "R?'8'S4y8%211%411'M'QD&R6r1%211'A';yR0%<11%311&QMr2%211(0%116%:3631'=%1299%G11&QOr3%211(:%116%C3631'R9r6r5%3221&R5r7%211'QI%Q611'Q6'Q:vS1(Q8r9r8%3221%6451NQ6&Q7&3&E(QG&S3+1%22Q91%411r;%74QEC21(5(Q>z%92Q@1&QL%11C%5231%Q51K%83L21%B3M:1%D3NQ:1p0F1pU:N1pV>Q01p0Q31p0Q71p0Q<1p0QF1p0R21pUFR61pUJR81pU6R:1").
Proof.
intros bs ms model Hfd1 Hh Hlazy Ho Hbm. revert Hbm.
induction Ho as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH];
intros Hbm tr c Hstar.
- cbn [map app].
destruct (to_exit_star_only segs (Z_to_bv 64 0) ms model Hh Hlazy Hte tr c Hstar)
as [-> | ->].
+ apply is_prefix_nil.
+ rewrite band0_255. apply is_prefix_refl.
- destruct HWF as (Hnb & Hwl).
eapply (to_wall_star_only segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
ms bs _ Hwl Hbm model);
[exact Hh | exact Hlazy | apply fd1chan_fdchan; exact Hfd1 | | exact Hstar].
intros ms' tr' c' Hex Hstar'.
destruct (to_exit_star_only segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex tr' c' Hstar')
as [-> | ->].
+ apply is_prefix_nil.
+ rewrite band0_255. apply is_prefix_refl.
- inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst; [apply is_prefix_nil|].
destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
subst evs. inversion Hc2; subst c2. cbn [app].
exact (IH Hbm tr2 _ Hstar2).
Qed.
Lemma read0_check_eof_cnt : ltac2:(TCodec.tc2 tcn__DrainSim "S;'M'S4yR0%211'QD'8y8%611%311'A'F&S5r3%22;1+QO%63521';'Q@%211&QJ&QK%119&S3z%22F1%6241(2(Q?%114%32<1%E3<51'QB&QNr4%211(QA%K3521&Nr7(1%3221%Q03Q61Ar8u2%7221vRF%Q53Q;21%O1Q7&R1&Q0vS1r9%3221u1%A231%7331:r6%O2QA1%QA3;31'4&QHr:%I219%QD2QMB%4221(?%QI3721'J&H&Q<r;%23E1:&R4%Q423Q2%211%Q625F%Q726Q1(R0(:'=%12R=R8%311%32R?R?%511'QC%711'9%82RD1%:11%<6R186641%F6C@?>1Q7(I'QI%?11%32Q;1%RF3L51p0N1p0Q71p0QD1p0QJ1p0R01p0R71p0RG1pV@RO1pUFS41pVBS61pUJS:1").
Proof. apply (StreamSim.read0_check_eof cnt Hcnt). Qed.
Lemma read0_ok_eof_cnt : ltac2:(TCodec.tc2 tcn__DrainSim "S5'M'S4yR0%211'QD'8y8%611%311'A'F&S5r3%22;1+QO%63521';'Q@%211&QJ&QK%119&S3z%22F1%6241(2(Q?%114%32<1%E3<51'QB&QNr4%211(QA%K3521&Nr7(1%3221%Q03Q61Ar8u2%7221vRF%Q53Q;21%O1Q7&R1&Q0vS1r9%3221u1%A231%7331:r6%O2QA1%QA3;31'4&QHr:%I219%QD2QMB%4221(?%QI3721&Q=&Q<r;%23D19(K'QF(R0(:'=%12R9R4%311%32R;R;%511'QC%711'9%82R@1%:11%<6QM86641'QI%=11%A4@3Q51%F3CQ61p0H1p0Q11p0Q>1p0QD1p0QJ1p0R11p0RA1pV@RI1pUFRN1pVBS01pUJS41").
Proof. apply (StreamSim.read0_ok_eof cnt Hcnt). Qed.
Lemma read0_check_bytes_cnt : ltac2:(TCodec.tc2 tcn__DrainSim "T>'M'S4yR0%211'QD'8y8%611%311'A'F&S5r4%22;1+QO%63521';'Q@%211&QJ&QK%119&S3z%22F1%6241(2(Q?%114%32<1%E3<51&Nr7(1%3221%J3Q01;r8u2%7221vRF%O3Q521%I1Q1&R1&Q0vS1r9%3221u1%A231%7331:r6%I2Q;1%Q;3;31'4&QHr:%I219%Q>2QGB%4221(?%QC3721&R?+1&R@&7%12QJQ1%311%6251%42QMQ0%611%921=&6'QB&R2&QNr;%211%=2R6Q0%5221%83R771%R73R81Q3'J&H&Q<r>r=%33Q:21&R4%QI24QG%211%QK26Q;%QL27QF(R0&G%12RGQ7(5'=%12RNRI(<%14S0RK9Q<(:%114%73531%72S4S4%411'QC%611'9%<2S91%911%B6@86641r<%N6JGFE21(I&R3&>%Q:15%QE2S>QN%Q=221%43S?Q?1%6219&E'QI(QE%11S4%44SF31R6%=261%SF3Q>?1p0Q@1p0QK1p0QO1p0R71p0R@1p0RM1p0S31p0S91p0SI1pU6T11pV@T21pUFT71pVBT91pUJT=1").
Proof. apply (StreamSim.read0_check_bytes cnt Hcnt). Qed.
Lemma read0_ok_bytes_cnt : ltac2:(TCodec.tc2 tcn__DrainSim "T9'M'S4yR0%211'QD'8y8%611%311'A'F&S5r4%22;1+QO%63521';'Q@%211&QJ&QK%119&S3z%22F1%6241(2(Q?%114%32<1%E3<51&Nr7(1%3221%J3Q01;r8u2%7221vRF%O3Q521%I1Q1&R1&Q0vS1r9%3221u1%A231%7331:r6%I2Q;1%Q;3;31'4&QHr:%I219%Q>2QGB%4221(?%QC3721&R?+1&R@&7%12QJQ1%311%6251%42QMQ0%611%921=&6'QB&R2&QNr;%211%=2R6Q0%5221%83R771%R73R81Q3&Q=&Q<r>r=%33Q921r<(K'QF(R0&G%12RDQ4(5'=%12RKRF(<%R12=QA%24RNRI1Q:(:%115%83631%82S2S2%411'QC%611'9%=2S71%911%C6A86641&R3&>%Q51I%Q@2S9QI%Q8221%43S:Q:1%621M&E'QI(QE%11RO%44SA31R1%Q24Q1=61%Q93Q5Q41p0Q;1p0QF1p0QJ1p0R21p0R;1p0RH1p0RN1p0S41p0SD1pU6SL1pV@SM1pUFT21pVBT41pUJT81").
Proof. apply (StreamSim.read0_ok_bytes cnt Hcnt). Qed.
Lemma read0_ok_inv_cnt : ltac2:(TCodec.tc2 tcn__DrainSim "TN'M'S4yR0%211'QD'8y8%611%311'QF'QI%611'A'F&S5r7%22>1+QO%63521';'Q@%211&QJ&QK%119&S3z%22I1%6241(2(Q?%114%32<1%E3<51&Nr:(1%3221%J3Q31;r;u1%7221r8%O3Q821r<u2%<221vRF%Q43Q=21%N1Q9&R1&Q0vS1r=%3221%531D8r9%L2QA1%Q>3931'4&QH%Q?2QK>%22G1(?%QD3521&Q=&Q<r?r>%33A21(K%14QNQ4?M%733C1'D'@'QB&QN%119(QA%R33421(R0(:'=%12R@R;%311%32RBRB%511'QC%711'9%82RG1%:11%<6R186641%RA3RDQF1%RB3RJQKJ%>1RE%RD3REQ81%G231%H251%I2D1'B&R?+1&R@&7r1%22S31%411%7261%822Q@&6&R2%Q41Q=%2217%43S:Q71%S73S;1:&G%12S><(5(<%14SES@QD?%33Q61Q5%Q:651Q4Q4Q2O%S?3SBR?1&R3&>%13SFQC=%321QL%SD3SLRI1&E(QE%11S8%34SMSJ1K%SI3SJS21%QL261%QM2<1%QN2E1%QO2L1%R02N1qU6T31%Q82T41%R42Q:1p0R61p0R?1p0RF1p0S11p0S71p0S=1p0SC1p0T31pUBT;1pUHTC1pU@T?1pV@TA1pU8TG1pUFTG1pVBTI1pUJTM1").
Proof. apply (StreamSim.read0_ok_inv cnt Hcnt). Qed.
Lemma read0_no_err_cnt : ltac2:(TCodec.tc2 tcn__DrainSim "RA'M'S4yR0%211'QD'8y8%611%311'A'F&S5r3%22;1+QO%63521';'Q@%211&QJ&QK%119&S3z%22F1%6241(2(Q?%114%32<1%E3<51&Nr6(1%3221%J3Q01;r7u2%7221vRF%O3Q521%I1Q1&R1&Q0vS1r8%3221u1%A231%7331:r5%I2Q;1%Q;3;31'4&QHr9%I219%Q>2QGB%4221(?%QC3721&C&Q=&Q<r:%23E1:(L'QF%211%734H1%911p0;1p0D1p0Q11p0Q71p0Q=1p0QM1pV@R51pUFR:1pVBR<1pUJR@1").
Proof. apply (StreamSim.read0_no_unmodeled cnt Hcnt). Qed.
Lemma sstep_read_inv_cnt : ltac2:(TCodec.tc2 tcn__DrainSim "UG'M'QD'S4yR0%211'8y8%511%311'QI%511'Q;'A';%11:&QMr6%211(0%11?%83631'=%12BB%B11&QOr7%211(:%116%A3631'Q@%B11&QJ&QKr8%211&S3z%22Q31%7241(2(Q?%114%32=1%Q03=51&Or:%211%82Q<G%Q53Q321'F&S5%12QAB+QO%Q:3421&Nr<(1%3221%Q?3QG1Er=u1%7221r;%QD3QL21r>u2%<221vRF%QI3R121%QI1QN&R1&Q0vS1r?%3221%531@8%Q52R5>%R23821'4&QH%N2R>=%22A1(?%R83521'Q9(Q8rAr@%3221%54A1Q2K'D'@'QB&QN%118(QA%RE3421%R71RI%RG3RIQ71(Q3&Q4&Q1rB%221R2%411%D21C%711%S03S1QD1%A2:1%B2=1'B&R?+1&R@&7r1%22S>1%411%7261%822Q7&6&R2%M1D%2217%43SEQ01%SB3SF1:&E(QE%11RK%34SKSI1>%SG3SIR21&Q5rC(R0&G%12T1D(5%SE2T6T2(<%14T8T4QEH%SB13%53421'QC%SE11'9%SM2T>1%SH11%>6<6SHSH41%A2@1%QA11&R3&>%13TAQLM%321QC%R5251%QH11%TA3TBS11%R22K1%R32Q11%R42Q81%R52Q:1qU6TJ1%QD2TK1%R92QF1p0R;1p0RB1p0RI1p0S31p0S91p0S?1p0SE1p0SK1p0T11p0TA1p0TK1pV6U51pUBU71pV@U:1pVBU?1pU8U@1pUFUD1pUJUF1").
Proof. apply (StreamSim.sstep_read_inv cnt Hcnt). Qed.
Lemma drain_read_step : ltac2:(TCodec.tc2 tcn__DrainSim "T>'8'S4y8%211%411'M'QDyR0%711&R=r4%211'A';%116&Or6%211(2r3%22<1%93741'F&S5%12A>+QO%>3421&Nr8(1%3221&S3z%22J1%F3J41r9u1%:221r7%K3O21r:u2%?221vRF%Q03Q421%Q01Q9&R1&Q0vS1r;%3221%531@8%Q22Q@>%Q93821'4&QH%Q12QA=%22A1(?%Q?3521&R?+1&R@&7r>%22QN1%411%7261r?%62R21%811%;21?&6'QB&R2&QN%11<r@%?2R;1%5231%83R<71%R53R=14'Q9(Q8%127@&E'QI(QE%11QGrA%54RG421(Q3&Q4&Q5(R0&G%12RM7(5'=%12RKRO(<%14RMS1Q5<(:%114%73531%72S1S1%411'QC%611'9%<2S61%911%B6@86641%D2Q41%F11&R3&>%Q:1QA%QG2SCM%Q=221%43SDQ?1%621QE%Q7281%Q011%Q:4R<Q8Q21p0Q<1p0QG1p0QL1p0R51p0R<1p0RF1p0RL1p0S21p0S;1p0SA1p0SL1pV@T41pVBT11pU8T21pUFT51pUJT71pU6T91").
Proof.
intros bs ms model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hlo Hhi Hpre.
pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
apply (sstep_syscall segs ms model x8
(mkEffect (len_word bs) [(buf, bs)] [])
(with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
(with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
(map (ReadEv (Z_to_bv 64 0)) bs));
[exact Hh | exact Hsvc | | exact Hh |].
- rewrite <- Hg1. rewrite <- Hg1 in Hw, Haok.
apply read0_ok_bytes_cnt with (w := w); assumption.
- rewrite (materialize_model_accesses_no_lazy _ _).
+ reflexivity.
+ rewrite m_vm_lazy_with_stdin. exact Hlazy.
Qed.
Lemma drain_star_admits_ok : forall s blocks s',
chunks cnt s blocks s' ->
forall a a' ms model,
M_loop model -> m_stdin model = s -> to_rd a ms ->
procs f a (concat blocks) = Some a' ->
exists c, star segs (mkCfg ms model)
(reads blocks ++ out_tail out s' a' (m_fs model)) c.
Proof.
intros s blocks s' HC.
induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
intros a a' ms model HM Hst Hrd Hp;
pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
- cbn [concat procs] in Hp. injection Hp as <-.
unfold reads, reads_ch. cbn [flat_map app].
destruct s as [|b0 s0] eqn:Hs.
+
destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & _).
assert (HssE : sstep segs (mkCfg msR model) []
(SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0)))
model))).
{ rewrite <- (apply_effect_no_write msR (Z_to_bv 64 0)).
apply (sstep_syscall segs msR model x8 (mkEffect (Z_to_bv 64 0) [] [])
model model []);
[exact Hh | exact Hsvc | | exact Hh |].
- rewrite <- Hg1 in Hw, Haok.
exact (read0_ok_eof_cnt msR x8 model w Hno Hfd0 Hst Hg0 Hg2 Hw
Haok).
- rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity. }
destruct (to_out_star_admits (out a) _ model Hfd1 Hh Hlazy Hout Hobm) as [c Hstar2].
exists c. cbn [out_tail].
replace (map (WriteEv (Z_to_bv 64 1)) (out a)
++ [ExitEv (Z_to_bv 64 0) (m_fs model)])
with (([] : list event)
++ ([] ++ (map (WriteEv (Z_to_bv 64 1)) (out a)
++ [ExitEv (Z_to_bv 64 0) (m_fs model)])))
by reflexivity.
eapply star_trans; [exact Hstar0|].
eapply star_step; [exact HssE | exact Hstar2].
+
cbn [out_tail app]. exists (mkCfg ms model). apply star_refl.
-
cbn [concat] in Hp. rewrite procs_app in Hp.
destruct (procs f a bs) as [a1|] eqn:Hp1; [|discriminate].
destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
pose proof (Hbytes bs Hlo Hhi) as Hcont.
rewrite Hp1 in Hcont.
set (advB := advance_past_svc (apply_effect msR
(mkEffect (len_word bs) [(buf, bs)] []))) in *.
set (model' := with_stdin (snd (stream_take s (length bs))) model).
assert (HM' : M_loop model')
by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
by reflexivity.
assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
(SNext (mkCfg advB model'))).
{ unfold advB, model'. rewrite <- Hst.
eapply (drain_read_step bs msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
Hlo Hhi); rewrite Hst; exact Hpre. }
destruct Hcont as (msL & Hms & HLa1).
pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
destruct (IH a1 a' advB model' HM' Hst' Hrd1 Hp) as [c Hstar3].
exists c.
change (m_fs model') with (m_fs model) in Hstar3.
rewrite reads_cons, <- app_assoc.
replace (map (ReadEv (Z_to_bv 64 0)) bs
++ reads blocks ++ out_tail out s'' a' (m_fs model))
with (([] : list event)
++ (map (ReadEv (Z_to_bv 64 0)) bs
++ (reads blocks ++ out_tail out s'' a' (m_fs model))))
by reflexivity.
eapply star_trans; [exact Hstar0|].
eapply star_step; [exact HssR | exact Hstar3].
Qed.
Lemma drain_star_admits_err : forall s blocks s1,
chunks cnt s blocks s1 ->
forall a a' bsE ms model,
M_loop model -> m_stdin model = s -> to_rd a ms ->
procs f a (concat blocks) = Some a' ->
(1 <= Z.of_nat (length bsE))%Z -> (Z.of_nat (length bsE) <= bv_unsigned cnt)%Z ->
fst (stream_take s1 (length bsE)) = bsE ->
procs f a' bsE = None ->
exists c, star segs (mkCfg ms model)
(reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)]) c.
Proof.
intros s blocks s1 HC.
induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
intros a a' bsE ms model HM Hst Hrd Hp HloE HhiE HpreE Hn;
pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
- cbn [concat procs] in Hp. injection Hp as <-.
destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
pose proof (Hbytes bsE HloE HhiE) as Hcont.
rewrite Hn in Hcont.
set (advB := advance_past_svc (apply_effect msR
(mkEffect (len_word bsE) [(buf, bsE)] []))) in *.
set (model' := with_stdin (snd (stream_take s (length bsE))) model).
assert (Hh' : m_halted model' = None) by exact Hh.
assert (Hlazy' : m_vm_lazy model' = [])
by (unfold model'; rewrite m_vm_lazy_with_stdin; exact Hlazy).
assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bsE)
(SNext (mkCfg advB model'))).
{ unfold advB, model'. rewrite <- Hst.
eapply (drain_read_step bsE msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
HloE HhiE); rewrite Hst; exact HpreE. }
destruct (to_exit_star_admits segs ec advB model' Hh' Hlazy' Hcont) as [c Hstar2].
rewrite land_255_small in Hstar2 by exact Hec.
change (m_fs model') with (m_fs model) in Hstar2.
exists c.
cbn [app]. unfold reads, reads_ch. cbn [flat_map]. rewrite app_nil_r.
replace (map (ReadEv (Z_to_bv 64 0)) bsE ++ [ExitEv ec (m_fs model)])
with (([] : list event)
++ (map (ReadEv (Z_to_bv 64 0)) bsE ++ [ExitEv ec (m_fs model)]))
by reflexivity.
eapply star_trans; [exact Hstar0|].
eapply star_step; [exact HssR | exact Hstar2].
- cbn [concat] in Hp. rewrite procs_app in Hp.
destruct (procs f a bs) as [a1|] eqn:Hp1; [|discriminate].
destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
pose proof (Hbytes bs Hlo Hhi) as Hcont.
rewrite Hp1 in Hcont.
set (advB := advance_past_svc (apply_effect msR
(mkEffect (len_word bs) [(buf, bs)] []))) in *.
set (model' := with_stdin (snd (stream_take s (length bs))) model).
assert (HM' : M_loop model')
by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
by reflexivity.
assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
(SNext (mkCfg advB model'))).
{ unfold advB, model'. rewrite <- Hst.
eapply (drain_read_step bs msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
Hlo Hhi); rewrite Hst; exact Hpre. }
destruct Hcont as (msL & Hms & HLa1).
pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
destruct (IH a1 a' bsE advB model' HM' Hst' Hrd1 Hp HloE HhiE HpreE Hn)
as [c Hstar3].
exists c.
change (m_fs model') with (m_fs model) in Hstar3.
change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE])).
rewrite reads_cons, <- app_assoc.
replace (map (ReadEv (Z_to_bv 64 0)) bs
++ reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)])
with (([] : list event)
++ (map (ReadEv (Z_to_bv 64 0)) bs
++ (reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)])))
by reflexivity.
eapply star_trans; [exact Hstar0|].
eapply star_step; [exact HssR | exact Hstar3].
Qed.
Lemma star_drain_only : forall c0 tr c', star segs c0 tr c' ->
forall a ms model, c0 = mkCfg ms model -> M_loop model -> to_rd a ms ->
drain_from cnt f out ec a (m_fs model) (m_stdin model) tr.
Proof.
intros c0 tr c' Hstar.
induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
intros a ms model Heq HM Hrd; subst.
- apply drain_from_nil.
- pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms' Hsvc Hstep Hrd'].
+
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
destruct (sstep_read_inv_cnt ms model buf x8 w evs (SNext c2)
Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
inversion Hc2; subst.
*
pose proof (to_out_star_only (out a) _ model Hfd1 Hh Hlazy Hout Hobm
tr2 c3 Hstar) as Hpref.
cbn [app]. rewrite Hs. apply drain_from_out. exact Hpref.
*
pose proof (Hbytes bs Hlo Hhi) as Hcont.
destruct (procs f a bs) as [a1|] eqn:Hp1.
-- destruct Hcont as (msL & Hms & HLa1).
pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
apply drain_from_block with (a1 := a1);
[exact Hlo | exact Hhi | exact Hpre | exact Hp1 |].
exact (IH a1 _ _ eq_refl (M_loop_take (length bs) model HM) Hrd1).
-- apply drain_from_err;
[exact Hlo | exact Hhi | exact Hpre | exact Hp1 |].
destruct (to_exit_star_only segs ec _
(with_stdin (snd (stream_take (m_stdin model) (length bs)))
model) Hh ltac:(rewrite m_vm_lazy_with_stdin; exact Hlazy)
Hcont tr2 c3 Hstar)
as [-> | ->].
++ apply is_prefix_nil.
++ change (m_fs (with_stdin
(snd (stream_take (m_stdin model) (length bs)))
model)) with (m_fs model).
rewrite land_255_small by exact Hec. apply is_prefix_refl.
+
destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
subst evs. inversion Hc2; subst c2. cbn [app].
exact (IH a _ model eq_refl HM Hrd').
Qed.
Definition dinv (c : config) : Prop :=
(M_loop (cfg_model c) /\ exists a, to_rd a (cfg_ms c))
\/ (fd1chan (cfg_model c) /\ m_halted (cfg_model c) = None /\
m_vm_lazy (cfg_model c) = [] /\
exists rest, buf_modeled rest /\
to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) rest
(to_exit segs (Z_to_bv 64 0)))
\/ on_path segs (Z_to_bv 64 0) c
\/ on_path segs ec c.
Lemma wall_out_dinv_step : ltac2:(TCodec.tc2 tcn__DrainSim "R6'8'S4y8%211%411'M'QD'QI%811&R6r4%211'A';yR0%>11%311&QMr5%211(0%116%:3631'=%1299%I11&QOr6%211(:%116%C3631&R5r9%211'R>vS1&S3+1%22I1r:'R<z%62M1%3281%:596<51'Q9(Q8%128?r8(Q3r7%521I%311%84B651&R8%9275%211p041p0>1p0J1p0N1p0Q81p0QD1pUHQJ1pULQL1pUBQJ1pUFQM1pUJQO1pV0R11").
Proof.
intros rest ms model evs ms' model' Hfd1 Hh Hlazy Hbm Ht Hss.
assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
by (apply fd1chan_fdchan; exact Hfd1).
revert Hbm.
inversion Ht as [msD kD HkD | msM restM kM HnbM Hwl
| msS msS' restS kS HsvcS HstepS Ht']; subst; intro Hbm.
-
right. right. left.
apply (on_path_step segs (Z_to_bv 64 0) (mkCfg ms model) evs); [|exact Hss].
left. repeat split; assumption.
-
destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
ms rest _ model evs (SNext (mkCfg ms' model'))
Hh Hlazy Hfdc Hbm Hwl Hss) as (n & Hn1 & Hn2 & _ & Hc2 & Ht2).
inversion Hc2; subst.
right. left. cbn. repeat split; try assumption.
exists (skipn n rest).
split; [apply buf_modeled_skipn; exact Hbm | exact Ht2].
-
destruct (sstep_instr_inv segs ms model msS' evs (SNext (mkCfg ms' model'))
Hlazy HsvcS HstepS Hss) as [_ Hc2].
inversion Hc2; subst.
right. left. cbn. repeat split; try assumption.
exists rest. split; [exact Hbm | exact Ht'].
Qed.
Lemma dinv_step : ltac2:(TCodec.tc2 tcn__DrainSim "C'Q6'8'QI%211&R8r3%211'Q9vS1r4(Q3r2%211%645481p018p091pU<@1pUB>1pU:B1").
Proof.
intros [ms model] evs [ms' model'] Hinv Hss.
destruct Hinv as
[[HM (a & Hrd)] | [[Hfd1 [Hh [Hlazy (rest & Hbm & Ht)]]] | [Hop | Hop]]];
cbn [cfg_ms cfg_model] in *.
- pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms1 Hsvc Hstep Hrd'].
+ destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
destruct (sstep_read_inv_cnt ms model buf x8 w evs
(SNext (mkCfg ms' model'))
Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
inversion Hc2; subst.
* right. left. cbn. repeat split; try assumption.
exists (out a).
split; [exact Hobm | exact (to_out_wall_tail _ _ Hout)].
* pose proof (Hbytes bs Hlo Hhi) as Hcont.
destruct (procs f a bs) as [a1|] eqn:Hp1.
-- destruct Hcont as (msL & Hms & HLa1).
left. cbn. split; [apply M_loop_take; exact HM|].
exists a1. exact (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)).
-- right. right. right. left. cbn. split; [exact Hh|].
split; [exact Hlazy | exact Hcont].
+ destruct (sstep_instr_inv segs ms model ms1 evs
(SNext (mkCfg ms' model')) Hlazy Hsvc Hstep Hss) as [_ Hc2].
inversion Hc2; subst.
left. cbn. split; [exact HM |]. exists a. exact Hrd'.
- exact (wall_out_dinv_step rest ms model evs ms' model' Hfd1 Hh Hlazy Hbm Ht Hss).
- right. right. left. eapply on_path_step; eauto.
- right. right. right. eapply on_path_step; eauto.
Qed.
Lemma dinv_no_error : ltac2:(TCodec.tc2 tcn__DrainSim "A'Q6'8'QI%211&R8r2%211&C'Q9vS1r3(Q2%443271%611p081pUB<1pU:@1").
Proof.
intros [ms model] evs Hinv Hss.
destruct Hinv as
[[HM (a & Hrd)] | [[Hfd1 [Hh [Hlazy (rest & Hbm & Ht)]]] | [Hop | Hop]]];
cbn [cfg_ms cfg_model] in *.
- pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms1 Hsvc Hstep Hrd'].
+ destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
destruct (sstep_read_inv_cnt ms model buf x8 w evs SError
Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
as [(_ & _ & Hc2) | (bs & _ & _ & _ & _ & Hc2)]; discriminate.
+ destruct (sstep_instr_inv segs ms model ms1 evs SError
Hlazy Hsvc Hstep Hss) as [_ Hc2]. discriminate.
- assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
by (apply fd1chan_fdchan; exact Hfd1).
inversion Ht as [msD kD HkD | msM restM kM HnbM Hwl
| msS msS' restS kS HsvcS HstepS Ht']; subst.
+ eapply (on_path_no_error segs (Z_to_bv 64 0) (mkCfg ms model));
[left; repeat split; assumption | exact Hss].
+ exact (to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
ms rest _ model evs Hh Hlazy Hfdc Hbm Hwl Hss).
+ destruct (sstep_instr_inv segs ms model msS' evs SError
Hlazy HsvcS HstepS Hss) as [_ Hc2]. discriminate.
- eapply on_path_no_error; eauto.
- eapply on_path_no_error; eauto.
Qed.
Lemma star_dinv : ltac2:(TCodec.tc2 tcn__DrainSim "A'Q6'8'QI%211&R8r3%211'Q:vS1r4r2%443261p016p071pU<>1pV><1pU:@1").
Proof. exact (star_inv segs dinv dinv_step). Qed.
Lemma to_rd_no_error : forall a ms model,
M_loop model -> to_rd a ms -> ~ reaches_error segs (mkCfg ms model).
Proof.
intros a ms model HM Hrd.
apply (inv_no_reaches_error segs dinv dinv_step dinv_no_error).
left; cbn; eauto.
Qed.
Lemma drain_obs_iff : forall pc ph sp brk0 mb rnd lim inp a0,
to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
<-> drain_from cnt f out ec a0 (in_fs inp) (in_stdin inp) tr.
Proof.
intros pc ph sp brk0 mb rnd lim inp a0 Hrd tr.
set (fs0 := in_fs inp) in *; set (stdin0 := in_stdin inp) in *.
unfold init_config.
set (ms0 := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
pose proof (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) as HM0.
set (model0 := init_model (segments_reserved segs) brk0 mb sp lim inp) in *.
assert (Hst0 : m_stdin model0 = stdin0) by reflexivity.
assert (Hfs0 : m_fs model0 = fs0) by reflexivity.
split.
- intros (tr' & c & Hstar & Hp).
pose proof (star_drain_only _ _ _ Hstar a0 ms0 model0 eq_refl HM0 Hrd) as Hd.
rewrite Hst0, Hfs0 in Hd.
eapply drain_from_prefix; eauto.
- intros [ (blocks & s' & a' & HC & Hp & Hpref)
| (blocks & bsE & s' & a' & HC & Hp & Hn & Hpref) ].
+ destruct (drain_star_admits_ok _ blocks s' HC a0 a' ms0 model0
HM0 Hst0 Hrd Hp) as [c Hstar].
rewrite Hfs0 in Hstar.
eexists; exists c; split; [exact Hstar | exact Hpref].
+ destruct (chunks_split _ blocks [bsE] _ _ HC) as (s1 & HC1 & HC2).
destruct (chunks_single_inv _ _ _ _ HC2) as (HloE & HhiE & HpreE & _).
destruct (drain_star_admits_err _ blocks s1 HC1 a0 a' bsE ms0 model0
HM0 Hst0 Hrd Hp HloE HhiE HpreE Hn) as [c Hstar].
rewrite Hfs0 in Hstar.
eexists; exists c; split; [exact Hstar | exact Hpref].
Qed.
Lemma drain_no_error : forall pc ph sp brk0 mb rnd lim inp a0,
to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
intros pc ph sp brk0 mb rnd lim inp a0 Hrd.
apply (to_rd_no_error a0); [apply init_M_loop | exact Hrd].
Qed.
Lemma to_rd_coexec : forall a ms model,
M_loop model -> to_rd a ms -> OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof.
intros a ms model HM Hrd.
apply (inv_coexec segs dinv dinv_step dinv_no_error).
left; cbn. split; [exact HM | exists a; exact Hrd].
Qed.
Lemma drain_omni_corun : forall pc ph sp brk0 mb rnd lim inp a0,
to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors.
Proof.
intros pc ph sp brk0 mb rnd lim inp a0 Hrd. cbn [omni_corun]. unfold init_config.
apply (to_rd_coexec a0); [apply init_M_loop | exact Hrd].
Qed.
Lemma drain_omni_cosafe : forall pc ph sp brk0 mb rnd lim inp a0,
to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
omni_cosafe (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
(drain_from cnt f out ec a0 (in_fs inp) (in_stdin inp)).
Proof.
intros pc ph sp brk0 mb rnd lim inp a0 Hrd. cbn [omni_cosafe].
apply cosafe_obs_iff.
-
intros t t' Ht Hp.
apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd).
eapply obs_trace_prefix_closed; [| exact Hp].
apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Ht.
- intros tr Hobs. apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Hobs.
Qed.
End Drain.
Lemma drain_omni_strong_equiv :
forall (A : Type) (cnt : word) (f : A -> byte -> option A)
(out : A -> list byte) (ec : word) (a0 : A)
source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp,
(bv_unsigned ec < 256)%Z ->
(0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
(forall a ms, rLH a ms -> to_rd source_segs cnt f out ec rLH a ms) ->
(forall a ms, aLH a ms -> to_rd target_segs cnt f out ec aLH a ms) ->
to_rd source_segs cnt f out ec rLH a0
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
to_rd target_segs cnt f out ec aLH a0
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd
inp Hec Hcnt HrLH HaLH Hr Ha.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[exact (drain_omni_corun source_segs cnt Hcnt f out ec rLH HrLH
rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr) | apply never_errors_covered]. }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH
rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr tr).
rewrite (drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH
apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha tr).
reflexivity.
- exact (drain_omni_corun target_segs cnt Hcnt f out ec aLH HaLH
apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha).
Qed.
Lemma drain_strong_equiv :
forall (A : Type) (cnt : word) (f : A -> byte -> option A)
(out : A -> list byte) (ec : word) (a0 : A)
source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim inp,
(bv_unsigned ec < 256)%Z ->
(0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
(forall a ms, rLH a ms -> to_rd source_segs cnt f out ec rLH a ms) ->
(forall a ms, aLH a ms -> to_rd target_segs cnt f out ec aLH a ms) ->
to_rd source_segs cnt f out ec rLH a0
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
to_rd target_segs cnt f out ec aLH a0
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
/\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
(run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
intros A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
inp Hec Hcnt HrLH HaLH Hr Ha.
split.
{ apply no_error_run_modeled.
apply (drain_no_error source_segs cnt Hcnt f out ec rLH HrLH
rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr). }
right. split.
- intro tr. cbn.
rewrite (drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH
rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr tr).
rewrite (drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH
apc aph asp abrk amb arnd alim inp a0 Ha tr).
reflexivity.
- cbn.
apply (drain_no_error target_segs cnt Hcnt f out ec aLH HaLH
apc aph asp abrk amb arnd alim inp a0 Ha).
Qed.

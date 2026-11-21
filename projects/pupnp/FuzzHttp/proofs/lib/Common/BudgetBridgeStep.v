(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO pair; the TASK_SIZE bound of the user-memory reads; mremap's new outcomes; munmap's cut). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run RiscvSemantics MemImageType Vdso.
From LinuxProcessSemantics.LinuxProcessSem Require Import Sys.SyscallTable.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Common Require Import BudgetBridgeCore BudgetBridgeTac BudgetBridgeMm BudgetBridgeDispatch.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib Require TCodec.
Ltac2 tcn__Common_BudgetBridgeStep () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap."; "OSSVerify.Proofs.pupnp.FuzzHttp.lib.Common.BudgetBridgeCore."; "OSSVerify.Proofs.pupnp.FuzzHttp.lib.Common.BudgetBridgeMm."; "OSSVerify.Proofs.pupnp.FuzzHttp.lib.Common.BudgetBridgeStep.Step."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1false"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2iff"; "3Z"; "0L"]; ["4Ok"; "4Unmodeled"; "5MachineOk"; "5access_report"; "5accessed_ranges"; "5machine_result"; "5machine_state"; "5ms_svc_pending"; "5step_accesses"; "6alloc_budget_refused_b"; "6config"; "6mi_account_step"; "6mkCfg"; "6refusal_b"; "6spurious_refusal_cfg"; "6sstep_cfg"]; ["6step_to"; "6sys_input"; "7syscall_spec"; "8Model"; "8SyscallEffect"; "8SyscallInput"; "8VmMaps"; "8event"; "8m_halted"; "8m_vmmaps"; "8materialize_model_accesses"; "8syscall_effect_accesses"; "8vm_limit"; "8vm_maps"; "9brk_budget_refused_b"; "9mmap_budget_refused_b"]; [":mprotect_budget_refused_b"; ";mremap_budget_refused_b"; ";mremap_move_budget_b"; "<Sim1"; "<setlim"; "=maps_bounded"; ">lift_to"; ">liftc"; ">okc"; "?le"; "0a"; "0accs"; "0b"; "0c"; "0cfg"; "0d"]; ["0eff"; "0evs"; "0f"; "0fd"; "0i"; "0l"; "0m"; "0m'"; "0m''"; "0m0"; "0ms"; "0ms'"; "0n"; "0new_n"; "0o"; "0old"]; ["0old_n"; "0p"; "0r"; "0r1"; "0r2"; "0report"; "0req"; "0segs"; "@bv"; "0x"; "0x8"]]).
Lemma materialize_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q9'>'Q3'4'8'RHyR0%211'5%5221%711&QI&Q<&Q9r3%211%411r4%7221';'6%11C&Q:%1269(1r2%22H1%83641&QDr6r5%3221%:21?%524C%:2Q01%@3>31p091p0C1pT@Q41pSHM1pT>Q61pQ0Q81").
Proof.
intros L m accs m' Hle H. unfold materialize_model_accesses, materialize_accesses in *.
change (m_vm_lazy (setlim L m)) with (m_vm_lazy m).
change (m_vm_materialized (setlim L m)) with (m_vm_materialized m).
rewrite vm_backing_used_setlim, m_vmmaps_setlim, vm_limit_setlimh.
destruct (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs) as [|p ps] eqn:E.
- injection H as <-. reflexivity.
- destruct (vm_backing_used m + Z.of_nat (length (p :: ps)) * page_size <=? vm_limit (m_vmmaps m))
eqn:E2; [|discriminate].
injection H as <-. apply Z.leb_le in E2.
replace (vm_backing_used m + Z.of_nat (length (p :: ps)) * page_size <=? L) with true
by (symmetry; apply Z.leb_le; lia).
reflexivity.
Qed.
Lemma materialize_setlim_none : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q4'>'Q3'4'8'RHyR0%211'5%5221%711&QI&Q<&Q9r2%211%411r3%7221';'6%11C&Q:&QDr4%2218%421<(0%11J%:3831%826=%<3:13p031p0?1pSHH1pT>Q11pQ0Q31").
Proof.
intros L m accs Hle H.
destruct (materialize_model_accesses m accs) as [m'|] eqn:E; [|reflexivity].
rewrite (materialize_setlim L m accs m' Hle E) in H. discriminate.
Qed.
Lemma materialize_limit : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "N'Q3'4'8'RHyR0%211'5%5221%711';'6%11;&Q:r3r2%3221(1r1%22B1%:3841'Q6&Q9%118r4%311%@3531p071pT@K1pSHD1pT>M1").
Proof.
intros m accs m' H. exact (proj1 (proj2 (materialize_model_accesses_frame m accs m' H))).
Qed.
Lemma brk_grow_bytes_setlimh : forall L h r, brk_grow_bytes (setlimh L h) r = brk_grow_bytes h r.
Proof. reflexivity. Qed.
Lemma brk_mark_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "N'>'Q3'RHyR0%211&QI&Q<&Q9r2%211%411r3%7221';'2&Q>%1258(3%53421&QDr5r4%3221%821<%;3:17p071p0>1pU>G1pT>K1pQ0M1").
Proof.
intros L m req Hle H. unfold brk_budget_refused_b, brk_budget_ok in *.
(* 08b1429 Sys/Mm/Mmap.v: brk_budget_ok charges [brk_grow_bytes h r] (was
   [bv_unsigned (r - vm_brk h)]); it reads only [vm_brk], so the setlim form is the plain one *)
cbv zeta in *.
rewrite vm_backing_used_setlim, m_vmmaps_setlim.
rewrite ?brk_grow_bytes_setlimh.
cbn [setlimh vm_brk vm_start_brk vm_limit]. unfold min_brk in *. cbn [setlimh vm_start_brk].
destruct (negb (w_is0 req || (bv_unsigned req <? bv_unsigned (vm_start_brk (m_vmmaps m)))) &&
(0 <? bv_unsigned (vm_brk (m_vmmaps m))) &&
(bv_unsigned (vm_brk (m_vmmaps m)) <? bv_unsigned req)) eqn:E;
[|reflexivity].
cbn [andb] in *. apply negb_false_iff in H. apply negb_false_iff.
apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.
Lemma mprotect_mark_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q2'>'Q3'RHyR0%211&QI&Q<&Q9r4%211%411r5%7221';'2&Q@r3r2%34:217(3%73621&QDr7r6%3221%:4>A91%=3<17p071p0@1pU4I1pTJJ1pSFK1pT>O1pQ0Q11").
Proof.
intros L m a n p Hle H. unfold mprotect_budget_refused_b in *. cbv zeta in *.
(* 08b1429 Sys/Mm/Mprotect.v: the mark opens with the vDSO/vvar gate, which reads [m_kernel]
   and [vdso_top] (via [mmap_top]/[alloc_top]), never [vm_limit]: normalise its setlim form so
   the loop below destructs it *)
change (vdso_top (m_vmmaps (setlim L m))) with (vdso_top (m_vmmaps m)).
change (m_kernel (setlim L m)) with (m_kernel m).
rewrite m_vmmaps_setlim. cbn [setlimh vm_noaccess vm_maps].
repeat match goal with
| |- context [if ?b then _ else _] =>
lazymatch b with
| context [setlim] => fail
| _ => destruct b eqn:?
end
end; try reflexivity.
all: cbv beta iota in H.
all: apply negb_false_iff in H; apply negb_false_iff.
all: apply mprotect_budget_ok_mono; assumption.
Qed.
Lemma mmap_mark_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q8'>'Q3'RHyR0%211&QI&Q<&Q9r7%211%411r8%7221';'2&Q?r6r5r4r3r2%67=54321:(3%:3921&QDr:r9%3221%=7AD<;:91%@3?17p071p0C1pTNL1pT8M1pT6N1pU4O1pT<Q01pSFQ11pT>Q51pQ0Q71").
Proof.
intros L m a l p f fd o Hle H. unfold mmap_budget_refused_b in *. cbv zeta in *.
rewrite m_vmmaps_setlim. cbn [setlimh vm_noaccess vm_maps vm_reserved].
change (alloc_top (setlimh L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
repeat match goal with
| |- context [if ?b then _ else _] =>
lazymatch b with
| context [setlim] => fail
| _ => destruct b eqn:?
end
end; try reflexivity.
all: cbv beta iota in H.
all: apply negb_false_iff in H; apply negb_false_iff.
all: first [ apply mmap_noreserve_backed_ok_mono; assumption
| apply mmap_fixed_rw_budget_ok_mono; assumption
| apply mmap_fixed_rw_span_budget_ok_mono; assumption ].
Qed.
Lemma mremap_move_budget_mono : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q2'>'Q3'RHyR0%211&QI&Q<&Q9r4%211%411r5%7221';'2&QBr3r2%347:21(9%73621&QDr7r6%3221%:41>A9%=3<17p071p0@1pTLI1pU2J1pU0K1pT>O1pQ0Q11").
Proof.
intros L m old old_n new_n Hle H. unfold mremap_move_budget_b in *.
change (mremap_move_charge (setlim L m) old old_n new_n) with (mremap_move_charge m old old_n new_n).
rewrite m_vmmaps_setlim, vm_limit_setlimh. apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.
Lemma mremap_mark_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q4'>'Q3'RHyR0%211&QI&Q<&Q9r5%211%411r6%7221';'2&QAr4r3r2%45;3218(3%83721&QDr8r7%3221%;5?B:91%>3=17p071p0A1pT0J1pSLK1pSJL1pSFM1pT>Q11pQ0Q31").
Proof.
intros L m a b c d Hle H. unfold mremap_budget_refused_b in *. cbv zeta in *.
change (mremap_source_b (m_vmmaps (setlim L m))) with (mremap_source_b (setlimh L (m_vmmaps m))).
change (mremap_backing_uniform_b (setlim L m)) with (mremap_backing_uniform_b m).
change (mremap_source_b (setlimh L (m_vmmaps m))) with (mremap_source_b (m_vmmaps m)).
(* 08b1429 Sys/Mm/Mremap.v: the mark gained a [TASK_SIZE] gate and splits on
   [mremap_inplace_room_b] (final budget with room, move charge without); the room test
   reads no [vm_limit], so its setlim form is the plain one and the loop destructs it *)
change (mremap_inplace_room_b (setlim L m)) with (mremap_inplace_room_b m).
repeat match goal with
| |- context [if ?b then _ else _] =>
lazymatch b with
| context [setlim] => fail
| _ => destruct b eqn:?
end
end; try reflexivity.
all: cbv beta iota in H.
all: apply negb_false_iff in H; apply negb_false_iff.
all: first [ apply mremap_final_budget_mono; assumption
| apply mremap_move_budget_mono; assumption ].
Qed.
Lemma alloc_mark_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "M'>'Q5'Q3&QI&Q<&Q9r1%211%411r3%7221';'2&Ir2%2261(3%63521r4&QDr5%221<%9241%<3;17p071p0?1pT>H1pT:J1pQ0L1").
Proof.
intros L i m Hle H. unfold alloc_budget_refused_b in *. cbv zeta in *.
destruct (bv_unsigned (in_sysno i) =? 214); [apply brk_mark_setlim; assumption|].
(* 08b1429 Run.v: 215 (munmap) dispatches to [Mmap.munmap_budget_refused_b], which is [false] *)
destruct (bv_unsigned (in_sysno i) =? 215); [reflexivity|].
destruct (bv_unsigned (in_sysno i) =? 216); [apply mremap_mark_setlim; assumption|].
destruct (bv_unsigned (in_sysno i) =? 222); [apply mmap_mark_setlim; assumption|].
destruct (bv_unsigned (in_sysno i) =? 226); [apply mprotect_mark_setlim; assumption|].
reflexivity.
Qed.
Section Step.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable L : Z.
Hypothesis MCLE : move_charge_le_stmt.
Definition liftc (c : config) : config := mkCfg (cfg_ms c) (setlim L (cfg_model c)).
Definition lift_to (r : step_to) : step_to :=
match r with SNext c => SNext (liftc c) | SError => SError end.
Definition okc (c : config) : Prop :=
~ budget_refused_at segs c
/\ vm_limit (m_vmmaps (cfg_model c)) <= L
/\ maps_bounded (vm_maps (m_vmmaps (cfg_model c))).
Lemma okc_mark : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q9'F'Q3'RHyR0%211&QH(Lr3r2%3221%511';'6%119&Q8%118(0%11=%73531&Gr5%211(1%12C@%=3;31'2&I&Q1vRGr6r4%43321%621<(3%G3921p0;1p0B1p0K1pUFQ21pT>Q61pTFQ81").
Proof.
intros ms m x8 (Hnr & _ & _) Hh Hs.
destruct (alloc_budget_refused_b (sys_input segs ms x8) m) eqn:E; [|reflexivity].
exfalso. apply Hnr. split; [exact Hh|]. right. exists x8. split; [exact Hs|]. left. exact E.
Qed.
Lemma okc_sim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q;'F'Q3'RHyR0%211&QH(Lr3r2%3221%511';'6%119&Q8%118(0%11=%73531&Gr5%211(1%12C@%=3;31&QCv?'Q4r1qUD21&Q2&Q1vRGr6r4%43321%;8:997661@p0=1p0D1p0M1pUFQ41pT>Q81pTFQ:1").
Proof.
intros ms m x8 Hok Hh Hs. pose proof (okc_mark ms m x8 Hok Hh Hs) as Hmk.
destruct Hok as (_ & Hle & Hb).
exact (syscall_nat MCLE L _ m Hmk Hle Hb).
Qed.
Lemma sim_fwd_ok : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q9'Q5'Q3'Q4'4'Q7%211&QCv?r1qUD71&Q2r5r4%786;;43321r6&QD%1295(@r3r2%34B821%;3751'<':r8r7%94H<B>%A3321';%>2FE%23MC1%8241qTDO1%;2Q01p0=1p0F1pT4O1pT@Q41pT2Q41pT>Q61pT:Q81").
Proof.
intros i m eff m' evs H H1. destruct (proj1 H _ H1) as ([x0 m0 e0|] & H2 & E); [|discriminate].
cbn in E. injection E as -> -> ->. exists m0. split; [exact H2 | reflexivity].
Qed.
Lemma sim_bwd_ok : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q1'Q5'Q3'Q4'4'Q7%211&QCv?r1qUD71&Q2r5r4%786;;43321r6(@r3r2%34@621%93581r7&QD%12?8%22@;%94F=18%?3531p071p0>1pT4G1pTDL1pT2L1pT>N1pT:Q01").
Proof. intros i m eff m0 evs H H2. exact (proj2 H _ H2). Qed.
Lemma sim_unm_iff : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "F'Q5'Q3&QCv?'Q4r1qUD21&Q2r2%7865532214&=r3&QD%12:5(A%11;%93531%:3692%8221p0:1pT>C1pT:E1").
Proof.
intros i m H. split.
- intros H1. destruct (proj1 H _ H1) as ([x0 m0 e0|] & H2 & E); [discriminate|]. exact H2.
- intros H2. exact (proj2 H _ H2).
Qed.
Lemma refusal_b_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "D'Q5'Q3'RHyR0%211';'2&Mr3&QDv?r2%3221r1%73621%83742%;3:21pU6=1pT>A1pT:C1").
Proof. reflexivity. Qed.
Lemma spurious_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "H'Q5'Q3'Q4&QCv?r1qUD41&Q2r3r2%7868843321&=&NvQNr4&QD%12<8%544318%6454:9%8221p0:1pT2C1pT>E1pT:G1").
Proof.
intros i m eff H. unfold spurious_refusal_cfg. rewrite refusal_b_setlim.
split; intros (H1 & H2 & (eff' & m' & evs' & H3 & H4)); (split; [exact H1|]); (split; [exact H2|]).
- destruct (sim_fwd_ok i m eff' m' evs' H H3) as (m0 & H5 & ->).
exists eff', m0, evs'. split; [exact H5|]. rewrite <- refusal_b_setlim. exact H4.
- exists eff', (setlim L m'), evs'. split; [exact (sim_bwd_ok i m eff' m' evs' H H3)|].
rewrite refusal_b_setlim. exact H4.
Qed.
Lemma okc_mat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "QM'F'Q3'RHyR0%211'Q4'4'Q7%211&QH(Lr6r5%3221%511';'6%11=&Q8%118(0%11A%73531&Gr8%211(1%12G@%=3;31&Q2&Q1vRGr9r7%43321(@r4%24Q0JI1%934>1'<%H1Q7&Q:&Q;%11;%32D1r1%D2Q=1%Q03731qTBQ?1%:2Q@1p0L1p0=1p0H1p0O1p0Q81pT4Q?1pT@QG1pT2QD1pUFQF1pT>QJ1pTFQL1").
Proof.
intros ms m x8 eff m' evs Hok Hh Hs Hsp Hh'.
destruct (materialize_model_accesses m' (syscall_effect_accesses eff)) as [m''|] eqn:E;
[exists m''; reflexivity|].
exfalso. destruct Hok as (Hnr & _ & _). apply Hnr. split; [exact Hh|]. right.
exists x8. split; [exact Hs|]. right. exists eff, m', evs. auto.
Qed.
Lemma okc_instr_mat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "QG'F'Q3'C%113&QH(Lr3r2%3221%511';'6'RHyR0%211%411&Q8%11;(0%115%:3531&Gr5%211%>3915'E%11G&HvRGr6%3221(Br4%22N1%H3841'<%I1Q3&Q:r7&D%12Q8;%4231(1r1%22Q;1%Q33941qT@Q=1%<2Q>1p0>1p0I1p0N1p0Q:1pU<QA1pT>QD1pTFQF1").
Proof.
intros ms m report Hok Hh Hs Hst.
destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m'|] eqn:E;
[exists m'; reflexivity|].
exfalso. destruct Hok as (Hnr & _ & _). apply Hnr. split; [exact Hh|]. left.
split; [exact Hs|]. left. exists report. auto.
Qed.
Lemma spec_limit : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q9'Q5'Q3'Q4'4'Q7%211';'2&Ir5r4%3221(3%73621&QE&Q=&Q9%118%311%511&Q2r7r6(@r3%24G@?1%63541'>&Q<%11<%>19%311%J3531p071p0?1p0F1pT4O1pT@Q41pT2Q41pT>Q61pT:Q81").
Proof.
intros i m eff m' evs Hmk Hb H.
pose proof (syscall_nat MCLE (vm_limit (m_vmmaps m)) i m Hmk (Z.le_refl _) Hb) as S.
pose proof (proj1 S (Ok eff m' evs)) as S1. rewrite setlim_self in S1.
destruct (S1 H) as ([x0 m0 e0|] & H2 & E); [|discriminate].
cbn in E. injection E as _ -> _. reflexivity.
Qed.
Lemma mi_account_step_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q6'F'Q3&QH(Lr4r3%3221%511';'E'8%12;:%311&KvRGr5%3321<(B(7r2%24DC?1%42:1%>3:61r6&QDv?%221;%>3=41%423G%;4MLI1%=2C1%G3C41p0:1p0J1pT@Q11pTHQ31pT>Q31pTFQ51").
Proof.
intros ms m ms' m' (_ & Hle & _) H. unfold mi_account_step in *.
destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate.
destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m1|] eqn:E; [|discriminate].
injection H as <- <-. rewrite (materialize_setlim L m _ m1 Hle E). reflexivity.
Qed.
(* 08b1429 Run.v: [sstep_cfg] gained three vDSO arms (after [*_instr_unmodeled], which gained
   [vdso_entry_fn segs (ms_pc ms) = None]); [budget_refused_at]'s no-svc clause became
   [instr refused \/ vdso refused]. No vDSO
   function's sysno (113, 114, 168, 169, 258, 259) is an allocation call, so the mark is false
   there and [syscall_nat] runs at it. *)
Lemma vdso_alloc_false : forall ms m fn n, vdso_fn_sysno fn = Some n ->
  alloc_budget_refused_b (sys_input segs ms (Z_to_bv 64 n)) m = false.
Proof. intros ms m fn n H. destruct fn; cbn in H; try discriminate H; injection H as <-; vm_compute; reflexivity. Qed.
Theorem step_fwd : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "I'J'4'Q7%211'Q0&QHr3%211'OvRGvQNr4r2%5543271&QGr5%211&QF%11<%;5:9381p071p0>1pU6B1pT4D1pSLH1").
Proof.
intros c evs r Hok H. destruct H as
[ms m ms' m' Hh Hs Ha | ms m Hh Hs Ha | ms m Hh Hs Ha Hnv
| ms m fn n eff m' m'' evs0 Hh Hs Ha Hfn Hno Hsp Hef Hh' Hm
| ms m fn n eff m' evs0 Hh Hs Ha Hfn Hno Hsp Hef Hh' Hm
| ms m fn Hh Hs Ha Hfn Hun
| ms m x8 eff m' m'' evs0 Hh Hs Hsp Hnsp Hh' Hm
| ms m x8 eff m' evs0 Hh Hs Hsp Hnsp Hh' Hm
| ms m x8 eff m' evs0 code Hh Hs Hsp Hh' Hk
| ms m x8 eff m' evs0 sig Hh Hs Hsp Hk
| ms m x8 Hh Hs Hsp ]; cbn [lift_to liftc cfg_ms cfg_model].
- apply sstep_cfg_instr; [exact Hh | exact Hs |]. exact (mi_account_step_setlim ms m ms' m' Hok Ha).
- apply sstep_cfg_instr_fault; [exact Hh | exact Hs |].
unfold mi_account_step in *. cbn [cfg_ms cfg_model] in *.
destruct (RiscvSemantics.step_accesses segs ms) as [report| |] eqn:Est; try discriminate.
+ destruct (materialize_model_accesses m (@accessed_ranges _ report)) eqn:E; [discriminate|].
exfalso. destruct (okc_instr_mat ms m report Hok Hh Hs Est) as (m1 & E1). congruence.
+ reflexivity.
- apply sstep_cfg_instr_unmodeled; [exact Hh | exact Hs | | exact Hnv].
unfold mi_account_step in *. cbn [cfg_ms cfg_model] in *.
destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate.
+ destruct (materialize_model_accesses m (@accessed_ranges _ report)); discriminate.
+ reflexivity.
- (* vdso_call *)
pose proof (vdso_alloc_false ms m fn n Hno) as Hmk.
destruct Hok as (Hnr & Hle & Hb).
pose proof (syscall_nat MCLE L (sys_input segs ms (Z_to_bv 64 n)) m Hmk Hle Hb) as S.
pose proof (spec_limit _ m eff m' evs0 Hmk Hb Hsp) as Hl0.
change (sstep_cfg segs cfg (mkCfg ms (setlim L m)) evs0
  (SNext (mkCfg (vdso_post segs ms (setlim L m) (vdso_frame segs) eff)
                (with_vdso_bump (setlim L m''))))).
eapply sstep_cfg_vdso_call with (model' := setlim L m') (model'' := setlim L m'').
+ exact Hh.
+ exact Hs.
+ unfold mi_account_step in *. cbn [cfg_ms cfg_model] in *.
destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate.
* destruct (materialize_model_accesses m (@accessed_ranges _ report)); discriminate.
* reflexivity.
+ exact Hfn.
+ exact Hno.
+ exact (sim_bwd_ok _ m eff m' evs0 S Hsp).
+ exact Hef.
+ exact Hh'.
+ apply (materialize_setlim L m' _ m''); [rewrite Hl0; exact Hle | exact Hm].
- (* vdso_materialization_fault: a budget-refused configuration, excluded by okc *)
exfalso. destruct Hok as (Hnr & _ & _). apply Hnr. split; [exact Hh|]. left.
split; [exact Hs|]. right. split; [exact Ha|].
exists fn, n, eff, m', evs0.
split; [exact Hfn|]. split; [exact Hno|]. split; [exact Hsp|]. split; [exact Hef|]. split; [exact Hh'|]. exact Hm.
- (* vdso_unmodeled *)
apply sstep_cfg_vdso_unmodeled with (fn := fn); [exact Hh | exact Hs | | exact Hfn |].
+ unfold mi_account_step in *. cbn [cfg_ms cfg_model] in *.
destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate.
* destruct (materialize_model_accesses m (@accessed_ranges _ report)); discriminate.
* reflexivity.
+ destruct Hun as [Hu | [(n & Hn & Hsu) | (n & eff & mo & evs1 & Hn & Hsp & Hd)]].
* left; exact Hu.
* right; left. exists n. split; [exact Hn|].
destruct Hok as (_ & Hle & Hb).
pose proof (syscall_nat MCLE L _ m (vdso_alloc_false ms m fn n Hn) Hle Hb) as S.
apply (sim_unm_iff _ m S). exact Hsu.
* right; right.
destruct Hok as (_ & Hle & Hb).
pose proof (syscall_nat MCLE L _ m (vdso_alloc_false ms m fn n Hn) Hle Hb) as S.
exists n, eff, (setlim L mo), evs1. split; [exact Hn|].
split; [exact (sim_bwd_ok _ m eff mo evs1 S Hsp)|]. exact Hd.
- pose proof (okc_sim ms m x8 Hok Hh Hs) as S.
destruct Hok as (Hnr & Hle & Hb).
eapply sstep_cfg_syscall with (model' := setlim L m').
+ exact Hh.
+ exact Hs.
+ exact (sim_bwd_ok _ m eff m' evs0 S Hsp).
+ rewrite (spurious_setlim _ m eff S). exact Hnsp.
+ exact Hh'.
+ apply (materialize_setlim L m' _ m''); [|exact Hm].
rewrite (spec_limit _ m eff m' evs0 (okc_mark ms m x8 (conj Hnr (conj Hle Hb)) Hh Hs) Hb Hsp).
exact Hle.
- exfalso. destruct (okc_mat ms m x8 eff m' evs0 Hok Hh Hs Hsp Hh') as (m1 & E1). congruence.
- pose proof (okc_sim ms m x8 Hok Hh Hs) as S.
eapply sstep_cfg_exit with (model' := setlim L m'); try eassumption.
exact (sim_bwd_ok _ m eff m' evs0 S Hsp).
- pose proof (okc_sim ms m x8 Hok Hh Hs) as S.
eapply sstep_cfg_killed with (model' := setlim L m'); try eassumption.
exact (sim_bwd_ok _ m eff m' evs0 S Hsp).
- pose proof (okc_sim ms m x8 Hok Hh Hs) as S.
apply sstep_cfg_syscall_unmodeled with (x8 := x8); try assumption.
apply (sim_unm_iff _ m S). exact Hsp.
Qed.
Theorem step_bwd : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeStep "Q2'J'4'Q7%211'Q0&QHr3%211'OvRGvQN&QGr4%211r2%7565291'<':r6r5r1%=5<;321';&QF%114%33E=1%9251qU8G1%<2H1p0>1p0G1pU:K1pT4M1pSLQ11").
Proof.
intros [ms m] evs r2 Hok H. remember (liftc (mkCfg ms m)) as c2 eqn:Ec.
destruct H as
[ms0 M ms' M' Hh Hs Ha | ms0 M Hh Hs Ha | ms0 M Hh Hs Ha Hnv
| ms0 M fn n eff M' M'' evs0 Hh Hs Ha Hfn Hno Hsp Hef Hh' Hm
| ms0 M fn n eff M' evs0 Hh Hs Ha Hfn Hno Hsp Hef Hh' Hm
| ms0 M fn Hh Hs Ha Hfn Hun
| ms0 M x8 eff M' M'' evs0 Hh Hs Hsp Hnsp Hh' Hm
| ms0 M x8 eff M' evs0 Hh Hs Hsp Hnsp Hh' Hm
| ms0 M x8 eff M' evs0 code Hh Hs Hsp Hh' Hk
| ms0 M x8 eff M' evs0 sig Hh Hs Hsp Hk
| ms0 M x8 Hh Hs Hsp ];
unfold liftc in Ec; cbn [cfg_ms cfg_model] in Ec; injection Ec as -> ->.
-
unfold mi_account_step in Ha.
destruct (RiscvSemantics.step_accesses segs ms) as [report| |] eqn:Est; try discriminate.
destruct (okc_instr_mat ms m report Hok Hh Hs Est) as (m1 & E1).
destruct Hok as (Hnr & Hle & Hb).
rewrite (materialize_setlim L m _ m1 Hle E1) in Ha. injection Ha as <- <-.
exists (SNext (mkCfg (access_value machine_state report) m1)). split; [|reflexivity].
apply sstep_cfg_instr; [exact Hh | exact Hs |].
unfold mi_account_step. rewrite Est, E1. reflexivity.
-
exists SError. split; [|reflexivity].
apply sstep_cfg_instr_fault; [exact Hh | exact Hs |].
unfold mi_account_step in *.
destruct (RiscvSemantics.step_accesses segs ms) as [report| |] eqn:Est; try discriminate.
+ exfalso. destruct (okc_instr_mat ms m report Hok Hh Hs Est) as (m1 & E1).
destruct Hok as (_ & Hle & _).
rewrite (materialize_setlim L m _ m1 Hle E1) in Ha. discriminate.
+ reflexivity.
-
exists SError. split; [|reflexivity].
apply sstep_cfg_instr_unmodeled; [exact Hh | exact Hs | | exact Hnv].
unfold mi_account_step in *.
destruct (RiscvSemantics.step_accesses segs ms) as [report| |] eqn:Est; try discriminate.
+ destruct (materialize_model_accesses (setlim L m) (@accessed_ranges _ report)); discriminate.
+ reflexivity.
- (* vdso_call *)
assert (Ha0 : mi_account_step segs ms m = MachineUnmodeled).
{ unfold mi_account_step in *.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate.
  - destruct (materialize_model_accesses (setlim L m) (@accessed_ranges _ report)); discriminate.
  - reflexivity. }
pose proof (vdso_alloc_false ms m fn n Hno) as Hmk.
destruct Hok as (Hnr & Hle & Hb).
pose proof (syscall_nat MCLE L (sys_input segs ms (Z_to_bv 64 n)) m Hmk Hle Hb) as S.
destruct (sim_fwd_ok _ m eff M' evs0 S Hsp) as (m0 & Hsp0 & ->).
destruct (materialize_model_accesses m0 (syscall_effect_accesses eff)) as [m1|] eqn:E1.
+ pose proof (spec_limit _ m eff m0 evs0 Hmk Hb Hsp0) as Hl0.
rewrite (materialize_setlim L m0 _ m1 ltac:(rewrite Hl0; exact Hle) E1) in Hm.
injection Hm as <-.
exists (SNext (mkCfg (vdso_post segs ms m (vdso_frame segs) eff) (with_vdso_bump m1))).
split; [|reflexivity].
eapply sstep_cfg_vdso_call;
  [exact Hh | exact Hs | exact Ha0 | exact Hfn | exact Hno | exact Hsp0 | exact Hef | exact Hh' | exact E1].
+ exfalso. apply Hnr. split; [exact Hh|]. left. split; [exact Hs|]. right. split; [exact Ha0|].
exists fn, n, eff, m0, evs0.
split; [exact Hfn|]. split; [exact Hno|]. split; [exact Hsp0|]. split; [exact Hef|]. split; [exact Hh'|]. exact E1.
- (* vdso_materialization_fault *)
exfalso.
assert (Ha0 : mi_account_step segs ms m = MachineUnmodeled).
{ unfold mi_account_step in *.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate.
  - destruct (materialize_model_accesses (setlim L m) (@accessed_ranges _ report)); discriminate.
  - reflexivity. }
pose proof (vdso_alloc_false ms m fn n Hno) as Hmk.
destruct Hok as (Hnr & Hle & Hb).
pose proof (syscall_nat MCLE L (sys_input segs ms (Z_to_bv 64 n)) m Hmk Hle Hb) as S.
destruct (sim_fwd_ok _ m eff M' evs0 S Hsp) as (m0 & Hsp0 & ->).
destruct (materialize_model_accesses m0 (syscall_effect_accesses eff)) as [m1|] eqn:E1.
+ pose proof (spec_limit _ m eff m0 evs0 Hmk Hb Hsp0) as Hl0.
rewrite (materialize_setlim L m0 _ m1 ltac:(rewrite Hl0; exact Hle) E1) in Hm. discriminate.
+ apply Hnr. split; [exact Hh|]. left. split; [exact Hs|]. right. split; [exact Ha0|].
exists fn, n, eff, m0, evs0.
split; [exact Hfn|]. split; [exact Hno|]. split; [exact Hsp0|]. split; [exact Hef|]. split; [exact Hh'|]. exact E1.
- (* vdso_unmodeled *)
exists SError. split; [|reflexivity].
apply sstep_cfg_vdso_unmodeled with (fn := fn); [exact Hh | exact Hs | | exact Hfn |].
+ unfold mi_account_step in *.
destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate.
* destruct (materialize_model_accesses (setlim L m) (@accessed_ranges _ report)); discriminate.
* reflexivity.
+ destruct Hun as [Hu | [(n & Hn & Hsu) | (n & eff & mo & evs1 & Hn & Hsp & Hd)]].
* left; exact Hu.
* right; left. exists n. split; [exact Hn|].
destruct Hok as (_ & Hle & Hb).
pose proof (syscall_nat MCLE L _ m (vdso_alloc_false ms m fn n Hn) Hle Hb) as S.
apply (sim_unm_iff _ m S). exact Hsu.
* right; right.
destruct Hok as (_ & Hle & Hb).
pose proof (syscall_nat MCLE L _ m (vdso_alloc_false ms m fn n Hn) Hle Hb) as S.
destruct (sim_fwd_ok _ m eff mo evs1 S Hsp) as (m0 & Hsp0 & ->).
exists n, eff, m0, evs1. split; [exact Hn|]. split; [exact Hsp0|]. exact Hd.
-
pose proof (okc_sim ms m x8 Hok Hh Hs) as S.
destruct (sim_fwd_ok _ m eff M' evs0 S Hsp) as (m0 & Hsp0 & ->).
destruct (okc_mat ms m x8 eff m0 evs0 Hok Hh Hs Hsp0 Hh') as (m1 & E1).
pose proof (okc_mark ms m x8 Hok Hh Hs) as Hmk.
destruct Hok as (Hnr & Hle & Hb).
pose proof (spec_limit _ m eff m0 evs0 Hmk Hb Hsp0) as Hl0.
rewrite (materialize_setlim L m0 _ m1 ltac:(rewrite Hl0; exact Hle) E1) in Hm.
injection Hm as <-.
exists (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m1)). split; [|reflexivity].
eapply sstep_cfg_syscall; try eassumption.
rewrite <- (spurious_setlim _ m eff S). exact Hnsp.
-
exfalso. pose proof (okc_sim ms m x8 Hok Hh Hs) as S.
destruct (sim_fwd_ok _ m eff M' evs0 S Hsp) as (m0 & Hsp0 & ->).
destruct (okc_mat ms m x8 eff m0 evs0 Hok Hh Hs Hsp0 Hh') as (m1 & E1).
pose proof (okc_mark ms m x8 Hok Hh Hs) as Hmk.
destruct Hok as (Hnr & Hle & Hb).
pose proof (spec_limit _ m eff m0 evs0 Hmk Hb Hsp0) as Hl0.
rewrite (materialize_setlim L m0 _ m1 ltac:(rewrite Hl0; exact Hle) E1) in Hm. discriminate.
-
pose proof (okc_sim ms m x8 Hok Hh Hs) as S.
destruct (sim_fwd_ok _ m eff M' evs0 S Hsp) as (m0 & Hsp0 & ->).
exists (SNext (mkCfg ms m0)). split; [|reflexivity].
change (m_fs (setlim L m0)) with (m_fs m0).
eapply sstep_cfg_exit with (model' := m0); eassumption.
-
pose proof (okc_sim ms m x8 Hok Hh Hs) as S.
destruct (sim_fwd_ok _ m eff M' evs0 S Hsp) as (m0 & Hsp0 & ->).
exists (SNext (mkCfg ms m0)). split; [|reflexivity].
change (m_fs (setlim L m0)) with (m_fs m0).
eapply sstep_cfg_killed with (model' := m0); eassumption.
-
pose proof (okc_sim ms m x8 Hok Hh Hs) as S.
exists SError. split; [|reflexivity].
apply sstep_cfg_syscall_unmodeled with (x8 := x8); try assumption.
apply (sim_unm_iff _ m S). exact Hsp.
Qed.
End Step.

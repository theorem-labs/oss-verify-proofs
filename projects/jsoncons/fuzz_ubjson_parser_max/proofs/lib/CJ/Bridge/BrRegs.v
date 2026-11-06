(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import IndefiniteDescription.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec ShapeAlg SpinAlg DivergeSim.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import MState Frame.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Bridge_BrRegs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Fpu."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.BrRegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.BrRegs.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nat"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "3lt"; "4Z"; "0F"; "5decode_exec_accesses"; "5machine_state"; "5ms_reg"; "5step"; "5step_accesses"]; ["6advance_past_svc"; "6apply_effect"; "6config"; "6mi_account_step"; "6sys_input"; "6syscall_args"; "7Model"; "7SyscallEffect"; "7SyscallInput"; "8fflags"; "9ffmt"; "9instr"; ":bv_eqb"; ":bvmap"; ":bvmap_set"; ";Core"]; [";accrue"; ";c_fcsr"; ";c_pc"; ";c_resv"; ";core"; ";exec"; ";fget"; ";fread"; ";fset"; ";fwrite"; ";inval_resv"; ";is_x0"; ";rget"; ";rset"; ";with_fcsr"; ";with_pc"]; [";with_resv"; "0R"; "0R'"; "0R1"; "0R2"; "0R3"; "=ares_eqv"; "=cfg_eqv"; "=res2_eqv"; "<canon_regs"; "<core_eqv"; "<eff_eqv"; "<ms_eqv"; "<regs_eqv"; "<res_eqv"; ">msteps"]; ["?getr"; "@of_nat"; "0a"; "0b"; "0c"; "0c'"; "0eff"; "0fc"; "0fl"; "0fmt"; "0i"; "0k"; "0mo"; "0ms"; "0ms'"; "0ms1"]; ["0ms1'"; "0n"; "0pc"; "0r"; "0rv"; "0segs"; "ABV"; "AZ_to_bv"; "Abv"; "0sz"; "0v"; "0w"; "0x8"]]).
Definition regs_eqv (R R' : bvmap 5 word) : Prop :=
forall r : reg, is_x0 r = false -> reg_get R r = reg_get R' r.
Lemma regs_eqv_refl : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs ":&My5'RHyR0%211%5241&QMr1%2211pS441").
Proof. intros R r _. reflexivity. Qed.
Lemma regs_eqv_sym : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "?&My5'RHyR0%211%5241&QMr2r1%3221r3%5241p031pS681pS491").
Proof. intros R R' H r Hr. symmetry. apply H, Hr. Qed.
Lemma regs_eqv_trans : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "A&My5'RHyR0%211%5241&QMr3r2%3221r5%5214p031p041pS<91pS::1pS8;1").
Proof. intros R1 R2 R3 H1 H2 r Hr. etransitivity; [apply H1|apply H2]; exact Hr. Qed.
Lemma reg_get_set : forall (R : bvmap 5 word) (k r : reg) v,
reg_get (bvmap_set k v R) r = if bv_eqb k r then v else reg_get R r.
Proof.
intros R k r v. destruct (bv_eqb k r) eqn:E.
- apply bv_eqb_eq in E. subst. apply reg_get_set_same.
- apply reg_get_set_other. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.
Lemma regs_eqv_set : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "F&My5'RHyR0%211%5241%415&QMr4r3%3221&Nr2r5%35=:521%45>;637%9221p071pUF>1pTH=1pS6?1pS4@1").
Proof. intros R R' k v H r Hr. rewrite !reg_get_set. destruct (bv_eqb k r); [reflexivity|apply H, Hr]. Qed.
Lemma is_x0_bv_eqb : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "@'RHy5%211'6'0&Q;r1%211&L(RFz(4%33;21%53<71%;3:71pU8=1").
Proof. intros r. unfold is_x0, bv_eqb. reflexivity. Qed.
Definition core_eqv (c c' : core) : Prop :=
regs_eqv (c_regs c) (c_regs c') /\ c_fregs c = c_fregs c' /\
c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.
Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvDefIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').
Lemma core_eqv_mk : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "N&My5'RHyR0%211%5241yQ0%511'3%115&QMr6r5%3221&QJ(Or7r4r3r2%5548321%65:9432%8221p0:1pU:?1pT@B1pU6F1pFF1pS6G1pS4H1").
Proof. intros. repeat split; assumption. Qed.
Lemma rget_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "D'Q4'RHy5%211&QJr3r2%3221'6yR0%911&Q<r4%2217%3298%73521p091pU8>1pT<B1pT:C1").
Proof.
intros c c' r (HR & _). unfold rget. destruct (is_x0 r) eqn:E; [reflexivity|]. apply HR, E.
Qed.
Lemma fget_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "D'Q4'RHy5%211&QJr3r2%3221'6yR0%911&Q6r4%2217%3298%73521p091pU8>1pT<B1pT:C1").
Proof. intros c c' r (_ & HF & _). unfold fget. rewrite HF. reflexivity. Qed.
Lemma fread_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "F'Q4'J'RHy5%211&QJr4r3%3221'6'9&Q7r5r2%33271%43982%73621p091pU8>1pTDB1pT<D1pT:E1").
Proof. intros c c' fmt r H. unfold fread. rewrite (fget_eqv c c' r H). reflexivity. Qed.
Lemma c_pc_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "A'Q4&QJr2r1%3221'6'RHyR0%211&Q2r3%211%31:%83521p0:1pT<?1pT:@1").
Proof. intros c c' (_ & _ & H & _). exact H. Qed.
Lemma c_fcsr_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "A'Q4&QJr2r1%3221'6'RHyQ0%211&Q1r3%211%31:%83521p0:1pT<?1pT:@1").
Proof. intros c c' (_ & _ & _ & H & _). exact H. Qed.
Lemma c_resv_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "C'Q4&QJr2r1%3221'6'3'RHyR0%211%411&Q3r3%211%31<%:3521p0<1pT<A1pT:B1").
Proof. intros c c' (_ & _ & _ & _ & H). exact H. Qed.
Local Ltac core_tac :=
unfold core_eqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
accrue, fwrite, inval_resv in *; simpl in *.
Lemma core_eqv_rset : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "F'RHy5%211yR0%411'Q4&QJr2r1%3221&Q=r5r4r3%43321%53438%:221p081pT<=1pT:>1pUF@1pU8C1").
Proof.
intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->).
destruct (is_x0 r); simpl; repeat split; auto using regs_eqv_set.
Qed.
Lemma core_eqv_fset : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "F'RHy5%211yR0%411'Q4&QJr2r1%3221&Q8r5r4r3%43321%53438%:221p081pT<=1pT:>1pUF@1pU8C1").
Proof.
intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->).
repeat split; auto.
Qed.
Lemma core_eqv_with_pc : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "B'RHyR0%211'Q4&QJr2r1%3221&Q?r4r3%3221%4237%9221p071pT<<1pT:=1pUF?1").
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_fcsr : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "B'RHyQ0%211'Q4&QJr2r1%3221&Q>r4r3%3221%4237%9221p071pT<<1pT:=1pUF?1").
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_with_resv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "D'3'RHyR0%211%411'Q4&QJr2r1%3221&Q@r4r3%3221%4237%9221p071pT<<1pT:=1pUF?1").
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_accrue : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "@'I'Q4&QJr2r1%3221&Q0r4r3%3221%4237%9221p071pT<<1pT:=1pTB?1").
Proof. intros fl [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->). repeat split; auto. Qed.
Lemma core_eqv_fwrite : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "H'J'RHy5%211'9'Q4&QJr2r1%3221&Q9r6r5r4r3%544321%645439%;221p091pT<>1pT:?1pUFA1pU8C1pTDG1").
Proof. intros fmt r v c c' H. destruct fmt; apply core_eqv_fset; exact H. Qed.
Lemma core_eqv_inval_resv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "B'RHyR0%211'Q4&QJr2r1%3221&Q:r4r3%3221%4237%9221p071pT<<1pT:=1pT6?1").
Proof.
intros a [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (HR & -> & -> & -> & ->).
destruct s' as [r|]; [destruct (Z.eqb _ _)|]; simpl; repeat split; auto.
Qed.
Lemma core_eqv_if : forall (b : bool) c1 c1' c2 c2',
core_eqv c1 c1' -> core_eqv c2 c2' -> core_eqv (if b then c1 else c2) (if b then c1' else c2').
Proof. intros [] c1 c1' c2 c2' H1 H2; assumption. Qed.
Local Ltac solve_core HR :=
repeat first [ apply core_eqv_rset | apply core_eqv_fset | apply core_eqv_with_pc
| apply core_eqv_with_fcsr | apply core_eqv_with_resv | apply core_eqv_accrue
| apply core_eqv_fwrite | apply core_eqv_inval_resv | apply core_eqv_if
| match goal with |- core_eqv (match ?X with _ => _ end) _ => destruct X end ];
first [ apply (core_eqv_mk _ _ _ _ _ _ HR) | assumption ].
Local Ltac eqv_struct HR :=
repeat first
[ apply EqvDone; solve_core HR
| apply EqvIllegal | apply EqvDefIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault
| apply EqvLoad; intros ?
| apply EqvStore
| match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
| match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].
Local Ltac unfold_exec :=
cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
with_pc load_val store_val exec_csr resolve_rm frm_of].
Lemma rget_eqvR : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "Q4&My5'RHyR0%211%5241&QMr2r1%3221yQ0%911'3%119%<1='6&Q<(Or8r5r4r3%554321?%721?r7%851654B%:21B%<3G41pU8>1pU:@1pT@C1pU6K1pFK1p0H1pS6M1pS4N1").
Proof. intros R R' HR F pc fc rv r. apply rget_eqv. apply core_eqv_mk. exact HR. Qed.
Section SE.
Local Abbreviation SEC_T_exec_eqv_core := (ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "Q6&My5'RHyR0%211%5241yQ0%511'3%115'K&QMr8r7%3221'QK&Q5r3r2(Or9r6r5r4%554;321%93871%75>=543%;3:91%=231p0?1pTFD1pUDK1pU:G1pT@J1pU6N1pFN1pS6O1pS4Q01")) (only parsing).
Variable R : ltac:(sec_ty2 constr:(SEC_T_exec_eqv_core) 0%nat 0%nat).
Variable R' : ltac:(sec_ty2 constr:(SEC_T_exec_eqv_core) 1%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_exec_eqv_core) 2%nat 0%nat).
Variable pc : ltac:(sec_ty2 constr:(SEC_T_exec_eqv_core) 3%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_exec_eqv_core) 4%nat 0%nat).
Variable rv : ltac:(sec_ty2 constr:(SEC_T_exec_eqv_core) 5%nat 0%nat).
Variable sz : ltac:(sec_ty2 constr:(SEC_T_exec_eqv_core) 6%nat 0%nat).
Lemma exec_eqv_core : ltac:(sec_stmt2 constr:(SEC_T_exec_eqv_core) 7%nat 0%nat).
Proof.
intros i HR.
destruct i; unfold_exec; rewrite ?(rget_eqvR R R' HR); eqv_struct HR.
Qed.
End SE.
Lemma exec_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "F'RHyR0%211'K'Q4&QJr2r1%3221'QK&Q5r5r4r3%43321%53439%7221p091pT<>1pT:?1pTFA1pUDC1").
Proof.
intros sz i [R F p f s] [R' F' p' f' s'] (HR & HF & Hp & Hf & Hs); simpl in *; subst.
apply exec_eqv_core; assumption.
Qed.
Definition ms_eqv (ms ms' : machine_state) : Prop :=
regs_eqv (ms_regs ms) (ms_regs ms') /\ ms_fregs ms = ms_fregs ms' /\
ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.
Lemma ms_eqv_refl : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "5'<&QLr1%2211pTL41").
Proof. intros ms. repeat split; apply regs_eqv_refl. Qed.
Lemma ms_eqv_sym : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs ":'<&QLr2r1%3221r3%5241p031pTN81pTL91").
Proof.
intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
repeat split; auto using regs_eqv_sym; congruence.
Qed.
Lemma ms_eqv_trans : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "<'<&QLr3r2%3221r5%5214p031p041pT:91pT8:1pT6;1").
Proof.
intros a b c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
repeat split; eauto using regs_eqv_trans; congruence.
Qed.
Definition res_eqv (r r' : machine_result machine_state) : Prop :=
match r, r' with
| MachineOk a, MachineOk b => ms_eqv a b
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.
Section WithSegs.
Variable segs : list Segment.
Definition ares_eqv (r r' : machine_result (access_report machine_state)) : Prop :=
match r, r' with
| MachineOk a, MachineOk b => ms_eqv (@access_value _ a) (@access_value _ b) /\ @accessed_ranges _ a = @accessed_ranges _ b
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.
Section SE.
Local Abbreviation SEC_T_interp_eff_accesses_eqv := (forall t t', eff_eqv t t' -> forall m,
match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
| MachineOk a, MachineOk b => core_eqv (fst (@access_value _ a)) (fst (@access_value _ b))
/\ snd (@access_value _ a) = snd (@access_value _ b)
/\ @accessed_ranges _ a = @accessed_ranges _ b
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end) (only parsing).
Variable t : ltac:(sec_ty2 constr:(SEC_T_interp_eff_accesses_eqv) 0%nat 0%nat).
Variable t' : ltac:(sec_ty2 constr:(SEC_T_interp_eff_accesses_eqv) 1%nat 0%nat).
Lemma interp_eff_accesses_eqv : ltac:(sec_stmt2 constr:(SEC_T_interp_eff_accesses_eqv) 2%nat 0%nat).
Proof.
intros H.
induction H; intros m; cbn [interp_eff_accesses]; auto.
- destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [| exact I].
specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
destruct (interp_eff_accesses segs (k _) m) as [[[c1 m1] acc1]| |];
destruct (interp_eff_accesses segs (k' _) m) as [[[c2 m2] acc2]| |]; cbn in *; try exact H0; try contradiction.
destruct H0 as (A & B & C). subst. split; [exact A|]. split; reflexivity.
- destruct (store_ok segs m a (width_bytes n)); [| exact I].
specialize (IHeff_eqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
destruct (interp_eff_accesses segs k _) as [[[c1 m1] acc1]| |];
destruct (interp_eff_accesses segs k' _) as [[[c2 m2] acc2]| |]; cbn in *; try exact IHeff_eqv; try contradiction.
destruct IHeff_eqv as (A & B & C). subst. split; [exact A|]. split; reflexivity.
Qed.
End SE.
Lemma ms_reg17_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "F'<&QLr2r1%3221'6'RHyR0%211&=r3(RFy5+A(4%43321%7261%82?2%=3:21p0?1pTND1pTLE1").
Proof. intros ms ms' (HR & _). unfold ms_reg. cbn. apply HR. reflexivity. Qed.
Lemma decode_exec_accesses_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "C'<'RHyQ0%211&QLr3r2%3221&QF&;vREr4%33216%43387%6221p081pUH=1pTNA1pTLB1").
Proof.
intros ms ms' w Heqv. pose proof (ms_reg17_eqv ms ms' Heqv) as H17.
destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
unfold RiscvSemantics.decode_exec_accesses. destruct (is_ecall w).
- simpl. rewrite H17. repeat split; assumption.
- destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
pose proof (interp_eff_accesses_eqv _ _ (exec_eqv_core R R' F' pc' fc' rv' (Z_to_bv 64 isz) i HR) m') as K.
destruct (interp_eff_accesses segs (exec _ i (Core R F' pc' fc' rv')) m') as [[[c m1] acc1]| |];
destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] acc2]| |];
simpl in *; try exact K; try contradiction.
destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). repeat split; simpl; auto.
Qed.
Lemma step_accesses_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "?'<&QLr2r1%3221&QF&?vREr3%3221%4238%6221p081pTN=1pTL>1").
Proof.
intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.
Lemma step_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "?'<&QLr2r1%3221&QN&>vREr3%3221%4238%6221p081pTN=1pTL>1").
Proof.
intros ms ms' Heqv. unfold RiscvSemantics.step, RiscvSemantics.drop_access_report.
pose proof (step_accesses_eqv ms ms' Heqv) as K.
destruct (RiscvSemantics.step_accesses segs ms) as [a| |], (RiscvSemantics.step_accesses segs ms') as [b| |];
cbn in *; try exact K; try contradiction. exact (proj1 K).
Qed.
Definition res2_eqv (r r' : machine_result (machine_state * Model)) : Prop :=
match r, r' with
| MachineOk (a, mo), MachineOk (b, mo') => ms_eqv a b /\ mo = mo'
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.
Lemma mi_account_step_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "A'<'F&QLr3r2%3221&QH&CvREr4%33216%43387%6221p081pTJ=1pTN?1pTL@1").
Proof.
intros ms ms' mo Heqv. unfold mi_account_step.
pose proof (step_accesses_eqv ms ms' Heqv) as K.
destruct (RiscvSemantics.step_accesses segs ms) as [a| |], (RiscvSemantics.step_accesses segs ms') as [b| |];
cbn in *; try exact K; try contradiction.
destruct K as [K1 <-]. destruct (materialize_model_accesses mo (accessed_ranges machine_state a)); [|exact I].
split; [exact K1|reflexivity].
Qed.
Lemma syscall_args_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "C'<&QLr2r1%3221'6'1'RHyR0%211%411&Er3%211%31<%:3521p0<1pTNA1pTLB1").
Proof. intros ms ms' (HR & _). unfold syscall_args, ms_gpr. rewrite !HR by reflexivity. reflexivity. Qed.
Lemma sys_input_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "D'<'RHyR0%211&QLr3r2%3221'6'H&DvREr4%33217%43398%73621p091pUJ>1pTNB1pTLC1").
Proof.
intros ms ms' x8 Heqv. pose proof (syscall_args_eqv ms ms' Heqv) as Ha.
destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
unfold sys_input. rewrite Ha. reflexivity.
Qed.
Lemma apply_effect_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "?'<'G&QLr3r2%3221&Ar4%2214%3265%8221p061pT>;1pTN=1pTL>1").
Proof.
intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] eff
(HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
unfold apply_effect, set_reg; simpl. repeat split; simpl; auto using regs_eqv_set.
Qed.
Lemma advance_past_svc_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "='<&QLr2r1%3221&@r3%211%316%8221p061pTN;1pTL<1").
Proof.
intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro']
(HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
unfold advance_past_svc, ms_pc; simpl. repeat split; auto.
Qed.
Definition cfg_eqv (c c' : config) : Prop :=
ms_eqv (cfg_ms c) (cfg_ms c') /\ cfg_model c = cfg_model c'.
Lemma cfg_eqv_refl : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "5'B&QGr1%2211pT:41").
Proof. intros c. split; [apply ms_eqv_refl| reflexivity]. Qed.
Lemma cfg_eqv_sym : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs ":'B&QGr2r1%3221r3%5241p031pT<81pT:91").
Proof. intros c c' [H1 H2]. split; [apply ms_eqv_sym; exact H1| congruence]. Qed.
Lemma cfg_eqv_trans : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "<'B&QGr3r2%3221r5%5214p031p041pT:91pT8:1pT6;1").
Proof. intros a b c [H1 H2] [G1 G2]. split; [eapply ms_eqv_trans; eassumption| congruence]. Qed.
Lemma msteps_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "G'<'QOvREr2r1%43321&QLr4%2214'7'5r3%;3:18r5%821:%5231qU2@1%82A1p0:1pTNC1p0?1pU0E1pTLF1").
Proof.
intros ms ms1 H. induction H as [ms | ms msa msb Hsvc Hstep Hms IH]; intros ms' Heqv.
- exists ms'. split; [apply CatSim.mst_refl| exact Heqv].
- pose proof (step_eqv ms ms' Heqv) as K. rewrite Hstep in K.
destruct (RiscvSemantics.step segs ms') as [msa'| |] eqn:E; simpl in K; try contradiction.
destruct (IH msa' K) as (msb' & Hms' & Hb).
exists msb'. split; [|exact Hb].
eapply CatSim.mst_step; [| exact E | exact Hms'].
destruct Heqv as (_ & _ & _ & Hs & _). congruence.
Qed.
End WithSegs.
Lemma reg_of_nat : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "E'RHy5%211'7'2'5'6r2&RG&R1r1%211%42;1%73;61&8uQ0%2261%<241qU4>1%@2?1pU8B1").
Proof.
intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.
Definition canon_regs (R : bvmap 5 word) : bvmap 5 word :=
mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
(getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
(getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
(getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31).
Section SE.
Local Abbreviation SEC_T_canon_regs_eqv := (ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "<&My5'RHyR0%211%5241&QMr1&QI%112%4231pS461")) (only parsing).
Variable R : ltac:(sec_ty2 constr:(SEC_T_canon_regs_eqv) 0%nat 0%nat).
Lemma canon_regs_eqv : ltac:(sec_stmt2 constr:(SEC_T_canon_regs_eqv) 1%nat 0%nat).
Proof.
intros r Hr.
destruct (reg_of_nat r) as (n & -> & Hn).
do 32 (destruct n as [|n]; [first [discriminate Hr | (unfold canon_regs, getr; cbn; reflexivity)] |]). lia.
Qed.
End SE.
Lemma getr_eqv : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRegs "E&My5'RHyR0%211%5241%415&QMr3r2%3221'6&R0r4%2215%3276%53<21p071pU8<1pS6>1pS4?1").
Proof.
intros R R' r H. unfold getr. rewrite <- is_x0_bv_eqb. destruct (is_x0 r) eqn:E; [reflexivity|]. apply H, E.
Qed.
